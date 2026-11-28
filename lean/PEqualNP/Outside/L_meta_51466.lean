import PEqualNP.Defs
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Forall2
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FinCases
import Mathlib.Data.List.Sublists
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
namespace PEqualNP.Outside.L_meta_51466
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
namespace ForestCore
def pn (a b : Nat) : Nat := a * 1000000000000000000 + b
open PEqualNP.CircuitLowerBounds
private def word80 (xs : List Nat) : Nat :=
  xs.foldl (fun a b => (a <<< 80) ||| b) 0
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
def inputs : List Sig := [(BitVec.ofNat 512 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa)),(BitVec.ofNat 512 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc)),(BitVec.ofNat 512 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0)),(BitVec.ofNat 512 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00)),(BitVec.ofNat 512 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000)),(BitVec.ofNat 512 (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000)),(BitVec.ofNat 512 (0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000)),(BitVec.ofNat 512 (0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000)),(BitVec.ofNat 512 (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000))]
def graph : Sig := (BitVec.ofNat 512 (0xfffffffffffffffffffffffffffefffefffffffefffffffcfefefafaeeccaa00fffffffffffffffffffffffffffefffefffffffefffffffcfefefafaeeccaa00))
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 3) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 5 && x 7) || (x 6 && x 7)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl
theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl
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
  ∀ w i,(asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w
def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2
def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws
theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws,(column oriented (sig a)).getLsbD i.val = true := by
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
  ∃ (f : Row → Row) (roots : List Sig),(∀ r, bit (f r) d = true) ∧
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
  (List.range 8).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def typeWord (t : Nat) : Sig := bin (t/81) (inputs.getD (t/9 % 9) zero) (inputs.getD (t % 9) zero)
def varsX (m : Nat) : List Sig := if m<512 then vars m else vars m ++ [typeWord (m/512-1)]
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def qG_ (m : Nat) : Sig :=
  let x := vertex m
  if m.testBit 8 then (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 0 &&& x 6) ||| (x 0 &&& x 7) ||| (x 2 &&& x 4) ||| (x 2 &&& x 5) ||| (x 2 &&& x 7) ||| (x 3 &&& x 5) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
  else (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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
  | 0 => (0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001)
  | 1 => (0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001)
  | 2 => (0x100000000000000010000000000000000000000000000000000000000000000010000000000000001)
  | 3 => (0x10000000000000000000000000000000000000000000000000000000000000001)
  | 4 => (0x1000000000000000100000000000000010000000000000001)
  | 5 => (0x100000000000000000000000000000001)
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
def supportPairs (t : Nat) (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) =>
    let r := if t/81==2 && i==t/9 % 9 then 1 <<< (t % 9) else if t/81==2 && i==t % 9 then 1 <<< (t/9 % 9) else 0
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))
def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))
def properB (T : Sig) := T != zero && T != one
theorem qP_ (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig := qG_ m
def rawMask (m : Nat) (c : ColumnInfo) : Nat := m % 512+512*(c.1/512)
def columnPairs (m z s : Nat) (G : Sig) : List (Sig × Row × Row) :=
  if m.testBit 8 then
    (selected s).map fun (i,a) =>
      let v := 1 <<< i
      let candidates := (0 :: (List.range 8).map (fun j => 1 <<< j))
      let r := (candidates.find? fun r =>
        bit (Fin.ofNat 512 r) G != bit (Fin.ofNat 512 (r ||| v)) G).getD 0
      (a, Fin.ofNat 512 r, Fin.ofNat 512 (r ||| v))
  else supportPairs (z/512+80) s
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let raw := rawMask m c
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := columnPairs m z s G
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (varsX free) xs && decide (L ≤ count-1)
     else properB (qG_ q) &&
       checkLift (fixRows (colFree free q 0) 0) G (varsX free) (varsX q) (qG_ q) xs &&
       decide (L ≤ prior q+count))
theorem col_sound {u} {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower u (varsX q) (qG_ q) (prior q))
    (ok : colCheck m c prior = true) : Slice u (varsX (rawMask m c)) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  revert ok
  obtain ⟨z,o,q,s,L⟩ := c
  intro ok
  let ms := fixRows z o
  let raw := rawMask m (z,o,q,s,L)
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := columnPairs m z s G
  change (((properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (qP_ _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (qP_ _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (qP_ _ ok.1.1.1) (qP_ _ hh.1.1) (valid q) p bank hr ha)
def carryOK (old rep : Nat) (swaps : List Nat) :=
  (properB (qG_ old) && plainWord (qG_ old) && (varsX old).all plainWord) && properB (qG_ rep) &&
    checkMap (swaps.map swapRows) (varsX old) (qG_ old) (varsX rep) (qG_ rep)
theorem carry_of {u old rep L swaps} (ok : carryOK old rep swaps = true)
    (h : Lower u (varsX rep) (qG_ rep) L) : Lower u (varsX old) (qG_ old) L := by
  simp only [carryOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (qP_ _ ok.1.1.1.1) ok.1.1.1.2 ok.1.1.2 (qP_ _ ok.1.2) h
def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound {u} (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower u (varsX e.1) (qG_ e.1) e.2) (q : Nat) :
    Lower u (varsX q) (qG_ q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he
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
    exact ⟨by omega,rfl⟩
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
  let x := fun j => if m.testBit j then v j else 0
  if m.testBit 8 then (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 0 &&& x 6) ||| (x 0 &&& x 7) ||| (x 2 &&& x 4) ||| (x 2 &&& x 5) ||| (x 2 &&& x 7) ||| (x 3 &&& x 5) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
  else (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 152) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (asRow v i) (qG_ m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  by_cases ht : m.testBit 8 = true
  · simp only [bit,qG_,liftGoal,if_pos ht,BitVec.getLsbD_and,BitVec.getLsbD_or,
      pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),
      pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide)]
  · simp only [bit,qG_,liftGoal,if_neg ht,BitVec.getLsbD_and,BitVec.getLsbD_or,
      pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),
      pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide)]
abbrev Cov := Bits × Bits × Bits
def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1,(z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
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
abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0,0,0,0,0,0,0,fun _ => 0)
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)
def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none
def lookupShort (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 4 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none
abbrev Forest := Nat × Nat × (Nat → Bits × Bits) × List ColumnInfo × List (List Nat) ×
  (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (g : Forest) : Nat := g.1
def Forest.mode (g : Forest) : Bool := !(g.1.testBit 10)
def Forest.cap (g : Forest) : Nat := g.2.1
def Forest.samples (g : Forest) : Nat → Bits × Bits := g.2.2.1
def Forest.cols (g : Forest) : List ColumnInfo := g.2.2.2.1
def Forest.autos (g : Forest) : List (List Nat) := g.2.2.2.2.1
def Forest.levels (g : Forest) : Nat → Packing := g.2.2.2.2.2.1
def Forest.index (g : Forest) : Nat → Nat → Option (Nat × Nat) := g.2.2.2.2.2.2
def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  exact raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 152) (hq : chartSamples m q = 0) :
    properPairs (chartGoal m) (asRow p) (asRow q) := by
  intro i
  simp only [chart_bit,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
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
def prefixWidth (d : Nat) := 10*(d-1)
def denseRowWidth (d flags : Nat) := flags % 16 + (if d=0 then 0 else 10) + flags/16
def denseRowStart (d raw dict : Nat) :=
  (dict % 65536)*prefixWidth d + (dict/65536)*(raw+d)
def forestRecord (tab : Packing) (raw i : Nat) : Nat :=
  let (_,d,_,dict,flags,_,marker,word) := tab
  let width := 10*d+raw+d
  if marker<1024 then packedAt word (i*width) width else
    let off := denseRowStart d raw dict+i*denseRowWidth d flags
    let pre := packedAt word off (flags % 16)
    let lastBits := if d=0 then 0 else 10
    let last := packedAt word (off+flags % 16) lastBits
    let mask := packedAt word (off+flags % 16+lastBits) (flags/16)
    let base := (dict % 65536)*prefixWidth d
    packedAt word (pre*prefixWidth d) (prefixWidth d) |||
      (last <<< prefixWidth d) ||| (packedAt word (base+mask*(raw+d)) (raw+d) <<< (10*d))
def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := forestRecord (g.levels k) raw.length i
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)
def getFieldV (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more
def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols[idx]?).bind fun ci =>
    materialize g.mode (varsX (rawMask g.mask ci)) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2
theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool g.mode (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols[i]? with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (List.mem_of_getElem? e)
def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)
def forceDatum {α : Type} : Nat → (Nat → α) → α
  | 0, next => next 0
  | n+1, next => next (n+1)
def readSortedHints (data : Nat → Nat) (dict cw d gapBits : Nat) :
    Nat → Nat → Nat → List (Nat × Nat)
  | 0,_,_ => []
  | left+1,st,first =>
    forceDatum st fun pos => forceDatum first fun base =>
    forceDatum (packedAt data pos 32) fun head =>
    forceDatum (Nat.log2 (head ^^^ (head+1))) fun ones =>
    forceDatum (base+(ones <<< gapBits)+packedAt data (pos+ones+1) gapBits) fun key =>
    forceDatum (packedAt data (dict+key*(cw+d)) (cw+d)) fun pair =>
      (pair &&& ((1 <<< cw)-1),pair >>> cw) ::
        readSortedHints data dict cw d gapBits left (pos+ones+1+gapBits) (key+1)
def promoteHints {α : Type} (a b : Nat) (xs : List α) : List α :=
  let rec collect : List α → Nat → List α → List α → List α → List α
    | [],_,first,second,other => first ++ second ++ other.reverse
    | x::tail,i,first,second,other =>
      if i=a then collect tail (i+1) [x] second other
      else if i=b then collect tail (i+1) first [x] other
      else collect tail (i+1) first second (x::other)
  collect xs 0 [] [] []
def forestHints (tab : Packing) (raw i : Nat) : List (Nat × Nat) :=
  let (num,d,cw,dict,flags,ow,marker,data) := tab
  if marker<1024 then
    let start := num*(10*d+raw+d)
    let pos := start+num*ow+packedAt data (start+i*ow) ow
    getPairs data cw d (packedAt data pos 6) (pos+6+marker)
  else
    let off := denseRowStart d raw dict + num*denseRowWidth d flags
    let pairs := off+num*ow
    let priority := decide (4096≤marker)
    let pos := pairs+(marker-(if priority then 4096 else 1024))*(cw+d)+packedAt data (off+i*ow) ow
    let n := packedAt data pos 5
    let gap := packedAt data (pos+5) 3
    if !priority || decide (n≤1) then readSortedHints data pairs cw d gap n (pos+8) 0 else
      let width := (n-1).log2+1
      let a := packedAt data (pos+8) width
      let b := if n=2 then 1-a else packedAt data (pos+8+width) width
      let extra := if n=2 then width else 2*width
      let xs := readSortedHints data pairs cw d gap n (pos+8+extra) 0
      promoteHints a b xs
def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)
theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible g.mode (targetOf g) k out.toFinset := by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (List.mem_of_getElem? e))
def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov g.mode ws,rules,ls) ws)
theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible g.mode (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact hT (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSet_sound g _ names (prior (by omega)) h
def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n) && block g k start n
theorem block_at {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeVerified g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem block_merge {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩
def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top, block g k 0 (g.levels k).1 = true
def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 152) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.all (fun c => colCheck g.mask c prior) &&
  g.autos.all (fun p => autoOK (targetOf g) (p.map swapRows))
theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower g.mode (varsX q) (qG_ q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact block_at (rows _ hk) i (by omega) (by omega)
def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
theorem root_index {g top prior k i ws} (low : ∀ q, Lower g.mode (varsX q) (qG_ q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible g.mode (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1
theorem lower_forest {g prior i hints} (low : ∀ q, Lower g.mode (varsX q) (qG_ q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower g.mode (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (qP_ _ hp) (essential_plain ess).1 (essential_plain ess).2 _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha
def Known (u : Bool) (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower u (varsX e.1) (qG_ e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (carries : List (Nat × List Nat)) :=
  carries.map (fun v => (v.1,L)) ++ old
theorem extend_ok {u old L m carries} (previous : Known u old)
    (main : Lower u (varsX m) (qG_ m) L)
    (ok : carries.all (fun v => carryOK v.1 m v.2) = true) :
    Known u (extendKnown old L carries) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact carry_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known true [] := by simp [Known]
theorem known_down {u es} (h : Known true es) : Known u es := fun e he => lower_down (h e he)
def lanePlace (v : Nat) (upper : Nat) := 2^153*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^153 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem lanes_and {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs = combineLanes (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_and,ih]
theorem lanes_or {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs = combineLanes (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_or,ih]
theorem lanes_xor {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs = combineLanes (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_xor,ih]
def fullMarks (r packed : Nat) := ((packed+r) >>> 152) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (153*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^153)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 153*(i+1)-153=153*i := by omega
      have ge : ¬153*(i+1)<153 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 152 = (a==BitVec.allOnes 152) := by
  by_cases h : a=BitVec.allOnes 152
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^152-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^152 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm
set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (153*i) =
      (f xs[i]==BitVec.allOnes 152) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^153*u+x+(2^153*v+1)=2^153*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^153 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬153*(i+1)+152<153 := by omega
      have di : 153*(i+1)+152-153=153*i+152 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)
abbrev PackedSig := Nat × Nat
abbrev PackedCov := Nat × Nat × Nat
def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2
theorem xor_meet (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
theorem packed_column {α} (s : α → Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs) = combineLanes (fun x => column d (s x)) xs := by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,lanes_and,lanes_xor,xor_meet]
def packedOp (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=0 then (a.1 &&& b.1,a.2 &&& b.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else if op=2 then (a.1 ^^^ (a.1 &&& b.1),a.2 ^^^ (a.2 &&& b.2))
  else (b.1 ^^^ (b.1 &&& a.1),b.2 ^^^ (b.2 &&& a.2))
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp op (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (dbin op (a x) (b x)).2) xs := by
  by_cases h0 : op=0
  · simp only [packedOp,h0,ite_true,packedSig,lanes_and,dbin,bv]
  by_cases h1 : op=1
  · simp [packedOp,h1,packedSig,lanes_or,dbin,bv]
  by_cases h2 : op=2
  · simp [packedOp,h2,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv]
  · have e (x y : Bits) : ~~~x &&& y = y &&& ~~~x := BitVec.and_comm _ _
    simp only [packedOp,h0,h1,h2,ite_false,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv,e]
def takePacked (c : PackedCov) (a b : Nat) (ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2
theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) ka kb) xs := by
  cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]
def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (dbin op a b) ka kb
def combField (c : NodeContext) (d ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov c.2.2.2.1.1 (column d a.2) (column d b.2) ka kb |||
    column d (dbin op a b).2
def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 153) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (153*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [onMarks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1 ≠ 0 := by
        intro he
        have at0 := congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 153) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn
abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]
theorem masked_comp (d x : Sig) : masked d (neg x) = d ^^^ masked d x := by
  apply bit_ext
  intro r
  simp only [masked,neg,bit,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,r.isLt,decide_true,Bool.true_and]
  cases d.getLsbD r.val <;> cases x.getLsbD r.val <;> rfl
def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem lossBound (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p + constantLoss p a keep := by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]
theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b kb ≤
    (delTwo ws a b ka kb).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  simp only [delTwo]
  omega
noncomputable def force {β : Type} (n : Nat) (f : Nat → β) : β := Nat.rec (f 0) (fun k _ => f (Nat.succ k)) n
theorem force_eq {β : Type} (n : Nat) (f : Nat → β) : force n f = f n := by cases n <;> rfl
noncomputable def forceMap {α β : Type} (f : α → Nat) (l : List α) : (List Nat → β) → β :=
  List.rec (fun k => k []) (fun a _ ih k => force (f a) fun x => ih fun xs => k (x::xs)) l
theorem forceMap_eq {α β : Type} (f : α → Nat) (l : List α) (k : List Nat → β) : forceMap f l k = k (l.map f) := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    change force (f a) (fun x => forceMap f l fun xs => k (x::xs)) = _
    rw [force_eq,ih]
    rfl
def nmask (d : Nat) (a : Sig) : Nat := Nat.land a.toNat d
noncomputable def anyEq (m : Nat) (l : List Nat) : Bool := List.rec false (fun v _ ih => or (Nat.beq m v) ih) l
def nconst (d m : Nat) : Bool := or (Nat.beq m 0) (Nat.beq m d)
noncomputable def navail (u : Bool) (d : Nat) (pm : List Nat) (m : Nat) : Bool :=
  or (or (nconst d m) (anyEq m pm)) (and u (anyEq (Nat.xor d m) pm))
theorem nmask_eq (d a : Sig) : nmask d.toNat a = (masked d a).toNat := (BitVec.toNat_and _ _).symm
theorem beq_toNat (a b : Sig) : Nat.beq a.toNat b.toNat = (a==b) := by
  rw [Bool.eq_iff_iff,Nat.beq_eq,beq_iff_eq]
  exact BitVec.toNat_inj
theorem nconst_eq (d a : Sig) : nconst d.toNat (nmask d.toNat a) = isMaskedConstant d a := by
  rw [nmask_eq]
  have e : Nat.beq (masked d a).toNat 0 = (masked d a == zero) := by
    have z0 : zero.toNat=0 := by simp [zero]
    rw [←beq_toNat,z0]
  rw [nconst,e,beq_toNat]
  rfl
theorem anyEq_eq (x d : Sig) (pool : List Sig) : anyEq x.toNat (pool.map (nmask d.toNat)) = (pool.map (masked d)).any (fun v => v==x) := by
  induction pool with
  | nil => rfl
  | cons a l ih =>
    change or (Nat.beq x.toNat (nmask d.toNat a)) (anyEq x.toNat (l.map (nmask d.toNat))) = _
    rw [ih,nmask_eq,beq_toNat,List.map_cons,List.any_cons,Bool.beq_comm]
theorem navail_eq (u : Bool) (d a : Sig) (pool : List Sig) :
    navail u d.toNat (pool.map (nmask d.toNat)) (nmask d.toNat a) = availableB u d pool a := by
  have x : Nat.xor d.toNat (masked d a).toNat = (masked d (neg a)).toNat := by
    rw [masked_comp]
    exact (BitVec.toNat_xor _ _).symm
  rw [navail,nconst_eq,nmask_eq,x,anyEq_eq,anyEq_eq]
  simp only [availableB,isMaskedConstant]
def unav (u : Bool) (p : BoundPool) (w : Decor) : Nat := cond (availableB u p.domain p.wires w.1) 0 1
def slowCost (u : Bool) (p : BoundPool) (ws : List Decor) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) : Bool :=
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let cm := ws.countP const - constantLoss const a ka - constantLoss const b kb + (isMaskedConstant p.domain z).toNat
  (((ws.map (unav u p)).sum == cond ka 0 (unav u p a) + cond kb 0 (unav u p b)) &&
    decide (k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+cm)) &&
    (availableB u p.domain p.wires z || (availableB u p.domain p.wires a.1 && availableB u p.domain p.wires b.1))
def zN (op x y : Nat) : Nat := cond (Nat.beq op 0) (Nat.land x y) (cond (Nat.beq op 1) (Nat.lor x y)
  (cond (Nat.beq op 2) (Nat.xor x (Nat.land x y)) (Nat.xor y (Nat.land x y))))
theorem zN_eq (op : Nat) (d a b : Sig) : zN op (nmask d.toNat a) (nmask d.toNat b) = nmask d.toNat (bin op a b) := by
  have tn (x y : Sig) : Nat.land x.toNat y.toNat = (x &&& y).toNat := (BitVec.toNat_and x y).symm
  have tx (x y : Sig) : Nat.xor x.toNat y.toNat = (x ^^^ y).toNat := (BitVec.toNat_xor x y).symm
  have tor (x y : Sig) : Nat.lor x.toNat y.toNat = (x ||| y).toNat := (BitVec.toNat_or x y).symm
  simp only [nmask_eq]
  unfold zN
  by_cases h0 : op=0
  · subst h0
    change Nat.land _ _ = _
    rw [tn]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,ite_true,BitVec.getLsbD_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  by_cases h1 : op=1
  · subst h1
    change Nat.lor _ _ = _
    rw [tor]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,Nat.one_ne_zero,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e0 : Nat.beq op 0=false := Bool.eq_false_iff.mpr (fun h => h0 (Nat.eq_of_beq_eq_true h))
  have e1 : Nat.beq op 1=false := Bool.eq_false_iff.mpr (fun h => h1 (Nat.eq_of_beq_eq_true h))
  by_cases h2 : op=2
  · subst h2
    change Nat.xor _ (Nat.land _ _) = _
    rw [tn,tx]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,OfNat.ofNat_ne_zero,OfNat.ofNat_ne_one,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e2 : Nat.beq op 2=false := Bool.eq_false_iff.mpr (fun h => h2 (Nat.eq_of_beq_eq_true h))
  rw [e0,e1,e2]
  change Nat.xor _ (Nat.land _ _) = _
  rw [tn,tx]
  congr 1
  apply bit_ext
  intro r
  simp only [masked,bin,bit,h0,h1,h2,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
  cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
def nloss (d x : Nat) (keep : Bool) : Nat := cond keep 0 (cond (nconst d x) 1 0)
theorem nloss_eq (d : Sig) (a : Decor) (keep : Bool) :
    nloss d.toNat (nmask d.toNat a.1) keep = constantLoss (fun w : Decor => isMaskedConstant d w.1) a keep := by
  rw [nloss,nconst_eq,constantLoss]
  cases keep
  · cases isMaskedConstant d a.1 <;> rfl
  · rfl
abbrev QS := Nat × Nat × Nat × Nat × Nat × List Nat × List Nat × Bool
noncomputable def quickSpec (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) : QS :=
  let d := p.domain.toNat
  let ms := ws.map (fun w : Decor => nmask d w.1)
  (d,ms.countP (nconst d),p.bound,Nat.add k p.paid,(ms.map fun m => cond (navail u d (p.wires.map (nmask d)) m) 0 1).sum,ms,p.wires.map (nmask d),u)
noncomputable def forceBool {β : Type} (b : Bool) (f : Bool → β) : β := Bool.rec (f false) (f true) b
noncomputable def forcePool {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) (f : QS → β) : β :=
  force p.domain.toNat fun d => forceMap (nmask d) p.wires fun pm => forceMap (fun w : Decor => nmask d w.1) ws fun ms =>
  force (ms.countP (nconst d)) fun c => force p.bound fun l => force (Nat.add k p.paid) fun t =>
  force (ms.map fun m => cond (navail u d pm m) 0 1).sum fun v => forceBool u fun u => f (d,c,l,t,v,ms,pm,u)
theorem forcePool_eq {β : Type} (u k ws p) (f : QS → β) : forcePool u k ws p f = f (quickSpec u k ws p) := by
  have e (b : Bool) (f : Bool → β) : forceBool b f = f b := by cases b <;> rfl
  simp only [forcePool,force_eq,forceMap_eq,e]
  rfl
noncomputable def forcePools {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (ps : List BoundPool) : (List QS → β) → β :=
  List.rec (fun f => f []) (fun p _ ih f => forcePool u k ws p fun q => ih fun qs => f (q::qs)) ps
theorem forcePools_eq {β : Type} (u k ws ps) (f : List QS → β) : forcePools u k ws ps f = f (ps.map (quickSpec u k ws)) := by
  induction ps generalizing f with
  | nil => rfl
  | cons p ps ih =>
    change forcePool u k ws p (fun q => forcePools u k ws ps fun qs => f (q::qs)) = _
    rw [forcePool_eq,ih]
    rfl
def kwN (v : Nat) : Nat :=
  let n := v % 2305843009213693921
  (n*(n+971)) % 2305843009213693921
abbrev Lane := NodeContext × Nat × Nat × List QS × List Nat × Nat
noncomputable def laneOf (c : NodeContext) : Lane :=
  let ws := c.2.2.1.map (fun w : Decor => w.1.toNat)
  (c,c.2.2.1.length,cond c.2.2.2.1.2 4 2,c.2.2.2.2.1.map (quickSpec c.2.2.2.1.2 (c.1-1) c.2.2.1),ws,(ws.map kwN).sum)
noncomputable def forceLanes {β : Type} (cs : List NodeContext) : (List Lane → β) → β :=
  List.rec (fun f => f []) (fun c _ ih f => force c.2.2.1.length fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
    forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
    forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => ih fun ys => f ((c,n,l,qs,ws,t)::ys)) cs
theorem forceLanes_eq {β : Type} (cs) (f : List Lane → β) : forceLanes cs f = f (cs.map laneOf) := by
  induction cs generalizing f with
  | nil => rfl
  | cons c cs ih =>
    change force c.2.2.1.length (fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
      forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
      forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => forceLanes cs fun ys => f ((c,n,l,qs,ws,t)::ys)) = _
    rw [force_eq,force_eq,forceMap_eq,force_eq,forcePools_eq,ih]
    rfl
noncomputable def fastCost (s : QS) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (s.2.2.2.2.2.1.getD i 0) fun x => force (s.2.2.2.2.2.1.getD j 0) fun y =>
  let av := navail s.2.2.2.2.2.2.2 s.1 s.2.2.2.2.2.2.1
  let hi := Nat.add s.2.2.1 (Nat.sub (Nat.sub s.2.1 (nloss s.1 x ka)) (nloss s.1 y kb))
  let lo := s.2.2.2.1
  and (Nat.beq s.2.2.2.2.1 (Nat.add (cond ka 0 (cond (av x) 0 1)) (cond kb 0 (cond (av y) 0 1))))
  (cond (Nat.ble (Nat.succ lo) hi)
    (force (zN op x y) fun z => or (av z) (and (Nat.ble (Nat.add lo 2) hi) (and (av x) (av y))))
    (cond (Nat.ble lo hi) (nconst s.1 (zN op x y)) false))
theorem spec_get {d : Nat} (ws : List Decor) (i : Nat) (hd : nmask d zero=0) :
    (ws.map (fun w : Decor => nmask d w.1)).getD i 0 = nmask d (ws.getD i defaultDecor).1 := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none => exact hd.symm
  | some v => rfl
theorem fast_slow {u k p ws i j op ka kb} (h : fastCost (quickSpec u k ws p) i j op ka kb=true) :
    slowCost u p ws k (ws.getD i defaultDecor) (ws.getD j defaultDecor) op ka kb=true := by
  have z0 : nmask p.domain.toNat zero=0 := by
    have : zero.toNat=0 := by simp [zero]
    simp [nmask,this]
  have su : (((ws.map (fun w : Decor => nmask p.domain.toNat w.1)).map fun m => cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) m) 0 1).sum) =
      (ws.map (unav u p)).sum := by
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left ?_)
    intro w _
    change cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) (nmask p.domain.toNat w.1)) 0 1 = _
    rw [navail_eq]
    rfl
  simp only [fastCost,quickSpec,force_eq,spec_get _ _ z0,su,List.countP_map,Function.comp_def,nconst_eq] at h
  generalize ws.getD i defaultDecor=a at h ⊢
  generalize ws.getD j defaultDecor=b at h ⊢
  replace h : and (Nat.beq (ws.map (unav u p)).sum (Nat.add (cond ka 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) 0 1)) (cond kb 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)) 0 1))))
   (cond (Nat.ble (Nat.succ (Nat.add k p.paid)) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb))))
    (or ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) (and (Nat.ble (Nat.add (Nat.add k p.paid) 2) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (and ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)))))
    (cond (Nat.ble (Nat.add k p.paid) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (nconst p.domain.toNat (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) false)) = true := h
  rw [zN_eq,nconst_eq,navail_eq,navail_eq,navail_eq,nloss_eq,nloss_eq] at h
  have ca : isMaskedConstant p.domain (bin op a.1 b.1)=true → availableB u p.domain p.wires (bin op a.1 b.1)=true := by
    intro zc
    simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
    exact Or.inl (Or.inl zc)
  simp only [Nat.add_eq,Nat.sub_eq,Nat.succ_eq_add_one,Bool.and_eq_true,Nat.beq_eq] at h
  obtain ⟨hu,h⟩ := h
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
  refine ⟨⟨hu,?_⟩,?_⟩
  all_goals
    generalize ws.countP (fun w => isMaskedConstant p.domain w.1) - constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) a ka -
      constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) b kb = c at h ⊢
    generalize isMaskedConstant p.domain (bin op a.1 b.1)=r at h ca ⊢
    generalize availableB u p.domain p.wires (bin op a.1 b.1)=q at h ca ⊢
    cases h1 : Nat.ble (k+p.paid+1) (p.bound+c)
    · rw [h1] at h
      cases h2 : Nat.ble (k+p.paid) (p.bound+c)
      · simp [h2] at h
      · have := Nat.ble_eq.mp h2
        simp only [h2,cond_true,cond_false] at h
        subst h
        rw [ca rfl]
        simp <;> omega
    · rw [h1] at h
      have l1 := Nat.ble_eq.mp h1
      simp only [cond_true,Bool.or_eq_true,Bool.and_eq_true,Nat.ble_eq] at h
      rcases h with rfl | ⟨l2,ha,hb⟩
      · simp <;> omega
      · first
        | (have : (!q).toNat ≤ 1 := Bool.toNat_le _
           omega)
        | simp [ha,hb]
theorem anyEq_iff (m : Nat) (l : List Nat) : anyEq m l=true ↔ m ∈ l := by
  induction l with
  | nil => simp [anyEq]
  | cons a l ih =>
    change or (Nat.beq m a) (anyEq m l)=true ↔ _
    rw [Bool.or_eq_true,ih,Nat.beq_eq,List.mem_cons]
noncomputable def linkAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (l.2.2.2.2.1.getD i 0) fun x => force (l.2.2.2.2.1.getD j 0) fun y => force (zN op x y) fun z =>
  Option.rec false (fun ys => forceMap (fun v => v) ys fun ys =>
    and (anyEq z ys) (and (l.2.2.2.2.1.all fun v => or (and (not ka) (Nat.beq v x)) (or (and (not kb) (Nat.beq v y)) (anyEq v ys)))
      (ys.all fun v => or (Nat.beq v z) (and (and (or ka (not (Nat.beq v x))) (or kb (not (Nat.beq v y)))) (anyEq v l.2.2.2.2.1)))))
    (fl (Nat.add (kwN z) (Nat.sub (Nat.sub l.2.2.2.2.2 (cond ka 0 (kwN x))) (cond kb 0 (kwN y)))))
theorem keySet_sum (xs : List Sig) : keySet xs = (xs.map keyWord).sum := by
  have go (a : Nat) : xs.foldl (fun v x => v+keyWord x) a = a+(xs.map keyWord).sum := by
    induction xs generalizing a with
    | nil => rfl
    | cons x xs ih => rw [List.foldl_cons,ih,List.map_cons,List.sum_cons,Nat.add_assoc]
  exact (go 0).trans (Nat.zero_add _)
theorem delTwo_sum (f : Decor → Nat) {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) (ka kb : Bool) :
    ((delTwo ws a b ka kb).map f).sum = (ws.map f).sum - (cond ka 0 (f a)) - (cond kb 0 (f b)) := by
  have er {l : List Decor} {x : Decor} (hx : x ∈ l) : (l.map f).sum = f x + ((l.erase x).map f).sum := by
    have := ((List.perm_cons_erase hx).map f).sum_eq
    rwa [List.map_cons,List.sum_cons] at this
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  have e1 := er ha
  have e2 := er hb
  have e3 := er hm
  cases ka <;> cases kb <;> simp only [delTwo,delOne,Bool.false_eq_true,ite_true,ite_false,cond_true,cond_false] <;> omega
theorem fastCost_good {u p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws) (ne : a≠b) (al : allowedB u op=true)
    (h : slowCost u p ws k a b op ka kb=true) :
    scalarPoolCut u p k ((delTwo ws a b ka kb).map Prod.fst) (movedChoice op a b)=true := by
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let rest := delTwo ws a b ka kb
  have ck := keptCount const ws a b ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b kb ≤ rest.countP const at ck
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  obtain ⟨⟨hu,hc⟩,hz⟩ := h
  have sum := delTwo_sum (unav u p) ha hb ne ka kb
  rw [hu] at sum
  have zs : ((delTwo ws a b ka kb).map (unav u p)).sum=0 := by omega
  have hs : (rest.map Prod.fst).all (availableB u p.domain p.wires)=true := by
    apply List.all_eq_true.mpr
    intro _ hm
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
    have v := List.sum_eq_zero_iff.mp zs _ (List.mem_map_of_mem hw)
    cases e : availableB u p.domain p.wires w.1
    · simp [unav,e] at v
    · rfl
  have opOK : (!(!availableB u p.domain p.wires z) || choiceOK u p.domain p.wires (movedChoice op a b))=true := by
    simp only [Bool.or_eq_true,Bool.and_eq_true] at hz
    rcases hz with hz | ⟨x,y⟩
    · simp [z,hz]
    · simp [choiceOK,movedChoice,x,y,al]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b kb+(isMaskedConstant p.domain z).toNat) at hc
  dsimp only [rest] at hs
  have ez : choiceVal (movedChoice op a b)=z := rfl
  simp only [scalarPoolCut,ez,hs,opOK,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
  cases hc' : isMaskedConstant p.domain z <;> simp [hc'] at hc ⊢ <;> omega
theorem zN_full (op : Nat) (a b : Sig) : zN op a.toNat b.toNat = (bin op a b).toNat := by
  have e (v : Sig) : nmask one.toNat v = v.toNat := by
    rw [nmask_eq]
    congr 1
    exact BitVec.and_allOnes
  have := zN_eq op one a b
  rwa [e,e,e] at this
theorem getW (ws : List Decor) (i : Nat) :
    (ws.map (fun w : Decor => w.1.toNat)).getD i 0 = (ws.getD i defaultDecor).1.toNat := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none =>
    have z0 : zero.toNat=0 := by simp [zero]
    exact z0.symm
  | some v => rfl
theorem wire_ne {c : NodeContext} {i j} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) : (contextWire c i).1 ≠ (contextWire c j).1 := by
  have gi : contextWire c i = c.2.2.1[i] := by simp [contextWire,List.getD_eq_getElem?_getD,hi]
  have gj : contextWire c j = c.2.2.1[j] := by simp [contextWire,List.getD_eq_getElem?_getD,hj]
  rw [gi,gj]
  intro e
  apply hij
  apply (List.Nodup.getElem_inj_iff nd (hi:=by simpa using hi) (hj:=by simpa using hj)).mp
  simpa using e
theorem link_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) (h : linkAt fl (laneOf c) i j op ka kb=true) :
    (c.2.2.2.2.2 (keySet (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))).any (sameWords
      (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  have hne := wire_ne nd hi hj hij
  have ha := mem i hi
  have hb := mem j hj
  have hab : contextWire c i ≠ contextWire c j := fun e => hne (congrArg Prod.fst e)
  have kv (v : Sig) := kept_value nd ha hb ka kb v
  have sum := delTwo_sum (fun w : Decor => keyWord w.1) ha hb hab ka kb
  have wi : contextWire c i = c.2.2.1.getD i defaultDecor := rfl
  have wj : contextWire c j = c.2.2.1.getD j defaultDecor := rfl
  simp only [linkAt,laneOf,force_eq,getW,←wi,←wj,zN_full] at h
  generalize contextWire c i=a at *
  generalize contextWire c j=b at *
  change Option.rec false _ (fl (keyWord (bin op a.1 b.1)+(((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum -
    (cond ka 0 (keyWord a.1)) - (cond kb 0 (keyWord b.1)))))=true at h
  have tot : ((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum = (c.2.2.1.map (fun w : Decor => keyWord w.1)).sum := by
    rw [List.map_map]
    rfl
  rw [tot,←sum] at h
  have tag : keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst) =
      keyWord (bin op a.1 b.1)+((delTwo c.2.2.1 a b ka kb).map (fun w : Decor => keyWord w.1)).sum := by
    rw [keySet_sum,List.map_cons,List.sum_cons,List.map_map]
    rfl
  rw [←tag] at h
  generalize keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst)=t at h ⊢
  cases hf : fl t with
  | none => simp [hf] at h
  | some ys =>
    obtain ⟨xs,hx,rfl⟩ := hfl t ys hf
    rw [hf] at h
    simp only [forceMap_eq,List.map_id',Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,anyEq_iff,Nat.beq_eq,Bool.not_eq_true'] at h
    obtain ⟨h1,h2,h3⟩ := h
    have back {v : Sig} (hv : v.toNat ∈ xs.map BitVec.toNat) : v ∈ xs := by
      obtain ⟨w,hw,e⟩ := List.mem_map.mp hv
      exact BitVec.toNat_inj.mp e ▸ hw
    apply List.any_eq_true.mpr
    refine ⟨xs,hx,?_⟩
    simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq]
    constructor
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact back h1
      · obtain ⟨hw,va,vb⟩ := (kv v).mp hv
        obtain ⟨w,hm,rfl⟩ := List.mem_map.mp hw
        rcases h2 _ (List.mem_map_of_mem hm) with ⟨x,y⟩ | ⟨x,y⟩ | x
        · rcases va with va | va
          · exact absurd (BitVec.toNat_inj.mp y) va
          · simp [va] at x
        · rcases vb with vb | vb
          · exact absurd (BitVec.toNat_inj.mp y) vb
          · simp [vb] at x
        · exact back x
    · intro v hv
      rcases h3 _ (List.mem_map_of_mem hv) with x | ⟨⟨x,y⟩,m⟩
      · exact List.mem_cons.mpr (Or.inl (BitVec.toNat_inj.mp x))
      · refine List.mem_cons_of_mem _ ((kv v).mpr ⟨?_,?_,?_⟩)
        · obtain ⟨w,hw,e⟩ := List.mem_map.mp m
          exact BitVec.toNat_inj.mp e ▸ List.mem_map_of_mem hw
        · rcases x with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
        · rcases y with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
noncomputable def fallbackAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  or (and (and (Nat.ble (Nat.succ i) l.2.1) (and (Nat.ble (Nat.succ j) l.2.1) (and (Nat.ble (Nat.succ op) l.2.2.1) (not (Nat.beq i j)))))
    (or (l.2.2.2.1.any fun s => fastCost s i j op ka kb) (linkAt fl l i j op ka kb))) (checkAt l.1 i j op ka kb)
theorem fallback_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (h : fallbackAt fl (laneOf c) i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true,Bool.and_eq_true] at h
  rcases h with ⟨⟨hi,hj,ho,hn⟩,h | h⟩ | h
  · have hi := Nat.ble_eq.mp hi
    have hj := Nat.ble_eq.mp hj
    have ho := Nat.ble_eq.mp ho
    change Nat.succ i ≤ c.2.2.1.length at hi
    change Nat.succ j ≤ c.2.2.1.length at hj
    change Nat.succ op ≤ cond c.2.2.2.1.2 4 2 at ho
    have al : allowedB c.2.2.2.1.2 op=true := by
      cases hu : c.2.2.2.1.2 <;> simp [hu] at ho <;> simp [allowedB] <;> omega
    have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
      simp [contextWire,List.getD_eq_getElem?_getD,ht]
    obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    have hne := wire_ne nd hi hj (fun e => by simp [e] at hn)
    have closed := fastCost_good (mem i hi) (mem j hj) (fun e => hne (congrArg Prod.fst e)) al (fast_slow ok)
    have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut c.2.2.2.1.2 p (c.1-1)
        ((delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst)
        (movedChoice op (contextWire c i) (contextWire c j)))=true :=
      List.any_eq_true.mpr ⟨p,hp,closed⟩
    simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
    repeat' split
    all_goals rfl
  · have cut := link_sound nd hfl (Nat.ble_eq.mp hi) (Nat.ble_eq.mp hj) (fun e => by simp [e] at hn) h
    simp only [checkAt,evalMove,closeChild,cut,Bool.true_or]
    repeat' split
    all_goals rfl
  · exact h
def swapIdx (v t : Nat) : Nat := cond (Nat.beq t (v &&& 15)) (v >>> 4) (cond (Nat.beq t (v >>> 4)) (v &&& 15) t)
def validSwap (v : Nat) : Bool := and (Nat.ble ((v &&& 15)+1) (v >>> 4)) (Nat.ble ((v >>> 4)+1) 9)
set_option maxRecDepth 8192 in
theorem swap_table : ∀ v : Fin 144, validSwap v.val=true → ∀ t : Fin 9, swapIdx v.val t.val<9 ∧
    wordMove (swapRows v.val) (inputs.getD t.val zero) = inputs.getD (swapIdx v.val t.val) zero := by decide +kernel
theorem swap_input {v t : Nat} (hv : validSwap v=true) (ht : t<9) : swapIdx v t<9 ∧
    wordMove (swapRows v) (inputs.getD t zero) = inputs.getD (swapIdx v t) zero := by
  have lt : v<144 := by
    simp only [validSwap,Bool.and_eq_true,Nat.ble_eq,Nat.shiftRight_eq_div_pow] at hv
    omega
  exact swap_table ⟨v,lt⟩ hv ⟨t,ht⟩
def idxOf (perm : List Nat) (t : Nat) : Nat := perm.foldl (fun t v => swapIdx v t) t
theorem idx_move {perm : List Nat} (ok : perm.all validSwap=true) {t : Nat} (ht : t<9) :
    movedWord (perm.map swapRows).reverse (inputs.getD t zero) = inputs.getD (idxOf perm t) zero := by
  rw [movedWord,List.foldr_reverse,List.foldl_map]
  induction perm generalizing t with
  | nil => rfl
  | cons v perm ih =>
    simp only [List.all_cons,Bool.and_eq_true] at ok
    obtain ⟨lt,e⟩ := swap_input ok.1 ht
    rw [List.foldl_cons,e,ih ok.2 lt]
    rfl
noncomputable def decodeN : Nat → Nat → List Nat → List Nat
  | 0,_,ws => ws
  | n+1,bits,ws => force (zN ((bits >>> 8) &&& 3) (ws.getD (bits &&& 15) 0) (ws.getD ((bits >>> 4) &&& 15) 0))
      fun z => decodeN n (bits >>> 10) (ws++[z])
theorem decodeN_eq (F : Sig → Nat) (F0 : F zero=0) (Fb : ∀ op a b, F (bin op a b)=zN op (F a) (F b))
    (n bits : Nat) (ds : List Decor) :
    (decodeBank n bits ds).map (fun w => F w.1) = decodeN n bits (ds.map fun w => F w.1) := by
  have gd (ds : List Decor) (i : Nat) : (ds.map fun w => F w.1).getD i 0 = F (ds.getD i defaultDecor).1 := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases ds[i]? with
    | none => exact F0.symm
    | some v => rfl
  induction n generalizing bits ds with
  | zero => rfl
  | succ n ih =>
    rw [decodeN,force_eq,decodeBank,ih,gd,gd,←Fb,List.map_append]
    rfl
theorem selectLive_map {α β : Type} (f : α → β) (bits : Nat) (ws : List α) :
    (selectLive bits ws).map f = selectLive bits (ws.map f) := by
  induction ws generalizing bits with
  | nil => rfl
  | cons w ws ih =>
    rw [List.map_cons,selectLive,selectLive]
    split
    · rw [List.map_cons,ih]
    · exact ih _
noncomputable def fastState (g : Forest) (k i : Nat) (perm : List Nat) : List Nat :=
  let raw := (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*depth
  force (forestRecord (g.levels k) (selected g.mask).length i) fun rec =>
  selectLive (rec >>> len) (decodeN depth (rec &&& ((1 <<< len)-1)) raw)
theorem fastState_eq (g : Forest) (k i : Nat) {perm : List Nat} (ok : perm.all validSwap=true) :
    fastState g k i perm = ((stateSet g k i).map (movedWord (perm.map swapRows).reverse)).map BitVec.toNat := by
  let ms := (perm.map swapRows).reverse
  let F (a : Sig) : Nat := (movedWord ms a).toNat
  have F0 : F zero=0 := by
    change (movedWord ms zero).toNat=0
    rw [moved_eq_rename,(rename_constants _).1]
    simp [zero]
  have Fb (op a b) : F (bin op a b)=zN op (F a) (F b) := by
    change (movedWord ms (bin op a b)).toNat = zN op (movedWord ms a).toNat (movedWord ms b).toNat
    rw [zN_full,moved_eq_rename,rename_bin,moved_eq_rename,moved_eq_rename]
  have raw : (wiresOf g).map (fun w => F w.1) = (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat := by
    simp only [wiresOf,rawDecor,List.map_map]
    apply List.map_congr_left
    rintro ⟨j,a⟩ hm
    obtain ⟨hj,rfl⟩ := selected_entry hm
    exact congrArg BitVec.toNat (idx_move ok hj)
  have len : (wiresOf g).length = (selected g.mask).length := by simp [wiresOf,rawDecor]
  unfold fastState stateSet readNode
  rcases g.levels k with ⟨a,depth,b,c,d,e,f,data⟩
  simp only [force_eq,storedDepth,len]
  rw [List.map_map,List.map_map,selectLive_map,←raw,←decodeN_eq F F0 Fb]
  rfl
noncomputable def linkedFast (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Nat) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).bind fun perm => cond (perm.all validSwap) (some (fastState g k pair.1 perm)) none
noncomputable def flOf (g : Forest) (k : Nat) : Nat → Option (List Nat) := fun tag => (g.index k tag).bind (linkedFast g (k-1))
noncomputable def batchMove (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,cov) := b
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  if len>k then true else
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp op a b'
    let mask := fullMarks r (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b') ka kb ||| packedColumn (!u) z)
    onMarks (fun c => fallbackAt fl c i j op ka kb) mask xs
theorem batchMove_at {fl u} (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (pass : batchMove fl u (makeBatch k n xs) (xs.map laneOf) i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] (!u) ka kb op i j != BitVec.allOnes 152 then true
      else if !properB (dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild u xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((delTwo xs[q].2.2.1 (contextWire xs[q] i) (contextWire xs[q] j) ka kb).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,mode,len,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b) ka kb |||
        packedColumn (!u) (packedOp op a b))) (xs.map laneOf)) = true at pass
    rw [if_neg small] at pass
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r,cov] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] (!u) ka kb op i j = BitVec.allOnes 152
    · apply fallback_sound nd hfl
      have m := marked_ok _ _ _ q (by simpa using hq) (by
        rw [mark_at _ _ _ hq]
        exact beq_iff_eq.mpr hit) pass
      simpa only [List.getElem_map] using m
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]
noncomputable def batchPair (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) :=
  let f := batchMove fl u b xs i j op
  f false false && f true false && f false true && f true true
noncomputable def batchRow (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i : Nat) (js : List Nat) :=
    js.all (fun j => (opsOf u).all (batchPair fl u b xs i j))
noncomputable def batchRows (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) : List Nat → Bool
  | [] => true
  | i::js => batchRow fl u b xs i js && batchRows fl u b xs js
theorem batchRows_at {fl u} (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows fl u (makeBatch k n xs) (xs.map laneOf) js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    refine ⟨?_,ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩ op hop
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    rw [mode] at hop
    have pass := allRows.1 j hj op hop
    have check := @batchMove_at fl u k n xs i j op
    simp only [batchPair,Bool.and_eq_true] at pass
    simp only [testPair,Bool.and_eq_true]
    exact ⟨⟨⟨check hi hj' hq budget arity mode nd hfl pass.1.1.1,check hi hj' hq budget arity mode nd hfl pass.1.1.2⟩,
      check hi hj' hq budget arity mode nd hfl pass.1.2⟩,check hi hj' hq budget arity mode nd hfl pass.2⟩
noncomputable def runBatch (fl : Nat → Option (List Nat)) (u : Bool) (k n : Nat) (xs : List NodeContext) :=
    batchRows fl u (makeBatch k n xs) (xs.map laneOf) (List.range n)
theorem runBatch_at {fl u k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hm : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (hn : xs[q].2.2.1.length=n)
    (pass : runBatch fl u k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha hm nd hfl (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all
def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov g.mode ws,rules,ls)
theorem flOf_ok (g : Forest) (k i tag : Nat) (ys) (h : flOf g k tag=some ys) :
    ∃ xs ∈ (contextOf g k i).2.2.2.2.2 tag, ys=xs.map BitVec.toNat := by
  change ∃ xs ∈ ((g.index k tag).bind (linkedSet g (k-1))).toList, _
  unfold flOf at h
  cases hp : g.index k tag with
  | none => simp [hp] at h
  | some pair =>
    simp only [hp,Option.bind_some,linkedFast] at h
    simp only [Option.bind_some,linkedSet]
    split at h
    · contradiction
    next v =>
      cases ha : g.autos[pair.2]? with
      | none => simp [ha] at h
      | some perm =>
        simp only [ha,Option.bind_some] at h
        cases hv : perm.all validSwap with
        | false => simp [hv] at h
        | true =>
          simp only [hv,cond_true,Option.some.injEq] at h
          refine ⟨(stateSet g (k-1) pair.1).map (movedWord (perm.map swapRows).reverse),?_,?_⟩
          · simp [v]
          · exact h.symm.trans (fastState_eq g _ _ hv)
def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem from_context (g : Forest) (k i : Nat) :
    nodeVerified g k i = (prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)) := rfl
theorem makeBlock {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → nodeVerified g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩
def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c)
noncomputable def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  forceLanes xs fun ys => (List.range len).all (fun d =>
    let i := lo+d
    batchRow (flOf g k) g.mode b ys i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (flOf g k) g.mode (makeBatch k ar (contexts g k start n)) ((contexts g k start n).map laneOf)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  simp only [rowCut,forceLanes_eq] at h
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha
theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  simp only [rowCut,forceLanes_eq]
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)
theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch (flOf g k) g.mode k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (flOf g k) g.mode (makeBatch k ar xs) (xs.map laneOf) (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := rowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)
theorem cutsBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : block g k start n=true := by
  apply makeBlock
  intro i lo hi
  let xs := contexts g k start n
  have hm : contextOf g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have nd : (xs[q].2.2.1.map Prod.fst).Nodup := by
    have p := one.2
    simp only [prelim,Bool.and_eq_true,decide_eq_true_eq] at p
    rw [e]
    exact p.1
  have hfl : ∀ tag ys, flOf g k tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat := by
    rw [e]
    exact fun tag ys h => flOf_ok g k i tag ys h
  have hm : xs[q].2.2.2.1.2=g.mode := by rw [e]; rfl
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hm nd hfl hn (cutsRun h)
def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d
theorem boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := rowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v
def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d
theorem cellsBlock {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true := by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v := block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v
end ForestCore
end PEqualNP.Outside.L_meta_51466
namespace PEqualNP.Outside.L_meta_51466.ForestCore
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
private def proofWord80 (xs : List Nat) : Nat :=
  xs.foldl (fun a b => (a <<< 80) ||| b) 0
def g82Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (0x3ff63ff63ff63ff63ff63ff63ff63ff63ff63f)),(BitVec.ofNat 152 (0x49204920492049204920492049204920492049))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (0xc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7)),(BitVec.ofNat 152 (0x92409240924092409240924092409240924092))),(0x0,0x0),((BitVec.ofNat 152 (0xf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8)),(BitVec.ofNat 152 (0x24812481248124812481248124812481248124))),(0x0,0x0),(0x0,0x0)]
def g82C : List ColumnInfo := []
def g82A : List (List Nat) := [[],[100],[65],[65,97],[97,65],[97]]
def g82D3 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7
def g82L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g82D3)
  | _ => emptyPacking
def g82I (_ _ : Nat) : Option (Nat × Nat) := none
def g82 : Forest := ⟨82,3,fun i => g82Y[i]?.getD (0,0),g82C,g82A,g82L,g82I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g82P3_0 : block g82 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g82B3 : block g82 3 0 1=true := g82P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g82T : checkedTables g82 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g82 0 0 0 = true)
  · exact (rfl : block g82 1 0 0 = true)
  · exact (rfl : block g82 2 0 0 = true)
  · exact g82B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g82G : graphValid g82 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low82 : Lower true (varsX 82) (qG_ 82) 4 := lower_forest (g:=g82) (i:=0) (hints:=16842816) (before_sound [] baseKnown) g82G g82T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K82 := extendKnown [] 4 [(82,[]),(137,[16,67,118]),(161,[16,84,118]),(164,[33,84,118]),(194,[100,84,117]),(196,[33,100,84,117]),(200,[49,33,100,84,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V82 : Known true K82 := extend_ok (m:=82) baseKnown low82 (by decide +kernel)
def g45Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (0xe6de3fff03fff1ffe6de3fff03fff1ffe6de3f)),(BitVec.ofNat 152 (0x648490a285024020648490a28502402064849))),(0x0,0x0),((BitVec.ofNat 152 (0x19e9c0fffc07fe3f19e9c0fffc07fe3f19e9c0)),(BitVec.ofNat 152 (0x50e8db2c3161408450e8db2c3161408450e8db))),((BitVec.ofNat 152 (0xece607fffff8003fece607fffff8003fece607)),(BitVec.ofNat 152 (0x8a7b6b04185892808a7b6b04185892808a7b6))),(0x0,0x0),((BitVec.ofNat 152 (0x1b3df8ffffffffc01b3df8ffffffffc01b3df8)),(BitVec.ofNat 152 (0x891524c082060030891524c082060030891524))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g45C : List ColumnInfo := []
def g45A : List (List Nat) := [[],[80,50]]
def g45D3 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xf
def g45L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g45D3)
  | _ => emptyPacking
def g45I (_ _ : Nat) : Option (Nat × Nat) := none
def g45 : Forest := ⟨45,3,fun i => g45Y[i]?.getD (0,0),g45C,g45A,g45L,g45I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g45P3_0 : block g45 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g45B3 : block g45 3 0 1=true := g45P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g45T : checkedTables g45 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g45 0 0 0 = true)
  · exact (rfl : block g45 1 0 0 = true)
  · exact (rfl : block g45 2 0 0 = true)
  · exact g45B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g45G : graphValid g45 (boundsBefore K82) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low45 : Lower true (varsX 45) (qG_ 45) 4 := lower_forest (g:=g45) (i:=0) (hints:=1283) (before_sound K82 V82) g45G g45T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K45 := extendKnown K82 4 [(45,[]),(75,[96,33,16,49,83]),(77,[96,32,50,83]),(89,[96,32,67,50,83]),(101,[32,99,67]),(102,[32,16,83,67,100]),(105,[48,82,96,66,64]),(108,[32,16,49,81,65,100]),(147,[16,32,67,117,101]),(150,[16,67,117,101]),(209,[96,32,67,50,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V45 : Known true K45 := extend_ok (m:=45) V82 low45 (by decide +kernel)
def g86Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (0xfdf00fff81fc7e3ffbe01fff03f8fc7ff7c03f)),(BitVec.ofNat 152 (0x45c09245142904808b81248a28520901170249))),((BitVec.ofNat 152 (0xe6a8703ffe007fc7cd50e07ffc00ff8f9aa1c0)),(BitVec.ofNat 152 (0x96a9b6d618b228112d536dac316450225aa6db))),(0x0,0x0),((BitVec.ofNat 152 (0xfbb781ffffff8007f76f03ffffff000feede07)),(BitVec.ofNat 152 (0x235249820c03122046a49304180624408d492))),(0x0,0x0),((BitVec.ofNat 152 (0x64ffe3ffffffff80c9ffc7ffffffff0193ff8)),(BitVec.ofNat 152 (0x24920410040040004924082008008000924))),(0x0,0x0),(0x0,0x0)]
def g86C : List ColumnInfo := [(4,0,82,0,4)]
def g86A : List (List Nat) := [[],[65]]
def g86D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
def g86L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g86D4)
  | _ => emptyPacking
def g86I (_ _ : Nat) : Option (Nat × Nat) := none
def g86 : Forest := ⟨86,4,fun i => g86Y[i]?.getD (0,0),g86C,g86A,g86L,g86I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g86P4_0 : block g86 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g86B4 : block g86 4 0 1=true := g86P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g86T : checkedTables g86 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g86 0 0 0 = true)
  · exact (rfl : block g86 1 0 0 = true)
  · exact (rfl : block g86 2 0 0 = true)
  · exact (rfl : block g86 3 0 0 = true)
  · exact g86B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g86G : graphValid g86 (boundsBefore K45) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low86 : Lower true (varsX 86) (qG_ 86) 5 := lower_forest (g:=g86) (i:=0) (hints:=16844352) (before_sound K45 V45) g86G g86T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K86 := extendKnown K45 5 [(86,[]),(90,[50]),(139,[32,16,67,118]),(141,[16,67,118]),(163,[32,16,84,118]),(166,[33,84,118]),(172,[33,49,84,118]),(195,[32,100,84,117]),(197,[16,32,100,84,117]),(212,[33,65,49,115,83]),(216,[49,66,114,82]),(225,[16,98,50,84,67,116]),(226,[82,50,100,116]),(232,[49,82,100,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V86 : Known true K86 := extend_ok (m:=86) V45 low86 (by decide +kernel)
def g165Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (0xfe7d01c7fc0fc7cfe7d01c7fc0fc7cfe7d01c7)),(BitVec.ofNat 152 (0x51d124928a290a051d124928a290a051d1249))),(0x0,0x0),((BitVec.ofNat 152 (0x3f8b8e38fff007f3f8b8e38fff007f3f8b8e38)),(BitVec.ofNat 152 (0x884b924930c3210884b924930c3210884b9249))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (0x3fe7703ffffff803fe7703ffffff803fe7703f)),(BitVec.ofNat 152 (0x10002492410402010002492410402010002492))),(0x0,0x0),((BitVec.ofNat 152 (0xc018ffc0fffffffc018ffc0fffffffc018ffc0)),(BitVec.ofNat 152 (0x20004924820804020004924820804020004924))),(0x0,0x0)]
def g165C : List ColumnInfo := [(1,0,164,0,4)]
def g165A : List (List Nat) := [[],[117],[32],[32,117]]
def g165D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
def g165L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g165D4)
  | _ => emptyPacking
def g165I (_ _ : Nat) : Option (Nat × Nat) := none
def g165 : Forest := ⟨165,4,fun i => g165Y[i]?.getD (0,0),g165C,g165A,g165L,g165I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g165P4_0 : block g165 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g165B4 : block g165 4 0 1=true := g165P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g165T : checkedTables g165 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g165 0 0 0 = true)
  · exact (rfl : block g165 1 0 0 = true)
  · exact (rfl : block g165 2 0 0 = true)
  · exact (rfl : block g165 3 0 0 = true)
  · exact g165B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g165G : graphValid g165 (boundsBefore K86) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low165 : Lower true (varsX 165) (qG_ 165) 5 := lower_forest (g:=g165) (i:=0) (hints:=1285) (before_sound K86 V86) g165G g165T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K165 := extendKnown K86 5 [(165,[]),(169,[48,82,32]),(198,[16,101]),(201,[98,50,83]),(202,[16,50,101]),(204,[32,16,49,101]),(210,[64,16,114,50,49,81,101]),(228,[80,16,98,49,67,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V165 : Known true K165 := extend_ok (m:=165) V86 low165 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low55 : Lower true (varsX 55) (qG_ 55) 4 := by
  have q := @lower_count true (vars 55) (qG_ 55) (qP_ _ (by decide +kernel)) (graphPairs 55 66885) (by decide +kernel)
  exact q
def K55 := extendKnown K165 4 [(59,[48,82,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V55 : Known true K55 := extend_ok (m:=55) V165 low55 (by decide +kernel)
def g79Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (0x1fff0007ff803ffc01fffffffffff245f3f007)),(BitVec.ofNat 152 (0x502a8350250681482d0550950a414040f37b6d))),((BitVec.ofNat 152 (0x1ffffff800003fffffffe001ffe001b15bc038)),(BitVec.ofNat 152 (0x854c2a62b62b1591482986d84c8661a159c6db))),((BitVec.ofNat 152 (0x1fffffffffffc00001fffffe00000ce425d1c0)),(BitVec.ofNat 152 (0x6703383384c19e2704e04e06f0b88a425d6db))),((BitVec.ofNat 152 (0xe00000000000000001fffffffffff22fedae07)),(BitVec.ofNat 152 (0x7803c03c0701e0380700700700c022d0c8492))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (0xfffffffffffffffffe00000000000dfa9e5ff8)),(BitVec.ofNat 152 (0x1800c004000020000180180180100452820924))),(0x0,0x0),(0x0,0x0)]
def g79C : List ColumnInfo := [(2,0,77,0,4)]
def g79A : List (List Nat) := [[],[33]]
def g79D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g79L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g79D4)
  | _ => emptyPacking
def g79I (_ _ : Nat) : Option (Nat × Nat) := none
def g79 : Forest := ⟨79,4,fun i => g79Y[i]?.getD (0,0),g79C,g79A,g79L,g79I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79P4_0 : block g79 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g79B4 : block g79 4 0 1=true := g79P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79T : checkedTables g79 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g79 0 0 0 = true)
  · exact (rfl : block g79 1 0 0 = true)
  · exact (rfl : block g79 2 0 0 = true)
  · exact (rfl : block g79 3 0 0 = true)
  · exact g79B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79G : graphValid g79 (boundsBefore K55) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low79 : Lower true (varsX 79) (qG_ 79) 5 := lower_forest (g:=g79) (i:=0) (hints:=16778851) (before_sound K55 V55) g79G g79T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K79 := extendKnown K55 5 [(124,[80,49,66,33,16]),(151,[64,16,49,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V79 : Known true K79 := extend_ok (m:=79) V55 low79 (by decide +kernel)
def g91Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (0xffc00ffc3fe1ffc01ffff87ffcd452be00001f)),(BitVec.ofNat 152 (0x22a4a228884522a950a81148805012bf5ad6b5))),((BitVec.ofNat 152 (0xfffff0003fffffffe00fffffc31359e2007fe0)),(BitVec.ofNat 152 (0xb00c0b102800b0182c0a0010a025922318c63))),(0x0,0x0),((BitVec.ofNat 152 (0xffffffffc001fffffff0007ffcefd1140f801f)),(BitVec.ofNat 152 (0x4c0904c013084c020302c21200af4100a5294a))),((BitVec.ofNat 152 (0x1ffffffffff80004d2fe9f003e0)),(BitVec.ofNat 152 (0x700e07021c10700c0403001c104d06c0c6318c))),(0x0,0x0),((BitVec.ofNat 152 (0xfffffffffffe000000000000033aa61bfffc00)),(BitVec.ofNat 152 (0x8030080020018030180c04602110a019084210))),(0x0,0x0),(0x0,0x0)]
def g91C : List ColumnInfo := [(0,1,82,8,5),(1,0,90,0,5),(2,0,89,0,4),(8,1,82,0,4),(16,0,75,0,4)]
def g91A : List (List Nat) := [[],[65]]
def g91D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x57d4d41
def g91D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x20120240d140ff41fd41fd31)
def g91H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc0
def g91D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x18989f
def g91H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x2051600028b5
def g91L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g91D4)
  | 5 => (3,1,3,0,0,5,0,g91D5)
  | 6 => (1,0,3,0,0,0,0,g91D6)
  | _ => emptyPacking
def g91I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g91H5
  | 6 => lookupWord 1 11 0 7 2 1 g91H6
  | _ => fun _ => none
def g91 : Forest := ⟨91,6,fun i => g91Y[i]?.getD (0,0),g91C,g91A,g91L,g91I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91P4_0 : block g91 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g91B4 : block g91 4 0 1=true := g91P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91P5_0 : block g91 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g91B5 : block g91 5 0 3=true := g91P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91P6_0 : block g91 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g91B6 : block g91 6 0 1=true := g91P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91T : checkedTables g91 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g91 0 0 0 = true)
  · exact (rfl : block g91 1 0 0 = true)
  · exact (rfl : block g91 2 0 0 = true)
  · exact (rfl : block g91 3 0 0 = true)
  · exact g91B4
  · exact g91B5
  · exact g91B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91G : graphValid g91 (boundsBefore K79) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low91 : Lower true (varsX 91) (qG_ 91) 7 := lower_forest (g:=g91) (i:=0) (hints:=16842819) (before_sound K79 V79) g91G g91T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K91 := extendKnown K79 7 [(91,[]),(118,[80,32,50]),(155,[64,16,49,118]),(179,[64,16,49,83,118]),(182,[64,33,16,49,83,118]),(241,[64,16,33,99,82,115])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V91 : Known true K91 := extend_ok (m:=91) V79 low91 (by decide +kernel)
def g94Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (0x3ffc003ffc01ffe00ffffffffffffeddea003f)),(BitVec.ofNat 152 (0x80a81a8128340a4160a02a094148524c6a1249))),((BitVec.ofNat 152 (0x3fffffc00001fffff007ff001ffc0118f681c0)),(BitVec.ofNat 152 (0x15315315b158ac8a45314c6d89919918f6b6db))),((BitVec.ofNat 152 (0x3ffffffffffe00000007ffffe000031f070e00)),(BitVec.ofNat 152 (0x19c19c19c260cf1389c2704e0de2e31f0736db))),((BitVec.ofNat 152 (0xc0000000000000000007fffffffffcbfdc7007)),(BitVec.ofNat 152 (0x1e01e01e0380f01c0e0380700e0300b3942492))),(0x0,0x0),((BitVec.ofNat 152 (0xfffffffffffffffffff800000000036237fff8)),(BitVec.ofNat 152 (0x20020020000100000004008010000000004924))),(0x0,0x0),(0x0,0x0)]
def g94C : List ColumnInfo := [(4,0,90,0,5)]
def g94A : List (List Nat) := [[],[50],[65],[65,50]]
def g94D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g94L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g94D5)
  | _ => emptyPacking
def g94I (_ _ : Nat) : Option (Nat × Nat) := none
def g94 : Forest := ⟨94,5,fun i => g94Y[i]?.getD (0,0),g94C,g94A,g94L,g94I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g94P5_0 : block g94 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g94B5 : block g94 5 0 1=true := g94P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g94T : checkedTables g94 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g94 0 0 0 = true)
  · exact (rfl : block g94 1 0 0 = true)
  · exact (rfl : block g94 2 0 0 = true)
  · exact (rfl : block g94 3 0 0 = true)
  · exact (rfl : block g94 4 0 0 = true)
  · exact g94B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g94G : graphValid g94 (boundsBefore K91) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low94 : Lower true (varsX 94) (qG_ 94) 6 := lower_forest (g:=g94) (i:=0) (hints:=16868928) (before_sound K91 V91) g94G g94T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K94 := extendKnown K91 6 [(94,[]),(143,[64,16,33,50,118]),(174,[33,84,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V94 : Known true K94 := extend_ok (m:=94) V91 low94 (by decide +kernel)
def g103Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (0xe001ffc07ff01ffe003ffc07ffffd37a12000f)),(BitVec.ofNat 152 (0x48d4128d0522c8549a9128d25229934a125555))),((BitVec.ofNat 152 (0xfffe00007fffffffffc00007ff01a3a9cc0f00)),(BitVec.ofNat 152 (0x82985b16164482981305b160644d2329c83333))),((BitVec.ofNat 152 (0xffffffff80001ffffffffff800003f4479f0f0)),(BitVec.ofNat 152 (0xe01c18078700e01c01c18078701304591111))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (0x1ffffffffffffffe663f7600ff)),(BitVec.ofNat 152 (0x1301602058081301202600048000643124aaaa))),((BitVec.ofNat 152 (0xffffffffffffe0000000000000019dd38dff00)),(BitVec.ofNat 152 (0x1c01800060001c01c038020700808cd204cccc))),(0x0,0x0),(0x0,0x0)]
def g103C : List ColumnInfo := []
def g103A : List (List Nat) := [[],[16,101]]
def g103D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
def g103L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g103D4)
  | _ => emptyPacking
def g103I (_ _ : Nat) : Option (Nat × Nat) := none
def g103 : Forest := ⟨103,4,fun i => g103Y[i]?.getD (0,0),g103C,g103A,g103L,g103I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103P4_0 : block g103 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g103B4 : block g103 4 0 1=true := g103P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103T : checkedTables g103 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g103 0 0 0 = true)
  · exact (rfl : block g103 1 0 0 = true)
  · exact (rfl : block g103 2 0 0 = true)
  · exact (rfl : block g103 3 0 0 = true)
  · exact g103B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103G : graphValid g103 (boundsBefore K94) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low103 : Lower true (varsX 103) (qG_ 103) 5 := lower_forest (g:=g103) (i:=0) (hints:=16778597) (before_sound K94 V94) g103G g103T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K103 := extendKnown K94 5 [(103,[]),(117,[65,49]),(121,[64,81,50,33,32,96])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V103 : Known true K103 := extend_ok (m:=103) V94 low103 (by decide +kernel)
def g109Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (0xf003ff0ff87ff007ffff87fffcd47c560003ff)),(BitVec.ofNat 152 (0xa4280a201120a4521481102080501c1694a529))),(0x0,0x0),((BitVec.ofNat 152 (0xfffc000ffffffff801fff87fc35353a20ffc00)),(BitVec.ofNat 152 (0xc0302c40a002c060580a01010a425122318c63))),((BitVec.ofNat 152 (0xfffffff0007ffffffe00007ffcafd11df0001f)),(BitVec.ofNat 152 (0x140b002c20b0080602c220a00a741086318c6))),(0x0,0x0),((BitVec.ofNat 152 (0x7fffffffffff80004d2fe8007fe0)),(BitVec.ofNat 152 (0x982c08b044c09048130004c100d22c94a5294))),((BitVec.ofNat 152 (0xffffffffff80000000000000033aa61bff8000)),(BitVec.ofNat 152 (0xe03000c00700e0701c044702118a6118c6318))),(0x0,0x0),(0x0,0x0)]
def g109C : List ColumnInfo := [(1,0,108,0,4),(4,0,105,0,4),(8,0,101,0,4),(32,0,77,0,4),(64,0,45,0,4)]
def g109A : List (List Nat) := [[],[98,83],[32,99],[32,48,80,96],[48,101],[48,82,96,32],[80,50],[80,98,48,50],[96,32,50,83],[96,82]]
def g109D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x57d4d10
def g109D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc1a0fd20fd10
def g109H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x8
def g109D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x23440bf
def g109H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x25fe0093000000520031000000000000000000200000000026000000bb970000000000000000000000006a0000000000000000)
def g109L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g109D4)
  | 5 => (2,1,3,0,0,4,0,g109D5)
  | 6 => (1,0,3,0,0,0,0,g109D6)
  | _ => emptyPacking
def g109I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g109H5
  | 6 => lookupWord 2 53 0 8 1 3 g109H6
  | _ => fun _ => none
def g109 : Forest := ⟨109,6,fun i => g109Y[i]?.getD (0,0),g109C,g109A,g109L,g109I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109P4_0 : block g109 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g109B4 : block g109 4 0 1=true := g109P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109P5_0 : block g109 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g109B5 : block g109 5 0 2=true := g109P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109P6_0 : block g109 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g109B6 : block g109 6 0 1=true := g109P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109T : checkedTables g109 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g109 0 0 0 = true)
  · exact (rfl : block g109 1 0 0 = true)
  · exact (rfl : block g109 2 0 0 = true)
  · exact (rfl : block g109 3 0 0 = true)
  · exact g109B4
  · exact g109B5
  · exact g109B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109G : graphValid g109 (boundsBefore K103) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low109 : Lower true (varsX 109) (qG_ 109) 7 := lower_forest (g:=g109) (i:=0) (hints:=33555715) (before_sound K103 V103) g109G g109T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K109 := extendKnown K103 7 [(109,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V109 : Known true K109 := extend_ok (m:=109) V103 low109 (by decide +kernel)
def g115Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (0xc003ff0ffc3ffc00ffffffffc02b3e79000fc0)),(BitVec.ofNat 152 (0x90a80a204890a92a4291204088292e194d34d3))),((BitVec.ofNat 152 (0xfffc000fffffffff003ff0fffec8a9d703f03f)),(BitVec.ofNat 152 (0x2304c411002300c13004209020009d3145145))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (0xfffffff0003fffffffc000fffd77e88afc003f)),(BitVec.ofNat 152 (0x4c090026104c030040584120172a00828a28a))),((BitVec.ofNat 152 (0x3fffffffffff00012697f4000fc0)),(BitVec.ofNat 152 (0x2702e08b822702409826009c110691e4b2cb2c))),((BitVec.ofNat 152 (0xffffffffffc0000000000000039d530dfff000)),(BitVec.ofNat 152 (0x3803000c00380380e03808e0208d5204c30c30))),(0x0,0x0),(0x0,0x0)]
def g115C : List ColumnInfo := [(0,1,82,32,5)]
def g115A : List (List Nat) := [[],[100],[65],[65,97],[97,65],[97],[80],[80,100],[80,65],[80,65,97],[80,97,65],[80,97]]
def g115D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g115L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g115D5)
  | _ => emptyPacking
def g115I (_ _ : Nat) : Option (Nat × Nat) := none
def g115 : Forest := ⟨115,5,fun i => g115Y[i]?.getD (0,0),g115C,g115A,g115L,g115I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115P5_0 : block g115 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g115B5 : block g115 5 0 1=true := g115P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115T : checkedTables g115 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g115 0 0 0 = true)
  · exact (rfl : block g115 1 0 0 = true)
  · exact (rfl : block g115 2 0 0 = true)
  · exact (rfl : block g115 3 0 0 = true)
  · exact (rfl : block g115 4 0 0 = true)
  · exact g115B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115G : graphValid g115 (boundsBefore K109) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low115 : Lower true (varsX 115) (qG_ 115) 6 := lower_forest (g:=g115) (i:=0) (hints:=16842821) (before_sound K109 V109) g115G g115T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K115 := extendKnown K109 6 [(115,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V115 : Known true K115 := extend_ok (m:=115) V109 low115 (by decide +kernel)
def g167Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (0xffc00ffc07fe03fffe00ffc0ffff447d401c7)),(BitVec.ofNat 152 (0xa0a86a128d0a458a0546a129a2929043d49249))),((BitVec.ofNat 152 (0xfffff00007fffc07ffff0000ff81386ac0e00)),(BitVec.ofNat 152 (0xc5314c5b162c89132984c5b2c324d386adb6db))),((BitVec.ofNat 152 (0xfffffffff8000007ffffffff0000be8947038)),(BitVec.ofNat 152 (0x1c0701c180f0e1c0e0701c303c709e0949249))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (0xf0000000000000007fffffffffffe6fe67803f)),(BitVec.ofNat 152 (0x601806020301020300806000400061c212492))),(0x0,0x0),((BitVec.ofNat 152 (0xffffffffffffffff8000000000001911bbffc0)),(BitVec.ofNat 152 (0x8020080004000004010080008000000024924))),(0x0,0x0)]
def g167C : List ColumnInfo := [(1,0,166,0,5)]
def g167A : List (List Nat) := [[],[32]]
def g167D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g167L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g167D5)
  | _ => emptyPacking
def g167I (_ _ : Nat) : Option (Nat × Nat) := none
def g167 : Forest := ⟨167,5,fun i => g167Y[i]?.getD (0,0),g167C,g167A,g167L,g167I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g167P5_0 : block g167 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g167B5 : block g167 5 0 1=true := g167P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g167T : checkedTables g167 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g167 0 0 0 = true)
  · exact (rfl : block g167 1 0 0 = true)
  · exact (rfl : block g167 2 0 0 = true)
  · exact (rfl : block g167 3 0 0 = true)
  · exact (rfl : block g167 4 0 0 = true)
  · exact g167B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g167G : graphValid g167 (boundsBefore K115) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low167 : Lower true (varsX 167) (qG_ 167) 6 := lower_forest (g:=g167) (i:=0) (hints:=1397) (before_sound K115 V115) g167G g167T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K167 := extendKnown K115 6 [(167,[]),(171,[48,82,32]),(199,[16,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V167 : Known true K167 := extend_ok (m:=167) V115 low167 (by decide +kernel)
def g173Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (0xfe1ff00ff87f87ffc07fff8fffd8b95000f0ff)),(BitVec.ofNat 152 (0x1440a0a0510110028505012008488941111111))),(0x0,0x0),((BitVec.ofNat 152 (0x1ffff0007ff87fff807ff1fc2b1e600f0f00)),(BitVec.ofNat 152 (0x5882c0c1620a010b06160a0411291e43333333))),((BitVec.ofNat 152 (0x1fffffff80007fffff8001ff941fb0f0000f)),(BitVec.ofNat 152 (0x610b0505802c222c08182c48a01416b6666666))),(0x0,0x0),((BitVec.ofNat 152 (0xffe000000000007ffffffffe000be4bf000ff0)),(BitVec.ofNat 152 (0x800c06060430443010203000c20260b4444444))),(0x0,0x0),((BitVec.ofNat 152 (0xffffffffffffff8000000000006442cffff000)),(BitVec.ofNat 152 (0x100808004000402040400100000008888888))),(0x0,0x0)]
def g173C : List ColumnInfo := [(1,0,172,0,5),(4,0,169,0,5),(8,0,165,0,5),(32,0,141,0,5)]
def g173A : List (List Nat) := [[],[80,50]]
def g173D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x4e09f
def g173L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g173D6)
  | _ => emptyPacking
def g173I (_ _ : Nat) : Option (Nat × Nat) := none
def g173 : Forest := ⟨173,6,fun i => g173Y[i]?.getD (0,0),g173C,g173A,g173L,g173I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g173P6_0 : block g173 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g173B6 : block g173 6 0 1=true := g173P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g173T : checkedTables g173 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g173 0 0 0 = true)
  · exact (rfl : block g173 1 0 0 = true)
  · exact (rfl : block g173 2 0 0 = true)
  · exact (rfl : block g173 3 0 0 = true)
  · exact (rfl : block g173 4 0 0 = true)
  · exact (rfl : block g173 5 0 0 = true)
  · exact g173B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g173G : graphValid g173 (boundsBefore K167) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low173 : Lower true (varsX 173) (qG_ 173) 7 := lower_forest (g:=g173) (i:=0) (hints:=1283) (before_sound K167 V167) g173G g173T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K173 := extendKnown K167 7 [(173,[]),(203,[96,33,16,49,83]),(205,[96,32,50,83]),(214,[16,67,117,101]),(218,[16,50,66,117,101]),(229,[32,99,67]),(230,[32,16,83,67,100]),(233,[48,82,96,66,64]),(236,[32,16,49,81,65,100])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V173 : Known true K173 := extend_ok (m:=173) V167 low173 (by decide +kernel)
def g211Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (0xffc01ffff0fffc00ff0ff0ff0c8957c00f000)),(BitVec.ofNat 152 (0x22a9549452202a8aa0a212222288157c777777))),((BitVec.ofNat 152 (0xffffe01fff0fffff000ffffff2c761b0f00ff)),(BitVec.ofNat 152 (0x4030181804020300c0c4040040080613111111))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (0xffffffe0000ffffffff000fff33b526000f0f)),(BitVec.ofNat 152 (0x88c0602118448c23090098488032b104aaaaaa))),(0x0,0x0),((BitVec.ofNat 152 (0xf00000000000fffffffffff000134bf8f00ff0)),(BitVec.ofNat 152 (0x30180c06088300c0200200304014868444444))),((BitVec.ofNat 152 (0xffffffffffff00000000000000cea8c5fff000)),(BitVec.ofNat 152 (0xc0201018000c0300c08c08c0846a080888888))),(0x0,0x0)]
def g211C : List ColumnInfo := [(0,1,82,128,5),(1,0,210,0,5),(16,0,195,0,5),(2,0,209,0,4),(64,0,147,0,4),(128,1,82,0,4)]
def g211A : List (List Nat) := [[],[97]]
def g211D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x5bd4931
def g211D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc8404fd31
def g211H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x50
def g211D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x232a8bf
def g211H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0
def g211L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g211D4)
  | 5 => (1,1,3,0,0,0,0,g211D5)
  | 6 => (1,0,3,0,0,0,0,g211D6)
  | _ => emptyPacking
def g211I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g211H5
  | 6 => lookupWord 1 2 0 4 0 0 g211H6
  | _ => fun _ => none
def g211 : Forest := ⟨211,6,fun i => g211Y[i]?.getD (0,0),g211C,g211A,g211L,g211I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g211P4_0 : block g211 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g211B4 : block g211 4 0 1=true := g211P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g211P5_0 : block g211 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g211B5 : block g211 5 0 1=true := g211P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g211P6_0 : block g211 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g211B6 : block g211 6 0 1=true := g211P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g211T : checkedTables g211 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g211 0 0 0 = true)
  · exact (rfl : block g211 1 0 0 = true)
  · exact (rfl : block g211 2 0 0 = true)
  · exact (rfl : block g211 3 0 0 = true)
  · exact g211B4
  · exact g211B5
  · exact g211B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g211G : graphValid g211 (boundsBefore K173) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low211 : Lower true (varsX 211) (qG_ 211) 7 := lower_forest (g:=g211) (i:=0) (hints:=16842823) (before_sound K173 V173) g211G g211T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior508 : Lower true (varsX 508) (qG_ 508) 8 := by
  have h := lift_ok (u := true) (ms := ([16,65,66,67]).map swapRows ++ fixRows 128 0)
    (raw := varsX 508) (T := qG_ 508) (xs := [(inputs.getD 7 zero,4,132)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low109
  have card : (([(inputs.getD 7 zero,4,132)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior505 : Lower true (varsX 505) (qG_ 505) 8 := by
  have h := lift_ok (u := true) (ms := ([112,66,115,117,118]).map swapRows ++ fixRows 128 0)
    (raw := varsX 505) (T := qG_ 505) (xs := [(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low173
  have card : (([(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior501 : Lower true (varsX 501) (qG_ 501) 8 := by
  have h := lift_ok (u := true) (ms := ([67,100]).map swapRows ++ fixRows 16 0)
    (raw := varsX 501) (T := qG_ 501) (xs := [(inputs.getD 4 zero,1,17)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low173
  have card : (([(inputs.getD 4 zero,1,17)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior500 : Lower true (varsX 500) (qG_ 500) 7 := by
  have h := lift_ok (u := true) (ms := ([16,65,66,99,84,101]).map swapRows ++ fixRows 0 0)
    (raw := varsX 500) (T := qG_ 500) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low173
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior493 : Lower true (varsX 493) (qG_ 493) 8 := by
  have h := lift_ok (u := true) (ms := ([117]).map swapRows ++ fixRows 64 0)
    (raw := varsX 493) (T := qG_ 493) (xs := [(inputs.getD 6 zero,1,65)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low173
  have card : (([(inputs.getD 6 zero,1,65)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior485 : Lower true (varsX 485) (qG_ 485) 7 := by
  have h := lift_ok (u := true) (ms := ([67,100]).map swapRows ++ fixRows 0 0)
    (raw := varsX 485) (T := qG_ 485) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low173
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior477 : Lower true (varsX 477) (qG_ 477) 8 := by
  have h := lift_ok (u := true) (ms := ([16,33,67,116,117]).map swapRows ++ fixRows 128 0)
    (raw := varsX 477) (T := qG_ 477) (xs := [(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low211
  have card : (([(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior476 : Lower true (varsX 476) (qG_ 476) 7 := by
  have h := lift_ok (u := true) (ms := ([32,49,66,67,118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 476) (T := qG_ 476) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low211
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior461 : Lower true (varsX 461) (qG_ 461) 7 := by
  have h := lift_ok (u := true) (ms := ([16,33,67]).map swapRows ++ fixRows 0 0)
    (raw := varsX 461) (T := qG_ 461) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low211
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior445 : Lower true (varsX 445) (qG_ 445) 8 := by
  have h := lift_ok (u := true) (ms := ([117]).map swapRows ++ fixRows 16 0)
    (raw := varsX 445) (T := qG_ 445) (xs := [(inputs.getD 4 zero,1,17)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low173
  have card : (([(inputs.getD 4 zero,1,17)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior444 : Lower true (varsX 444) (qG_ 444) 7 := by
  have h := lift_ok (u := true) (ms := ([32,49,50,117,118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 444) (T := qG_ 444) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low211
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior441 : Lower true (varsX 441) (qG_ 441) 7 := by
  have h := lift_ok (u := true) (ms := ([112,66,117]).map swapRows ++ fixRows 0 0)
    (raw := varsX 441) (T := qG_ 441) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low173
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior429 : Lower true (varsX 429) (qG_ 429) 7 := by
  have h := lift_ok (u := true) (ms := ([117]).map swapRows ++ fixRows 0 0)
    (raw := varsX 429) (T := qG_ 429) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low173
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior413 : Lower true (varsX 413) (qG_ 413) 7 := by
  have h := lift_ok (u := true) (ms := ([112,33,66,115,117,118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 413) (T := qG_ 413) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low211
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior381 : Lower true (varsX 381) (qG_ 381) 8 := by
  have h := lift_ok (u := true) (ms := ([16,65,66,67]).map swapRows ++ fixRows 1 0)
    (raw := varsX 381) (T := qG_ 381) (xs := [(inputs.getD 0 zero,8,9)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low109
  have card : (([(inputs.getD 0 zero,8,9)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior380 : Lower true (varsX 380) (qG_ 380) 7 := by
  have h := lift_ok (u := true) (ms := ([16,65,66,67]).map swapRows ++ fixRows 0 0)
    (raw := varsX 380) (T := qG_ 380) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low109
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior377 : Lower true (varsX 377) (qG_ 377) 7 := by
  have h := lift_ok (u := true) (ms := ([112,66,115,117,118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 377) (T := qG_ 377) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low173
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior365 : Lower true (varsX 365) (qG_ 365) 7 := by
  have h := lift_ok (u := true) (ms := ([16,33,99,100,117]).map swapRows ++ fixRows 0 0)
    (raw := varsX 365) (T := qG_ 365) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low211
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior349 : Lower true (varsX 349) (qG_ 349) 7 := by
  have h := lift_ok (u := true) (ms := ([16,33,67,116,117]).map swapRows ++ fixRows 0 0)
    (raw := varsX 349) (T := qG_ 349) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low211
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior504 : Lower true (varsX 504) (qG_ 504) 6 := by
  have h := lift_ok (u := true) (ms := ([33,50,83,84,117,118]).map swapRows ++ fixRows 40 0)
    (raw := varsX 504) (T := qG_ 504) (xs := [(inputs.getD 3 zero,32,40),(inputs.getD 5 zero,8,40)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 3 zero,32,40),(inputs.getD 5 zero,8,40)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior497 : Lower true (varsX 497) (qG_ 497) 6 := by
  have h := lift_ok (u := true) (ms := ([16]).map swapRows ++ fixRows 160 0)
    (raw := varsX 497) (T := qG_ 497) (xs := [(inputs.getD 5 zero,1,33),(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 5 zero,1,33),(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior496 : Lower true (varsX 496) (qG_ 496) 5 := by
  have h := lift_ok (u := true) (ms := ([33,50,83,84,117,118]).map swapRows ++ fixRows 32 0)
    (raw := varsX 496) (T := qG_ 496) (xs := [(inputs.getD 5 zero,128,160)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 5 zero,128,160)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior492 : Lower true (varsX 492) (qG_ 492) 6 := by
  have h := lift_ok (u := true) (ms := ([33,84,118]).map swapRows ++ fixRows 72 0)
    (raw := varsX 492) (T := qG_ 492) (xs := [(inputs.getD 3 zero,32,40),(inputs.getD 6 zero,8,72)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 3 zero,32,40),(inputs.getD 6 zero,8,72)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior489 : Lower true (varsX 489) (qG_ 489) 6 := by
  have h := lift_ok (u := true) (ms := ([16,67,101]).map swapRows ++ fixRows 192 0)
    (raw := varsX 489) (T := qG_ 489) (xs := [(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior484 : Lower true (varsX 484) (qG_ 484) 5 := by
  have h := lift_ok (u := true) (ms := ([33,84,118]).map swapRows ++ fixRows 64 0)
    (raw := varsX 484) (T := qG_ 484) (xs := [(inputs.getD 6 zero,128,192)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 6 zero,128,192)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior481 : Lower true (varsX 481) (qG_ 481) 5 := by
  have h := lift_ok (u := true) (ms := ([16,84,118]).map swapRows ++ fixRows 64 0)
    (raw := varsX 481) (T := qG_ 481) (xs := [(inputs.getD 6 zero,1,65)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 6 zero,1,65)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior473 : Lower true (varsX 473) (qG_ 473) 6 := by
  have h := lift_ok (u := true) (ms := ([16,67]).map swapRows ++ fixRows 144 0)
    (raw := varsX 473) (T := qG_ 473) (xs := [(inputs.getD 4 zero,1,17),(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 4 zero,1,17),(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior472 : Lower true (varsX 472) (qG_ 472) 5 := by
  have h := lift_ok (u := true) (ms := ([33,50,83,84,117,118]).map swapRows ++ fixRows 8 0)
    (raw := varsX 472) (T := qG_ 472) (xs := [(inputs.getD 3 zero,64,72)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 3 zero,64,72)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior469 : Lower true (varsX 469) (qG_ 469) 6 := by
  have h := lift_ok (u := true) (ms := ([16]).map swapRows ++ fixRows 132 0)
    (raw := varsX 469) (T := qG_ 469) (xs := [(inputs.getD 2 zero,16,20),(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 2 zero,16,20),(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior468 : Lower true (varsX 468) (qG_ 468) 5 := by
  have h := lift_ok (u := true) (ms := ([33,118]).map swapRows ++ fixRows 64 0)
    (raw := varsX 468) (T := qG_ 468) (xs := [(inputs.getD 6 zero,16,80)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 6 zero,16,80)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior465 : Lower true (varsX 465) (qG_ 465) 5 := by
  have h := lift_ok (u := true) (ms := ([16]).map swapRows ++ fixRows 128 0)
    (raw := varsX 465) (T := qG_ 465) (xs := [(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior464 : Lower true (varsX 464) (qG_ 464) 4 := by
  have h := lift_ok (u := true) (ms := ([33,50,83,84,117,118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 464) (T := qG_ 464) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior457 : Lower true (varsX 457) (qG_ 457) 5 := by
  have h := lift_ok (u := true) (ms := ([16,67]).map swapRows ++ fixRows 128 0)
    (raw := varsX 457) (T := qG_ 457) (xs := [(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior453 : Lower true (varsX 453) (qG_ 453) 5 := by
  have h := lift_ok (u := true) (ms := ([16,84,117,118]).map swapRows ++ fixRows 4 0)
    (raw := varsX 453) (T := qG_ 453) (xs := [(inputs.getD 2 zero,128,132)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 2 zero,128,132)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior449 : Lower true (varsX 449) (qG_ 449) 4 := by
  have h := lift_ok (u := true) (ms := ([16,84,117,118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 449) (T := qG_ 449) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior437 : Lower true (varsX 437) (qG_ 437) 6 := by
  have h := lift_ok (u := true) (ms := ([16,118]).map swapRows ++ fixRows 36 0)
    (raw := varsX 437) (T := qG_ 437) (xs := [(inputs.getD 2 zero,16,20),(inputs.getD 5 zero,1,33)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 2 zero,16,20),(inputs.getD 5 zero,1,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior436 : Lower true (varsX 436) (qG_ 436) 5 := by
  have h := lift_ok (u := true) (ms := ([33,118]).map swapRows ++ fixRows 32 0)
    (raw := varsX 436) (T := qG_ 436) (xs := [(inputs.getD 5 zero,4,36)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 5 zero,4,36)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior433 : Lower true (varsX 433) (qG_ 433) 5 := by
  have h := lift_ok (u := true) (ms := ([16,118]).map swapRows ++ fixRows 32 0)
    (raw := varsX 433) (T := qG_ 433) (xs := [(inputs.getD 5 zero,1,33)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 5 zero,1,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior428 : Lower true (varsX 428) (qG_ 428) 5 := by
  have h := lift_ok (u := true) (ms := ([33,84,118]).map swapRows ++ fixRows 8 0)
    (raw := varsX 428) (T := qG_ 428) (xs := [(inputs.getD 3 zero,32,40)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 3 zero,32,40)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior425 : Lower true (varsX 425) (qG_ 425) 5 := by
  have h := lift_ok (u := true) (ms := ([16,67,101]).map swapRows ++ fixRows 128 0)
    (raw := varsX 425) (T := qG_ 425) (xs := [(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior421 : Lower true (varsX 421) (qG_ 421) 5 := by
  have h := lift_ok (u := true) (ms := ([16,84,118]).map swapRows ++ fixRows 4 0)
    (raw := varsX 421) (T := qG_ 421) (xs := [(inputs.getD 2 zero,32,36)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 2 zero,32,36)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior420 : Lower true (varsX 420) (qG_ 420) 4 := by
  have h := lift_ok (u := true) (ms := ([33,84,118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 420) (T := qG_ 420) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior417 : Lower true (varsX 417) (qG_ 417) 4 := by
  have h := lift_ok (u := true) (ms := ([16,84,118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 417) (T := qG_ 417) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior409 : Lower true (varsX 409) (qG_ 409) 5 := by
  have h := lift_ok (u := true) (ms := ([16,118]).map swapRows ++ fixRows 8 0)
    (raw := varsX 409) (T := qG_ 409) (xs := [(inputs.getD 3 zero,1,9)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 3 zero,1,9)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior405 : Lower true (varsX 405) (qG_ 405) 5 := by
  have h := lift_ok (u := true) (ms := ([16,118]).map swapRows ++ fixRows 4 0)
    (raw := varsX 405) (T := qG_ 405) (xs := [(inputs.getD 2 zero,16,20)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 2 zero,16,20)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior404 : Lower true (varsX 404) (qG_ 404) 4 := by
  have h := lift_ok (u := true) (ms := ([33,118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 404) (T := qG_ 404) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior401 : Lower true (varsX 401) (qG_ 401) 4 := by
  have h := lift_ok (u := true) (ms := ([16,118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 401) (T := qG_ 401) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior373 : Lower true (varsX 373) (qG_ 373) 6 := by
  have h := lift_ok (u := true) (ms := ([16]).map swapRows ++ fixRows 36 0)
    (raw := varsX 373) (T := qG_ 373) (xs := [(inputs.getD 2 zero,16,20),(inputs.getD 5 zero,1,33)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 2 zero,16,20),(inputs.getD 5 zero,1,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior369 : Lower true (varsX 369) (qG_ 369) 5 := by
  have h := lift_ok (u := true) (ms := ([16]).map swapRows ++ fixRows 32 0)
    (raw := varsX 369) (T := qG_ 369) (xs := [(inputs.getD 5 zero,1,33)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 5 zero,1,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior361 : Lower true (varsX 361) (qG_ 361) 5 := by
  have h := lift_ok (u := true) (ms := ([16,67,101]).map swapRows ++ fixRows 64 0)
    (raw := varsX 361) (T := qG_ 361) (xs := [(inputs.getD 6 zero,1,65)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 6 zero,1,65)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior345 : Lower true (varsX 345) (qG_ 345) 5 := by
  have h := lift_ok (u := true) (ms := ([16,67]).map swapRows ++ fixRows 16 0)
    (raw := varsX 345) (T := qG_ 345) (xs := [(inputs.getD 4 zero,1,17)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 4 zero,1,17)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior341 : Lower true (varsX 341) (qG_ 341) 5 := by
  have h := lift_ok (u := true) (ms := ([16]).map swapRows ++ fixRows 4 0)
    (raw := varsX 341) (T := qG_ 341) (xs := [(inputs.getD 2 zero,16,20)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 2 zero,16,20)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior337 : Lower true (varsX 337) (qG_ 337) 4 := by
  have h := lift_ok (u := true) (ms := ([16]).map swapRows ++ fixRows 0 0)
    (raw := varsX 337) (T := qG_ 337) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior329 : Lower true (varsX 329) (qG_ 329) 4 := by
  have h := lift_ok (u := true) (ms := ([16,67]).map swapRows ++ fixRows 0 0)
    (raw := varsX 329) (T := qG_ 329) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior317 : Lower true (varsX 317) (qG_ 317) 6 := by
  have h := lift_ok (u := true) (ms := ([16,67,101]).map swapRows ++ fixRows 20 0)
    (raw := varsX 317) (T := qG_ 317) (xs := [(inputs.getD 2 zero,16,20),(inputs.getD 4 zero,1,17)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 2 zero,16,20),(inputs.getD 4 zero,1,17)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior313 : Lower true (varsX 313) (qG_ 313) 5 := by
  have h := lift_ok (u := true) (ms := ([16,67,101]).map swapRows ++ fixRows 16 0)
    (raw := varsX 313) (T := qG_ 313) (xs := [(inputs.getD 4 zero,1,17)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 4 zero,1,17)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior301 : Lower true (varsX 301) (qG_ 301) 5 := by
  have h := lift_ok (u := true) (ms := ([16,67,101]).map swapRows ++ fixRows 4 0)
    (raw := varsX 301) (T := qG_ 301) (xs := [(inputs.getD 2 zero,32,36)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 2 zero,32,36)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior297 : Lower true (varsX 297) (qG_ 297) 4 := by
  have h := lift_ok (u := true) (ms := ([16,67,101]).map swapRows ++ fixRows 0 0)
    (raw := varsX 297) (T := qG_ 297) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior460 : Lower true (varsX 460) (qG_ 460) 4 := by
  have h := lift_ok (u := true) (ms := ([16,65,100,117]).map swapRows ++ fixRows 0 0)
    (raw := varsX 460) (T := qG_ 460) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low45
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior440 : Lower true (varsX 440) (qG_ 440) 4 := by
  have h := lift_ok (u := true) (ms := ([16,65,98,100,101,118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 440) (T := qG_ 440) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low45
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior397 : Lower true (varsX 397) (qG_ 397) 4 := by
  have h := lift_ok (u := true) (ms := ([101,118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 397) (T := qG_ 397) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low45
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior376 : Lower true (varsX 376) (qG_ 376) 4 := by
  have h := lift_ok (u := true) (ms := ([16,65,98,67,100,101]).map swapRows ++ fixRows 0 0)
    (raw := varsX 376) (T := qG_ 376) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low45
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior372 : Lower true (varsX 372) (qG_ 372) 4 := by
  have h := lift_ok (u := true) (ms := ([16,65,66,99,84,101]).map swapRows ++ fixRows 0 0)
    (raw := varsX 372) (T := qG_ 372) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low45
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior364 : Lower true (varsX 364) (qG_ 364) 4 := by
  have h := lift_ok (u := true) (ms := ([16,65,67,100]).map swapRows ++ fixRows 0 0)
    (raw := varsX 364) (T := qG_ 364) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low45
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior357 : Lower true (varsX 357) (qG_ 357) 4 := by
  have h := lift_ok (u := true) (ms := ([67,100]).map swapRows ++ fixRows 0 0)
    (raw := varsX 357) (T := qG_ 357) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low45
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior348 : Lower true (varsX 348) (qG_ 348) 4 := by
  have h := lift_ok (u := true) (ms := ([16,65,50,101]).map swapRows ++ fixRows 0 0)
    (raw := varsX 348) (T := qG_ 348) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low45
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior316 : Lower true (varsX 316) (qG_ 316) 4 := by
  have h := lift_ok (u := true) (ms := ([16,65,66,67]).map swapRows ++ fixRows 0 0)
    (raw := varsX 316) (T := qG_ 316) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low45
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
def generatedKnown : List (Nat × Nat) := [(508,8),(505,8),(501,8),(500,7),(493,8),(485,7),(477,8),(476,7),(461,7),(445,8),(444,7),(441,7),(429,7),(413,7),(381,8),(380,7),(377,7),(365,7),(349,7),(504,6),(497,6),(496,5),(492,6),(489,6),(484,5),(481,5),(473,6),(472,5),(469,6),(468,5),(465,5),(464,4),(457,5),(453,5),(449,4),(437,6),(436,5),(433,5),(428,5),(425,5),(421,5),(420,4),(417,4),(409,5),(405,5),(404,4),(401,4),(373,6),(369,5),(361,5),(345,5),(341,5),(337,4),(329,4),(317,6),(313,5),(301,5),(297,4),(460,4),(440,4),(397,4),(376,4),(372,4),(364,4),(357,4),(348,4),(316,4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem generatedPrior : Known true generatedKnown := by
  intro e h
  simp only [generatedKnown, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact prior508
  · exact prior505
  · exact prior501
  · exact prior500
  · exact prior493
  · exact prior485
  · exact prior477
  · exact prior476
  · exact prior461
  · exact prior445
  · exact prior444
  · exact prior441
  · exact prior429
  · exact prior413
  · exact prior381
  · exact prior380
  · exact prior377
  · exact prior365
  · exact prior349
  · exact prior504
  · exact prior497
  · exact prior496
  · exact prior492
  · exact prior489
  · exact prior484
  · exact prior481
  · exact prior473
  · exact prior472
  · exact prior469
  · exact prior468
  · exact prior465
  · exact prior464
  · exact prior457
  · exact prior453
  · exact prior449
  · exact prior437
  · exact prior436
  · exact prior433
  · exact prior428
  · exact prior425
  · exact prior421
  · exact prior420
  · exact prior417
  · exact prior409
  · exact prior405
  · exact prior404
  · exact prior401
  · exact prior373
  · exact prior369
  · exact prior361
  · exact prior345
  · exact prior341
  · exact prior337
  · exact prior329
  · exact prior317
  · exact prior313
  · exact prior301
  · exact prior297
  · exact prior460
  · exact prior440
  · exact prior397
  · exact prior376
  · exact prior372
  · exact prior364
  · exact prior357
  · exact prior348
  · exact prior316
def generatedSamples : Array (Bits × Bits) := #[(BitVec.ofNat 152 (0x3e0f0f3f800300700383f8000cc100f11333f), BitVec.ofNat 152 (0x20050400000050010048488000440005011115)),(BitVec.ofNat 152 0, BitVec.ofNat 152 0),(BitVec.ofNat 152 (0x1c00030c0003c00007c7c010037064cc29cdcc), BitVec.ofNat 152 (0xe12d1c50d101d42b0accc990015024cc09454c)),(BitVec.ofNat 152 (0x30c00380000f8f80007a1338088f0ce0e0f), BitVec.ofNat 152 (0x4478b3ba4496a19898819721338008504a0e0a)),(BitVec.ofNat 152 (0xe01c000fc01c0f000007f8023c030f00f00ff0), BitVec.ofNat 152 (0xcc26120082c03103113320214010900f00aa0)),(BitVec.ofNat 152 (0xff000e00000fff80043c003f000fff000), BitVec.ofNat 152 (0x1a8240052a680a44653220424003d000b4a000)),(BitVec.ofNat 152 (0x1ff00007000fff0000007c0003ffff000000), BitVec.ofNat 152 (0x93000845b3410c66462400540002f6aa000000)),(BitVec.ofNat 152 (0xffe0000007fff0000000007ffffc0000000000), BitVec.ofNat 152 (0x10828a0492208080000429aaa80000000000)),(BitVec.ofNat 152 0, BitVec.ofNat 152 0)]
def generatedColumns : List ColumnInfo := [(1,0,508,0,8),(4,0,505,0,8),(8,0,501,0,8),(9,0,500,0,7),(16,0,493,0,8),(24,0,485,0,7),(32,0,477,0,8),(33,0,476,0,7),(48,0,461,0,7),(64,0,445,0,8),(65,0,444,0,7),(68,0,441,0,7),(80,0,429,0,7),(96,0,413,0,7),(128,0,381,0,8),(129,0,380,0,7),(132,0,377,0,7),(144,0,365,0,7),(160,0,349,0,7),(5,0,504,0,6),(12,0,497,0,6),(13,0,496,0,5),(17,0,492,0,6),(20,0,489,0,6),(25,0,484,0,5),(28,0,481,0,5),(36,0,473,0,6),(37,0,472,0,5),(40,0,469,0,6),(41,0,468,0,5),(44,0,465,0,5),(45,0,464,0,4),(52,0,457,0,5),(56,0,453,0,5),(60,0,449,0,4),(72,0,437,0,6),(73,0,436,0,5),(76,0,433,0,5),(81,0,428,0,5),(84,0,425,0,5),(88,0,421,0,5),(89,0,420,0,4),(92,0,417,0,4),(100,0,409,0,5),(104,0,405,0,5),(105,0,404,0,4),(108,0,401,0,4),(136,0,373,0,6),(140,0,369,0,5),(148,0,361,0,5),(164,0,345,0,5),(168,0,341,0,5),(172,0,337,0,4),(180,0,329,0,4),(192,0,317,0,6),(196,0,313,0,5),(208,0,301,0,5),(212,0,297,0,4),(49,0,460,0,4),(69,0,440,0,4),(112,0,397,0,4),(133,0,376,0,4),(137,0,372,0,4),(145,0,364,0,4),(152,0,357,0,4),(161,0,348,0,4),(193,0,316,0,4)]
def genData5 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x271329649a411a8a43a11027e3d9e0ea72379b0d26631980ba5a2b950a24e259208a421f8f07236198c05a2a13890421e0d8602a1207830120601801f80551305954358910f886e6ab2ea81ac4887a115858d4059543443d08aa2c6c02caa1a21e2861e485837458910f122d0ba260bb286887891685cd405d943443b40a1ac4c82c899221da04e1466414358910ec82b2982caa1ac4887621595016550d62443a28abf26b02cbb9a21c945639358165dcd10dd0348b1260b2264886e81a44e16050d62443740d226eb0286b1221ba0691305954358910dc8746ab2ea81ac4886e11a65513059543443649d22ec9ba08b1a21ae060ca461d0358910d4a34cac260b2a868866a3a46598741162443350d2320b2a86b12217a0ed9375014358910bd07689c2c881ac4885e81b39216440d62442f20dac6eb2a06b12217286de485837458910b92367ba2ce822c6885aa0b461d6060d62442b8859b2aa02ecaa2215a8ed3964117358910ad4768cc2c1b9ac48856a3b4661605d162442b51da330b02e6b12215a86d1606554358910ad4168cc2c0b9ac4885663b5661605cd62442b305ab30b02e6b12215702dd984c14358910a9c76ecc2c0a1ac48854e0b76616050d624428d85bb30a02caa1a213e0ed1a88dd03589109d836d53a7081ac4884ea3b668e4741162442571d93493420cbaa211f0ec9a4e4d7540d108f2768d1726bb206884793b36a647595044423c9d9b4bca2ec822211b86ea985817358910)
def genData6 (j : Nat) : Nat := if 7 ≤ j then 0 else (if j<3 then (if j<1 then (0x10abca9d6841953442af1a899d0654d10abc6968758163442af1a59a1065cd10abc6926841975442af1a49a1065cd10abc68e8758165442af1a39a1065d510abc68a6841975442af1a29a1065cd10ab9e998749952442ae7a661d264c910ab669983419544c27e3a961503589109f8e8997551034427e3a065783589109f86a78740d624427e1a0e5d83589109f868397499324427e1a0a6373589109f8682985cd624427d3a365d65411109f4e8d97595034427d3a365d6440d109f4e8d97551034427d1a98dd6540d109f469b935d5034427d1a5e4d7640d109f4693935d9034427d1a4e4d7540d109f468b935d9034427d0a365d65411109ece999391d044427b3a564e47411109ece9197595044427b3a365106551109ec6a647595044427b1a6e5175411109ec697945d9044427b1a4e5d65411109ec69393595044427b1a4e4565411109ec68f945d9044427b1a3e5175411109e9e9198dcd624427a7a466174589109e9e91985cd624427a4a466173589109dc6839755954442767a566173589109d9295985cd62442754a365576551109bce959399d064426e7a665d53589109b9e999750d624426e7a664f74589109b9aa5645cd624426e6a8e5973589109b969b985cd624426e5a6a5f83589109b969a9760d624426e5a5e5973589109b9693965cd624425e7a7661435891097929d9850d624425d5a7e4d65dcd108fce81985d9544423f3a066176549108fce81985d9324423f3a06617550d108fcaa7805d9524423f1a9e1d03589108fc6a397595044423f1a0e6165dd1108fc68398597724423f1a0e61655d1108fc68398595724423f1a0e5d86551108fc68397619524423f1a0e5d864c9108fc68397615434423f1a0a6175589108fc682985cd624423e7a266176551108f9e89985d5434423e7a2653865d5108f9e8994e0d754423e5a6e4987551108f5e8d985d9544423d7a36617654d108f5e8d985d9524423d7a366165dd1108f5e8d95e11764423d4a366176551108f528d98597744423d4a3657845d9108ede91985d9524423b7a4661764c9108ede9197e15624423b7a464b835d9108dde95985d9324422f7a66617550d108bd299985d5434421f7a76616550d1087de9d98591324421f7a1663755913087de85985d9544c21f7a165b805d54387de8594e15764c21f4a76616550d1087be89985d9544421efa26617550d1087be8995e19744c21efa2653865d51087be8994e0d754421eda6e49875513087b69b9261d544421dfa36617655110877e8d98597744421dfa3657845d91086fe91985d9324421bfa464b835d91085fe95985d9324420ffa66617550d10fa05193050d62443e41564c15358910e38e1e87581624436a1466414358910d945959341953442ea3a461d6058910ba86916050d62442ea0a461d6058910) else (if j<2 then (0x9110cece61405d5434433b298501645cd10ceca6140551734433b1985016550d10cec66140591324433b1946016550d10cec50396615434433b140e4d8655110cd6661504d9544c33599560d0655130cd556393597734432f3985817559110cbce61605d5634432f3985817558910cbce61605cd624432f298581655cd10cbca6160591734432f2975838359510cbc9a50660f754432f26941983dd110cbc9a50660f724432f1985816550d10cbc66160591324432f1606538359510cbc58193e11624432f0985817558910cbc261605cd62442fc3a54e10358910bf0e913840d62442fc3a361d0358910bf0e8d7540d62442fc2a74e10358910bf06a23740d62442fc1a58dd0358910bf068f8740d62442fc1a3e150358910bf068f8440d62442fc1a3a610358910bf068c8740d62442fc0a74e10358910be8e918741162442fa3a461d0358910be86a24741162442fa1a591d0458910be868e4741162442fa0a461d0358910be4e993750143442f93a44dd0458d10be46913059132442f91a391d0458d10be468d0651543442f63a56610358910bd4e99574c153442f53a355d6540d10bd46963759503442f33a655d4055110bcce915759504442f31a591d6541110bcc6964741153442ee3a461d6058910bb8e8d8758162442ee1a8a1d6058910bb869a8740d62442ee1a64118358910bb8699045cd62442ee1a64115358910bb86968758162442ee1a589d6058910bb868e8758162442ee1a389d6058910bb868c8758162442ed3a64dd0650d10bb4e95674c163442ed3a54dd6058d10bb4e913758163442ed3a361d6059510bb46993059543442ec7a64dd4358910bace918758162442eb1a691d0458d10bac6916050d62442ea5a45954358910ba669943419544c2e73a655d0655110b9ce995741953442e73a455d6059510b9ce8d5758165442e71a5a1d6059510b9c6966741953442e65a589d6558910b74e8d765d503442dd1a6dcd7540d10b74697735d903442db1a5dd17641110b6c68f745d904442da5a79237458910b3c6966741973442cf1a399d065d510b35e95764dd63442cbba551d6059130b1ee915758165442be3a26558059110af8e899560143442be3a261d0655110af86838760d62442bd3a361d0358910af469a874c153442bd1a5a1d3058d10af468f8740d62442bd1a3e110358910af468f8140d62442bd1a34198550d10aece998051543442bb3a461d0458d10aece918741153442bb3a461d0358910aec6a24741163442bb1a891d0454d10aec6a10651543442bb1a6921045cd10aec6964841173442bb1a44198550d10ae92918760d62442b73a56498058d10ad6e9983541544c2af3a661d0655110abce998741953442af3a661d0654910abce998741943442af3a661d064c910abce916841932442af3a35a106551) else (0x55cd10e3661d63419544c38d96341b855d130e3658d06613754c38d57858d7654d10e355e1635d9434438d5685cd7650d10e2e611605d5635038b96851d0655130e2e59187419544c38b96461d0655110e2d5e1645d9544438b5785917650d10e2d5a1745d9434438b56461d1655110e2d591815d9544438796855d0655110e1e59587419544438795858165dd110df0e5d30499324437c3914c1264c910df0a5d3054d624437c1984c15358910df06613050d624437c193499044c910df0649305d9324437c1924c1164c910df04e39440d624437c1386414358910de8925045cd624437a1985014358910de85019550d62443793935017550d10de4e4d4059543443791944dd0650d10de4651305d943443791944c17550d10de46513059543443791944c11550d10de464d4741943443791935017650d10de451f964c14344379143641644c910dd465530dd953443751954c37454d10dd4655305d9534437519355d0654d10dcce5d4055954443733915015655110dcc655405d954443731955011655110dcc6515741954443731945450655110dc665543419544c3719945413655130db8e61605cd624436e3975818358910db8e59045cd624436e3925817558910db8e49605cd624436e2985837358910db8a61605cd624436e2975838358910db8a5d6060d624436e2975815358910db868d96411624436e1985837458910db866160dcd624436e1985817458910db8661605cd624436e1985814358910db865d60e0d624436e1975815358910db865d6050d624436e19661d0458910db86416550d624436e162641644c910db85839560d624436e160e557358910db85839460d624436e160e517358910db858195e0d624436e1606577458910db858195dcd624436e1606554358910db858193dd1624436e0985817358910db825d6060d624436d39358165dcd10db4e4d60595434436d1964c37558d10db465930dd1634436d1964c17558d10db464d60dd5634436d1935837458d10db459f944c1634436b1945816550d10dac5199050d624436a6495918358910da95199750d62443665595954358910d9665563419544c36559558d7654d10d74e4d765d5034435d1798dd6540d10d6ce51765d50444355557e4d65dcd10d3ca5d60595734434f269419755cd10d39e5b755cd624434e7965d57358910d3565973dd5634434d5965cd7558d10d355db954dd634434d576e513758d10d355d993dd5634434d57664f7458d10d2e65160dd5644c33d3984c17654d10cf4e61305d9434433d3984c1764c910cf4e61305d5634433d3984c17550d10cf4e4d805d5434433d2974c18654d10cf466130595434433d1984c1644c910cf464d86411324433d130e598550d10cf44c394619324433b3985017655110cece61405d9434433b398501755))) else (if j<5 then (if j<4 then (0x17558910f38583755cd62443ce1605d77358910f38581755cd62443cd1764dd0458d10f345d930dd563443cd1764c37458d10f345d9305d563443cd1764c17458d10f345cd60dd563443cd1735817558d10f2cdd16741163443cb17651d6440d10f2c5d9405d564443cb167501645cd10f2c59d4045564443c994758d0655130f2651d60591324c3c99345817558d40f255d1635d943443c95645cd7650d10f1cdd95741953443c715758165dcd10f1c55d6059772443c7157581655cd10f1c55d6059572443c71575816544910f1955b725d562443c65565c97558910f1695d63419544c3c557558d7654d10f15559735d563443c396591d0655110f0e59257419544c3c396455d0655110f0d5d5645d954443c356455d1655110f0d591515d954443c1d6551d3655130ef060f8740d62443bc183e150358910ef060d8740d62443bc1836150358910ef04c12661132443bc1274c1864c910ef04853061932443ba18461d0458910ee85212641132443b92484c14358910ee46013651543443b91474c18650d10ee450d8641132443b91404d98550d10ee44dd4061943443b91306194550d10ee44c14661543443b51584c17550d10ed45613059543443b51584c11550d10ed455d3061953443b3258501545cd10ecc561405d543443b31585016550d10ecc5614045543443b31575018655110ecc551805d543443b31546016550d10ecc5518045543443b31515018655110ec660d50519544c3ae3875818358910eb861d60e0d62443ae1875818358910eb85a12741932443ae168485064c910eb85898741952443ae16261d064c910eb85898141932443ae162419844c910eb849d60e0d62443ad1684dd0650d10eb45a1305d943443ad1684c163dc910eb45a1064d132443ad16361d0654d10eb458d8741943443ad1636017650d10eb458d8059543443ad1634198550d10eb44e16058f72443ab2485814358910eac5a14741943443ab1685017650d10eac5a10651543443ab16461d0655110eac5918741943443ab1646050655110eac591805d943443ab1644198550d10ea65a143419544c3a996460d0655130ea658d8441953503a716855d0655110e9c5a15741953443a71685450655110e9c5958741954443a716561d0654d10e9c5958141954443a715858165dd110e9c5616059773443a715858165dc910e9c5616059543443a71575838459510e9c55d60e0d65443a71566017558d10e9c5598055163443a596560d0655130e9658d8541943543a556561d3654d10e9556163595434439e387a1d0358910e789e22740d624439d3784c17654d10e74de1305d5634439b2485d9045cd10e6961e48dd162443959835417655130e56561305d5434438f3785817558d10e3cdd987419534438f26841b755cd10e3c9a1065d5734438f26741b8) else (0x2448f246122490c47d23d11dc8e847123711ac8d0465231117c8b845922b113489444721f10d485841d20d105c82840b20410147f83f31f50f847b03cf1e60f0c7803bd1dd0edc7683b11d70eac7503a51d10e7c7383991cb0e4c6fc37b1b60da46cc3571a70d2c6903451a10cfc67833919b0ccc66032d1920c8463c3151890c3c6183091800bdc5e82f11770bac5d02e51710b7c5b82d916b0b4c5a02c715f0aec5702b51590abc5582a91530a8c54029d14d0a5c5282911470a1450427f13e09e44ec27313809b44d4267132096c4b0255129093c498249123090c48023d11d08c4450225111087c43821910b084c42020d105081c4082010ff07ec3f01f50f907bc3d81e90f3078c3c01dd0ed075c3a81d10e7072c3901c50e106fc3781b90db06cc3601ad0d2066c3241890c3060c30017d0ba05ac2d01650b1057c2b81590ab054c2a014d0a5051c28814109f04ec27013509904bc258129093048c24011d08d045c228111087042c21010508103fc1f80f907b03cc1e00ed075039c1c80e106f036c1b00d5069033c1980c9063030c1800bd05d02dc16809904801d40c004501b0054000fe09213050d62443f81474c14358910fe050d2641132443f81385014358910fe04dd4050d62443f41574c15358910fc4551305d543443f11544c16550d10fc45513045543443ec2375950358910fb05893059132443ec162419344c910fb04e16440d62443ec1385814358910fb04dd6050d62443ec1305954358910fa8e918758162443ea2485910358910fa892160dd162443ea2485814358910fa85894059132443ea1605154358910fa85256440d62443ea1475814358910fa85198741162443ea1465d10358910fa85190460d62443ea1464117358910fa85190454d62443ea1405954358910fa82918758162443e91644dd0650d10fa4591305d943443e916351d0650d10fa458d405d943443e91635016550d10fa458d0651543443e91464c14358910fa450d6059132443e85464dd4358910fa150d6259132443e85385194358910f9855d6054d62443e61565d50358910f985590454d62443e51654d90454d10f9458d5741953443e51564c17558d10f945593055163443e316591d0655110f8c5915741954443e31645450655110f8c5594055163443e31545816550d10f895516550d62443e196550d0655130f8658d4541943543e155458d6550d10f70dcd7540d62443da37461d0458910f645d1305d943443d91735017650d10f645cd405d543443d51758dd6540d10f545d530dd953443d51754c17654d10f4c5d5405d954443d3157501545cd10f4c545405d954443d19544c17550d10f4650d505d9544c3d15545cd7550d10f455513745543443d15544c57550d10f38dc9605d562443ce1785837458910f385e1605d162443ce17258)) else (if j<6 then (0x8412850407ca1420121414850400a10400281c100a20101f288080000a0704000a30188804a3010281c10281c1012481a0b0682010000248010000283c10af891080000fc0d420159070846c05683c341e050641000527a0f0948283c281550708000000c1c192060f0800000248183c202244100088c06220188c0683c1a0f0400062010048183c200003704088c04000000000000000000000000000000081f04000c1c10000000000000000281c10000000000000000000207c1000a0f0683c18850541e2142000000541000485052141485052141891060541000541000000000000000000000000815c0f5070c011b01508002480a4823070400000000000000009200400162010000005070703c10000000000000000000141c102d040000000000000000000000000d410000000000000000141c10000000000000000209418190400000000000000000000000000000000000000000000000000000000000009270648019200648010000005270548010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000124862041e80c418c042bc46c44f03c44921881070e05843ca310284815c0f0810483ec2962161850b311b5070f30d974cb1654327d92cc8d645321d908c7563631758a8c4562130cd860c2d6123085830c0f6032fc57d0be55ee2f657a0bc75e22f0577cbb55d62ea5740b9d5ca2e2d704b795b82db56d4b675b22d856a4b495a32cf5674b3759a2cc5650b2558b2c4d620b075822c055fcaf55732b755a8acb55e2ab553ca9b5492a25500a7d53d29c54dca6b53429954c4a5f52e29654a0a47522290547ca3b51c28d5464a2f51628a544ca235102875434a1750a2845410a0550127e53e09e74f227853bc9d54e927253809bd4da26ad3389994c826353149814bf25ed2e496f4b6258d2c09574aa254529093f49e24cd26092d495248523090f48623f51dc8e5471237d1ac8cd46222ed1648a9450227513489144421fd0ec87343521850bc85b42c21550a484f42320f50748314142095038813405201cffc7fb3fc1fd4fe47e93f01f5cfa87d13e71f2cf907c53de1ee4f6c7b33d81eb4f547a13cf1e6cf247893c31e0cf0077d3bd1dc4edc76b3b11d7ceb87593ab1d4cea074d39f1cd4e5871d38d1c44e1070537e1be4dec6ed3751b84da46cf3661b24d806bd35d1ac4d5069f34e1a4cd2068734219ecce4669333198ccc065732a1944c9c64531b18ccc6062130917f4be85eb2f41794bac5c72dc16d4b645af2d6168cb285912c7162cb105792bb15b4ad45672af1554a9854329d14dca6852b2941464a2c513285141c9fc4fb27c13d49e44ef27613a49cc4e327013749b44d726a134499c4cb26413149844bf25b12cc9604a7252128493c49b24c12549) else (0x62280c218804a1414850641c118c04a20100000a1480c22030641d21429070548241c20205541c20005880409880441c1588048c205541c311b04029204030a06054100000a201288040a030401200680c190705630130b04000000028d40a09248102220100000028804001550708000a2010000281c18889070a81c12880682812886070942981c22886070809070641c120304000c28100000000000001b04a48100000000000000000000000000028d0400281c16070581c100001244100284189104050704284118888508089104002248100028804002244100a20100089204a20100a201000002cc18910524410089543c221950f08864100049204a2018850680c150f0543c12880400243c158805244128804050f0543c10000000004920524410143c150f04090f0643c190f04011b0400000143c102704a20100000000028d0400000000243c100090f04a2010000000243c100050f0400000000000a890a082))))
def genIndex6 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x4a1d0e59346f80f018ba40aa57adaa249014f00b7fc0586f01e001a285f0100a18f80f01e00ed958f010c3c0780f01463c0210f0148e8d16213de018df80c2edcbc012af17226f3f80c3e211499a7f00fb1f5296f01a20ce391f01e03507805c787796f804db49254dcb15f83fc0233f0143a197f3659e0115f80f0029b8aca2f01e03c0780f001988075a806c33c070a83236543209000016c00198100c9)
def genData7 (j : Nat) : Nat := if 14 ≤ j then 0 else (if j<7 then (if j<3 then (if j<1 then (0x14358910f7093ac0b1221ee12158162443dc10eb02c4887b459d3058d10f68b1a0ca9a21ed16341943443da2c2982c6887b44dd6058d10f6898ac0b1a21ed13059563443d62cea02c8887ac5910655110f58b220ca1a21eb16150164443d628eb02c8887ac5190458910f58a0ac0b2221ea54650d62443d3286b02c8987a64d16058d40f38b2a0caa221e716541953443ce2aeb02ca8879c5456059510f2cb1aa0b2a61e5953581654c3cb26ab02c6a87955953654d10ee9b9aec81a21dd3735d503443b66e8bb2088875655d3054d10eaca9aec82a61cf267419754439e4ce832e68873659d3058d10e6cb1a0dbaa61cd96341b744c39b2c6836e29873658d065d530e6cb1a0cba261cd937581634439aaec9bac68873559d3158d10e6a9bac2b1a21cb967501644439728eb02c89872e51d6059110e5abb28eb2221cb5675056444396a8eb0ac88871e59d5059530e3cabac0b2a21be380499524437a50e984c6886f4a1d3094d10de943a60b1a21bd2874c1534437a3009b286886f44c18654d10de89830ca1a21bd130619324437a260c2a86886f44c1844c910de49830521a21bb2484117344376300a3286886ec6014550d10dd8a420899221bb1406195444376280c3286886ec5018650910dd8a030aa1a21ba9825014348373260c2664886d660d5059530dacc1aa0aa261b5953601654c35e50eb02ca886bca1d6058d10d793420cbaa21af268419734435e300b2ac6886bc5a10655110d78b420ca9a21af168419524435e2d083286886bc5a10650910d78b420c99221af160e15624435e2c1c22ca886bc5838458910d78b0706b2a21af160e0d624435e2c1c12ca886bc21d6059510d6cc1ac0b2a61ad983581644c357308b02c6a0679e1e8758910cf33c44eb12219e627e0562442fc72881ac4885f86414398910bf0c8286b12217d3964c143442fa728982c6885f4e4d7640d10be9c9aea81a217d1968dd03442fa32b1ba06885f464e8740d10be8c9a0ca9a217d19341943442fa32682264885ece517641110bd9ca2ea822217b19691d04442f632b23a08885ec6510655110bd8ca20ca1a217b19391d04442f4f28c3ac4885e92518758910b78cb208b12216f19599d06442de32733a0c885b9e597358910b72cb50eb12213f396601434427e728c02c6884fce4d80591109f9c830ca92213f298591034427e33083286884fc65b8440d109f8cb700a92213f194e19034427e321c3aca884fc64387589109f3c930eaa2213d79361d654427a926c3aca884ede5187589108fbc8b0eb22611ef9261d544c23df24c3aa88847b65b825d5408f6cb104baa811df9361d6544237f28c3ac4887a85190458910de09830521a21b913061332442f83241ba06885e46503740d10ba8ca86e81a216e19641162442da32c1ba068843b658825d540) else (if j<2 then (0x6884fd653855d9109faca70ab9a213f594e0d764427eb29c1aea884fd65383595109faca702b2a213f593e1d624427eb27c32ea884fd64f855d9109fac9f08bb2213f593e11754427eb27c22c4884fd64f825d9109fac9f02b12213f593a1d654427eb25c3aca884fd64b865d5109fac970cb9a213f592e15764427eb25c1aec884fd64b81595109fa4c2eab12213f4985cd624427db25c0aca904f7e5983551309efc9b0eb2a213dd984d9544c277f2cc22a6a04dfe598550d508ffcc2ecaa2611ff985d9544423ff30bb2a6a047fe6176549108ffcc2eca8a811ff985d9424c23ff30bb2648847fe6176485308ffcc2eab22211ff985d5434423ff30ba2a29847fe5d86551308ffcbb0caa2211ff97619524423ff2ec32648847fe5d8550d608ffcbb0aa1a211ff9661d544c23ff2cc3aa88847fe5987549108ffcb30ea1a411ff9661d324423ff2cc1ee48847fe5981dc9308ffcab0eb22611ff9561d644423ff2ac3a868847fe5583dd1108ffca30eb2a611ff9461d654423ff28c3aa68847fe5181dd5308ffc9b0eb12211ff9361d544423ff24c3aca8847fe4987591308ffc930eb1a211ff9161d544c23ff20c3aa898c7fa61545cd108fecc6eab22611fd98dd5414c23fb31ba2a68847f66176551308fecc2ecaa2211fd985d9324423fb30baa868847f66165dd1108fecc2cbb92211fd98593724c23fb30b1ee48847f65f81595208fecb70aba2611fd96e11754423fb2dc12ea8847f65b825d1308fecb704b9a211fd96e017550e3fb2bc32e89847f657845d9308fecaf08bb2211fd95e11734423fb2bc1aeca047f657825d9108fecaf02bb2811fd95e05744c23fb29c32ea8847f653855d9308feca70abb2211fd94e15734423fb29c1aea8847f653825d9308fec9f08baa211fd93e09764423fb25c32ea8847f64b865d1308fec970cb9a211fd92e15764423fb25c22ec9847f64b835d9408fec9706bb2211fd92e05764c23fb23c2ae89847f647825d9308fec8f00baa871fd90e057550ff846e81ac4887f04e10358910fe0982a6b1221fc13050e62443f8260a1ac4887f04c1264c910fe093a6099221fc1214c132443f448e822c4887e85210458910fd0a028731221fa14050d62443f428093284887e451d3050d10fc8a1a0899221f91414c143443f22809b286887e44dd4050d10fc898a80a1a21f913051943443f2260a2a86887e24c94050d20fa8aba60a9a21f51514c153443ea260ab2a6887cc55d4055110f98a8a80aa221f314055954443e3286a82a8987c550d5155131f7143ac0b1221ee22758162443dc30eb02c4887b85950358910f70b2206b1221ee16241952443dc2c483284887b8589064c910f70b0706b1221ee160dd162443dc2c1b9ac4887b85818358910f70b02e8b1221ee1605cd62443dc2c0a9ac4887b858) else (0xeb2bbb2a6885dd6577454d10bbacad0eb2a21775955d954442eeb2abb2a6885dd6551655110baecaa68a8a6173d9550d51502def2cb9ac4885bde556758d10b7acb6eab1a216f596dd163442deb2d43aca885bd6597558d10afbcb2eab9a215f7955d973442bef26bb2ea8857de49765d510afbc92ec8aa215f791619744c2bef22c22ec9857de45835d940afbc8aeca8a815f7915d9214c2bef22ba2a29857da5d655cd10afacbacbb9a215f59759573442beb2dbaae68857d657765cd10afac9eecbaa215ef92615744c2bdf24c22ea8857be49805d543af7c92eab1a815ef925d531502bdb24bb26488577e4d865d510aefc9b0abb2215df935d932442bbf26baa8688577e49764d130adfcb28eaa2615bf955d943502b7f2aa3ac89856fe51825d910adfca2ecaa2215bd9691d54442b7b29baac89856f6517655130adeca2eaa1a215bd9391d54442aff2cabaa88855fe55825d930abfcaaecaa26157f9455d65442afb2d2baa89855f6577454d10abecaaecaa22157d9195d544c27f720c32a4884fde6176551109fbcc2eca9a213f7985d9524427ef30bb286884fde61764c9109fbcc2eab22213f7985d5634427ef30baac4884fde617550d109fbcc2e6b12213f798597744427ef30b2ee4884fde61655d1109fbcc2cab92213f797619544427ef2ec32a4884fde5d864c9109fbcbb0aa1a213f79661d544427ef2cc3aa6884fde5987549109fbcb30ea1a213f79661d324427ef2cc2a86884fde5983dd5109fbcb307ba2213f79660f724427ef2ac3ac8884fde558758d109fbcab0eb12213f79561d434427ef2ac1eec884fde5583dd1109fbca30eb2a213f79461d634427ef28c3aa6884fde51864c9109fbc9b0eb2a213f79361d644427ef26c3ac4884fde4d87551109fbc9b0caa2213f79261d654427ef24c3ac6884fde4587591309fbc8b0caa2213f791619524427ef22c3286904fde45864c9109fbc8b0aa1a213f6985d5624427ed30b9ac4884fda61655cd109fb4c2c8b9a213f698551734427ed2fc1aca884fda5d8654d109facc6eca9a213f598dd5634427eb31ba2c6884fd6637454d109facc50eb2a213f5985d9544427eb30bb2a6884fd66176549109facc2eca1a213f5985d9324427eb30baa86884fd66165dd1109facc2cbb9a213f598597724427eb30b2a86884fd661644c9109facc2c7b92213f598459544427eb308b264884fd6611550d109facbf0ab12213f597e11654427eb2fc1aca884fd65f83589109facbf04b2a213f596e15734427eb2dc22ea884fd65b845cd109facb706baa213f596e09754427eb2dc12e6884fd65a8754d109facaf0eb12213f595e19734427eb2bc22ec884fd657845cd109facaf06bb2213f595e09764427eb2bc0ac4884fd6568758d109faca70eb2a213f594e19754427eb29c32e))) else (if j<5 then (if j<4 then (0xd9544433eaf1bb2a68867d5e37558d10cfabc2ecaa2219f5785d9534433eaf0bb2868867d5e17558d10cfabc2eab12219f576e15734433eaedc22ea8867d5db845cd10cfabb706baa219f576617744433eaecc2ee68867d5d983dd510cfabb307ba2219f516e11754433ea2cc2ee88867be498755130cf7c930eaa2219ef9261d324433db0e932648867b49d864c910cefc9b0eb2a219dd874d9544c33bb0c9a6e49867760d7655130cee9c2c7b92219dd36e15744c33ba6cc26ea9866fe518758910cdfca30ea1a219be485d1714c337c90aa2e68866f61d4655130cdec3a8caa2219bd845d95350337b08baac6a066f52164dc930cdea3b0caa26197f9561d534432fcb0baae68865f961545cd10cbec3aacaa22197d585d5434432fab0b2ee88865f56165dc910cbeabb0caa2218ff9661d634431fcd0bb2e68863f9a1765c530c7eb42c7b92217f39759504442fe72cbaa08885fce597540d10bf9caaec822217f3955d903442fe728bb206885fce517540d10bf9c9aec822217f3935d504442fe726b2a08885fce497640d10bf9c8aca822217f39061562442fe720c12ca885fca5d6540d10bf8cc2c881a217f19759504442fe32eb2a06885fc65d6440d10bf8cbaa881a217f196dd503442fe32dba206885fc6595440d10bf8caeec81a217f195dd103442fe322b2a08885fc6455440d10bf8c82c8b9a217f19059153442fe320b2264885fc64163dc910bf8c82c6b92217f19058d42442fe320b1a24885fc6414358910bf3cc2e6b12217e79760d62442fcf2e93264885f9e558358910bf3caae6b12217e79461d62442fcf28c1ac4885f9e517358910bf3c9b0eb12217e79261175442fcf24baac4885f9e497358910bf3c8a4c992217e698dcd62442fcd30b9ac4885f9a5f8358910bf34bb06b12217e69754d62442fcb31ba2c4885f96637358910bf2cc50eb12217e5985d162442fcb30b9ac4885f96614358910bf2cbf06b12217e59754d62442fcb2ea1ac4885f96578358910bf2caee8b12217e595dcd62442fcb2b43ac4885f96562758910bf2caa86b12217e593dd162442fcb2743ac4885f964e2758910bf2c990eb12217e5925d932442fcb248b264885f92617358910bf24bb06b12217d7964dd43442faf2a9bac6885f5e513758d10bebc9b0eb2a217d79361975442faf26c2aec885f5e4d764c910bebc9aeaa1a217d79359773442faf26b2a86885f564f7558d10beac9ee8b1a217d5935d943442fa926c32ea885f524d855d910bdcca20caa2217b79461d62442f6f28c12ec885ede517655110bdacb48eaa2217b5945d943442f6b28baa86885ed6516550d10bdaca22aa1a217b59391d54442f3b289b2a8985de6550655130bbbcbaacaa2217779655d54442eef2cabaa6885dde515759510bbbc9aaeb2a217779155954442e) else (0x21cbd645d9544438facabb2a8986fce418654910df9c3a06b1221bf386dd1034437e70cba206886fce19045cd10df9c2a08b9a21bf38440d624437e70281ac4886fce017654910df943a0ca9a21bf196601434437e32ac02c8886fc6558058d10df8cab00a1a21bf194601634437e326c02c8886fc6498059110df8c9300b1a21bf192601434437e30e832a8886fc61d0654d10df8c3a0ca9221bf187419434437e30e83264886fc61d0458d10df8c3a08a9a21bf18740d624437e30cc2206886fc6190454d10df8c320899221bf18640f724437e30c81a84886fc6050655110df8c0a0ca9221bf181419324437e302822a6886fc6050358910df8c06eab1a21bf180dd1634437e300bb286886fc6017559110df8c02eab1a21bf1805d5434437e300ba2c6886fc6016550d10df8c02a8b1a21bf180455644437e3008aa86886fc5db8440d10df88370ab9a21bf106e11754437e20dc22e6886fc41b835d510df883704baa21bf106e09734437e20cc2ee8886fc41985dcd10df88330bb9221bf106615434437e20cc2264886fc41983dd510df883307ba221bf10660f724437cf24c3aa8886f9e49874c910df3c3b06b1221be587e0d624437cb0ec1ac4886f961d2654910df2c3a4c99221be581499324437ca4fc1ac4886f949d864c910df29330899221be521619324437b306832a8986f660d0650930decc1a0ab2261bd930619324437b260c2a86886f5e4d8759510deac3a6ca9a21bd5874d9434437ab0c9a264886f54e163dc910dea9bb0ca1a21bd536615434437a926c3aca886ee6110654d40ddcc220c99281bb9805154344377280c32a8886ee5018650d20ddca030aa1a21bb79461d6244376f28c3a86886ed921545cd10ddb24286b1221bb5875195444376b0ea3286886ed6194550d10ddac0a8caa221bb5476194344376a8cc2a86886e7921345c530dcec226ca9a81b9d83519544c373a86c2a82986de6150650d50dbca830caa261b779561d534436ecb0baae6886dd961545cd10dbb2c22ab9a21b7587559544436eb0eab2a6886dd6055655110dbaac2eaa1a21b7558597744436eab0b2ee6886dd56165dc910dbaac2caa1a21b7558455434436eaafc22ca886dd55f8359510dbaabb0caa221b7557619534436eaa2c32a8886d76153650d50daec1aacaa261afa68419734435f4d0832e2986be5a10655130d7cb420caa221af968419524435f2d083264886bde598758d10d7b342ecb9a21af668459734435ead0bb286886bd5a163dc910d6f3426cb8a619f987419544c33f30e832a88867e41b855d130cfc83708baa219f906617744433f20cc26ea9867de458759130cfbc36eab9a219f7865d5734433eef0bb2a68867dde17558d10cfbbb70ab9a219f587459544433eb0cbaee68867d61975dc910cfac322bb92219f5815)) else (if j<6 then (0xb02cbb9a21ef16059772443de2c0b2ae8887bc581655cd10f78b02cab9221ef16059543443de2c0b2a28887bc5816544910f78b02c8b9a21ef16059153443de2c0b2264887bc58163dc910f78b02c6b9221ef16058d42443de2c0b1a24887bc5815458d10f78b0286b1221ef16045564443dd2c4832a4887ba589064c910f73cb2e6b1221ee62759562443dcacaa1ac4887b95918358910f72b22e6b1221ee56259132443dca4eb2ac4887b659d3058d10f6cb1a0cba261ed963419714c3db2c6832a8987b658d0654d40f6cb1a0ca1aa1ed963419424c3db2c683242987b6581644c930f6cb026ab2261ed93758163443daf2c9bac6887b55d93758d10f6ab3a62b1a21ed5635d953443daac6bb286887b558d6550d10f6ab1a2c98a41ed53759563443daa6eb0ac6887ae5910655130f5cb220caa221eb96441953503d72c8832a2a07ae5816350940f5cb028ab1a81eb947581644c3d6ac8bb2a8887ad5917650d10f5ab222caa221eb54650d62443cf2ca832a89879e5950655110f3cabac0b2a21e75565d563443ceaacbaac48879d5595458d10f2eb2a6caa261df3765d503443be2edbaa068877c5db7440d10ef8bb2ea82221df1765d503443be2ecba2068877c5d91541110ef8bb208b9a21df17541173443be20dbaae68877c41975dcd10ef8832ebb9221df1065d573443be20cbaae48877c4197544910ef3baae6b1221de7725d562443bcaf1ba2c4887795e17458910ef2baee6b1221de5755cd62443bcae4baac4887765d9054d130eec982ec99221dd9305d543443bb20cba264987755cf7558d10eeab9aeca1a21dd5735d563443baae6baa86887754dd1550d10eea98aeaa1a21dba4741954443b728e832a89876e5017655110edc832eaa1a81db7745d954443b6c8e8b2a88876d5d17650d10ecfca26ea1a21d9d47591324c3b3a8e9b2a89876750d7655130ecea1ac9b9261d9d3751943483b3a6ea2a86887674d17558d40ece9a2ea98a81d7a57419544c3af2aeaa2068875e55d0655110ebca82ecaa261d76585d573443aecb08aae68875d5d77654d10ebabaaecaa221d75755d953443aeaaeb2ee68875d55d65dc910ebaabacab9a21d755759572443aeaaeb2a248875d55d545cd10ebaabaa889a21d755745954443aeaa2bb2a88875d54565dc910ebaa8acab9221d755155173443abcae9b2a89874f95d4655130e9f23aacaa221d3d5751954443a7aa8bb2a2a074f5517550d10e9ea3aacaa261d3d455d1514c39f4d0832e68873e5837559130e7cb02eab2261cf9605d5644439f2c0baac6a073e58165dd110e7cb02caba221cf6685d9734439ecd08b2e68873d5db7558d10e7abb6e8b1a21cf5765d5644439eaecbaac68873d5d97458d10e7ab3ac8b9a21cf567455644439eac2baac888737e593758d10e6ebb26eb1a) else (0x58910ff0ca206b1221fe18741162443fc30e81ac4887f86150358910ff0c2206b1221fe17540d62443fc2e881ac4887f849d064c910ff093a06b1221fe12641132443fc24c81a84887f8485064c910ff090a06b1221fe10460d62443fc208b9ac4887f84115358910ff043a06b1221fd23761903443fa46eb2a06887f46593050d10fe8ca260b1a21fd13840d62443fa26e83286887f44dd0458d10fe89b208a9a21fd130dd953443fa261baac6887f44c37458d10fe8986e8a9a21fd1305d953443fa260bb286887f44c1764c910fe8982eab1a21fd1305d543443fa260ba2c6887f44c17454d10fe8982caa1a21fd13059153443fa260b2264887f44c163dc910fe8982c6b9221fd13058d42443fa260b1a24887f44c15458d10fe898286b1221fd13045932443fa2608aa86887f44c11454d10fe88326899221fc93049932443f924683242987f14e14358910fe29ba86b1221fc5264d132443f6490822e6887ec91d6541110fd923aa881a21fb24741954443f648e822c6887ec91d0454d10fd8ca2ca82221fb14859103443f628eb2206887ec51d0650d10fd8a32a881a21fb1405d954443f6280bb286887ec5017559110fd8a02eaa1a21fb14059543443f6280b22e6887ec5016454d10fd8a02c899221fb14058d42443f6280aa2e6887ec5015458d10fd8a02a889a21fb14050d62443f62808b2a8887ec5011559110fd8a022aa1a21fb10651543443f5284822c6907ea5016448d20fd3ca30eb1221fa648dd162443f4c90a1ac4887e951d4358910fd2a2a86b1221fa49461d62443f3286832a8987e650d0559130fcca1a0aa0a61f99404d943483f326883264a07e64c14550d10fcbca26ea1a21f95474d943443f2a86b2264887e54dd4650d10fca9ba8aa1a21f953651543443f2a688aa62a07e54c54550d10fc69928ca1a41f715759504443ee2aeb2a06887dc55d5440d10fb8aba0caa221f715741953443ee2ae822a6887dc5595440d10fb8ab208a9a21f715159504443ee2a2aa206887dc5450655110fb8a8a08a9a21f698254165483ecaaea9ac4887d655d3054d10faca9a0ab2261f5953415414c3eb2a09b2a8987d555d3654d10f9caa20ca8a81f3950519544c3e728a83286a87ce5015655110f9b23aacaa221f355751954443e6aa8baa86887cd5516550d10f9aaa22aa1a21f355151954443e6aa2a2a62a07c75153650d50f8ea2a68a8a61f1d43559544c3e3a86aa262a87bca1d6059510f793420cb9a21ef26741953443de30eb02ca887bc61d6058910f78b3ac881a21ef16741163443de2ca822c6887bc5910358910f78b06eab1a21ef160dd163443de2c0c2ac4887bc5818459510f78b0306b1221ef16060965443de2c0baac8887bc5817558d10f78b02eab1221ef1605d163443de2c0b9ac4887bc58165dd110f78)))) else (if j<10 then (if j<8 then (0x2c2c1e2c15ac07abf9abebabddabcfabc1abbeabbbabadabaaaba22b942b862b782b752b722b69ab66ab63ab5b2b52ab4a2b41ab392b30ab2dab252b1cab19ab16ab13ab10ab0dab0aab07ab04aaf6aaf3aaf0aae82ada2ad1aaceaac62ac32ac02ab7aab4aaac2a9e2a902a87aa84aa81aa792a70aa6daa652a572a4eaa462a432a402a37aa29aa26aa132a052a0229eea9eba9e329daa9d7a9d4a9d1a9cea9cba9c8a9b529a72999298b297d297a29772969296629632960295d295a2957295429462938292a2921a913a905a8f7a8e9a8e6a8e3a8e0a8d828cfa8c728c428bba8b328aaa89ca899a88ba888a87aa877a869a866a858a84aa83ca834282ba81da815280727fea7f0a7e2a7dfa7dca7d427cba7c327baa7b227a4279ba793278aa782277f27712763274fa747273ea73ba738a72aa71ca70ea700a6fda6faa6eca6e426d0a6c2a6ba26b1a6a3a690268d268a2681a673a670a662a654a651a64ea64ba648a645a637a629a626a6132610260225f9a5f125ee25e5a5dd25da25d1a5cea5cba5c8a5c5a5c2a5bfa5bca5b9a5b125a8a5a5a5a2a59fa59ca599a596a593a58b2582a57a2571a569256625632560255d255a255725542551254e254b254825452542253f253c25392530a52da5252522251f2511250324f524e724dea4dba4d8a4d024c7a4c4a4c1a4b924b0a4a8249fa497248ea486247da47aa477a474a471a4692460a458244fa4472444243ba438a435a432a42fa42ca429a4212418a415a40d240a240723fea3d523aba3822342a313a2d4229fa25aa236a207a1c821992159a13020fba0bc2092a05e201e9ff51fbb1f8c1f5d1f231ef41ebf9e859e569e279de81db39d7f1d559d269cf79cad1c681c2e1bff1bd59bac1b779b431b141af01ac11a871a319a0299e419ba9991195c9938990418d518a61871984d981e97f517bb178697521733971516eb96c7969e16699640162195fd95c915a5157b9557952314f414c514a6947d14539424940093d193a81373934a131592db92ac92831249121491da919b116c1137910890ea10cb90a79083905f9036100c8fd28f9e0f5e8f248f008ed70e9d0e630e340e0a8dd08d9c0d5c8d1d0ce88cae8c850c668c428c298c108bec8bc30b998b5f8b360afc0ac20a988a748a4b0a2c89f289ce89aa897b89520928890f88f108d288a388748850882707fd87e487c0879c8778873e871a86f106bc869e067a0656063205f805d405b5859705730533850f84eb84cd049e047f845b8437840e03ea03b5838c035d0339031a82f682e882cf82b6829d828f8287027e826b02260218020a01d5819b8161812780ed80b38074003a00007f8e1d0358910ff1c2a06b1221fe38440d62443fc6ea81ac4887f8dd10358910ff14c206b1221fe28740d62443fc44e81ac4887f866103) else (if j<9 then (0x442f0c2e2c2d4c2cc42be42b042a24299c2914288c27ac26cc2594250c237c219420b4202c1fa41ec41d341ba419bc1884174c15bc14dc13fc131c11e410ac0f740e3c0d040c240b440abc09dc095409240844076406dc054c046c03e403b402d4019c01140033ff53fe73fdebfd0bfc2bfaf3fa13f933f7fbf6c3f483f3a3f373f343f2bbf28bf203f1d3f043ef63ed7beb93eb0bea2be9a3e973e8ebe703e67be59be4bbe433e403e323e193e0b3e02bdf4bde6bde3bdd03dbcbdb43dabbda33da03d97bd8f3d86bd733d653d573d4ebd463d383d353d2cbd243d1bbd0dbd0abd07bd04bcf6bce8bce5bcdd3ccf3cc6bcbe3cb03cad3caa3ca73ca43c963c883c7a3c71bc6ebc663c633c603c5d3c5a3c573c543c513c48bc403c3d3c2f3c26bc1e3c1b3c0d3c04bbf6bbf3bbf0bbedbbe53be23bdf3bdc3bd93bd63bd33bc53bb73baebba63ba33ba03b923b8f3b86bb78bb703b67bb5f3b5c3b53bb4b3b483b453b3cbb39bb313b2e3b25bb1d3b1a3b173b093b00bafdbafabaf23ae43ad63ac2baba3ab1baa3ba95ba823a743a663a5dba4fba41ba393a2b3a1239feb9eb39d239b939a03987396e395ab941b933b925b912390438f638e838d4b8c138b8b8b0389cb894388bb87db875386cb864385bb848383a382c381e3810380237f9b7f137e8b7dab7ccb7c437ab3797b784377bb773375a37413733372ab72237143700b6f836ea36d136ce36c036b236a436963682b67a366c365e3650364d364a3647363eb6363628361a360c35fe35f5b5e7b5d9b5d135ce35cb35b7b5af35ac359e359035773569355b354d353f353135233515350cb504350134fe34fb34f2b4ea34d134bdb4b534a73499348b347d346f34613453344ab44234343426341db40fb401b3f933f633f333f033e7b3e4b3dc33ce33c033a73393b385b377b36f33613358b350334d3344b341b33eb330b32db32ab327b324b321b3193316331333103307b304b301b2f3b2e5b2dd32d4b2c6b2c3b2bb32b832afb2a7329eb29bb298b2903287b27f3276b25db255324cb244323bb233322ab2223219b2113208b1efb1dc31d3b1cb31c2b1ba31b1b1a931a0b187b179b1713168b1603157b14f3146b12db11fb10c3103b0fb30ed30d430cbb0bdb0afb09c308e30803077b06f3066b058b04ab03cb02eb020b012b004aff12fddafca2fc1afa32f8faf872f7eaf70af682f652f572f492f462f382f24af21af1eaf1baf0daf052eec2ede2ecaaebcaeb42eabaea32ea02e97ae8f2e7bae78ae75ae622e492e35ae27ae24ae1c2e13ae05adf7adef2de12dd32dcaadc7adc4adb12dae2dab2d9d2d89ad7bad6dad652d5cad59ad512d4e2d45ad3d2d2f2d1bad18ad102d07acf9acebace32cdaacccacc42cbbacadaca52c972c83ac7b2c6d2c5f2c5c2c53ac4b2c42ac3a2c) else (0x5b029122a32055001c5b0af05a0a551c15815a2601d00281ac1b12424544407a0038b315e0b40fc1512501f43403a0050af0530544890fa0ea1742403a0050af05a0a50a90ab1280c71702d81691b41441c615e0b40fa1520f619018e2d814a0f91882851662bc14a1512283d83c85b0880ca16c0b41491541440c617046c8a91381f02860720e05b02902283205500201a89202303d04407a00383502424607a0820f400715e46c89e0f105791b22783e018a2bc8d913c1e80c524c46c8b40f31041e01d002014916c2083cc410790a80c822d8410798820e80c604c05887c8880f212818e0980c01692303c83c841c1ec0f50980040760a41340a509800607a06c0a81341f210607606c0a813415210603605c0b01502644085a84203800a07e05887a8c814a10607e05887a8880ea12818e0e81481f02c41ec328550900c903f03d03a86c00281f03702903a86c00303d02a04d07c0790c303b02a04d0540790c304105a24887a8dc170294400750c504121f4294400750c301502622203c861618415c2183f018a2cc8de10c1ec1f018c1041681f23603d4750ab1041ec34032c1d81b02a04e4720a180d81502624607c8e181889142083f018a0f45791b22684107a8ec06403a62043e44407141f91b92303d441071820c1b92503d44407181682942a43f05a0a4063c1b42d03e44407c00304107e0e81ac1ba2043d44407241341b02ca4507c8880e38ac15028e0ab1021f02a01900980b51081ea21038c1085c20f414c00507c07c89a0f406c006c1781c286f83f05e0a1307a8cc17828486184307e031307e070b038381c105ac3f03860a40fb0fd1782b44e07e0c61481982e00660fc14160fc0610b323624a8518820e61a01d00240b09161e23185207d0c21442103290a89161e2318508820e21101e822809891c1e23305088c0e214422032809891c1e2330508840e214426032809891c1e23105088c0e2144260328208b32362490800fa1562083d86806581312283c4660a11181c42884c06502903fa2f05689c0fc18c2903e0054a8a4a76ca634a4fca36ca2e4a204a0cc9f3c9e5c9d249bec9ab499d498f49814973495fc951c93e4930492249144900c8f848efc8dc48d3c8bac8a1c888c8754867485ec845c82cc813c7fac7ecc7d947c5c7b7c7a447964788477a4771c75e47454737472ec72bc723470fc701c6f3c6f0c6e846dfc6dcc6cec6c0c6ad469f4696c678465f4656c64e463ac6274619460b45fd45dec5d0c5c845ba45ac45a3c59b4592c58a45714552c544c53145234520450cc50444fbc4f8c4e544e244d444c644bdc4afc4acc4a4449bc493449044824479c4714468c460444cc444443bc428441fc40c43fe43eac3d743c943bb43ad43a4c396c38e438043724359434b4337c32f432c43294320c31dc315431243))) else (if j<12 then (if j<11 then (0x5307b0838af12283d8530790b61101b00245991b22683d4730ab1041ec3120c48989141ea3985307b08420fb1842ac4b07b0830b323683d8558820f61ac2102bc0f81522703e4750aa0ea1541140c05781f02a85089c0f91d42a83a85006a0980d003c5791b22724607d0aa0f00c82262450828e908282912243cc728c814a10712243cc728880ea12818e0e41ac162262450800f51d210906244c48c0f91ca1060720d418a1722624607c8e50848b80520990b09191c429421007c0d9131248414740790c402d0362488798e51b02944286244910f31d42944286181a81f2262490828e80f218803e06c8989281f239430e0b40f91b124a3a8518820e61a01940d40da1a22624a07c8e00ea1891662490828ee1462083986c06483522c24a07a08141a89181e820838a2d81690f31ca3544c071c5b02921e63946289185b11381f23905a89a0e383906e2d889c0f91c82c05289241c8b60520988b21181438b604c45a07a0c141c82912303d0610a185c0291226384620b414a2642120f40d81312303d420c0ec0d815026232052841c0a81312503d03a86181c82904c44c4620b01541e42120e41481622303d0620a512403b16c06c0a81321e63a051006c0989121e63850720d48989142003e420e0e40c01622243d0640a1c1a8260300588890f41101c806a0980b11112043c60720a4130162226390640a201a81622243cc720880e383906a85c0b11312304207c8e241891312284107a8e908383906a0c48989102083d47484241c83502e8588989182103e47284281a81f2262490800f80f218806a4584940f91c820038e0d40f81b43444c4941081f238039407c0d91312484107a8e80f218906a07c0d91312404107a8e80f218a06a07c0d81a22624a0840f91c81d43160e41491642203e0640a912403906e2d889c0f91c82c0550724560a814605487e0b415208881e23044085108289181422042884148d91522624607d00188d91522623205500181d01692243d03c84185c02912243c4620a60038354362448788840ec0070520610b21512243d83885406c00a0520990da1611842844207600482914207d0a88820f61842a03d04c00b02c2458788c61481f43085108c00a03e06c4410730d400607485a4910f11001e430e0e814a1691b42c8508800f21b42140a45081f1390544410750b00e80140b50d89221e2350520760040354362488788840ec0071660b40f89c42a24887a07406c00a05286c4690ab1222103e84600482904207c0e08880f21902903605400b02c85448b0f118c2844084407a0980160e41c0b60528460780c81540090520984680c81522504407609400a0722d814c0f418029820e46c8a91381540052364548989181f400607663a05500104890f31d400407e85807c8e918428616c0b60d89281501e800e2e0) else (0x20ce030809180a109101113c141037918100060a040001a820d4106a0e0a0701838281024603230100000000000003ea142000c060a88c0e1607040c10080060a040c1e0835c14101f510160a040030382c1c10244030d7038581c1c1608006030688607080a1742b038742e8504050b51181c303038380c100000000085707f038709f05050970185083038506701840010830384000000000043760e143160e142760e1307061be0a0a196070a186030a15e0708000006a0e07070182060307038383c1c1f80c2021050708091982820113e0a08046341c244f41c21700dc283e08390514c1f081a828a60f8507c126f81c226f428200083e0e0307038380c1c0e083043e1037041b820c0106e0808de83848c683848dd87e0a0e818340c100044ec28246f41c244f41c246ec282000616c28260e0a2b43ec1c3440c1c2a140a8805193070915a1f60e18006030513e0a08046341c244f41c20000000112b03090cb0308046087d8186060fa14160f058182060b0703820607040000000000028502a20100000000002148307c1c060d03070182000000000000000000000000a1c1011a820010d614850d60f848a60f848d60f850d41000c060e0a04002818340c1a060a3505148341c186a0d07040000010f828d41a140d0a050f82050704000000000c28287c1030382000c1c123644c48c0f30900e800e45a07d0710a61201d001c8b20f318428c2203600382903e4590aa0f31041cc2203d04c00b2364590798820e61101b00201481842c05487b0710aa1001c82600582903e0600a913a0e21642282241481f0310580aa1422741c42c84006a08c22703c8398680740061660748dc0f20e61a01d00201481f42a83d8518820e61a42a03600591b41ec28c410730c80d80100b40f81d13805487a0750c00e413002c0f81b22622143484a06382903f4284410730ca1542403241a81f03686a0b11311001d43484a065c9121ec284420750d210704007c0d913a1422203c86508483504007c0da172274284440790ca10b42d2488788890ca11818e0a41301b42d2348508890ca1181940a40f88880f21902903604402904c44c4620b51341e42100e41482682c44c4620b014a2642142e01482642c43c46489508401f03644c46a0b51322203c86240f81b22623505a8991101e43301281690f11b02e44a8840ea1880520988b08d81522504304201a82204045c46c0b91282143304a0258af23644e48c0fa1541e01d00245791b22703e4750aa0ea1541122bc0a91392303e855071c5c12651c6318590a8074008236a490828e31041e01d00205782d0520915181521e63a05689a0ea15411a2bc1681f03a0548798ea1501f4328550460af0520548798ea1541d42e8450450b315e24507b0a60f61101902cc89a0f61562083d861c8d91312283d8)) else (if j<13 then (0x38581c1c0e080010aa0e10101c111b02824160a8b054402028b06098200081c10103820413060982000a4b0384a441000c0e0a92c0e141782c109142083c340e0a0a0651b000a07c85098848880e1c1b9101420a0e15070483c850a07c850a880244e87841041f83a06a204205a428308409885060b414826214204107e0e81a881041f83a06a203e03b01c81880f814818206201d03040c345607c0dd0f1113d0f0912d0f091001ba1e1a19a1e1231a0e1227a0e123003f214307e0ea038741c1a0e083d90b00c390a0a2b0512d0f090c8289c1460090a0489e1020e1d105101292a161291a16150b510111b522120706440342c1a16a202265220261e081b61f82c83890800db0f0c1db0fc161b0f0587820ec09b0fa16203b026c3e85880ed8784c3c161e081361e1420026c3c361e0c2b606101902a215410800b306010309221025a1e1019a1e1019a1f00c3032081992210a1910101922010000080c12140c375181027a1e1020a1e1507c06150f04104920987c8d0a1b8200142c850880d0502021b214143060e10200362214308082850462242840ae878408287840d685040ad05840824885230121008000143c144c083b04e23144880ec859890e838242cc4840ae878409e87840ae878442d440543c858543c858543c1510090b510111b416120b064920b0a48a0b09058200004130408140c158061415806103d06224547080f48818e0c8818e08882880a428305c888543c1a1e08041c100006aa402000000028782000028d0400287a8d0a87a8c094403428103f4282018782030f058782c3c100061e0b0f058182c0c10320600aa8212878324415180d0f068382a341a1e0b0f058782c1c10740800da86101d10830c1d0a06878343c15180d0a068782898107609c13289101d9890a838343c15100d0f068783248107e0f418a8e101e98e081f91131c1c8507038342f03840ed48c8ca162607041ea8c0a882880a85a8840e1d10c0e150bc0e160705428381c194680c2946828242723020820d4226f81c226f2302265220225607e44060f409c8c0c1eb109101c88041d813922a31858a0ed85c880c9b824ac1840648220e0806450184854c8840215820118890a80c300001854850b07830c20ae0f60e230790a1120c1ec1c386183c2c160e0f070782060f0707822be48e0f0c00118015a0e1a3023605707880c08d8150c1a01f08014208300493e0f089060f098502c2e8384c2d8504c28100024183e838600183d42840c00fa850c182850b07e030a48830801001002060b070803443018542d446070c0c0e0e0f041060f0818e070b05838401c170282c060e10068860a0988020c944040ac0fa880d44020ad44040830504060807038302c18160c0b60e160f8161607054620b0905c880905a89081be07081ba8c081be070800) else (0x922098c21500c331041e018644cc610a0c89e1031041c422c0913922111381e214307c4980c116108b1070918015a0e1a3002b244324c090c606074c404631858446cc4040554284056078850e83a85080ec0710a181550a101581e130790a112041ec1c360e0c910448c0f5081a13041f81621f01c407405a07907104888530900c444006e03860820785028122643d4620a1089a9141e4284226a45079071089a8c41441c45188282036a21038744142a030d48a0f0a85a8840e191b522111b518128840e128c06c92854061a1332243d0188854c884644101488262083a030e882030a85a070804060885040a0e214224141c2a0e215018704cc30484c142663685c0a110291351b82e050844c1226089211aa18342d03c038606e078406d4405028440406e8828d41481c5036a202524090a510110a510119204c902648143a082031a4288389a44c690a11041c5040428231121501874410504050b214a203910091d04086105583860188c061120310118806184150804100a08058182048d214102004100380c10400820a1501c3a140a08041050a80e1b03060790bc0e1c0f216101b91101c303682e0386a31058522283852220385220121781c280e0a0b80e1488a0e10b60470288188630858444c4600a0c860200082c1020402040b40e108d817028392482c2216a202510090b51014924161408a0e130a0545820981a1441c216c44c282643cc70644c107a2e089a0b101e81f02a850898a06e0385220191009888061113523230850844d48c8820e20b615f28c85203145b09220e18af123214316c2be5190311492070948c8c080aa03088da919101c1941e80c3426429038684e4610a0d0990a4061a1b21410b82141215045c10a088502019220e119220e1192050999190a80c442a6442322080a4644042cec42030d0382093058444142840c54705428161541c260f2142240a498386a1501840950a8444c4880f0c0b20880e1a1702d04c8889021e302622210001110403240800588989181e203190810312262450820f1418913122041078a4401220a20251008009c102e44c48c1081e2a080546c0a08891070883820291810111612503c03884410384440122081c231180c20146a0b80e191381e0283216090b064402003b041e8204c141f02b038683e050406e038581c19100c88a0e1000ec1026090a040aa0308000002b41c202b41c20185020550185428150a0a8840e1000000288c0e150ac0e1288c0e128d04040e080000000001828132408142a03840a4103e081222038501c151a828200003038200000000122283852228)))))
def genIndex7 (j : Nat) : Nat := if 3 ≤ j then 0 else (if j<1 then (0x7c00322cca7e462e8ba5d28b089e003c007221b1e7c6dfc0018051260c83745dc9caf001f94a4e9f1a5e1d6b4afc004931f001e003a2d08365470e0b38b3b80c9009e0006a3f800f001e003c006227f001739047820feb3cbe003427f403108de0035197800e413e003c00081bf0004597cda90fc32c1e3de44c7800a43cf8a701df800caf7a5a1c39309d345ec634845a1dbb331005bc001257f001e003c00210bf001e0014f391eaf0006513c0005725408042bc007800f001e0036f07800e3656912ccf1a2b416de003c002a11d06893898bf59ecf00155d4b23d637f00101252e97c8d196b050ac6d9dcc5153e000429e84cc0f7e002080661781dec2d0c9b5935f9e1e0020ff05e8cb30e20fc006a52f0010427c007800829f42d620cf800f001e003c007800f001e0034ce7800a47dc84c86929d1f00113afafb2d2c01cf71cbc007800a1ebe002315780091db279bc001839f001e001462199014a913bfc00780070b04537c0075c6a0d542df528bd7032a95775681da0a7481e0008dc9802f000a4f3c00194610840283c8cf800d143e2fa49730fd62386116cc7a225f001e003263d035f001e002d229013d327e0024d07800b3b2c373c007800b1bca07627674fff001435f8bdc0a4b10c02a9c43d23bf001c954adc780091e2579810651439196527fc007800f45592ee6474920e229e003c001069c03465b7c007800b087e003c00608df001e003c002e00f001e002cd4ba1660ea82b7c007800a46083dbc00484833c220c045c0894b123207bc000d6df00161db313e0a3f00161b7c00780081f55947c007800b2440397c00194ab1cd937acbe7e425157e000a207800031118cec66b4d4f000960bebb6a22d348d7268678cf24255e003c00624d0435468582cb9125bd82792ce37800cc94247d84e7800e4b4c26f0b2523c4b846353c31f800d249e45dcd99d74f0ff435563b38a21371a8df461690fe2a1e000864206bf001e0024e8780052afe003c007800f001e000ab59e40f001e003c0025565837e002cbc008ef00045ac919f8004935e0004467800096fe001cf46234a3ebe001489822390b5e0010eef800115de003c002040f001e0006b3f800f001d1c7c002956f000b6b3c0068eed14de0030d59205b879d0db8a3f08a1235e0028443024d945e0008f9f800907b578fc007800232de0020bb9a157997e0020b67800a277e001044f8000100436cd4850410832842030052870410055000810002836c21c00081040500847d304064b00400c00704200004505d2817400ca141b4000500214a0c60000ec20320a1541091d50000550420065c304128260000c14508a1430c12470080010001842c00c20423400890403c206100508028214204058834900024400000200708b1894401070005a90810181900190c70c1005043) else (if j<2 then (0x7f000f6e6c3309c4f101e003c000a39700fe0024cbf800f001e00089d298c7013f5b982bc17272e190efc007800f000996bc002868f001e0024c0f800f271c7b61237195f001e0034747d2af001e003c004923e45ba436c23a86fd38be00262988c7d4b2e175d1059f0dab9e003c0070a5ea89e003c007800f001e521428912ce2ea44f7c0008372359e000c62c1a7f001e70ac18f800f000843a872600f62aaa7f04ffb208ebae42c3d29b826b46db665ce4e823a07dc7e907558f40a662447c005c74d0c5815bee555aef001284805c9959d1b3f49f264164c9391e003c003901f001e003c002896114f56c3c007800f00084600a705ea810ac2c9d0c4562f000c4cbc00525029d3664b07cd09ea236c7554d564fee404890a8b5205b108278a0cc141eef39b55c488378002c6be018c97e219aab5c4cc43f404dd86b34030a96078f0018007e877800f001e001858a908f001e0000ded116f001e002f07f800f001e003c0019be2151e003c00085ef000c78e80e11da0cb7b83701551eb03f1e0010a4883253af219d8384a03a2be81ddcea48d050bfb2dbf21c210d007b42fe2210500869e001d037800f000e6fe4c57800f001e003c007800f001e003c007800f001e003c000854a8c194350a05deef001e83f51200929042e8730cfd65404b7d38f8657800d4b1e003cd77800f001c8bbc0036314198d78a80bf800f000b1cfc007800b2c7e003c005928f001e00150a7800f001a69bcac780008b682f3c004540f001b5fbc0029fdf001c8d7c007800f00086f3c007800f001e003c0078007416c8a7c007800f31cd2a2caf004a3057e0004ec7800e05e26a20b79194788263e28e1e9cbf001f3958b72055f001e00012419c1c207835bc0001eff001e003c00591d602be001c0001897493e4e7c007800a2b98173c005d92e01020a3c007800f001e002430103883f3e000e94f800538f61e68117800f001f6b7cd15c01f000c8013088951f000e577727117ad2c5a61452ef800bc92a875500d081ec4836d982765ff4041e36bf2b780011e5e00009a780083ec170fc003979f000a602c94e864f001e267c0010ec348fe003c000a4b73c1d51985ec16961ba7943c0078008475e002c6308e1f001e003c003984b33b783bc0061865afa045510700cef00080a7c007800a05d37facddc8fbdaae136b861ad41e127885fc0078e2235f7304ccd9065d24fa74bc7ff800cb07a1c50fa19f1f001e003029424c69337070a82653d43b9e002927dd4fc299e6d011ff800f001e003c007800f001b8e34eb7800f00054ed71d7800f001e00192b7a4e8a99e003c00101ff001e003c007800f000034c864c1215bc3e001468e8afd023e5f4f197800f001e003c007800e48241ebc007800f001e00112e5176b8efe003c00780003354303c0044845af8051) else (0x7800f001e0004ad4630d44c890fc00382d143fe0006d5e07400c30585ad9ae53f001e003c0078009363e0020077800f001140bc007800f001e0018c8f800f00122fcaf59814f001e0022a5d12d9031e0000e0300d5c89384bc0038df2b43e003c0038e9f00024958c3f8001b51c2b0413c83a739c10fd0f4aa4a4399e003c00780093f7e430ad28141e3bfe003c00693ef01647dfc0029adf0002257c007800f00008f4b1cf80059bfe00080c99baf0001865c9bb13f0307b1e7c0044074108b5e08b359b6f001477a405386e5183e003c0045bdf00073c7c007800f001a417c000207f205e003c0019b07cba4242c5d7073fbca81f3c00183fb067427fc00312b32b6249bc007800f0018667c007800f001e003c0078003b17e0010a5f800d1c7c41fc004e01f00108c7c0078004209e003c00780073c5e0010a9f800f001972101e0404f02545fc841107d72e632148887171f000d8d3808306cb11f2360ce7b0e0304af72dc8f189aa450086f8f949a34166012fc00209)))
def genData8 (j : Nat) : Nat := if 17 ≤ j then 0 else (if j<8 then (if j<4 then (if j<2 then (if j<1 then (0xd8458d40bbd8454d40bbd844c940b7d8550d51b7d8550d509ff87597209ff87595209ff865d5109ff865d1309ff865cd109ff855d9309ff855d9109ff855d1309ff855cd109ff845d9309ff845d9109ff845d5109ff845cd109ff835d9409ff835d9109ff835d5109ff825d9309ff825d9109ff825d5109ff825d1309ff825cd109ff815d9409ff815d9309ff815d5439ff815d1309ff805d5439fe8798d109fe8794d109fe87905309fe87595109fe87591309fe8758d109fe8754d109fe87505309fd87cc9109fd8798d109fd8794d109fd87945309fd8790d109fd87905309fd87885309fd87597209fd87595309fd87595109fd87591309fd87591109fd8758d109fd87589109fd87551319fd87551309fd87551109fd8754d109fd87549109fd8750d209fd8750d109fd874c9109fd874c6609fd874c6509fd874c6409fd874c6209fd8740d109fd86dd5309fd86dd5109fd86dd1309fd86dd1109fd86dcd109fd86dc9309fd86dc9109fd86dc5309fd85dd9109fd85dd1109fd85dcd109fd85dc9109fd84dd9309fd84dd5309fd84dc9309fd84dc5309fd83dd9109fd83dd5109fd83dd1109fd83dc9109fd81dd9309fd81dd5309fd81dd1309fd81dc9309fd80dd9319fd80dd5319fd80dd1319fd80dc931fe10498910fe10458910fe10398910fe10358910fd23740d10fd130cc910fd13098d10fd13094d10fd13090d10fd13058d10fd13054d10fd13050d10fd1304c910fd03740d10fb24741110fb14059110fb14055110fb14050d10fb14050910fa94241120f695241520f595341530ef26741910ef16059510ef16059110ef16058d10ef16058910ed96341930eb96441940dd7739cd10dd63784d10bf38640d10bf38440d10bf3805d110bf3805cd10bf3805c910bf38054910bf287c1110bf287c0d10bf28741110bf28740d10bf281c1110bf281c0d10bf28084d10bf2801cd10bf28004d10bf184dc110bf183dc110bf183c1910bf183c1110bf181c1930bf181c1530bf180cc910bf1809cd10bf18098d10bf18094d10bf18090d10bf18080d10bf18059110bf18058d10bf18050d10bf08740d10be68290f10be68290d10be6821cd10be68204d10be58290f10be58290d10be5821cd10be58204d10bcd82cd130bb684ccb10bb684cc910bb6841cd10bb68404d10bb584ccb10bb584cc910bb5841cd10bb58404d10b9d84cc930b76851cd10b768504d10b75851cd10b758504d10af6861cd10af68604d10af5861cd10af58604d109fa801d1219f9801d1219f88740d109f68784d109f6811c1319f5815c0319f487451219f48744d109ef825d5409ee821cd109ed821cd109ec825d5409de831d1219dd831d1219be841cd109bd841cd1097e859c52097e851cd1097d859c52097d851cd108fe861cd108fd861cd10ee16058910) else (0x6dc530df9065d540df9065d530df9065d510df9065d130df9065d110df9065cd10df7765d510df7765cd10df77645510df77644d10df7755cd10df77544d10df7705cd10df7165cd10df7155cd10df5835c660df5835c650df5835c640df5835c630df5835c620df576dd510df576dd110df576dcd10df5765d510df5765d110df5765cd10df57645510df57645110df57644d10df575dcd10df575dc910df5755cd10df5755c910df57544d10df57544910df5174c660df5174c650df5174c640df5174c630df5174c620df516dd510df516dd110df516dcd10df5165d510df5165d110df5165cd10df515dcd10df515dc910df5155cd10df5155c910ded7649720ded7598910ded7398910ded274c910ddf764d130ddd764d530ddd764d130ddd744c930ddd3798d10ddd3790d10ddd3758d10ddd3750d20ddd3750d10ddd3744e10ddd3740f10ddd36dd530ddd36dd130ddd36dc530ddd365d530ddd365d130ddd34dc930ddd34dc530dbe4755110dbd7650d40dbd7550d41dbd7550d40dbd4759130dbd4759110dbd4755130dbd4750d10d7e5755130d7d5759510d7d5755110d7d5754d10cfd6759720cfd6759110cfd6758d10bfb8640d10bfb8440d10bf983c1910bf983c1110bf981c1930bf981c1530bf980cc910bf98098d10bf98094d10bf98094530bf98090d10bf98090530bf9808c530bf98088530bf98084d10bf98080d10bf98059530bf98059110bf98058d10bf98050d10bf78759510bf78758910bf7865d510bf7865cd10bf78644d10bf7855d910bf7855cd10bf78558910bf78544d10bf7845d910bf7845d510bf7845cd10bf78459510bf78458910bf78444d10bf7835d910bf7835d510bf78359510bf78358910bf7825d910bf7825d510bf7825cd10bf78259510bf78244d10bf78159510bf78158910bf7805cd10bf68798d10bf68794d10bf68759510bf68758d10bf68754d10bf587cc910bf58798d10bf58794d10bf58790d10bf58759510bf58759110bf58758d10bf58758910bf58755110bf58754d10bf58754910bf58750d10bf5874c910bf58740d10bf586dd510bf586dd110bf586dcd10bf586dc910bf58655310bf58655110bf58654d10bf58654910bf58650d10bf58650910bf5864c910bf585dd910bf585dd110bf585dcd10bf585dc910bf58550f10bf58550d10bf5844c910bf583dd910bf583dd510bf583dd110bf583dc910bf583dc110bf583c5910bf583c5510bf583c5110bf583c4910bf581cc910bf58198d10bf58194d10bf58190d10bf58184d10bf58180d10bf58159510bf58159110bf58158d10bf58158910bf58155110bf58154d10bf58154910bf58150d10bf5814c910bf580c5531bf48759510bed8290d10bed8250d20bdd8359530bdd8359130bdd8355130bdd8350930bbd84cc910bb)) else (if j<3 then (0x4520bfd8650d20bfd864c910bfd864c520bfd8550d60bfd8550d10bfd8550560bfd8550530bfd854c540bfd844c550bfd8348560ff3805cd10ff37640d10ff37540d10ff37440d10ff3705cd10ff31640d10ff31540d10ff31440d10ff3065cd10ff30644d10ff3045cd10ff30444d10ff28740d10ff23740d10ff23140d10ff20740d10ff18640d10ff18440d10ff17641110ff17640d10ff17541110ff17540d10ff17440d10ff16541110ff16540d10ff16440d10ff15440d10ff137c0d10ff13740d10ff131c0d10ff13140d10ff11641110ff11640d10ff11541110ff11540d10ff11440d10ff106dd510ff106dd110ff106dcd10ff106dc910ff1065d510ff1065d110ff1065cd10ff1065c910ff10655110ff10654d10ff10654910ff10650d10ff10650910ff1064c910ff10645510ff10645110ff10644d10ff10644910ff1045cd10ff10458d10ff10458910ff10454d10ff1044c910ff10444d10ff103dc910ff103c4910ff1035c910ff10358910ff10350910ff10344910fe90448d20fe90398910fe78358910fe77458910fe77358910fe68758910fe62758910fe58758910fe58358910fe57598910fe57458910fe57398910fe57358910fe55358910fe54398910fe54358910fe52758910fe5274c910fe52654910fe52650910fe5264c910fe52158910fe5214c910fe51598910fe51398910fe48758910fd93641530fd930cc910fd93098d10fd93094d10fd93090d10fd93058d10fd93054d10fd93050d10fd9304c910fd9064d530fd9064d130fd9064c930fd9054d130fd53798d10fd53790d10fd53758d10fd53750d10fd53740f10fd53654d10fd53650d10fd5344c910fd53198d10fd53190d10fd53158d10fd53150d10fd5154d131fcd3250d20fcd2348530fb94059120fb94059110fb94055110fb94050d20fb94050d10fb90651540fb90650d40fb90650940fb64755110fb54759110fb54750d10fb54655310fb54655110fb54650d10fb54550f10fb54550d10fb54159110fb54150d10f9d4359130f9d4355131f9d4355130f9d4350530f9d3458d40f9d344c940f9d344c540f795059530f795059520f795055130f790655150f790654d50f790654950f755759510f755755110f755754d10f755655310f755655110f755654d10f755159510f755155131f755155110f755154d10f5d5359530f5d5354530f5d3558d50f3d5454540f3d4550d51f3d4550d50ef96059530ef96059510ef96059130ef96059110ef96058d50ef96058d40ef96058d10ef96058910ef56759110ef56758d10ef56558d10ef56558910ef56458910ef56159110ef56158d10dfb7640d10dfb7540d10dfb065cd10df97641530df97641110df97640d10df97540d10df906dd530df906dd510df906dd130df906dd110df906dcd10df90) else (0x10ff77558d10ff77458d10ff77454d10ff68759510ff58759510ff58758910ff5865d510ff5865cd10ff5855d910ff5855cd10ff58558910ff5845d910ff5845d510ff5845cd10ff58459510ff5835d910ff5835d510ff58358910ff5825d910ff5825d510ff5825cd10ff58259510ff58044d10ff5765d510ff5765cd10ff57655110ff57654d10ff57654910ff57650d10ff5764c910ff57645510ff57644d10ff5755cd10ff57559110ff57558d10ff57558910ff57550d10ff57544d10ff57458d10ff57454d10ff57358910ff565dd110ff565dcd10ff565dc910ff5655d110ff5655cd10ff5655c910ff56550d10ff56545110ff56544910ff5645cd10ff56454d10ff5644c910ff563dc910ff5635c910ff56350910ff56344910ff5545cd10ff55458d10ff55444d10ff54358910ff5165d510ff5165cd10ff51655110ff51654910ff51654520ff5164c910ff5164c520ff5155cd10ff51559110ff51550d10ff5154c540ff51454d10fed8259720fed8259520fed6448d20fed2654910fed264c910fed2458d20fed2348560fdd764d130fdd644c930fdd3798d10fdd3758d10fdd365d130fdd365c530fdd3655130fdd3654d40fdd3650d50fdd3650d20fdd3650930fdd364c520fdd3648530fdd3559130fdd3550530fdd345c530fdd3454530fdd344c550fbd6350940fbd4759130fbd4655130fbd4655110fbd4654d40fbd4654540fbd4650d20fbd4558d40fbd4550d60fbd4550d10fbd454c540fbd4354540fbd4350550f7d5759510f7d5754d10f7d5655130f7d5655110f7d5654520f7d5454560f7d5454530f7d544c550f7d5354540f7d5350550efd6758d10efd6358520dff865cd10dff855cd10dff845cd10dff825cd10dff7559130dff7550530dff7454d10dfd8759720dfd8759520dfd865d510dfd865d130dfd865cd10dfd855d930dfd855d910dfd855d130dfd855cd10dfd845d930dfd845d910dfd845d510dfd845cd10dfd835d940dfd835d910dfd835d510dfd825d930dfd825d910dfd825d510dfd825d130dfd825cd10dfd815d940dfd815d930dfd815d543dfd815d130dfd805d543dfd765d510dfd765d130dfd765cd10dfd765c530dfd7655130dfd7655110dfd7654d40dfd7654910dfd7654540dfd7650930dfd764c910dfd7648530dfd755cd10dfd7559130dfd7559110dfd7558d40dfd7550d10dfd7550530dfd754c540dfd745c530dfd7458d20dfd7454d10dfd7454530dfd65dd110dfd65dc910dfd655d110dfd655c910dfd64dc930dfd645cd20dfd63dc910dfd635c910dfd545cd10bff865cd10bff865c530bff855cd10bff845c530bff8159520bfd8798d10bfd8794d10bfd8790530bfd8759510bfd8759130bfd8758d10bfd8754d10bfd8750530bfd8655130bfd8655110bfd8654910bfd865))) else (if j<6 then (if j<5 then (0xd1793cbc2a5de52eda975ecba8c5d112e6917288b8e45c422e0b96f9cb75a5b822dab96c88b5e45ac72d469694cb43259e42cd7965e8b28059012c6116234b0b058232bf995ef8af0857542b9215ba8ad6056762b1e1581cab9055892aaa15454a99854972a2e950a0a7dc53b429bf94d28a62a52d6294b9499ca46e520c28ee146c4a2f8514c288b94374a1505073281a13ffc9f9e4f9527ad93c849dec4ebc2741139349c304de326d9935a89a384cdd2651931a4985e4beb25d392d8c96484ae02555929ec947849f824e412660929e4906245e922209092481423ef91e808ed64736237911acc8ce8463522fd916dc8ae6452f227d11300890c443d21ff10ee88700433c217990af884fe424f2108107588342416c209b903f481864089202a1007c7fca3fba1fbd8fcdc7e0e3ec81f4e8f9b47c7a3df91edd0f5d87a6e3cf31e5a0f1e878623bf71dd48eda8764c3ae71d518e97c742c39d21cc20e500720238c71c468e160701e37c61bbe8dcd06dea36b61b3b8d8e06be835c41ac28d5046a0434b91a358d0b067c6339f19ad8cc8465ba32a319348c8d0641231ca18c58c544624c30ec18590c1e06086300417e50be405eac2f1c176e8ba8c5cd22e2f16fa8b6d85af82d3d16818b2fc58f62c4616060af3457262b59158d0ab58552e2a53150c8a754532c2957148c0a3645134285b140e09f744f3c275f139009b984d4e26681314897a84b60257b129e094084990248e122a0905447b6239c11ae88ca045e622b9113f88928442a21e010ce08560422820d010460814840261fcf0fc587d303e101ec90f450792c3c181dc80ebf874d839ee1cbd0e3a070c037ce1ba30dad06c4435901a840d1d868043366196f0c9a86400319618960c2e060602fa8178b0ba385c342dba169e0b2a858582b9a15840a9d853c8297a14790a1d04fec275a135f098d84b842544125409080470822ca111c08698428c20f0103907f803eec1f160f65079f83c641d8c0e6e071c838241ba80d9f06b2834ac19e20cb7063c03148181c0bc505c082d1c15fc0ac4054502940140e09cd04c982564123e08d6044e02188105007e403d781dd40e7606fc036101a200c9c061402ed016800acc052c0274012a408de0449021180ff4079a03a701b900cb805ca02a60136008b403d201a000b3004b001ee00ae0037800980000ff98640d10ff98440d10ff98140d10ff97640d10ff97540d10ff96541110ff95440d10ff9065d510ff9065d130ff9065cd10ff9065c530ff90655130ff90655110ff90654d40ff90654910ff90654540ff90650d50ff90650930ff90650550ff9064c940ff9064c910ff90648550ff90648530ff90559130ff90550530ff90458d20ff90454d10ff90358910ff7865cd10ff7855cd10ff7845cd10ff7825cd10ff7805cd10ff77654d) else (0xe0440e00502648e218791885a144460e4290981e03801c87b1c46617851118390a4260780e00602648a208791985e144460e4290981e03801c4881e4721483806800f48e0a454521ea9085480aa3f351eba8eed473ea37e51aea8d2d4654a31d5185a8c0d45eca2e95170a8b51457aa2b55156a8a814530a28b513a289754482a22a5109a880543d4a1ce50d92864542eaa16850a3a848541f6a0df505ca827540f8a0565015a803d3fe69fd74fdda7e7d3ee89f4e4f9927c453df49eca4f4fa7a0d3ce29e5f4f21a78c53c169de54edd2768d3b0e9d754eaf274e13a389d0a4e7c27385398a9cb34e50a723d39049c6b4e27a70e138429c0f4dfea6f8537949bb84dd0a6e2936dc9b524d9b26c4135d49ace4d5ba6a9535269a8b4d352694d34789a2f4d0c267f133b699c94cd426645330899774cada6525325a99074c75a6329317098ab4c4a261f530e098684c302614d3096982f4c1126041300697e24be5a5ea92f3a97954bc1a5d9d2eaa97394b93a5c412dfc96e24b6325aa92d2696814b3a259892c96963e4b1b258692c2495f64af2257492b8a95b34ad32563d2af095614a9da546929fc94dd4a5ba524528ea94544a19a503527e293d049da24e6126e4934c4995a4c2925dc92c84953a4a1924d49244490f247f523b891bb48d2246352300917848b8245a122b6914e4896a446d220890e8486b24325216e90964844a41f120e8905d4823240d1204e9015480423f9d1fa08fbe47cea3df11ec08f44479ba3c811e128ef2476b23b111d5a8e96473fa39b51cb68e49471e238a91c308e0b46fa237891b968dbe46d8a36911b2e8d58468ca335519408c574609a2f3d17168b514586a2b6115328a55450da275d134e8963448fa236d1142885d440ca1f7d0f4087574389a1b150d34865b4315a179d0b46855a428b2132108f4843b4200a0f090710834e4187a0b55052c8252410c2072903208147408420325010080373ff99fed0feea7f223f6f1fa7cfca27e123ee49f614fa6e7ce93e4b1f1acf8267bd93dcf9ed94f6607af13d5e1ea1cf4867a043cdd9e618f2a279033c621e200f09677f83bd29dd84ee2676d43b431d8ccebf275ce3ac51d518ea0474c33a3f9d0d8e7e473a939bf1cd4ce64672ee395c9ca10e4bc722938fc9c724e328715a38929c3c0e1767077381e9c034dfa66fa837af9bc58ddc26ea2373b9b944dc426df136de1b61cda866d0436679b240d8ac6c1735e99ae78d6be6b2535759aaecd50c6a4c35091a79cd35a698234ae1a4b0d1f868c7344b9a160d04667ee33da19de8ce8a6710336b19a84ccec664b330d997accb62656d32a1193e4c99c64a8323499058c7cc63c031c598d1cc5fc62c9314c98990c44a61e630d8985f0c28e6108306e9828cc0e66043300717f78bf705f882fa997ca0bddc5eb42f3)) else (if j<7 then (0xe0aa1f0581544a0f428074120070400981e0551003d0c01800482e0981e0500f4200600101002a09a2107a170551003d0d01a0260360b82a09a2107a170551103d0b42406809c10026078154400f4300680800502e0981e0500f4200680800482687a148390881a00382687a148390881a003a1e8520e4220600a0038400d8340c82a09821078170531003b0d018030020100360c82e0a8260841e05c14c440ec2b09018030022099230801f4701403b08018005026078144400f433080180048270892007d1c0500f8200600140981f061160551203e0801800502a48a1e462144420e4200741200582648a1e462144420e4290881a005c2007d1c462144420e4290881a00592287c16055124420e4290881a00582e0b122879188500f4310a4220680180981e0500e42006000e2085a0f8364942007d1c8551003d0c819a1f8520b1230801f475188551083d0b4220670741483e0d82c87a144400f4350b42206692307919051110390a4240680c00582e48e218791985e1503d0c42206c1603801c0b923879198540f4310881b0580160992387919851118390881b0580160861e05e144460e42206c100380160b9238861e466178540f4310a4220780e00702e48e1e4661503d0c4290881e00582648e1e466144460e4290881e00582187817851118390a4220600e00582c08e1e0661503d0c0280881e00582e48e218791985e1483b0c4240741603801c0b923879198520ec310901d05801609923879198520ec310a4260780160861e05e1483b0c429098180380160b9238861e46617851104240741603801a0b92387919851104240741600502648e1e466144420e4290981e00582187817851108390a4260600e00582d0a82387819850108380901d05801848e1e85a14c49118390a4260780160861e853124460e429098180380160992387918851118390a4260780160861e05a144460e429098180380168821ec7119851118390a42607801687b1c05e144460e429098180380160992287919851118390a4260780160821e05e144460e4290981803801649620c791b85b144410d82a0781602c01a0a1258811b859104390d82a0781602622107a17051110390a4240680c005a1e8520e4220700a00391e4510f8210680900391e4510f021060090039250811b0590c82a06814024a1e8520e4220700a00385b87d17055138440f83207801448e218791985e144460e42206c1603801a099238861e46617851118390a4220780e0070520fe1f45c1544c0f8330a81b0580184962046e164390c82b0981e0580960a1258811b859104390c82e078160261238861e466178520ec310a4260780e00682648e218791985e144420e4290981e03801c0c92187a14c4e0f82c0781103801648a16853124460e4290981e0380160c9218791783e0b01) else (0xa8268821f8551103d0d81e03801a1c8360a82648a2087e1583d0981e03801a1f84c0b32087e1583c0b01d0580161e83609a2087e1583d0b01d0580e00606a130300b2224821f8560f8260740e0068720d82a09c1ec62168531383e0780e0068760a82787a168551103d0d81e0380181c8360a8278791885a1583d0981e03801a1d8520d82787a1583d0b01d0580e00606a130300b52107e1483b0d8260780181d0300b61f45c148420ec360981e0060741303e0b42b87e1483c0b01d0580181a84c0d8300b61f8521083e0981d03801a1c8360a82648c2107d1d8560ec260780e0070720d82a09e1e464170551383b0981e03801c1a82a09e1f8511103d0cc260780e0060520d82787e158390b01d0580e00586a130300b4224841f4761583e0981b03801c1c8300b61f061170551383e0981b03801a1a84c0d8300b61f8541103d0d82606c0e00704c0f82c0ae1f8560f02e0901d04c0e00684e100320bc230811f47314c3e08c1e02c01c188400c82ec7c190591544b0f8230780b007062138320ba2cc7b150410f43608c1e02c01c1884e0f82e0ab1ec530f0290741602c01a168520f82b0801f4721483b0d428074120071668dc2007d1c8531083b0c01a0058520f8308b02b0801f472148390ac2007412007a4c8b1230801f473188531083b0801a00684c0d82c0a82707c150390901c00582a48a1e462144420e4200741150801f47118851108390a42206512287c16055124420e4290881940d82c48a1e4621403d0c4290881961484c0c02c48c2007d1c8520e42206801a1484c0c02c879190581544a0e42206801a1484c0f8360c02c87a144400f4310881a0070520f8300b02a87a148390a4200741200682c0992307919051110390a42406582a09c1f051100390d01c00485a0f8364901f472144400e432068018168520f8368791b05815449100390c81a0070520f83687a144400e4350b422068018168520f83a4e02a87a140390d4280741200705a1483e0e8380ac1f0500e4320a01a05001c16852120460fc1e4581444c0e828068140070721484c0c02d078184581444c0e82407001c0d82a099220791d0540f01c0051705b05a1481e475190581544a0e81a00685a0f8364901e472154400f432068018149220791d462154420f42d0881a0061665785a1483e0a9220791c8520f428074120078721a852130300b0224801e4741503a0901c00786a1683e091200791d0521003a0d01c00682648e1e466144460e4290981e00582648e1e466144460e4290981c038018130300b1228801ec75190551103d0b42407001e130360c02d07c144400ec350b42407001a190561003c0d8340a82687a154400f43206801e1884e100360c82e0a82748a1f462154420f42d0881a0090601283c0c82a0a02687a1483d0a01d04801c561505183)))) else (if j<12 then (if j<10 then (if j<9 then (0x20420e835098016148420f8380420e8310b01d0580161e06a1101a06216849114350980961e05206818852124440f42600516c1604b07d170551383a0a81a0580185b96c1685307d170551383e0a81961d87287d1905c1544e0f81e0380161d06ac821f8541103d0d8260780161c86a48a2087e1583d0981e0380161f87214c1e863168531383e0981e00607a1cc1ec62168531383e0780e00587414e1ec5a150440f4360981e00587214e1e462168560f4260780e00587e1ad2107e148420ec360981e00587a1a83f0841f8531083b0d81e0380181d83f87c170531083b0d81e0380161a83e0dc2d87e144420f4260780e0060821ad2107e148440f8330981e00587a1c86a48c2107d1d8560ec260780e0068761c8538791905c1544e0ec260780e00687e14d2107e1583a0a81b0580141e83f0841f8560ec2a06c160380161d8520fe1f05c1583b0a81b0580e0060741483e8ae1f8540e82a06c160058520f82b87e158390a81b0580e0058821a83e4841f8561103e0d81b0380181f8721ac224841f4761583e0981b03801a1e06a11622c81170460f8360b8230260741a83e0de1f8541103d0d82606c0e00687814b1f459150420f83608c1b005a270841f47119851118390a4260780e00692387c17055124460e4290981e0380180a921879178541103d0d8260640e0060728da2a89c1f464170560f81e0380181aa4c8c22d4841f8541103e0981e0060728da2a899230841f8560f81e0380181ca368aa278791905c1583e0780e00606a930368c22d87e150440f8260780180b82c0a92387919851118390901d04602e0b42107d1c466144460e4290981980b82c48e1f05c15449118390a4260660360b82a0992187c190551383e0640980b82c48e1e4661503d0c4290981960b82a09921879178541103d0d8190260360b8264861e45e1583c0b01d044098178581284707d170560e82a068160060841f8721c0521341f065170560f81982107a1d8721bc1f464170560f81962087e1d06b4841f8541103e0650821e86a1903e0dc2107e154440f81981f87a1c86a189230841f8560f81961f07a1803e0ac2107e1583d0b01961e06a1584e11041884170450f82961e074168521361f45c150440f81961d85a1583e0de1f05c154440f4360660761c8521384d8791905c1583e0658761484a1203e0ae1f05c1583d0b01981d0521083e0e8308ae1f8540f02a0660741a8400f83787e144440f81941483e0c8300ae1f8560e42c06502c09c230821f8721483d0881a00582c09a1f064168561283d0881a00582c09a1e8541083e0d4220680140b02687a1483c0b4220781200502e0b02707c150390901a0300141f8720c02c87c1945c1544e0f82607801a1c8360a82687d1905c1544e0f81e03801a1a84c0c02cc821f8541103d0d82607801a1e86a) else (0x1d04582f0841f47119851118390a42606582e48e1f05c15449118390a42606582e48e1e4661503d0c4290981941e8761b96d07d1905c1583e06507a1903e0d9250841f8551103e06587a189230841f8560f81901e8605783e0aa270841f8560f42c0660761583e0da278791b05c154440f4360668761484f8791905c1583e0648761484a5183e0ae1f05c1583d0b01981003e0de1f8511103e0640520f8320ae1f8560e42c06482e09c1f0540e4240680c00487a0d82a09a1ec751905c1544e0f81e00687a0a8268821ec76154440f4360780181e8360a82648a2087b1d8560f42607801a1e83609a2087b1d8560f42c0741600616c1a85a4921e46c170551103e0780e00696c16c364921e46c170551103e0780185c16c149228791905c1583e0780165b15e1685251c2a87c170551383d0b01e00706b0d92448a2087e144440f81e0059665785a0f9390a9248821f8540f4350b01e00795e14c2a48a2087e158390b4240780181d8360a82707d1cc62168531383e07801a1d82a09e1e85a14c4d1103d0d81e0060760d82a09e1e462168531383d0981e0068761483609e1e85a14c4e0f42c0741600686a1161e4691885a14c491103d0981e03801c14c378791a46216853124440f42607801a149420f9380cc2b87e144420ec310b01d05801e188360a82648c2107d1d8560ec2607801a0d82a09e1e464170551383b0981e0060400a82787e144440f4330981e0058520d82787e158390ac240741600582e0b02707c1503b090180300140d82e0a82648c1f470178560ec260600e0070360b82a09821879190551383b0981803801c0b82a09821878178511103d0cc260600e0070360b8260861e05e158390ac240741003801c0b92387919851118390901d0480e00602f07d1c466144460e4290981a0380180b92387c15449118390a4260680e00602e48e1e4661503d0c4290981a0380180b8260861e05e144460e4290981803801a0b82707c150390901a0300121c86e5b02107d1805c1583e0680e00606a1903e0d1240841f8551103e0680e0068721a8620b9220841f8560f81a0380181815e0f82a0a2260841f8560f42c0680e0070560f8360d2278791a05c154440f4360680e0078721484e0be1e460170560f81a0380181484a5183e0a829878170560f42c0680e00706a1003e0d8340be1f8511103e0680e0068520f8320b82a0a61f8560e42c0680e0068360b82a0841845512c3e0b8200259708da2a89c1f4751905c1544e0f81e00682e48e1e4661503d0c4290980e0058521083e0e11103d0c02a068160058721c16c14823078190520980141a92408c1e0440e8260040781484c8b11a064154481103a098018148420f9380440f4300a8240741600602e48e1e466144410901d0580e00586a091230781083a0d80101e052069190551)) else (if j<11 then (0x60c02d8521083b0c826065a2a8991b05c15449100390d80942086a0921f8541003c0d42606506a158440d01a85b130440d42d0980981685206a14c4c1003c0d4260650741aa2c4941f470100390c486a0f8360d2264942107d1c0390c587414a2c46d17055120400e43608586a0f8360d227851100390d426065a308b11644c1103d0d82101d8721b96c89c1f470160511383961d83e8991a0581444d1103d0d80961d87214a26460160511383d08505e1604a4741544a0a81a0580141e86a0fa26490200791d03d0c507a1c86a899220801e47508486a130300b1228801ec741503d0901e03001c1a84c0d8300b42707c144400ec350901e03001e0b02648c2007d1c0500ec200780800602c0981e0511003d0cc200780800582c09c224801f4701403e0801800582c0981f061160551203e0801800582c0a92287918851108390801d0580a00682d0801f47118851108390a4220780a00682c48a1f05815449108390a4220780a0068360a826484180551283e088190280180b82c48a1e4621403d0c4290881e02801a0a826481170400f4360840a00502c0992045c1102c0840a0048360c026481168540b820074110280180b0270821f05a144420e4290881c02801a0b026078140390801e020012210725b05207c180560880122086a0f9250801f472154400f4320780a00707e1c86a0b1230801f4721483d0881e02801c1d06a0f8360b21e8511003d0d4220780a0071705b41f4751905c1544e0f81945783e0aa270841f4761583d0b01d04607687b1d464170551383e078014189228821ec761583d0981e00504e100320b92287e1583d0981c0380181ec1f4731885a14c4e0f81e0050538791885a14c4e0f4260780145785a14c2b07a168531383d0b01d05801a188400c82f879188560f4260700e00607a0f8370841f47614c420ec360780181d83e0de1f05c1544b1083b0d81e0060400f83787e144420ec350981e0059705b05a8dc1f05c1544b1083b0d81e00695e1683f0ac2107e1483b0d42c07416006862138360c82f87e144420f4260700e00687a48c2107d1d8560ec260780141d8538791905c1544e0ec260780165b0530791905c1544e0ec260780165995e14c2a48c2107e158390ac240741600707a0f82b0841f4761583b0a81b0580181d8520f82b87c170551383b0a81b05801a1483e0ae1f8560e42d0881b0580165b05a14a2b07c170551383b0a81b05801a1884e0f82e0ae1f8560e42d0881b0500e0071705b41f4641544e0f81a0380145783e0aa2707e1583d0b01d0480e00602e0b02687a1483d0881a004a270841f47119851118390a42607801848e1f05c15449118390a4260780168da2a89c1f464170560f81e0052368aa2648c2107e1583e0780148da2a89e1e464170560f81e00502e0a923879198511183909) else (0x81c8300b21ec74180520040720d82a09a1ec74160551283a00586a130300b21ec741003a00486a0a8268821ec700f4320048720d82a099228821ec750880141a84c0c02c8892087b1c801216a1ec741a0500e800e1c8521302c87b1d0601480121d87209a1ec74160551283a0050741a82c87b1d0400e80101a83e0dc3409a2087b1c03d0c80161c86b0b82c099228821ec750880161d96c0d82a09a1ec741705513839618836099228821ec750840720d82a09a1ec74170551383c025872188360992287b1d42402484e0d82a099188531383d084872138360a82646214c4e0f42402582e0b02687a1483d0881a0280141f8360b82648a1ec721742202504c0d82e0a826881188531383d08809809a2307e1d0540ec2407001209c1e8641584c0ec2407001209c1f0521103e0cc240700120b82707c1503a0901c00402707c1503a0ac240781400487a5b0360a8268821ec741544e0e582a099248821ec740f43101e836099228821ec7508407a1d8268821ec74170551383941e83e0d8268821ec740f43121e862099228821ec7508407a1c8260821ec74170551383c02587a1a83e0d8260821ec740f43402587a1c86a188264882087b1d4240258760d82a0991885a14c4e0f4214149460d82685a14c4e0f01d0450761484e0991885a14c4e0f42141d8520f82a09a168531383c0741161d8721484e0991805a14c4e0f4240260761483e0a82605a14c4e0f01d05009809c2287e1c8520f4220640a00502687c188561283d0881902801409a1e8541083e0d4220640a00502e09a1e8520f0220640a00482687a1483c0b422078110280141c8360a8268821ec741544e0e80961a82a09a2087b1d03d0c80921c836099228821ec750880921d87209a2087b1c05c1544e0e80961a83e0d83409a2087b1d03d0c80961c86a0bc2c099228821ec750880961c8360a826462168531383d0880961483609a168531383c074120250721482f0b026462168531383d0880981483e0a82809a168531383c0741202605e1604687c154480a0180580141483e89c1f472168531383d0b01d0460520fa2e8b2270841f476158390ac2407411c1483e0a82889e0e42d0801904506a130300b21f8541103d0d02606587e1c8520b02287c190551302141f86a0b02287e150440f4340981961d0520f82c0420ec340b0240741161e82e0b42107d1c461104290850360b82c489198540f4310a42141c86a0b82c899230841f4710850520f8300b6144440f4300a4220781181a83e0d82e0b2278511103d0c42606602e0b21e8520e4220700a00482e0b41f0540e4240680c0048720c02c88a1ec741482101a84c0c02c88a1ec740e82121a84c0b2224821ec720840721484c0b22287b1c0641482141d06a0b22287b1c0440e82121303e0b6148420ec320901d04506a1303))) else (if j<14 then (if j<13 then (0x3d0c4290880941c86a1882e8992307d1c42202506a1003e0d82e89e144440f4310981a02686a110400ba16c4c114340b0220258520f91103d0c0290881a0448520f8308b02a4a60e02a0801904585a0f9240780e4320680101a83e0da264942007d1c851100390c81a00703e0da268791b05815449100390c81e02801c1483e851100390d02a0781200506a0f83689a1e851100390d42206801816a1f068150400f03200406a87a150400f03200385a0f83b0e21e03c0c01a004a2a8991b05c15449100390c48640f836899250841f4700e43141003e0da27851100390d42606506a1692487b1c46c17055124400e43602685a0d92487b1c46c17055124400e43184922087b1d851100390d42606506a1111a85a14c49100390d4260780981483646a16853124400e4350981961a8640f8360d2264941f4700e43202606a1003e0d83489e144400e4350981a02686a8b12507e140400e4320981941a8441022e46c17448104320a8260260521322c46c15448100390c82606586a0f8364d22d850100390c82606586a48c1f8501083a0c4260648520fe140420e8310a4240741141a8400f8364be140420e8310981961c8705b0521322c078180511280165b05a1481e0511281a0040521322c46916051130400f82200585a87c1b058150480e80101c85287c1805412800e1685212446878150480680121d96c89c1f470160511383921d83e0da264681644d1103d0c507614a26460160511383d08496c1a85a87b1c4681644d1103d0d80985b05a87b1c4681644d1103d0c51705b05287b1c460160511342141c86e5b22707d1c0581444e0e80961a8441022e4681644c114360880960f8368991a059134440f43202507214a26460160511383d0880941c8705b0521322d078180511282161c8521322c061160511383a08507214923078188521242100f81a459128420e83502406a1101a85a124410d42602485206a16852124400e4350848721c16c1484c8b01e474180520058721b96c8981e475190581544a0e81a00686a8b1240791d0400e80101a83e0da26490200791c8551003d0c81a007072149220791d0621480101a9220791d0420e800e1c86a899220801e4721483d0881a0060605783e0aa26488200791c8520f428074160280201e83e0da26490204740f43121ea26488200791d420e5c16c149224711885a14c4d08516c5785a1491cc62168531383c0741600695e1683e8d9240811d8531083b0d01d05801c1a83e0da26490204740f4320250721aa26488200791d4220248720d82a099228801ec750900141c84c0d82a0991885814c4c0f4240060620b02648a2087b1c8520f4220680181f8721482c8881f0641544c00507a1a83e09a2007b1d03d0d00141e8721a82648a2007b1d4240050761c85213026462160531303d09001) else (0x81c82687b1d464160551283a0700a00606a0f8370d02687b1c8551003d0c81c02801c1c86a18c2e0992287b1c8520f4220700a00703e0ac2809a1ec721483d0a01d0500a0068400f83609a1e8511083b0d4220680188dd230801f472144420ec350881a0061661683e8d82b0801f47214c420ec350a01d04802014a3687d19058154491083b0d42206801a1483e0aa1e8520ec350b4200741200606a1003e0dc2e09a1e8511083b0d4220700a0078520d83009a1e8520e42b0801d0480180d8308b0270821f05a148390ac200700a0070520f8300a82687a148390ac20074120068520c22c0a9230801f472148390ac20074120078520f83a0c22c0aa1e8500f4310ac20074120078520f8308b02b0a02687a148390ac20074140280201483e83b0d028070120040520f8308b02a89c2007d1c8520e42b0801d0580a008966579230841f4761583b0901e00596689c2107d1d8531083b0d01e005a36899230841f4761583b0901e00595e8da2748c2107e1583c07801457a3689c2107d1d8560e428064160060605782a89d230841f8560f0194579230841f8560e42b0901e0050520f82a89c1f472168531383d0b01d0469661923689c2107d1d8531083b0d01981483e0c82a89c2107d1d8560e42b0901d047062899230841f4761583b09019507d1cc62168531383b0901e0050520fc2b0841f47614c420ec310ac24074160079668dc2107d1d8531083b0cc240780181815e0f82a89c2107d1d8560e42806411a1483e0c82a89e0e42d0801904515e16852121460aa1ec7417055138390a0190580205785a0f83a4e02a8821ec761503d0c4280641600815e1482a8821ec76158390b420064160068605783e0a82889c1f476158390a0190480e0078520f8320a82889e0e42d080190480981483e0aa2707d1c85a14c4e0f42c0741203801e1483e0ca2e0aa2707d1d8560e42b0901d0480e00815e8da2748c2107d1d8560f01e0058721482c8881f0520900100b02a8992287918851108390801d04801a0b2270801f47118851108390a42206801a0b22648a1f05815449108390a42206801a0b22648a1e4621403d0c4290881a0060721a82c899230801f472148390881a0068721484c0b226879190581544a0e42206801c1a83e0d82c89a1e8511003d0c42206801a1483e0c02c0aa2687a148390a420074120070721482c87c180540880101a82c87c1003c0881a0040520c02c87a0f02c0801a0048521302c853130400f0220680141e82e89c2107d1c461104290850360ba26489198540f4310a421418a2648c2107d1c420e1003e0da278511103d0c42606502e0b41f0540e4240680c00485248a1ec711905c154490849228821ec76144440f4310981941483e0ce144420ec310a4240741160ba260841f471184410a42202502e89922466150)) else (if j<15 then (0x3889685348c10838a85511038693436125b1003e18740da1083b0d408c8ed221237460545829bc268540e226f09a1501889bc3685069bc2a142cc920e1c30c90509b228821e42c06342ac8a210188c6a1483870bc2c8821ec7508342f09a2287b1d408d0b21685313420b09a1083b0d408a5b606102e0b42042080b82d05908202e09c104088210721b96d058a2086a49061f86248c20204e131190588100364d410244d0440e1c3705c141c2b05c06196f81845ac3f81870aa21018658e06161e8511103890da16850655e1e45c0e2156930453e0e114185044ce1e1062138400c82e09a1e8520f4220680180d82a099228801ec741503d0901c00604c0d82a09c1e462160531303d0901c00682a09c1f0511003b0d4240700140d82e0b02a09a2087a168520f4220680a0070370b02a0992207a170540f4240680c0068370b02a09a21079180540f4240680c006c2c0a8268841e85c144400f4240680c006862099228821ec721483d0881a0058630b8264882087b1c8520f4220700a00684009a1e8511083b0d4220680141042e09a1e8511083b0d4220700a0060360b02a09a2107a170540f4240680c00682648c1e464144440e4290901c00582c09a2107a17051110390a4240680c00682c0981e0500f4200680800487e130300b1228801ec741503d0901c006874130360c02d07c144400ec350901c00687a0f83609a2007b1d0551103d0d01c00687a099228801ec741503d0901c0058760f83609c1e85814c4d1103d0d01c0068761484c09c1e462160531303d0901c00683e0d82707c144400ec350901c00585b0d81ec7216053134440f4340700185c0521342c07b1c462160531303d0901c0070370b3248801ec74144400ec350901c006852130370b41ec6a16053124400ec350901c00782e09c1f0540e4240700100992307919051110390a4240680c00602e09c1f0540e4240680c00482c0992307919051110390a4240680c00686a0f8268801ec74154440f4340680c0068721ac2c099228801ec741503d0901a03001c0f83609c1e85814c4d1103d0d01a03001a1c8521342c09c1e462160531303d0901a03001e1a83e0da350b02707c144400ec350901a03001e0d82a09a1ec75190581544a0e81a00602a09a2087b1c8551003d0c81a0058360a82648a2087b1c8520f4220680180d8268821ec721483d0a01d0480161d82687b1d464160551283a0680160f83609a2087b1c8551003d0c81a006062099228821ec721483d0881a00583e0a8268821ec721483d0a01d0480181683687b1d46c16055134400f43206801a14a1ec75190581544a0f42206801616852125460aa1ec74160551283d0a01d04801e0da2087b1c8551003d0d4220680161683e0e82a8821ec721403d0d428074120070520aa2087b1c8520f42d0801d04801) else (if j<16 then (0xec7416387a1892287b1c287a1d86e5b4208531238761391885312296c5794685313018c1e8640d9250820ec30e1d8560f83646c1683b0c40400d91083b0c296c4911a83b0c287a189230830828761391905b08295e4890ac2406287a1815e0f82b08206c1101d84a5182b05a06c10e0c82a42a06c10a5b15e51c1481b04302e0990880081e87609a2087b1d05c1544921e862099228821ec750840368851b0540e2a21464141c488840618368821f4440e2a2142c06187a0982087c1705512387a188264882087d0838761382646216853134211492168540e25230791885a14282a85c061a168551103881d84e0991805a15420e1023748910838a1023746060cc1f018709a168540e21710991885a142c268540618570da14197013a14184b0a845c2154440e206e15c368540e286e12c2b0188103244420e23254620e1b2542c061c26c8a1e42c0628330ab2301890eb2301860cc2ac8c062040c6a14838948b1a85110838a13840c6a14838a59b108390b018a1d8268821ec7017050e0bc2c099228821ec70e0da2146c15038a12c48884062121056061a2142c061c0a082f0b02685a14c48d492168540e22168551103890460e10408dd1883885b05e11c14810a5b05e11c1481a04332502c06184a1202b05c14018c1802a8810a223a81840a90a107e0b02287c0e2b2502c06182e0b22708108282e0b22648c210790838740b21e0440e282e0b42688920878c13223038646414121f8511103884891103e0622230184878301828640e140e082e0b4268420e2d16838505e1483870ec06122c4941e0400e430c4911b0501020364921e46c17050c8920e120e0a1f02e061d2286a140420e291a85110183646a168511028408520e1d170521083880de14440689c1e05814448a8991805814448a1321e46c11038a1b91a05c0e221e45e0619168384131168386139408520e221183850382899220801e470a82830bc2d09a1ec70b0b214c48709a0ec30681b04122d4940e1c368b0489d190520e205e11c1481081f0490520620841e8761c86e87b1c38821f8741aa1ec70c1f87a18a1ec70a2107e1c04c8531230841e8761c86e8531238781d05a1484c8531238761384c8531228821f8741aa0ec30c2087a1903683b0c3076168560f83683b0c38741003683b0c28821f8741aa10c20c1f87a18922c20a1d84e13118c20a2007e1f0520c206c10e1f07a1803e0aa06c10e1d84a1202a81b0430741083a0c206c10c0c8300aa06c10a2087a1903709120c08e1f87a18c224830230781584e10116c08c1d0400dc10c08a1e074168521320ec00e1e87687b1d05c15448e1f87487b1d03d0c307a48a2087b1d420c1fa224821ec7502351b05411038946c170540e25188385120345830e8342c06142a48041d91885a14c4d08324d4940e1d2485a150) else (0x1f82c48a20078a1d0360b110038a0b02642202207a099228801e287609918858142a160540e1b1a858144400e287609a1f0581428740b21f0400e2c2e0b02648a20878d0b82c09a224821e304c87c10183687d1b05814038c87a0e104887c161a0e0a1e850487c0a12140a1e83848821f4280622140c0a0a150405040283a06151905814838848c2042806206309a1ec7508284e8531342081042683b0c203281b04182e09d08800889a1f46417050a89d2307918850a89d230841e4420e3227464170520e296c89841e8765c06e5b226307a1815e0f82a89c06387a1d86e5b21))))))
def genIndex8 (j : Nat) : Nat := if 5 ≤ j then 0 else (if j<2 then (if j<1 then (0xb122638cf000f15258a653692301f000908270c573e1643453235432f00000dedb9492df428ee980f000f000f00023bff000e05eb183f0006404eb89f000f00032b2f0003034b1ccf0006872a079b87108c313e3f000f000f000c012b2bbc3263136840102f2127653507125e44cf000b1d8f0005201d118f000f00040bc636d226e2449f000d03880ff83148b69cabcf000f0000afc8128f000f000f000f000a0f72be5f000d0cbd094f00003607206234b88cbf000f000f000d1fef0006a35f0005225d2a5f00050e03ba3729b0394630d1377f000f00013433157b2bf84264b04e08ff3fbc392f00053c3f000c1b8d1eca924f000125cf000e466f00022841088d39ff0001172f000f000bc6cf30a4289e3fa233cf000f8a509bd50cef0009b97f000f000f0008b74d37abbe0c10ea8481436510cf000ac60245fa272495c3058b1ae3bab82b7936f607fe0b7919cca9bc0aef000f000f000cb9823b6a3bbf0003304295df000f000f000f00092c9f00050f9d0d2f224d8f0c074f0001319f00040d7b329d01ff0008155e17591d9f000217df0000053d135f38ac3aa7408f000a248a30841a2f000e3bdf000f000c22830d3f000912ee2c4f000f000542fb04af000f000f0006419f000614681ab609d383d834cf000f000f0e9f000f000f000b459f000e0eea0dd428a8176c02de3d14332c3fd5413132a51f9f000a86dc1b7f000c43ce0f04249f03ac2f522166435f000d8b5a421416e714ff000b40d53cd609852f8b4456c1520eb117a284cf000c127e063791793a631fbec05412cf000d3bc41b07030f000139ad059f347ead2f0004ac8f000f0000361f000f000e3edf000535bf3510286f000f000b2076290d393f020f000242491e651e0b84de27508ca037c508eb142d15de24ef000f0002b37f0001285215bb2acf000f00002fe9189b23e2a411ad6f000f000d20cc0f6f00030c4f0006089f000e1b232b3b17892e4b1294bb9f000f065a38de3f06390f000023b2184f0000aca527bd08bbbd1f00042e62223f0006288519027400099001005d090da3824430030a5a8100711834234108a0c4201bce44600018854628000d1414c401964200318002510208c3866880040800412432080c584205704140100800510118224414828419a4511090040031030460850020c820d2c52431041df0410065c00c50830040c7ac20024460c740109204f0030021c718204338d74020801d2070001831171410161803430c108408500500114400004700a0890c02870001811001020070c704b3d328b0c30811491804200cc0000802c000704c08505d40568100504000000000e0080022400800c00000028c12400400041030850c00c20c10010400810530000811820cb1046863460410011891010000400c50dd1c23c8443445003108) else (0xbf511ed884f000013a525a521bf000333bc08ab31cf000e00af000f000f00008c4f000431f4b25f000f00073d6f00050db7092e2d3f000f000db59f000f17b31938333a3c6f000f000824a0894e1c2f000f000da15f000611f509f21eef000a21ef000a1ed188bf000f1bcf00059dc62fbf000f00091bdf000f409e4063096f000f000f0006141705d90e3ac0933c710b8834d093c2002e3c0f0008291b00bd378f000f000ea53f000bb6ef000e0240028203bf000f000bb10f0003a313adf6292f0000427f0002169f00032ed345de240f00030f8f000d0bd6371307ed456f000f0000c5feba22928f00028f7527f03b9d06e80c7f000f00021cff000b11a4078236e9414bc64f00080fd80a50080dbe6543b2014f000f000f000944db876f000d2680167837ee27d72f43241bc27f000f0d0a2aa34506120a2bc418f0ab67003f0009036ead7f000b9a5f000b42ef000f8145047129f686a292cb0d6f000e0ef08a0f000f000f00080e4c431805593e4dba1d2334103932798a4f0008186f000f000f000f000f000f000f000f000f000f000446ca344f000940ec121f000f000f0006158f3cbf000f000f161108639189001f000f00001d63bbe92a2f000f000f000f0009093012bb463214e5a1223f6304e18a9d181fbbaf000f000f000f000f000f000214913a3f00053740230f00060fc629d31018076da6af00059f9f00012e7f2ce51b9725ef000a316f000f000f000f363f0002281181b493bd3cebc67932083afe446206ac462a2265075f00042b4f418f00050c8944301c52137b10ab1adf00004384386a1a3f0001339aadad0e1f000b384f000d34e23df60b99083b878f000c44bf000025d2823f00021f0f000f000e9294b91f933009ef000a00f505053a0f000a83801f371a8f00050a4f000ab84c32270be806b40f1f00093be3bbc704c3357f000f04183fc64684108f000f000684971d07269f000f000f0003c6a1a05e420f000f000821273a7135cfbdef00031acf0008274f1e9f000f0005044d341a17ff000f000d220a86b3afff000e3d4d899b1e7ea82f00060cfc2eb9173a29c02e2318d81def000f0001c33d1fdf000f0004893c30fb373d040f24c515af000f000ac69f000f00093f20359f000043952997ae672a9f000f000f00030c6d283f000f000f000f00083ba2356f000f000f000f00092cbf00061989bcb6159f452f000630ea97462660bb3c3121ad3a40ae08d4a45b1a090b6e945b1a13117d1b1f896f000f00022d9d37bf000640b12ec2402f000f000427af000f000f000f000d36a5180f000f0001381329e02eef000f00091f8f000f000e353d262f0000134f00028a7f000f000f000701542cafc08029711d4f0467a43f0000425f000f000711103832975b174f00040adf000f000409b31e1f00073dbcbebf)) else (if j<3 then (0xf000f29481c3f00091a6f00042f051132ac7441cf000f000b07de3b8f000c1aff000cb8aec30543ef000f000601b43c11c4e71ddf0000242f00031cd5a99488a50908c37fb600222f0000bb5f20d63764195f3d5242b41e8f0009328704df00002d6116ff000cb7cf000f447a46b74076182e428004920aff000422c718a81e42b0191e3ab541abbf000e0d87465f38ef000b2f6e025f000f433d39543ae2300202e4b61f000a85a60b01217b280f0002aacf000b22bf000a031021af000f000417e10a2f000f000f000f000c084f000f000f000a846c89268a341fc089ae0112278922fb008395ac83f03544bcaf218f000f000f00032311043f000323f9bfbc255e06df46729e8f000f000ab33f0003364f000f000a870f000e1b514537171f000f000f000f000f000f0008367ec53f000f000f000f000f000f000841500d54b5a63def0007130f000a109f0009352b847f000f000b1caf1f5f000a037f000f000cc1bf000b026f3d8f187b16bf0a9f00082c110f5f000f000c3d760b1f000c2b952a3f00032c5e2ffe39641902bbdd23903e9f00063b340edf0005397f105a839f000dc56f000e2aef000f000c45cf00040e724519348f0003200f000f000f000f0005b4ff0005148626a3464f000f000f000f000f00042ddf000f000134ac027f000d0aaf000cbaa73ee9ba5f000c2b8ab20a20e83d9403d8a68c30c5b45b8ab73c4d140f000f00061a5f000e41a503e618c42f3f000f00013f9c86e641d3405d2f783f4e10ff43af0002ad4a2c2831572fc7877f000c32bf0008163f000f000f00041b3f00081dff00043f3312451d7f194f00012eaf000c243f000f000f000f81560776460721d4a9261d1f000f000f000f000f000f000e185f00071c48c103b22f000eb90f0005b1a0b265411b154e01723e8f379d295119db0c3f000c234c0ca1bcd3039f000c20a8ba4116c2925f000fa23910bc0a093acf86cf000f000f000f976f000ebb0a41261bef000f0008334a1a78365422df000f1bb6bfe516a6293f000f0003133f000f000f000388fe02a4c0d8069f0003370f000632df000e022fb6ff00012b6f000d164821f2bb1f000f000f00042a0f000f000b890b2c0f000f000f000f000f000f000d11d8337f000b3e2f000ab93f000f000f00051f6f000f000f000a1c9a40fb31bf0007bb2f000f000f000f000d1b669e2f00013fff0004b71b160c023f00063eab232f000bb884085228ff00081e5400c23d2d303f0006444f000f000f0009398f22a20da90b2407b7b6b20994842f000f000f00033188006f279817cf000f07a0277f000f00048a8c2a7e23d88aa2251b19f1bacf000021c7458f000f000742d20fb61a9bbd04321b213533ed3b1f000f0005018f000a375016d02cc806422dbf000f000d88cd1069338035ff0008c62a) else (if j<4 then (0x2ba632ff0005b7062d4f000f0004317f00021c1f000c302f0006116124ff00061ebbb41e382e071dc362a2cf000f00088c2a1aaf000637df000c372f00081fff000a296c097910db3c881ea70a870a3f000f000205123b4bc1e3b56918ef000a01ef0001a14f000f0000c6be1197c1cf00098c161ba2168a12a6b19f000384a6a86f00068748bf3408cf000112fb24df000c8c8a211d247f000f000f000f000cbb4f000f000f000f000f000f00003917336128223462a6dea9c9112bbad2019a873f00042fd9a1df191cab7012db271f000445e502ff000d9a7426562c690b5b15189e9f000001d1b5ff000b132f000f000444a53ab5ae5f000f000f0007454e045c34213c980b3f0007b73e335744188af713dd143d0c0b2a69c5990d9d3996110e0577203b210f0613b3fd310b236f21482cda263687c1903f000211c6366335823b599f3c3f8e2e8f14d7253f000913edaded897b3d373da231d1197f000f000f000f000f0000147b3850257fb0310425349f00024032bcc3a5f20ec434f8331f000b32ef000f000f000f0004a57f00070e6f000a15f83f5f000f000f000f000f000c14cc41b6202b9ecca6cf000f0002b21d43dc8889162fb42a204e926f0009330b2b573cac854f000b457c05bc2af8c57b229f000f000d06050cdf0dfb1ef638ff44ff000f000b1888138c1d373a51115dc5ef306709c02e3f000c26461cb20ea322ea0a601008c16197bf000f000f1f1938033a420629199f000f00073b0f000a3e5c88e90000007b2da223ab27e3410f1d552d8f828031a933d22383156f0001817f000113cc39db2e14a10f000f000f00018cc842a9c2e3056939bd40c3915a287f20b88c92235f000f000f000c44ef000f0008430227cf0005852f000f000f000f000f0003311bc3ff000f00043cff000b325c029f000f000f000f000f00060ba11cef000f0a1f000304fc440d35a6abff2d1c09562f1cb3af1dad26110a7f000a448a25092a89429d0b401db097702abf8f69be9d345f000f00073a1f000b2f90ba0e2c343d0f0005841f000f00043130beef01cf0002177d33a91e2921521c7f00002279455f000d2d7f000f000f000d469f000f000c2cf00f28054438bf000f000d0f4f000f000d032f000dc123355046a63099245887f531ef000b19bf000f461225bf000f0006048f000f000cc6120cc541ee010f000f000b2dcf000f0007246643ff000f000f0004091bab4f000a0812067e2be519a836b0066f00040fe82b0fc63d11b6104f368a102f000f000f000598db14b12b1f0008298a107226781f21bb6f1f4305af0009b8f9b2f308762d0f00072bdf000f000426df00002a1f000ea32b3c5a0aba3fe4ac5f000f000235ddc014340f000f013f000715e28588c5ad20ff000005f73a83ab98423428df000f0004aa722d2f000f) else (0xf000723c907c0270f000f00063a2eab3a02bf3891244f000f000f0003305213911b4a8a2bb9ff01a726ca04b02de2307f000eb58f000d3ecc844f89bf000c03343ad424bf0000bf2e0d449b03be4f273a362f000d26ff000f000f000f000b0c13862f000f000e324f000f000f843f000f000a29af000f000f0009005f000f000e131a8450b31f000f000218bf000735e9237f000f000c0faf000f00042ef402cf45a12e5f0000196f000bbed791ff000f00028377221f0002416e0725af4b208f000f000f000f000a0bbf0003437f000f000f0737a1f941ff000b254f000ea0790e2332cf000f30bc13b236cb1c6f000a4426b83f000342cf0003209f000f000225630d1f000e2faf000f1dc80e870356b15f000283e33ccd33f539e01f74addd9169170619e81a43c54437f40dcf14a605c009a98b250524192f00042add145600eea4251d2c28b014473b7c21911269b8be0acd9596070a3dc000901fa13e70a60239c715383e6d13f088dba2512e9c3b2025fca28f000928cf0004b3272c882d5f000f000f000f000f000f000f000f0003ad5c388f000f0006150f000f000a252f00023f709b6f0006c323259140080c2f000a25853eb826bf000f165306fe2605387f00001c090c9f03ff2a4045bf000da9a0aa1f84bf000f2e03a1af000100df935d3dd706c716690f373f15179f000d3a923e0d422f000f00033efe205f000f0007021f000b1c8f000f000f00052c7f00083c2f000c004f000c4174016012381bf2b3940e5f15c01140acd1068f000f000803cf0001))))
def genData9 (j : Nat) : Nat := if 9 ≤ j then 0 else (if j<4 then (if j<2 then (if j<1 then (0x5c83f692a41fb49320fda48907ed23487f691a41f7cd930fbe6a987df344c7ef9a261f7cc930fba6c987dd354c3ee9a263f74d130fba64987bf43507dea3281ef51543f7a8aa07bd43507dea1a81ef50b40f7a84a077d54547beaa2a1df54d51efaa6a877d52d43bea92a17fdd941bfeec98dff764c2ffbb2217fdd541bfeea98dff754c2ffbaa217fdd131bfee8985ff74486ffba2217fdcd41bfee690dff73442ffb92837fdc931bfee4985ff72442ffb8a617fdc141bfee098dff70486ff3a4437f9d121bfce810dfe73c42ff39c217f9cd10bfce6085fe72d46ff396837f9ca51bfce520dfe72546ff392837f9c851bfce420dfe71d0eff38e817f9c730bfce3905fe7190eff38c817f9c630bfce3105fe7150eff38a817f9c530bfce2905fe7110eff388817f9c430bfce2105fe70cc6ff384637f9c131bfce018dfd76d46febb6a17f5db20bfaeca05fd764c2febb2217f5d720bfaeaa1dfd75506febaa817f5d531bfaea985fd75482febaa217f5d320bfae9885fd74946feba4837f5d231bfae910dfd744c6feba2617f5d121bfae8905fd74442feba0437f5cf10bfae7305fd73946feb9ca17f5ce41bfae7205fd738c6feb9c617f5ce21bfae7105fd73842feb9a437f5cd20bfae6885fd73042feb96a37f5cb50bfae5a1dfd72d06feb96817f5cb10bfae528dfd72906feb94637f5ca21bfae4885fd72146feb90837f5c743bfae3a05fd71cc2feb8e417f5c660bfae329dfd71942feb8c877f5c640bfae3185fd71882feb8c217f5c443bfae2205fd710c2feb88417f5c331bfae129dfd70946feb84877f5c241bfae118dfd70886feb80637f1d121bf8e6885fc72506fe38a617f1c131fe6e0887f310843f983221fcc1110fe606887f106443f882221fc40d10fd641107e721887f331621f998910fcac4887db308c3eb98c63eed0240f6e8320f9f4390fbda84a1ddd4651ebea729efb60982fd380a77e9c041bf4e018df97014efcb80837e5c031bece3305f671942fb38c817d9c630bece3105f671182fb388a77d9c450bece2205f6710c2fb388417d9c410beae3305f571942fab8c817d5c630beae3105f571842fab88c17d5c453beae2285f571102fab88617d5c420bdce521dee72142f7390837b9c840bdce418dee720c2f6b94877b5c850bdae420ded72102f6b90637b5c830bbce6305de73142ef39883779cc40bbce6105dd73182eeb98a1775cc41bbae6205dd73082df3a6a36f9d060b7ce829dbe74142df3a0636f9d030b7ce8105bd74d46deba0c16f5d053b7ae8285bd740c6deba0616f5d020afceba1d7e75106bf3a8815f9d431afcea1857e75082bebae875f5d441afaea2057d750c6beba8615f5d4209fcec284fe761067f3b0813f9d8319fcec184fe760827ebb0a13f5d8419faec204fd760c67ebb0613f5d820) else (0x3df53c753b1939e1386136753561344d32f1314d2f852de12c852b2929f1289526f1252922f5212d20191f051df11cdd1ba51a6d191117fd167d14d912a510950e190be509f907c5056d03810128fef4fce4fad4f8e8f6d8f480f324f15cef70ed18eae4e7d8e5c8e370e25ce028dea8dc98db18d974d7f4d6bcd584d3e0d260d128ced0cce4c9b4c8a0c6fcc558c36cc15cbf70bd84bb98b9acb808b6acb478b31cb1c0afd4ada0ab6ca95ca7dca65ca4dca338a1dca0a49f489e109cb49ba09a8c99789744957c939091c890008df08c288a6088988688849c8268810c7ed87de87c8c7b547a407908778875787488739871886f9c6e646d746c846b946aa469b468a067b0669c65ac642c62ac61085ff45f045e145cdc5b805a2458ec5790567c5544540c52f851e450d04fe04ea84d704c384b2449ec48b447c446b0459c44ac43bc42cc41283fcc3e703d383c003aec39b438a037b036c035d034e033cc3294315c30482f342e442d302c402b502a6028982760260424a82370225c214820101f201e0c1cf81c081b181a28188417701638150013c81290111010200f300e400d500c600b4c0a38092407ec06d805c404b003c002d001e000f00003ff99221ff9cd10ffce2987fe704c7ff31a21ff94d10ffca2987fe43443ff20a61ff8c530ffc42987fe13443ff01a21ff5d930ffaec887fd75443feba261ff5cd10ffae2987fd704c7feb2e41ff59530ffaca907fd65443feb2261ff59120ffac8887fd63543feb1a81ff58d20ffac6887fd62443feb0a41ff55131ffaa8987fd54443fea9ac1ff54d41ffaa6a07fd53443fea9221ff54560ffaa2a07fd514c3fea8a41ff50d60ffa86a8ffd43543fea1a41ff50d10ffa84987fd41583fea0aa1ff50530ffa64a07fd32443fe98cc1ff4c650ffa63207fd318c3fe98c41ff4c560ffa62a87fd31503fe98a61ff4c520ffa42b07fd21543fe90a61ff44e10ffa26887fd03c43fe81a21fec1930ff60c887fb054c3fd82221fec0d10ff20ca87f906503fc83261fe41910ff20a987f905483fc82241fe41110ff207087f903443fbbb221fddd510feee8887f773443fbb9221fddc110fee65887f732443fb8b221fdc5531fee2a887f714487fb8a221fdc4d10fee24887f673c43fb39a21fd98f10fecc6887f653c43fb29a21fd90f10fec86887f613c43fb09a21fd80f10fec06887f576443fabaa21fd5d310feae8887f573c43fab9a21fd5cb10feae4887f565c43fab2a21fd59310feac8887f563c43fab1a21fd58910feaa9887f554443faa9e21fd54d10feaa5887f552443faa1e21fd50d10fea85887f542443fa99621fd4c910fea2c887f5154c7fa8aa21fd45310fea2910ff514487fa8a221fd44f10fea26887f512c43fa89221fd40f10fea06887f473443fa09a21fbc8d21fdcc4887ed2)) else (if j<3 then (0x18040040401c0a0380c003044160a048200a041c1e0c058240e03000e0f050200c03000c0f0501c0803000c0f0501c0a02000c1f0b844180883c180a0441a08b07830160903a140682001210058200e0642a0d0401241e0a040190a034100080802c10050220d0401201e0a038100682000e170883011078301408403c180b0481c06001c200b0401c0c01181e0a04018060018200b040140801181e0a03810060018200e0501d0803000e0f0602c12074200c0040401608038190a8400900f050200c84018007078280e05420080038401c0a0380c00303c180b0481c06001c200b0401c0c01181e0a040180600181e0a03814040018681e88034180b05025108743404c08038148803a18060020220b0502410874301408483c180b04a200e860180090802c1087430140801201e0a03a180803000e0f0501d0c0501000711c401a0c05828130120200e0501c060018220b050241005020e0f0602c12070180070802c1005020046078280e04018006078280e050100060f04a220c45a2410070341608584016890401c0c011c1e8b0522410060180080802d1489040140801201e8b052240e0401800807a2c1489038140400203c1a094441a080381a0b0428200b0401c0c01181e0a04018060018200b040140801181e0a038100600181e0a038140400181e0c058240e03000e104702c100703004707a3814080300c0038411e8e058200a0400900f470280e0401800707a3814070280800383c180b0481c06001c200b0401c0c01181e0a04018060018200b040140801181e0a038100600181e0a0381404001ae856e66ae47ee2fee112df26dd16dae2d8f6d70ad4fad332d1d6cfeacdfecc12ca26c85ec696c486c29ac042be56bc46ba5ab86eb63ab44eb286b0beaed2ac7aaad6a8a2a692a482a2baa0aa9ee29cf69a7a98d697329522935a91b690128e6e8c5e8a4e87f685e683fa81ea80227e127c4a7a8278ba775e7596738671766f666d7a6b6a697e676e653a63de61f260ba5f5e5dde5c5e5ade5982584a568254ba521a4fc24d6a4ba249da47a6466e42f641523fae3e523c663ae6398a377a35b233ea31da30122e262c5e2a4e288626be24d222e621421f7a1dd61bc619fe1836164a151213da11ee0fde0dce0c2a09f6079e05b2040e01b5ffc9fd71fb85f8e5f6f9f4a1f291f081ee29ec61ea2de7f9e5a1e3b5e115dee1dcd1db09d8d5d635d401d1f1d005ccd5cac5c891c519c32dc141c009bed1bd2dbb65b99db769b57db36db181af71ad3dab99a9d1a809a665a4c1a2f9a0c59eb59c819a4d986196519465925590698e118c258a398829863d8451824180557eb17ca17a6d785d760573f571e56ff96de96bfd6a35682565a963bd61ad5fc15d455a5d584d5685549951b14f594c4d4a19489946ad459943d1429940653f51) else (0x200c02001c471006830160a04a15068280962387834180b04c1d0a0341400b0f0703212888361807030160883411a1e0e050251006c2c1007032150682809c1e0e054250f06c2810064280d0500343c190a0421e0b8541d0a034100600687832150a0421a0b854250a8341004d0f0642a140802e1107832150682009a1e0a850200b84016088341004b0f06828100581406020092290f85428138843e170a83a14068280c00f08034180a04a150682009210058200e0642a0d0401243c1a0c849200d458200e0682c110268783415092421e0d45c2810070340d03003c2e1308a421e0c45c281107028120681801e3012878289087a2e15070280c0481801c13888401f0e0501c068100141708a40170a848200a0440941307c30160a8481c068100141708a40188b0441e0c0502204b0983c150803c180681001213078280f0401a0400404c1e0a03c1407024080090b04c1e0a0380c02002022900622c0e060281102483c14080300d02001c1e0a038100681000e0f0501c0a024080070b04c231047832168a0421c0a0441c05007858228f8582a120843814088340181b0a850261047c30150943a0c0280342e1608a3c188a03c180a0441a00c0a84c208f05a2a10078320c0280303615098411e0b454210f058220c02803836130823c168a43c14070200a00c098411e0b450210e050220c028030289288236168843a1a0b0381404c09a46210f4642e148883a15090380c00e180943414894421b0b832150682809a1b0b054269087a2e150883c16090340c00f0b04d1e8a43c1107014012200f06c32170a84c200f058280e0300800f078280e0300800609a44200f470280e030012130782910074300c00404c1e0a03a1006001d221007a3814070180081687c360f052200e8601800a1489830164883d180a4401d0a8401800e078280e050100060802c0a03010046168a4441007a3a170a83a14068280c00e168a43e150803d1d0a83a140682801a910803d1d0a8380e00403c14070200c00304016080281002303c14080300c00304016080381802304418070301408303c180b0481c06001c200d06028120118220b050241005020e10070280e03000c110582812084381408834014104782d14080381906014014104782d140843814088300a00b0882c1409040140838401608038180230401608028100230401f0e0501c068100100f8602c15090380d020024400f054200f0601a0400485c1e0a03c100681001019078280f0501c09020024200e0501c0681000e110582812080281102403c180b0481c068100100f050200c03408007078280e0401a0400383c14070280902001c1e0a0380c020018271107c3814070180080983e180a8481c060020260f054200f060180080983c14078200c00384c1e0a03c1407020010160983c1407))) else (if j<6 then (if j<5 then (0xb0381004a0e069251046c2d1087434160702809a1005a180a030100470b0421e0b852220e854240c0300302e0f0501d08038080080b859231087a32170a4441d0a8481c0600783c14074200c02001c61100682c128541a0a024850251006c2c0c8541a0a025078210d05c250a834100490e040170642a0d040120601e88434170942a0d05012860250e052251086c2e0c8541a0a0268401a0942a0d04011c200b032150682008e194822c1007034160881242a9087a2e14080381a06818016134843d170a0441c0a0481a0600606d210f45c2a0e050180903002c3690458220f06028110248801e0a8401e0c034080090b83c14078200d020020320f0501e0a038120400486c32954822c11078341608812c40154843d170a8401e0d0340c00c0d85c2a134843d170a8441e0b0481a0600786c329087a2e15078280e04818018904581c0c0502204707828100601a0400383c14070200d02001c1e0a038140481000e1347a290e0441c050040591e8a43c11060140101609a3d14878220e0280251e8a438110601400e36118411c0d0602c140980943607a381a0c05828130781c00b198c05e2c12879200f4742a0e050180a0079046a2d0f849200f4742a10078340e0070fc723514858229007a3a190a8441e0b0481c0111e8e46a1f09a44200f4742e150781c060078b04a230f43d160a44c1c0a0301400d1e0d4522288834188b452241107834160878d45c2b1107c3c1a88034168a44c220f0680a02d1487e1e0d45829130803c1a0700347235150a44e220bc40180b4522611058240501c8a44c1687831160a44c220f058240e0078b452241187e1e8b052260f0501c0a0070ec72290f84e1e8c05829130781c060070cc581e0e0521f0a03a180a0301400d1007834190843c170a4401d0d0300c00e10078361a0c85428100682e15094421d0c01403c1a0a040160803818024878361a0a840160843a1a0b040098200f06c341005a210e8682c0e0401346a221007c361a0c85e210b0421d0d058240501d0d4521f0d85a1f0a0401d0d058240e0078d05c220f878381a0c854289288236168843a1a0b03814055168a43e1d0e0561f0a03a1a0a0381400e1a87c361a0a84e210f85c2910074340e030040200b430140602008e200c85c2c108782e148883a15090300c00f0b046200f870280e8401800a1006c32170a840180b85425108542004e0b03c190b054240e8401800a0c85c2a10058220f0642a10025858260f050200f064200c00505c2610058200a040090160983c14070200c00408036170802d10054240e04012c2c13078280e054200e0400282c0f0501d0803808008150a4441f0c85c2a148842d10054240e050140521f0c0582b0f8541c0a8401c0a0068e46a290f86c2e160a84d231087a32170a4441d0a8481c0600b03c14074) else (0x4240c03003c7235188a44e200f86c32170b054269187a32148883a15090300c0180f06428108782e15074280d0401801a290f854281387c2a0e8501a080300342c0f0501d08038080080b04c1e0a03a10060020269187a32148883a1509038016130843c170a4441d0a84818060060c04a1e0a442168802a1006028098290f856261007a3a170a83a14068280c00f16094461e87a2c1489838140602801a2d14890461f87a2c1489838140602801c3316078381487c280e860280c0500345a290f874381587c280e860280c05003854291107c32150a442168802a100602809e290f8561f0a83815080301400b0b2401e8e064281107028120700302c1187a2c14890441c0a0481c00c0b846200c858210e8602812025858230f064280e860281207002c2c1508c3c190a0441c080341400c1c8d452260c058229007a3a15070240e0078e452260c05a1e0c4582913070240e0070d444200f86c32178842c10874301409013c6a291307c36180b43e140803a180903801e290f8602c1587c2a0e050200d0500343c1a0c85c251006c2c1007032150901386a2d0f849200f4742810070340e0068d4522288834188b452241007034160870b4521f87835160a448200e0681c00d1a888401f0f06c34198842c1007032150901406a290f86e1f0a0401c0c854240e00687838150943c1b0a040190a0341400d168a43e1d0e0561f0a038190a0341400e1a8b8441f0f4401a0b04a210e86809a2d1487e1e0d05828128803a1a0700347235150a445100602c140944215090138722987830160a04a220e854240e00688e1e0d0602c13074280d05002c5a291208c3f0f0582813074280d05003856200f06c34120823d1d0d85c220f06809e27100642e110823d1d0c85c220b04809c35130602c114803d1d0c854220f058240e0080e4361509a44200f4742e150781c060070c8401e0d86a200d05a29130883c1a0270c440190bc40180b45226110582404d1c8602d0f0622c14898441e0b0481c00e1c86c2a1387a30160a44c1e0701801a31138642f10858210e8682c120260d44c1b0c05a1f0a0401d0d058240e0070c04a1e0c854289288236168843a1a0b038140511a854271087c2e148803a1a0701801a3215878361a0cc42160883c190a84809c30128782a148842d10054240e050134721b0a84d231087a32170a4441d0a8481c060088c856200f06c34190a852251086c2e110783215068280a831138803e170ac42170802c110682809c260f8582b0f8541c0b0401a0a0060a436138843e170a83a14068280c00d1a89836180b05427114843e188b854220f058240d030050642b1007834158823e168a8401e0c8380a0101889c40190b8582a1388c411f0c85a2a108782c110701402a301287832148823e168a43c14070280a00f0e040168843a1a)) else (if j<7 then (0x9c401f0b052200e8601c040078581e0a03a1007010010391a8a44c1f0d8602e160a84d231007a32160a4401d0a8401c0400c06c2a13488401e8e8541e07002c361509c3d180b052260f0380161509c3e148803a1a070024361509a461e8c852220e854240e0068a4361387c2a0e8501a0a00505c2c13078280e030080090ba46210f4642e148883a10068280c00e0b855230f4642911074200d050030361509a441e8e05c2a0f0300c00c1006c32170a840180b45226110582004e0d854261087a30148983c0c0300303c190a850200b4421d0d0581c0802685426108782e148803a1a060180181b0a84c210f05c29110742a120601801c1b098421e0b8541d0a0341006006058210f05c29110742a1206018018170b04d230f46429110742a12070034200f47232170a4441d0a8481c060068401e8e46429110742a1207002d230f05829128883a15090380c00c48c3c160a44a220e854240e00585d231087a32170a03a190a8481c0600706c2e9187a3214074321509038018160843c170a4441d0a8481806006058269187a32148883a15090300c00d0b83c14074200e0200202e13078280e840180081e87c361509a44200f4742a0f03801a3b1487c361509c3d180b052260f03801c200f06832108782e148803a1a0601801c1f0d854270f852200e8681c00b100642e160843c170a4441d0a84818060078a43e1b0b054269187a32148883a15090380201e0c850210f05c2a0e8501a08030034521f0a84e1f0a83a1406828016391bad86a2d1483d1c8c05829130781c060082e16c2d1483d1c8c05829130781c00d1a8d05a22490401e8e85c2910074340e0300405a1f0da48200f4742910074340e0068e46a2911244200f47232170a4441d0a8481c060090a5221007a39190a4441d0a8481c00d59abc5a290f855221007a3a15074280d0500406a2d1143d1a0b0522510074340e0300385a290f86e1e8d05829128803a1a07003872351488a1e8c05829128883a15090380c01014c3d180b05225110742a120700305a291228c450f0582913074280d0501801e2d14891461f0ac3c160a44c1d0a0341400f1a88840198843e170a4401d0c854240e03004052200f86e1f0a4401d0c854240e0068d05a220f07538198843e170a03a190a03414060090b4521f0f075381587c280e864280d05003c52220cc421f0b8541d0a8401a0a030038521f0c8561f0a83a15080341400c1c8d43e1b0a84d221007a3a1507818060078e46a2a1489c44200c85c200c05a29130882c100290e4521f0d854270f4602c148983c0c03003c401e0d064210f05c2910074340c030038401e0d868200b4421d0d0581c080268d05c220f878381b0d0642a14490411a0b4421d0d0581c0802b0d43e1b0d054270f852200e868180600708032170b0421e0b852220e85) else (if j<8 then (0xa83a1207018018260c05c2c1387c2a0f0481a060060c44e200c85c2c1347a290f0441c050072d8582507a39160a44c1e0b0381400d1c8e16c29134581e8e0622c148983c120700416c2d1483d1c8b052260f0581c0a0068e46eb68983d1c8c05829130781c060070d62c924803d1d0a0401d0d0481c00d1687d249007a3a1407434160702801a350f86e26920803d1d0a4401d0d0380c00f1c8a5220f47032170a84c1d0903801a3548a401e8e850220f064240e0060a5229007a3a150702a1207028018391ac4d221007a3a15074240e03003460af0f85626910803d1d0a83a14068280c0100fa401e8e8541e0b03812060058d44e221045e208d05a2410874341609013c52268b43d1a8b052241007434120700383e1b89c3d1a0b0522510074340e030038722987c39188b052260e8481c00c1a888411a8823016890441e0c8542404e14c3d188b05224110783212070030722989c3d180b052260e8481c060068a44a245187c2b138782c148983a14068280c0111cc3e1c8c45829130781a0600587e1e8b0522611078340d03002c72291345a1e0c4582913078240d030038521f87a2c148983c16070240c00c1ac421f0e852200e864240e0058d4451085c2510874321509012c530f85c2a128803a1909038016290f8662b0f852200e8602a120702801c351007c371387c291007432120701801c290f87538188b0561f0a03a180b0401a0a0080d43e1b4d0421f0e852200e8681a0600707c369a8782e15094401d0d0340c00d1a87c369a8b43e140803a1a090340c00e1487c2b0f8541e0c854200d050030521f0c856270f8541d0a8401a0a0300386297088421f0e8541d090340c00c13a5e1e0c05c2a13074240d030030409709c3e140883c19090340c00c0b84e1f0a8381206818012194b84e1f0a838150903812060060e46a314b844210f8742a0e8481a060070e452274bc3c180b854260e8481a060070d4401f0da5e1f0a0441e0c8481a0600705c2c1187832140883814090340c00d1487c32970ac3e150702a12070240c00e0f855281087c3a15074280d0481801a290f855290f05c2a13074280d0481801c290f8622c154a43e150702c10068240c00f0b85a1f0a83a12060180121b0b85426108782e15074240c0300342c0f0501d08038080080b04c1e0a03a10070100121608a401e8e0501e0803001413488401e8e0501c070100141607831160a4481e08030014130782910074300e020024260f0501d08038080081c8b4520f47432160a8481c0600306a2d0fa401e8e054200f0601800c1c8d452260c058229007a3a180a8401e0b040180121c8d43e1b0a84d221007a3a160a0380e0200407229130602c0f0622c14898401e0b04018010168a43e0f4582912078280e0400305a290f8541e0a03a1a0a0381000c1a87c36150) else (0xf85c2b1348c3d190a4441d08034140600785c269187a32148883a15090380c00d0d8582a134843d170a83c120681801a170b04d1e8a43c1107014015130803d1c8c852220e854240e03003626918782c14894441d0a8481c0600689837160aa421e0c052260f0481a0600707c361789a461e8c8501d0c854240e03003e2c154843d170a0401d0d0481a06006858269087a2e140883814090340c00d0d8622c9087a2e150702c10068240c00e098421e0b852220e854240c0300302e13078280e8401c040048fc4c180b045200f4742a0f0481c00d1e86c2a13488401e8e8541e0701801a3b0d854270f4602c148983c0e03003474260d8602d0f850200e868240e00686c2e160a84e1f0)))))
def genIndex9 (j : Nat) : Nat := if 4 ≤ j then 0 else (if j<2 then (if j<1 then (0xe003c007800d133e003c007800f001e0004223024f0000240176b9d1e3b0715c193390ce1b6cc089a7bcf76c0e6629868985a62d30830cc8968ff000a741ae3c908f001e00086ef06b20ebe003c003809f001e003c00780003bd28b7c0cf800516c554f5087800f001ac86857f800a362e5a3c0031bced92a6b3c00780013d927d14b33cdd436be000895d9c6a8d7e003952a8a44dc6995bc003817f0005d1fc007800f00002886048195f3d56b90eec7e97fb31e86bd8335a0f001a1fbc0012147134e1a1efa6ae68365c87640938c7f0016596812eafff00143dfc0078008425d333819f80051d0f323c00586e214d4c578e09943f001ed00d215323f000b5dbc0078002195e0008df7800f00007a7629a724944c0317c007800f001e003c007800a160815611819dcf001b0ebc007800f0006d47c00323eedb9a69fc00002ed4fa6cde033780052e229320047800d869e0012fb7800f001e003c001118704ddbea898f800f000a357865818b94270a8bc0078009653e003c0051b8f001e0022b2428cf001048e0e11283f001e003ce60b4eaa968a562e85136f001e003c007800f001e003ca9d20de2e9e6fd81de1ce464fe0012080ab6f000c4a141cf800e9a0f45192812f0b59e60ac059f800f001e003806f8006adbe00104fb4157551e000d738926e43de003c001ed7663a1a66f80f8008bd943f40a745c1b690c2f3c0033503588c514d0133192224445fc007800903f897044638ce3213e003c0044f833e5e003c00212af001e001777f800254de003c0044d892e509b6cd47800f0008307c001ac912bd68865379041cde7ec000a9203df001e0025a4a178855a0d34975733af001e041f4778000106a5dad45c086b63602b792ff80045232d17c007800f001e003c004962f00108e3c00780043e2633fc66f800f001e003c00089cf001e003900f8005afde00388a3840ab6a3cfc6367800fb9b261fc005240f000c1b09947800e5e6430fc007800f00141ee0edf800f041e00254b7800f001e00176b78000bff098317d7800f001e002901f80024512ce6504115db6172924211002dd2896bf19a3f80065a12987c001acaf001e003026f8002206917fc007800c686c687c0078000536291424d575a0c00c724021e4440c01940830421421c0491c0a00309750a0c228238b1c11c01c33c838304d0900042011843811c210920a0000c403d0414000400831904f66dc15c0803c02006891084170cf3801804810263cc1460010430020c060000104015604308024800000010a3840c00c214308008c1c400419910350040104100408a01100008040290100208d04200e0050c30410110050400821860c110300f38154d0040030ad3a60470002860010421003d01043c30861810410cb2800010c400800a002200000004083000281248001) else (0x727363b5e0018d1f800254743e9eea91981448a4dfc007800f0002555da9810ef001e25fc007ae2d5a6d53bc007800f0019abfc007800f001e00217761d4ecf1e003c00684ef00085ba48c8ed574cc03c3c007800456fe000c7f5f49f2f6a28cb41285764e2757db06f800f001d6a94db214b4aa9c64b6d4a20550b62587c005920a2f9e00387e780015b59863c002de880efe00006a780011d30d1bc0070a7f61d6ae3c0032d591d86c5cedb40d97b8cb71626899bd6607a47fc0018d0716be00180308673639e001c217800f001e003c003426bcf9e00290fdccdf001ed33c007800110fe00199a7800d0a7e0000f478009925c6888f6f800f001a92f0427800fbc53873c002234f001e000d5ed68770f368ffc004b3f4361aa1a2d39b3d63fa2a3f497c06595fc2af3c007800f0017587c0060f5f0bbe003c004030d2a3e003c1c0854b29efd21f391834f001e0034bbf800c0e1e003c0049c8335c182ac10e8e27c87c6aed797800f00184e3c00514a73f6a8c60dd7c0ad57de003c15309d9a436a1547a16caf000663686012f6bd7e20fbc006028f0013ca086f7800f001e003c0078003205fba7c007800f001238528e2322a026eb0bc00333e900fe00002c2190f001a2b9334f800338ed1bbcf1cdebe2fe4859708f800e5bde000882bd310577e003c006142550e23eccc9f800f000a72a330b9164267e000c41780052d5a953c007800f0005cf9031e1e721a7e003c00680cf001e00104b44561122aa0af0bf8005278e75ed6a12a1e1cac69960b78000de1e000ceaf800eaf9e003c003ce355d97808d033f1d39ea148095792e0f001ac060d54ab3012a806fc007800c9d1ec909376935f0018c1102421f0f00061b7c005dd7f001f50dad37800f001e003c00017a0b99e002988aad6f31fe003c001a76f0010cf112bcd1beabc64fbc007800f001e003ca438d2f001e003c00780033c8c5afc0078000cd1e0024287800f000d854808f80012f2ea4fc29108841151d3ef7978000387e000e9d74aea4f9e00107308c822b9799bc00780014eba07ac0ab9c07373e003c007800731d03ce144288df0006537c00134275fbe003c0021e5f0007597f44f800f000a863c0032d9f001e00282ff800c389e00342cf800a188c1cbc007800f0010857c007800f001e003c007427f001e0003157800e28de003c001a80fc77e003c002a79e4bbe185e8bfd6cb00be001a4e1341f20fe0004914818b098f82e08e05c02458c2074ff01eff001e003c005e05f000d15562a6aa7f000fa3047c7a656db5e003c007800f001e001a933985be86eafec0518dfa28f07858a0f800301fe0004fbc24af000bb9209978007df05348880f800f00176bf96369c9606d7b1fc007800e565b509c8d78b1027ae006f168e63394904bbc5dee2e15c6bd048630160e2b5)) else (if j<3 then (0x1e003c0029cff000ecb932e7800f001a81fc000098f0016550ed8f800f001e0025341014f9653528b493b08ec47e5919381a4fd630975bb3254ce00f1e00376c7800db7de8ab0acdb13fbda800a09df2236d9be003c002100f000f8528ac7800b2d9cab8e65e876b58e99ea48a81c59112439fc007800349093ebc007800f001e003f60f80078718503c003189113d9913c007800f001e001e4b1626f001e000845f80041ad2bdf93df800f001e001d34f800f00100fe2637800f001e000025f80035ca072fc007800792782a50d9f800f001823fc004051f001e0035027800f001e000520e924f63e46d1023eb0c25c38824595a6db134181c5e11ad47d4b72b140fe52a07ba628e8d9b7800d641acc3c007d8bae7be001332f30dd51cc91b1aa594cf000da6fc001ccfc9757d02d17f800a052ebacd2c60b4b47762f7c0041fff000c2acd6454db4338db97c000616a6a444c3c005ec0c23dc477c00231ed53c26238eff800f000e7eb52191d201b56a7c6d778001039699003e7dd4f33c4cbfc000ab5b563e00389d6259e3cdeab054d6cdef0019a8e04da21b9141774751b7800b52e06b7c007ca5c441e003c0072220467aae7d8d234b6e8dfbd94357800e417e0890cff800f0014a41d0050b9c171e003c00129cf0013a2fc003237d1dde003c0078004b45e000cf77800f0016767c01f800f00004ffc007dc9f001d6ce07972d2a349c8ae24b8ee64e429804508f80044a44d2accdb1ddbde3bc0f168f1966307abe46e5191bf00093c3c007800f0006aa48594981f001663250e6a9432adbbfbd74780004d5e002c789d6024f5e487c2521f37268a2f90cec8efa3d7e6116727800f001e001131b2cd7bcac202f158298f000ccef8abc3079575e000e6e289233f0ebd24a49333d525e003c007800f00098f09897800f001e003c0029a9b4efe3b652710c951ede00110c9adf84ab2c14ad478006c0d096903a2864099220df978c87f52224667c001b2d459c1c09774780064fdc5bc4b6e2395db3e003c0056ff6561e003c002335f00193ed165f800f001e003c00028a603be003c0035cff001e000d1ae8d8f000c6948b98addf001e003c00687adacfcbe229d98e4f001e00011295dc72e1e002cfac530f001e0028dbf800f000cb014e6f800f00020bc67cb229f001e00117492b43159e003d07d90ff000049e4f17800211de003c003925f0000a3600269d395dfe0008960331f00186098820284f001e0004cd2ad784a66c4203e8acc5614410e0afba3d2688e02fc00780045825a37c0078009075e002d61d12df001e003c003023f001c333c007800a1d5e001370b338f001e00259978dcd9ec36ff85ff800f001b26718b726c635e84a645402675895e5f90f02046bb422becf33a045f8dae42fc0020940ab6378c513aa56f000ca24d17) else (0x649a39dc4bd7c0036fbd0d3e0034dd80e0ea992944c898b09bdce55354a85232f001a35e886f80075b89ce514ee82743f299828bef04910c505d7037c27862c6c13e1408139bc5f017a10ba24d30e6a002955f800806a526fc007800abd5c9cbc49a54fd655865fc007800f001e001b76f8002cfbe001592b8ba7215a442019482c7b645a4401e7800c30cc828d5202620479e003c007a7fa0c07ae3c0020c2f001e002052f800b48e3afbc005aaaf001e003c007800e10be002a65525edda15b3bc007a742489e003c00560ff000365ccadf800f0010653c001106d1c7259e2ae22dbf001e000cc07800062993bd450d8aaf000283a96c3299a0ac0c3d53595de816fe003c00780021d7c05b0fb2031f001e002c2e64b0f001e003c007800f001e003c007800f00020381966ecbf00183e7b44556b60353456c7ff800683fa758ebef800f00)))
def genData10 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x23100d0c0b0a0901203c34302c28241c0c0091e1a12110d0c08070605042c78704840342c201c1804a1e1a120f0d0a08070603002c584440302c20141004917110f0c0a0807050403002cccc0b09478503c281c140c0800d201e1917100f0b0a070301003044403c38281c0c008110c0b0a090805042080786c6454504034302c282404d0f0c0b0a09070300205c4430201c18141081e191514100b08070601284c3c28201c180c0081e1b1513100b08050401284c3c281c100c007201e1b1a100b05030201284c3c281c140c08008160f0a070301001c44403c38281c0c008392a29110c0b0a090805042ce4b8a8944034302c282404b2d290f0c0b0a0907030028d48880443430201c181410b3534322e2b22201f1e1b1a12100d0b080706014cb47c6c3c28201c180c00a3935312a272220191711100c0b0805040144a4986058443c3028201c14100c00e34302e2a25221f1e191514100b0503020144b4a47c543c281c140c0800b1f1b1513100f0b0a0703010030444038281c0c007110b0a090805041c40343028240460f0c0b090703001c44301c1814106100b08070601183c2820180c006100b08050401183c281c100c006100b05030201183c281c14080060f0a0703010018403c2c281c0c040080f0a07030017a138db76360b49335b1e302ae92d7ac62aaa99287a72260a4b23ba26214a051f39dc1c49af19797015a9371198f60de8c50b58a609888907b86e06085304583802a81d00b8003ff51ffd43ff43ffd07ff40ffcc7ff30ffc83ff10ff983fe53ff947fe50ff90ffe41ff903fe31ff8c3fe21ff883fe10ff583fd53ff547fd50ff50ffd41ff503fd31ff4c3fd21ff483fd10ff183fc53ff147fc50ff10ffc41ff103fc31ff0c3fc21ff083fc10fdc43f510)
def genIndex10 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (0x7801c1726b3e0058754dbf8012d9cf0de000ade01396d019b56d3e004093003731fa82f45f073f800e643056e2ae8f66077b33e00213de00584400bdb03e00725f98cb98d48538d295c1ae4a07d92683302f621962a8e95f801e007801e00217a3b568dd4c67acbe00780187ca908ed598fb22bb274e50acd566b72094b8b812e28aa5ce0ce8a5ebcf88ee59e2ac46f5011c27beeba8f2ac4a105a9187a7a63aa08621c61a97deda780067d6aa2e456364254d1b7e0009bbe00412bfc9416ac564317803a04de007800d8b590de007801a9cf801a937800858710722758b1e007801e0010a1883928fe007727e007800590d82917fe83899d3261e002b398cadb556b27801e0078002027801e00206de007801e007801863f312270f801e001668484f8013c6780004e82c1a9f78000b7022ee0eb228abd5046f8e61caa1fb025e001e7de00688049fd8edc399f3002e7801e0062efe007801c9bae37dc17801c7059a3c4df8002dc321062df8004679911a60f801e0049cda6988b5e000a45e007801e001975e00334dbc3b6a1e0071b3e000055e00780055c89d02d42a6d66b845548d2278a628a6bca90b37e00412f89c44c889e92e9d27660ee0d31a1bc19a941200e594c478002ca7ae027ac1c8cd6ea0280c78006d020d48b3e61f289465d87c4e798d1c242c38d8f1c596220647f800c2a1113e0078012af5a77602f800a1ac269e00715658c780104958ebe007801e31c307e005293e00707362681ffe0048b3e007801e007801e00780124c78016c8130de005b5fe0078002317801e000077e007801e835db3e003e57e00395de003a5186e7afbe007800e08780043e3146cd63d75e003173a267629aaa9e6ea4e5739e00780045a7331e00711be000335e000970656cb2cbc8f801e004920c717849e0069187dcc9e10d10807e0008694775216a0df801e007801373581b04718ef210f800a77f0bec76e255e0075fadbe724be007b3e72b59a8e94f800021fb1a3ab7985c1f736074e6324a16cf46e4b2d6fe003a1be0046640cf7801e007801699f35de0032a1e001e71e007801e0036b5e007800219f800e25f801e001635e0000f3aacf8012c57801e007801835f800ec3c2d1e007801e007801e007801e002e45ed3f801e007801aac12f9e241a8004078010abf801e006a9ee927800cb1f801e001265e007801a37e994a89f800c7b31b5e007801e007801fd0796347ef801e00383cb9af801e007801e0012b8781f801e00241800182183009804541120020004021c70f04301881a0401412047b4346008008018811e0400b021451300040021a1420d104008812180800c080001e19980100008082140050288100160c5011604184101858400002010078008001c1033014280021448a000010e1a3c080107040310140801e04281) else (0xa217801e007801e007801e007801e007801e007801e0008fe288a9d9e007801e00780182b7801e0062bbe007800c749905e00194de004e05e00499d432f800e4cf800a4fdab7e006a4668e7801e00780188cf80166ff801dcdf801e004999052233a243d193e00318965df800c8b52ede007800abc29790a17ad9e5bf17f2bf59fdcdb4d6da3a7801e000e729c801e7e006f3be00036be007801e002b23e0012b4817f801597f801e002b49e0001d7e00313507e332fbd1780144a7800796e0bdc939861e004a5a67be9d5e007abfe007801e007801e00753b98711232baf8006d4b0141dab2d7c017145a53f800c8788c9e00595fe006a302b9f801240e343e0039b0aa1f80141c49ab45290c1e0078012367801e8630e105b307be00067a67d8259e007801e0018957d0f801e007801a09f801e007801820a059b269e9f7803117e001f3fe00606eab4f801e007801e002e2b98b9ed7e00010b218b483250203fa369050265b9a40c2f8015998151e0001e2cdcf801e003823c12fddfe007363e00701702ee205e00229dec9f80023d7a40755b155e00351f68ade16c00cb4b1adf800222fa89e0052cd233b677b7f51c6a8df8795825e4c1bb431d1ca357bab68a99ec259e5bcb4aa6bcbe301e005ac2a30c02b6b57801e0008d1e001a8de007800266fa00f2cf801e00582c8c16206214da9b8067800e004297460323fe00780088ef80142250fcd809d7de003afee233a8a0397801e0020a7dd28a1de))
def genData11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def genIndex11 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x8afd8281780ab9e29e4c85b58e25c87a8f90187c060f33e37935f80141b8bc0780f01e00ad780f00c93c078028fe0090f80f01a47c02455388b7c06a2046d9e80c0cf01f4fc05263d250c41c18f01e0342007b17e0065780e0de03c0780c2f26bc01eac10d3fc044224fe03b2780f00377c07800332974ad54e29079e0812d80f6e28ae69d9e02e7265f01877c0780f00e6fc0780f01e03c0668f0152fc07c6fc7e0200329427e006ff80f01e03a978075c1b46ac2a91be024b4abeacdbbc040ef01e00031082150c0901c203044504700)
def generatedLevels : Nat → Packing
  | 5 => (53,6,7,0,0,9,0,genData5)
  | 6 => (606,5,7,0,0,13,0,genData6)
  | 7 => (1133,4,7,0,0,16,0,genData7)
  | 8 => (853,3,7,0,0,17,0,genData8)
  | 9 => (442,2,7,0,0,16,0,genData9)
  | 10 => (47,1,7,0,0,12,0,genData10)
  | 11 => (1,0,7,0,0,0,0,genData11)
  | _ => emptyPacking
def generatedIndex : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 18 107 5 11 6 1 genIndex6
  | 7 => lookupWord 200 1213 6 15 10 1 genIndex7
  | 8 => lookupWord 366 2195 6 16 11 1 genIndex8
  | 9 => lookupWord 283 1699 6 15 10 1 genIndex9
  | 10 => lookupWord 137 827 7 14 9 1 genIndex10
  | 11 => lookupWord 22 142 5 11 6 1 genIndex11
  | _ => fun _ => none
def qF_ : Forest := ⟨509,11,fun i => generatedSamples[i]?.getD (0,0),generatedColumns,[[], [112,50,100]],generatedLevels,generatedIndex⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP5_0 : block qF_ 5 0 53 = true := by
  apply cellsBlock (ar := 6) (rows := 0) (d := 3)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB5 : block qF_ 5 0 53 = true := genP5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP6_0 : block qF_ 6 0 8 = true := by
  apply cellsBlock (ar := 6) (rows := 0) (d := 1)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP6_8 : block qF_ 6 8 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP6_104 : block qF_ 6 104 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP6_200 : block qF_ 6 200 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP6_296 : block qF_ 6 296 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP6_392 : block qF_ 6 392 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP6_488 : block qF_ 6 488 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP6_584 : block qF_ 6 584 22 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 2)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB6 : block qF_ 6 0 606 = true := (@block_merge qF_ 6 0 296 310 (@block_merge qF_ 6 0 104 192 (@block_merge qF_ 6 0 8 96 genP6_0 genP6_8) (@block_merge qF_ 6 104 96 96 genP6_104 genP6_200)) (@block_merge qF_ 6 296 192 118 (@block_merge qF_ 6 296 96 96 genP6_296 genP6_392) (@block_merge qF_ 6 488 96 22 genP6_488 genP6_584)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_0 : block qF_ 7 0 9 = true := by
  apply cellsBlock (ar := 6) (rows := 0) (d := 1)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_9 : block qF_ 7 9 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_105 : block qF_ 7 105 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_201 : block qF_ 7 201 5 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 0)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_206 : block qF_ 7 206 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_302 : block qF_ 7 302 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_398 : block qF_ 7 398 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_494 : block qF_ 7 494 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_590 : block qF_ 7 590 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_686 : block qF_ 7 686 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_782 : block qF_ 7 782 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_878 : block qF_ 7 878 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_974 : block qF_ 7 974 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_1070 : block qF_ 7 1070 63 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 3)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB7 : block qF_ 7 0 1133 = true := (@block_merge qF_ 7 0 494 639 (@block_merge qF_ 7 0 201 293 (@block_merge qF_ 7 0 9 192 genP7_0 (@block_merge qF_ 7 9 96 96 genP7_9 genP7_105)) (@block_merge qF_ 7 201 101 192 (@block_merge qF_ 7 201 5 96 genP7_201 genP7_206) (@block_merge qF_ 7 302 96 96 genP7_302 genP7_398))) (@block_merge qF_ 7 494 288 351 (@block_merge qF_ 7 494 96 192 genP7_494 (@block_merge qF_ 7 590 96 96 genP7_590 genP7_686)) (@block_merge qF_ 7 782 192 159 (@block_merge qF_ 7 782 96 96 genP7_782 genP7_878) (@block_merge qF_ 7 974 96 63 genP7_974 genP7_1070))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_0 : block qF_ 8 0 1 = true := by
  apply cellsBlock (ar := 6) (rows := 0) (d := 0)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_1 : block qF_ 8 1 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_97 : block qF_ 8 97 14 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 1)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_111 : block qF_ 8 111 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_207 : block qF_ 8 207 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_303 : block qF_ 8 303 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_399 : block qF_ 8 399 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_495 : block qF_ 8 495 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_591 : block qF_ 8 591 13 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 1)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_604 : block qF_ 8 604 96 = true := by
  apply cellsBlock (ar := 9) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_700 : block qF_ 8 700 96 = true := by
  apply cellsBlock (ar := 9) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_796 : block qF_ 8 796 57 = true := by
  apply cellsBlock (ar := 9) (rows := 0) (d := 3)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB8 : block qF_ 8 0 853 = true := (@block_merge qF_ 8 0 399 454 (@block_merge qF_ 8 0 111 288 (@block_merge qF_ 8 0 1 110 genP8_0 (@block_merge qF_ 8 1 96 14 genP8_1 genP8_97)) (@block_merge qF_ 8 111 96 192 genP8_111 (@block_merge qF_ 8 207 96 96 genP8_207 genP8_303))) (@block_merge qF_ 8 399 205 249 (@block_merge qF_ 8 399 96 109 genP8_399 (@block_merge qF_ 8 495 96 13 genP8_495 genP8_591)) (@block_merge qF_ 8 604 96 153 genP8_604 (@block_merge qF_ 8 700 96 57 genP8_700 genP8_796))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_0 : block qF_ 9 0 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_96 : block qF_ 9 96 16 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 2)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_112 : block qF_ 9 112 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_208 : block qF_ 9 208 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_304 : block qF_ 9 304 65 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_369 : block qF_ 9 369 73 = true := by
  apply cellsBlock (ar := 9) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB9 : block qF_ 9 0 442 = true := (@block_merge qF_ 9 0 208 234 (@block_merge qF_ 9 0 96 112 genP9_0 (@block_merge qF_ 9 96 16 96 genP9_96 genP9_112)) (@block_merge qF_ 9 208 96 138 genP9_208 (@block_merge qF_ 9 304 65 73 genP9_304 genP9_369)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP10_0 : block qF_ 10 0 2 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 0)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP10_2 : block qF_ 10 2 45 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 3)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB10 : block qF_ 10 0 47 = true := (@block_merge qF_ 10 0 2 45 genP10_0 genP10_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP11_0 : block qF_ 11 0 1 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 0)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB11 : block qF_ 11 0 1 = true := genP11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genTables : checkedTables qF_ 11 := by
  intro k hk
  interval_cases k
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact genB5
  · exact genB6
  · exact genB7
  · exact genB8
  · exact genB9
  · exact genB10
  · exact genB11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genGeometry : graphValid qF_ (boundsBefore generatedKnown) = true := by
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowGenerated : Lower true (varsX 509) (qG_ 509) 12 :=
  lower_forest (g := qF_) (i := 0) (hints := 1027)
    (before_sound generatedKnown generatedPrior) genGeometry genTables
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
end PEqualNP.Outside.L_meta_51466.ForestCore
namespace PEqualNP.Outside.L_meta_51466
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds ForestCore
def graph (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0,3,0,4,1,4,2,4,0,5,1,5,2,5,3,5,0,6,1,6,3,6,4,6,0,7,1,7,2,7,4,7,5,7,6,7] : List ℕ).length / 2,(List.ofFn x).getD (([0,3,0,4,1,4,2,4,0,5,1,5,2,5,3,5,0,6,1,6,3,6,4,6,0,7,1,7,2,7,4,7,5,7,6,7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0,3,0,4,1,4,2,4,0,5,1,5,2,5,3,5,0,6,1,6,3,6,4,6,0,7,1,7,2,7,4,7,5,7,6,7] : List ℕ).getD (2 * i + 1) 0) false = true)
def coding : Fin 8 → Nat := ![0,1,2,3,4,5,6,7]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def roots : List Sig := List.ofFn (fun i : Fin 8 => inputs.getD (coding i) zero)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def codedGraph : Sig := 0xfffffffffffffffffffffffffffffefefffffffeffffffeefffefffefefeaa00fffffffffffffffffffffffffffffefefffffffeffffffeefffefffefefeaa00
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wholeBound : Lower true roots codedGraph 13 := by
  have h := lift_ok (u := true) (ms := fixRows 2 0) (raw := roots) (T := codedGraph)
    (xs := [(inputs.getD 1 zero,16,18)]) (by decide +kernel) (qP_ _ (by decide +kernel))
    (qP_ _ (by decide +kernel)) lowGenerated
  have count : (([(inputs.getD 1 zero,16,18)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [count] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def sampleInput (r : Row) (i : Fin 8) : Bool := bit r (inputs.getD (coding i) zero)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sampledInput (r : Row) : List.ofFn (sampleInput r) = roots.map (bit r) := by
  rw [roots, List.map_ofFn]
  rfl
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sampleCorrect : ∀ r : Row, bit r codedGraph = graph (sampleInput r) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def signedNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem binaryLower (C : Circuit) (fit : FanInTwo C)
    (comp : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = graph x) :
    13 ≤ C.gates.countP (fun g => !signedNot g) := by
  have goalEq : (execute C.gates roots).getD C.output zero = codedGraph := by
    apply bit_ext
    intro r
    rw [← b_read, execute_bits _ _ _ (fun g hg => (fit g hg).1), ← sampledInput]
    exact (comp (sampleInput r)).trans (sampleCorrect r).symm
  have out := get_rep (u := true) (execute C.gates roots) C.output
  rw [goalEq] at out
  unfold ForestCore.Repr at out
  have pg : bit 0 codedGraph = false := by decide +kernel
  rw [nrm_id pg] at out
  have properGoal : proper codedGraph := by unfold proper; decide +kernel
  obtain ⟨k, S, hk, run, sub⟩ := extract (u := true) C.gates roots fit (by simp) properGoal
    (out.resolve_right (fun h => h properGoal))
  change k ≤ C.gates.countP (fun g => !signedNot g) at hk
  rw [nrm_map (by decide +kernel : roots.all plainWord = true)] at sub
  have step := list_run run S.toList (Finset.nodup_toList _) (by simp)
  have ready : supply true (roots.map observe) (S.toList.map observe) := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
    exact Or.inl (List.mem_map_of_mem (sub a (Finset.mem_toList.mp ha)))
  obtain ⟨q, bank, reach, hit, paid⟩ := contraction (observe_proper properGoal) step _ Reach.start ready
  have lower := wholeBound q bank reach hit
  omega
def upperGates : List Gate := [⟨.or, [7,3]⟩, ⟨.or, [7,6]⟩, ⟨.or, [1,0]⟩, ⟨.or, [10,2]⟩, ⟨.or, [10,4]⟩, ⟨.or, [6,5]⟩, ⟨.or, [13,0]⟩, ⟨.or, [7,5]⟩, ⟨.or, [15,4]⟩, ⟨.and, [14,8]⟩, ⟨.and, [11,16]⟩, ⟨.and, [12,9]⟩, ⟨.or, [17,18]⟩, ⟨.or, [20,19]⟩]
theorem upper_shape : ∀ g ∈ upperGates,(g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [upperGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem upper_sem : ∀ x : Fin 8 → Bool,
    Circuit.eval ⟨upperGates,21⟩ (List.ofFn x) = graph x := by
  decide +kernel
end PEqualNP.Outside.L_meta_51466
open PEqualNP.Outside.L_meta_51466 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_51466 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gs o legal _ computes
  by_cases neg : ∃ g ∈ gs, g.op = .not
  · obtain ⟨g, hg, eq⟩ := neg
    have fan : FanInTwo ⟨gs, o⟩ := fun t ht => ⟨(legal t ht).1,(legal t ht).2⟩
    have low := binaryLower ⟨gs, o⟩ fan computes
    change 13 ≤ gs.countP (fun g => !signedNot g) at low
    have lt : gs.countP (fun g => !signedNot g) < gs.length := by
      rw [List.countP_eq_length_filter]
      apply List.length_filter_lt_length_iff_exists.mpr
      exact ⟨g, hg, by simp [eq, signedNot]⟩
    refine ⟨upperGates,21, upper_shape, ?_, upper_sem⟩
    change 14 ≤ gs.length
    omega
  · refine ⟨gs, o, ?_, le_rfl, computes⟩
    intro g hg
    obtain ⟨op, cap⟩ := legal g hg
    exact ⟨op.imp_right (fun h => h.resolve_right (fun eq => neg ⟨g, hg, eq⟩)), cap⟩
