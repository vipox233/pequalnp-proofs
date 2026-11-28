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
namespace PEqualNP.Outside.L_meta_51432
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
  if m.testBit 8 then (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 0 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 3) ||| (x 1 &&& x 4) ||| (x 1 &&& x 7) ||| (x 3 &&& x 5) ||| (x 3 &&& x 7) ||| (x 4 &&& x 6) ||| (x 4 &&& x 7) ||| (x 5 &&& x 6) ||| (x 5 &&& x 7)
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
  if m.testBit 8 then (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 0 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 3) ||| (x 1 &&& x 4) ||| (x 1 &&& x 7) ||| (x 3 &&& x 5) ||| (x 3 &&& x 7) ||| (x 4 &&& x 6) ||| (x 4 &&& x 7) ||| (x 5 &&& x 6) ||| (x 5 &&& x 7)
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
end PEqualNP.Outside.L_meta_51432
namespace PEqualNP.Outside.L_meta_51432.ForestCore
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
theorem prior506 : Lower true (varsX 506) (qG_ 506) 8 := by
  have h := lift_ok (u := true) (ms := ([16,66,84,101]).map swapRows ++ fixRows 128 0)
    (raw := varsX 506) (T := qG_ 506) (xs := [(inputs.getD 7 zero,2,130)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low109
  have card : (([(inputs.getD 7 zero,2,130)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior505 : Lower true (varsX 505) (qG_ 505) 8 := by
  have h := lift_ok (u := true) (ms := ([112,66,117,118]).map swapRows ++ fixRows 128 0)
    (raw := varsX 505) (T := qG_ 505) (xs := [(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low173
  have card : (([(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior499 : Lower true (varsX 499) (qG_ 499) 8 := by
  have h := lift_ok (u := true) (ms := ([33,67,84]).map swapRows ++ fixRows 64 0)
    (raw := varsX 499) (T := qG_ 499) (xs := [(inputs.getD 6 zero,1,65)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low173
  have card : (([(inputs.getD 6 zero,1,65)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior491 : Lower true (varsX 491) (qG_ 491) 8 := by
  have h := lift_ok (u := true) (ms := ([16,115,116,101,118]).map swapRows ++ fixRows 128 0)
    (raw := varsX 491) (T := qG_ 491) (xs := [(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low211
  have card : (([(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior490 : Lower true (varsX 490) (qG_ 490) 7 := by
  have h := lift_ok (u := true) (ms := ([32,65,50,67,84,117,118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 490) (T := qG_ 490) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low211
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior483 : Lower true (varsX 483) (qG_ 483) 7 := by
  have h := lift_ok (u := true) (ms := ([16,84,101]).map swapRows ++ fixRows 0 0)
    (raw := varsX 483) (T := qG_ 483) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low211
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior475 : Lower true (varsX 475) (qG_ 475) 8 := by
  have h := lift_ok (u := true) (ms := ([33,67,116,101,118]).map swapRows ++ fixRows 8 0)
    (raw := varsX 475) (T := qG_ 475) (xs := [(inputs.getD 3 zero,1,9)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low173
  have card : (([(inputs.getD 3 zero,1,9)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior474 : Lower true (varsX 474) (qG_ 474) 7 := by
  have h := lift_ok (u := true) (ms := ([32,50,67,116,118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 474) (T := qG_ 474) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low211
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior473 : Lower true (varsX 473) (qG_ 473) 7 := by
  have h := lift_ok (u := true) (ms := ([112,66,67,116,101,118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 473) (T := qG_ 473) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low173
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior467 : Lower true (varsX 467) (qG_ 467) 7 := by
  have h := lift_ok (u := true) (ms := ([33,67,116,101,118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 467) (T := qG_ 467) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low173
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior459 : Lower true (varsX 459) (qG_ 459) 7 := by
  have h := lift_ok (u := true) (ms := ([112,65,67,118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 459) (T := qG_ 459) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low211
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior443 : Lower true (varsX 443) (qG_ 443) 8 := by
  have h := lift_ok (u := true) (ms := ([33,67,84]).map swapRows ++ fixRows 8 0)
    (raw := varsX 443) (T := qG_ 443) (xs := [(inputs.getD 3 zero,1,9)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low173
  have card : (([(inputs.getD 3 zero,1,9)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior442 : Lower true (varsX 442) (qG_ 442) 7 := by
  have h := lift_ok (u := true) (ms := ([16,66,83,84]).map swapRows ++ fixRows 0 0)
    (raw := varsX 442) (T := qG_ 442) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low173
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior435 : Lower true (varsX 435) (qG_ 435) 7 := by
  have h := lift_ok (u := true) (ms := ([33,67,84]).map swapRows ++ fixRows 0 0)
    (raw := varsX 435) (T := qG_ 435) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low173
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior379 : Lower true (varsX 379) (qG_ 379) 8 := by
  have h := lift_ok (u := true) (ms := ([16,66,84,101]).map swapRows ++ fixRows 1 0)
    (raw := varsX 379) (T := qG_ 379) (xs := [(inputs.getD 0 zero,8,9)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low109
  have card : (([(inputs.getD 0 zero,8,9)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior378 : Lower true (varsX 378) (qG_ 378) 7 := by
  have h := lift_ok (u := true) (ms := ([16,66,84,101]).map swapRows ++ fixRows 0 0)
    (raw := varsX 378) (T := qG_ 378) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low109
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior377 : Lower true (varsX 377) (qG_ 377) 7 := by
  have h := lift_ok (u := true) (ms := ([112,66,117,118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 377) (T := qG_ 377) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low173
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior371 : Lower true (varsX 371) (qG_ 371) 7 := by
  have h := lift_ok (u := true) (ms := ([16,116,117]).map swapRows ++ fixRows 0 0)
    (raw := varsX 371) (T := qG_ 371) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low211
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior363 : Lower true (varsX 363) (qG_ 363) 7 := by
  have h := lift_ok (u := true) (ms := ([16,115,116,101,118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 363) (T := qG_ 363) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low211
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior504 : Lower true (varsX 504) (qG_ 504) 6 := by
  have h := lift_ok (u := true) (ms := ([33,50,84,118]).map swapRows ++ fixRows 80 0)
    (raw := varsX 504) (T := qG_ 504) (xs := [(inputs.getD 4 zero,64,80),(inputs.getD 6 zero,16,80)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 4 zero,64,80),(inputs.getD 6 zero,16,80)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior498 : Lower true (varsX 498) (qG_ 498) 6 := by
  have h := lift_ok (u := true) (ms := ([118]).map swapRows ++ fixRows 96 0)
    (raw := varsX 498) (T := qG_ 498) (xs := [(inputs.getD 5 zero,64,96),(inputs.getD 6 zero,16,80)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 5 zero,64,96),(inputs.getD 6 zero,16,80)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
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
theorem prior488 : Lower true (varsX 488) (qG_ 488) 5 := by
  have h := lift_ok (u := true) (ms := ([33,50,84,118]).map swapRows ++ fixRows 64 0)
    (raw := varsX 488) (T := qG_ 488) (xs := [(inputs.getD 6 zero,32,96)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 6 zero,32,96)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior481 : Lower true (varsX 481) (qG_ 481) 5 := by
  have h := lift_ok (u := true) (ms := ([16,84]).map swapRows ++ fixRows 128 0)
    (raw := varsX 481) (T := qG_ 481) (xs := [(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior466 : Lower true (varsX 466) (qG_ 466) 5 := by
  have h := lift_ok (u := true) (ms := ([118]).map swapRows ++ fixRows 64 0)
    (raw := varsX 466) (T := qG_ 466) (xs := [(inputs.getD 6 zero,16,80)])
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
theorem prior457 : Lower true (varsX 457) (qG_ 457) 5 := by
  have h := lift_ok (u := true) (ms := ([16,67,118]).map swapRows ++ fixRows 64 0)
    (raw := varsX 457) (T := qG_ 457) (xs := [(inputs.getD 6 zero,1,65)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 6 zero,1,65)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior441 : Lower true (varsX 441) (qG_ 441) 6 := by
  have h := lift_ok (u := true) (ms := ([16,67,101]).map swapRows ++ fixRows 144 0)
    (raw := varsX 441) (T := qG_ 441) (xs := [(inputs.getD 4 zero,1,17),(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 4 zero,1,17),(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior440 : Lower true (varsX 440) (qG_ 440) 5 := by
  have h := lift_ok (u := true) (ms := ([33,50,84,118]).map swapRows ++ fixRows 16 0)
    (raw := varsX 440) (T := qG_ 440) (xs := [(inputs.getD 4 zero,128,144)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 4 zero,128,144)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior434 : Lower true (varsX 434) (qG_ 434) 5 := by
  have h := lift_ok (u := true) (ms := ([118]).map swapRows ++ fixRows 32 0)
    (raw := varsX 434) (T := qG_ 434) (xs := [(inputs.getD 5 zero,128,160)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 5 zero,128,160)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
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
theorem prior427 : Lower true (varsX 427) (qG_ 427) 6 := by
  have h := lift_ok (u := true) (ms := ([16,67,101]).map swapRows ++ fixRows 130 0)
    (raw := varsX 427) (T := qG_ 427) (xs := [(inputs.getD 1 zero,8,10),(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,8,10),(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior426 : Lower true (varsX 426) (qG_ 426) 5 := by
  have h := lift_ok (u := true) (ms := ([67,118]).map swapRows ++ fixRows 32 0)
    (raw := varsX 426) (T := qG_ 426) (xs := [(inputs.getD 5 zero,8,40)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 5 zero,8,40)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
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
theorem prior424 : Lower true (varsX 424) (qG_ 424) 4 := by
  have h := lift_ok (u := true) (ms := ([33,50,84,118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 424) (T := qG_ 424) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior419 : Lower true (varsX 419) (qG_ 419) 5 := by
  have h := lift_ok (u := true) (ms := ([16,84,118]).map swapRows ++ fixRows 2 0)
    (raw := varsX 419) (T := qG_ 419) (xs := [(inputs.getD 1 zero,128,130)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,128,130)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
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
theorem prior411 : Lower true (varsX 411) (qG_ 411) 6 := by
  have h := lift_ok (u := true) (ms := ([16,67,118]).map swapRows ++ fixRows 18 0)
    (raw := varsX 411) (T := qG_ 411) (xs := [(inputs.getD 1 zero,8,10),(inputs.getD 4 zero,1,17)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,8,10),(inputs.getD 4 zero,1,17)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior410 : Lower true (varsX 410) (qG_ 410) 5 := by
  have h := lift_ok (u := true) (ms := ([67,118]).map swapRows ++ fixRows 16 0)
    (raw := varsX 410) (T := qG_ 410) (xs := [(inputs.getD 4 zero,2,18)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 4 zero,2,18)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior409 : Lower true (varsX 409) (qG_ 409) 5 := by
  have h := lift_ok (u := true) (ms := ([16,67,118]).map swapRows ++ fixRows 16 0)
    (raw := varsX 409) (T := qG_ 409) (xs := [(inputs.getD 4 zero,1,17)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 4 zero,1,17)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior403 : Lower true (varsX 403) (qG_ 403) 5 := by
  have h := lift_ok (u := true) (ms := ([16,118]).map swapRows ++ fixRows 2 0)
    (raw := varsX 403) (T := qG_ 403) (xs := [(inputs.getD 1 zero,16,18)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,16,18)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior402 : Lower true (varsX 402) (qG_ 402) 4 := by
  have h := lift_ok (u := true) (ms := ([118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 402) (T := qG_ 402) (xs := [])
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
theorem prior395 : Lower true (varsX 395) (qG_ 395) 5 := by
  have h := lift_ok (u := true) (ms := ([16,67,118]).map swapRows ++ fixRows 2 0)
    (raw := varsX 395) (T := qG_ 395) (xs := [(inputs.getD 1 zero,8,10)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,8,10)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior394 : Lower true (varsX 394) (qG_ 394) 4 := by
  have h := lift_ok (u := true) (ms := ([67,118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 394) (T := qG_ 394) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior393 : Lower true (varsX 393) (qG_ 393) 4 := by
  have h := lift_ok (u := true) (ms := ([16,67,118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 393) (T := qG_ 393) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
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
theorem prior353 : Lower true (varsX 353) (qG_ 353) 4 := by
  have h := lift_ok (u := true) (ms := ([16,84]).map swapRows ++ fixRows 0 0)
    (raw := varsX 353) (T := qG_ 353) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior347 : Lower true (varsX 347) (qG_ 347) 6 := by
  have h := lift_ok (u := true) (ms := ([16]).map swapRows ++ fixRows 10 0)
    (raw := varsX 347) (T := qG_ 347) (xs := [(inputs.getD 1 zero,8,10),(inputs.getD 3 zero,1,9)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,8,10),(inputs.getD 3 zero,1,9)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior345 : Lower true (varsX 345) (qG_ 345) 5 := by
  have h := lift_ok (u := true) (ms := ([16]).map swapRows ++ fixRows 8 0)
    (raw := varsX 345) (T := qG_ 345) (xs := [(inputs.getD 3 zero,1,9)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 3 zero,1,9)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior339 : Lower true (varsX 339) (qG_ 339) 5 := by
  have h := lift_ok (u := true) (ms := ([16]).map swapRows ++ fixRows 2 0)
    (raw := varsX 339) (T := qG_ 339) (xs := [(inputs.getD 1 zero,16,18)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,16,18)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
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
theorem prior315 : Lower true (varsX 315) (qG_ 315) 6 := by
  have h := lift_ok (u := true) (ms := ([16,67,101]).map swapRows ++ fixRows 18 0)
    (raw := varsX 315) (T := qG_ 315) (xs := [(inputs.getD 1 zero,8,10),(inputs.getD 4 zero,1,17)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,8,10),(inputs.getD 4 zero,1,17)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
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
theorem prior299 : Lower true (varsX 299) (qG_ 299) 5 := by
  have h := lift_ok (u := true) (ms := ([16,67,101]).map swapRows ++ fixRows 2 0)
    (raw := varsX 299) (T := qG_ 299) (xs := [(inputs.getD 1 zero,8,10)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,8,10)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
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
theorem prior482 : Lower true (varsX 482) (qG_ 482) 4 := by
  have h := lift_ok (u := true) (ms := ([16,33,66,99,116,117]).map swapRows ++ fixRows 0 0)
    (raw := varsX 482) (T := qG_ 482) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low45
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior472 : Lower true (varsX 472) (qG_ 472) 4 := by
  have h := lift_ok (u := true) (ms := ([16,65,98,99,117]).map swapRows ++ fixRows 0 0)
    (raw := varsX 472) (T := qG_ 472) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low45
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior451 : Lower true (varsX 451) (qG_ 451) 4 := by
  have h := lift_ok (u := true) (ms := ([33,67,100,117]).map swapRows ++ fixRows 0 0)
    (raw := varsX 451) (T := qG_ 451) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low45
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior376 : Lower true (varsX 376) (qG_ 376) 4 := by
  have h := lift_ok (u := true) (ms := ([16,65,98,100,101]).map swapRows ++ fixRows 0 0)
    (raw := varsX 376) (T := qG_ 376) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low45
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior370 : Lower true (varsX 370) (qG_ 370) 4 := by
  have h := lift_ok (u := true) (ms := ([16,49,66,99,100,101]).map swapRows ++ fixRows 0 0)
    (raw := varsX 370) (T := qG_ 370) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low45
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior362 : Lower true (varsX 362) (qG_ 362) 4 := by
  have h := lift_ok (u := true) (ms := ([16,49,66,100]).map swapRows ++ fixRows 0 0)
    (raw := varsX 362) (T := qG_ 362) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low45
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior346 : Lower true (varsX 346) (qG_ 346) 4 := by
  have h := lift_ok (u := true) (ms := ([16,66,84,101]).map swapRows ++ fixRows 0 0)
    (raw := varsX 346) (T := qG_ 346) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low45
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior314 : Lower true (varsX 314) (qG_ 314) 4 := by
  have h := lift_ok (u := true) (ms := ([16,66,83,84]).map swapRows ++ fixRows 0 0)
    (raw := varsX 314) (T := qG_ 314) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low45
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior307 : Lower true (varsX 307) (qG_ 307) 4 := by
  have h := lift_ok (u := true) (ms := ([33,67,84]).map swapRows ++ fixRows 0 0)
    (raw := varsX 307) (T := qG_ 307) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low45
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
def generatedKnown : List (Nat × Nat) := [(506,8),(505,8),(499,8),(491,8),(490,7),(483,7),(475,8),(474,7),(473,7),(467,7),(459,7),(443,8),(442,7),(435,7),(379,8),(378,7),(377,7),(371,7),(363,7),(504,6),(498,6),(497,6),(489,6),(488,5),(481,5),(466,5),(465,5),(457,5),(441,6),(440,5),(434,5),(433,5),(427,6),(426,5),(425,5),(424,4),(419,5),(417,4),(411,6),(410,5),(409,5),(403,5),(402,4),(401,4),(395,5),(394,4),(393,4),(369,5),(361,5),(353,4),(347,6),(345,5),(339,5),(337,4),(315,6),(313,5),(299,5),(297,4),(482,4),(472,4),(451,4),(376,4),(370,4),(362,4),(346,4),(314,4),(307,4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem generatedPrior : Known true generatedKnown := by
  intro e h
  simp only [generatedKnown, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact prior506
  · exact prior505
  · exact prior499
  · exact prior491
  · exact prior490
  · exact prior483
  · exact prior475
  · exact prior474
  · exact prior473
  · exact prior467
  · exact prior459
  · exact prior443
  · exact prior442
  · exact prior435
  · exact prior379
  · exact prior378
  · exact prior377
  · exact prior371
  · exact prior363
  · exact prior504
  · exact prior498
  · exact prior497
  · exact prior489
  · exact prior488
  · exact prior481
  · exact prior466
  · exact prior465
  · exact prior457
  · exact prior441
  · exact prior440
  · exact prior434
  · exact prior433
  · exact prior427
  · exact prior426
  · exact prior425
  · exact prior424
  · exact prior419
  · exact prior417
  · exact prior411
  · exact prior410
  · exact prior409
  · exact prior403
  · exact prior402
  · exact prior401
  · exact prior395
  · exact prior394
  · exact prior393
  · exact prior369
  · exact prior361
  · exact prior353
  · exact prior347
  · exact prior345
  · exact prior339
  · exact prior337
  · exact prior315
  · exact prior313
  · exact prior299
  · exact prior297
  · exact prior482
  · exact prior472
  · exact prior451
  · exact prior376
  · exact prior370
  · exact prior362
  · exact prior346
  · exact prior314
  · exact prior307
def generatedSamples : Array (Bits × Bits) := #[(BitVec.ofNat 152 (0x3e1c79e78003003c3838381004c001f08f673), BitVec.ofNat 152 (0x200a0800000050004084848000440005005231)),(BitVec.ofNat 152 (0x1c0000618003c000007c7c064070c26c34cb9c), BitVec.ofNat 152 (0x614e99062901d290c9d4b4824050c22c14c294)),(BitVec.ofNat 152 0, BitVec.ofNat 152 0),(BitVec.ofNat 152 (0xe0003801f81c00003c007f9809810c70c70c1f), BitVec.ofNat 152 (0x163042a8002c042524094b0808810c50410c0a)),(BitVec.ofNat 152 (0x6007e00e0007c007f80208e020f80f80fe0), BitVec.ofNat 152 (0x8cb140809264010c162b09008a020480e80d40)),(BitVec.ofNat 152 (0x183f8007000f803f800040f003f000fff000), BitVec.ofNat 152 (0xc8c580029b4081881b321000d0025000bea000)),(BitVec.ofNat 152 (0x1fc00000000fffc000007f0003ffff000000), BitVec.ofNat 152 (0x1300377d649b2e73a040627f0001ab7a000000)),(BitVec.ofNat 152 (0xffe0000007fff0000000007ffffc0000000000), BitVec.ofNat 152 (0x2451449228420000007525280000000000)),(BitVec.ofNat 152 0, BitVec.ofNat 152 0)]
def generatedColumns : List ColumnInfo := [(1,0,506,0,8),(2,0,505,0,8),(8,0,499,0,8),(16,0,491,0,8),(17,0,490,0,7),(24,0,483,0,7),(32,0,475,0,8),(33,0,474,0,7),(34,0,473,0,7),(40,0,467,0,7),(48,0,459,0,7),(64,0,443,0,8),(65,0,442,0,7),(72,0,435,0,7),(128,0,379,0,8),(129,0,378,0,7),(130,0,377,0,7),(136,0,371,0,7),(144,0,363,0,7),(3,0,504,0,6),(9,0,498,0,6),(10,0,497,0,6),(18,0,489,0,6),(19,0,488,0,5),(26,0,481,0,5),(41,0,466,0,5),(42,0,465,0,5),(50,0,457,0,5),(66,0,441,0,6),(67,0,440,0,5),(73,0,434,0,5),(74,0,433,0,5),(80,0,427,0,6),(81,0,426,0,5),(82,0,425,0,5),(83,0,424,0,4),(88,0,419,0,5),(90,0,417,0,4),(96,0,411,0,6),(97,0,410,0,5),(98,0,409,0,5),(104,0,403,0,5),(105,0,402,0,4),(106,0,401,0,4),(112,0,395,0,5),(113,0,394,0,4),(114,0,393,0,4),(138,0,369,0,5),(146,0,361,0,5),(154,0,353,0,4),(160,0,347,0,6),(162,0,345,0,5),(168,0,339,0,5),(170,0,337,0,4),(192,0,315,0,6),(194,0,313,0,5),(208,0,299,0,5),(210,0,297,0,4),(25,0,482,0,4),(35,0,472,0,4),(56,0,451,0,4),(131,0,376,0,4),(137,0,370,0,4),(145,0,362,0,4),(161,0,346,0,4),(193,0,314,0,4),(200,0,307,0,4)]
def genData5 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x9f4e2652c9348235148742204fc7b3c1d4e46f361a4cc6330174b4572a1449c4b24114843f1e0e46c33180b45427120843c1b0c054240f060240c03003f00a1a40b2ac899221f085d2275956440910f50290b1260b2264887a81435898059132443d20b1b24c02ca99221e9058d52601654c910f44290902cab2264887a11484c16559132443c60b42e6902ec99221e305a1724c1764c910ec8326902cab22648874a147e496059372443a28cbf26b02cbb9a21ca85239258164dc910e4a530982cab1ae4887251936016559132443740d3286902c899221b90699924c1654c910dc834ca9260b2a64886e41a649d3059532443661d1aec93a06b1221aa869948481644c910ce832451b2eb2a04885e43b649d3059532442f21d9b44b2ac6812217906cba35956340910bc4764a3acab2204885e21b489d6559102442e60d96e6b3a06b12217146df9358165dcd10b8a166cbac0b2ae8885a53b36616059772442d29d9b30b02cab9a21694ecd98581655c910b4a766cbb00b2ac6885a51b64c16561132442d2859b30b02cab922168ced198581655c910b46168cc2c0b2ae4885960b76612059532442c39dbb30b02ca9922161c2dd98581654c910af0164ca260bb2868851d0b766130591324427a1d9b5313aca812213986daa764965409109ca760d2726b2ac6884a73b6e819859572442539dab473420cba22129c6eb98581655c9108f8766d2f24bb2048847c3b26a637591034423e1d9349c9aec81a211d8ed5a3e497440910)
def genData6 (j : Nat) : Nat := if 7 ≤ j then 0 else (if j<3 then (if j<1 then (0x10ad5e8d9859572442b54a3661655c910acde919859572442b34a4661655c910abce998741954442af3a661d0654910abce998741943442af3a661d0650910abce998741932442af3a35a10654910abce896841943442af2a75a10650910abc6a26741942442af1a59a1065d110abc6966841972442af1a4a1d6058910abc6926841972442af1a39a1065d110abc68e6841972442af1a2a1d6059110abc68a6841974442ae9a66090650d20a9de998759542442a77a661d654c910a9de998755952442a76a99a1655c910a9d69a9859574442a75a6a61655c910a9d6926859572442a75a39a1655c910a5de9d9859532442974a7661654c9109f8e8997595024427e3a265d6440d109f8e8997591024427e3a265d63409109f8e899750d024427e1a989d64409109f869b925d1024427e1a5e4976409109f8693925d9024427e1a3e4976409109f868f925d1024427e1a2e5d65409109f868b93595024427e1a2e4565409109f828997591034427d3a664a3740d109f4e91928dd034427d3a365d65409109f4e8d97591034427d3a264d0650d109f46a637591034427d1a6e4d7440d109f4693935d9034427d1a3e5d6440d109f468f92591034427d1a3e456440d109f468b935d9034427d1a2e4d7440d109ec68397519434427a4a26517650d109dce959750d02442771a0e5d56549109bce919299d064425e5a7e4964dc9108fce81985d9544423f3a066176549108fce81985d9434423f3a0661744c9108fcaa7805d9544423f1a8e5d65409108fc6a397591034423f1a0e61655d1108fc68398595724423f1a0e6164dcd108fc68398591734423f1a0e5d86551108fc68397619524423f1a0e5d8650d108fc68397611324423f1a0a6375591108fc682985d5644423e7a266176551108f9e89985d9434423e7a266176509108f9e8998593734423e7a2653835d9108f9289985d9434423e4a266164dcd108f928994e0d764423d7a366176551108f5e8d985d9524423d7a365f84595108f5e8d95e09764423b7a466176549108dde95985d943442377a5661744c9108dde9593e1974442377a564f825d1108dd69b9561d434422f7a6661744c9108bd299985d1324421f7a7661654c91087de9d98591324421f7a16637458d2087de85985d9434821f7a165b805d13287de8593e11764821f4a7661644c91087be89985d9434421efa266164dcd1087be8994e0d764421dfa36617654910877e8d95e09764421bfa4661765491085fe95985d94344217fa5661744c91085fe9594e197348217fa564f865d11085fe9593e097444217da6e558750d2085f69b9561d434420ffa6661744c910f9058d2059532443e21644816550910e9458d805953244387387a1d6059510da85919241942442e53a361d6059510b946993059532442e50a361d6059510) else (if j<2 then (0xc910cf848396611324433e120e4d8654910cf4e61305d9434433d3984c1764c910cf4e61305d1634433d3984c1744c910cf4a613058d724433d2984c1435c910cf466130595324433d1984c1644c910cf464d80591324433d130e59844c910cf44c392619434433a9985012650d20cea65182419434833a548e4964dc910cbce61605d1634432f3985817458910cbca6160595744432f298581655c910cbca6160591724432f298581635c910cbca5d60e09644432f26941982dd510cbc9a50660b744432f26941982dcd10cbc66160595324432f198581644c910cbc58193e09644432f16064b8359510cbc26160595744432f098581655c910c9da616558d724432766959582dd110c9d9a56560b73442fc3a649d304c910bf0e8d2740d62442fc1a3419254c910bf068a3740d62442fc1a2419344c910be8e994748142442fa3a251d6440910be86922759102442f93a651d3050d10be4e8d4759103442f91a48dd6440d10be46923740d42442f63a46496540910bd8e8d9259502442f63a265d6540910bd8a9d9259502442f61a989d6540910bd86922759502442f61a2e616540910bd868b9759502442f61a2e516540910bd868b9359502442f61a225d6540910bd829d9259502442f53a365d6540910bd428d9759502442f33a46616540910bb8e992741932442ee3a459d2058910bb8e912758162442ee3a349d6058910bb8e898758164442ee1a6481644c910bb4e8d8758165442ed1a68dd0358910bb46993059532442ec9a64c90650d20bace994741943442eb3a651d0650910bace8d4758164442eb3a251d6059110bac6928758164442eb1a499d0650910b9ce8d8758165442e73a261d6059510b9c6a28758165442e71a6a5d6540910b9c6928758165442e71a495d6059510b9c68a8758165442e71a295d6059510b9c6888758165442e67a649d654c910b95e8d9759563442e57a36496558d10b9569f9359563442e55a4e4d6558d10b9568b9359563442de3a25d97440910b7869b725d102442de1a4dc97640910b74693735d903442dd1a2dcd7640d10b5569f9359773442d54a365d655d110b3c6926741972442cf1a299d065d110b39e917649d62442cdba44dd6058d20b2ee8d4758164442c75a6a5d655d110af869a8748142442be1a4a1d2058910af86890661132442bd3a6601344c910af4e8d8740d62442bd3a361d0350910af46a23740d62442bd1a88dd0350910af46a1064d132442bd1a68e1035c910af46923840d72442bd1a3419844c910aece919560162442baba66094050d20adcea19459502442b73a56518058d10adce959460132442b73a561d0650d10adce819859572442b71a8e5d6540910adc6839859774442b71a0e6165dc910adc6839859574442b71a0e61655c910ad5e8d9859772442b57a3661655cd) else (0x458d10e9c6016559132443a716855d0654910e9c5a15141952443a716561d0655110e9c5958741952443a71656050654910e9c58165e1172443a7160597835d110e9c58165e0d72443a7160597825d110e9c5816561373443a716059584dc910e9c5816561132443a716059582dd110e9c5816560b73443a7158581654c910e9c55d60e0965443a7098581655d110e9c2616059572443a556361d654c910e8d52165591324439e3784817650910e78de1205d1624439d2385d9035c910e6a609405d9434839a948481744c910e3cde1605d1624438f37661d0650910e3c9a106dd1724438f268419745c910e3c99d06e11724438e9875890650d20e3a58906e11734838e96241983dd120e395e1625d9424438e578589764c910e395a1725d9324438d9835817458930e365a137419434838d96361d0650d20e3658d87419434438d57858d7650d10e355e1635d9324438d5685cd764c910e3558d87459434438d5636057650d10e2e5a147419434438b96461d0650d10e2e521605937344387668597745c910e1d9a1655d1724437c393481654c910df0e49305d1324437c3924c1644c910df064d27419324437c193481764c910df064d205d1324437c193481644c910df064d20451324437c1924dd064c910df0649305d9324437c1924c1654c910df04df96481324437a1944837650910de865120dcd424437a1944817650910de86494741942443793974c14650d10de4e453051943443791944c17650d10de465130459434437919351d0650d10de464d4141943443789944c90650d20de264d4049943483763974815654910dd8e49655d102443763914815654910dd8655205d952443761954811654910dd864b975950244376192e516540910dd86499759502443761926516540910db8e4960593724436e392581644c910db865920dd5624436e1964837458910db865920dcd624436e1964817458910db864960dd5624436e1925837458910db864960dcd624436e192581654c910db859f93481624436d393581654c910db464d60591324436b1945837559110daa65162419434836a5945897650910d9c6416558d72443671905956350910d9c5959058d524436579365d6558d10d9564d6559132443635566537559110d78e49765d1024435e17989d6440910d74e4d765d1034435a547e4964dc910d5ce5e97595024435727995d6540910d5565f93597734434f297581645c910d3c9a5065d1724434e5965cb7458910d39659725d1624434e576e512758910d395db9349d624434e57664b7458910d395d992dcd624434d9935837458d20cf8e61205d9524433e3984817650910cf8e61205d9324433e3984817458910cf8e61205d1324433e392601744c910cf8a5d20619424433e198481654c910cf866120591324433e192601654))) else (if j<5 then (if j<4 then (0x17358910f385c960dd162443ce1725817458910f34dcd6740d62443cd1764dd6340910f345d9305d163443cd1674c1635c910f3459d3045163443cc9375890650d20f324dd6049563483cc9235817458930f315cd625d932443cc5635c9764c910f2cdd94741942443cb1745837559110f2c5d1605d564443cb14758164dc910f2c51d6059172443cb1475811559110f2a91d6241943483ca5745897650910f29519725d162443c99648dd0650d10f2658e4741943483c996351d0650d10f255d1635d943443c956351d1650d10f2558d415d943443c8d644dd2650d20f1ca5d6059574443c7257581655d110f1c65d6059774443c719758165dcd10f1c65d6059574443c7197581655cd10f1c58165dd172443c716059574dc910f1c581655d172443c7157581655d110f155e53759563443c35565d37559110f0d559745d564443bc1804d9254c910ef0601264d132443bc137481864c910ef04c12661132443bc1274c1864c910ef0481864d132443bc1204d9844c910ee8521205d132443ba148481644c910ee85212045132443ba1474818650910ee49213050d72443b91484c1744c910ee45213059132443b91484c1144c910ee451d3061943443b9143601744c910ee450d8059132443b9143601144c910ee45053061943443b89825013650d20ed8a1d2059542443b61a25978340910ed86612059542443b6198481654c910ed86498059532443b6158481654c910ed855d2061952443b6152601654c910ed85452061952443b5238595035c910ed46613059532443b51584c1654c910ed44c16561132443ae16849d064c910eb85a1205d932443ae16261d0650910eb85898741932443ae162601764c910eb85898059132443ae162419844c910eb45a13741932443ad1684c1764c910eb45a1064d132443ad16361d0650d10eb458d8741932443ad1636050650d10eb458d805d932443ad163601654c910eb458d0661132443ac9684c90650d20eb258d8241943483ac96260d0650930eac5a14741943443ab16851d0650910eac5a14141943443ab16461d0650d10eac5918741942443ab1646050650d10eac5216059373443ab14858164dc910eac5216059132443ab1475838359110eac51d60e0964443ab1466017458910eac5198050d62443aa9646090650d20eaa5898441932503aa56461d2650910ea95216259132443a739858165dd110e9ce616059772443a7398581655d110e9ce616059572443a7298581655d110e9ca616059572443a72875816550910e9c9a16540d72443a7258581655d110e9c9616059572443a71a26016558d10e9c6616059774443a719858165dcd10e9c6616059772443a7198581655cd10e9c6616059572443a7198581654c910e9c65d8059563443a71875816550910e9c61d6059532443a71805957) else (0xf447723a11c48dc46b23411948c445f22b114c8a044d225111c88844121f10ec87043521910a484c423210105c81c4052010fe47ec3f31f80fb47d43e71f20f847bc3db1ec0f547983bd1dd0edc75c3ab1d10e7c72c38d1c20dec6f03751b90dbc6d83691b30d8c6c035d1ad0d4469c34b1a40cfc66c3331980c6c6303091830c0c6002fd17d0bdc5dc2e51710b645ac2d31680b345942c71620b0457c2bb15c0ad45642a91530a8c54029d14d0a5c5282911470a1450427f13e09e44ec273135099c4c826112f096c4b0255129093c498249123090c48023d11d08dc468231114089444421f10e086442c213108083441420710207ec3e41e90f3078c3c01d70e7072c3901c50e106fc3781b90db06cc3601ad0d5069c3481a10cf066c3301950c9063c3181890c3060c30017d0bd05dc2e81710b705ac2d01650b1057c2b81590ab054c2a014d0a5051c28814109f04ec27013509904bc258129093048c24011d08d045c228111087042c21010508103fc1f80f907b03cc1e00ed075039c1c80e106f036c1b00d5069033c1980c9063030c1800bd05d02dc16809904801ec0c004501b0054000fe050d205d132443f8143481644c910fe050d2045132443f4393481654c910fd06493059532443f41524c1654c910fd04dd2059532443f41274c1654c910fc851d2059542443ec16349d064c910fb058d205d932443ec163481654c910fb058d0649532443ec1624dd064c910fb0589305d932443ec1624c1644c910fb0589064d132443ea1644990350910fa85894741942443ea1464817458910fa85192050d62443e91648dd0650d10fa458d4741943443e91635050650d10fa45193050d62443e9143581644c910fa25913241943483e89624d1064c940fa150d6259132443e62275956440910f986896558d02443e6192581654c910f985952058d52443e6152581654c910f9849d6059532443e6120595644c910f984816558d42443e53a361d6059510f94e8d6558d02443e539358165dcd10f94e4d6059532443e51974c16558d10f945953058d52443e5160595344c910f944e16558d02443e51375956340910f944dd6059532443e51305957458d10f944c16559132443e5130595635c910f944c16558d42443e50a361d6059510f9158d9259532443e4563549654c910f9158d2759532443e31475956440910f8c51d6059542443e1543595644c910f705cd205d932443dc1724c1764c910f705c9305d132443da17489d6440910f685d120dd942443da1744817650910f645d1305d943443d91474c1435c910f64505305d943443d8943481744c910f624c9405d943483d85435c9744c910f6150d2745132443d8543485744c910f58dc9655d102443ce17649d0358910f385d920dd162443ce1764837358910f385d9205d162443ce17648)) else (if j<6 then (0x7d43c200050407060c3c200000003060c3c2000a0704021850f08000000a28100000000090f0400243c128504000000090f0400143c1000000000285040a040402850408ca142000028101000289062141289040a04040a04040492068201a050400000008ca3420000124410000223418890621418890683c1a0f0683c1a04040685040a0f040033070606482504040037604080000889040000000000000000000000000000000823040000304040000000000000000a040400000000000000000208c10000243c190f07060103060100000000000000000088d06235810200001d04048d04048d05234148d06244100000000000000002a141000014101c0f0400207703d41030007445c2000000000a18060dc1000dc1000000000000000000014101000000000000000c4100000000002d040000000000000000000000000000504040000000000000000028681a180607c10000186816180400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000124a430a14810428905248a1481030b6117113c0f1205043ca2501c481dc0f080fc43ec1ea16a0c50b81175040f2dd968cb16513265920c8763f31d58e4c6f63031758b4c516243115884c3f61e30e5854c2160f3055824c0f606300d800bf15f42f657a0bc15df2eed758ba95d32e75710b855be2dcd6d4b615af2d55698b495a02cdd65cb2558e2c4d620b0d5852c055fcafb57c2bbd5c0ad75672b1556caa754c2a55524a8f5462a2550ca8354029f54e8a6b53429954c4a5f52e29654aca535282935494a47522290547ca3b51928bd458a2350d284541ca0b50427fd3ec9ed4f227853bc9d54e6270d3809bd4dd26dd35c9ab4d1267d3389934c826353089814bc25d52e49694b025752a89514a7252d284933495248523090f483240d2008f747723ad1c48d9468231d17c8bb45c22bd14c8a344d224511c88b44121fd0f887943b21b50c886142c213d09884341d20dd05c82b4142095044819408201cff07f53f91fa4fcc7e33f01f5cfa87d13e11efcf6079b3c91e24f0c7773b41d64eac7533a51d1ce7c72f3961ca4e407113871c2ce107053811bccde06ed3721b84da46cf3661b24d8c6bd35d1adcd686b13571aacd4469f34e1a4cd146873421a04cfc67b33919bccd86633301974cb465732a1944c9064531e18e4c6062130f186cc3060f3061824c005f72f717acbc45df2eb174cb945c12dc16d4b645af2d61674b345972ca162cb105852c115e4ae05672af1554a9854329d14dca5c52b291147ca2c50727f13ec9d84e9273138c9b44d726a134499c4cb26413149844bf25e12e496c4b325812b49544a7252128493c49b249123c91848924011f48) else (0xa14100090c28509234148d04a141a0404a24100090c20408000a14128504000000028a40709248102214100000a14100a370102a0404a364102a0405862810200081d50408001a14143711da040c0c8505010141705a1410141c119204081d05810160404860150805a24100000a1410000281018859040a81012850681c12856040941d810228560408000000000000001704a48100000000000000000000000028a0400281016040581010000085c1a040681c1a040400141c1a0706810100000089104089204000a14100089104028504002248128504028504000028d042a681c20a40523410a406244148d0400029010a404049204a14150f0543c128504001244128504050f0543c100028504000001248149104050f0543c10243c190f0401170400000143c101a04a141213a070800243c100003060100003e03108001da040807485e43c34220507c100476810261a90f0986243c200049104050f048))))
def genIndex6 (j : Nat) : Nat := if 1 ≤ j then 0 else (0xf01e01ee780d5fe03c0780d419cc58b30d28414534e5f01eb4ed8f4716f68aea0929aed5d73e4f494d32be17c8ce9646432f4488d89f1d2c6b7fc6f80823e03c041ef01e03c0780b9136338b1a024412d6780f016abc031ff01e00c7780f00fc3c07804d7e03c0201f01e01d43a7556e6f10c80f01e03c020a98fe02cb00ff01e008ce03e0f67201088f01e01b7780b0c183c0018c67e02083a9f01657c01d8331c451828410c66e1807)
def genData7 (j : Nat) : Nat := if 14 ≤ j then 0 else (if j<7 then (if j<3 then (if j<1 then (0x10650910f58a3ac0b2221eb14158164443d52c4a02c8907aa5096059120f54922c0b1281ea56449942443ce50eb02ca8879c95d6059510f38c3ac0b2a21e716559102443ce2cab1a048879c5950655110f38b2a0ca9a21e716541952443ce2c0b2ee88879c58165dcd10f38b02cbb9221e716059574443ce2c0b2ae68879c581655c910f38b02caa1221e716059532443ce2aeb02ca8879c5456059510f3843ac0b2a21e579359563443caac6b2a64887954dd6558d10ef1b92ec81221de3725d102443ba6e6bb2068876a51d2050910ed4a12ec82241cf267419744439e4ce832e48873a59d2058910e74b120dba241ce96241b734839d2c4836e29073a589065d120e74b120cb9a41ce927581624439caec93ac48873959d2158910e7293ac2b1221cd9674c1634439b26eb02c6907364dd6058d10e6abb26eb1a21cd5674c5634439aa6eb0ac68872e59d4059120e5ca3ac0b2221be287482624437c50e90484886f8a1d2058910df143a40a1221be180499324437c30092a64886f84818654910df09030ca1221be120619324437c240c2a64886f8481844c910de91c206b9221bd1804d9324437a3009a264886f44c18654d10de89830ca1a21bd130619324437a260c2a64886f44c1844c910de49030729221ba9825016448375304a0286906ea5098059120db9c02acaa221b7180995324436e300b2a64886dc5978340910db49030b19221b5983541524c35e50eb02c8886bca1d6058910d793420cba221af268419724435e300b2ac6886bc6016458910d78b420caa221af168419534435e2d0832a4886bc5a10650d10d78b420ca1221af168419324435e2c1c2ac8886bc5838459510d78b0706b2a21af160e0d644435e2c1c12ca886bc5838259110d7843ac0b2221ae982581644835d304b02c6906b660d6058930d3b342cab922197787a1d654432ecf12baca8865d95f8159510bf1cb240992217e39348162442fc724bb204885f8e497440910bf0cb44e812217e19489d02442fc32543a04885f86490650910bf0c920c992217d3935d903442fa726ba206885f465a3740d10be8ca46e81a217d19341943442fa32683264885f464a3740d10babc9b0eb2a217549361d65442de32933a0c885bc64a6741910b3acb50eb2a213f396601324427e726c02c4884fce498058d109f9c830caa2213f29858d024427e33083264884fc65b83409109f8cb700aa2213f193e19024427e321c3aca884fc64387591109f3c930eb22213e49261d644427af26c3aca884dde558750d108fbc8b0eb1a411ef9261d644423bf26c3aca8845fe558750d208bfcab0ea1a2117d96e15744c22fb2c42ae8987944c16558d10de09030729221b6120616324434e300b2ac6885f064c2740910bd0ca04e812217619509d02442dc32c13a048841f658855d130) else (if j<2 then (0xc884fd653835c9109faca704bb2213f594e05654427eb2943ac4884fd64f87591109fac9f0cba2213f593e19724427eb27c22ec884fd64f845c9109fac9f04bb2213f593e09744427eb27c12c8884fd64f81591109fac970eb2a213f592e19744427eb25c2aec884fd64b845d9109fac9706bb2213f592e0d744427eb25c1aca884fd64b81595109fac950eb22213f498595744427e930b2ae4884fbe598250d209f7c930eb22213ed98499434827bf2cc1a84984efe59844c9408ffcc2ecaa2211ff985d9534823ff30bb2a48847fe6176545208ffcc2eca1a411ff985d9434423ff30bb2849847fe6176505308ffcc2e8b1a211ff985d1324423ff30b9a829047fe5d86549108ffcbb0ca1a411ff97619434423ff2ec2264b047fe5d844c9108ffcb30eaa2211ff9661d534823ff2cc3aa48847fe598750d208ffcb30ea1a211ff9660b754423ff2cc0eea9047fe5587591108ffcab0eb1a411ff9561d624423ff28c3ac69047fe518758d108ffca30e992211ff9460b734423ff26c3ac89047fe4d87591108ffc9b0ea12211ff93607744823ff24c3aca8847fe498750d108ffc8b0ea1a411ff9061d434863fd30b2ae48847fa61435c9108fecc6eab22211fd98dd5634823fb31baac48847f66375585208fecc6e8b1a411fd98dd1314823fb31b9a848847f66176549108fecc2eca1a411fd985d9434423fb30ba2648847f66164dcd108fecb70aba2211fd96e15734823fb2dc2ae48847f65b845cd208fecb706ba2211fd96e01744ca3fb2bc32e88847f657865cd208fecaf0cb92211fd95e11764423fb2bc1aec9047f657825d9308fecaf04bb2211fd95e05764823fb29c32e69047f653855d9108feca706bb2411fd94e0d764423fb29c1ae48847f653825d9308feca702bb2611fd94e05734823fb27c32e88847f64f855d9208fec9f08bb2411fd93e11764423fb27c22e48847f64f825d1108fec970abb2211fd92e0d744423fb23c2aec9047f647845cd208fec8f00ba2651fd90e05744cbf826e90264887f04c5204c910fe09824c99221fc13049532443f824e98264887f0485304c910fe09026c99221fc1204d132443f428e90284887e85052050910fd09028ca1221f91474c143443f228298286887e44c14650d10fc499280a1a41f853250543487ec44eb2a04887d86496540910fb0aba40a9221f615148152443ec24132a64887d84816550910fb0902ca99221f612055952443ea26132a64887d44c1654c910fa8982aca9a21f4923541524c3dc2ce902c4887b85890650910f70b120c99221ee16148162443dc24eb02c4887b84856058910f70902c8b1221ed1674c163443da2c683286887b458d064c910f68b0a60b1a21ed13758163443da262b02c6887b44c16558d10f64992c0b1a41ec923581624c3d62c883286887ac59) else (0xeb252baca885dd6488759510b7bca2ceb12216f596dd562442deb2dba2c4885bd65b7358910b7acb50eb22216f5965d162442bef2cba2e48857de55765d110afbcaaec8a2215f7945d972442bef24bb2e88857de45865cd20afbc8b06bb2415f791609764c2bef22bb2a29057de457650530afbc8ae6a0a415f69759172442beb2eb2ae88857d65d64dc910afacbac8b92215f596dd574442beb2dbaa288857d65b745c910afaca6ecb92215f592dd974442beb23baac29057be557648d20af7c930cba2215ef9261176442bdf24bb2a48857be49744c910af6cb6ea91a415ed92dd562442bbf2c9ba8690577e51764c930aefca26eb1a415df9361576442bbf26bb2868857765a3750d10aeec9eeab1a415dd93dd163482bbb26bb2869057764d744c910aeec946ea1a215bf9651d43442b7f28c2aec9056fe517650d20adfc9a8eb22215bd9691d43482b7b29baac88856f6537350910adeca2eca1a215bd9191d43482aff2ac22e69055fe55835d110abfcab00ba26557f955d1624c2aff2aba2c29855fe557448530abecaaeca92214fd96dd5624427ef30bb2a8884fde6176549109fbcc2eca1a213f7985d9424427ef30bb264884fde617458d109fbcc2e8b12213f7985d1324427ef30b2ae8884fde61655c9109fbcc2c9b9a213f798591734427ef2ec32a8884fde5d86549109fbcbb0ca1a213f797611324427ef2cc3aa8884fde5987549109fbcb30ea1a213f79661d424427ef2cc3a64884fde59844c9109fbcb305baa213f79660b744427ef2cc16e6884fde5587591109fbcab0eb12213f79461d654427ef28c3ac6884fde5187589109fbca30e992213f79460b764427ef28c16e6884fde4d87591109fbc9b0eb12213f79361d424427ef26c32a4884fde4987595109fbc930eb22213f79261d634427ef24c3a86884fde498650d109fbc8b0eb1a413f791619524427ef22c3286884fde45844c9109fb4c6eab22213f6985d5644427ed30b2ae8884fda61655c9109fb4c2c8b92213f69858d724427ed30a1ae4884fda5f82591109fb4bb0ca12213f598dd9424427eb31baac8884fd66375589109facc6e8b12213f598dcd624427eb31b9a84884fd66287591109facc2ecaa2213f5985d9524427eb30bb286884fd66176509109facc2ec992213f5985d1324427eb30b2a64884fd66164dcd109facc2c9b92213f598591324427eb308b2a4884fd6611650d109facc228992213f597e15644427eb2fc22ca884fd65f83591109facbf04b2a213f597e09644427eb2dc2ae8884fd65b855c9109facb708b92213f596e0d744427eb2dc1ae4884fd65b825d1109facb50ea12213f595e1d644427eb2bc32e8884fd657865c9109facaf08bb2213f595e09764427eb2bc0ac8884fd65387595109faca70cb92213f594e15764427eb29c1ae))) else (if j<5 then (if j<4 then (0x1d624435ecd0bb2e4886bd9a1655c910d7b3422cb9221af5685d9324435dcd0932e29067e61d0650d20cfcc3a0ca1a219f906e11734833f20dc1ae88867e41984dcd10cfc83307ba2419f79161d634833ef0dba2e48867de19745c910cfbbc2eca12219f7785d1624433eeedc22e48867d61d1650d10cfac32e9b92219f5815d9434433eaf1bb2848867d5e37458910cfabc2eca1a219f5785d9424433eaf0bb2648867d5e17458910cfabb708b92219f576e0d744433eaedc1ae48867d5db825d110cfabb309b9a219f576613724433eaecc16e88867d5d982dcd10cfa8b706ba2219f516613734433df24c3ac88867b61d2650d20cf6c12eca1a419ed26e11734833da4cc1ee890677e4d8759510cefc9b0e992219de385cd714833bc70a1ae48867761d3650d20ceec3a6ca1a219dd835d9424c33bb06ba2c4986774dd8650d20cdfca30ea12219be485d17244337c90a1ae48866f61d4650d10cdea42e8992219bd485937344337a8ec32868865fe558754910cbfcab0ea1a4197f9561d434432fcb0b2ae48865f61d5654910cbeabb0ca92218ff9661d624431fcd0bb2e48863f9a1765c520c7f342cab92217f39759502442fe72eb2206885fce597440d10bf9cb2e8812217f3955d902442fe728bb206885fce517640910bf9c9aec812217f3935d102442fe726b2a04885fce497640d10bf9c92e881a217f39259103442fe722b2a04885fce456440d10bf9c830ab22217f39061165442fe52eb2204885fc6616340910bf8cbaca812217f19759103442fe32eb2204885fc65d6340910bf8cba86812217f196dd502442fe32dba204885fc65b7340910bf8cb2a6812217f19650d02442fe329bb204885fc6537340910bf8c8aca812217f19159103442fe322a1a04885fc641635c910bf8c82c6a92217f19058d42442fcf2c93a64885f9e512758910bf3c9a4eb12217e79261d64442fcf24c32e8885f9e49845d910bf3c92eca92217e7925d132442fcf24b26e4885f9e49644c910bf2c96eab12217e592dd162442fcb25b9ac4885f9649764c910bf2c92ca992217e49261974442fc924c22ec885f664d0650d10bebc9b0eb2a217d79361576442faf26bb286885f5e4d654c910beacb46ea1a217d5935d932442fab26ba264885f564d644c910beac9a28992217d5928dd43442f9b2693286905ee6510650d20bdbcba8ca1a217b79651d43442f6f2ca3a84885ede4d4759110bdbc928eb22217b79151943442f6b29bb284885ed6537559110bdaca6e6a12217b594a1d64442f6b28bb286885ed6517650910bdaca22ca1a217ad9448d41482f3b2899282985dde5d5654910bbbcab06ba2217779361d65442eef24c3aca885dde455654910bbacc50eb2a21775955d952442eeb2a8b2a4885dd6528759510bbaca4aeb2a2177592a1d65442e) else (0x21cf567451634439eac2ba2c68873be592758910e76bb24eb1221cdd635d9434439bac6ba2c29872f5917650d20df9c830caa221bf386dcd024437e70cb9a04886fce19035c910df9c2206b9221bf3805d9544437e50e83284886fc659804c910df8cab00b1a21bf195601624437e32ac0264886fc6518058d10df8ca300b1221bf194601324437e326c02c4886fc6498058d10df8c3a0caa221bf187419524437e30e83286886fc61d0650910df8c3a0c99221bf18740d624437e30e81a84886fc6198340910df8c3206a9221bf18640d424437e302832a8886fc6050654910df8c0a0ca1a21bf18140d424437e301baac4886fc6037458910df8c06e6b1221bf1805d9324437e300baac4886fc6017458d10df8c02e8b1221bf1805d1324437e300b9ac4886fc601654c910df8c02c899221bf18054d624437e300a1ac4886fc6011558910df8c0228b1a21bf180451324437e2edc1a04886fc41b855d110df88370ab9221bf106e11724437e20dc1ae8886fc41b835c910df883704ba221bf106615324437e20cc26ea886fc41984dcd10df883309b9221bf106611324437e20cc16ea886fc41982dd110df883305b9a21be982419534837d30483286906fa6090458d20df49030ca9221be920611324437cf24c3ac8886f961d2650910df2c3a4c99221be527619324437ca4cc2264886f92498759110decc1a0ca9261bd983419424c37b3009a264886f64c18650d10dec9830899221bd79361d654437af26c3a64886f58e1435c910deac3a6ca1a21bd5874d9324437ab0c9a264886f56053650d10dea9bb0c99221bd5366113244379c7091ae2906f360d2650930de6c126ca1a41bcd32611314837730883264a06ee5018650d20ddbca30ea1221bb6485d17244376c90a1ae4886ed921145c910ddac3a8ca1a21bb5875194244376b02a3286886ed521744c910ddaa42c9b9a21bb5485937244376a90b2264886ed521144c910ddaa3f06b2221bb547e096444376a8ec3286886ed51d8650910ddaa0b0ca1a21bad844993250375b04a3286906dde6165dd110dbbcc2cbb9221b7798595744436ef30b2ae4886dde558754910dbbcab0ea1a21b7698595744436ed30b2ae4886dda1d6550910dbb2c2caba221b7658595724436eb30b2ee8886dd66165dcd10dbacc2cbb9221b7598595734436eb30b2ae4886dd661654c910dbac3acaa1221b7587595324436eb0eab2a8886dd61d5654910dbac0aaca9221b7565e11724436eacbc1ae8886dd597835c910dbab2f04ba221b7565613734436eacac26e4886dd595844c910dbab2b05ba221b756560b734436eab0b2a64886dd55f8259510dbaabb0ca9221b7551619524436e930b2ae8886dd261655c910d7d3420cb9221afa68419714835f2d0832a4886be5a10650d20d7cb420ca1a21af7966)) else (if j<6 then (0xb02ca89221ef16059373443de2c0b26e4887bc581645cd10f78b02c8b9221ef16059132443de2c0b2226887bc581635c910f78b02c6a9221ef16058d42443de2c0a9ac4887bc5814358910f78b022ab2221ef16045562443de2c08a2c6887ba59d2058910f74b120cb9a41ee96241971483dd2c4832a6907ba5890654520f74b120ca1a41ee962419424c3dd2c483264a07ba5812558d20f74b0248b1a41ee92758162443dcf2c93ac4887b95d92758910f72b3a42b1221ee5625d942443dcac4bb264887b9589644c910f7293ac8b1221ee52758562443dca2eb12c2907b658d0650d20f6cb1a0ca1a21ed963419424c3db2c683282987b65813558930f6cb0268b1261ed93758163483daac6bb286887b558d764c910f6ab1aca99221ed56345943443daac29b282987ae5910650d20f5cb220ca1a21eb94758164443d6a8eb2ac8887ad5197458910f5aa3286b1221ead6449943483cf2ca832a48879d9a1655c910f3acbacab1a21e759259563443ceacaba2c68879d595644c910f3ab2ac6b9221e756558d52443ceacab1a848879d55b7559110f3aab2eab2221df3765d102443be2edba2048877c5db7340910ef8bb2e881a21df1765d102443be2ecb9a048877c5d91440d10ef8bb206b9221df17440d72443be20dbaae88877c41b745c910ef8832eaba221df1065d372443be20cba2e48877c419155d110ef4bb20891a41de9205d952443bd240ba2648877a419255cd20ef2b96e8b1221de5725d932443bcae4ba2c4887795c9744c910ef293a2899221de5215d132443bb46e83286887764dd0650d20eec982eca1a21dd9065d1324c3baee6bb286887758dd1650d10eeab9aec99221dcf9349d32443b9a6e93286907734dd2558d20ee6996eab1a41dcd325d943483b9a64baac69077349d344c910ee691ae8b1261dcd235d1214c3b748e832869076e51d4340910edca3a0ca1a21db9405d943483b6c90ba2e48876d921145c910edaba6eca1221db574dd564443b6ae8bb2868876d5d17650910edaba2eab2221db54759372443b6a8eb22e48876d51d435c910edaa3a8689221db54745943443b6a8e8aac88876d5077559110edaa0aeca1a21db5415d564443b6a82a1ae48876b91d2650d20ecf23a6ca1a41d9e3751943443b3a8e9b2868876750d7650530ecea1ae899221d9d3751943483b3a68b9a829075da5d655d110ebb2bacaba221d759759774443aeb2eb2ee68875d65d655d110ebacbacab9a21d7565dd172443aeacaba6e48875d595745c910ebaabacaba221cfa68419724439f2c1ba2c69073e5817458d20e7cb02e8b1a21cf9605d1624c39f2c0b2ae48873e58164dcd10e7cb02c8b9a21cf6685d9724439ecd08b2e48873d5db7458910e7abb6e6b1221cf5765d1634439eaecba2c48873d5d97358910e7ab3ac6b92) else (0x50910ff0906eab1221fe120dd162443fc241b9ac4887f84837350910ff0902eca9221fe1205d942443fc240bb264887f84817558910ff0902e8b1221fe1205d132443fc240b9ac4887f84817350910ff0902ca99221fe12059132443fc240b1aa4887f84816350910ff0902a6b1221fe12050d62443fc2408b2a4887f84811558910ff09022899221fe12044d42443fc20c92a64887f48e1035c910fe91bac881a21fd23750d02443fa46e83286887f48dd0358910fe91ba06a1221fd19359103443fa270b1a04887f44dd6340910fe89ba0c99221fd13650d02443fa260bb286887f44c1764c910fe8982e8b1a21fd1305d132443fa260b2a64887f44c1644c910fe8982c6b9221fd13058d52443fa260b1a84887f44c15358910fe898286b9221fd13050d62443fa260a1a24887f44c11650d10fe898228b1a21fd13045132443fa20c9a264887f24c90650d20fe499208b1a41fc93241131483f9246832a4987f248d0558930fe49026899221fc79349d32443f8a6e93264887f14d9254c910fe293a6c99221fc5274d132443f8a4c9a264887f148d1448530fe290a6899221fb14759103443f628eb2204887ec51d4340910fd8a3a0ca1a21fb14741942443f628e81a84887ec5194340910fd8a3206a1221fb14159103443f6282a1a04887ec5050650d10fd8a0a06a1221fa94748142443f5284822c6907ea509044c520fd4a024ca1a41fa54749942443f328683282987e65013650d20fcc9a20c99281f993051943443f2c6ea3286887e551d3650d10fcaa1ae899221f954359132443f2a868b282987e550d144c910fcaa0a6ca1a21f95414d1214c3f1a6893264a07e34d12350520fc69928ca1a41f8d3250d21503ee730b2a04887dce5d6540910fb9ca2ca81221f739359502443ee52eb2a04887dc95d6540910fb8cc2ca81221f719759502443ee328b2a04887dc64d6540910fb8b2ee881221f7165dcd02443ee2cac1a04887dc5957440910fb8b2ae681221f716540d72443ee2aeb2a04887dc55d0654910fb8ab2a681221f715640d52443ee2a2b2a04887dc5450654910fb84baca81221f695241951483ed240ab2a4887d9649654c910fb2a92ca99221f652759532443eb2a682ac4987d5e4d8759510fabc9acbb9a21f579359532443eaaca9a264887d54dd654c910faa49b0eb2a21f395441561503e6a8eb2a84887bca1d6059110f793420cb9221ef26741942443de30eb02ca887bc61d6059110f78b3ac681221ef16740d62443de2cab1a04887bc5910358910f78b06eab2221ef160dd562443de2c1ba2c4887bc5837358910f78b030ab2221ef16061165443de2c0c1ac8887bc5818259510f78b02eab2221ef1605d562443de2c0ba2c6887bc5817458910f78b02e6b1221ef16059574443de2c0b2ae4887bc581654c910f78)))) else (if j<10 then (if j<8 then (0xd9abd6abd3abd0abc2abbfabb72baeaba0ab92ab84ab81ab7eab7bab78ab702b67ab5f2b56ab4e2b45ab3d2b3a2b2c2b23ab1b2b182b152b122b0f2b0c2b03aafb2af82af52aecaadeaad62acdaacaaac22abf2abc2ab3aab0aaa82a9faa91aa83aa7b2a782a752a6caa642a612a58aa502a422a39aa36aa33aa30aa2daa2aaa27aa19aa112a08aa05aa02a9ffa9f1a9de29d029bca9b429a6299da99aa997a994a991a98ea97b296d2959a94ba93da93aa937a934a926a923a920a91da91aa917a914a911a90ea900a8f2a8e4a8dc28ce28c028b228a428a12898a8902887a87f2876a873a870a86da86aa85ca859a84ba848a83aa837a82f282c281e2810280227f427e627dda7d527cca7c427bba7ada79fa79ca794278ba783277aa76ca764275ba753274aa742273f27312723270fa70ca709a6fba6eda6eaa6d726d426d126c326c026b226a4269626932685267ca669265b2652a64a263c2628a625a622a61a260c2609260625f825ea25e725e425e125d325caa5c7a5bf25b6a5b3a5ab25a825a525a2259f259c259925962593258aa582257f257c25792576257325702567a55f2556a54e2545a542a53fa53ca539a536a533a530a52da52aa527a524a521a51ea51ba518a515a50d250a25072504250124f8a4f024e7a4e4a4e1a4d3a4c5a4b7a4a9a4a12498a4902487a484a481a479247624732470246d246a2461a4592456244da44aa4422439a431242e242b2428241fa41ca414240ba40323faa3f7a3ef23ec23e3a3e0a3d823aea36f2345a31122dca29d2273a239a20aa1d0a1a1a16d2133210420d52095a06c2042a00e1fc91f899f601f311ef19eb79e889e4e9e1f9e011dd79dae1d799d559d211cf21cc31c8e9c6a9c3b9c121bdd9ba39b851b669b3d1b191aef9abb1a919a731a4f1a1a99e619b199881959192a18df989a98609831980817de97af977b174c172816f916bf1669963a961c15e795b3158f15659541950d14de14af14909467143d940e93ea93bb9392135d933412ff92c59296926d123311fe91c4918511561121910310e490c0909c90789044100a0fe08fb70f778f430f1f0ef58ebb8e818e528e290df48dc00d860d518d178cee0cbf0c958c718c428c088bc90baa8b868b6d8b548b150af10ab70a7d0a430a1989f009c689a28979094a092608ec08cd88a9887a88510827880907f007d187b3078987600747072306ff06db06a1067d06538635061105ed05c9058f056b054c852e050a04e604c2049304748450842c840303df03aa83810352032e030a02eb82d282b982a08292828482768268826002578244020481d00196015c011c80e280a8806e803480007f889d8640910ff113ac881221fe19648132443fc326902c4887f86496540910ff093a0c99221fe12740d62443fc24c81a84887f848376) else (if j<9 then (0xe8c2e5c2d7c2cf42c142b342b042a242944280c2784259c240c232c22a4216c20e41fac1e1c1c8c1afc19141784164c1514148c13ac12cc11ec10b40fd40e9c0d0c0bd40a9c0964088407a406c4063c055c04d403f4036c028c025c022c01a4006bff33fcf3fc6bfc3bfb5bfb2bfafbfa73fa43f8b3f7d3f5ebf403f37bf29bf213f18befa3edbbed33ec53eb73eaebeabbe9dbe84be76be6e3e5abe4cbe49be46be333e1fbe173e0ebe063e033df53de73dd3bdc5bdb7bda9bd963d883d7fbd773d693d60bd583d4fbd3c3d2e3d203d17bd0f3d013cf8bcf5bce7bcdf3cd6bcd3bccb3cc2bcb4bcb1bcaebcabbca8bc9abc8cbc7ebc763c733c6abc67bc64bc61bc5ebc5bbc58bc55bc4d3c44bc41bc33bc2b3c22bc1fbc11bc093bfb3bf83bf53bf23bef3be6bbe3bbe0bbddbbdabbccbbbebbb63bb33bb03ba7bba4bb96bb93bb8b3b7d3b74bb6c3b63bb60bb583b553b523b443b363b283b1a3b173b143b0bbafdbaf53af23aef3ae6bae3bad5bacd3aca3ac1bab93ab63ab33aa53a9cba99ba96ba8e3a803a723a5eba563a533a4aba3cba293a1b3a0d3a04b9fc39ee39d539bc39a3398fb97c3968b94fb936b91db90fb901b8e8b8dab8c738b938ab3897b88f3886b878b8703867b85f38513848b83538273819380b37fd37ef37e137d337cab7c7b7bf37b137a8b79ab78cb784377bb773375a3746b733372ab71cb703b6eab6e236d9b6cbb6b836b536b236af36a6b69e36903682367436663658364fb64cb649b636362db61fb611b5f8b5eab5dcb5ceb5c0b5b2b5a4b59c3593b590b58db58ab5823579b560b54d3544b536b528b51ab50cb4feb4f0b4e2b4da34cc34be34b5b4a7b499b491348e348b347d3474b471b46934503442343f343c34393430b428341fb40c33f333e533e233d9b3cbb3bdb3afb3a1b38e3385b377b36433563348333a3337332eb31b330d3304b2f6b2e8b2e032d232cf32c6b2b8b2b5b2ad32943280b272b264b256b248b2403237b234b22c32293226321832153212320f320c32093200b1fdb1f531f231ef31e131d331cab1c231bf31b6b1b3b1ab31a2b19a31973194318bb183317ab1723169b1613158b15031373123b11b3112b10a3101b0f930f0b0d7b0c9b0c130b8b0b030a7b09f3086307db075306cb064305bb042b034b0213018b00ab0022ff42fdb2fd2afca2fbc2fae2f9aaf8caf7eaf70af682f5a2f51af43af35af27af19af062ef82eea2edc2ec8aeb52ea1ae8e2e85ae7d2e5eae4b2e42ae3a2e31ae23ae20ae182e0fae0cae042e012df8adf02de22dceadcbadc32dbaadb22da42d962d8dad852d7cad6ead662d5dad4fad472d3ead30ad1d2d14ad06acf8acf5aced2ce4acdc2cd3acc5acb7acaf2ca12c98ac8aac7cac6eac60ac52ac4fac4cac49ac412c282c1a2c172c03abf02be22b) else (0x1380f400523a45c8989181f400607663a03d00104890f31d400407e0b411a1701f23886307d0a81341960f90a00f91d224838c2d85902d054a9a0ec0c80fa1a80142e05b02d04705c4940c809a0e80142d81541d12243d46c0ca09a0a80142c816c1712501e025001c5a0b205424544c07a00383182e24848a8580940071640b41511d21881c616c0b41521d41841ec30e2d81682343a45d06104b0640b41640b48ba0720830b816c0a90e89141f23506304b0450b205483e44a07145a11d22e44e07c07181a8341640a808a0980f400806224808c0f40b012800e0c40909181e814825001c1789122043e860a2d88b913c1e20b622e44f07c0c145b11722783d060a0640a10fa19216024821c0f01902924607904904383d81ea0b00080ec1501980ea0b000c0f40e81702683e410c0ec0e81702681e410c0740b81502804c8810850440700140f80a10f51301d410c0f80a10fa18a16022821c11c0f408a0f000a08c0bc07408a0f000c0f40e81341f012418c0ec0e81340f012418c0fc1689221ea2b0440750a01141940fc87d0750a011418c0740988580920c586f0770860fc1828b822f84307e0c608303b03a05c09c8e40e301d02e04c48c0f91c303d16c45c89a1041ea3b06100e98810f90b010507c45e48c0f50a410607f05e4940f50b010605a0a90e90f419821038f05d0a40f90b013000c0fc1f03a06305e8810f50b010903305c0a29141f216020e2b0548a683ac4087c0c80e401902944207a85408304104644d07a0c600304016883d03b001619e0fc1181c4c1ea2704607121be10c1f8304c118102c1f8102c1f81c2c1f8302c080e040416b0fc08182a046c3cc5e88c0fa1b82e04e07c00b17085c4910c60ea15022836004814122c3d0668b112c1c429041045014122c3c4690c112c1d02683104503f17085c4941001e43183e85409a0cb0262470788dc1822703885408208a0262470788dc1822503885c08208a0262470788d41822703885c08208a0262450788dc1822703885c08208a05408f44607d0dc1702703e004ca5e4a55ca3cca23ca0ac9f749e949e0c9c7c9aec995c97cc963c9504942492ec920c912c8ff48f148e348cfc8c1c8ae48a5c89d4894c886c883c875c872c86a485c4853c835481c4813c80b47f7c7e447d647c847ba479bc78dc78547774769475b4752c74a4741c73947204701c6f3c6e5c6e2c6cf46c6c6c3c6bb46b2c6afc6a746994690c688467fc6774663c65b4652c63f462bc61dc60a45f6c5e8c5dac5ccc5c445b645adc59fc591c57e4575c572c56fc5674564455bc558c54ac5374529451b4512c50a44fc44ee44e044d7c4cf44c6c4b8c4b044a7c4944480c472c45f44464432c41f441143fdc3e4c3d6c3c8c3bac3a74393c385c372435ec350c342c33a4337432ec320c312c304c2fc42))) else (if j<12 then (if j<11 then (0x60ea1502283281891412503d028a0c448c0f40a41051640b48798e514a1a020e2c81510f31ca25430c2c889c0f91c821435041c1a83316444e07c8e41001d43120d45902a03245108c071c5901922903d048a0d41509181e824838c2d01509131c2250420750d208916c45c89c9181f03283d04a0048b622e44e07c8e51aa2e83d04245b01d22724607d07a0838b483263906489a1101f001105cc911031c83242c04c0040b605a0a813aa603a43cc728bd1301f43504345b02d0460860b90f31ca2e83e85809a0cc16c0a80e90f31ca3545d07a09a08a42e84c87e89c1081f43304205c21321ec1f42a04d063a1742624487b07609a08742643cc7689c1081f43304205c21742643cc7307d0a81341920bd0989121e63983b04d04410fd1281f43304d0430b842e43d83e85409a0f41102d81181d22703e4728d51741e82140dc5b02303a87089c0f91ca340628ba0f41180d003c5b11722724607c0ca0f410816c24a0820450628b8124440c750ce0ea1502283245c03042e24a0840f91c81141920f40b81312303d410c0ec0e81702622603a821c0e81312503d02283181a82a03244c44a0800f41241120d41501422303d04a0750c403b1640740b81321e63a039005c0989121e638506a0c48989142003e410e0d40f01422243d04c071c1881e0320508890f40b01080620640a11112043c606a0a80c81422263904c07201881422243cc720580838350628540a11312304207c8e241791312284107a8e90438350620bc8989102083d47482241a83102a8508989182103e4728228188232262490800f80920c80624504940f91c814020e0c41181742c44c4941081f238021408c0b91312484107a8e80920c906208c0b91312404107a8e80920ca06208c0b81622624a0840f91c81141960d41511442203e04c0790c40350662c889c0f91c82003d04260788d112214410a24446c0710a208523a45c8989181f400623a45c8988980f40060740524890f40920860740a81181491a43102683904482a03c8750a09121e2350630460050b40542448788940ec00706285c4890f10a811800e0a85202342e2348658b10a81341b002c1501942e8504490710a811801208c0b88520860e800c0e90a49221e214024831c1d02a42922a8410710a01241e82285c02d0462810b89221e831023002816a1712443c45207408c00806285c4910f10a811800e0a85202314085c86085408c00905485c45107b0c215026826004814122c3d0668b112c1c4288260050350682c81521181e02603d00241501911402603c8640b01181500281a8b205503d0480760438ac1522980e90f91782103900a90a51021e43142a041d0a51021e43142a041a0cc1782883d0648580980080282458788d112c1d02683104c00a0540901182011b03245a05208c0e80164748b9) else (0x6832241421214222781c20672242000000c0e08310418820c41c180e070703820023c0e1489064482000000060f070202001830150b8102c080e0f040c0a0800607040c1e0e0f0418e070811a850b0382001810160808183c190a0c31c0816040400000000011a8d0a468381c100002886040a84507c081d08a0e150850b8103a1e0d0fa181604040000000851833038707f060508e0de040e0d6070a0c6040800008318102000000000000866c10285ec102834c1026080c37c181433c0e1430c08141bc081000c41c180e0407020381c100000083141020244e0708043581c2028602022fa08121aa0810b4066122a846122a8461423041a820c418460c230499e040899d07080c180e040702020cc106e88c206608370419834301a180808ce82048be82048cd87e070c00114607090fb0c08046e88d860600086983840233a08121aa08123360e100c218384c10144686d8206861820541c150a0a306081223436c103000c180a1ac0e100022fa08121aa0810000143f038543c1030403810103020200000000000141c150a080000000060c07060383018540c230400000000000000000000000142020000014301a180a3104001154230a18c2a0a18c230918c230a18834301a180d0c0400118820000000604051182022a040a080c3106820200002230404620d0706838288c10282020604040608082302e44e86085507208706208c0ba1682844e86085008a0e411724487b0710a81141c821c1502391a43183885408a0e411208c0c01722741c42c04906a08906208c0c01742a44e8388580920d41168524910f61821641a821c1501902e8518648a20e21641a82281501922622504286a09208806a0a80cc142262250400750d208a1680a80ca1421e2264328220118172262290428690b012419208c0b9131148214348580920d80940b48788a81121942a04506402a0324504540790c81581100c41281822a22a0448640aa0d815012d0ba1312303e06282c003a1481e23606604505800705408c0f01d22623545d04904482a0460780ea1c82844c4680c51741241180a811a1742843c8658b50a811413002d0a10f218a2503a826003a1742843c86285408a0980100a80f01d42843c4680c916c11413002c1502342e43c8630750a81141b00290b90f218c1d42a04506c00805a08c108a042e43e45a04506c00a05408c46c0c916814823032089891420a3a410a0a84890f31ca2603a821c4890f31d43142c0450438350630508989142003d47482241791312303e47282181a83105e8548989181f23941122d01501942824647107504402302e44c4921051d01241900b40b89221e6394540750aa0c912443cc750750aa0c606208c89892420a3a02483201181722624a07c8e506383102e8588989281f23802283241682342e24a4710c)) else (if j<13 then (0x8080060404020f410202020222a038482015100a85040510080001d42e101dc08101dc0e101dc081000507040ee070a09820008101009b90f0902020413060982000a4b0204a441000c080a92c081415828109142083c340808081c194cc002621216020705e428506282054101a200913a1e103f07c0e818881041090c808204105407886080840f10c0c2002d20e184003241c305a0a80c907101f83e0740c4407e0f81d031111450f090fd0f0811a1b02f43c443543c243005e87868be820486a82040f81d4040e8203410145143c243e0a1b050d02a44860441c1227840820744142844754884a4a8404a468405421428445d48844314284810102428247608054201a10a142261214261e0b0f05878205d87e08208241802ec3c3076c3f0406c3c1076c3c207604d87d08101d81361f420461e0b0f0409b0f0a0c01361e180000830120e0c33512101aa1e1018a1e1018924130f9141433040028410710a1a07050b9070a1bb04080c01710aa0c403141c203743c203143c206341c2036820203124429120905040000a1e0a19041d81a112a184076420c3074101210618203743c203543c203743c2210a142a1e4202a1e420250a090850a1117410120806492080a48a0809040200084f038543c102878207c0e88d516241b61810000143c1a1e081d049b81dc08193703a85e87880e4118400a4050d50f090c50f081450f080fd0f080fd0f8181b0f07045040a0c30fa081e08c0e1508c081508a0e100c3c1830c3f0206291428407c103f244203e4402c0e0d0fa1810104c183b03020203820f41789151c203d220638383f43022206382220a14282a4442a1e0d0f040208080003152010000000143c101450200143d450543d4484a141a0e080c3c1018782c3c161e080030f058782a241a1e0a8a058782c3c1608083a03005d41880e8829830e838343c1a1e0a8906838286410760680ca86101d9860a820343c150a0d0f06490207c0f01d516230c05860343c1a1e0c91041f03d05ea38407a638207c444c707430181f2342c080d08c08103b5232268408a341c08083d512151050a150850a810350a8102a218102a118102c080c0f91a160406532070a5320c0909c89081f831089b82391a1933c081133912113090a1023237214307b23606060f409c890c1eb1090a1c850642820ec09c91512c205076c2242864dc1266091b060c1920802080c180400300818201c200d10c18150850b810303020383c1c1e0818c1e102fc0816040704038401c1101c2c180e100688607094282c401060a14204606d4286a141036a14203181c203028381018100c0806043040b07c080b0202a25040583c14112142410a1820678102066a24206781020000304030de0ee0f6082437c1e1000dc0e9170c1b82351a183751a1307040000c1ea342024) else (0x48c0f5041a13041f01421f010407405207904104888d818a08443005e0206062078501c122643d44a071089a9141e4304226a45079071089a9141e4104226a2503904128828d4181a8940e101750a810323aa44252283c2a10a15020645d488445d448443142a040d42a040ac928d4181a89054882a441a20830202842040804080c133061213050998aa1101c428a44d4560880e2113048982248452830d0a40f008181781e101750a140710a1017a20a2903a04140ba8509490241d4284431428441d428464813240992049082060c5107208269131441c42904140c1070a88207080a1041d428721410102828141008203228838406010300d0c040c0206283c040e8382814103141e020703c846040e07908080bc8580818174110103512820290b410290b010290a0908c08140405044040a42d04088988900e190904001040204050408108102115022038724904044214284a141608090850a14924101405a0813070544020641a0e41024280c91060628940e1c0c50a8103427244242703c46861040f219428213703b244304e8654486085428504e44c070e09b1090b01048290102913420282f214283043e82060760788d0c0ea8d0810c858081a8d90b410303b03c203aa342922080234111b810211b810243181022420c3783ac10302862850a428286142850de0e84028941010b2226141321e6383226083d0460750e113141e8b4226820402f010290a0a0c90b010390a091321881c3226a464690c1089a9191241c4226a4642904105b0b294c431038a2d8594a620e20b2124410316c2464686474123aa4425248102523224222ea464286074860507c8790c0c5c10cd0a810405f07c860684c83a040d09c8920e1a1720e10b420e10b420e110704c910408c9026488204a4415232142000408091312203c302881602068540a413222240878c4441000c911080014902001422624607880be41040bc8989142083c505e44c4881041e29100488285094282068102a44c48c1081e28152290444840f150282a2a0384448820441010148c05088a09281e010422081022200d0c50a81032208102000514822020644e078070d0402420190a08044146840bcc7040dc8ee040cc6e040a846040a83e040a0c192a081a8da0815040703820a08e840ec107a08130507c07c081a0f80e10178081604064283216820404c1000ea07081d8241c1028382a34150a810200000050b8102a0f810250b8102514080810100000000001490381c10283c0408150208c10242c040a0202a290384000001810100000090b410290b4102c)))))
def genIndex7 (j : Nat) : Nat := if 3 ≤ j then 0 else (if j<1 then (0x865e8287800f0006801efc70e4f001e003c004207d0bbe003c0078009201e003c007130f000a7ebcf79936b24be003c003965c2a9b717c00081ff001e0018437800b9f6249fcea1caef001e003c00418300dad63bc007800f000e154a4778006004a3efc0001994188c3e4e2bc86cf001e003c007800c18098f5014c17ef108690bc007800f001090e88e7800f001e00389990cd00ec73ea2e9613d538c8253c005048010b76bfc007800f0012663c007800f000c87bc007800e2cc319504b1c8aa375c7efc00621bb03d43770770113d0cb530020cedf18ca5e003726f23af001e003c007800f001640942bf8006131e001854f800f001e00106a49dc8b8de003c0001d99483e0038d6c5384be8d23fc000c4af000f577c001a11d193455f6c8509b83a03930eecd9ea49fe80104f001a8e0c7e8fc076f800f001e0008c27800b280a45b409f800621285a6b2c4174010268afc007800f0010317c00624822cf457d035780030c8d6fec67780084bbe0030407800ac4a641bc007800344928cfc002079f001e003c007800a4b1a85cecd71f7f001e003d16257702dfe002a01f800f298095a2527800f000c6490cf499f63f285f2ac8e53bf001e001b22c883f3fb8763c007800f0008267c007800f001533fc004182f000365a901314ef071e003869497bf0000443c00780001f157bdc4be43489fa48c6443a53af001a1f7ea120006ab9e003c007800c4a9e6a5aac2061d177e003082a158f001220a69b19a7f001451bc00292b41a3374d87eccaff000c946886780073cde0024c678000337e00287478000171e001c897800f000c94bc007800f001e00088fb4d1d2ba8699c290d41e2e5e697c00419d60eb4035c68709db3c33971125780033a3e926ad6092874b9111e883f800995a05abd1dda08c111e0014d1191121eb28f10393117f001472a0a878002079e003c007800bb8ee164703f8b7841fe0039135091d1cae835400b16e01693627c0078009031e00271d68a572bd906d01651ac53afe000c19d4ebfb9e63c3c00315c7b642545695910ba06fa1c3c0078008440068fc0029a4cad9c2c3c000a30f000e3630c348478386c4218c559b4525c495fc000dd0f001e003c004131f001673d91ab180b119e0008f6f800b13fe003c0040b934b7e00210cf800f00120fe6657800f00000590651044ab7de003c007800f000c30fc002071f14327d7c0064cc5030d93a23141400420911001020880ca1c221bd0904510300461d0ea2004c008f00004038208810c1c709904574208344009104914829a5405091cd0c008144500200304018048a0400001970010810800452800432c00450020c20010c00460c220300210400208004000120008c20310034008100309a1811813a21c13421c304144a0060020c90010412c0198000880081000) else (if j<2 then (0x503bf0016930808c17173f1e00087b78004061637309fd5cc515ec564cc4f8004481e000e52f800399ab901a851232f001c437c001d23b06d604bc1ce11af08cb77bcd0313a5c73633c11199e233bc809906b7800ea5201a7d067800d36ea0bbc25c9524191810789cb13e9996c703c0059f3200b43dfc00552ef001741a108024e12797867c0078007178c033c007800f000c6424c0d0c26473e003c007800f46de003c00780060e667b3c000e33f001d947435f800f001e0014337800f001762d80e78005a5860d711ef800025fe003e9cf800f001e000901962991ae349e916f8005417e0018a2ad3ef3ba8307c006135e9c5e003c00780000d047a70a1f800d007812510e45f6d277c6bd8f80206516ba08bc0035eef00097350b9cdfe8c8942fea7f3d86a2fb674bc007800f001e003c00304d5b3b434c87f780063c6c8d2addca3701f4a31f0bc5e2e616d2093c0021c2f001472c03b91c4c4b3e001877f80060fe60afc00525af001e003c0070ebf0000717ad0f80050dfe003c003806f001e4abc007985f001e00204f7247b409e001c9c0179204fe0012da01bf914fe003c00780083fde003c007800e31da332412f800f001e003c007800f00061394f27800db9d816ecf3c8e701be403ca6b84404abde00308c29aaf001e003c000929f00106724a17800a425e003c0078001c7d315881d408a8a9d462e044f800f327e003c0000ead04380c4ef87800f0c5e003c00600ac07de00091c5921f001f822e6278d5d292558f00df800a14dc7d8cb5f4b1f000a23b42c103d301742814a0a1b0c36a611600a88ecf000446fc007053537d68fb31aac05f0f9e00247a5093fc59e0028f978006162c3f26fac814c39b1360aa3915b4120935603df800f001e002c8eda4543ade003c00708ff001e003c003a55e0f5e003c004e3f70ce416b47002095154d6e3c007800f2ffe003c006c794379828a804ee28f001e00285d78008135e00180d509cf147e003c00004cf2dbe003c007170f1c605824f8f800f001e00286d0db3f001876cc78e05c829fe00050efdcaf000e43bc0049876c5ae6e32377800d2ea98dfc007800f00115cfc0028f342ad272281a39fff000f893c00780091660520896f92cf0010725e5c7800a83967d08d9f800e055e000a00e43c32c7e003c0038e64011e001c370a539046f22ce22780083f8c01ec65ca46b2c3e0026e4c545236c85a3f2cd57cf000b5480910924e095837ace768ac915044d18dd997a842a605ef237800b209c66bc001244f001e002ca5b53c33ab40816d4e854f000d3b7c0078002033e001a68782fd149e00090c7800f001e256c207800f001e00331e7800743fe0001151a50629b238bc005c7a9453a84fc007800d45fc0a3caaae26524c276850d002df00023fe4d58188e18de003c007800d0f1) else (0x156dbc00607ef001e003c000631f000c8bbc00490100bca17fc007800037be0000ad643bb17c82afc0008b2e21f288486db994409fe001aab29a1d415996bc000119c0c1e003c004c3564290657911064ef001e003846f8001117e000a750e41a3d1e000902894492c8d107c007800f00166e78a51d5ff0010647c007800f000877ccd8f80022d9e5ddcd960e910a3092f48ad9033ac8c93f6690c3f132d610881921c13a4be002c56a9234214a51f48f7800f000e10d9147800d41da45085739c7ab3c87b83037800a95734758076227f001e0032767800f001e003c0038d9f00124dfc0059321b6be00261b7800f001b423c002874f0004897c000c9211c3e001e25bcc1849bc63480839ebf00173e4a03897668a1e0024f2f920f00148070d779d381e5e003c007800f12422f710b78007a4972b0ca9c18f8399258b6c6501df000215bc00)))
def genData8 (j : Nat) : Nat := if 17 ≤ j then 0 else (if j<8 then (if j<4 then (if j<2 then (if j<1 then (0xd8350930bbd844c941bbd844c940b7d858c910b7d854c9509ff865d1109ff865cd209ff865c9109ff855d9209ff855d9109ff855d1109ff855cd209ff855c9109ff845d9209ff845d9109ff845cd209ff845c9109ff835d9209ff835d9109ff835d1109ff835c9109ff825d9309ff825d9109ff825d1109ff815d9309ff815d9209ff815d1329ff815cd209ff805d1329fe87989109fe87985209fe87909109fe878c5209fe87591109fe8758d209fe87589109fe87585209fe87509109fe874c5209fd87989109fd87985209fd87949109fd87945209fd87909109fd87905209fd878c9109fd878c5209fd87595109fd87591209fd87591109fd8758d209fd8758d109fd87589109fd87551109fd8754d209fd87549109fd8750d219fd8750d209fd8750d109fd87509109fd874c9109fd87486609fd87486509fd87486409fd87486309fd87409109fd86dd5209fd86dd5109fd86dd1209fd86dd1109fd86dcd209fd86dcd109fd86dc9109fd86dc5209fd84dd9109fd84dd5109fd84dcd109fd84dc9109fd83dd9209fd83dd5209fd83dd1209fd83dc5209fd82dd9109fd82dd5109fd82dd1109fd82dcd109fd81dd9209fd81dd5209fd81dd1209fd81dcd209fd80dd9219fd80dd5219fd80dd1219fd80dcd21fe22740910fe12098910fe12094910fe12090910fe1208c910fe12058910fe12054910fe12050910fe1204c910fe02740910fd23740d10fd13058d10fd13054d10fd13050d10fd1304c910fa94241120f726540d10f726540910f716540910f595341530f395441540ef26741910ef16059510ef16059110ef16058d10ef16058910ee96241920ed96341930e756558d10de7729c910de62784910bf38640910bf38340910bf3805d510bf3805cd10bf3805c910bf38055110bf287c0d10bf287c0910bf28740d10bf28740910bf281c0d10bf281c0910bf28084910bf2801c910bf28004910bf183dc110bf182dc110bf182c1910bf182c0d10bf181c1920bf181c1120bf1809c910bf18098910bf18094910bf18090910bf1808c910bf18080910bf18058d10bf18058910bf1804c910bf08740910bd68394b10bd68394910bd6831c910bd68304910bd58394b10bd58394910bd5831c910bd58304910bcd83c9520bb6841c910bb68404910bb5841c910bb58404910b76858cb10b76858c910b76851c910b768504910b75858cb10b75858c910b75851c910b758504910b6d85c8d20af6861c910af68604910af5861c910af586049109fa801cd519f9801cd519f887409109f687849109f6811c1219f5815c0219f487455319f487449109ee821cd519ed821cd519de831c9109dd831c9109be849c5509be841c9109bd849c5509bd841c91097f855d13097e851c91097d851c91097c855d1308fe861c9108fd861c910e716059510) else (0x6dc520df9065d130df9065d120df9065d110df9065cd20df9065cd10df9065c910df7765d110df7765c910df77645110df77644910df7755d110df77545110df7745c910df77444910df7705c910df7165c910df7145c910df5825c660df5825c650df5825c640df5825c630df5825c620df576dd110df576dcd10df576dc910df5765d110df5765cd10df5765c910df57645110df57644d10df57644910df5755d110df57545110df574dc910df5745c910df57444910df51748660df51748650df51748640df51748630df51748620df516dd110df516dcd10df516dc910df5165d110df5165cd10df5165c910df5155d110df514dc910df5145c910def7648d20def7548d20ded7649120ded7648d20ded7548d20ded2798910ded278c910ded2758910ded274c910ded2744a10ded2740b10ded26dd120ded26dcd20ded26dc520ded265d120ded265cd20ded255cd20ded23dc520dde3750d10ddd764c930ddd744c931ddd744c930ddd3758d20ddd3758d10ddd3750d20ddd374c910dbe4750d20dbd4759110dbd4750d10dbd4750910d7e655d110d7e655c910d7d7655350d7d5754910cfd6758d10cfd6758910bfb8640910bfb8340910bf982c1910bf982c0d10bf981c1920bf981c1120bf98098910bf98098520bf98094910bf98094520bf98090910bf98090520bf9808c910bf9808c520bf98088520bf98084910bf98080910bf98059120bf98058d10bf98058910bf9804c910bf78759510bf78759110bf7865d110bf7865c910bf78644910bf7855d910bf7855d110bf7855c910bf78559110bf78544910bf7845d910bf7845c910bf78459510bf78444910bf7835d910bf7835d110bf7835c910bf78359510bf78359110bf78344910bf7825d910bf7825d110bf78259510bf78259110bf78159510bf78159110bf7805c910bf68798910bf68790910bf68759110bf68758910bf68750910bf58798910bf58794910bf58790910bf5878c910bf58759510bf58759110bf58758d10bf58758910bf58755110bf58754910bf58750d10bf58750910bf5874c910bf58740910bf586dd510bf586dd110bf586dcd10bf586dc910bf58655110bf58654d10bf58654910bf58650f10bf58650d10bf58650910bf5864c910bf5854c910bf584dd910bf584dd510bf584dcd10bf584dc910bf5844cb10bf5844c910bf582dd910bf582dd510bf582dd110bf582dcd10bf582dc110bf582c5910bf582c5510bf582c5110bf582c4d10bf58198910bf58194910bf58190910bf5818c910bf58184910bf58180910bf58159510bf58159110bf58158d10bf58158910bf58155110bf58154910bf58150d10bf58150910bf5814c910bf580c5121bf48759110bed8259120bed8258d20bed8254d20bed8250d20bdd8394910bdd8358930bdd8354930bd)) else (if j<3 then (0xc520bfd8654910bfd8650d20bfd8650d10bfd8548560bfd844c960bfd844c910bfd844c560bfd844c520bfd8448530bfd8348540ff3805c910ff37640910ff37540910ff37440910ff37340910ff3705c910ff31640910ff31540910ff31440910ff31340910ff3065c910ff30644910ff3035c910ff30344910ff28740910ff22740910ff22140910ff20740910ff18640910ff18340910ff17640d10ff17640910ff17540910ff17440d10ff17440910ff17340910ff16540d10ff16540910ff16440d10ff16440910ff16340910ff15340910ff14340910ff127c0910ff12740910ff121c0910ff12140910ff11640d10ff11640910ff11540910ff11440d10ff11440910ff11340910ff106dd510ff106dd110ff106dcd10ff106dc910ff1065d510ff1065d110ff1065cd10ff1065c910ff10655110ff10654d10ff10654910ff10650d10ff10650910ff1064c910ff10645510ff10645110ff10644d10ff10644910ff1035c910ff10358910ff10354910ff10350910ff10344910fe92641120fe92098910fe92094910fe92090910fe9208c910fe92058910fe92054910fe92050910fe9204c910fe90649520fe90649120fe90648d20fe90448d20fe52798910fe5278c910fe52758910fe5274c910fe52740b10fe52650910fe5264c910fe5254c910fe52198910fe5218c910fe52158910fe5214c910fe51448d21fd93058d10fd93050d10fd9304c910fd9064d530fd9064d130fd9064c930fd9054c930fd63750d10fd53758d10fd5374c910fd53650f10fd53650d10fd5364c910fd5344cb10fd5344c910fd53158d10fd5314c910fcd3258d20fcd3250d21fcd3250d20fcd324c520fcd2358930fcd2354930fcd2348530fb94059120fb94050d20fb90651540fb90650d40fb90650940fb54759110fb54750d10fb54750910fb54650f10fb54650d10fb54650910fb54159110fb54150d21fb54150d10fb54150910fad4259120fad4250520fad2458940f9d4350530f9d344c941f9d344c940f7a6540910f795054930f768759510f76655d110f76655c910f76654c910f766545110f766544910f765759510f758759510f7565dd110f7565dcd10f7565dc910f75655d110f75655cd10f75655c910f756550910f75654c910f755759510f755754910f755655110f755654d10f755654910f755159510f755154910f748759510f6d5254520f6d254c950ef96059510ef96059120ef96059110ef96058d20ef96058d10ef96058940ef96058930ef96058910ef56758d10ef56758910ef56559110ef56558d10ef56458910ef56158d10ef56158910eed6258520edd6358530dfb7640910dfb7440910dfb065c910df97641120df97640d10df97640910df97440910df906dd120df906dd110df906dcd20df906dcd10df906dc910df90) else (0x10ff77650910ff77559110ff77558910ff77458910ff77358910ff77350910ff68759110ff58759510ff58759110ff5865d110ff5865c910ff5855d910ff5855d110ff5855c910ff58559110ff5845d910ff5845c910ff58459510ff5835d910ff5835d110ff5835c910ff58359110ff5825d910ff5825d110ff58259510ff58044910ff5765d110ff5765c910ff57655110ff57654910ff57650d10ff57650910ff5764c910ff57645110ff57644910ff57559110ff57558910ff5745c910ff57458d10ff57458910ff5744c910ff57444910ff57358910ff57350910ff5655d110ff5655c910ff5654c910ff56544910ff564dcd10ff564dc910ff5645cd10ff5645c910ff5644c910ff56444d10ff5635c910ff56354910ff56350910ff55358910ff5435c910ff54358910ff54344910ff51798520ff51758520ff5165d110ff5165c910ff51655110ff51654910ff51650d10ff51650550ff51650530ff5164c540ff51648550ff51559110ff51558910ff51550560ff5145c910ff51458d10ff5144c910ff51448530ff51350910fed7648d20fed2798910fed2758910fed265cd20fed265c520fed2654d20fed2654520fed2650d20fed2650930fed264c940fed2558d20fed2558520fed2458d20fed244c520fed235c520fed2350520fed2348540fdd3758d20fdd3650d20fdd3650d10fdd3650930fdd3650530fdd3558930fdd3458930fdd3458530fdd344c960fdd344c910fdd3448530fdd3250530fdd324c540fbd4759110fbd4750910fbd4650d20fbd4650d10fbd4558540fbd4358540fbd4350560fbd4350520fbd4348540fbd4250530fbd424c540f7d5654910efd6758910dff865c910dff855c910dff845c910dff835c910dff7559110dff7558d20dff7558910dff7558520dff7458d20dff744c520dff7350910dfd865d110dfd865cd20dfd865c910dfd855d920dfd855d910dfd855d110dfd855cd20dfd855c910dfd845d920dfd845d910dfd845cd20dfd845c910dfd835d920dfd835d910dfd835d110dfd835c910dfd825d930dfd825d910dfd825d110dfd815d930dfd815d920dfd815d132dfd815cd20dfd805d132dfd765d110dfd765cd20dfd765c910dfd765c520dfd7655110dfd7654d20dfd7654910dfd7654520dfd7650d20dfd7650d10dfd7650930dfd7650530dfd7559110dfd7558d20dfd7558930dfd7558910dfd7558540dfd7558520dfd745c910dfd7458d20dfd7458d10dfd7458930dfd7458530dfd744c910dfd744c520dfd7448530dfd735c520dfd7350910dfd7350520dfd655c910dfd64dcd10dfd645cd10dfd435c910bff865c910bff865c520bff845c910bff835c520bfd8798910bfd8798520bfd8790910bfd878c520bfd8759110bfd8758d20bfd8758910bfd8758520bfd8750910bfd874))) else (if j<6 then (if j<5 then (0x817914bc165ddb2ed3175c4ba825d072e6917274b8bc5c2e2dff16f38b73c5b732d9c96c38b5c65aae2d3f1694cb43259df2cd2965acb25858f72c611620cb09c58192bf215ebcaefe57452b8a95b94ad5656712b1b957e0ab7c557f2aa295440a9b654a12a31150b4a7f053c329c214d50a64852f9296494a78a4d2523928ff94714a320515b288e1439ca16e507d2821940249fbc4fa427b513cd49dec4ead273e939209c264de326cd135309a1a4cd3264c9317c98364be625d112da096484ae52550929b0947849f824e412660929e4906245e921f89092481423ef91e808ec2471d237191a7c8cc0462b22fb116c88ae64534227a912ec88e4442e21f510ed486f64332217c10ae485084254210a9076c834c4171209e10408819a4093202f1007c7fd43fb01fc28fd187e2c3ed21f510f9dc7c8e3e081ee20f6147a823cf81e550f1ac784e3be81dd70edd0764c3ae21d4f0e97c743639d21cc70e528722038d11c4b8e188703237d01bc38dcf86dfe36c01b408d9086bfc35ce1ac28d5186a0434c31a3d0d0d867d033a919b28ccac65ce32b219438c920641231cf18d20c5a8626030f618608c21c609a301317ec8be7c5eca2f2b17760bab45cdc2e2f16fa8b6ec5b022d4716840b338591e2c5516088af34571c2b4a15858ab1c551a2a4915028a7185304294314820a314510c2847140409f244f142750138889b484d262659130d097804b4225671299093cc4972247a121d890184798239211a988c6445c822aa113a888ec440c21d110c90854c421e20cb10438810c3ffe1fbb0fbb87ce03df21eb50f3b078c83be61daf0eb30749c39bc1c9f0e2b07048379c1b850d9e06bcc35541a610d13867c8337019830ca4864143178187d0c1a05fe82f94178b0ba105be42d7e167b0b16857402b1815430a7d0531428ee143309fa04ed426ce1323097484abc24e0122208f184654229810ef0853041d82096101107e683e601ed00f42078e03bd81d5a0e5a0712837d41b800d8b06a88345c19b00c9e062f830e417ea0bac05b682ccc15d40ab0053b028f013e609b904bf82514121608d1044b82174104607da03d001d980e5806e80359819e40c7e060502e5816440aae051d026c8129008d40444020f00fe0079003a201b400ccc05de02a60136008c803f001af00bf804ec01e400ae0037800980000ff98640910ff98340910ff98140910ff97640910ff97440910ff96540910ff96440d10ff94340910ff9065d110ff9065cd20ff9065c910ff9065c520ff90655110ff90654d20ff90654930ff90654910ff90654540ff90654520ff90650d20ff90650d10ff90650930ff90650530ff9064c940ff9064c540ff90558930ff90558540ff90458d20ff9044c520ff90350910ff7865c910ff7855c910ff7845c910ff7835c910ff7805c9) else (0xe0841603801c1504787a18c5c154440f4360b02607801a87b1c46e1844e118390b8210580e00602648a208791b861138460e42e0841603801c4881e4701883a08800f48aea43b52122902147d8a3d551e1a8e9d4716a36f51a728cb54636a30e5180a8ba945c4a2da516428a9d4534a2925142a89f544e0a268512da894d4478a2205107287dd43c0a1c950d6a866d42fea16350a1284994232a0f35069282b14120a065501fa808d40049fdc4fe027e7d3ef29f4e4f9927c593df49ede4f6127aad3cf69e504f1f278b13c209dfe4ef1276f13b2c9d894eb92751d3a609d144e7ea735d39769ca94e4ba721538dc9c524e1da707d381a9bfb4df226f2137629b9a4dc426dd936be9b434d93a6c2d35ca9abf4d4ca6a0934e09a544d21268c134469a1b4d02267b533c099bf4cd4266453308996d4ca8a64d5321e98f34c6926315317a98ab4c4f2621d30e098634c2b26139306498254c09a5fc92fb697ba4bd6a5e952f30977c4bb2a5d4d2e6e97254b8725bf12dc096c44b5425a452d1296724b32a594d2c78962f4b13a58412be895d84ae5a56e52b4e95904abf255752aa0953e4a98a546929e894d34a5ba524528d6944a4a14a503527d893c649d024e1126c69342498e24c0125be92c34953a4a0524c0923f4911a47f523ae91b648caa45d122d8916448aba45292266911c4887a441d21f490ed487024325217890af4847241f120ca90494819240812026900147f023f4d1f968fb947d123e411efc8f5d479e23c811e088eed476b23afd1d508e8c473d2398d1c988e35470f238311bf48de846eda37111b648d9b46c7236051ae88d35467b232dd18e68c3e45faa2ec516da8b294572a2aad14ce8a3244f9a26bd12ea89314480a22f510f2883543fda1edd0ee6872f437aa1a9d0cb2861a42e8a16350a7e84f142632121d08ae841341e7a0e19066682ef4150a094d043281da40d020585024480e84054a01bd00427fd83fcc9fd54fe367ee13f4e9f978fc2a7dcc3ec69f538fa007cbc3e371f10cf7fe7bc03dbe1ecf4f5f27ab03d339e88cf3e679c83cce9e5a0f26678fe3c6c1e28cf0e678433c071df50ef3e776a3b9a9dbc4ed6e766e3b129d798eb6c758b3ab29d4d4ea0a74d03a4d9d15ce83073e339d21cda8e65672e739591c9cce47271ff38e79c668e2c0712638761c2f0e122706b381d9c018dfac6f9737b11bcb4dde66eb937421b93cdc2a6de036da9b628dab46d2a36691b288d8da6c2935f01ae5cd6926af6355b9aa08d4906a0e34ea1a690d2ca6930347d9a2f0d0f0684333fa99e9ccec66715336b19a70ccc4663232ef99694cac26536327699308c938645d32169901cc786637a31a298c40c5c062b5314798968c43661dc30d3985c8c27a60fe306998264c0d26039300217f50bf5c5f7e2fa497c78bdc85eaa2f3)) else (if j<7 then (0xf42a094120091585494c1183a8781945d130400f43208801c0c0260781803d0a0250600120a826078180380941000403009a2107c188440f4280941a02582e0a8268841f46c188440f42c094120268300981e0600f4280941a0200140a826078180380941202001209a1e8620e82104800e09a1e8620e82104800e87a1883a0841002800e0c02e0b0260841f0601103b0a0230600c00703a0c02e0a8260841ec6c180440ec2c08c10030020099230801f4701803808c10005026078180390a02506c100048270892007d1c0600e0260400140981e064124400f4300981000502648a1e46a1844a0e42a08412005c2007d1c46a1844a0e42a0841200582a0a12287819459128390a82104801848a1e46a190400f4310a8210480160a82848a1e46a1844a0e02506412006026078180380841000387e168460b9250801f4721883d0a02506687c1502848c2007d1d46a1944a0f42a09411c1d0541182e0a21e8620e4280941d0461230791b061130390b0210480c00582a48e2187c19459138460e8230641603801c0a92387c194591383a08c19058016099238791b8611383a08c190580160861e46e180460e823064100380160a9238861f0651644e118390a8210580e00702a48e1f0651644e0e42a0841600582648e1e46e1844e0e42a084160058218791b860118390a8210400e00582808e1f0651604e0e02a080160059238791b8621083b0c42e084160058218791b8620ec310b8210400e00582648e1e46e1844a0e42e084160058218791b860108390b8210400e00582a48e2187a18c59138460f0250641603801c0a92387a18c591383c094190580160992387a18c59138390b8210580160861e863160460e42e084100380160a9238861e469138460f0250641603801a0a9238791a44e0f0250641600502648e1e46a1844e0e42e084160058218791a860118390b8210400e00582808e1e06a1804e0f02506016005a2087b1c46e1844e0e42e08416005a1ec711b860118390b8210400e00582648a1e46e1844e0e42e084160058208791b860118390b8210400e0059258831e8661645610c390a4210780b00683849621859158410a4210780948841e46c188440e42c0841203001687a1883a0841402800e479184390981202400e479184390901002400e8942045a150420a82207009287a1883a0841402800e4962086e16456104290841b0580960b12588616456104290841e0251238861e46e1844e1183a08c190580e00682648e218791b861138460e42a0841603801c0b92187c1985b1283b0d8210380164891b8621083b0c42e084160380160b92187e1b066164420f821038016099238861e46e1844a108390b8210580e00705b87d1103d0d82c0981e0049238861e8631644e118390b8210580e00682648e218791a861138460e42) else (0xe82e09a1f865130440f4360980e0068620f0320a32087e1983c0b0250781600687a1883a09a2087e1983d0b0250780e00686a0e82e099228821f8660f8250580e0068620f0320a2224821f8660f8260540e00686a0e82e09c1f863128420ec360980e0068761502e09e1f0631283b0d8260380181d83a09e1f8621083d0b0250780e00606a0e82e09e1f861128420f8250580e0068620f0320a52107e1983a08c1e0580181d0460ca2e0a61f0660e82a08c1e05801a1d03c0a61f8651103a0a823078160060620f0320b82987e1983a0a8260540e00686a0e82e099230841f4761983e08c1603801c1502e09e1e46c1945e0f8230580e00606a0e82e09e1f861130440f43608c1603801c1883a09e1f8660e42c0941b0580e0060620f0320a4224841f4761983e0981303801c1183a0c82987c1b0651783e0981303801a1a83c0a61f864124440f4360981303801a1883c0c82e0a61f8660f02c0941e04c0e00703e0d0300ac230811f47318c3b0981602c01c178340c02a8a31f0691945b0ec260580b00705e0f8300ab1ec64130410f4330981602c01c1783e0d02a8a31ec630f0290941e0580b00703a0c82e0a02707c1903c08414005c2007d1c46a1844a0e42a0841140e82848a1e0651644a0e42a08411648a1e46a190400f4310a82104502e0a1228791a86112838094190458540f0320a1230801f4721883a084120068541183c0e8320a21e4681945a0e82104801c150320a21e861130400f432084120060541183c0c82e0a21e8620e4280941904801c0a02648c1e46c1844c0e42c0841160e82707c190390a021070012168460b92407d1c8620e4280841a00605a15046109400ba1e065168390a02106801c168541182e87a184541003d0c4280841a0070541182e87a188390a0210741200586a150320a41f060124400e4340881400685a150460ec2e8801ec7018c5c0f42c0941c0078541183c0ec330a22007b1c46818c5d1303d0b0250500250cc2848a2007b1c0651303d0b02505001a16854118421002f0781845c0e8280881c00705a1504e130470781845a128400e83409001c0e82e099220791d0640f0240051705b05a150460e9220791d4681945a0e8220079685905a1501e4721944c1003d0c82200685a1182e4901e4721883d0a025068018151220791d46a1944a0f42a0941200606a188540f0320a0224801e4741903c0881400786216846091200791d0640e8280881c0069710b9240811c8660f42c0941e00582648e1e46e1844e0e42e0841600582648e1e46e1844e0e42e084140380180f0320a1228801ec751b0651303d0b02505001e0f0320b82907c190390a0230741400606e140440f83a0e02e09a1f4681945a0e822007860110360c02e0b02687a1883d0a02506801c1783e0e8340c02e0a82748a1f46a1944a)))) else (if j<12 then (if j<10 then (if j<9 then (0xb41d0580961e0540501283a0c42c0941600502a48e1e4691383c094190580e005854120461001a8621642c0941e0058761aa1f865130440f4360980e00587418b2087e1983c0b0250781600586a189228821f8660f8250580e00587c1552107a1a8631783e0981600587a11c2107b1a8631783e0980e0058761504787a1944c1103d0d8260380181d05411c2f87a1983c0b025078160060541183b0a61e46a1983e094160380181f06a1541f86212c420ec360981600607a1ac1f863128420ec360980e0058741561f8631083c0b0250781600586a1561f861128420f8250580e00587c18d2107e1983a0a8230781600587a188470841f8660ec2a08c1e0380181d84787e190440ec2a08c1e038016188460bc2987e198390a8250580e00607e18d2107e1983a0b02606c1600587a1a86248c2107d1d8660f8230580e0068761a85587e1844c1103d0d8230580e00687e188464841f8660f82c0981b0380181f06a18c224841f4761983e0981303801a1e06212e22c861a4440b82607813026074188460be1f8660f02c0941e04c0e0068781531ec651043c0a82607813005a270841f4711b861138390b8210580e00683a0ba2908c1f476184460f8260440e0069238791b8641103d0c42e084160380180ea284861f8611183c0b0250781103801a1aa3a8ba2707e1944c1103e0980e0060628f2328a52107e1983c0b0260580181aa3a8ba2648c2107e1983e0980e0060628f2328a4224841f8660f8260580181aa3a8ba2787e1844c1103e0980e0060628f2320ba2987e1983c0b0260580180a8290841f4711b861138390b82104603a0b82a09c2307d1d8611183e0840980a82848e1f0651644e0e42e0841160b82a0992187c1b065164460f82102602a0a1238791b8641103d0c42e0841180e82e0a8264861f8641303d0d82102602a0a1238791b8611383c0941904583a0a8264861f8611183c0b0250640982087a1b8460ec2107d1b0660f82162007c1a8681503307e1904d1103e0860801e8761a86707e1944c1103e08587e1f07418d2107e1983c0b02141f87a188601182f0841f8660f42c08607c1e86a1885e48c2107e1983e08587615050138460ee1f065130440f82181d054120461083d0be1f0660f02c0860541183e0f03b8791b0660f82141e062128360d0318861b0440b42161e074168540ce1f8651103c0b02161d85a118360be1f8641103d0b0250660761a8540d03387e1844c1103e085874188460c02f87e198390b02140a02708c2087e1c8620e8250480160a02687c1a8661683a0941200502809a1e864130420f8320941200582809a1e8620f02a0981d0480140a82809c1f0640f0210480c00507c0c828c821f06c1945e0f8260580181e82e09a2087d1b0651783e0980e00607c1a83c0a21f864134440f4360981600686a) else (0x41160a92387c19459138390b82104502a48e1e46e190440f4310b82104582a48e1e46e1844e0f0250641141e86e5b0460ea270841f46c1983e08607a1d8665941f865130440f82141e8601182e4942107e1983d0b02161e85e48c2107e1983e08407615050530460ee1f065130440f8218150460f83b8791b0660f82121d8460d82e89e1f861150440f42c09419a1d8540d61f861130440f8212118300be1f8660e42c08402a09c1f0640f0210480c00487a0b8268821ec751b0651783e0980181e83a0b82687b1d865130440f43609801a1e83a09a2087b1d8660f42c0941e00607a0e82e099228821ec761983e0941600696c5905a1514d0ea1f065130440f43609801c5c16c168465042e4922087c1983d0b02507801e5b0550e9228821e46c1983e094160061641885a4921f861150440f42c0980e00696416c2e4921f861150440f42c0980185a1641512287e1844c1103e09801618c2e491228821f8660e42c09801615148119400c42f8791a863178390b02507801e1d83a0b82707d1d863128420ec3609801a1d8540b82787c1945b128420ec3609801a1d83a09e1f8621083b0d42c0941e0060760e82e09e1f861128420ec360941600686212e1f8611444a1083b0c42c0941603801c1542f87e18451128420ec310b02505801a1783a0b82648c2107d1d8660f82305801a1502e09e1e46c1945e0f8230580160e82e09e1f861130440f43608c1600603a0c02787e198390b02506c1600582a0a02707c1903c08c100300140e82e0a82648c1f476180460f8230400e00702e0a8260861e46c194581183e08c1003801c0e82e0a8260861f8611303d0d8230400e00703a0a8260861f860118390b02506c1003801c0ac1f4711b861138390b8210480e00602a48e1f0651644e0e42e084120380180a9238791b8640f4310b8210480e00602a48e1e46e1844e0f025064120380180a8260861e46e180460e42e0841003801a0a82707c1903c084120300121b96c1183a0e2260841f46c1983e0880e00706a199640841f865120440f822038018188601182c4902107e1983d0b02203801a1a8621782a4882107e1983e0880e0060541414c1183a0e61f065120440f82203801c150460f83a0e02b8791b0660f82203801a118360b82c89e1f861140440f42c0941a03801e1a8540d02b87e184481103e0880e006062118300b82c0ae1f8660e42c0880e00683a0b82a0861b0490f433098100259688ea2e89c1f4761944c1103d0d82600686a1a164150230781303a0580141892408c1e02c08816004054120465001b0651602c0941a0580181e0540ca284501303d0c02c0881600602a48e1f0651644e0e4290580e005862091230780a822078010150481184046c194580a8220780161e0540511303d0c02a0881d0580161e0621281404a108310)) else (if j<11 then (0x483b0d0280901d04507418a284941f4700a0210648621182e0b2264942107d1c021065874152284551103d0c0280841e0458621182e0b2278660e4280841d045a3c8a1104340b0250781101d86a1996489c1f470100390d82161d846899140400e4350b0250780961d86a15226448100390d82504505411c2687b1c8631744c1103d0d8218150470ac2909a2087b1c46a18c5e0f82504706c1604c8781a05c0f4360048541183a0e2264681845e0941141e86211a26490200791d02506507a1a862899220801e4750448620f0320a1228801ec741903c0941603001c1883c0c82e0a42707c190390a0230741603001e0a02648c2007d1c0600e023058080060280981e0600e4280941b0580800582809c224801f47018038098100058280981e064124400f430098100058290801f4711a861128390a8210580a00683a0b8270881f471118110280140a82848a1e0651644a0e42a0841602801a0b8264841a065164420f8110280160a1228791a8641003d0c42a0841602801a0e82e099208641203d0c8260440a00602a0a1228791a86112838094190580a00683a099204440a025078110280140a0264841a4440b0110280120a0270821e46a190420e42a0841402801a0a02607818038084160200122006a5905407c1203e0480121f862119250801f4721883d0a0250780a00707c1a8620a1230801f4721883a0941602801c1d0621182e0a21e8620e4280941d0580a00716c1183a89c2107d1d46c1945e0f82185a16507d1d865130440f43608507687b1d865130440f436098014179228821ec761983e0941600503e0d0300a92287e1983e094140380181e8460ec2107d1cc6a18c5e0f826006076150460ee1e8631744c1103d0d8260068541183b8791a8631783e09416005964168548ec1e8631744c1103d0d82600685e0d0300ae1e46a1983e094140380181ec1f47618c4a1083b0d82600505587e1844a1083b0d8250580145b05a1543b07c1945b128420ec3609801a1783e0c02b87e1844a0f8250500e00607a1182f0841f4761983b0a8230780181d8460be1f8641103d0cc2a08c1e0060460c02f87e198390a8230741600596c168470ea2f0841f0651783b0a82307801c5a16416a2f07e190440f4330a82307801a1783e0d02e0ae1f8660e42a0941403801a1e9230841f4761983e08c160050761561f861130440f43608c160059705b0550e9230841e46c1945e0f82305801c5905507e1844c1103d0d8230580165b0460ea2707d1b0651783e0880e0061685941f8651303d0d8220380140a82809a1e8620e82504801289c2107d1c46e1844e0e42e084160061238791b8641103d0c42e08416005a3a8ba2707e1944c1103e0980148ea2e899230841f8660f82600523a8ba2787e1844c1103e0980140ac2107d1c46e1844e0e42e08) else (0x500181a83c0a21ec741203a00406a0e82e09a1ec741003d0c8220058620f0320a21ec740a0220048620e8268821ec700941a00486a0e82e099228821ec750480141883c0c8288892087b1c801216a1ec741403808800e1a8540c82887b1d0480e80121d86a09a1ec741003d0c8220050741882887b1d028088010188460bc2c09a2087b1c0250680161a8630a828099228821ec750480161d9640e82e09a1ec741103d0d82161782e099228821ec7504406a0e82e09a1ec741103d0d82402586a1782e0992287b1d4140248545302e09a18c5c1103d0d82141502e09a18c5c1103d0d82402503a0d02e0991283b0d82504486a0e8340b82644a0ec360941402582a0a02687a1883a094120280141f02e0a82648a1ec721141202503a0c82e0a8268811283b0d82504809809a2307e1d0640f02305001209c1e86c1985c0f02305001209c1f0621303e0d02305001209c1f0640e82c0981b0500120a82707c1903c0881400407a5903a0b8268821ec740f43608583a099248821ec740941901e82e099228821ec7504407a1d8268821ec741103d0d82141e8460b8268821ec740941921e85e099228821ec7504407a1a8260821ec741103d0d82402587a188460b8260821ec740941c02587a1a862178264882087b1d414025876150460e826863170440f4360858541183a0e026863170440f4360900981d83a0b82644a1083b0d82504507615034099128420ec360941141d86a15034099120420ec360941402602708a1f8721883a0941102801409a1f06a1985a0e8250440a00502687a1904a0f8320941102801409a1e8620f02a0981d0440a00502a09a1e8620e8240440a00486a0e82e09a2087b1d03d0d8220258620e8268821ec740941a02486a0b82648a2087b1d4120248761a8268821ec701103d0d8220258621182e0b0268821ec740941a02586a1882b0a02648a2087b1d412025876150460e826863160440f4360880981a83a0b82644a1083b0d8250480961a8540ac28099128420ec36094120260620f0320a21f8660f02c0941c0458460c8288631783c0b0250701141f06a1502808a1f04c0f43404507c1882808a1f8660f02c0941c0458541183c0a01a8631783c0b0250701181e82a0a42107d1c4691242904502e0a8284891a44e0f0250641141a8620a828899230841f4710450621182e0a82889e198390b0250641180a82887a1883a084140280120a82907c1903c084120300121a83c0a22287b1d03a0440620f0320a22287b1d0220448620c8288892087b1c81101a8540c82888a1ec701303a0450741882888a1ec700b022044874150460a21a8631602c0941a0458620f0320b8298660e82a08c1a045a3a899150440f4310a0210780941f8620921f8660f0280901d045062128360b51a05210c340b01d058098168558601))) else (if j<14 then (if j<13 then (0xe4340a0260480161685413c4c8781803c0c801216a1f0541003c0c02200406a1521f0480f0320038765922707d1c0400e4360848761182e899140410d42c0941941d854899120400e4360941125906216a1ec71140410d42c0941e02616416a1ec71140410d42c0941945a1641521ec71120400e43504506a1996489c1f470100390d822025862128308a9140410d02d078120258460ba26450104350b0250680941a854899120400e4360941202506a1a164150328a41e0480e43204586a150328a0124400e4360881141a85448c1e04a0e831044046051104320a8220740901884a052108310a41d058092150148420e8310a021074112150460f03b0a4268801ec711a0631703c09416030022150464681845c0a8260680125b22e89d230841f0660f8260050541183b09a1ec7218c5d130440f4360868541183e0ec268821ec711a8631783e09411c150470ba2087b1c8631783d0b025074160070541183b09a1ec7218c5d130440f4360900e0078541183e0ec2b09a1ec711a8631783e094140380205b22e89c2107d1c4681845e0f82600606e5b03a89d230841f0660f82150bc2687b1c865130440f4360980165c4268821ec721983d0b0250780170bc2648a2087b1c8660f82505801709a1ec721944c1103d0d82125c0610bc268821ec721983d0b02506605f099228821ec721983e09411487b1c865130440f436094160051710ba2087b1c8660f42c0941d0580181b96c1183a89c2107d1c4681845e0f821a150460f83a8991a0611782504516c168541394c0ea1ec711744c1103d0d82600796c16846109410ba2087b1c45e0f42c0941e00796c1503a8821ec711a0611783e0941600686e5b0460e83889c1f4711a0611783e0880e0078541183e0e8388991a061178250480985b22e89d230841f4741983e098016150460f03a4e2280681845e0881161504606a188590b0250641121b96c1183a899220801e4751a0651683a0980a00806a1a164150328a01e4741203a00586a199648981e4721944c1003d0c8220068628a1240791d028088010188460ba26490200791c8620f4280941a00706a151220791d04a0e8010189220791d02a08800e1a862899220801e4721883a0941200607a1182e899240811d02506487a899220801e47504396c5905a1511c8631744c1103d0d82600696c168470b9240811c8631783d0b02507801c5a16415122471128420ec350450621182e899240811d0250680941a862899220801e4750480921a8628a0224801e472044062118244811c82206386a0e82e099228801ec750500141a83a0c82e099128400ec340941400605e0a02648a2087b1c8620e8250480181f06a150288881f04c0f43400507a1884609a2007b1d0250700141e86a1882648a2007b1d4140050761a8540c82644a1003b0d025) else (0x5130400f4320880161182e09a2087b1c8620f4280941a00605e099228821ec721883a0941200585a1504f5303a87b1c0651744c1003d0c82200785a118420ba2087b1c0651683d0a02506801c1503a8821ec751a0651683a0941200605a0ba1ec72194541003d0d4280941a00685487b1c865130400f4320941200582e8821ec721883d0a025074120058460ec3809a1ec751a0651683a0900a00686a09a1ec721944c1003d0c824028018188460bc2c09a1ec721883d0a0250700a00706a1885f0a82648a1ec721883a0941402801c118300b82687a188390a8230741200622f48c2007d1c8620e42a08c1d048018150460e8308ba1f4681945a0e42a08c1d04801e1522e87a1944c1003d0c42a08c1d04801a188460c02f0a82687a188390a8230741402801e1a8540a22207c0e81400402889c2007d1c46a1844a0e42a084120068288992287819459128390a8210480180a22648a1e46a190400f4310a82104801a0a22648a1e46a1844a0e0250641200606a18828899230801f4721883a084120068541183c0e82889a1e4681945a0e82104801c1a8540c82889a1e861130400f432084120070621182e0a22687a188390a025064120068540f02887c1a0620901200486a1502887c1203c0480101882887a19028090120040540c8288620ec340a0240480141e82a89c2107d1c4691242904502e0aa264891a44e0f02506411417a2648c2107d1c410e118300ba278660e42c0941904502a0a41f0640f0210480c00485448a1ec71130440f4310449228821ec76198390b025064114150460c11a863178390b0250641160aa260841f4711a4490a41202502a899224691383c094190480941a8621782a8992307d1c412025062118300b82a89e198390b02506412026862128300ac1a8430d02d070120258621182e899250801f472188390a02106801c1182e89a1e861150400f4310a0210780a0070621182e89a1e8620e4280841d0480181684610c408781802406801216a1f0500f0280901a00406287a0f0280901a00385411a18c5a0f0280901a004a3a899150440f4310a0210648601182e899250841f470084194118300ba278660e4280841d0450621692487b1c4541103d0c4280841e02685a0b92487b1c4541103d0c4280841984922087b1d8660e4280841d04506212e184521083b0c4280841d0580981502f861148420ec310a021074116188601182e0b2264941f4700841a026062118300b82c89e198390a021074120268628a12507e198380a0210681141884a0c22a869150450c029068160260540ca298611503d0c0280841a0458621182e4b2298660e0280841a04586248c1f8660e02a088190448541191b065178380a822064114188460c02e4ae198380a8220641161a868590540ca28078120390c8016150328a1144400)) else (if j<15 then (0xc668e848f524124348848ed2308218224f48048f520107644a1083b0d410c8cd2502074921083c08225a1552302a082a5a11d20440883d0b02068cc2e125a11c3018740ba0a82307408c8bd1215100a6e87a181a6709a0f020899c2e8386c520e82070ac288821ec7504342b09a2287b1d408d0a21083b0d410b09a0a82307408a0a82908104202a09c2240880a82904104202a09c0a40882006a19965040a1f86249061f05e48c20207a17c2248080d03244c1020300b92d02890ea2106070cc0b02070bc1103864fe1e161e8390b02090ba1083864de1e4440821368c844d608113183841783e0d0300a82687a1883a0941200603a0b82648a2007b1d0640f0250500181503c0b8270791a0631703c0941400603a0c82e09c1f061128400ec340941400683a09c1f0640e42808c1d0500140e82e0a82809a2087a188420e8250480a00703a0bc280992207c188440f0250480c00682f0a0268841e468188440f0250480c00683a0bc2809a2107c184480f0250480c00683b0a0268841f062110390a0250480c00685e099228821ec721883a0941200585f0a8264882087b1c8620e8250500a00683009a1e8620e42a08c1d0480140c42a09a1e8620e42a08c1d0500a00603a0b82809a2107c188440f0250480c00682648c1e46c1844c0e42c0841400582809a210791b062110390b0210480c0068280981e0600e0250480800487c0f0320a1228801ec741903c094140068740f0320b82907c190390a0230741400687a1182e09a2007b1d0640f42c0941c00687a099228801ec741903c094140058541183c0e8270791a0631703c094140068761182e09c1f0621003b0d42c0941c0068761503209c1f061128400ec34094140068460b82707c190390a02307414005970168460ec2e8801ec7018c5c0f42c0941c0078540f03b0a1228801ec711a0631703c0941400785b0b81ec74188400ec350b0250700185a0540cc2807b1d061128400ec340941400702f0a3248801ec74190390a02307414006854118420f02f0a41e063170390a023074140078540c82f0a41f063148400ec310a0230741400782a09c1f0640f021050010099230791b061130390b0210480c00602a09c1f0640f0210480c004828099230791b061130390b0210480c006862118268801ec741903d0b0250680c00686a18c28099228801ec741903c0941203001c150460f03a8e42809c1e46818c5c0f0250480c0080460b82707c188400ec350b0250680c00686a150330a02707c1844a1003b0d0250480c0078621182e8b42809c1f0640e42808c1d0480c00782e09a2087b1d4681945a0e82200583a0b82687b1c865130400f4320880180e8268821ec721883d0a0250680160e82e099228821ec721883a094120060460e8268821ec751a0651683a0880181d82687b1c86) else (if j<16 then (0x1183a89c18387a1d96819964898c1e8761996487b1d040e1e85e48a1ec70a1e86e5b0460ec208631640761414c0ea18c5c10383e0e91a86316296c5914c86317038c1e876199650820ec30e1d83444a0ec30a5b1645341883b0c307a1802e49420823063876118360b91504208c1900c02e42a08c18a5912445208c18a1e85e48c20c10a1d83444c10c10a5b12246c18c10a0a82641200207a1d8268821ec741103d0c487a1782648a2087b1d411113a2103868851b06060ba214540f020a8851303860ba2087d0b020a1e8260821f0440f430e1e85e099220821f410e1423a103e8ed2286081d834099128420ec350445248420f020948c1e44a10838a8420f42c0820760d0264481083d0438308bd2242a0828308bd12183a86410183e87a1819708650b02081b85e0fa1e860b09a1083c082169099128420e28370ba0e19680d20e196883d0b0208198370ba0f020a0c32442a08232546c188208c9512820690d2282060c31483a082522c520e42a0828340c31483a08282a8a02708902282a8a0270892107902387609a2087b1c0440e382b0a02648a2087b1c385113a2103888851b06060ba214540f020a4861903864440f82060bc08141a08661423b03880fa3b48a18203b03840ac2809a1083b0c35248420f02088420f42c08240b82040c22f44a08207c0a02287c08282a0a22708104282a0a22648c210790438740a21e02c08282a0a42688920878c88c081418083288c081913038487e0e42c08252486a190209482181213020502020a82909a0a820b44208141183a081a284941e02808418c491150380a202e4921e45411038c8920812080a42820548a148380a820b4811083a0821148390a182e452108390a283083a081d1103a0a82080be0e428689c1e0400e430a899120400e430a0ca1e4540b020a1991404408220e0d200420e82084420810324420818344c20e820882e081408086e0ea204688899220801e470b0ac2909a1ec70a86316142883b0c1c26823061c6689a1903888a525020689d230841e46a18322948048a52502070ba28122744c0e82082007a1d86a19a1ec70e1f87c1d06287b1c307c1e85e87b1c28842087c1503c8631638821e86e1183a8631638761404e0ea18c58c1d0481083c86316303e0f03a8631628801f0680ca0ec30c2007a1d86a19a0ec30e1e074168540ca0ec30e1d8340ca0ec30a1f87c1d06282306307e1e8600ba08c18c1d85a118360ba08c18e1d0300ba08c18a1f87c1d06282b04307c1e85e48b0428760d03244b04287e1e8600bc2448302387c1e85f08920c08c1e0360d0304430230740c02f02b0228781d05a1503282300387a1da1ec741103d0c387c1d21ec7409418c1e9228821ec7504307c8892087b1d408d1383108346c18143a48054540f02c0825150440f020944a081510) else (0x7c0a1228801e28740b8284280828280990480881e82648a20078a1d82644a10038a48a2046818221003c081b148400e42808287609a1f0400e28740a21f028082c2a0a02648a20878d0a82809a224821e304e87c101a1f028487a08122087d1a0608838306820ca1f02860ba1f4541003808321e8204820287a0e120e0a188204838283c0a140a0d130400e820817c2687b1d410a0fa18c5860d20ec3504203109a08c1880a82741200222687d130440e2a268640e1a2748c1e46a182a2748c1e44a0e2a2748c210790a820c89d130440e820a59226107a1b96c))))))
def genIndex8 (j : Nat) : Nat := if 5 ≤ j then 0 else (if j<2 then (if j<1 then (0x780078005c58084c843a71b32dfff800420df800607ff80022085192a9cbf80079fe1094d12cb9cd780011e3b0b7413589c6210e603c7008861ed1124987758da16cb5222814301bd806d58e892e8226f8004c5b9c0df8007800156ef80020fb11c52056780078007853f8007800780001ad7923e03468fc69adf82b80679195605dd0d7e126d177f95ebd9d780078001da0f80078003d19780029c229eef80051711518f80039817800391af80078007800780021ccf80078003855fcc67800098f6800780040b5110aa9c8b16ff8e1b8ecf8007800780078007800156d80acdddef800649a78007800780078007800719b78005801780009d5c5c6b1a800dff80078007800088ab452c96af8007800742278007821112a780011e2a80ffa10f996f800790d0148940aca27f8005cac58e6f80078007064f8007058a906f8001c2978005450780060a6780078003960f80031f2d83e61eff8001df39a0370c0780078002a1f28f7f800780078007800204ed88209314955e1cc78007800780009f4f800195fccf2a8f0f80060b0986181278986949f0172487978007800780021a3f8000955411bf8007800693c780018157800780078004e181928d00e1047f80015f6463425452dab780031577c200e075054aa2f91b96c8be90091dff800780078007800780078007800780050da7800780078007800121c0a188896780078004def792f79441962d811c8e4d0c9911df800780078002557f800388b115a2de74951f80078001031996e78006946b4bb78006a300a0629400076780049fb911f90f17800104c5099f800780021c3180978007800780050e9b16e89d1f80019a76952780015ea1a11f8006164000202128224f10958e0780021ff4ddf69b4f800780041aa7800161d24547428f800120e3c517800105451c0d819f800487d68600dc5c8e76616c10ff80071a0f139f80078007800406c40209993f80069743973f2078b002c0121211404262400300004800e1440d201d1120604501120c2a0000431a00440c40c0800102301810a0048608002002820203182800300041135a24001021918912004000200981103c214060002c182008c440048310002830800901020c00d02200870a045090804008001db820e0019a3a9c10100702810c000056e2488e160c0010004a010650200240c182047060704088000c042001a0410128241830040280080488b0e080030400005061c109020c2004008105040c300182000926040000e000020604100280d400000090b10180002200008140c4840000003005c7831c04105022000500040095c00080023028002140031c0419b061008028041860004280041848002002950614800164c08502085831800380183c12a02300820404489260050104040801c40100000060f00040030a04185) else (0xc906103922259c5af8004152f800780011aaf80070a58d69990778003138f80039ca1451f80078006220399268e87800644cf14801bb7882f800780078007800780078005913f8007800780078007439f800780061a2f8004890514720b5c83a78002053217ef80078000838780018a4685e5450c219d944f80078000073f80078002e0d8910993ef800088831c768ca921de84a780020725a21901a780069fc4c5581453868f800780008178802f800780068bdf8005930780078006077780078007800780001bcf80078005d6a9836f80019e97800780028ce722970fff800108de918e9e238d0780078002090f800406259671823289b78005214c12c21f7211578007800019f918a1a05c8687800259cf80045e229cde9a9e888f800106a49836a1c807f21497800780000c87800780078007800780078003d55780078000c96f80071d9f91a780078007800545678004a28300a5db351807800620880eb78006016b157f45a70ed6803999f01db98cc3d69100f35fcf834a9f0813440101a36780020a7780078000875f80041e1da09f8002931a0647800243f852a7800086581087800116db0eaf204e9df40ff7950f800598b289d28d98079f80008be819d5ddcd8ea780078007800200549967800780048c0b22ac0b4b083513e259c414f7800555aa8ca3a0ca87df885e8ab108c783c9060b4de21ecf8004d8878007800780071fea5f13042aa30e09a780050660d02780061d2691ee1e178002d24f800780051f8509580273169f80070ba78006dd8780040e46dced561f800500850f87800492e602f38058163894a5949a9b2f80078001612f80000b7f8007800780065a4f800780055d7f8007800623448bcf80078007800717e26003080785b6142009abc38f8007800750f01daf8001132904149a190cb08bd4dc9d1de002499d2d16178004537591c78002010f80054f47800613241f278007800044681194172f800780015eef97f501888c14e09f1fae02cf80031147800345e780078001c327800780069e8f800745cf800780078007800382d6866f800780022167800656f7800780020bc70c5a99bbda061ea7800615f089f780050bac927780011845887197cb97b78001846780078004c4959ed78000423e953f80078000154a9dd7800512378007800217fc139780078000e0571d3f8005015fdc509294dca194cf80055ddf41f78004a0fa85cf80078001a0d780031abe00df8007800186711e51912fde1e12af800780079bb896c38b479667ddd0896d93bba210cfb78002c24714b1c24f80020ccc857c08e308a7800453e48c919eb01bff8003c1c207ccd5211ae997ac1283d4e7045a1a6c1a5721a7800287b30f3146078007933f1b5a4aed80a98d1f8000189f80078007800780048ed84ace8f615d74982983af800493f)) else (if j<3 then (0x1dc4198da44f2c2e780078007800611f081ad88088247442b96978005030a01e5c8b74f7f0b951e4f800780079f03203f1769c2141365033d233f80039b9f800219df8cef8007800780028267da38043f8007800204ac837a8317800780078007800118578001de6f800780020a680a041a4186510ee4990f8007800686e988ef8007800618081b1914671f6b162397a4049f80010e24d90f800601c780010f8ea23658e78d5e0c6b1d6f800780440e9780078007800018d1847780005d20422f14be82c419ed9595983f80039b07800384f3d6e7800305a20cdf80078002596f80070367a01f800780015aef881c812061410bf45d67800405eea112420c027f898009cf8007800780078007800686b780025f6f8007800780078007800780078005941d1fb7800516bf8007800780030e2f8007800780061d02c43780009c42981f80008cf51c6f800690cc841f800780078006d54f80078003979f80041b64093b9c87d91605078000589f800220b74ad78007800295d8950780078001126780040f2b03dc110780058fdc10070f578002d2dd9c0181940a878f6edd5ca3305ff2876f1e73040ac1368eb89bada156d1ad8f950aa8c8e58bb1813c1b155647800780010dd91ee70def80078006072f17d4063d8f4f800780011fd6091584d41ef7800792df800011e201df800780011f450f05975f96b780078007800217c4a0020a1780065977800780025f7660af8000579d82188707800780001b6e59878004dcb780050d220de780034456166a077d8b871c3b8a8fc36f80038d30a22780078005174c07ec92bf80045fd309dd22f393cadb0a232ec94780078002829f800698c7800186ce0f1c07178004c9671e7f8007800780078004225780078007800780041bd780040a919eaf09529917800492ff8005a2678007991f800180d70527560c546d0c3fd4291e37800314d9a2d29e6b885586bf80001b8f15b49c2a13a419808446a270032443c0111aa1e9158002fc168f80051c7ed21e89e9c57f045582e11947800780021ec6df4780078006875110b78007800780065af3935780078004626d505f800780005cbf800780078001982111d780039a368481999e0a278004937780011a4c04e7800108cf80025a309ac816a194ffc9ab0e3c80ca220b0fce0a4f8005a2d85f50229f800259f7800189971a8f800780078006a0b8c21f8004874d41ff800520a09b398e5490a01d918331213e937f80030ef7dcdf092f8004c4a1564b0352a1e30e1022c08f3f10531af0852b9ce25045529ade67800615c0c5278004925a170780018d1583ede233a358cd581a27967f80078007800780078007800381d48cbf80011d0f80078007800780038b29007d1eba4f07800604b21f3f80078002e07c0e7a8557800207aa1437800780015c79965284b) else (if j<4 then (0xb11119227993303fad95e0b659d4a914d994c190785f854bb8d6919898789901d8a38044f80000dc40187800794d79b77800247a780069cb407338b1f8005c1e4178b883b0af654dc4a2ecf4f00c5c5b7800780048a2a15d50c1d5cff800780020d86d73582a780000a30103284d84383447418849bc68dd309c186af800315cf8007a0978001960607408fef800780071f9095e78000134c0286961d9718046c1b7e177720c4c926871a5c36c23720778b8b9dc7d7a648c099cb0afd0bf861e09a7e09434daf800240bb8a0b85740a5206f780005f2f8007800310f789745260806561619781a2b29d8e96d1db078003a0ec8a7f800403be069045c1c47f80029ab78007c1d78007800494e0170b200f8007800780062130518780078007800780049ae780010ad3026d5d07800305a84fea99a583f79bd8902f800601ef80029be780019c979ba522ef80011db70ae41027228b600c886d0fe4dc2a56825d6d089780078005878742b7800780078005084e13ae0df48e6797df907d942f0dce14ef800217670fd780061fcf80078007800312b79b84e0878007800795178000a2285c731f50804e122a8faf8001d0dd8d9780018e8f8007800417378007800780078002904687c79dd9d717800418af1b5102388b3e15aa0b211fdf14af800001b71e87800780078007d2e780070815cbef800780078007945e121f8007800500b78007800121fb003780069cea54ef80078007800780079d5621bf800688d78001a3179334822780031a62832e05d00cd199e780058c4f8004dfa80d8f80069f5c50d40c7f800705f70ada904a88799d78a3255f4a1afe5812215a9f789d179caa9e64049389e180748c55a2a300990628059cddad01f784045fde1531943d001f8002de7a8d2d165d13d01fa3929e5eaf8007800506ff8007800491cf9e5c028fc3b7800780068c461def80078007800508611cf7a3504d19df5e461f8007800422e50d4f80031c9f8004c48f8007800115bf80048aa709378002d0852197800780079253a17343b89bf780068177800492d7043780001c58158f80071d818efcc395db8205c6924988f440a1968780078002988a93ff800780078007800780029f130514147d618ac5988f2780074ba858f420af13694fe1a057800780030cff800780001b410d448abed9bf8007800610ef80028daf1ac78001492c0c278006195f8004dd8a16f78000959c22ccda50a10187e79e03097d941606179a14909f80078004121303730b6d9d64156a1f1e8c8f9b0c90df08fc930d089f8dbde2b780028f59206f800780030e0c517d00bf80078007c46385958ee8c4d7800780078007800780078007800219aa905f8006a16f80048b9f80078000838b02eb4792915b997b154798619247800780040427800780048fbf223f800780070be) else (0x78000c1cf80078007800780068c7780071b2481fd01cf8007800780069f8f80078005e04f800687091a939d410db39897800702b218fd83078007800399c78007800198cc429d18ef4bc780078001ddbe541a05bf80005f7d90bf4287800780078007a0161a5f0d76202f8007800562bbd173e17906d7800361cf8007800111b289fd8d3884fd5f948d0f80028d5703599c1e91378005c54e814f80071563917050ff80069f9ba143091c87bec80fa1b780005381d8080c3420411d35940921af80021977116608bc82290ac3800e919f8002a17f8004120a97bf80078007800517978005597f80078007800402ae0f9e2185987f8001813780001fff8004234a964c8d625001dfc65427800780078000963455ce8f7780050e5f1bec0295c3750a9f80078007800780078000c2a21e44903f80000c641c11916f8005dcae493780049757e0d0511e80ee856d89bb917f80030206db4503b49dce0aef80078002025f800481678005898f8005d6079da78001184c03d413b780038ec68a1f80060b338bb8e03f800793de851f185dd63689278002c2dfc36756250b07800106378004058584881e0f800607a1908c069e039c41ec10c786db90150e3581295adba1d2212186e3224082568f4701129a009387800544af5db61ed9a2bb44871c4f8b1499978007800314c5d81f1f37800780078002918780078002050f8007800020f5ddc7800780059cfe92078004a31a88451f649d750fa6c49882dc0c2818bf5ce220201e9818e2c35))))
def genData9 (j : Nat) : Nat := if 9 ≤ j then 0 else (if j<4 then (if j<2 then (if j<1 then (0x6483f792a41fbc9120fde4690fef23483f693241fb49520fda48907ed23487f691a41f7cc931fba6c987dd35cc3ee9aa61f74d132fba68987dd324c7ee99261ef51740f7a8aa07bd43507dea1a81ef50941f7a84a077e65443beaa6a1df55150efaa7a877d53543bea92a17fdd931bfeec90dff76482ffbb2217fdd531bfeea90dff75482ffbaa217fdd131bfee890dff74482ffba2217fdcd51bfee690dff73482ffb9a217fdc951bfee498dff72442ffb8a417fdc151bfee098dff70486ff3ae837f9d731bfceb20dfe758c6ff3aa837f9d531bfcea20dfe750c6ff39ca37f9cd51bfce628dfe72c42ff394217f9c910bfce4085fe71d42ff38e657f9c730bfce3905fe71942ff38c657f9c630bfce3105fe71542ff38a657f9c530bfce2905fe71142ff388657f9c430bfce2105fe70c86ff384437f9c121bfce010dfd76d42febb6837f5db40bfaec985fd76482febb2217f5d741bfaeba05fd75ccafebae637f5d730bfaeb885fd75946febac837f5d631bfaeb10dfd75502febaa637f5d530bfaea90dfd75482febaa217f5d441bfaea18dfd74d42feba2657f5d131bfae8985fd74486feba2417f5d110bfae7a85fd73c42feb9ca37f5ce41bfae718dfd73886feb9a437f5cd20bfae6885fd73146feb96217f5ca60bfae528dfd72942feb94837f5ca40bfae518dfd728c2feb94437f5ca20bfae5085fd72442feb90217f5c750bfae3995fd71cc2feb8e417f5c660bfae3285fd7190afeb8c817f5c632bfae3185fd71882feb8c217f5c450bfae2195fd710c2feb88417f5c321bfae128dfd7090afeb84837f5c232bfae118dfd70886feb80437f1d531bf8e6a8dfc72442fe38a417f1c121fe6e0887f310843f983221fcc0d10fe604887f106443f881a21fc40910fd641107e721887ed98461f5cc631f9e65197bb40903dba0c83ebd0a42ef6a12877751947bb32e21dd99510eeaca886fb60982fd380857e9c031bf4e010df97010afcb80637e5c021bece3305f671942fb38c817d9c630bece3105f671182fb388a17d9c442bece2205f6710c2fb388417d9c410beae3305f571942fab8c817d5c630beae3105f571842fab88c17d5c450beae2215f571102fab88617d5c420bdce4305ee72142f7390817b9c831bdce4185ed72182f6b90a17b5c840bdae418ded720c2ef39e83779cc60bbce6285de7310aef39881779cc21bbce6105dd73d06eeb98c1775cc50bbae6215dd73102eeb9843775cc20b7ce9995be74142df3a0636f9d030b7ce810dbe74082deba6656f5d050b7ae818dbd740c2deba0436f5d020afceb1957e75102bf3a8635f9d430afcea10d7e75082bebac655f5d440afaea18d7d750c2beba8435f5d4209fcec284fe761027f3b0633f9d8309fcec10cfe760827ebb0a13f5d8409faec18cfd760c27ebb0433f5d820) else (0x3d653c2d3a89397537ad36753441332d3189302d2e892cc12b652a0928ad277525ad242d226520311f1d1e091cf51be11aa919711815170114cd134d11a90f990d1d0ae9098d07e905fd043502490038fedcfc84fa98f8d0f6c0f3b4f1a4ef04ecd0ea78e964e850e664e430e1d8dfecdd94db84d974d788d59cd3b0d1a0d044cea0cc6cca5cc828c6ccc498c318c174bff4bde4bc64bac0b940b808b6d0b598b268b154af20ad58ab48a914a794a638a4b8a338a194a0389f009dc89cb49b589a44993096fc9534936c91808fb88df08be08a18880886648454822080c47e907da07c447b0c79f878c077407530744073507260717070806f6c6e7c6d686c786b886978678c6654656463e4626460c05fac5ebc5dcc5c945b3859dc588057485634552053e852b0519c50884f984e604d284bf04ab849a4486c477c468c45784464437442844170405c3f243dec3cd83be83af839e438f43804363c350433cc327031142fdc2ec82d902ca02bb02a9c2988289827a8260424a82394225c21241fec1e6c1d7c1c8c1b9c1aac19bc181816e015cc14b81380126c113410200f300e400d500c600b4c0a380924081006d805c404d403c002d001e000f00003ff39221ff9c520ffce090ffe62443ff30a41ff94910ffca2907fe42443ff20a41ff8c910ffc62907fe21483ff09221ff80910ffaec907fd76443feba221ff5cd20ffae4887fd71483feb8243ff59510ffac8907fd64443feb1a41ff58d10ffac4a07fd624c3feb1221ff58550ffac2a07fd614c3feb0a41ff55110ffaa6907fd524c3fea9221ff54560ffaa2a07fd51483fea1a43ff50d20ffa86887fd42583fea1263ff50930ffa84887fd41583fea0aa1ff50530ffa82907fd32583fe992a1ff4c941ffa64a07fd32443fe98ac1ff4c540ffa62907fd21983fe90ca1ff48640ffa43187fd21883fe90ac1ff48550ffa42a07fd214c3fe90a41ff44a10ffa24887fd02c43fe81221fec1920ff60c887fb04483fd81a21fec0910ff20ca07f9064c3fc83241fe41910ff20aa07f9054c3fc82241fe40d10ff205087f902443fbbb221fddd510feee8887f773443fbb9221fddc110fee2c887f7154c7fb8aa21fdc5121fee28887f713443fb89221fd9cb10fece4887f662c43fb31221fd94b10feca4887f642c43fb21221fd8cb10fec64887f612c43fb09221fd80b10fec04887f576443fabae21fd5d510feae8887f573c43fab9a21fd5cb10feae4887f565443fab2621fd59110feac7887f563443fab1621fd58910feaa9887f554443faa9e21fd54d10feaa5887f552443faa1e21fd50d10fea85887f542443fa99621fd4c910fea2c887f515c43fa8ac83fd45631fea2aa0ff5154c7fa8aa21fd45121fea28887f513c43fa89a21fd44b10fea24887f502c43fa81221fd1c910fe824887ef2)) else (if j<3 then (0x601c0801001010070300e04000c0f0682c0e04000c11068200e060280870783012080301000383c18070280c00303c1807020080030401c0c0381104001c1e0d0581c0882000e0f060241006022080040411a0802810068200900f0601c0a034100070803818070200060783416070200060783012080301000384010050200c02303c18070280c0030e44510050241007032150883809810070300e850220c00403c1a0b03a140883001011068200e0602a110602241e0c048200c850220c0048401a0802a11060200900f0601c08830100071344014090401c0d0120200e0601c0800181e0d0581c080018220d0401c0c05010e0f060241006020007080341005010046078300e040100061104a230d04a210c050200e04583c1a0b44a200e86020009080210c050200c02383c188803a180a03001010068210e860280802403c188803a1808020010220b04a230d05014080381140f0682c0e04000c10040140803008c0f0601c0a03000c10068200a02008c0f0601c0802000c230a8441a8c458240b0481808b07831160904018080020208b040140803008e0f0622c0e0501800708035188b040140401201e0c4581c0802000e150883412058240c04403c18090401808001c2008028100601181e0c03814060018200d040140401181e0c038100400181e8e0682c0e04000e0f0602410060200070823810050200c02383d1c0c0381406001c208f47034100501004807a3818070200800383c1a0b0381000303c18090401808001c2008028100601181e0c03814060018200d040140401181e0c0381004001ae832e646e4c6e2dae0eedebadcaadabed8aed67ad48ed2a2d0dacf7ecd92cba6c9bac7cec606c43ec22ebfd6bd7ebb6eb982b74eb562b39ab1aeb00aae42ac7aaa8ea812a5baa3aaa19a9fae9d9e9b6a993697269516934e913e8f768d8a8be68a1e887a866a84c682fe815a7fb67da67b9679aa779a75d2740a7242707a6f1e6d0e6afe68ee66de64f2639661aa60725f165d965c165a96593a5802563a547251d24f7a4db24bea49da47ca4692431a41763ff63e523cf63b0a39ae37e635fa34323222305a2e922c822aba28ce26e2253e232e21661f9e1dfa1bea1a22185a166e153613fe121210020e3a0c2a0a3e08be068a043201d9ff81fd95fb3df951f6b1f4c5f291f05dedbdeb89e90de6fde4ede2dde0a9df05dcf5db2dd8f9d6e9d491d2a5cfbdcc45ca35c7b9c585c399c1adbf79bc01bac9b991b7edb625b45db2b9b0f1af4dada9ab75a965a779a569a335a1499f5d9d719b61995197659555938d91e98fd98ded8c0189f1882985d183e581d57fe97dd97bed79b977a97551734170c56ed96cc96add68cd66e164f5630960215e595c6d5a81584d566153e550fd4ea54c714989482d46ad4509438941c13f8d3e79) else (0x883a14088380c00f08034180b04215088300921f0c054281087a36180883a16088200c00f0a046200f870300e0441000a0c05c2a1006c32160842a08025850260f0683216070220800507c3a180b854208d048220f0642a080270501e0c04c200f060220800507c3a150823410058240d04012c2813078300e050240d0400282a130803410050100480a04c1e0c03810040020280f0601c08828080081a8c454230e85c2a1409a46210f46c31130883a16088280c016078300e04410040038dc50220e05d210f06830168883c1103003c4416092421a0a44014080381204c11058249087c30148883814080340c00e0a84c22908783618094441c0b040120600784e221007c3818070220400504c1f0d0642c0e044080090a845200d0441e0c0501204a0983c19090401e0c0440800a0a845200d04a200b048180902584c1e0c03c1409034080090983c1807024090200202813078300e0400800807834160702204003845200d04a200803012049078300e0501a0400383c18070200902001c281308c411e0d46026108702a100501401e17098411f0d0642c108742005006050228f06a32100783015080240181d0e05c261047a321207832100280342a1408a3c1a8c04a1c090301200c0e84c208f460210f050240c0280303a17098411f0d460210f0542408028038261047835180843815080200a00c1806c2d1288235188b854220b0481c04e0e059251085a2a10854220e02584d231087a3618898441d0b04414060070742e1409a421f0d862220f058240903003c281347a310e84814050048883e1d0c05c2a130803c18080381002003c1e0c0381002001826910803d1c0c0381000484c1e0c03a140883001013078300e04410007488401e8e0601c0800205a230b83c180742811060028541e0c851220f468311207428110400381e0c03810040018200d040140401181e0c03814060018200802810060118220d048100602181e0c048200c04000e10050240e06008c11068200e0602808707834160702000608034180b040046168a84a1007a391a0c45c220f0480c00e168a8461d0803d1c8d0622e0f04801a910803d1c0c83c120040401c0c038100030441a8c0401c0c05420090050411e8c0421c0a04018050050411e0d460210e054200802802c220d0401c0c05010e10040140803008c10068200a02008c1007c3818070220400407c1f0d0642c0e0440800907832120803c180881001218078300f050240d0200242a0f0601c09024080080803818070220400383c1a0b0381102001c220d0401c0c05012048078301208030110200201e0c038140681000e0f0601c0802408007078300e0400800609c441f0e0601c080020260f8683216070200080983c190903c18080020260f0601e0a048180080983c180702408003850260f))) else (if j<6 then (if j<5 then (0x160a048200e0680921c09441160a84014080380942208235188b85424110783004b100411a8c458220b0481804a1b88a208d4622e15090441e0d01306e2810072251046a31170a844160903809e104582812070300470822c10050200c023880210b0421508830090200b24a210b454210a8441c04b0802c10854220c023850210f46c30110742c110401801815078300e044140400405428918843d1b0c44c220e858220a03003c1e0c038110401000e174843c1a0c05a220f0440c00b0fa421a8802810070240921d4843e188883814080340c00b09a421e0d862220e05820090300303e0f8683216070220400485d200d4401609030120490c03c1807828120681001215078300e048120400407c2e9087c34190b4441e088180181f0ba421a8802c12070240941d0c2421f0c4441e0a0481a060060742e1509a421f0d862220f058240903003c1e0d0581c0881000e9006a200803012047078300e0501a0400383c18070200902001c268f4621d080280a0080a23d188742408028020281347a310e8481405004a3d18874200802801c70371b0b050224803d1c0d0602e0f04801e32130411c0a048200e0680943207a3a180a048200e0682400b1f8c45a23092401e8e8641e0a0481c00e1f0d4622a0a045200f47436190983c16090280223d1a8c44613488401e8e864220f0480c00f13441160a048200e0680922687831160a048200e0682400b110802c1288835160a848140803811a221007025104582a10050200e02608840160943c188b0541c0a0401c00d1107c38180843d1a0c458220f0400c00e110702c100683016080092220f87438180b8411a8c45c2a120883c180280883e1d0e0411a8c458220b0481804d11074381708035188b044160401305a2a13898470f0622e130803c1a090038722e1288c44200e0602e16894411a8c45c2a11058240e02a8b45423108802f0f0622e0f050240e0070ac54251187c3a1c0c056200d4622e130882c0a0290a8461e0e8521e0d0622e130782c1205003c54230e8702e138843d1a0c45c220f0480c0100822c14090381802384116080281006011c58281308a1e0d05a251007434120068f0622a12c461a0a04a210e8602c1207023c622e1288c441b0b440140843a1a0b0481c050168a8470f860291007434140903801a35188ac54250d056210d048210e8682c0a0280d454190a43e18094401d0d058240a0070ec6a2a1184e1f0c448200e86824060070e058221005e1e0d05c1d0a0441c00d110602c1087c301107428110601801a220c05c2c1086c32160842a11060134441c0c05c2c10050220f0642a11060138441c0b04010050200c0248882e160843410054220e04012c6225118602e160ac421b0802a110702809e3a188a846170a43e1907028110702801c311185c2c138843e19) else (0xa8421a090421d0d058100511a8a8461d0b84e1f0c448200e868200600788830160843e180883a14088300c00d1888c2e1609c3e1907428110601801a1f0c054281087a36180883a16088200c00f1a8c45e2a1187c3a1a0c05c2a1409a461e8d862260e8582208030060280f0601c08828080080a04c1e0c03811040020269187a36188983a1608828016130843d1b0c0441d0b0441006006051200f47036180983816080280181408c3c188b04c1c0b0401400b0a0461e0d862200e8602c100500302a1188034130802a11060280961408c3c1b0c04c1c088301400b1a8c4541e0c850229007a3a19078200a0078a8461e0e864290f0683117078200a0070d454190a43e18094401d0d0401400d1889446180b856200d84015088301404e188a8461e0c85c290f8641c0a044180a0078882c15094411a0a84014080341404d188b446124803d1d0c838140803801a2210058250f0622c1507028100700345a2a11884401787831170702810070038622a12c461a0a04a210e86028100702385a2a11c3e180a4401d0c050200e0068c44a230c05c2d1046c200a0401a0a0270c454230bc3e190702810068280182687831160a048200e0682400b168a84e2611c3c188b048200e0682400e188b84a23114401408032150883809a2d1508e1f0c050200e06428110700346a31158a84b10468241007032150501386a2a87c301208038190b0441400c1508c3b17898401e8e46831170883c1203004058281308a1e0d05a251007434120068b454271308e1e0c05a251007434120070e058221005e1e0d05c1d0a0441c00d168a846211005e1e0c05c1d0a0441c00e1508c3b0f06830168983a160882801a220d8602e16090411e8e854220b0481c04f0f8683015088411e8e86c26110581404e18878321408a401e8e86c32130782c120500406a1d0b84d221007a3a190883c1203003860220d8602e16894411a8c45c2a11058240e0288bc34180ac401a8c45c26110581404d11874321487834188b84c1e0b0481400e1505c271087a34188b8441e0901801a30110602e16880281087434160903809c2f0f8602b10868241087434160501346a1e0a43e18094401d0d058240a0068d43a1709c3e18890401d0d0480c00d1b8a0441f0e87030170b24a210d8642d150842a110701505e1f0d056210d84015088381404c1887832170a43e1907028110702801a310e84e210f864220e850220e0300346e2811074381888036190b44c210a82809e301106c2e168823610058240d0501346a1d0b84d231087a3618898441d0b04414060088c43c1d0c85c281388a421f0d86425110782c120481802837140883e1c0bc411f0d0642e1087424050080c0441b0c05a208f464210f050240e02803c5e1f0d0602a1409c46208f86a32130843c15090280a0141bc41)) else (if j<7 then (0x803c190803a14088380800e0a03c18070220a0200206a311508c3c1d0c85c2a1409a46200f46831130803a1408828080180e85c26910803d1d0c83c120058a82e1387a34188b83c120050742e1387c31120803a1a09002c3a1387c320e850220e0048742e1348c3d1b0c44c1d0b0441400d0a850260f0601c080100121d0b84d220f4743011078200600608830170b0411a8c458220b0481804d0b84c210f46831160883c100300303e1d0c05c2a10868241087434160401383a17098421f0c4481d0d0400c00c0e84c210f860220e850220c0300303a17098421e8d860220e8582208030038281087a36180883a16088200c00c0a850269187a36188983a160882801a1007a391b0c44c220e858220a030034200f47236188983a16088280161548c421e0c45a26110742c110501801c1d0aa461e0c45a260e858220a0062461e8d860200e8642c11050180189187a36180803a190b0441400b0aa46210f46c31130883811068280c00e0b855230f46c3113070220d050030281087a36180883a16088200c00c0a04d230f46c31130742c110401801a15078300e0441404004054260f0601c088200103d118742e13488401e8e8641e090034441f0e060210f46831160883c1003003854230e85c270f46831170782400c1d8a8461d0b84e1f0c448200e8682400e110602c1087c301107428110601801a230b84e1f0c83a14088380141f0c054281087a36180883a16088200c00f1508c3a170a04d230f46c31130742c1105004170b6168a8461d488401e8e4683117078240101a8cd6431168a81e8e8622410074341203004168b2168a81e8e862241007434120068e4622d12a48200f47432110742811070180202d1185d241007a3a1907428110700346a3115095221007a391b0c44c220e858220a03004854910803d1c8d862260e858220a0068b45427530961e0c45a2410074341203003c5a2a13a98461d8783116890401d0d04801e3916894442150062210f0622e110742811070180242d1508c44215005e1e0c45c1d0a0441c00f150943e188843d1a0c45a26110742c11050180222a1187c3b0f46831168983a160882801c31168961f0c450200e86428110701801c2d1508c2f0f862281007432140883801c35188a84b0f86224100743216088280c00f1543e18890401d0c858220a0058c44a188843e190883a140883414060070a846180bc3e19074281106828018351888c3a1709a44200f474320f0400c00f1107c38180843d1a0c458220f0400c00e1107c3a1c0c05c208d4622e15090441e0c0140441f0e870208d4622c11058240c0268b8562a1409446220f874381046a31170a848220f0600a8391709446221007c3a1c0d8602e16890411a8c45c2811058240c02c0a8461d0e05c270f468311707820060070d4622b150943418) else (if j<8 then (0x70a43e1907028110702801a1d0b854281387c320f044140600607832150a04e1f0c83c12048180182f0f86830150a04d1e8c43a120501401c375b08c3b13488401e8e468311707824060080d468b215066280f47430128803a1a090280203519aca260f47431120803a1a0901801c318a249200f474320e050220e05003462230bc4d241007a3a1907428110701801e35152441e8e8602611078341105003462914803d1d0c83816090341400c1a8c626910803d1d0c83c110501801a234803d1d0d8642e0f0440c00b1aa401e8e8642411078341103003062234803d1d0c83c16090340c00c1a8c628114803d1d0c83c120481801a2a1409d4c230ec4e1e0c45a24100743412030044542310a803c178a43c188b8381408838140101508c311787a34188b83816090341400e1508c3e1d89c3d1a0c45c1e088280c00e11875381087c391a0c45c1e0881801a2a11875390f0622e120883c1a0881801c2a118783a9c8a43c1a0c45c1e090240c00f1889434188ac421a8a042180a8441c0a0278a8331487c31148803a180a0441c0a00708c2f1387c31140803a190a0441c060070d4550f87431128803a1a0882801831128622d1046a24108602c120682809c2a87c31128803a180b0481a0a0060d4551387c31120803a1a088280c00d1ac3e1d0c44a200e86822060058a8470f8642d128803a1a088180182387c31100743416090340c00b1a8a8331487c30128803a1a090240c00e18c421f0e8641d0a0441a0a0058a8461787c32170742811068280183112c411b0883215088341404b1543e190883c190a0441a0a0058c446180bc4e1f0c83a140883414060070c446174b0421f0e8641d0a0441a0600708c2e9687c30110783214088340c00d1888c2e968a43e190702811070240c00e17a54221087c3a1907822090300303e9509c3c1b0c85c1e088240c00c0d2561f0c048220f0682209030030309509c3e190702c12068240c00c0a84e1f0c83c100481801235188bd2a110843e1d0c83c110481801c2a1187c3a9587836190b83c110481801c35150692b0f860241107834110481801c31118602e9587c320e058240d0481801c150a0461e0d860260e05820090300342a1487c320f04410060048742e15098421f0c0441e088200c00d0a03c18070220a0200202813078300e0441404004850229007a3818070240800504d221007a381807024040050501e0c04a200e860240800504c1e0c03a1408838080090983c18070220a0200206a2d1503d1c0c84c200f0602000c188b4469007a381807828120600306a3115078321408a401e8e868321207828120400486a31118742e13488401e8e064200e04808010168a8460f0622e130803c180800305a2a1185c1e0c4581e0a0481800c1a8a8321407830128803a1a0a0481000e1888c2e138) else (0x1509a461e8d862260e858220a0300343a170a04d210f862220f0481206006854281347a310e848140500544c200f47236188983a16088280c00d0e85e281107a3a188883c120481801a230e856269187831168983a16088280c00f0f05e289087834188b4441e090240c00e89a461e8d860200e8642c110501801a1d0c85e289087c301207434120481801c230b856269187a36188983811068280c00f0ec51210f862220e050220e0481801a1409a421e0d862220e0582009030034261087a36180883a16088200c00c0a84c1e0c03811050100123e0f06428114803d1d0c83c120500347a1d0b84d221007a3a1907824060068ec3a1709c3e18890401d0d0480c00d1d078321)))))
def genIndex9 (j : Nat) : Nat := if 4 ≤ j then 0 else (if j<2 then (if j<1 then (0x859e003173cad6736f01b78c7890bf00056dda0ad9c0f001b9fc2b5f800f001e003c007800f00129ba949df3b94a5e001ee950bcf001abf2d0af800f001e003c0030985425e003c007800a1e1a4220918305bdd7d707c007b477415e00398d2257f001e002861b545f001715bc00399e9d830a842e66975f001eb3144e5285f000e0c99887cd02423e000b74f800f00009526f72f4ef0003297c0014dbf001e00103d7800841947374e63721d47fe0034fb71e36351a57259002a5f001a606855e027f001e003c005624e494fbb7516c80449efe0010b559a1f00144558cdf800d4c1e002180f5aae4cbe001c688828f001e0032b5780014ec27dfe4c36dbf54da742b137800f001e003c0070567c4aaa5be4b8a24f001acec741f8001081e003c0078000115a64bc00780010b1e003c007800616af163c007800f000e513c0048daf00169ab0d67800ddf3e002c0ff6998471e003c007800f000a3488438273013fa2d18def800e446ad3fb760a21f001e00330cf8000696a6f385b520db411885285c2c9692932bfbc007800f001e003c007800f001e00145fd8f2f00021d1449f8002c818377c00780049f5e003c0065f2f0004b03c006c39b4c602b67431934707be003c002055e6995a33c0078005631545f50c7800f00127b3c22f9aa53d1e003c006943a681e003c006922f000324ead90a1cf00001dfc000a05f001e0004ec490664dbe9e376cfa53f001e003c0005c41a8fe003c005b22c5c16964f824a3440834ce9348533f6e801688935f800f001a4a3c0076e6bb8fe000f31eb0e782de00265a50facbf9e003c0038eddd39e0028abf800f000dd1a85285e36dd4ba1ceafed3b364a007948e3a00b4bc0bdfa17a21955e384bb488707eaab124a784a7c55f001e9e7c007800f001a6c2517601d6e82f2c3c004f4595a04577c00473ae48ef8136f223023551e0038638177f001ab87c00134ef0010acfc007800f001e0034eff8005321e000c8a78007b8d4af504265c3f0004adfc000afb4462a22379e02caa35da3dbc0039863365e00248c7800f001e003c001947124213bdd7af800f001ac4c0f2e099f000c6dbc0030fb51fdc10aca8f800d1bc642baa5e8d0f001e0034258f4fc623e00020060400440412001c32d10442c030d0850402192fc1050810880d62c000064b1840c20b746c0590010020010c00074c824e38014259335b08b0cb0001000801803cb019001381041a4018d1150403422430c200501e3c7887040047002018150001251140280ec01430c50010821d20070453c005048301a34a3003010411420002800000c704009010a0e510c1c00000010033c604000204638a10008700300524404b01535a1011090002010805c013b4c500d04414810000004410014004350a0430070000410099410d500900000200a) else (0xc005909f001e00009af80070dee9d7c0072072585e0008cef800f000623bc004982ac8250c3859f800f001e00001bca5c45cd237d8bcf80072dbe003c007800b43be00048b780076460a6df5ca304f001681874bb8f1cc0a90d3c007800f001e93bc0054997c0487b90b3f8004523e00356faa372629e003c0054e883af6d07da9b024f001e000ab0f80081d3e00325bb0504234cd1bc001989f0014c6d73f5834f001b5439a1b6bee14627859967800f001e003cf9780043c5e003015c4d2f00146f8541481821e8213bc00627cf0016cb5d6d780033eac1d6425780042e1e003acbf800f0012ce0c397d6cf001e003c00717af001e003c0039a6f00164cfc007800f0010187a8df800b9dc240a47344e4f001e003c007800e9f7e000071f800f001e00240bf800c2a96a0c07af0ff3087e0004e9aa5af000ac676e9f800b56de0016f9c08bf29887c6024fb24c2e72413936032bf53adb229a4faa7f0014217c001148749214c4cb07800a119e003c0031cb99350311801740e605ab7ab0b908ba4158a8bfc007800f001e00342668b1a07c5bdd121f1789af7235f0188df573952c57d15530053763b5e86c403c268b230806cdc28600b457bc00780083e8954984bf80050f2c29fc0040c5f00061f22be08e13515e000c14f8003a6146666527800050c65bb4069aee4a918774546685f45440ccfc0078006315e93542998ef10b86ab3c007800b28c2ac30377800265ca4e19589b1cf000018bc007800f00055454579a89f001e0018cb70713145e0024ed697fb06be0036b23847c3b9eaf0c5d85bd05c478a3c0029fa60d5e000098230d9317c54048644dedbe15d0c0338086f0004977c007800f001c2848cbf8009182738e90f95b8902a2ab836860707d09404fc007f0351947ba25330dfba137772097b387fd0cd2b1145f6ddd42b5a9dc8c2d66000a309318a09ac55dac857c665787d636a233fc00445df001e00148bc0ee11f1e003c0042baf000270fee2f800f001e7e34ff780060b3e003c0078007d996bcd76c22d7abbde0014b0e0dc2061e003d3f7800f001ccd9933d900263d453647cd19a653f2a3c99368fd5e8ed69fc00363f21b644de404f800641707a751ea9cff00024e7c007800f000260240d7800f000847f8a7c2d9731188c91258d4fbbd98d53c003b4275db3737c007800b5c7e003c006a1ef001e003c001d5719a3a5c41203acb94a12086d2af80044ada827c0078001549e502076592af001243bc0078002531849e482b869f001a4fbc00780020012d425647800f001e00243dbae93991e003c007800f001e003c0078000039b173c005a9c446ca5f1994c112d331b627567c6cd2d013797c004b302e904842cf5c08161ef9035ea9c8449456220ef0378002528d6b382f78e78894e747c0001a955a6e0bc0997800c)) else (if j<3 then (0xf001e000095f800a64283910c3ee3e85d56bcbc0002e4f000402fc002337f000d32fc006e10f001e0030b129a361f96383922a9fc54c5e25846058a09593e003c0078006407e0000d8f8005121c6e54e70e271477e003c007a5ff3e73a3469086dd33b3c41d11f780072b3d77fc006a1a15a20517c007800f0004681a8a7e89c025e0028d3f800d403e002b3bc8e5f001e01eeff98d4617be001f45d68e405ce1b2c1cd064002ddbf89762eee8441cafa403780040f0a4c5d6f780054fb6a23c0002c3809be001507cb5262266bf60c67800f001e003c00000ab59de001092412fb3b7e003c007800c63e6ad7c003ac6c0d1cc5a5403b489a75e003c006287cd8022ca514f80092d7c4e809ee665f001e003d55268ff0016b37c0048ae22cbb5ebc002abfc5770c2057c7800f000483917ff96f4571835bc007800bd9f377094901c5f0006549827eec2f001ccbd960f80049ea47aa8e97800e367e001540833908bc87f7c001dd0f001e000c818a6ff00107ffad4e819f3db28f06da78000607e0035309454799be56202a4e85f001e0028133a0285dfa4b7c00206bf0011d10ef3ba7af001e003c007936f001e001452580ff001e001b7e91d4f0012337c007800c66446380b4f8001023e00312275165055e003c0001a2e155e003c005076e3098a134d2212684a30405af492b2a173808d42bf800f001e000d5048a98409f50fc007800f001e001703805af63be003c007800f2cd8208cdfcc52f001e00368e2a463569c388cf2780040375bbfc0038cee259bbc3c007800f000871916db34d7857e003c00409df001e003c001025b52bc54e27c7800f001e003c004410f00068b0c242852e07ee3afc004a68f0008203c0078008615070999538030279cc3f4c8f800f001e003c007800f001e003c0078004546c8971866217a49159d7d833e95f001e00199ac0c8f001ebc0469aad8265181cd6667800f001e003c0078007e3bd6cd4e0f8008b79e003d45f800f00124829a210b075e9e00110db89af001e003c003a9ac2ede003c000822f000284fc007800f000ac5f9a578007cc9c52bc00094b452ec32fc007800f001e003c0075ba60038656156b03af001728fc007800c5d6bc6bc005942f001e003c002233f0014abc0ea8925f001e003365d18d30203beb913f80032d90a3716ef800612bc2469690edafa9d5d0bc00215bf001e003c047800d9a64c2fc0030a6dd11e003c005242f0016227c00327f1df7e003c004a16567be000ad47800e16fe003d4cf800d4e1e003c0059d660b6469412c4241d23d646fc007800c21e0cf3c661cda1393e003c79cac764b7d98835fa5ede9b8d33d6e5b82c6964f7c4172ea2663dee8ea9a891b8f2ad46d30ca78004aade00117d78004a2a65f90d581c7d9e9d6afc0040a89029e0004cfb334651d47c3) else (0x1e0004067800fac5e000aea74ce411f678008ca239e49e87e7c00509ef00124efc00611df0012c4a55c9833c2f7eaa7c007800f000c713c0078008b4c4447c0078001b3183a2c1dfad5f00048a3c00680ed1aaebe479278009071e0030e47800f00174f0692aedcf001e002a4a4a9e633843aaa1c32ab7cbfe6b6d1ada90835e618ccc1e97d6de26083c002e81f001918fc003193229de0004ef7274d9f3e003c002309f001e003c307964f001e000538f08df001e002c9f82e850bbe002ad85adcb08c13774fdf8006c45e003c007800d4d3b6bfc004174c21be003c001c9b818de003c001563d37597d356a0092f00109eed3926caf000e5a281b7800f001e003c002b274193a556ea27800c2c7b83f5115065f001e003c0009e7160f4cfbc00533199ede8c0a2bf1e61b7de003c003264)))
def genData10 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x38372c28221c0f0d0c0b0704003498402824201c180480f0c0a090807060400248858484434282414100c08b222012100a0805040301288858483c30281c14100c00b1411100d09080502012454443c3430241c14100800b221f1815100f0c08070401003044403c38301c1000822181716100d0c0b0801284c3c34302c1c10008110d09080706050220887c7470605c402824201c1804d0f0c090807060400205444342414100c088221f1d1c100805040301284c3c301c14100c008221d1713100d08050201284c3c301c1008007140f0c070401001c44403c38301c1000839372e2b282523221f1d1c100d0c0b080144b4a88c743c34302c1c1000b352b2a110d0908070605022cd4b8aca0402824201c1804b2d2a0f0c09080706040028c494604434282414100c08b3931302e2523221b18171612100a08050403014cb48c5c3c301c14100c00a35312f2b251f1a181511100d090805020144a8786450443c3430241c14100800e231d1713100f0c080704010030444038301c10007100d0c0b0801183c342c1c10006110d08070605021c4028241c180460f0c09080604001c443424100c086100805040301183c301c140c006100d08050201183c301c10080060f0c0704010018403c30201c10040080f0c0704001797385b7235ab4532db1a302ae92d7ac22b0a9f283a72260a4b239a24214a051f39d01b89a118997415c93511f8fc0de8c50b58a809a88b07d86e06085304583802a81d00b8003ff50ffd07ff40ffccbff31ffcc3ff21ffc83ff10ff983fe51ff943fe42ff907fe40ff8cbfe31ff8c3fe21ff883fe10ff583fd51ff543fd42ff507fd40ff4cbfd31ff4c3fd21ff483fd10ff183fc51ff143fc42ff107fc40ff0cbfc31ff0c3fc21ff083fc10fdc43f510)
def genIndex10 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (0x125c5054cf7f0002be74d3c00829455a26d20bc4183183bc23ce5b151404a0f3522b442127e3e042142afb3d731fc00c137c006573c004e6fc00d5c0082f002078f0008cb6053c003242b9db233c008ed7c005cebc00b1d8aa880f6ae17563c00d62bf8da202afe3647c00f00110434ac16df001704aba212d501e0cdf003c00e2a3c00f0010e7f001949f001b3273798e10e67f5b94dfc0045ef06df003803e59fc002405b02d173c00439a4e9cabb4f3058f906f003c00f003c00f003c00f003c00d0439a6f26740ca1dfc007e83c0055960b5f000916768f54b86818b75360842f003c005cbdf2bf001034a40124cf457c00a4e0ca3f003c00a38fce8f003d5fac57c00dca3c00f003c00f003c00f003c0080bbc00e46fc00f0029840293c00f003c00f001337ecf3c70c42bc00442c82db522ca1f002d6689670f9f003c00f519d7f8470171d22ed85f003c008e5593cf0264913298018d4ffd93d06e04ff4348daf003c00da995b6f003c00a537c00f003d18f00143fe29d433f003c00f003701f00318e88dbc00f003c004ab5d683e2b49a5358859f003c00fac3c00f003c00e2ab45b2d499b1f001b8673e9b03a1ad1a50e8ad7948eed2a82b2117411d92126e7c008067c00f0014c2f00007bf00172ef00005a1e048b8d33990775f3f6a554170711a74642a97c000340d5ef00398df003c00e657c00a132cc314b35a9d1d5911762f062f0023147215465c1ebc00f003c005333c00f003c00f00180e4cd955724dbc00f003c0053efc0073ad97390c458ff4f8c2bf003c0050d7c00f000027f003c28c3f3c7d4023c00f001046f003c00f000c79f003c52f003c0073c6012f003c00f003c00a28bb2913c0a416303c001329f8bfe7bc00f003c0040894bff000cb2f003c006939cbd649282f66be4dbf003c00f003c00f000b5101cbc00f003c00f003c00f001b98f003c00f002868f002d3b435148e6d41592c6d7c00621bc004c1a40070fbc00f003541c112dad90b24f4f003c00f003c00e07347e15be73590c1147f003c00240bc00f003112c623c00f001873b14681f8bf7c00f003c00402d829f00284ab95ad5df000727555957e26c396be27d3b67207c7cf000856f000d1ef003c00f001f13037fd9df001331f0021a82bffcdc5082509638ad5b12794b4b3b6d264497c00f002152f003c00f003f26f037c00f003c00f0005a723c8c361513c00e53ddabb68bc00ac3a41a325018146a8425b0ab796346723ff003c00fc35545f003d402e5c0321074849c33f493f000a1140802001c53e96930aa0012cd2051851c20810810013c00001800c400f1c02db54614940614208004700340905224120d3020050180a30020861000411415800040480000000c00411070800cd1c400a40000200114e0420001001c81010801450d2082385) else (0x42bbc007af7589f0014bba5ab839118603794a5d74b10f79af0039b28223c00f002986c5df390bde757df00174f461e70b6236d60f0021b741bccc98cd14401cfbc003c69055723ec6c405a52f62291a10439cc64c14133a35fc00f003c00e5b30b1f003c00f003c00235497af003c00f00003a95dbc008483c00f003c0034c576b165adb8a63007ff000554f00109b10795643cc1cecf002866e66c8583213c00da9fc00f00393513f5582c05cd235c01cff7ed02e08383c002abd998b2ce09734eb801f0000c5f003c0023ab40a52e7c00f003c0082a476936923395225b2a06bbce435a7824c0efc00d52bc00be33c00f0032b2f3f8cd2821c0f6f003c00f00389df003aec534fc0013ba528f002cb6f5ba8d9f002d1d8e474385e3fd08567e4c43e4e826f002d9a4177c001014151f003c0052c3c00e1c645e89aa0ad546bc00f003c007107c00f003c00f000402f003c00f003c00814ed784531f19004c86a9123d55d65173bf003c00713b962f003c00020fc0014e700622e890cfe490929508095f00144b640f590f003c00f003c0025d7c0086b3c00f0035536ccfc00d673c0004158a0267b89cd2f8cf5508f8c8f002db30347c00865d011203fc00b142b68f003c00f001d7261bb914850fc006c97c008ce353d94c9d1324b945fe1d0580f003c0021178aff003c004667c001263ba1a305161637454e719fc00618c896f003130f003c00a566457b43c51f43bfc00f0))
def genData11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def genIndex11 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x348f01e014415ad41e01cef80f01995b4622f01e03c0780523e03c0447f00a26c2a0ea83e01b278098de03c042b653e03c02e2f018b7cc780f0fe0081780f01e0101f80f01e0375f0b14ea4fc05a69bfe03c0780f01e03c07805a1e036e780237e0329780f01e00b764e602547c03db19fe02350a4f01f8f4b0cb85169586192a9347aa1fe91c1b16e2715f00e6b2af8051e577c005e5da85fc0780b800b286f6c52094fc0780b0d75fc0780f0190b95780f01e03cca67ccc67d4a4a1147e28821d47388bbc036180110099c001546082155002340003040)
def generatedLevels : Nat → Packing
  | 5 => (54,6,7,0,0,9,0,genData5)
  | 6 => (606,5,7,0,0,13,0,genData6)
  | 7 => (1133,4,7,0,0,16,0,genData7)
  | 8 => (853,3,7,0,0,17,0,genData8)
  | 9 => (442,2,7,0,0,16,0,genData9)
  | 10 => (47,1,7,0,0,12,0,genData10)
  | 11 => (1,0,7,0,0,0,0,genData11)
  | _ => emptyPacking
def generatedIndex : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 19 115 5 11 6 1 genIndex6
  | 7 => lookupWord 198 1187 6 15 10 1 genIndex7
  | 8 => lookupWord 361 2167 7 16 11 1 genIndex8
  | 9 => lookupWord 281 1689 6 15 10 1 genIndex9
  | 10 => lookupWord 137 831 6 14 9 1 genIndex10
  | 11 => lookupWord 22 145 6 11 6 1 genIndex11
  | _ => fun _ => none
def qF_ : Forest := ⟨507,11,fun i => generatedSamples[i]?.getD (0,0),generatedColumns,[[], [112,97,83]],generatedLevels,generatedIndex⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP5_0 : block qF_ 5 0 54 = true := by
  apply cellsBlock (ar := 6) (rows := 0) (d := 3)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB5 : block qF_ 5 0 54 = true := genP5_0
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
theorem lowGenerated : Lower true (varsX 507) (qG_ 507) 12 :=
  lower_forest (g := qF_) (i := 0) (hints := 51)
    (before_sound generatedKnown generatedPrior) genGeometry genTables
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
end PEqualNP.Outside.L_meta_51432.ForestCore
namespace PEqualNP.Outside.L_meta_51432
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds ForestCore
def graph (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0,3,1,3,0,4,1,4,0,5,2,5,3,5,0,6,2,6,4,6,5,6,0,7,1,7,2,7,3,7,4,7,5,7] : List ℕ).length / 2,(List.ofFn x).getD (([0,3,1,3,0,4,1,4,0,5,2,5,3,5,0,6,2,6,4,6,5,6,0,7,1,7,2,7,3,7,4,7,5,7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0,3,1,3,0,4,1,4,0,5,2,5,3,5,0,6,2,6,4,6,5,6,0,7,1,7,2,7,3,7,4,7,5,7] : List ℕ).getD (2 * i + 1) 0) false = true)
def coding : Fin 8 → Nat := ![0,1,2,3,4,5,6,7]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def roots : List Sig := List.ofFn (fun i : Fin 8 => inputs.getD (coding i) zero)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def codedGraph : Sig := 0xfffffffffffffffefffffffffffffffefffffffffffffefafffefffaeeeeee00fffffffffffffffefffffffffffffffefffffffffffffefafffefffaeeeeee00
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wholeBound : Lower true roots codedGraph 13 := by
  have h := lift_ok (u := true) (ms := fixRows 4 0) (raw := roots) (T := codedGraph)
    (xs := [(inputs.getD 2 zero,32,36)]) (by decide +kernel) (qP_ _ (by decide +kernel))
    (qP_ _ (by decide +kernel)) lowGenerated
  have count : (([(inputs.getD 2 zero,32,36)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
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
def upperGates : List Gate := [⟨.or, [1,0]⟩, ⟨.or, [7,5]⟩, ⟨.or, [7,6]⟩, ⟨.or, [2,0]⟩, ⟨.or, [11,3]⟩, ⟨.or, [7,4]⟩, ⟨.or, [13,3]⟩, ⟨.or, [11,5]⟩, ⟨.or, [15,4]⟩, ⟨.and, [8,14]⟩, ⟨.and, [16,10]⟩, ⟨.and, [12,9]⟩, ⟨.or, [17,18]⟩, ⟨.or, [20,19]⟩]
theorem upper_shape : ∀ g ∈ upperGates,(g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [upperGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem upper_sem : ∀ x : Fin 8 → Bool,
    Circuit.eval ⟨upperGates,21⟩ (List.ofFn x) = graph x := by
  decide +kernel
end PEqualNP.Outside.L_meta_51432
open PEqualNP.Outside.L_meta_51432 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_51432 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
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
