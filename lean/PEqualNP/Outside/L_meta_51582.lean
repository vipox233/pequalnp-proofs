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
namespace PEqualNP.Outside.L_meta_51582
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
  if m.testBit 8 then (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 0 &&& x 7) ||| (x 1 &&& x 4) ||| (x 1 &&& x 5) ||| (x 1 &&& x 6) ||| (x 1 &&& x 7) ||| (x 2 &&& x 5) ||| (x 2 &&& x 6) ||| (x 2 &&& x 7) ||| (x 3 &&& x 6) ||| (x 3 &&& x 7) ||| (x 4 &&& x 6) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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
  if m.testBit 8 then (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 0 &&& x 7) ||| (x 1 &&& x 4) ||| (x 1 &&& x 5) ||| (x 1 &&& x 6) ||| (x 1 &&& x 7) ||| (x 2 &&& x 5) ||| (x 2 &&& x 6) ||| (x 2 &&& x 7) ||| (x 3 &&& x 6) ||| (x 3 &&& x 7) ||| (x 4 &&& x 6) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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
end PEqualNP.Outside.L_meta_51582
namespace PEqualNP.Outside.L_meta_51582.ForestCore
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
def K211 := extendKnown K173 7 [(211,[]),(217,[64,49,33,118]),(242,[80,32,50]),(244,[64,33,16,49,83,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V211 : Known true K211 := extend_ok (m:=211) V173 low211 (by decide +kernel)
def g213Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (0x7ff003ffffe03ffff001ff80ffc0069abc81c0)),(BitVec.ofNat 152 (0x12a5a94a2a458a12a2d4251a148b029aacb6db))),(0x0,0x0),((BitVec.ofNat 152 (0x7ffffc00ffffc07ffffe0000fffff8da038e07)),(BitVec.ofNat 152 (0x4c1306c0c891304c098362c19124892039249))),(0x0,0x0),((BitVec.ofNat 152 (0x7fffffff0000007fffffffff00000ff10e0038)),(BitVec.ofNat 152 (0x4701c0708f0e1c4708e138309e1c0fd10a5b6d))),(0x0,0x0),((BitVec.ofNat 152 (0x800000000000007fffffffffffff99af6d703f)),(BitVec.ofNat 152 (0x1806018030102018030040002000102c242492))),((BitVec.ofNat 152 (0xffffffffffffff800000000000006754f2ffc0)),(BitVec.ofNat 152 (0x60080200c00000600c018040c0202540504924))),(0x0,0x0)]
def g213C : List ColumnInfo := [(1,0,212,0,5)]
def g213A : List (List Nat) := [[],[64,118]]
def g213D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g213L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g213D5)
  | _ => emptyPacking
def g213I (_ _ : Nat) : Option (Nat × Nat) := none
def g213 : Forest := ⟨213,5,fun i => g213Y[i]?.getD (0,0),g213C,g213A,g213L,g213I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213P5_0 : block g213 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g213B5 : block g213 5 0 1=true := g213P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213T : checkedTables g213 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g213 0 0 0 = true)
  · exact (rfl : block g213 1 0 0 = true)
  · exact (rfl : block g213 2 0 0 = true)
  · exact (rfl : block g213 3 0 0 = true)
  · exact (rfl : block g213 4 0 0 = true)
  · exact g213B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213G : graphValid g213 (boundsBefore K211) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low213 : Lower true (varsX 213) (qG_ 213) 6 := lower_forest (g:=g213) (i:=0) (hints:=33949191) (before_sound K211 V211) g213G g213T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K213 := extendKnown K211 6 [(213,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V213 : Known true K213 := extend_ok (m:=213) V211 low213 (by decide +kernel)
def g227Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (0xffc01ff87fc3fff00ffff1ffed2e680007c1f)),(BitVec.ofNat 152 (0x222894451108808a4a0a02444252268a5294a5))),((BitVec.ofNat 152 (0xffffe0007ffc3ffff00ffffe11773400f83e0)),(BitVec.ofNat 152 (0x40b018162050082c0c2c140089146346318c63))),(0x0,0x0),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (0xffffffff80003ffffff001ffce8f541f0001f)),(BitVec.ofNat 152 (0x84c12098026111301030588900a8d154a5294a))),((BitVec.ofNat 152 (0xf0000000000003ffffffffe0005f98fe0003e0)),(BitVec.ofNat 152 (0x701c0e0438221c06040600e104b9898c6318c))),((BitVec.ofNat 152 (0xfffffffffffffc000000000003280bbffffc00)),(BitVec.ofNat 152 (0x8020100040002008080801000000021084210))),(0x0,0x0)]
def g227C : List ColumnInfo := [(1,0,226,0,5),(2,0,225,0,5),(32,0,195,0,5),(64,0,163,0,5),(33,0,194,0,4),(66,0,161,0,4)]
def g227A : List (List Nat) := [[],[97],[16,101],[16,80,96],[80],[80,97],[96,16,81],[96,81]]
def g227D4 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x31825f63547409bd89544426d6215110)
def g227D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (0xc110204810001882188201141080d176bcc8d018160c02faa3a07bd4940bfa8a81fb40502fea8885f95110beaa2217c54443f280885bd4940)
def g227H5 (j : Nat) : Nat := if 1 ≤ j then 0 else (189208 * 1000000000000000000 + 253964038873192720)
def g227D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x3140cc503540a0380ff40fd40fd10)
def g227H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (0xd4f4400e18d31640021400003c7f1000c2000000000034200143f0400a0000585c9002571)
def g227D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1605f
def g227H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (0xc4005e51200000000000e10307400003c4012a00003a400000010254000020000005)
def g227L : Nat → Packing
  | 4 => (3,3,3,0,0,4,0,g227D4)
  | 5 => (10,2,3,0,0,7,0,g227D5)
  | 6 => (3,1,3,0,0,6,0,g227D6)
  | 7 => (1,0,3,0,0,0,0,g227D7)
  | _ => emptyPacking
def g227I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 11 0 8 2 2 g227H5
  | 6 => lookupWord 4 29 1 10 4 2 g227H6
  | 7 => lookupWord 3 31 1 9 2 3 g227H7
  | _ => fun _ => none
def g227 : Forest := ⟨227,7,fun i => g227Y[i]?.getD (0,0),g227C,g227A,g227L,g227I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227P4_0 : block g227 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g227B4 : block g227 4 0 3=true := g227P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227P5_0 : block g227 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227P5_1 : block g227 5 1 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g227B5 : block g227 5 0 10=true := (@block_merge g227 5 0 1 9 g227P5_0 g227P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227P6_0 : block g227 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g227B6 : block g227 6 0 3=true := g227P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227P7_0 : block g227 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g227B7 : block g227 7 0 1=true := g227P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227T : checkedTables g227 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g227 0 0 0 = true)
  · exact (rfl : block g227 1 0 0 = true)
  · exact (rfl : block g227 2 0 0 = true)
  · exact (rfl : block g227 3 0 0 = true)
  · exact g227B4
  · exact g227B5
  · exact g227B6
  · exact g227B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227G : graphValid g227 (boundsBefore K213) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low227 : Lower true (varsX 227) (qG_ 227) 8 := lower_forest (g:=g227) (i:=0) (hints:=16777317) (before_sound K213 V213) g227G g227T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K227 := extendKnown K213 8 [(227,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V227 : Known true K227 := extend_ok (m:=227) V213 low227 (by decide +kernel)
def g63Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (0xfffffffffffffffffffb944e4fa4fd6803f03f)),(BitVec.ofNat 152 (0x282a00a128028520214b844c0320dc00145145))),((BitVec.ofNat 152 (0xffff000003fffff000076ab5eb70a632000fc0)),(BitVec.ofNat 152 (0x14c280db0a02642066762344a50a4324d34d3))),((BitVec.ofNat 152 (0xfffffffffc000000000067c4351bd4f7fc0000)),(BitVec.ofNat 152 (0xb27002c9c00b37804b8026c43508d4f33cf3cf))),((BitVec.ofNat 152 (0xfffffffffffffffffff58b1674957bf000003f)),(BitVec.ofNat 152 (0xc380b30e02cc38048c040b12749523f0ebaeba))),((21453 * 1000000000000000000 + 254836694424752064),(BitVec.ofNat 152 (0xfc00c3f0030fc008f00088cbb5a9420cb2cb2c))),((68276 * 1000000000000000000 + 774967573781409792),(BitVec.ofNat 152 (0xfc0003f0000f000451028857220cc30c30))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63C : List ColumnInfo := [(0,2,45,16,5)]
def g63A : List (List Nat) := [[],[65],[80,50],[80,65,50]]
def g63D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g63L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g63D5)
  | _ => emptyPacking
def g63I (_ _ : Nat) : Option (Nat × Nat) := none
def g63 : Forest := ⟨63,5,fun i => g63Y[i]?.getD (0,0),g63C,g63A,g63L,g63I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P5_0 : block g63 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B5 : block g63 5 0 1=true := g63P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63T : checkedTables g63 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g63 0 0 0 = true)
  · exact (rfl : block g63 1 0 0 = true)
  · exact (rfl : block g63 2 0 0 = true)
  · exact (rfl : block g63 3 0 0 = true)
  · exact (rfl : block g63 4 0 0 = true)
  · exact g63B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63G : graphValid g63 (boundsBefore K227) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (varsX 63) (qG_ 63) 6 := lower_forest (g:=g63) (i:=0) (hints:=66883) (before_sound K227 V227) g63G g63T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K63 := extendKnown K227 6 [(63,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V63 : Known true K63 := extend_ok (m:=63) V227 low63 (by decide +kernel)
def g95Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (0x1ffffffffffffffffdd22222ff857c000001f)),(BitVec.ofNat 152 (0x2d14154509514290851d222027b017ab5ad6b5))),((BitVec.ofNat 152 (0xffffff80001ffff8003adda05ba07880007fe0)),(BitVec.ofNat 152 (0x4800a6006d80132019ba19a04a007086318c63))),((BitVec.ofNat 152 (0x1ffffffffe0000000033421e54bfc800f8000)),(BitVec.ofNat 152 (0x705938164e059bc12e023421654bfc9ef7bdef))),((BitVec.ofNat 152 (0x1ffffffffffffffffcc58e7684e4f41f0001f)),(BitVec.ofNat 152 (0x8061c01870061c02300058c3484e4854a5294a))),((BitVec.ofNat 152 (0xfe000000000000000004579a17773c3e0003e0)),(BitVec.ofNat 152 (0x7e001f8007e003c004441215770c18c6318c))),(0x0,0x0),((243983 * 1000000000000000000 + 393810807020059648),(BitVec.ofNat 152 (0x1800060001800040001820c80800121084210))),(0x0,0x0),(0x0,0x0)]
def g95C : List ColumnInfo := [(4,0,91,0,7)]
def g95A : List (List Nat) := [[],[65]]
def g95D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g95L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g95D7)
  | _ => emptyPacking
def g95I (_ _ : Nat) : Option (Nat × Nat) := none
def g95 : Forest := ⟨95,7,fun i => g95Y[i]?.getD (0,0),g95C,g95A,g95L,g95I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P7_0 : block g95 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B7 : block g95 7 0 1=true := g95P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95T : checkedTables g95 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g95 0 0 0 = true)
  · exact (rfl : block g95 1 0 0 = true)
  · exact (rfl : block g95 2 0 0 = true)
  · exact (rfl : block g95 3 0 0 = true)
  · exact (rfl : block g95 4 0 0 = true)
  · exact (rfl : block g95 5 0 0 = true)
  · exact (rfl : block g95 6 0 0 = true)
  · exact g95B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95G : graphValid g95 (boundsBefore K63) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low95 : Lower true (varsX 95) (qG_ 95) 8 := lower_forest (g:=g95) (i:=0) (hints:=16844355) (before_sound K63 V63) g95G g95T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K95 := extendKnown K63 8 [(95,[]),(126,[80,50]),(159,[64,16,49,118]),(190,[64,33,49,80,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V95 : Known true K95 := extend_ok (m:=95) V63 low95 (by decide +kernel)
def g111Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (0xffffffffffffffffffd961ba3aa853c00003ff)),(BitVec.ofNat 152 (0x28802a402520148051921322280139294a529))),((BitVec.ofNat 152 (0x1ffff00007fffc003eda224bb248800f8000)),(BitVec.ofNat 152 (0x54c294c15b60a99099be58224b32488e739ce7))),((BitVec.ofNat 152 (0x1ffffffff8000000073423e149fc81f07c00)),(BitVec.ofNat 152 (0x2700270013800de02e0230236108f486318c63))),((BitVec.ofNat 152 (0x1fffffffffffffffc858e56c4e4f7e00001f)),(BitVec.ofNat 152 (0xb80338019c00ce01300058c14c4a4c4c6318c6))),(0x0,0x0),((BitVec.ofNat 152 (0xffe00000000000000004579a17773c00007fe0)),(BitVec.ofNat 152 (0xc013c009e004f001c0044688147708294a5294))),((243983 * 1000000000000000000 + 393810807020027904),(BitVec.ofNat 152 (0x1c000e000700020001821c808501318c6318))),(0x0,0x0),(0x0,0x0)]
def g111C : List ColumnInfo := [(2,0,109,0,7)]
def g111A : List (List Nat) := [[],[80,50]]
def g111D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g111L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g111D7)
  | _ => emptyPacking
def g111I (_ _ : Nat) : Option (Nat × Nat) := none
def g111 : Forest := ⟨111,7,fun i => g111Y[i]?.getD (0,0),g111C,g111A,g111L,g111I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7_0 : block g111 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B7 : block g111 7 0 1=true := g111P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111T : checkedTables g111 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0 = true)
  · exact (rfl : block g111 1 0 0 = true)
  · exact (rfl : block g111 2 0 0 = true)
  · exact (rfl : block g111 3 0 0 = true)
  · exact (rfl : block g111 4 0 0 = true)
  · exact (rfl : block g111 5 0 0 = true)
  · exact (rfl : block g111 6 0 0 = true)
  · exact g111B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111G : graphValid g111 (boundsBefore K95) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low111 : Lower true (varsX 111) (qG_ 111) 8 := lower_forest (g:=g111) (i:=0) (hints:=16778595) (before_sound K95 V95) g111G g111T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K111 := extendKnown K95 8 [(111,[]),(125,[65])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V111 : Known true K111 := extend_ok (m:=111) V95 low111 (by decide +kernel)
def g119Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (0xffffffc0003fffc00ad27ec6ac340000000fc0)),(BitVec.ofNat 152 (0x25104a90da9094856ac27ec2a03404d34d34d3))),((BitVec.ofNat 152 (0x3ffffffffffffff720988afa71b000fc003f)),(BitVec.ofNat 152 (0x98213021302190243209888e801a145145145))),((BitVec.ofNat 152 (0x3fffffffc0000009cd1cb9421e203f03f000)),(BitVec.ofNat 152 (0x4e009c009c00de0b88441cb8421c20c30c30c3))),(0x0,0x0),((BitVec.ofNat 152 (0x3ffffffffffffffa162d5a1393dfc000003f)),(BitVec.ofNat 152 (0x7004e004e004e00c081625121312128a28a28a))),((BitVec.ofNat 152 (0xffc00000000000000915e285ddcf000003ffc0)),(BitVec.ofNat 152 (0x27002700270010011180051dc30b2cb2cb2c))),((BitVec.ofNat 152 (0x4ea977125e06ffffc0000)),(BitVec.ofNat 152 (0x80380038003800200488024104e04c30c30c30))),(0x0,0x0),(0x0,0x0)]
def g119C : List ColumnInfo := [(1,0,118,0,7)]
def g119A : List (List Nat) := [[],[65]]
def g119D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g119L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g119D7)
  | _ => emptyPacking
def g119I (_ _ : Nat) : Option (Nat × Nat) := none
def g119 : Forest := ⟨119,7,fun i => g119Y[i]?.getD (0,0),g119C,g119A,g119L,g119I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P7_0 : block g119 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B7 : block g119 7 0 1=true := g119P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119T : checkedTables g119 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g119 0 0 0 = true)
  · exact (rfl : block g119 1 0 0 = true)
  · exact (rfl : block g119 2 0 0 = true)
  · exact (rfl : block g119 3 0 0 = true)
  · exact (rfl : block g119 4 0 0 = true)
  · exact (rfl : block g119 5 0 0 = true)
  · exact (rfl : block g119 6 0 0 = true)
  · exact g119B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119G : graphValid g119 (boundsBefore K111) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low119 : Lower true (varsX 119) (qG_ 119) 8 := lower_forest (g:=g119) (i:=0) (hints:=16844101) (before_sound K111 V111) g119G g119T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K119 := extendKnown K111 8 [(119,[]),(123,[80,50])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V119 : Known true K119 := extend_ok (m:=119) V111 low119 (by decide +kernel)
def g175Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (0xfffffffffffffffffff83ab722001c3fc01d4e)),(BitVec.ofNat 152 (0x29014005401280290298083422492444402948))),((BitVec.ofNat 152 (0xff800fffe0003fff800ee9901800e00020e17f)),(BitVec.ofNat 152 (0xb22a65298adb15324ccee99019fffdddc0617f))),((BitVec.ofNat 152 (0xfffffffc0000004485df40703c0070875)),(BitVec.ofNat 152 (0x3c13804e009c01bc17004855b4db6cccc20a55))),((BitVec.ofNat 152 (0xfffffffffffffe319cb82380003c80fb7)),(BitVec.ofNat 152 (0xc05c06700ce019c0180311cb81b6d9998006b7))),(0x0,0x0),((BitVec.ofNat 152 (0xfffff0000000000000047738edc003fc3000ba)),(BitVec.ofNat 152 (0x6007800f001e0060043708492491112044a2))),(0x0,0x0),((129962 * 1000000000000000000 + 219234010589033153),(BitVec.ofNat 152 (0x8001000200000000000000002221c9000))),(0x0,0x0)]
def g175C : List ColumnInfo := [(2,0,173,0,7),(1,0,174,0,6),(4,0,171,0,6),(8,0,167,0,6),(32,0,143,0,6),(0,2,45,128,5),(3,0,172,0,5),(6,0,169,0,5),(9,0,166,0,5),(12,0,163,0,5),(34,0,141,0,5),(36,0,139,0,5),(11,0,164,0,4),(128,0,45,0,4),(128,2,45,0,4)]
def g175A : List (List Nat) := [[],[80,50]]
def g175D3 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x6304c865085585504826832642ac2a82419818750f5150120)
def g175D4 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x8e080000000000009820000002684100043820000000000000000401f4f4773a1c4dc6b32184bc5b2c154a44f26114843f1e0e45c2b140843c1b0c054240f060240c0300235e0d70d85528d584dcd60d4635e0d70995218e7825d36154239e0976d45409e180dc5544826961075585209c5831d56148361dd143585209a7845db5148271e0d76d45208e7865d35148278e1170d4520dc3835c3514837050d70d4520b298419550482d260c65541209c88750d50483c25514354120b60855855048398d956154120d8b7550d40483625d54350120f81435c540482e8e116150120f8143585404827861f5150120ba184d4540483e050f51501208b7845db5148235e0d76d45209e3805cb514827860275485208e7825d265442a56126550d109d08750d50443c45514354110)
def g175H4 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x940000d80000000900000)
def g175D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x181000000000000000007021c10000000000e093040040804c10e080d08041da051da04000000cc10002608001304090087a6106a61004c1040001810e0800004c1000000000012000a98200000c040640a004703801800d1054024e1700f1dc5f11c2f05bfef9bcee6b82dab52ceb22c2af2b6ac2aaa9297a2a849fa789ca6c99a59932468e63389a1984dff7add7745cb715bf6c9ac6999964d8d6017a5b5595153f4ad2547d12414ff3e4f3398e0368d4338c8308bc2a09b2548f2247c1d8691704f108350a01b0026fb9ac1a94f570d85529eee0b16a33ddd160d476bb9ac1a8cf77258351baee6b06a33d5c265486f3b82a490cef72593509bae9b1aa1b5dc7635427aba6c2a84f572d8550daec7b0aa1b5d8f515436bb1a42a84ef72595409eaeda8a817c5c3515039caa2a0a05e571d9520b5ee8b2a4173dcd65482f3b8aca905ad7419520b9ae632a41795c465482f2b8ec8905e970d51209deecaa2413b1d954482f3b8aa8907cb7050d20bc8eab0a41b9d956148372b2ac2905e77458520f8a86b0a4179ddb51482f2bb6a2905e574d4520f8a87a8a41f85c351483b5b2aa0907686554120bd6e8a8241dad5150483b4aa2a0907cb7354120f9286a8241f8dc550483f0b0aa0907e35154120bd6eaa02417a5d540483d5b2280907a95450120fc2e2a0241f858540483f1a8a80904bf74595209bee6b2a417a5c352482f3b8aa4905eb70549209eaeda8a41795cb51482f8b86a2905e67548520dceca90a41b959521483f090aa0904f574995109eae532a2179dc9544436abb286886d66550d10f2aa8a1a21f4dc143443b8aa2a0887d37354110fa286a822135dcd60d46f0b86a2907894350120)
def g175H5 (j : Nat) : Nat := if 1 ≤ j then 0 else (0xf3781c00680609e780000063000000381dbe00085d8d023e2b8ca90000e300481292800000000943c5400000ab344fc72a3000880cd00693855ac79c1b0a32f8b5a24c1d28006977800000048200087c0009d001724c1c08e4994c0004253692011d20)
def g175D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x608070868010a08018a09a38498a10401c1807042860067020821e010a0046d000668d18719c38628010a18400850c10a09c0840a01a00a89a01a89840a02848281a0584a028060a010a08018a20600880212070430e10b10472780420c91c18c7054802d621acb619ac0549b5867163870e01002d01a14561a7160a422e83d01c4850185810185810a0858f40741a13741c1a6dcc1d0d9c19031c1cc29612624647a8d11421f426835039fe3ea7a4ee9d13906e4d81aa348660c91862e85a0af9532944f89792623a450858fc1e039c6c0cc1862dc558a212c2283c06c0c0150228390600900c00c000bf58352fdd8552bfd8152fd58b51fd54b51fd58351bf59350bf58b50bfd9150dfd5150df55150f7d8d50bfd8950fdd8550fdd4550fd48550bfd9540bf59540fd58540fdd4540fe54140fbd9520fb99520fb59520fb19520fbd9120fb59120fbd5120fb55120bfd9520bf59520fbd4920fb54920fd58520fdd4520fe54120fd55110fd54910bdd8552bd58b51bd58351bd99521f954921b7d8d50bdd8550f9d4720f350d20f958520f9d4520fa54120fa50120f948520bd99510bd59110f550d10bd58910fc54110)
def g175H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (0xe9f30bc4eb3c04600000000000000084900000000000000084d000000000000000353000000a13000000c36000d2864a93bf09a0482bf0ac2083933d340719199db5548000000286000000000000000d520000000000001342266b8585db711600028a00022c227000000000000000bc2000000000000000000883a1e00000049e00000000000000013e24c000c06937000000000000e87000000000000047000000418000000000fc400051200000054b00800000000000000000052d000000000f3a000454a38000000000000000000000000000e32000000a2a0001b4b9b000c2211b00001da4f030000a2500000000000042f0000004a500031a8210003410000000000000000006510000000000007a300000000000000061ce45000000000000000000000000e8900000f000505d23f31000000000f3f00069c000000e00000207000000000aaca0df2ee15000601000210942e4400000000013300000041100050c0007af000803000000000000602000000000000000000155b5000000000000024300000071700010e51f429f24514388235304180019010015150700008200)
def g175D7 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x14c16e15c14c162905043857105040ae82d023a0858990377815d14ace2c10b0c54820476d061230f96d2ed428734124681a007fd4bfaa5ff50fea87f503fa41f751fa90fbc83da41f510)
def g175H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x31a46508f91336000518002ab00e4a808ee4000002b57ef5320000000033600000000a2a31000000b282bc0000011629348156f1c0018c3b19005d3ea00000000000000b6eab0000000015cc00000000a1400000000000002cb0006c0007340124495065db708340040345c074000009a1e4c00128000003e7d0881521b935810000028b800000858007a7aeb0300060425bca42400000169400000000000ce05c26b14710c9f105879e160f001ccc3302c80027a2100283040a)
def g175D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x9b8013f
def g175H8 (j : Nat) : Nat := if 1 ≤ j then 0 else (0xa1014008a0034b0e31eb80001307302400ba9a803303300000400064003c7e10066609100401)
def g175L : Nat → Packing
  | 3 => (3,5,4,0,0,4,0,g175D3)
  | 4 => (37,4,4,0,0,9,0,g175D4)
  | 5 => (86,3,4,0,0,10,0,g175D5)
  | 6 => (57,2,4,0,0,11,0,g175D6)
  | 7 => (11,1,4,0,0,9,0,g175D7)
  | 8 => (1,0,4,0,0,0,0,g175D8)
  | _ => emptyPacking
def g175I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 17 0 6 2 0 g175H4
  | 5 => lookupWord 11 67 5 11 6 1 g175H5
  | 6 => lookupWord 27 271 4 12 7 1 g175H6
  | 7 => lookupWord 18 127 5 11 6 1 g175H7
  | 8 => lookupWord 5 31 5 9 4 1 g175H8
  | _ => fun _ => none
def g175 : Forest := ⟨175,8,fun i => g175Y[i]?.getD (0,0),g175C,g175A,g175L,g175I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P3_0 : block g175 3 0 3=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B3 : block g175 3 0 3=true := g175P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P4_0 : block g175 4 0 37=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B4 : block g175 4 0 37=true := g175P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P5_0 : block g175 5 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P5_3 : block g175 5 3 83=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B5 : block g175 5 0 86=true := (@block_merge g175 5 0 3 83 g175P5_0 g175P5_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P6_0 : block g175 6 0 19=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P6_19 : block g175 6 19 38=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B6 : block g175 6 0 57=true := (@block_merge g175 6 0 19 38 g175P6_0 g175P6_19)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P7_0 : block g175 7 0 5=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P7_5 : block g175 7 5 6=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B7 : block g175 7 0 11=true := (@block_merge g175 7 0 5 6 g175P7_0 g175P7_5)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P8_0 : block g175 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B8 : block g175 8 0 1=true := g175P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175T : checkedTables g175 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g175 0 0 0 = true)
  · exact (rfl : block g175 1 0 0 = true)
  · exact (rfl : block g175 2 0 0 = true)
  · exact g175B3
  · exact g175B4
  · exact g175B5
  · exact g175B6
  · exact g175B7
  · exact g175B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175G : graphValid g175 (boundsBefore K119) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low175 : Lower true (varsX 175) (qG_ 175) 9 := lower_forest (g:=g175) (i:=0) (hints:=1395) (before_sound K119 V119) g175G g175T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K175 := extendKnown K119 9 [(175,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V175 : Known true K175 := extend_ok (m:=175) V119 low175 (by decide +kernel)
def g183Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (0xfffffffe0003fff801d61939a64a20000f83e0)),(BitVec.ofNat 152 (0x489402540da81290ad541930a24a20c6318c63))),((BitVec.ofNat 152 (0xfc00fffffffffffffe600516ffc95801f0001f)),(BitVec.ofNat 152 (0x902610982130432048600412fe40514a5294a5))),((BitVec.ofNat 152 (0xfffffffc00000139c4f2134e803e007c00)),(BitVec.ofNat 152 (0xe13804e009c01bc1711184b2134e00c6318c63))),(0x0,0x0),((BitVec.ofNat 152 (0xffffffffffffff428bea0b99e80000001f)),(BitVec.ofNat 152 (0x1c0a7014e029c0181028be80199aeb5ad6b5a))),((BitVec.ofNat 152 (0xffff0000000000000122fa117cb687c0007fe0)),(BitVec.ofNat 152 (0x38007000e002002260014c908318c6318c))),(0x0,0x0),((742129 * 1000000000000000000 + 573845209073025024),(BitVec.ofNat 152 (0x200c001800300040088024c00210421084210))),(0x0,0x0)]
def g183C : List ColumnInfo := [(1,0,182,0,7)]
def g183A : List (List Nat) := [[],[32]]
def g183D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g183L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g183D7)
  | _ => emptyPacking
def g183I (_ _ : Nat) : Option (Nat × Nat) := none
def g183 : Forest := ⟨183,7,fun i => g183Y[i]?.getD (0,0),g183C,g183A,g183L,g183I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P7_0 : block g183 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g183B7 : block g183 7 0 1=true := g183P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183T : checkedTables g183 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g183 0 0 0 = true)
  · exact (rfl : block g183 1 0 0 = true)
  · exact (rfl : block g183 2 0 0 = true)
  · exact (rfl : block g183 3 0 0 = true)
  · exact (rfl : block g183 4 0 0 = true)
  · exact (rfl : block g183 5 0 0 = true)
  · exact (rfl : block g183 6 0 0 = true)
  · exact g183B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183G : graphValid g183 (boundsBefore K175) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low183 : Lower true (varsX 183) (qG_ 183) 8 := lower_forest (g:=g183) (i:=0) (hints:=66885) (before_sound K175 V175) g183G g183T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K183 := extendKnown K175 8 [(183,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V183 : Known true K183 := extend_ok (m:=183) V175 low183 (by decide +kernel)
def g207Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (0x7ffc01ffffffffffffc035677a50000f000f)),(BitVec.ofNat 152 (0xd01482c82a425214829c035454a5555555555))),((BitVec.ofNat 152 (0x7ffffffff0007ffc00f354385e8000f000f0)),(BitVec.ofNat 152 (0x5615914814c1b60990ccf304385e8333333333))),((BitVec.ofNat 152 (0xff800001ffffff80000026278cbf400f000f00)),(BitVec.ofNat 152 (0x9819e2702701380de17026078c3f4333333333))),((BitVec.ofNat 152 (0x1fffffffffffe580f6a35b0f000f00f)),(BitVec.ofNat 152 (0xe01e03803801c00e0180180a2a358222222222))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (0xfffffffe00000000000024f859c3ef0000fff0)),(BitVec.ofNat 152 (0x200000c0060030020000f041802444444444))),((7591 * 1000000000000000000 + 16750954317807616),(BitVec.ofNat 152 (0x400001000800400000000000000888888888))),(0x0,0x0)]
def g207C : List ColumnInfo := [(2,0,205,0,7)]
def g207A : List (List Nat) := [[],[33]]
def g207D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g207L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g207D7)
  | _ => emptyPacking
def g207I (_ _ : Nat) : Option (Nat × Nat) := none
def g207 : Forest := ⟨207,7,fun i => g207Y[i]?.getD (0,0),g207C,g207A,g207L,g207I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207P7_0 : block g207 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g207B7 : block g207 7 0 1=true := g207P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207T : checkedTables g207 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g207 0 0 0 = true)
  · exact (rfl : block g207 1 0 0 = true)
  · exact (rfl : block g207 2 0 0 = true)
  · exact (rfl : block g207 3 0 0 = true)
  · exact (rfl : block g207 4 0 0 = true)
  · exact (rfl : block g207 5 0 0 = true)
  · exact (rfl : block g207 6 0 0 = true)
  · exact g207B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207G : graphValid g207 (boundsBefore K183) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low207 : Lower true (varsX 207) (qG_ 207) 8 := lower_forest (g:=g207) (i:=0) (hints:=16778851) (before_sound K183 V183) g207G g207T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K207 := extendKnown K183 8 [(207,[]),(222,[64,33,49,118]),(238,[80,50,64])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V207 : Known true K207 := extend_ok (m:=207) V183 low207 (by decide +kernel)
def g215Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (0xfe007ffe0007ffe00a64598b000700004cc0fd)),(BitVec.ofNat 152 (0xa44b12545b514a456a44598b3bbb777700c0fd))),((BitVec.ofNat 152 (0xfffffffffffffffff783e1e0807800ff11023d)),(BitVec.ofNat 152 (0xc812009802600c82478281808889111100401c))),((BitVec.ofNat 152 (0x7ffffff8000001dc843307800f00220c5f)),(BitVec.ofNat 152 (0xf09c04e013806f0381d48433199b3333000a1f))),(0x0,0x0),((BitVec.ofNat 152 (0x7ffffffffffff214f06d8000f00fbc3287)),(BitVec.ofNat 152 (0xe047011c047004001470655556aaaaac0a83))),(0x0,0x0),((BitVec.ofNat 152 (0xffff800000000000011b0b1f7800fff0c03de8)),(BitVec.ofNat 152 (0x180060018008000908082220444440a160))),((BitVec.ofNat 152 (0xce43e807fff0000ffc112)),(BitVec.ofNat 152 (0x1006001800600100020220044448888bb0000))),(0x0,0x0)]
def g215C : List ColumnInfo := [(1,0,214,0,7),(4,0,211,0,7),(0,1,86,128,6),(2,0,213,0,6),(16,0,199,0,6),(3,0,212,0,5),(4,1,82,128,5),(5,0,210,0,5),(17,0,198,0,5),(18,0,197,0,5),(64,0,151,0,5),(128,0,86,0,5),(128,1,86,0,5),(6,0,209,0,4),(65,0,150,0,4),(68,0,147,0,4),(132,0,82,0,4)]
def g215A : List (List Nat) := [[]]
def g215D4 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x120224040000000000000000d99b05184f1b305490f182430300b0d821915454ec56046455153d477454d514867121d5350521d457554d41487c15515350521da374505604863a60772593508eb825db43d423ae0976d07508eb825d941d423661b73507508eb8759121d42b8e116148750ae18650521d43a85914148750)
def g215D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x62058818c040000000000620400308100000000101040708103c20b08108049010090100b01240402c0490124010800d04901022414207048010d64070c0000000000000001810190100181640490b38038b052c1b0abcadab0aaaa4a5a889ea749ba6898a5c95a5090a3c8da2888a1c85a10829fc7b9e0729bc6b9a06698c619785a964559484c92c47910428f4398d82e8b42b8a82889c25890228841f8701a85c158480e81c038009bee6b0ca93b5c762552e7b92c8a9dd77159153b9ae4322a7755c46454f8fb22a8a9f1c6455153e9ee4aa2a757dc55454e77b92cba1e5d6554f439dee4b2a873ddc56550f2fb2aa6a1e5f6454d51eaee2a9aa33bdc965d072eb2aa7a0f1d5454f419bee6b2a833bdc9655066ebaec6a0ed970d8d419bceca9a83371d9535072eb2aa6a0f1d5454d41e6aa8a8a83d554d515076db1ac0a0de57199121b9ee6b2243795c65448677bb2a890f4d5454d21f8ee2a9a4379dd151487b2aa2a290de77550521bcaeaa0a43e995141487d2aa28290fc77350521f8aa6a0a43f85c141486f5ba2c090eea6458121fc282b0243badc964d427db8ac9a84f976d0f509f6e8b0ea13e5db41d435cb2683a84f97650750d72c8a0ea176dcd41d4378b0a83a86e97648750dd2c890ea1f850521d42edb9a82a06ea7648540fc28290a81d154d5148675b92c9a86e16148750)
def g215H5 (j : Nat) : Nat := if 1 ≤ j then 0 else (0xf8fa5200914f0000950070270000930600de8c346df97b78)
def g215D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x202001800704c0c1010018b0889008890048d1214020b088d121403044689008890090c5820018c0810404040090a00b0c2020018304040082c104002063020404007081170a006101000c2020200407082840c2090f0062e1c2802421410e921432081606890043c6a4448050681606806ac0c102002052020801c9200782604130e018204c380643170c3c01a483821ac146e012b041b804861e48d582611616116a4342a65868f08e1822180a6609606b3560a8b4aa844f49a528a404658950da0a3f97bcef1d7b9b70edb1afb44652c1d79adf588a89472734b09110da003ca760e91c53626acc817c2b44c48b0ed1962c04707a0be11011000bf58e54bf58654bfd8d54fbd8954bfd8554f7d9153f799153f759153f719153f7d8553f758553bfd9153df55153bf59743f754f43bfd9543bf59543f754d43bfd9151df55151bf59741ef55341f754f41bfd9541bf59541ef95141ef55141f7d8d41f754d41fd54541fe58141fb59521fb99121fb59121fb95121fb55121fed0f50fe50f50fed0750fe50750fe50d40fe50540bbd8954d755153d754d51b7d8d41f354d21f954521f950521fa58121be59350be58750fa48750bed8540fa48540)
def g215H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x618361cffd1000f78e5000209f65cbc00000750000006a7000002c90000006b35d80037d6d08ba1f000003900c2f2be0ba0d2551b05800083000000c2a1d25420194cb79166400272d0000015c00018000000000000884d1b01000000038000358d80058ca10cd54980071f8f74c89ee860015999145c002120000018380010a34c0015c8000000029893ac360199580000147000000cad0621011a000150)
def g215D7 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x40e084a3062840e084c18a82130914b0a180a2462ca8602452a08493052c286024a1822ca86024682130910482384c14136c80916984b0c02a984c145849304ea6ab0d5c9c451d4c0511f8b4420f003fca9fd54fea9ffd0ffa87fd51ffa0ff507bca7dd53f690fed43f281f910)
def g215H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x20d298000000000000000000019d1d000c8800003d23d40000000003540031100000000f100132000000000000000000000000004000000000000000000000000000000000000000000000000971af7a000000000000000125001230001300000000000000000000002200034200000002f03a40000000e140060c000000000157000000000000000000000000000344207d60038e73c000000007dd86a800a2de45224a000000000000000000000000000000000000011e00000003550020c0016d7cc87000000000000309003da000000000000000000000000000000f002b000000000051800000002b0b6c64003bb5b00167000e10000000000000000000000000003208420)
def g215D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x6242013f
def g215H8 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x99a8000005d03006c2b804e1100fcd5804680000052004900)
def g215L : Nat → Packing
  | 4 => (16,4,5,0,0,7,0,g215D4)
  | 5 => (68,3,5,0,0,10,0,g215D5)
  | 6 => (55,2,5,0,0,11,0,g215D6)
  | 7 => (14,1,5,0,0,9,0,g215D7)
  | 8 => (1,0,5,0,0,0,0,g215D8)
  | _ => emptyPacking
def g215I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 4 23 2 8 4 0 g215H5
  | 6 => lookupWord 17 109 4 11 7 0 g215H6
  | 7 => lookupWord 13 211 2 10 6 0 g215H7
  | 8 => lookupWord 3 23 5 8 4 0 g215H8
  | _ => fun _ => none
def g215 : Forest := ⟨215,8,fun i => g215Y[i]?.getD (0,0),g215C,g215A,g215L,g215I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P4_0 : block g215 4 0 16=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g215B4 : block g215 4 0 16=true := g215P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P5_0 : block g215 5 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P5_3 : block g215 5 3 65=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g215B5 : block g215 5 0 68=true := (@block_merge g215 5 0 3 65 g215P5_0 g215P5_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P6_0 : block g215 6 0 13=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P6_13 : block g215 6 13 42=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g215B6 : block g215 6 0 55=true := (@block_merge g215 6 0 13 42 g215P6_0 g215P6_13)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P7_0 : block g215 7 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P7_6 : block g215 7 6 8=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g215B7 : block g215 7 0 14=true := (@block_merge g215 7 0 6 8 g215P7_0 g215P7_6)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P8_0 : block g215 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g215B8 : block g215 8 0 1=true := g215P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215T : checkedTables g215 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g215 0 0 0 = true)
  · exact (rfl : block g215 1 0 0 = true)
  · exact (rfl : block g215 2 0 0 = true)
  · exact (rfl : block g215 3 0 0 = true)
  · exact g215B4
  · exact g215B5
  · exact g215B6
  · exact g215B7
  · exact g215B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215G : graphValid g215 (boundsBefore K207) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low215 : Lower true (varsX 215) (qG_ 215) 9 := lower_forest (g:=g215) (i:=0) (hints:=16844359) (before_sound K207 V207) g215G g215T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K215 := extendKnown K207 9 [(215,[]),(250,[80,50,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V215 : Known true K215 := extend_ok (m:=215) V207 low215 (by decide +kernel)
def g219Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (0xc007ffffe0ffff4214900003f000000fd4759f)),(BitVec.ofNat 152 (0x8a510a20422440400492ad555555555554558e))),((BitVec.ofNat 152 (0xfff800ffffffe014ce8000fc0000fff00a49f8)),(BitVec.ofNat 152 (0x602c02800082048600630c30c30c30c248b8))),(0x0,0x0),((BitVec.ofNat 152 (0xffffff0000ffffa110381f00003f000fc38e7b)),(BitVec.ofNat 152 (0x80300b040900a010094228a28a28a2828a71))),((BitVec.ofNat 152 (0xffffffffff0000860de800000fc003f02c1067)),(BitVec.ofNat 152 (0x2304408c008e048208ed94b2cb2cb2cb2c9043))),(0x0,0x0),((BitVec.ofNat 152 (0x992347e0000ffffc00301f84)),(BitVec.ofNat 152 (0xc018030083008190102084104104104100504))),((BitVec.ofNat 152 (0x6ae02ffffff00000003fe000)),(BitVec.ofNat 152 (0x300600c010c010026024108208208208292000))),(0x0,0x0)]
def g219C : List ColumnInfo := [(1,0,218,0,7),(2,0,217,0,7),(8,0,211,0,7),(16,0,203,0,7),(64,0,155,0,7),(128,0,91,0,7),(0,1,82,136,6),(0,16,137,66,6),(2,16,137,64,5),(3,0,216,0,5),(8,1,82,128,5),(9,0,210,0,5),(17,0,202,0,5),(64,16,137,2,5),(80,0,139,0,5),(128,1,82,8,5),(129,0,90,0,5),(10,0,209,0,4),(19,0,200,0,4),(25,0,194,0,4),(66,0,137,0,4),(66,16,137,0,4),(72,0,147,0,4),(82,0,137,0,4),(130,0,89,0,4),(136,0,82,0,4),(136,1,82,0,4),(137,0,82,0,4)]
def g219A : List (List Nat) := [[],[64,49,118]]
def g219D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x101000b6785b3060336d8f7054941d3554dc9515078d5915454521f2554509514878d5955450521f255454941487cce055454540)
def g219D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x1800206000860542050401a04000605c54315040c30400600081c0c2001c180c0041505085411504541421a04685421523020c101040454442a36008015058c542140d636110007c40b181454304a7a11a1058546831a150aaea62829d26e9825a952368a2228520e7e1e2771b6681926116e5814a4b11e440fa390de340ba2508e1e05a0d0160027eb96c2aa4fd72d9151beee2b22a3dddc5545467eba6c4a8e7d54d8951e7aa8a12a33fdc9655077bb8acaa0fb77155141e7aa8a92837edc152506fbb92a2a0cfd75d91219feeab22433fdd9544867ebb2a890ebd6455121beee8a8a43bdd91514877ab22a290f755454521fca84a8a437d5d5414877bb2a8290ef56550521f6aa8a0a43f954941486efb9a82a87bb7155140f72e2aa281ee5c542502efb9a82904dd75d8d41e6aa8a8a83ce55151503d4a1242a07195454d40)
def g219H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x940000d6a1730000000072fac54000ac000d)
def g219D7 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x52a11846543308ca8664c111e8110c68c152c2434064a0858a11108d20c68a910c7070c1a320183462c30714302005450c080182a2988e9c7c14831b0e1019a303180c080172a3464a543311929510b860a00a9118b1184182802e54836608a3106862e45323c108a8e6ca8454d848d40a883c5345422a6820e0e20a803c6cb8b0410f1064b109078718d342173411a2a116c38c69a1650c868d70ee0cbf778eeb1c8b766b6cc984ad95529e52f23c418738cf1672a64fc8b1021dc2f8470730a20f414800ffd8554ff58554ff59151ff58951ff50951ff54941ff59121ff55121ff50d50ff50550ff50520bfd8554bfd9151df55151bfd8951bf59541ef55141fd54541bfd9121bf59121fd54521fd50521fe54640fe48640fed8540fe54540fe48540bfd8540b7d8d41f694e40ee55140f694d40f654d40ee50940)
def g219H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x65400000aa20000000093580400000c49e7c000000000000000000000390023001684c49cd0018000000000064b468460000000000080fb2c00690000000000000000000000091c000000000000004c9d40000000000000000000000000f30000007220280000000028800000000e0dc9800d282088b69d61776800000c8200000000000c33cf41800000182000b3600000000000a3f4b8000000000000000082342d86000002e80a50000028e14e1c004005c)
def g219D8 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x228603e33451086019238a03c81495c60e58a05474429648c880a04991240a10d8e100428f1cc34a2049213d31088ca24f14d8e10046c600d8e111a1b556e9f409c8b44b1e0a82a007f553faa3fd41fe90ff543fa81fd30fe907f443f481f940)
def g219H8 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x145400000000000a7491294e70007c0e8e0000064d00026c00000b3eb6e2b7510000000000000000000000c86000000000000000000092f080000000000000061d001a0c007600000000000013c0020b68200000240800000002c7800208002a7f420000014481800000000000000000000003a40004a00003400000261001c200071300000000000d24000c5e54f0b867c700020fb3206000001a3603000000e28002100000000070000000000221108000001900802)
def g219D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xa4188201bf
def g219H9 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x2460048000000083ba800000055913e50000001f50000066000000000008c00242c00001800000000000007c9200000288000000000004400320000000007c8000000000000000000000008)
def g219L : Nat → Packing
  | 5 => (7,4,5,0,0,6,0,g219D5)
  | 6 => (38,3,5,0,0,10,0,g219D6)
  | 7 => (34,2,5,0,0,11,0,g219D7)
  | 8 => (11,1,5,0,0,9,0,g219D8)
  | 9 => (1,0,5,0,0,0,0,g219D9)
  | _ => emptyPacking
def g219I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 17 4 8 3 1 g219H6
  | 7 => lookupWord 12 127 3 11 6 1 g219H7
  | 8 => lookupWord 12 127 5 11 6 1 g219H8
  | 9 => lookupWord 4 71 2 9 4 1 g219H9
  | _ => fun _ => none
def g219 : Forest := ⟨219,9,fun i => g219Y[i]?.getD (0,0),g219C,g219A,g219L,g219I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P5_0 : block g219 5 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B5 : block g219 5 0 7=true := g219P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_0 : block g219 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_1 : block g219 6 1 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_5 : block g219 6 5 33=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B6 : block g219 6 0 38=true := (@block_merge g219 6 0 1 37 g219P6_0 (@block_merge g219 6 1 4 33 g219P6_1 g219P6_5))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_0 : block g219 7 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_6 : block g219 7 6 17=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_23 : block g219 7 23 11=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B7 : block g219 7 0 34=true := (@block_merge g219 7 0 6 28 g219P7_0 (@block_merge g219 7 6 17 11 g219P7_6 g219P7_23))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P8_0 : block g219 8 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P8_2 : block g219 8 2 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B8 : block g219 8 0 11=true := (@block_merge g219 8 0 2 9 g219P8_0 g219P8_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P9_0 : block g219 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B9 : block g219 9 0 1=true := g219P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219T : checkedTables g219 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g219 0 0 0 = true)
  · exact (rfl : block g219 1 0 0 = true)
  · exact (rfl : block g219 2 0 0 = true)
  · exact (rfl : block g219 3 0 0 = true)
  · exact (rfl : block g219 4 0 0 = true)
  · exact g219B5
  · exact g219B6
  · exact g219B7
  · exact g219B8
  · exact g219B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219G : graphValid g219 (boundsBefore K215) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low219 : Lower true (varsX 219) (qG_ 219) 10 := lower_forest (g:=g219) (i:=0) (hints:=16842819) (before_sound K215 V215) g219G g219T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K219 := extendKnown K215 10 [(219,[]),(246,[64,33,16,49,83,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V219 : Known true K219 := extend_ok (m:=219) V215 low219 (by decide +kernel)
def g231Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (0xff000fff80ffffedec100070001c6184c3f237)),(BitVec.ofNat 152 (0x2a26a2251a25228de81b559294a42004413207))),((BitVec.ofNat 152 (0xfffff00000fff01992c003807c0002071c03a3)),(BitVec.ofNat 152 (0x4c04c0b62c0644d992c6ccb18c6c02050800a3))),((BitVec.ofNat 152 (0xffffffffff00000559c03c0f83e00008201ccb)),(BitVec.ofNat 152 (0x700700383007870558c244908424000000044b))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (0xffffffffffffffea0d91c00003ff83f03fe0f5)),(BitVec.ofNat 152 (0x804804c0004800020504aa65294a8aa13e40b0))),((BitVec.ofNat 152 (0x4922e000ffc03fc003fff02)),(BitVec.ofNat 152 (0x700700407008000029334631832820739b14))),((BitVec.ofNat 152 (0x13606ffff00003ffffc00008)),(BitVec.ofNat 152 (0x80080000800000000000084210514a800000))),(0x0,0x0)]
def g231C : List ColumnInfo := [(4,0,227,0,8),(1,0,230,0,7),(2,0,229,0,7),(32,0,199,0,6),(64,0,167,0,6),(3,0,228,0,5),(33,0,198,0,5),(34,0,197,0,5),(36,0,195,0,5),(65,0,166,0,5),(66,0,165,0,5),(128,0,103,0,5),(35,0,196,0,4),(37,0,194,0,4),(67,0,164,0,4),(129,0,102,0,4),(130,0,101,0,4)]
def g231A : List (List Nat) := [[],[16,101]]
def g231D4 (j : Nat) : Nat := if 1 ≤ j then 0 else (0xf624c3021d730b22e4302a74e3915917218153873c930db8aa921e38e0780dc96550f1c302c02e432a8798b746087054d43)
def g231D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x1860b88c01000000000000000000000000000000000000000904000000000000000000000001020800000000000000907a9cee470b79b6d86ab499ecc64b1986c05c6b353a6d1e833b9acbe53238ec5e230b82bfdf2f376b9dc2db6ab3d92c35a2b950a24e259208a421f8f07236198c05a2a1147e39198b44e210d8541e00ae5821c564d4e75e0574d4e538bf875906454e75e0574d4d53aeb825d36054ebce0574d8153ad9831d36054ebce0554d81538ef825d36054e3de0574d8153aeb825936054ebce0564d81538fb875906054ebae096418153af3815906054f3ad917218153ce9645c86054f36e037654c53cdb76dc15314fa65937054c53ae7815516214fb2e0153588538f7875516114fb4e015358453af3815516014f36e1d53580538f586dc55490eb560f5458643ed38054d6190f3ae037259543ce880dc96550f3adcb7059543cf371dc16550f3adc87059543cf3711c16550f3a601721954387f875946550f1b5957219543b4d821955350ed66006554d43cd876dc15350f66dd07054d43bc9821c15350e3be097654d43a6d821955350e9e6006554d438ef825d943d423de057650f50d5953dc143d423de0574d8d509f3815d350542b6e017558f40acd821d563d02b56047558f40ad9801d563d03a5e055458f40c9d7458f53d02a7e195350f408f7815db53503c654d43541408f7815d265cc23be0976553308f7815d954cc27ce0574d43308f7815d2654c23ee0176d51308ef825d9544c23de0576551308fb805d9544c3965915354130)
def g231H5 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x7c620000074011806a000000003c00)
def g231D6 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (0xf7dba6c0a9efa74d8153df2e9b02a7be1d36054f7daa6c0a9efa54d8153df2a9b02a7bedcf6054f7db8ec0a9ef971d81539fae9b02a7bed936054f7d326c0a9ef964d8153df0c9b02a7f6dcf6054f7db1ec0a9fdb53d8153df6c3b02a7be5876054efd3b0c0a9efb6418153df2c8302a73f5da5414f5eb24a829cff7655053beee2aa0a7b7dd95314f6eb22a629fdb7054c53ddca8b10a7bb5516214f7b2a2c229ef55458453df4a8b00a7be5516014f3eb2ea921ddd73d5243cfccaaa4879f5955490eefb9aa921df77155243dbeeca9c87f6dc15390f7baa2c321ef554586439fae1b2a873f5ce6550f3fb2ccaa1cff7359543dbee6b2a87bbdc96550e7fb82caa1efb7059543df0e0b2a879fd956550ef7b92caa1dfb70595439fcec32a879f5946550ef6b90caa1df97019543cfecba9a876f5d35350eef3b4a6a1ddd7594d43f3ca929a87b71d95350fafb2aa6a1f5c6554d43f3ee8a9a87e71d15350fcf2a2a6a1f9d5454d43bbee2a9a87f6dc15350fec382a6a1cfd7654d43cfecaa9a879f1955350edfba2a6a1dfb7054d439faebb0287af5536050f6ea9ec0a1cff7359350deee2b26a17ddc564d42fbb8aa9a84ff7458f50df6e0b1ea1dedc153d427fbb287a84fd7650f50d7ac8a1ea1b758d43d43aea9a87a85fb7050f509fae7b22a17ddc564542fbb8aa8a85fb70551509fae9b1aa1dedc153542fdb82a6a84ff7650d50dbec6a1aa1d754d43542fcba6a0a85f973d4150ef2a7a82a13f5ce65d027fb9acba05bf7355340f6ee2aa681b7dd563d036f3aac7a06dd7558f40db8eab1e813fdd563d035eaa2c7a04fd76d4f40b7ae9a9e81b758f53d027fbb2a7a04fd7654f40dbac6a9e817edc153d02dfbaa87a05bd7550f40d7acaa1e81e754d43d027eb9ccaa04ff7359540deee2b2a81bedc165502dfb9aa8a07b77155140f76e0aa2813f5db53502deba6a6a05f970d4d409feeca9a817edc153502dfbaa86a05bd7550d40d7acaa1a81e754d43503ddb8286a07b95454140ef6a6a8281de54d50503dca1aa0a04fd74997309fee8b2e61bedc165cc27fbaac9984fd76d5330bbae7aa6613fdd954cc27ebb2a9986bd6455330beee2aa6617edc154cc36eb22a7987db7054f30df2eda8661be59750cc2fcba6a1987d973d4330fb2a7a86617e9d540cc37cb2a81987b95450330fb2a6a06613f5d2654c27fba2ca986fb70595309feeab2261bedc1644c27ebb6a8985dd73d5130bf2e1aa2613fdd9544c27ebb2a8986bd6455130beee2aa261b7591534c3edb82a6986f96454130fb2a6a8261fc545504427bb8ac9a9de972181539beeca98a7a75915314f66a9ac429ed55358453db2a6b00a7b554d6190e77b92caa1cfb70595439dae432a873e5c06550e7bb8ac9a869d5458f409eee2b2a81d654f50cc27db82ca987595354130) else (0x408006080000001820108200042080060820008001082000c4c012182000c4083020000400100004b130060219084860a18200282c00a182c4c01018200181050885838020302000031020110203102010820000204202010820608382000820000008002000f0040bc0100020000001608001102420821084004820000000942131508586080908212081008006000800008005082420808204081820800030200100040685821820282080020800000204085a0850608202080a082005a184168610082000000820a08208c4c00c20202001820020206021008209021418200082060a0820000408002020e082001020208202002020208082068412082820848212084821e4610102000000020800400101d10400102087a08400302040820c080002008412081020030200002000820608004001058200482068210582160810085c0087848606880dc010370040c1010370040dc0103700407002201e170058583c01057005c0087837007c0085f0060773971d7116f56e96dd6d16c56a969d68167566964d6416356195fd5f15e55c95bd5b158556955d55153551950d5014d54c94bd48147544942d4114053e93cd3b138536935d3312e52c92bd2b12a528927d26125523922d2112051e91dd1c11b519917d16115513912d1211050e90dd0b108506905d05104503901d011004fe8fccfa0f94f78f6cf60f54f48f1cee0ec4ea8e8ce50e34e28e0ce00df4dd8dbcda0d84d78d5cd50d44d28d1ccf0cb4c98c7cc70c54c48c3cc20c04bd8bbcba0b84b68b5cb30b04ae8adcad0ac4ab8a9ca80a34a18a0c9f09e49c899c98095493892c9108f48d88cc8c08a488886c85084482880c7f07e47c87ac79076474872c7106f46d86ac69068467866c66064463860c5e05d45c85ac58057455854c5305145084fc4d04b449848c47046444843c4204043f83cc3b03a438835c3403242f82dc29026423820c1e01b418817c1601341080dc0b009405803c0013fdc564d4f7bb8ac9a9ef471593539fee0b26a77ddc564d4eeeb9ca929ddd74d4e539fae3b22a73f5c36454f5fb24c8a9df97099153bdee4b22a77ddc56454efdb82c8a9ebd6419153d7ec92a2a7775ce5454eefb9aa8a9ddd74d4d539fae9b0aa77edc16154))
def g231H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x83d92163fc0c4101229300004a8b1600000073a000000e0d000334505804000c12000a2600050f402b19000000000000f1a3a2d2f642fa7ba3000a00000000b45433d2b808899e1c03943c000000000000000820217000e9f42402500000032900a000000b41000000000118000000c3e00033500000022a000206000915d0e000e3658100010700062700002da38000a84809a23d1122ef1fd0ba1b6a4a9d000000f1de43932f1423b00044482c740713501ba600300051ef37000a3122814000228951846b204041a480)
def g231D7 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (0x406042c1a10c78608242830040909141802c2160c30909103105840618b045a24280416890a0080c6161021684203101a108309085a21218b442431618216182080c5c1107a21218445047883c3043c304101c11e2101e14382407862c1840c1810818b121031210b020c3088808310586082220c18104105e01426020304098078c105840f8030a103600e2070d805880808b07805200f00f1026018184c0303c4861e010789c0304081c36016284161f00614587c0184081f006162840f803082c207c018516103e00c28202101e0148601e182038032004104078078e10587c0185c42d08309806162700c10384c01840e1300610583c0384161300c105e00c18bc03031d8080c1018ec03c4083f00c107e01818fc03031e3300e100c3c0404070700a162838380509047e01420bc028309805060c1e01c2c41e0f00e105e01c1e012303463f00e102410f8058a130410e20bc0243883f0410e201c11c3c0263861300c1620f09806082c4e01820bc03031f806063b00b182101e3b00c1478ec0304431f0061c2600c20b0f803082c3861020b0f803082c3e00c2440f80309042600e241c0283e5be40e33e1fe04df0dcedbada6d8bd69d55d41d2dd12cfecdccb3c98c76c5bc4ec2cbfcbe8bc6bb2b9eb83b68b54b40b1eb03ae1acdab9a97a7ca61a46a2ba17a039e89c69b299796e94c92a9018df8bd89487285783c81a7f87cf7a678475b7397106e76be6a36886516285f85d65b459257054e5335184f64d44b249747c45a43840f3ed3cb3a938e36c34a32f3142f22c92a728526324822d20b1e91c71ac19116f1461241090e70c50a308105f03d01b000ff99353ff59353ffd5253ff95253ffd9153ff99153ff59153ff19153ffd5153ff95153ff55153ffd4d53ffd8553ff58553ffd8153ff58153ff95053ff55053ffd5243ff55243ffd9543ff99543ff59543ff19543ffd4d43ff54d43ffd8143ff58143ff59350ff55350ff58f50ff54f50ff50f50ff59150ff55150ff58d50ff54d50ff50d50ff58550ff54550ffd4f40ff54f40ffd4d40ff54d40ffd5330ff55330ffd5130ff55130bf59353bf58753bf58353bf59653bf59253f7d4e53bfd9153f7d4d53bfd8553bfd8153fed8153fe18153bf99453bf59053f754c53bf99643bf59643bf59243f754e43bfd9543bf99543bf59543bf19543f794d43f754d43bfd8143bf99443bf59443bf59350bf58f50dfd4f50df54f50bf58750bfd9150bfd8d50dfd4d50df54d50bfd8550fed4150bf99740bf59740ef55340bf58f40ef50f40bf99540bf59540ef55140ef50d40fe54140bf99730bf59730bf59330f754f30fed4330fe50330bf99530bf59530bf59130f754d30fe54130bf99510bf59510fe54110bed8153af99053af59053bb58853bd58453be58053bd58643b798f40b758f40) else (0x16084442c3160840610b080c34224208890a0101890a08b0a084061a28210189041842c604))
def g231H7 (j : Nat) : Nat := if 3 ≤ j then 0 else (if j<1 then (0x3a802727960000004a0c000000000323000000000000000000000005ccd58a0000000000001259c10800312600000000015960000000000b740000440000000000d4e8000000000000000318eee5856800000000000056b1c491e171379f400000053980000000a00000000c04000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002565ad0000000000000000000000000023400000000000000000a340000000000d0cf3840000000000001b260000000002b700000002094000000d6ccaac000000000701400000000000000000000570001d640000000000000000000000000000073c000000000000065b4000000000000000179b00000000000000000000001e1500000000000000000000000000000000000000000000000000000000001e320000000000000000537f1a800040c000000000000000000025020000000000000000000000000184200000000000000004d800000000000000000e3e000000000000000000000000000000000001ea90000002d74000000000000000000000000000000000000000000933000000021894ffd0400000000000038a400000000000000000000de40016b1000000249c00000072600000000000000000000000000000000000051adc9e0000000000000000a6980000000000000003988000000000000148e0000003410a130000000000000000000000102d3640000000000000000000000000000000000000000000000000000000000121b0000000000000b6f000000000000000000000000000000000000000000000000000000000000000000000494000000000000000000000000000000000000000000000000000000001f800000000000056499aa0000004b380000000000000000000000000000000000000000000000005290000000000000000000000000000000000000000000000000000000000000000000000000000000000a55b5e80000010be000490511e000e5d800000000000000000000000000000c73262a3e0b28001cc1000000000000000000000010cfb3680000000000000000000000f648000000000000000000000004680000000000000000000000b28c90c000000648000000000039f800000000000000013ac00000022d400000000000000000000003194000000000000288bce0000000043c00000023180000000000000001e0400000000000000007a2df02000000000000000000000000000000006c6318600000043372be00000000000000000000000000c4dac13a28cd800000053930ae0000000000000000000000206800000000008fe000c40000000042700000000006310620400000802012010c0600000000200200005800040031680201) else (if j<2 then (0x8a8b9580000000000000000000000000000042300000000000000001258000000231b85c000000000001c000000000000000000000028cc00101d64d80000000000000000000000c238000000000000000000000000000000000000000000001340000000000069e9490b40f54000fc48000000000d08cd1c00000000000030d2000000000000000032d8000000000468800050c00000000000000000000650000000000000000000000071ebf3941a00000000018a5000000000000000000000000000000000000000d3a80000000000000003e0c00000009b8001e7400000000000000002aa800000000000000000000007a0800000093c80012340000000000001830000000000000000000018ee00000000000000000000000000000000000000000000000000000000000000000000000000000000000000021460000000002599b17000036c0000000000000000000000000000088900000000000000000000000783000000000000071a89c8001816000000050a291000000000000000063680000000004a5081a640000582c0014b83b6000000000000000000000000000000000000f73000000000026e8000000000000000000000031d000200c0002eab871e368dc0000003e920000000000000000210000000000000000014a0000000735000084661d8000000000000000000000000000030c800000000000000000005acc001a2800022bc00098d000000000000000058f40000000000000001590d978000000000000000000000000000000000008c70000000000000000000029900000000000000000000000000000000000000000042d800000000066a184400000000000880000000000000000f3080000000000048000001b980000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c000000000492000c840000b476670000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010140000000000000000000000000033000000000000000000000000000000095000000000000000000000000000000000000000000000000000000000000000000000c4d0000000000315000000000032a5c72f6ea0a242000000000000000e0000ed20000000cf6000000000000000000060f00000000007d2800000000000000000000001a8800000000000000000000001df800100f00000000640000005e7c00000000000000000000000000001a2c0000003e3a0000000000000000000000000000000000000000000000000db0000f2d00000000000000002c56000000000000000000000000000000000000000000ece80001420000000000000000000000000054800000000) else (0x18ba0000000000000000a00ca9945e0004970000001a1f0000000000000000000000000000000000000000001b8c000000307193000000066b80000000000000000000ea70000000001cdf0000000000000000584000000062c1af0000029ac60000001e0300000020b80000000000001c3600000000000000000003d7e00000000000000000000000000000000000000081200000000000000000000001cd6c3b3a5c000000c5c80000000000000000001a2e33f0000000000000000000000000032c00000000000002c6e0002b4000000000000000001c4000000521c00000000000010bc00000000000000000000000000000000792c000000000000000000000039c40000000000000000848000000000000035b8000000000000000000000000000000006c08d13308000000000000000000093800000000000000000000000000214c00000000000000000000000002752000000000000000014a80018be0000)))
def g231D8 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x4043e030510780610112030410204b1e01870841e018528980c1071201840503a030504f3a030518180a10680e0c90601c42603033a0303cc5eab92c843a998a8421989c300c003fea7fe53fea9ff14ffc87fd43fe21ffd43faa1ff40fea07fcc3fa61fd10)
def g231H8 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x92766bc0d6f53c8e53a65d7400024d56e000eae107ee425b00080e0426441b0704b2a789828503d181670006751cb071915b11c9b0e54735c954b8df82bc3c11dd3145d61a755133668930377b994490004d7a5ad47000840e6d01e659a45226c25d05a01000000000698e565d2d2d10b020909b12450b62d1793e40254eb2ed2115813209e15f21c724edcc38f54200a61c08bd55e683bb37a22b6470fe101361630ca54867099a25ce6f58e543952335d4600083fa1f000d16bafa29051ada7ee372a6623905e9de14c64a62c76064180a71483486912f0ef8dd64fde7c19e13b3a523000f1b80c86ad76d06b3d000b5776cb9c1802a1043e18140212701374004767640f0301218f2b00230f61023706002d000010310000)
def g231D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x8200ff
def g231H9 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x71c56000000000895b58c00008a000016d000000000a0002503b6d003820032000000019002b20019800003d0000001d1000030a00000000000cad080000004f0012c750008c00000000000204)
def g231L : Nat → Packing
  | 4 => (6,5,5,0,0,5,0,g231D4)
  | 5 => (70,4,5,0,0,9,0,g231D5)
  | 6 => (231,3,5,0,0,12,0,g231D6)
  | 7 => (120,2,5,0,0,12,0,g231D7)
  | 8 => (14,1,5,0,0,9,0,g231D8)
  | 9 => (1,0,5,0,0,0,0,g231D9)
  | _ => emptyPacking
def g231I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 17 0 7 3 0 g231H5
  | 6 => lookupWord 20 127 5 12 7 1 g231H6
  | 7 => lookupWord 72 1481 3 13 8 1 g231H7
  | 8 => lookupWord 37 163 8 12 7 1 g231H8
  | 9 => lookupWord 6 67 2 9 4 1 g231H9
  | _ => fun _ => none
def g231 : Forest := ⟨231,9,fun i => g231Y[i]?.getD (0,0),g231C,g231A,g231L,g231I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P4_0 : block g231 4 0 6=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B4 : block g231 4 0 6=true := g231P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P5_0 : block g231 5 0 70=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B5 : block g231 5 0 70=true := g231P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P6_0 : block g231 6 0 18=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P6_18 : block g231 6 18 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P6_114 : block g231 6 114 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P6_210 : block g231 6 210 21=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B6 : block g231 6 0 231=true := (@block_merge g231 6 0 114 117 (@block_merge g231 6 0 18 96 g231P6_0 g231P6_18) (@block_merge g231 6 114 96 21 g231P6_114 g231P6_210))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P7_0 : block g231 7 0 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P7_9 : block g231 7 9 63=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P7_72 : block g231 7 72 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B7 : block g231 7 0 120=true := (@block_merge g231 7 0 9 111 g231P7_0 (@block_merge g231 7 9 63 48 g231P7_9 g231P7_72))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P8_0 : block g231 8 0 14=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B8 : block g231 8 0 14=true := g231P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P9_0 : block g231 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B9 : block g231 9 0 1=true := g231P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231T : checkedTables g231 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g231 0 0 0 = true)
  · exact (rfl : block g231 1 0 0 = true)
  · exact (rfl : block g231 2 0 0 = true)
  · exact (rfl : block g231 3 0 0 = true)
  · exact g231B4
  · exact g231B5
  · exact g231B6
  · exact g231B7
  · exact g231B8
  · exact g231B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231G : graphValid g231 (boundsBefore K219) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low231 : Lower true (varsX 231) (qG_ 231) 10 := lower_forest (g:=g231) (i:=0) (hints:=16778597) (before_sound K219 V219) g231G g231T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K231 := extendKnown K219 10 [(231,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V231 : Known true K231 := extend_ok (m:=231) V219 low231 (by decide +kernel)
def g237Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (0xfff8fffac0000f8001fe61b1183199c0387ff7)),(BitVec.ofNat 152 (0x88120882c94aa4920a506090190099a8080a40))),(0x0,0x0),((BitVec.ofNat 152 (0x3fff3fc020007001fe00023e1fc261ffcf9c19)),(BitVec.ofNat 152 (0xa040080318818622302034538040cc8a9d48))),((BitVec.ofNat 152 (0xc0003ff94007807e000e843fe00c7e03f01fe9)),(BitVec.ofNat 152 (0x2c082010631130c6422042642046202d31185))),(0x0,0x0),((BitVec.ofNat 152 (0xffffc004a0f800001ff107c0000f8003ffe01e)),(BitVec.ofNat 152 (0x1300131434a55a28c4870400000f0003142014))),((BitVec.ofNat 152 (0x1f00007fe001f800000ffffc000010)),(BitVec.ofNat 152 (0x1c041c2018c66c3088c54800000b9530044210))),((BitVec.ofNat 152 (0x71fffff800001fffffff00000000000)),(BitVec.ofNat 152 (0x20002000000000411108934984200000200000))),(0x0,0x0)]
def g237C : List ColumnInfo := [(1,0,236,0,7),(4,0,233,0,7),(8,0,229,0,7),(32,0,205,0,7),(64,0,173,0,7),(128,0,109,0,7),(5,0,232,0,5),(9,0,228,0,5),(12,0,225,0,5),(33,0,204,0,5),(36,0,201,0,5),(40,0,197,0,5),(65,0,172,0,5),(68,0,169,0,5),(72,0,165,0,5),(96,0,141,0,5),(37,0,200,0,4),(41,0,196,0,4),(73,0,164,0,4),(76,0,161,0,4),(100,0,137,0,4),(129,0,108,0,4),(132,0,105,0,4),(136,0,101,0,4),(160,0,77,0,4),(192,0,45,0,4)]
def g237A : List (List Nat) := [[],[98,83],[32,99],[32,48,80,96],[48,101],[48,82,96,32],[80,50],[80,98,48,50],[96,32,50,83],[96,82]]
def g237D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc7060f915c87254110
def g237D5 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (0x5384297321ba2c8a9c218b9646037154a1086fc9b0dba2a308527e4d875915184295f24c3ac8a8c21a35856056454610c5cb2301b92a30852ee417559141842c6b2caa2a2a0c2163b956056454210b55c92e8b22a10878664d6454d50843532c9c1ae2a842149f9460b7359510a4e4a305b9aca8853564482dcd6544217f28c16e6b2a2189f84dcd7259510c4e426e6b92ca88437a60735c96544313f0839ae4b2a218d873e017259510877cc2e4392ca8843765f83596624420ff30ba8eab12210df9361d64d491086fc9b0eb1ea488627e13835d95244313f0841aeca92218d883e01765491086fc9b0dba2a48842fe5187d8d524421f730bb0e0a92218b97661070549108f9cc2e2382a48866c611711c1524433a306b88e0a92210df9361d6590910a2fc9b0cba88488437e4d87594424421bb2fc1aca2122185d75e0d6510910c36baf04b288488437e61655cc4244297728b2ae0212214db935957010910a75c92cab80848842fe5187595324420ff2ac3ac89922157195a077454110af0c9503ba2a08859a64885591504434b6c6c16a6a82219c9835c87254110af1c8ae4392a08859664c85589504434b707a9ac4a822166992d4d6254110b64c98e4b12a08859ae4964d49504434b306b1ea4a822166992d915254110d2dc1ec6a92a08859a64b6354950442e5328392a4a8221749931c95254110bb0c88e4a92a0885d264e6254950442cd726b12a4a8221a6b835895254110d34c32a5212a0886d854981909504434d30ca9464a8221b61526063254110d2cc32a6992a08869a619524c950443c96c6a9264a82215e0925d37154110db0c12a438aa0886d86095294550443cc2c4a94a2a82219d383dcd5154110ea9b9aa6a8aa08879458d53545504436c704a92a2a8221e6162549515411086ecbf06b2e808874555173547404423e32fc0aa920221c69755895290110cb9c3aa8a8c808847c65f82546404431b10fc1acaa0221a9b8420d6550110bc8c9908a8a80885e86488454540442e632b2a2a2a02219d383dcd5150110b98ca6a6a8a80886cc5538254540443c62a9b12a2a02211f3985d62150110d98c2aa910a80887585d55248540443e42a8a9242a0221f81434c92150110c6dc3f06b2c60884f4e4d81d52304427a726c0ea518221d3174551518c110ce8baf06a8c60884f4e4d8548630443ac2eaa924318221e5391595534c110e2cb2ae8a9a60885d464f5454530443a62e8aa2a298221d517454d514c110f28b2aa690a60886f0e1532485304437830a9924298221dc1754c9214c110f60b2a6490a60887705d132485304421f32fc32a7902215e39760552c8110cf1c3b02a964088674e0d7354720443aa2e6a9aa390221bc3834c951c8110fa0a9a64a8e408875854971543204421bf26c3aca90221c69765495048110) else (0x1c304003010301000000000000000000000000000000000000000000000000000000000014100002800400206040504001410000000000000001041000000004104220400ae0812206418500002410400080040000000000590108901080b06065902240440000b810000004001000a4d4828d514a1d422814fc9ed3c2754e49bd362694cc98d3025d4b495d2a25149c92d242454848fd1e23946c8cd1822d45489d1222143c86d0c21542483d0620940c80d001fd3f47dcfa1f13dc7acf41e53c477cee1d93ac74ce81cd39471ce21c137c6ecd99b0350680ce99a32e650c898e316620c29822fe5f0bc9762e65c0b696a2ce590b095e2b6560aa95229e530a49462865009e93a26e4d09892e24c48c9011d22a448879071fe3f07a0f11dc3ac740e51c437c6e0d91ac338658c818a3085f8b715e2b04808d11421c3f87c0f21c43706b0d01943105f0b81502383f0500941101a02e0500880e00c00c00217f28c16e6b0ea18cd73e056218950967c9b03b14a4a84cee5181dc1525436c324c08e0a92a13699260470549508ddca303b82a4a852e650805cb6154295f28c32e530aa14cf936197298550cb4c2b00b94c2a843766264dcd6154299f24b26e6b0aa14cf92590735855086fcc6e6312c2a8627a13731896154313b09b98c4b0aa1569905c95218550c6bc3f06b08c2a8437e4d87d8a515421ef22c26eca9c410df9361f545862086fc9b0dba2a31063cdc5809c5654821ef30b88e2b2a410bf9461b735452085fca30eb2c629059a647635495048369706a9aa4a82415c9931c97154120da5c1aa4b8aa09069a61952945504834d30ca9462a824186d65e0974d4c20a57c92e8b26a610533e497458f530821ef22c26eca98414b79161d6454c20c5cb2301b9aa90852de4587591))
def g237H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xa
def g237D6 (j : Nat) : Nat := if 11 ≤ j then 0 else (if j<5 then (if j<2 then (if j<1 then (0x987d4a30442be61b528c110d7975d4a30442fc607528c1109fb8754a304435e5d5528c110df175546304437c5d1518c110f735454630443dc551518c110fd38354630442fce09518c110bf38548630442fc615218c110df17548630443bc595218c110fe152486304427ee11754c110ddb835d5304437ce05754c110edb8359530443bce05654c1109fb855d1304433e595744c110df3815d1304427e61f544c110af986d5130442f660f544c110bf181d51304427e61d544c110db97455130442fce05544c110ed96554d30443765d1534c110bdb8254d30443f4605534c1109f987d4930442be61b524c110bd983d4930442fc607524c1109fb8754930443765d5324c110ed9654c930443765d1324c110df175545304437c5d1514c110f735454530443dc551514c110fd15354530442fce09514c110fd13254530442fce15214c110bf185485304437c5d5214c110ef165485304437c5d1214c110fd15348530443f8549214c110fe142485304427ee0d75c8110df1815d7204427e61e65c8110be982997204427ee1d65c8110bdb8359720442fae0965c81109f987d4f20442fa60b53c8110bf181d4f204427e61d53c8110afb8654f20443765cd53c8110deb8754b20442fae0d52c8110de97354b20443f860552c8110be9854cb204437a5d532c8110fc9534cb204437c5d551c8110bf383547204437c5cd51c8110f735354720443dc54d51c8110fe15254720443f84c951c8110bf1854c7204437c5d531c8110fd1534c720443f854931c81108ff8759720442b7e0d65c8110aef82597204433d59571c8110de5525c7204427de1d51c81109f58754720442fa60b50c8110f6952d4320442fc60750c8110d797554320443da54950c8110bf381543204437c5c550c81108ff855d9204427de0575481109fb805d5204423f61d6548110adf8359520442bbe096548110cf576545204433e5d95048110f6952541204437c6057508110df1755442044237e0d71d89508ef8758862543335cd6218950b39841c152542d660c7054950b71811c1525423de1d61185508df835d9518839658d5354220b6982d4d50482f260c7254120b698594950482dae0d5254120e6b63549504839a54b6154120c7965dc1530832e5937054c20cd963dc1530832e59170d5210cb9645c3538432e59170d4a10cb9645c3518438e5935354210e396454d508439658d5354210e3964d49508438e5915254210e69625495084396595534c2108df835db5244237e0d7654910e5b63d4d504439658d5354110e69625495044237e0d76541109f38754640443cc5515150110bd3835463044396595534c110f515354530443f04c9214c110d71815d4204427ce1d5108110d7175544204436c5d15108110dd17354420443785d52108110d617548420443705cd2108110) else (0x154950443ba58952541109fa87d09504427e61f4254110af986d0950442be61a4254110b798590950443da54a4254110bf18190950442be6194254110f6952509504427ea1c42541109f98710950442be6184254110b798510950442f660c4254110bf18110950442be61a3254110b79858c950443da54a3254110bf1818c950442be6193254110b79854c950443b6d8d3254110f59534c950443da5493254110df174dc550442fc60f7154110df173dc550443dc54f7154110bf182dc5504437c9cb7154110f7152dc550442f6e0d7154110bf1821c550443dc5487154110df37494550443bc5925154110bf18294550443bc58a5154110f7152945504437cdcd5154110ef36354550443bc58d5154110f715354550442fce095154110ef36254550443bc5895154110f71525455044337e0d76541108ff825d950442b7e0d6554110a7f85591504429fe156254110cef72589504439b58952541109f582dc5504423fe1d65d0110c7d7559740442afe1165d0110adf83597404433759573d0110d9d545cf404433d59571d0110db5545c7404427de1d51d01109f587547404435d5d551d0110f355454740443755cd51d0110d797554340443765cd50d0110df171543404437c6057590110cfb8759640443b6e0d6590110afb8259640442be61b5490110d7975d5240442fc6075490110d797555240442fce055490110afb8558a404433e5d562901109f987d4a40442be61b5290110d7975d4a40442fc60752901109fb8754a40442be6195290110d797554a40443ba5895290110df17554640443dcd515190110f715454640442fce095190110ef16254640442be60b6550110bb984995404433e21d6550110ebb8459540443ae2116550110edb8359540443b620d6550110afb8259540442bee056550110ef38159540442eee116550110bdb8359540442be6176250110cf975d8940442eee1162501109f987d4940442be61b5250110d7975d4940442ee6135250110bf181d49404427ee1d5250110d7975549404427e61f5150110bb984d4540442fc6165150110df375945404437c5d65150110df375545404437c5d55150110fb38454540443ec2115150110f735454540443ec9515150110fb15454540442fce0d5150110df37354540443dcd4d5150110f715354540442fce095150110ef36254540442eee115150110f395454540442fc6162150110df17588540443bc5962150110fb154885404437c5d52150110ef36548540443bc5952150110fe15248540443f84c92150110abf8459540442b7e0d6550110f355454540442fc6075050110af98654140442fce0550501109fb845d6304433ee1d658c110edb83596304433e595748c1109f987d5230442be61b548c110bf181d52304427e61d548c110db97455230442fce05548c1109f)) else (if j<3 then (0xc1524433ed977054910cf965dc1524427e61370549109f983dc1524433ed8b7054910df281dc1524437c60770549109f581dc1524433e9db7054910cf976dc1524437c9c77054910df171dc1524433e5d87054910bb9841c152442f660c7054910df1711c1524423fe1576909109fb805d6424423f61f65909108ff87596424423f61d6590910abf8459642442b7e0d6590910ced7654a424433dd957190910cf5655c6424437954971909108ff865d5424427ee0175509108fd87d95424423fe1d6550910adf83595424423f61f6350910f2d54549424423fe157610910c7e865d4424431f6197510910d79805d4424423f61f6510910c7d75d94424423fe1d65109108fd87594424431f5d56510910adf8359442442bbe096510910cdf655cc42443375957310910cfb655c0424433e59570109108ff855da324427ee01758c9108ff87596324423f61d658c910adf83596324433b5d9528c910beb8054a324433d595718c910de5525c6324423fe15764c9108ff845d9324433ee01764c9108ff87595324423f61d654c910adf83595324423fe1d644c9108fd8759132442bbe09644c9109f985dc1324427e613704c910cf964dc1324429fe1564d4110a7f8558b504433b5c962d4110cf5645c7504427de0971d4110cf5625c7504433ee1d6494110db97455250442fce055494110cfb8758a504427e60f7454110df281dd1504437c6077454110bf181dd150442f660e7454110bf1819d150442fae097454110be8825d150442fce057454110af982d9150442de6166454110bd983991504439ee156454110e788559150442bee096454110b7b8559150442be61a5454110dbb74951504436edd15454110bf381551504427e6137354110bf3815cd50442be6136354110edb73d8d50442be60b6354110b7982d4d50443d6dcd5354110b7b8254d50443dc6055354110ddb7354d50443b658d53541109fa87d0d504427e61f4354110af986d0d504427ea1d4354110ddb7350d50443b6d8d4354110bf38150d50442fc6067254110bf3815c950442eea107254110bb9841c950442f660c7254110de9721c950442fc6047254110af984d89504433edd36254110b798598950442f660e6254110e7b85589504439e2156254110afb84589504433edd16254110afb83589504439ed4d6254110e795358950443badc96254110ee87258950442dee156254110d7b74d49504439ed935254110e7964d4950442de60f5254110e7b63d49504439e58f5254110e7b62d49504439e58b5254110af98694950442de6165254110ee96294950442fc6065254110d7b74549504439ed915254110e796454950442dee0d5254110e7b63549504439e58d5254110f6b7254950443da1c95254110e7b6254950443da9895254110f696254950443dca055254110f718) else (if j<4 then (0x50843ae5915354210ed96354d50842bee197254210eb9645c9508439e5875254210e7b7654950843ae5915254210ee96254950843ae5917154210bdb835c550843ae5915154210ef16154550843ae5914154210cfb865d5308427ee11754c2109f987d5130842be61b544c210bd983d5130843b6595534c2108ff845cb6544337e0b7359510cde82dcd654433760b7359510cdc82dcd6544337e037359510cdd80dcd654423f60b7359510edb80dcd65442bee0173595108fd84dc9654423f60f7259510cdf73dc965443371cf7259510add839c96544337dce7259510cef729c965442bd6067259510af9809c965442afe117259510abc845c965442b7e0d7259510cdf735c965443371cd7259510af7815c965442bee017259510cdf731c9654433b5c87259510af984dc165442be60f7059510edb73dc165443b61cf7059510ef371dc16544337dcf7059510ddb80dcd6544376dcf7059510df371dc16544337e0d75d8d108ff825d7634423fe1572d8d108ff845cb6344337e0d76d4d108ff825db5344397e0d65d4d10cdf635cb534427ee0172d4d109fb845c3534423f60b7654d10cdf835d9534423fe097654d10cfb805d95344397e0d6554d10e7b8059553442b7e0d6554d108fd86dc9534427d6077254d109f980dc9534437c5c57054d108ff845d7624423fe1574d8910c7d7559662442b7e0d6598910aef82596624433759573989108fd83dd5624431fdd67558910af5819d562442b7e0d7558910af7815d5624431f5d47558910add831d5624423f61773589108fd84dcd624431fdd66558910aed82995624431fdd56558910adf8359562442bbe096558910aef82591624423fe1176d49108ff835db5244337e0d76d4910cdc835db5244277e0d76d49109f7815d3524423f61f64d49108ff87593524423f61d64d4910cbd7459352442bbe0964d49108fd87d8f524423f61d63d4910cdd7358f524429f61762d4910cf7645c7524433d59171d49109f7835c7524433dd8d71d4910cf5635c7524433dd8971d49109fb845c3524433ed9170d4910cf9645c3524427ee0d70d4910cfb635c3524433e58d70d4910cfb625c352442bb60b6594910adf8359652442bbe096594910cf7655c6524433d59571949108fd84dd9524423f60f76549108fd80dd9524431fe1576549108ff835d95244337e0d7654910cdc835d9524423fe057654910cf7815d9524433ee0176549109bf845d95244277e0d7654910abf845d952442b7e0d7654910aed82d9552442b7e0d6554910aef82595524423f61b74549109f581dd1524423f61f6454910cbf74d9152442bb60b64549108ff8759152442de60354549108fd86dcd524427d60773549108fd87d8d5244337dcf6354910aed82d8d524429f6176254910bcd83989524427e6037154910cfa86d) else (0x483dadcd5254120f697354950482fae0d5254120eeb6354950483da54d5254120f6952dc550482fa60a7154120f69529c550482f6e0d7154120beb825c5504837a1c97154120f69525c550483da5487154120eeb72d8550483ba54b6154120b798598550483da54a6154120b7b8558550483da5496154120af98694550483da54a5154120f695254550482be61a4154120af9868c550483da54a3154120f59534c550483da5493154120f6b8054950483da6015254120a7d84dcd650829fe117359420e7b805cd650823f6137359420add849d563082b7e117558c20edb805d563082b7e157458c20cdd755d1630831f59574d4c209ef825d3530832f61d64d4c208fd87593530832f5d164d4c20cdd7458f530823f6137654c208ff845d9530823f61b7454c20c7d65dd1530832fa1d6454c20cbd8759153083a760d6454c20cbf745915308337dd16354c20cf986dc1530833e5977054c20cf964dc1530833e5db7054c20e7965dc153083ae5937054c20ed963dc153082bd6135358420af78454d610823f60f74596108fd84dcd65842b7e0d7159610abd839d564842af6067559210abf835d564842afe057559210abf855cd648432f5d57359210abf855c5648432f5d57159210cbd645cf548432f59171d52108fd83dd9548423fe0d76552108fd86dcd548432f59373552109f980dcd548432f59371552109f980dc5548423f61f5458e10add83d5163842be6035458e10cbd87593538423f61d64d4e10cbd74593538433e59170d4e108fd84dd9538423fe117654e108fd86dd1538427e6037454e10cbe87591538432f61d6454e10e9d83591538432fdd16454e10c7d655c7528432f59171d4a10c7d65dc5528432f5937154a10ced62dc5528427e6037154a10cf986dc1528433e5977054a10cf976dc1528439e5977054a10ee962dc1528423f61f5258610af581d4961842be6035258610cbd87593518438f61564d4610cbd74593518429f61954d4610e3d64553518431f59572d4610cbd645cb518427ee0172d4610ced7258b518433e59170d4610cf9625c3518429fe1165546108fd86dd1518432fa1d6454610cbd87591518438fa156454610e3d8559151843ad6056454610cbf74591518429f61b5454610e3d64d51518429fe195454610a7d86551518438f59154546108fd86dc9518431f5977254610cbd64dc9518427e60372546109f984dc1518427ee017550610cbd7559141842afe195450610abd86551418439d5955150610eb56454541843cd5515150610af984dd950842be60f7654210af982dd9508427e60f7454210afb865d150842fae097454210eb98559150843ae60d6454210eb98159150843ae5d16454210eb964551508427e6137354210afb865cd50843ae5917354210e7964d4d508439edd95354210e796454d)))) else (if j<8 then (if j<6 then (0x23f61f64945508fd87d8a515433b5cb6294550af584d8651542bd60b6194550cfb645c2515435e5497094550cdf73d8d5154397d8d53545509f984dc1515427e60f7054550d7953dc1515427e60b7054550d7952dc1515423f60f74596208fd81dd165882bbe0974596208fd84dcd658823f6137159620adf835c5658823f60f76552208fd81dd9548823fe0d7655220cef825d9548823fe0576552208fd86dcd548832f59373552209f980dcd548833b61b7255220ced65dc9548827b6077255220de980dc9548833b5db7255220ead64dc9548823f61b71552209f980dc5548837adc970552208fd87d5163882b760f5458e20af980d5163882bbe095458e209ef825d3538823f61d64d4e20cbd74593538833e59170d4e208fd84dd9538823fe117654e208fd86dd1538823f61b7154a208fd87d5161882bd6075458620af980d5161882bde055458620af581d4961882be6035258620afb80549618827be0974d46208fd87593518832f5d164d4620e3d64553518823f61d62d4620cf9645c3518833e58970d46208fd84dd9518823fe117654620cdf835d951882b7e0d76546208fd86dd1518832fdd16454620e3d64551518827e6037254620e7754585518839d5516154620cf77258551882be6137654220af983dd950882be6077654220afb865d150882fae097454220eb96455150882fae095454220afb865cd508839e5935354220e7b7654d508839e5915354220ed96354d50883ba5895254220afb865c5508833edd97154220bdb835c5508833edd16154220e7b52585508839e5496154220ef161545508823f61373595208fd81dcd65482bbe097359520afb805cd654823f60f7159520cf7719c565482be6027159520adf835c565482bee017159520cf5711c565482be6137059520eeb72dc1654833edc77059520deb72dc1654823fe0575d8d208ff855c7634823fe1176d4d208ff815db534827ee1170d4d208fd84dd9534823f6077654d20adf83595534823f61b7454d209ed82dd1534823f61b7154d209ed82dc5534831f5d56598520af781596614831fdd66558520c7f75595614823fe0d76d45208fd87d8f514829f61761d45209fb845c3514833ed9170d4520cfb635c3514835e54d70d4520cfb615c351482bd6076594520af781596514823f60f76545209df835d951482b7e0d7654520af581d9551482bde0565545208fd86dcd514823f61f6354520cdf73d8d51482bd6076354520a7d85d85514827b60b70545208ff855da314823fe1d658c5208fd8759631482b7e0d658c520cf576546314823fe1d654c520beb825d150482be6076454120dbb7455150482fae097354120af981d8d50483d6dcd5354120f698254d504837a5d37254120be983dc950483da54f7254120f688754950483dae0d5254120f698354950) else (if j<7 then (0x1e303cc002fc4beb2f94bdf2f1cbc12ec8ba32e50b852dd8b5e2d3cb492ce8b2b2be0ae92b8cad42b14aad2a78a8f2a24a7a29aca652958a502904a3228b0a26285ca11282ca0527d89f027849db27309c626dc9b1268899326109752598957254494224f0936249c921244890323f48f7237c8d923288bb22d48af225c88821e487321b485e2118837205880720047fb1fb07e61f5c7c81f087b31e6c78c1dd076e1d587351cbc7171c207021bcc6e41b786d81b486c31af46b71aa06a21a7068d19d4666195c648190863c18d8627186061218305fd17dc5f117ac5e5177c5d917045b216b0594163858815e4573159055e153c54914e852b144c50d13f84ef13804c812e44aa129049e11f445c10ec41a102c4050f903cc0ed03930e1035a0ce43210c242fa0bac2dc0b342b50a7427c096c243088820107a41da07501bc069017a05d015c04c8123042c0ea03000a80240078018004800c001800023f60f7458b508fd81dd162d423f6137358b508fd81dcd62d42bee017358b508fd84dc562d423f60f7158b50aed829c562d42be6027158b50abf845c562d423f60f74587508fd82dd161d42bd60674587508fd84dcd61d423f60b73587508fd84dc961d423f60f7258750add839c961d42bd6067258750abf845c961d42af2117258750adf835c161d423fe0d74d89508ff815d3625423fe1173d89508ff815cf625423fe1171d89508ff835c76254337e0d71d8950cdc835c762542b7e0d71d89509df835c7625433bd897198950cef8758862542bbe056218950df1805c4625427e6017118950aed81d8a525433bd897194950b6f8258d52542de6137054950b7983dc152543dad8b7054950b7981dc152542dea187054950b79811c1525427e61370549509f983dc1525427e6077054950a7d859d361542b760e74d8550af9809d3615423fe0d74d85508ff825d3615423fe1173d85508ff825cf615423fe1172d85508ff835cb615433ee0172d8550cf8805cb61542bee0172d85508fd8794b61542bee0162d8550ced865ca615435b6157298550cef645ca615437a6017298550af78158a615425f61f5298550d6d72d4a615435e5c35298550d6d7254a61542bd60b6198550cbf7499161542b760e6458550cdf64dcd61543379937358550cdd64dcd6154376e037358550cdf641cd61543375907358550d5f73d4d6154357dcd5358550e5f6354d6154337dcf6258550cdf73989615433bdca6258550cdf73589615423fa1c6258550abe8418961542af6106258550add831896154337dcc625855097e87d496154357dcf5258550d5f73549615435bdc95258550ddb73dc161543761cf70585509f9805d0615423fe1d6418550aef82590615427e60172185508ff87588615435b5c95218550cf78758461543b5e0d6118550cf5725846154) else (0xf027b19eae7939e1277e9dbe7609d467429caa7249c5670f9c266e89b426c19aee6b59abe6a99a6a68b99f267699c266a999265e9962652993263d98de631988a60a97ee5f597be5d797465cb96f25b696c25a1966e58c961a58095ea56b9596556954253894ca523945250593da4f093aa4e493564cf93024ba92d24a5927e4909206472918e45d915e448910a43c90da43090aa41b905640690023e88f8a3ca8f123b58e7638e8e223828df236d8d7a3588d4a3438cf63378cc63228c4e3048bfa2ef8b822da8b522ce8b222b98ace2a48a7a28689ba25f894224a88ee235889a21788221f987ce1e4877a1cf87021a8864218a85ee16c8576157854614b851613f84e613384b61278486112843210683de0e883660d383120be82be0a0826a094821607681c2058812603a80ae01c80360077fe1ff27fb1fdd7f39fbf7ee5faa7e6df8c7e19f807de9f747db9f687d65f537cedf2c7c99f177c45f027b85ed27b0deb47a95e9679f9e7879c9e637975e577921e4278f1e2d789de187849e0c7819df777c5de2774ddcd76f9daf76a5da37651d8e7621d7975cdd6d7579d4f7525d4374f5d2e74a1d22744dd0d741dcf873a5cda732dcbc72d9cb07285c9b7255c8f7225c8371adc65717dc507105c3b70b1c1d705dc086fe5bf36fb5be76f85bd26f31bbd6eb9b9f6e65b936e11b7e6de1b726d8db546d39b3f6cc1b2a6c6db156c3daf76ba1ae26b71ad66b1dab86ac9a9a6a51a7c69b5a5e693da3768c5a226871a16681da0167ed9f567bd9d767459cb66f19b666c19aa669198c6619980657d94764e192964458f0633d8ae62a18a2624d88d61d586f618184860e582a609181e60198005fe97f45f957df5f417c15ec97a35e5178e5dfd7705da97645d557465cdd7285c6570a5c116fe5bbd6e95b696cb5af16b65a9d6985a4968c5a1967759a1662594d64d58f963858c962c587561758215f957cd5ed57795d857255ba568958a55ed56c5575557554553954a9524545550653b94e853654ca53114be52bd4a0524548b521547f51e54735191455513d44950e942b5095416504140a4fed3ec4f753ce4efd3b94ea939b4e5538f4e2537a4dd13654d5933e4c993054bd92e74b612c94ae92ab4a9529f4a4128149c925a492d233489120c47f51ee47a11d947291bb468d19d465d191460917c45b515e456114944e913444b911f444110143c90e343750ce42fd09e423d08041c5059412904440f902f40810113fe4fea3f6cfcc3f18fc03ec4fab3e70f8d3e1cf783dc8f633d50f4e3cfcf303c84f1b3c30f063bdcef13b88eca3b10ebe3ae0ea93a68e943a14e763978e4f3924e3a38ace1c3858e103828dfb37b0de6375cdc836e4db33690d9e363cd8035e8d6b3570d4d34d4d26345ccff339ccd83300cb13288c9c3210c753150c3c30b4c))) else (if j<9 then (0x80010302010c1008608016040d240800000082430400b0206040843080008001042c090410000082083c1001e090c107820010100820c1810044090410082042184220482089244104802108811100422082240405100429203245100431210420302240482090411202000028818100060482083011102c30418410810080c3051808ac10069230c500020104112020421842404020800305060800304011034104000060800000004032020104100000806404440a0c1400201042008010040001e0800104060800088021008104060800029001004101820000104448108160c1844810c020800104100120a00100c8088802120c1320202011301091301208600b8101004100020e04100001020800418100004022e04040604100b04100002020c0410000002000000000c3010480040120002000408200001004408000040208100610000040a08141038182030341040002f640386120a8443090542218482a110c20080150804430284420a84420284822184410b8542212102c1208861061041061041004240c9419282109285250884100a844308054221c942210482a110c2a1208861108052504004c942028402038200c051000b04020c8581806120c08582010602c100c1164088404098402098402098402098402098402098402098402098402d42b504d3d74efd3a74e3d3774ced3234c2d2f34b6d29f4a1d24b48cd1f7477d1a3462d173456d14344ad0ef435d0bf429d06b414d03b408d00b3fccfdb3e7cf633d2cf333bdcebb396ce1f378cda735acd5334ecd23342ccf3336ccc332acc9331ecc63309cbeb2f4cbbb2dfcb672c1cacb2acca77297ca4728bca17276c9c326ac96f255c91b240c8a3219c8071fbc78f1cbc7171bfc6e71b3c66f18cc5f716ec55b150c52b13bc4b311dc43b0ffc3e70eac36f0d5c31b0b7c2c70abc273084c1d706fc1a7063c153045c0b7027c087012c00eff4bfbafe8bf8afdcbf5afd0bf2afbbbed6fafbea6fa3be52f8ebe22f82bdf2f76bd9ef61bd6ef4cbcf6f37bca2f22bc72f16bc42f01bbeeeecbb9aed7bb46ec2baceeadba7ae8fba26e83b9f6e77b9a2e62b972e56b91ee38b8cae23b876e0eb7fedf0b7aade4b756dc6b702db1b6aeda5b67ed90b62ad84b5fad6fb5a6d5ab52ed45b4dad30b4aad24b456d06b3decf1b38acd3b336cc7b2e2cb2b28ec9db25ec88b20ac73b1b6c67b186c5bb156c4fb126c3ab0aec1cb05ac07afe2bf2afb2bddaf5ebd1af2ebc5aefebb9aecebadae9eba1ae6eb95ae3eb80adc6b62ad72b56ad1eb38aca6b23ac76b0eac22af9abceadbab56acfab02abaaaaea9caa36a7ea9bea4ea8fea27a83e9eea77e9d0a6e29a0a646982a5ce964a556934a496916a41e901a3ca8e3a2e68aaa26e88ca1f686ea17e859a12a829a0227f99fce7e49f567c69) else (if j<10 then (0x20000100000000020004100060800304000800004000800000000100000040800100060800304000c8410001082000400a8200000141000002a08005040a080090400000002050404080000422080000010000080001c1000e08000000000000040608001000008041000000200000000000000000000001000204040000a08001000200004040028200330a10000241002a08601210209042a080801050e0a086022101422106012420c84081410c0442402142c28242070a08181400216088183038280040a08025040c08200c25038802040e08581028205040e08007040a0240060501000301020000101020204000020191001008100040808100020204020008000020000250800352c002000200000000040008001000000000000000200065041a0008820800004001000000100011020000100000000800104001800200000a0415282000400000002000410000002008810182000402080000010000000000080220400180020146a208040820d528400040000008301040000008000000064a08041001a083410000000a8202941001aa5081807080a0888100120801504120c9410282001c1002a0c9411101420481820282081410682000000000000000c104000080840100020004102820840100005820004007838208020b041e08001000200381000830340040c080c1060c081810000000000802060c0210041002008000042c158306160400080810002010482400800000080002c10000282000010000004080000400080000400080000c1000000200003040a08000005040000a080001412082010480081410000282000000030c00100000410002000c1078200001000200000000040000203040008000141000000008101000a080010002080030c0210041000002408901018601080090182618206040c083244100010400006080000030c04100000410000000984820000230c04188982100810102030104040180830250c041c9703800c00016080c302040004101808201838104001060208000008820010101020d040a080c1000208341000008204040008141030341040000c08001070a0e141030a0e141000020c08141000a080010400001102001415282000150400803060420050b0a01080208141008200081000422040c28215044415080c28205040030208181030200000002001400200080040a08125040000a08041000205044408080042e08000015040800300040e060a4480082f22090605040208041028205040008000141090385044401080a088b0216041112042028200040408205040008ae4a100000150400a82150400a8341040010008141510205050008125040a081a03000c0e0814102830003040304000000800100820580040004060804100007820010120820000100820c001028a0) else (0x10200000000040000000008004040008200001000000000408000003040000000018a081410000c0219043017082a085810a820704000000000000000000820004000020800d0504c00406282000001400400020080a104043314260020b5084005a80105446100000000c02102c105820b068a10080028008581a00340040a08185040a08140042008000041018042a00200001001a00215908400016070a08581000000000000008000000001000000000e08000081038)))))
def g237H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x1401e905a827dc813c28a9057414610c5c2b0000000000002a2344010000000000003048c0001c09a00bc0000819c0000c12c00000000000189f800000002008b812348db888fc2450158000000000000000000004270000081ae9cf4000041f000000001812ad0d85c0c00000000000001e9c00a81fc0000000000000000000040fa9ce48214000090b281b6804ac475192704640001003d202c000309f74c900000000300b2c0c0c1e742a800ac000011840000000142310014cc9fc114000081a800008033c1ec0003416800020201c89a419b44688280423f503b203f8888000214cb10ef8079511281348025c04cc1cf417909c101ddc2340000485082b5cc77417284acc267417d40524119605a04b4c07000014254096ec07fc8a5884008a04210000340866078525b40804150c10400000462824c0003c0ef1824000141f980b988cf80e40000dcf9c8008075c05c0000000141600002d80641330df800018125501b5009dcf20166c0e00002013bc0cc0000000101cb41e000000002c489420ec01800000003815601b9429c0001d234000380a3419182a350280000000045504c80c06192a601f46564818b4097024388440002810904a9c0eb84b20447a1ac00000000000000028961180c8054c28c0003912c088512a00003422d418e8895c682501400000000000001410cb81a47d022c54a444e510300a80002806480f4019780dec06c000380b600d40000944185ac0000d4240001503c00008c8e411d42a5d1970258000241dac08c00024c4400039193c268487b90365079c2271c24000000000000000180d140a402600000000000000000000250e80002414b8248000351a00001825dc16e8c8b006801740000000044e0000201d742180000000000000000c228000000014424000082ac000091880001829b81d150300000000302794040544aa136c2238524c276489c00f3510c0003c15c00000000000101a0000341c20c98413c0000000300c400039cfc0000000112440003854c0000d0244112025000014046911400000003402000001451e006845d4003cd4ac00fd82f420440fc0292020a0c7f81824df4c23992a80002c26c8004887d80cb40290037c14c0003010e11a541bfdce80003655f918d0964c09e129f513348c400000000000000008487c869421dd249e130000000000000d01c0001144e41a400000000000000000002484800000000000081c4000251040000c02c00000826100541b18295410140d9405b403b82860091dc11818551ac000010051001461c604014018904c10703a14024500102b1430cb0440820826000c94ce5000030430481c60080400032c22854450412040cd980283)
def g237D7 (j : Nat) : Nat := if 9 ≤ j then 0 else (if j<4 then (if j<2 then (if j<1 then (0x33eb2aa6106be6454c20d7ac8a9841b758d53082fdb82a6106f75398420deaa730841bd9d5610837abaac2106f75358420deaa6b08413f5db510833eb2ea2106de63d4420dbac7a8841bd587510827fbb2a2104fd7654420cfacaa8841b798d510836eb1aa2106f561544209fee8b2c213fdcd658427fb92cb086be7559210d7aeab2421af5cd648435eb8ac9084fd76d5210d7ac9aa4217e5c3548427fbb2a9084fd7655210d7ac8aa4213f5db538433eb2ea7086be64d4e10d7ac9a9c217e5c3538427fbb2a7084fd7654e10cfacaa9c21af991538435eb22a7086dd6354e109faeda94219f597528435f326a5086bd64d4a10bf2e1a94213fdd9528427ebb2a50867d6554a10d7cc8a9421af5915284376b12a5085fb7054a10cfacba8c21af993518435eb26a3085f970d4610cfacaa8c21af991518435eb22a3085fb7054610d7ac8a0c21bedd950842fdba2a1086f96454210bf6e6a8421be58d50843bda9aa1087795354210df2c4a8421ded4950843bca92a1085f9754c210df2ca98421f654d30842fcbae41087e952c82109fae5b2a213fdcd654436fb9aca886dc73595109fee4b2a213fdc1654437db82ca885df73595109faebb1a213f5cb634427ebb6a68867d65d4d10dbec7a9a217e5c3534427fbb2a6884fd7654d10cfacaa9a21b758d534427ebaec4884fd74d8910bbae7312213fdd5624427fb9ac4884fd76d4910beae3a92217e5c3524427ebb4a4885f571949109feeca92213f5d952442fdb82a4884fd7614910b7ce8292216f5d052442eeb98a4885f57114910bf2e0292213f5da42442fab8c84884fd7610910afcea212215f5d442442eeb9884885f970109109faed192217d5c6324427ebb264885fb704c910beae3a82217e5d650442fcba4a0886f96494110df2c5282217edd1504437db22a0886f96454110bf6e6a8221bed8d504437cb1aa08877b5354110ef2a6a8221bed89504437cb12a08877b5254110ef2a4a8221fcdc550443f838aa0887f25154110fe2a2a82213f5d950442fbb8aa0885dd73d0110beae3a02217e5d6404437cb2c80885f97490110df2c520221fc546404437db2a80886f96550110df6c4a0221fc94540443f8a8a80887f22150110fe242a02217e5d6304437cb2c60885f9748c110fe2a318221fc48630442fcbaa60886f9654c110bf2e898221f654d30443ec99260887f1514c110fe242982217e5d720442fcb9e40887e952c8110fd26590221fc54720443f898e40885f571c81109faec902217e5d420443f8a8840884ff73594109fee4b28213f5db530433eb2ea6084ff7654c109faeca98219f595530436eb1aa6084fd76d4810cfacba90213fdd9520427ebb2a40867d6554810ddac4a9021da549504835cb22a1084df7359510af2ea102216e5d020442ecb9840887e12108110) else (0xff4a8a8221fe55150443fdb9aa0887f97354110ff2a6a8221fed0d50443fca1aa0887fb7254110ff4e4a8221fe5c950443fc392a0887fa6254110ff2c4a8221fe94950443fca92a0887fb4254110ff484a8221fe50950443fc212a0887fa3254110ff264a8221fedc550443fcb8aa0886fd6554110bfee8a8221bf59150442ffb92a0886fd6254110efea4a8221df54950443faa8aa0885fd75d0110dfacba0221ef55340443faa8e80887f950d0110ff6a920221fe55240443fda9480887f95290110ff4caa0221fe59540443fcb1280887fb5250110ff2a4a0221fe4c940443fcb8a80887fb5150110ff2a2a0221bf59540443faa8a80887fb5050110ff2a0a0221fed5230443fcaa460887fb528c110ff2a518221fed5130443fcaa260887fb524c110ff2a498221fe50930443fd32e40887f965c8110ff6a790221fe54f20442febae40886fd65c8110fdaa590221fd54720443fda8640887f950c8110bfaea90221bf59520443f6a9240887f55148110ff2a090221bf5cd650437eb92ca086fd7654c10dfacaa9821bf5d9520437eb2aa4084ff7458b509fee6b16a13fdc562d427fba2c3a84ff73587509fee4b0ea13f5d3625427eb9ec4a84fd71d8950ddec5312a16f9d062542deba0c4a85de7318950bbae6312a1bb58862542fb388c4a85f57118950afae7a92a15f5d65254377b14a4a85f97094950ef6e0a92a1de1c152542fdb82a4a84fd74d85509fae7b0aa19fd4f615433ea9ec2a84fd72d8550bdce530aa17b5ca615437bb0cc2a85df7358550bb8e6b0aa1bd584615437bb0ca2a85f97094550bf6e0a8aa1bb5c5621437aba2c2286f572584509fee8b2c413fdcd658827fb8acb104fd76d5220bf2e1aa4413fdd9548827ebb2a9106bd6455220bdee4aa4413f5db538833eb2ea7105f970d4e209feeca9c413f5d9538833eb2aa7106dd6354e20cfacba94417e5c3528833eb2aa5105fb7054a209faeda8c417e5c3518827fbb2a3104fd7654620deac2a8c41bedd950882fdba2a1106f96454220df2c6a8441ded4d50883bca9aa11077b5254220ef2a4a8441be585508827eb8eca904ff73595209fee2b2a413fdc1654837db82ca904fd75d8d209fae3b1a413f5db53482f6b96a6905f970d4d209feeca9a413f5d7614827ebb6a2905f970d45209faed28a413fdd9514827ebb0a2905dd7314520bf2e028a413f5da31482f6b96a0905f97594120bf6e8a8241bed91504837db1aa09077b5354120ef2a6a8241fadc950483f4392a09077b5254120fd4a4a8241fa549504837db0aa0904fd7654120bdee4a8241db549504833fb9aca1067d7359420cfee2b28419f5c5650827fb9aca104ff7159420dbceab1841b75d5630836eba2c6104fd76d4c20cfacba9841af993530835eb26a6106dd63d4c209feeca98413f5d95308)) else (if j<3 then (0x82ffbb2a2906fe7654520bfaeca8a41bf5d9514837fb2aa2906fd6554520bfee6a8a41bfd8d51483bfa9aa29077d5354520dfec2a8a41fd98551483fab0aa2905ff7054520bfaec28a417f5d6314837eb2c62907f5518c520dfaca98a417f5c750483fca8ca0907fb7454120ff2e8a8241fe55150483fdb9aa0907f97354120ff2a6a8241fedc950483fcb92a0907fb7154120ff4e2a8241fe5c550483fc38aa0907fa6154120ff2c2a8241fe94550483fca8aa0907fa4154120ff282a8241fe8c550483fc98aa0906fd6554120fdaa4a82417fdc5504837eb9aca106fd7159420bfae9a9841bf593530837ebb2a6106fd6554c20bfee8a9841bf59153083fdb82a6106fd7654420dfacaa8841bf5d1658437eb9acb086fd7259610dfae2b2c217f5cf54842feb8ea9086fd7655210dfacaaa4217fdcd54842ffb8aa9087f97055210dfea8b1c21bf55163842feba6a7086fd64d4e10dfaeca9c21bf59553842ffba2a7086fd6454e10ff2e0a9c217f5c7528437ebb2a5086fd6554a10bfee2a9421fedc1528437fa92c3085fd74d4610dfac9a8c21df55351842feb96a3086fd62d4610dfacaa8c217fdd1518437eb22a30877f5454610efaa8a8c217fdc9518437eb12a3085fd7550610dfacaa0c21ef55141843faa8a83087f97454210ff2a8a8421fe5cd50843fca9aa1087f97254210ff2a4a8421fe5c550843fca8aa1087f94154210ff6a898421fe55130842feb94ca886ff7359510dfae6b2a21bfdc9654437f392ca886fd7259510df8e4b2a21bfdc165443efb9aca885ff7259510ff6e0b2a217f5cb534437ebb2a6886fd6554d10bfee4a9a21fe5c153442febacc4886fd6598910dfeeab1221bf9d5624437ebaac4886fc7558910dfee6b1221bf5cd62442ffbaac4886fe6558910dfacab12217fdd1624437eb22c4885fd76d4910bfae9a9221bfd93524437eb26a4885fd73d4910dfec7a9221bf58f524437fb16a4885fd71d4910bfae1a92217f5da52442febaca4886ff6594910dfacb29221fb58a52442ffbb2a4886fe7654910bfaeca9221bf5d9524437fb2aa4886fd6554910bfee8a9221bfd91524437eb22a48877f5454910efaa8a92217fdcd524437fb1aa4886fd6354910dfec4a9221fb98952443f6b12a4885ff7154910fece2a9221fd5c552442ffb82a4887fb7054910ff0e0a92217f5d852442febb484885fd7590910dfecb21221bf59642443f6a9484885fd7650910bfaeaa1221bfd95424437eb2a84886ff6350910dfac6a1221fb54942442febb084885fd7510910dfeca21221bf59442442febac64886fd658c910fdaa519221bf595324437eb2264885fd74d4110dfac9a82217f5cb504437eb16a08877d52d4110ff2a928221fe54a50443fdba2a0887fa7454110ff2e8a8221fe1d150443fd322a0887f9645411) else (0x6030be017742e505bb0b5016542c1056f0ab8152429b05230a2013f427504df09a01304257049b091011e4235045f08a01104219041f08180fc41f103d307780e841c5037b06d00d641a5033b06600c84187030305e00b9416b02c305700a94149028704f809a412d024b048008b4111020f03f807a40ed01c7037006940c9018702f005940ad014b027804a408d010b020003c407100d3018002b404f008b00f0019402500370058008400b000b0000dfae8b16a1bf5cd62d437f38ac5a86fd7158b50dfae0b16a1bf9d161d437eba2c3a86fd7358750dfce4b0ea1bf5c961d437eb82c3a86fd74d8950dfae7b12a1bf9c7625437eb8ec4a85fd74d8950bfae7b12a17f5c762542feb8cc4a85ff7458950bfee6b12a1bfd8d625437eb1ac4a85ff7158950ff6e0b12a17f5c462543beb1ea4a877d62d4950bfae3292a1df1d952543bfb1aa4a877d6354950efee0a92a1df5c1525437fb1aa4a85ff7054950dfce9b0aa1bf5d3615437eb9ec2a86fd53d8550dfce5b0aa1bf5cb615437f296c2a86fd52d8550bfae9b0aa17f5cf615437eb1ec2a877d53d8550bfae5b0aa1bf98b615437eb16c2a877d52d8550bfae930aa1bfd9261542feb94c2a86ff6298550dfac530aa1dfd4a61543bea94c2a85ff7458550dfec8b0aa1bf991615437eb22c2a85ff7358550fbee6b0aa1f71cd615437fb1ac2a86fd6358550efea6b0aa1df54d61542ffb92c2a86ff6258550dfcc4b0aa1bf589615437e312c2a877f5258550efaa4b0aa1fedc161542feba0c2a86fd6418550bfae430aa1bf58861543bea90c2a85fd7494550dfec928aa17f5ca515437fb14a2a877d5294550dfec6a8aa1df54d51542ffb92a2a86ff6254550efaa4a8aa17fdc1515437eba2cb106fd7359620dfae4b2c41bf5c565882feb9ea9105fd71d5220dfaecaa441bf59554882ffb9aa9107ef7255220bfee2aa441fe5c1548837faa2c7106fd5458e20bfae9a9c41bf593538837ebb2a7106fd6554e20bfee8a9c41bf59153882feb8ea5106fd6554a20bfee2a9441bfd51618837eaa2c3106ff5258620dfaa4b0c417f5d3518837eb26a31077d54d4620bfae5a8c41bf58b518837ebb2a3106fd6554620bfee8a8c41bf59151883bfaa2a31077d5454620bfee4a8c41fe5d150883fcaa2a1107f97354220ff2a6a8441fe5c950883fca92a1107f97154220ff2a2a84417f5c6654837fb9aca906fd7359520dfee2b2a41bf9c5654837eb8aca906fc7159520dfee0b2a417fdc565483fdb82ca905fd74d4d20bfae3a9a41bf5d9534837eb2aa6905ff7454d20fdae4a9a417fdc553482febacc2906fd6598520bfeeab0a41bf995614837eb2ac2905fd76d4520bfae7a8a41bfd8f51483bea9ea2906ff61d4520bfae1a8a417f5da51482febaca2906ff6594520dfacb28a41fd586514))) else (if j<6 then (if j<5 then (0x95d52b525634ab095352a125374a589485289250f4a1893f527724df49a8931525b24af49409245245247748d8918522b244b488890f5219242b4840905520523ff47d88f751e723c347788ec51cf239347108dd51b5236346b08d351a1233746508c75187230345f08ba516f22d345888ad5153229f45288a1513d226f44c88945121223344508865107220343e887950ed21cf438886e50d5219b431885f50b7216342a8851509d212f42488465089210341e8839506b20c7417082b504f2093411081f503b206b40b8813502120334058807500720033ff07fb4ff31fdb3f987f14fdb1fab3f407e54fc51f7b3ee07da4fad1f533e907cf4f991f273e307c14f7f1eef3db87b54f651ebb3d607a84f4b1e8f3d0079c4f311e4b3c8078d4f151e1b3c207814efd1deb3bc07744ee11dbf3b687694ecb1d8b3af875b4ead1d4f3a9074f4e971d1f3a287414e7f1cef39c87344e611cb339487254e451c7f38e871a4e2b1c4f388870f4e191c2738307034e011bf737c86f54ddf1baf37406e54dc51b7f36e06d94dad1b4f36886cd4d931b1b36206bf4d751adf35986af4d591aa735386a34d411a7734d06964d231a3734506854d0319f333c06734cdf19ab33306614cbd196f32b86534c9f192f32406454c8318fb31e06384c6b18c7317862b4c4d188f310061d4c331853308860d4c0f181330105fe4bf317db2fa05f14bdd17af2f505e64bc5177b2ed85d64ba717432e705ca4b8d170b2df85bb4b7316d72d885ae4b5316972d1059f4b3916672cb85934b2116332c405834afd15e72ba85704ad7159b2b0055c4aaf154b2a7854a4a8d150b29f05394a6714bf29605284a45147728c05134a211437283850349fd13ef27c84f449e313bb27584e749c7137f26e04d749a5133726484c6498312f325c84b7496512bb25584a64943127724d0496492512372450485490311f323c047348df11b3234846548c3117322c8454489f112f2240441487910e721b04324857109f212041f48371053208840d4813101720103fe47f50fd71f903f047d90fa31f283e147bd0f6b1eb03d147970f1f1e103be47750ed71d883ad47530e931d0839c472f0e4b1c7038947090dff1bd837646e30db31b4036346bd0d6f1ab8352469d0d2b1a30341467b0ce719a8331465b0ca71930322463b0c6718b031146190c1f18182fe45f30bd317802eb45cf0b8b16f02d945a90b4316602c745870afb15d02b645630ab315482a545430a7714c8294451f0a2b143828344fd09eb13b827444e109af134026444c1096f12c025344a109331240244448108f311c0234446108af11402254443087710c82154421083b105820443ff07f30fd01f543e107a70f281e243bb07630ea81d2439f072f0e401c3437b06e30d901ac434f068b0cf819b4331064f0c7818a430b) else (0x40c11a51010444054304181110105410444041511100e9445104040ca511101014444032512110c9448443a511130e044694484011211151004485c44415011211105448443a511130e9604444840511120c480444315100a94404c30ca210a51088405431615100e94404c30ca5a210108858403a50d121010585420115120c2704544842215100c40544431015110c6054404441512110c48544431715121110544440311100860444031108120c5420484440402100e94100840410043c2c4031615060403021810084058406160a9618265040210104414104041615250402101858549440446a50854889440404021018101008403251008144020402100c1448403171286111020100c1c1851105041010585410080c94624a200162514540448944080512111020484430403170c100c222c3011210204894444c125241113044894444c11225111020489444401122511102014484440812110c142090444c1252411105c2090444c508241113142090444080510121314204048411050410104b14ac404162425101030885440410120814484030510120d908a0018464001510103430181441522100c569440305100854944031825100c548840308060507101854489442505221706121990185436415100d90028894405010064a2062518585410084052415100e1b14504840d12100e90884031504100c484021310120c5a88904040c1008590c10184121008304c40316a20c06104840206c31312105430884041510084840216a264101020484031822100c584020c221410106040214121110105a8990404086411101200184c380862b131200184c38086132b105804184c4131008204840308051012104c4021613100c4450543118112151094504432514110c504421514110c54504430514110c94450448411254112104504483154111121054450448405114112100800941448446111512101296182131008404c21310084c402b5756a72d435a68b49568f2d135a08b3e56772cdf59a8b32565f2caf5940b24563f2c7358d0b1756292c4b5878b0b560f2c135808afe55f52bdb57a0af055d92ba75730ae355c12b7756d8ad955ad2b4f5680acc55912b175610abe55792aeb55b8ab455652abb5560aa9554f2a935508a9e55372a6354b0a9355232a2f5450a8655092a0353e8a7a54ef29cf5388a6e54d5299f5320a6054bd296752b8a5454a129335248a44548528fb51d0a36546528bb5160a285449288750f8a1c542f28535090a0d5413281750109fe53f727e34fa89f253df27af4f409e453c127734ed09d753a727434e789cc539327174e109be537526e34da89b2535d26a74d409a55343267b4ce099a532f26534c98991531f262f4c509875309260b4c0097d52f725e74bb897452e325bb4b6096852cb258b4b0)) else (if j<7 then (0x5c1888341150a14402190c8541101a14959042510083430941840625640c64182101508604021825100d9040281060888005438522410c5e141d0442215100c8840943072508061204188831706222510188a0590425810622101a0448325228110109604188842581062b101504215100858550c1840580060c36001434215060c2016003068009081a003058008641822510040c101822524100c944022481060c6604901848106088a041832406085890403072408061088184832206120c5040ad2c4c50c060830182160c060c590e001040c0608901820c060830182410c081812241000c24185030981410e042418322814109120448281220a04ac28141220e04188831780060d0e040830280060c1818122410c95048a044170108590e000840722060e881c18306070854242150708542420340150c541c20240150c0c04485c40401111710100c005c403020016101008584040403001610540c044841504011110585418100c0861512110c2090544440812151113144840308121511105d90443c512100c20485444418150511105c5414484451512110c54484430540170c5c14544844515c3401710640c08305451504021010544021510085c541c100c046c510120c34231440415100b144020fc51011105840215100b08544031540160e14484031285100e1448403030112151010445440404021015100c04544841512080c0464484150301121016844838c041044544041125100c405444304101811105410444041511100c14444031125120c445448317151112105c44483040215101008544030402161010541008404c205a41010245c54315120818544831015110c40544431815101110445448317151211103208544040112110c10044431715070403011804485c44417110804484430510120c5c549410044461725110c5494443040111181004484431715040301251808549430513100c100c5832513100c4c944031325100c144c40317122511105448443120448544431512110c54944431825110c1c5420015110c5448944440005121110480800449451512110c5c5404484451215110c944844364821510105592084041513100c544c4030482151010404c5436482651011959208404650c821010110854404a442151011110a944040c42a51012910a94404044218101054110840415a44210129511084040ca542101016910840410c20a0a019450465828014104c419436513100d9209944046564821010544c4031513100d010c4e944a513100e944c403a513100c544c4031513100e95010c4c4a513100c144c403030112151010445440401111215118d044994465634112119430444040d651210100c0454484a381a5121004544830301191210540c0448405a38112101044544041125100c4695104) else (if j<8 then (0xc60544030a800814544031722150e001080416005430d24084810608220c8854222010888140220858849030d4008403c2242108584022386084010a45234015144011615100c4011606220c2054443210b0884442450b100c58442110608585418324150822160030122150e14105228040103430240150818201c32240150d008a0031523400a104011621070c2089005444022800c560500315420c0c542421715070c5424183001808005821512081209005441900080b002190241001064544830c05090c25086430219000c143021509080d00543180008603022100160c5d009438521000c3014183190c060c141821706080864003050c09101001708141c21543060c05005431644000c58183038105120484316000855083031915428010241182508545c1c30225082418216048458215110844101040411211010c041150708148420704641c20716084411104601c2181108601c2162508940420806250c148422521085c542180708141c24304141c2021508201820716081c0420701081c201830001624230c1d110c30725010c1c0421643070c1c8c58381050e048430721050c1c1250807061058082080608581c20301080410a041c582160448542191208644821511086026150841825110c0055083150708541854208581a144440785081c94208062507101e08216041e0820782081e0820782085c541c32580081e02143150908541821402190c32942150909028c5430014180c602430340045418240a1150c54302150908541c2161509061210600038400160c305420440150c6400219000864544830c05090c2464219000a943021509080d005431844000c60243031815090c4c0058315070809005431300170c89002050608640020ca5086411300170c15001c31640250d100058381160c0c15120434481084e1400307160a10002150d08341450d0854301c31915800c542428018150c1c11722250c2458183054108003420c0908241172208585440310045409043100b0840082410b0854402a523860c5488210060c5c1831004944021806086040217250840942c308050706101411210050c2014484041004444020807250c148821025220c204821204588c5431912060c15001832402818005146018206a508144024105060c00582011508201c21722060c180824306020c1c1820300190421724230c19110c30602090c180831712060c91005c1848117084c11312090c5c1830623170c405c24106050c1810807060c5c002170840061048205c31740010d04008834106220c201c20807085c182020608110e0408422044c482060438182430e08388c183100e084c482080708201c5c1842502100c94110c400851722060c0e0408317220a042c2800b086430183050d085c182050809081820c19060c) else (0x1917120c605c443401708485c5831715070c58119160860584031016085c5821516100c54482151108885420115110c64544831815110c588c185442108085c4821711082c54211045c888431715070c20845431811085c541c3060809005c5431505110c882420517400c545d003151108560900310150810542151008544021504085428015082200543192415)))))
def g237H7 (j : Nat) : Nat := if 7 ≤ j then 0 else (if j<3 then (if j<1 then (0xf40767c1c73805d3083400000d0386a05400000000024041480832216940ed1c00728308a635ca00ec0000204052273c000000000682b3000000a1d68463290cf0000000002486e000000000000f56c16f88a20c01306082900e400000f077c64642805d8040f00000a0364000000000820a2201c020b2000004017100da04159298cb00001c050ec08ba88890000140a51c188981ca0115b00444d021511ba000000000000005823523448309c9c213801c2616ec0000011a70000000001e08d8c60de0389f464e80e22c1f98034900001c026dc0342036ca209c063254413c88f892309e496000000233d80168610a9cc57b8184d110c0000240dec82d23069ee0f97c095d019040439e46b000000826c00000c01b9015888036c025400002412e181e9705260000000000000000001c0e50000060417101d0000034c80000000000180a3c6110603c44036e822f5017fa08f0621b6000000000631a7c054d68b19410ee03d980189e0d01486210237c24f02463fc4741108054630e05e701d94304dd06776e4fe419a28a9c407b0403aa00f86406ee081a40a8a414e5b9c1b086ea0dedcd52a92c5d409264305c1f380000701e2807820009b83755009f009dfc05ee0059e04c8e202b00b380000c03d120df0c8fc481495235bc0a978853c91a4684c420071a18dfb9cec07592025540ab101d8d03100000000005a32ec010be881c901e8420c202a82e6f3c0fef02190000000002019280000b0178c20400000780ec360009010e470107071b003903011d12050001050616160005080801272a010307050a072b22070804032f0203012000070a2b0f0c0e0701005700071401000800011701064a0f00000e041b13360c34350742020008035942045c002e02040303030214114b0e0d000a0a0104081a021b25010225070b0000000425010a0144071036020006031700190907000a011c0203020b0a05083001000303000c0a002113050006120001080205022602032a0002060003000315012b003c000200353e0003d92000140001000f01201f03020d0205000a04051007030401001a03071f041c110b0f01072f03050e0004000005040027091901190502020006000200070b15010e01011c04110007010407080e0c060901170e13010108000100000200131801000518000801040300031000021a011702151f03010715003e06050401020304010308000f073f02000204000101040200000c8d0002020106020d1b0205051908261502060006080002000a05000301022603020112140c000d00050820150607020004040300063800000b0016090d010400001b01000d040012002b0503000d000106080e04060c130e000d0106061a1107080b011901010003030034000105090d001a2500010001000807000d0804010105000402) else (if j<2 then (0xa180b500000a1186000008c84b81e3e07b5c06080000100239216a60fd55ca10000065104810e0000040017b1500a426c0d11c0986540b12220a41cf7804d052ebc06cc00fc800000000000d1800000000072173e02e4000000000c40df24263006380000404da000000000239b60000180104000078097000010a204c1ef1030c2422180ee940b900000000000085900d7c98bc0000000001d1028000000000e9053c0d3321569133340b2ac45700005f510800003c10a80000e2021e235694c0001770061e000039ce04036e80066288c7618d718ca701bc0000000003b9330000000001a024f81d0007ffce4b9d56b2801a2462f68180000000000470ac40980c1dda122d000002226481b9a804cb020e4015dc01c21bba80370b2510a13aa009e576ebe661f80adfb079306a1e232c9c9b800001209e406c28cceb931c610f60000301a22a30000001423e9815c800000000040fc080de6880e140da00000017e800009004868cc788ab088b8900bd00eba01384842800000087a1412598022d6260a46368032283976977664456c03e000000000140998c18d090d0000014642008ce800000000000002e073c8212892872064909a30000000001c446882105a03e9083a047c7c060800003110a2cc63412930258d00ec40f7e80438000000001ce4d800000000070430000020071610995057620f34815180000505008234b1440443905027200002806e000000000000001487200000c665c0000184be381cd205bb600340145c02c0404f020ae84181800008110600002c0c700000224bee08b550047813de0717c0af30479900693008c0000101cd800006032a00000000000000c310aeecb8d8ad3836fa05a1206c400000a883e2356000000000000005085c00003485fc801ed31906a5dd005160257905d0a49878182a8110e1326008040000783a9313502886e615400000f04a2e007440cf80000a07afe105ac21ff023a5022d80d8ac219000005049c000038080d11f6a02820000100350030ac479300d5800001020d5030681093814cc8187c648800000887380000000014635c0000600120000000002018e80000e114760b540000798b3c031ea43450145184026213520058d19300000203f126a9800000000000731e0b052036f108310207a4330d01d101f67065c00002046f00000b5617e68898086139387044ec6300809e188ba305ee6001281886812d5077f410d7c05638bf83073be8e60c0cbb832100000ce6c8c16c2a03200028e01e681c0e90e5a4345c0b1f91b700000b0005a0cb2a43600000c03eac1084000010050000006640bc0bb30298f1228325e7c0f78c9ba932ba0226a817a510b1505c800001c0f6b83779649c606b44c87502db00000005ce4d0a880d7d21c5203c88857b0161700f04107815e72026bf029) else (0xce4313200001e412800000000070482000008479600be00000c0eb5818cd00fb2065f40168c20a281892035800003c0e2000002221cc23c6c004a01c500001c0a1440328a332701b66448a80b4500c3a079060c36802b003dd340680000321a0a83d0001f4c0bfac141883f9f463e000014932ac8856251400003811160221023a8000000000000000000000000000078130f005f501b000000000000001ccd53c19fa82cc00000000000000000318447600003806a8000000001c45f00000610bd000012623088241821e88432000000000000000000180d68000000000302e3607c6dd1380000d02470098c00000000000001a0d0b405748042d00c400002c84380000e206e00003020978441f43d60000000002087d0000088141c1e2d03454463944364000022b660000000001943a00000704a660aa80000103840231588dc400003043100000000014220690c8006bfea244000028a1590140e223a819cea2380000081045a4a2b835d906600000100537013f8014e00afc01cf928922034702328000000000a03aa610e4000070248605dce008041729810b782404103b017900000752eda0d9cc105f910c00000408468955098cf226ae60c900000000007085e000038219a434391343e0485c0a8a39d0102b0000031117403b1f7272283b3401a98162c015560dc040ddba350721f120554c59e08a192083924a9e812c900d6502cce021241aa32978504df4018e9808180a1a013fa22d848a23831e0000000000000000b36221956a227803d80000980c8b2edf412f800000000000d6448e740152d21aa4a243019480000000008491fcd0e6110b523f8c0127d9e70000024087c059301bc80000106c6e10630837582a70000000002883b00000540b8a0e340000000000000164644810de80fd00000000000000302de9482bc0f99c16490093d440d086b3c0eb700f0b31a2e8c8f81a09025a504aba0bb7c85f081aa4038680ea84058b03a780266000f44021908eff222748105807bb02e1904f2c02ce01e50814e505d3a02274d413838f273f3ee5000000583cc00000c0cfbc1e5b02e2e072dc816a4951800000000100891482ea842dc0429c03af41c2e2117000000000040645011fb056c00000000009175b041920a20601a30297300975025e0111e80f8d10fc0000200b5a0008e6094081ba8475000006727520ca98043613ca3053a00000000000000c040400001c048a02ce000000000000002925e004f800002c1c8500e0621560905e8805c0131b422a0000384cd000003050244a0800005126c403002064741dca01eef01a2000028cd40098a750120000080bd539504223f60d2d090480000a01800000342099894e0000cc06840000790de6709c80be8c157180c60000060220000000000684d34042ac5fab022600001685))) else (if j<5 then (if j<4 then (0xe87052481040c09a8040a8317360c1041d2510c9422432816e80f9681ce1132584300085248071d02d9c0c7ec0360a04f2427c208a6c039810c6c40bc623088177c08a7b00db26412c1fee004ec469f881440474a8a9a1237dcecd39ce9a83534367a008fc407fd317f203e7408ef208c01188631a6400d3c200f83c6305b9e090240a45043ee2022a43098821e88e740727c0a46c1f700000b076a40fca94bef81d30634be022e40dab040bd034be4a9b80db00318304ac20c5540e78820fb406c80da98ca8e03ef622060000208318000090056000024454f88eb00000000028cc458358324e662283844c00000000018082000002186c446a72076e0833000001049b210ecc103f832d701a7680f000000000000001c904800007023ce025e00000c0590807a00000c0c2408e299bb3802980000348fa8006f9008904136d4bf411200000000001c0cf00000208190441dc829d82a1c0714405f41cd8a81a0306364100c00b6800005101a0000148280017be40c20000350f6188a140534101ac0000000005230fc003f41f480000424e9e061400003034e00000000000000382ec006c28266341583828600001849e99c988000000000c0774000060989800aa000030c9f00000824f36032d41e0a81ff00000000024023db2433320200000000002024e01f3006180000000000000000000000000000320e8408a2c1c3d317c546b480086c46be02b500349c63114052602c6011540000340e90000000000e10f0005af990ab423e00000c16b9b04be279a641c744523831c922868a0400ddf802da5023ae064dc950b80cfa0375a82d50449583d3640a400816011a104267736800001cc6a00000703b8000005003100c9000018412e444fd02bd2024e409fe80a580000a320c00000000000000b40582858c0000299f5000012445c0000280030048c000000000000008049e00000488a00000942abc06a400002924a3737568c69813b6911e402ea2498a510bd0391403f4602be4c5ec83789117242cfc0000702ade0356c012000a8000000000086ec9c17000000b015000001c0cd00000602bb44e6948c588328f0073501a9c013582abc06db00060881a202d9c6099a070281e1790e9c07f6a44e9c183e01dff24eec0c8f1ce2b39fab048e7025b84c60a005a051282304411cc003f7067800001407a3815e000002075c04a9a91aa000012c53800006804a323ab40368c00800000f045680c5b8934bb855324a2cc154920c80000506400000000006aa80000014085c00005c1149067b403d800000000000499e0dc80d51d808d145a2e097b80c61895df46d9204161104a18de2053e0000000000000020016000000000002b7000008039400000000000000ea1cc00001233400001602fc0000602456021a0000000000015a3033a000038c) else (0x7e22e71801417aa7f842d200003488c502cf00000000000000582a800000000000000000000000000002c0484825d00000000000000182cb00001c076a404a680e3e07458040800003c115d241e20f3d41e4800000000040a300000000000000148778000022112642cfc00b3c9e77305700000000000000002f8e02e0204c800006802500000000015c9d8108e101f884670c926000005404706306445400000e223308530000004bb800000063180000408c7995c72007c000000000f04b600001cc7ff811a0000160e9800000000000000000038132800000000160115c509618d63000e609a0406100000e02854ad87cc66803ea40699e08f9c06c0026900001c10a40000381f74086c00002d02c882c5022760000341c1c80e64077ae0baadcd380000000000000240ef02413a43c1449bd88bcd00cd3114ca2270017db811ce012c0000380a332004d07a400001886eb8295424c84098a9022e23740067400003415000000305e60000181edb923e4227004b10407aeb93596229842f010ac00000b07c5004b8c171e0040d032c000f8944380000000000ace8000000000a0019a05bd901fd008ce07a8702d70468ca164a02c0e01d3885d6824a05484807d088c700000c4222c0ede90f2800007206a000000000000000000032ee800004b932200320000000000a1e90466004f2c61a5d013a0000160fa301b5e3824943ce0000000000198ca0694a032848248000000000000000000303fe0000000000000000000301be00000000000000000012c9240000680a545115822740000000000000000002415c2297c540242c8800000610e3b320780792401380000e04080000000000000000001428900000518cec04e8642edd0f2202fcf0719a099fc01860364603a3ec1c781fb701c60000100f8d002880000a11d8000020927d393d50466c0ab14804d837f0000000000000000000a042080d54000032346404dc00000c014800009085600df9002fc00d0273e9aa1cb04c2d835be426402e2042118000070250e449800001908f000004265ad0a6f008f00000c047a420f939a6205e08046c0000002d15052c00001c03bb0200e077000001019a982f1224ba201fc00004011800001a42a150ed9832b00000c824c000000000b02e8000000000692750000180784883a8a031d05acc8cad01809108c0043e00003c457b88cd3012468d5800000000000000000008054da235307ac8265d883900000443b8605f0822100000000014027501fe4028d2014600002813d2008e921c2804ed01077c2bc0000000000000000000100c320cdc51b9139f3d116824f3201e8e8a7f207420000341f080000703a9ca22fc87e710ea200b6006c9c183708f9c00cc000000000603b0b0212e0d5c59b07010ff81290431d01ae60275902b2a055d084a11)) else (if j<6 then (0x2841cab80f300000442cdc07200000306a3aa936409c7209600000a0e8ec09b5088d801dfa0e02487b3837400000046ec08d09b93c973a2000010185f836900000c07f3403968415602bfa09cc0000000003245e00003c0bc0120ce10f80000000000000040337a44140000403bc702d3ca9f4c1350335f840d00000000004a333000010438000002837a00001a40e0000000000000014a21801282a32f00001a0d940000009510000000003085c00000824b400001c076a8165584120000201e7000000000180f81990ff2044c0588823dc000000000f00ea0000000002042500000a0663c180481ea0000120b20c0196016e7408000000c47680000b038ea0e94c09200119b24ab204a642000000000001e42c990f1888f4031764877e8203a0314c0552841b100666a33ea00c00000390b35003c9053ce4a8800006029b0000000001902f8000030508000020c661a0940000000000000000000d05f2e49270d70800005046200000000058331000006868c000000000a018a000024084008d600000206f8402e00000341ea000028199582716114a0000041a380000f468000001c1c96012600001006640000301a8e055ec21fc0000281e7c1160000034c6ae90395013400000d5d68022500000c0570816a00000000000000008bf1028e0000020ea000002b9b800000608e001f600000711dc607b1c1b000000702400000081b88822e904938ecc3804e681a2904a8e0d2141d9903b6105d668cb68189023701132a000009ce7f83825317400003d99ca02c37255a6005600c580000c111820495c83200000c1670c80b5087be8115d05ce00000c0d3f099410281802659898b02b4a7666800e800004927681303c07040000383afc067000000000000000d087ac106c00002027de80e10858bc8fa3801b3258cc222b80dfb0112000006a220884439272673b30043b15b1000000000040510043c000004739200cce0083101cca728200002444da90739219cc101000006807d6143e000024181000001026f802af500058163301dc00001102ee813e00001c24b400003117a0370c0000341f6983c700000088b40000001e2b064f20d0dd0a42895a00000a0537d04afc066b0435c08be8074d04344119da0fac0000483c00000180b4c8c69401c9b01a8000000000181341736600003c5f900000957de00001c0a9e83a02047ac034941308000053171c02de4139000000000180153013f242c6f726940c8800000000000000a40300000302c200000000000000000000000040d3400000a05300000e0794c00898206000010422900f58a202707c80000004665833600001a00b559095a3d01070d0a2340000601b44028a0000000000907700001202c0000000000b07ee0000000001221400001209eda4bdc831700000a825c0000083f44) else (0xa0f0f854a00000d006f64a94c1484926ed045800001c5ef698c30000000002482f8814700000c8c055077000002127d20fe800003a1e1a21120000100bfe1876405ec000018c8280000141e9844dc00006824200000a01f904911043a073ad00450044f30213a0626cc9140000000002032940386c0171828700735e496414056012cd11ec0819e4035a202ba02fc20d4884afb08bb00000c0a914c86a0399f22104202f41b3283f8d005560dd800000000000000c02b48118112a000464a23fa8204781aef0413c0b3400004241a780de610c000004a2cc6061ca0338c17300000102002080c4836c8243192f5e44e40c6858081a06bda019ec0ff002be340d5e8777d0a38000000000e8c8640fda0113a00a600003484200000d06fb41088000000000b00b000001887d182f5500a400000000070bdd001bb403f820b1a2007000000000201ee2022ac0244000000000002204081260671d02300000373e4000030c83c802800000222880000238570000000002407380326000000000240a52a1613236b4000400005a8777318f42374c2030000010100000014862902445812600001c05b701b900000000000000201cb20738e23674805018c23317dc247390cf80000403cda0eaf020c800006031a00228000040104f0315010b000c0e80ba124b9))))
def g237D8 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (0x5612200312901e2a5244048a94910122a5244048a95112202a52844330141a528446230529210b8504948c1243812e48291142022c1480a44a800a4880c1a292222452440300042922a4462a48291101000a4888a002020a5480c18905222120a4032200a9220285204830a3089010286244440b08910102922000a91180a524444029491110291204840a8491110325244440a009252229526001101428c044040a4c80644015244050a409061461120205010491114405244040a488002a4461844806484110c2024a404061012520285284480814a1120205440491014905224c80a8929220205440129015101244040250992202a2244034404a11202810040988049900ca00245409118294221852404888080052640522009052029202002942231124148080800526405260011010103004c426001101008200504040099010980221080a4401220259e6c93620af4d6caadb53da83537693f461a004f42725369995cc0a5972a2935c90a4411f08d946422cf12288042b61090628194025fa4fa27b23d09e24ee2755ba09c88e226f5b709b08d5b695b4259a4c8d635b125824be95d22ded696b145722aed516a62515a8253ce9c54ce26052a292f47c233d14c87642a20e50127e73df1e38ed87513941c34dd66c935399dccaa63330897bcb9a5a42bd9564a7c51527d136095e48d22e910884e4051ee0ee873036f1a30c905f62d91580a544d824a11787fc3c81c20cc85c028011e07a834c16208f036812c044000ffd8950ff98950ff58950ff18950ff94950ff54950ffd8550ff98550ff58550ff18550ff94550ff54550ffd5220ff55220ffd4e20ff54e20ffd4a20ff54a20ffd4620ff54620ff99520ff59520ffd4d20ff54d20ff98520ff58520ffd4520ff94520ff54520ff14520ff8c520ff4c520ffd4120ff54120ffd4c20ff54c20ffd4420ff54420ffd5210ff55210ffd4e10ff54e10ffd4a10ff54a10ffd4610ff54610ff50610ff99510ff59510ffd4d10ff54d10ff98910ff58910ffd4910ff94910ff54910ff14910ff90910ff50910ff10910ff8c910ff4c910ffd4110ff54110ffd0110ff50110ffc8110ff48110ffd4c10ff54c10ffd4810ff54810bf58b50bf58750bf59650bf58a50bf58650bfd8950dfd4950df54950bfd8550bf58850bf58450bf59620bf59220bf58e20bf58a20bf58620fe54220bfd9520bf59520bfd8d20bfd8520fe94120fe54120bf59420bf58c20bf58420bf59610bf59210bf58e10bf58a10bf58610fe54210fe4c210fec8210bfd9510bf59510bfd8d10bf58d10bfd8910bf58910fe94110fe54110fe90110fe50110fe8c110fe4c110fec8110fe08110bf59410bf58c10bf58810bb98850bb58850bd98450bd584509f994209f59420b798c20b758c20bd98420bd58420af99210af59210) else (0x4200905225462a844452444642549452228842140122a4472a860800a4888e08ac1425c012221490a91100205462a9110d111480e911158a4051a202a4440081520aa445121000a4080256224868e1222d010800a6c347050a524319090e0a34294911112114a40530162034894890220a1229490a5e0a542148921e224849480a5a20148961101cb21249488a852922224449050a522318880e0a442948905929024225101891115223890d0c2801d2921d293202012d11243470a025421cb2445293202c54a4c889152c4484480d050924a4452b050804a4888f11203849480c602c406912c2204014a4c808582814a4c80c121a3829490c6424346960921e224229480a602c406912912044122949085c2824b048921e224109480a5a2014a90405204454a4069214c974889290192224a40488901c2449480e602c407092224a4092e949101128824404470d106824928e1929210445045e1a34505286244882094911152c50c48411192a30d16193243a58a20824223454a8881214a454a488901a122189480a))
def g237H8 (j : Nat) : Nat := if 4 ≤ j then 0 else (if j<2 then (if j<1 then (0xb1d92c89b00e1890618a26600002c206000008a150000040d0f00ac81727036cc2f10000281e360a8e00ce00000d2614027fd16320b511c5a70987c05f781ea81fa5056bc965d20b982fc503bd0113308d6d01ab2253caaa72761427a309a8c2d3b07784aa00000000e2005d44179d493c822e802d8808b455a842d844a664569476e3c890b679b1300821c890e5e035ec5a89087bc228a01b8c2f8d082742df502400000157f5028700c1fc30020810000000003c0bcd07c2c125f05da0110c1632146f52814969be0612c0874088f82abc05e38279a03b6ca1eb089a0578d591f8257c360202b86084c831ce07e309f004320c15e005f94072b23e3c1dfa2744404350713c157c27ec4225e03c6515e303ed0445b09ca825f60276409220593803f90606c9afb0432c2cf30454c08fc00e9c030b0168499400000c60b00001414c6043800000000141dcc04480000b6a1cc0711049b92598280101440000300f700000000050c6801cfc05bc000014098562b000001dbbf259ad68c54a5501390000314cd000034248f025389db000010e5ee060e40f300000000070bb0c14a0000300b4300b00000401e066bcf24b20837000038a7be0c340000c0008000000003527f408c90a7900001915d02634000082764525e106b686e72098cc6e1846b0824f30912126c006bdddbf74654028b506e9c06df01984a68c430ec80800002c0d800000561100002001ab4ac05643707aec131e074305b0521539c5fd00a20031a090c00000000009df8074b00c600001c25000002004f0032e0a70406ff8689000000000c16ed4006000000839f110e016b806600000d011e82a5241800000f5a21409500000c1505013bc6ca02679442a60b028169706e6829700b9c00009099f028f024485d3f7006c08260000342175026710640012b549eb13000722172d881e110d00490409d4011c6b8307122f27002e1c0d1501001d07206d05571d0d153203b11f4f00021016020f1315718b03a0276b0112060502228112c20106030a1c017304000101382a862500000003010057104300610003001e0340081507003907031b502504021b4f3c071300281441002a0201008813550013a21102610608000249020e0179420b0125180b1a16b10b00080d011e170000040d00030e530703281501501906d40c19032c400601333a041e0004060c0404261a560112522d051700b652130f10003f041d0004148402040608010400052018021821047037105b02010b0002090b000a011102068905000c14050501530d0d1bae3c070024062b021717071d0a08030c004d1b043a04001e00020b01060101010328004a030011060901016a040001180b1a0e01281d07003507000012010017090a1000100103018902190b03090209032c013176040b000a0b060103000000) else (0xa2283102daf1a7210ccf00d80000b0703c56a449a25d939123650d6e5bf380ea000018211b8a7c509fa0900813fa0bbac005108a9a51f000000000109d5016e0009cc20fa264bc69b30960810d5877f030bd05f1c1fc40a980000a0c1a5081c7643c096a2b21c1d1c69b3442d78a9f00440010241a0a06ae45a1604ae968980c12901f00000000064588411d000000e1600001856d000000000d09380000000000000206769a8b20795408d05b7bddebe08a400006348fc6ee40c7b003790508c2667771111cae086400001774c0000932cb025a513c2409300003426ec2b42e6bd000014182f76d89475020570851e30de457ef03480000176c8407b2260711c7b456c42e430b0d02e3b069b896d78741c15d000015253000000000d368a0008e0a8b5a89a208182f65323dc29ef00300704b03700000803dac00e00000802ea224ec0b1f43d3026f109ce42d0f04a240bb4089f431d0079ac18b000000000938d4000063aeea0f4e0099822c907cc0000e407448432075016ca610bac31fd0c09d0c7f27ebc083c06d68214e066941d90000102050000389b1902a0c4efb0b97cd72402dfc97b00002c17a51850c974d090a82aaf015fe264e0bd4419fe0acf0171807d0c95ad04d294257059e1c52c0792844da2893c13c00000024bb033383210041d02fdf2088413621113c9620000000008018f81955041b806570c4040ec0417310414876081b660ad2ca03c30c280bf7763c497ea8b3b8613b05b1802950114c1bcd08920062c286cc2b000001d28da0a048470e09700000f056001bd510b3030eb63f540e8208308a4f00000dde8f0716da86f14d4064c703940000a0c44e0f2209364067d0057c22bb0b49c2c500000004a7017201f21075841bec0c05c04290755c30300b58414fc1757014db435e15fcc07f780cf348a8160ba400e856ca07de5de18494040a2776ea4484a4621d264405cf4dd5649fa1d66f01df02fb71c39d051802e8000080ba74000676f654fc909b005a030445c11c515d2c951306dcc1090000209a581979c0a5b0bfc9098c07a2481300001c3130000340ad00003c23ea0a574293000000000a02ab457d41b7ad4eb00003d27d000025c5420ad80000d2609009a100b40000b179940e60775fc65f701be4e346022082a700000422d366c5424c57647c1cc5069e8a2563aea51f3e54d4ddb53021700d9706b8059f309649c5762139ddd2e23d80000501d40000e4405115af082a49a300001da4d60a8300ae000034265000000000f014802bbc0645d227d03c800003059aa27f00000000030a75825b801544286000014221f3a740000420d00000d25624a09a050400001472282b5102e64c2e1045b8317a06484320f14259c1b2384fc83c3492c01b8c04ee421b325a58119c4a3cc3229075fc701e44e40000f051)) else (if j<3 then (0xb4ddd4a091551864262b056ed057e01c90080a42743478dd305a20c544e4508e18971d0c2809d034570000040b54ca04801500000d051c00c53063d02206019180dd00003c87ff025d1c50b04b480a9815eec1c1408bc45a7901f58d81309f840c91212150f0d06b2800b00c67c57f00b989472827fa80b074abd45726590482f2043419819651c700105014102569047b61e6f432fc9ab320b7c3086520a814010a7f09c220a100000c03bb010bd88684567f02cd021ab43740000d0c5102a955acc00007031d89ba64194004d209e0c124b1c2790e7000000000e042b40619035442715065c801c00a47084424c12c16dc00640e0cd98d9407980180000050b464069e026cc283c2581c5e9058c74251d099101cac004840a6d2b1800df60279d1e4a258e416880918c1053483c023b000030c3860b2281b30000301490000001da17160c97fc05ed52892017a52525109491aa1508d52f8025b9a01f000028174307a90a02108c2c0cda10c18247d0b718305e2870c12f40091c1a174c1fc0bd00002d159965da0051911bcc1627071dc0c0e0118000340c63c081000000208a039311ade20d6c8290000100e0114dbd8fb101afd00280a00c03d9087d10e8b07a402820000000000000349c300000caa100000000090afc4879043540000302e00000e0486008ae06c7c1f6000000000d47860de98260e00fef4c0783129074c8215838e5162da02d59061a01a88236005c20049151b94ec0e36ac80ab90a16c15365bd2823ca06a282ea34b45106730a58003364202113bf717a892b820ca9422135c6015120421819450585026df09f7ca5090ab9c12010224499ff109c02f400001410fb00fa826be268950f361b7d80a0b0a700000d0a32008237709947040bde50695072f827770b12c18ad07e6198f7491b44eb000028a1ff1bd5cd8430077821250218c81ae0ba2d1cc508038c2d0000111c970671cea0210cbc6fc4770605a6a386d895e91c17c2e0f03e7cd77604cc8074110e9c849776cc8e4fd0bc19303b6a2a014be063919fec0621010211b5090e3b27a84118a094ec255815c70819000014827205540000a0559000900ab30d73c003c81e2c0bbe808cd63f80000a00785160c077702a8310be1251676d00000c223fc2bd30088450aa08fd496a826c801cde89b490d100003959dc09740000b061cd01800a6800009434b9c534050c82fe10b1bd42087a240000f10900000a04c3c222c076c0000d09c00000a40580000c035a4809f0c3140c200001a263c15cd48450000008249279842af00000c0d4c0c3dc955000010a72a2b1e48f50000340a41278405a9802fa42c1e0239e6c1308400000867ef0991953ef805b30a6cd085000010d830012141172122f82b1d0b894315b596c403440760c165041a1948400a65984510107023) else (0x3497aa89bc0000643e3c1e041434000000688a026904e354fef30b1c18900ae70568b717481ce0000280d35072142be806c2c039344f240fc714f940eb443ba031620323c05600000000000a20000000002813200002c27660709013ec0c6e016000003caa32438bd26e92b261c5950a254135000000000000008122707d42594449ec0000e0a8790c400286019642986560a908e4c08451224421c02783c268505144a1810a60924c6412f00ac32836005d000020180e15acc2dbd198040a750b240000619759015e4926c474204a80000c2754e59e9213f89b4b0b76427b903694001807b3428e457e8457c4083b809cc108fc262506d040175030fc0f51445810e1503e9824132097c5d00205cd0f1647c8000080b30d05b9068c443610a29c1c3e058cd107600a980af8457c0000154240070000038294d2b2c0000b0386c9d4a012e41bb0000380e3a407091dac00e182b2c5a2b420d80bb4c611a06a4c148210c50103710cd159fd0804dc56f5473097201a780000d08f4148890564dd0280306828d91bd000000162d49a47082c02c20001c0000321ee126f2279f898c108dd807ab36080000901300000805fcc99dd0bafc0e75207c000030929803c00001c44e00002469dd4b5d0013727e0c612b456381fe00003c18d221308254400c9c154009f04104330ac815c91b81425e109ffc00460a4900ff93aa1c123166cb8846c03780000c388b8447c054a0579000031226c071a486200000814ed08c400000064c000000000807c527fe41ffb698f419b329460014b0037c4ec5614280f0504000000e10acc97500001d0cf80b65c2f3e01cd024980679926582a5f556900002011be04684101917f2412cd472f8d74a081c00002034608f946742013da0ade8127a028f86cb1498e48300061500765112bc29010b79812900ab7496458b2582cbe03e394aa0005b413ab458782d7c08ce8d78c2003815b000000000d0be400003440848f760862c5a3e00940428c15dcc80b20160882c106940000000000000e0859c2ba000024177826140053c007fc1140000282caa21e9c08050be8882315adfc260e0312c137000028269998eb897370b1d807e500ef42bc202605063e07c782528509149e9e69f5818ce078588f3d07bb8323e4ba40000c10a4816a6080fc190740ff802038997060ad0a92d115c4410802fd197150662275a80b2f10d7421db07be89efd1599c018f05f752f00000106e6a08d0d13a015eb501ed40ce806c321da622134ac550bd842fa1c55a4a50400a0000342e170b3792420000151d89079c0000904bb80cae1b3d4021007b541fb906cae24ea168b00f4a0c254059e43809244501fd40fd2008d01a4d196dc1aa2445240e9d4951144331223181b206658011e02474a062047d82cea00d50068149)))
def g237D9 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x1030810051911030811524002440c20450064440c20524050094451030814900091440c10804912051030500930084451030814900091440c2040407485103091054009f96db19508a379506c1e003fea1fe50fea87f143fc41fd20fe107f843fa21fc10)
def g237H9 (j : Nat) : Nat := if 3 ≤ j then 0 else (if j<1 then (0xe1380000a46f0000f74e0000f41da0795147d27c0000000000000000c0580000000000000000e0690000405e20670000c87c000014260000000000000000000000000000801700000000000000000000000062510000000000000000000000000000e25a000000000000000000000000000000006111e248000061120000000000000000000000000000000000000000f059517ee1818116440400000000e033500600000000000000000000e166f7400000e05f00000000537900000000000000000000000000000000303bd2130000104f0000d405000000000000000000000663603c00000000000000001028102e0000b11b12460000000000000000000000000000000000005253655d0000b11e175b000074430000b086a114000074440000000000000000000000000000000000000000000000000000000000009450000000000000f082102a1057640f0000b0040000000000000000000000000000b24300001063827300000000000030551039545c0000706d0000000000000000000020070000000000000000501f00005032000000000000000000000000000000000000000000000000000000000000000000000000000000000000b3460000000046780000000000000000e2470000512e000000000000000000000000f26c000000000000695fb74f00002046000000000000d24f02120000000000009250000000000000000000000000000050650000000000000000000000000000841000000000000000000000306f0000000000003077000000000000000000000000a068724e00000000000000000000000000005782000000000000000091809013000062620000000000000000685ab0300000f43f0000000000000000000000000000000000000000000000000000000000000000967000000000802900000000000011370000e74b000000000000000000000000000061848056f1360000000000000000000000000000000000000000705d0000d04d40150000000000000000000000009466517f720c9076d468455400005542000000000000e014a24500000000c35f0000000000000000f24000000000007d0000c12c00000000000000000000000000000000000000000000000000000000465d00000000000000000000c08391357775000000000000813d000000001578000084380000000000007038a0520000000000000000000070800000b475074c00000000074d0000d05cd045e4510000000000000000000000000000a03f700f003ac51e27500000000000000000000000000000000000000000000000000000000000000000c13400000000707c000000000000703dd03654290000000000000000802d0108a010245260820860801069100200203b080250018800600200202) else (if j<2 then (0x563000000000000b0516072b664000000317269000000000000000000008002000000000000000000000000000000000000c75c60010000155e000012160000000000000000000000000000000000000000000000000000100000000000100800000000000000000109000000000000000000000000000000000000c01222590000000000000000b06b00000000000000002249327400000000d24a00000000042b000000000000000000002210000000009511f00a00000000000000000000c04300000000373f00002165000000000000000000000000000000000000e04e000000000000000000000000717d000000000000f18200000000e01000000000000000000000000000000000610a0000675100000000196000000000000000000000000000000000d0210000000000000000000000000000000000660000000000000000000000000000000000005129000000000000000000000000000000000000000000000000000000000000908100000000000000000000607f00000000000000000000000000000000945b806e0000000000000000b0490000000000000000a44000000000000014640000000000000000218600000000644e000000000000000000000000000000009062701e0000c7380000000000000000000086770000000000000000000000001084000000000000326a00000000000000000000000000007258000000000000e04181390000000070190000f5550000000000000000204400000000000000000000736000000000000000000000000000000000000000000000702c0000000000000000000000000000000000005025f65e000000000000000000000000607b27760000000000000000a261307a34700000e13e0000000000000000a859517b000000000000117cb06c0000e0340000b0746476202700000000501a000000000000d66f0000000000000000000090050000f003000000004040b02fe0640000d0260000000000000000000000000000000000000000208500000000f244000000000000113a11150000e46500000000e0750000305300000252210b721800009541601100000000000000000000000004820000706000003048604c906100000000413b0000000000000000424d000000005183f05a0000000000000000800e007e84637119000000000000000000000000000000000000102b3874607155776519704bc03700000000d03e00000000000000000000846700000000886800000000007000000000611f00780000244f205b000000000000a26ba57000001215601b000000000000a00bd018520f6009897a000000000000000000000000000000000000000000006022000000000000000000000000000000000000b01c8211b5640000b06ab00c0000f4280000b073000000000) else (0xc00d0000000000000000000000007047000000000148000000000000000000000000000050540000374a00000000e10800000000000000000000b042000000000000000000000000000078730000621400000000000000000000000000000000d0200000000000000000000000000000000000000000e1280000000000000000000000000000e56fe03500000000f01dd04a0000a01651850000b02403580000c979000000000000000000000000000000000000000000000000037a0000523f000000000000e217e023605000000000000000000000f)))
def g237D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g237H10 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x5a358380000001451812a491c00e1ad999836a4000291000209e1a7148000000130005080003c3c24b08c490001ba800000000223f41000604b13834ea953464493100020a00000074301880070180018af33d82e01528704021538428c89442900438e923329aafb91990002a9e22f33244492e0214a94398840022420c9061)
def g237L : Nat → Packing
  | 4 => (1,6,5,0,0,0,0,g237D4)
  | 5 => (174,5,5,0,0,11,0,g237D5)
  | 6 => (1091,4,5,0,0,14,0,g237D6)
  | 7 => (804,3,5,0,0,15,0,g237D7)
  | 8 => (135,2,5,0,0,13,0,g237D8)
  | 9 => (10,1,5,0,0,9,0,g237D9)
  | 10 => (1,0,5,0,0,0,0,g237D10)
  | _ => emptyPacking
def g237I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g237H5
  | 6 => lookupWord 77 461 6 16 8 4 g237H6
  | 7 => lookupWord 475 2591 8 19 11 4 g237H7
  | 8 => lookupWord 360 1657 8 18 10 4 g237H8
  | 9 => lookupWord 76 1129 3 16 8 4 g237H9
  | 10 => lookupWord 15 79 5 12 4 4 g237H10
  | _ => fun _ => none
def g237 : Forest := ⟨237,10,fun i => g237Y[i]?.getD (0,0),g237C,g237A,g237L,g237I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P4_0 : block g237 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B4 : block g237 4 0 1=true := g237P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P5_0 : block g237 5 0 96=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P5_96 : block g237 5 96 78=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B5 : block g237 5 0 174=true := (@block_merge g237 5 0 96 78 g237P5_0 g237P5_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_0 : block g237 6 0 2=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_2 : block g237 6 2 47=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_49 : block g237 6 49 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_145 : block g237 6 145 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_241 : block g237 6 241 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_337 : block g237 6 337 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_433 : block g237 6 433 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_529 : block g237 6 529 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_625 : block g237 6 625 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_721 : block g237 6 721 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_817 : block g237 6 817 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_913 : block g237 6 913 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_1009 : block g237 6 1009 82=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B6 : block g237 6 0 1091=true := (@block_merge g237 6 0 433 658 (@block_merge g237 6 0 145 288 (@block_merge g237 6 0 2 143 g237P6_0 (@block_merge g237 6 2 47 96 g237P6_2 g237P6_49)) (@block_merge g237 6 145 96 192 g237P6_145 (@block_merge g237 6 241 96 96 g237P6_241 g237P6_337))) (@block_merge g237 6 433 288 370 (@block_merge g237 6 433 96 192 g237P6_433 (@block_merge g237 6 529 96 96 g237P6_529 g237P6_625)) (@block_merge g237 6 721 192 178 (@block_merge g237 6 721 96 96 g237P6_721 g237P6_817) (@block_merge g237 6 913 96 82 g237P6_913 g237P6_1009))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_0 : block g237 7 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_7 : block g237 7 7 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_103 : block g237 7 103 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_199 : block g237 7 199 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_295 : block g237 7 295 42=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_337 : block g237 7 337 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_433 : block g237 7 433 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_529 : block g237 7 529 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_625 : block g237 7 625 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_721 : block g237 7 721 83=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B7 : block g237 7 0 804=true := (@block_merge g237 7 0 337 467 (@block_merge g237 7 0 103 234 (@block_merge g237 7 0 7 96 g237P7_0 g237P7_7) (@block_merge g237 7 103 96 138 g237P7_103 (@block_merge g237 7 199 96 42 g237P7_199 g237P7_295))) (@block_merge g237 7 337 192 275 (@block_merge g237 7 337 96 96 g237P7_337 g237P7_433) (@block_merge g237 7 529 96 179 g237P7_529 (@block_merge g237 7 625 96 83 g237P7_625 g237P7_721))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P8_0 : block g237 8 0 12=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P8_12 : block g237 8 12 51=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P8_63 : block g237 8 63 72=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B8 : block g237 8 0 135=true := (@block_merge g237 8 0 12 123 g237P8_0 (@block_merge g237 8 12 51 72 g237P8_12 g237P8_63))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P9_0 : block g237 9 0 10=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B9 : block g237 9 0 10=true := g237P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P10_0 : block g237 10 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B10 : block g237 10 0 1=true := g237P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237T : checkedTables g237 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g237 0 0 0 = true)
  · exact (rfl : block g237 1 0 0 = true)
  · exact (rfl : block g237 2 0 0 = true)
  · exact (rfl : block g237 3 0 0 = true)
  · exact g237B4
  · exact g237B5
  · exact g237B6
  · exact g237B7
  · exact g237B8
  · exact g237B9
  · exact g237B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237G : graphValid g237 (boundsBefore K231) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low237 : Lower true (varsX 237) (qG_ 237) 11 := lower_forest (g:=g237) (i:=0) (hints:=33555715) (before_sound K231 V231) g237G g237T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior509 : Lower true (varsX 509) (qG_ 509) 12 := by
  have h := lift_ok (u := true) (ms := ([]).map swapRows ++ fixRows 16 0)
    (raw := varsX 509) (T := qG_ 509) (xs := [(inputs.getD 4 zero,1,17)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low237
  have card : (([(inputs.getD 4 zero,1,17)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior507 : Lower true (varsX 507) (qG_ 507) 12 := by
  have h := lift_ok (u := true) (ms := ([33]).map swapRows ++ fixRows 16 0)
    (raw := varsX 507) (T := qG_ 507) (xs := [(inputs.getD 4 zero,1,17)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low237
  have card : (([(inputs.getD 4 zero,1,17)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior503 : Lower true (varsX 503) (qG_ 503) 12 := by
  have h := lift_ok (u := true) (ms := ([67]).map swapRows ++ fixRows 2 0)
    (raw := varsX 503) (T := qG_ 503) (xs := [(inputs.getD 1 zero,16,18)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low237
  have card : (([(inputs.getD 1 zero,16,18)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior495 : Lower true (varsX 495) (qG_ 495) 12 := by
  have h := lift_ok (u := true) (ms := ([33]).map swapRows ++ fixRows 4 0)
    (raw := varsX 495) (T := qG_ 495) (xs := [(inputs.getD 2 zero,32,36)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low237
  have card : (([(inputs.getD 2 zero,32,36)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior510 : Lower true (varsX 510) (qG_ 510) 10 := by
  have h := lift_ok (u := true) (ms := ([64,65,67]).map swapRows ++ fixRows 64 0)
    (raw := varsX 510) (T := qG_ 510) (xs := [(inputs.getD 6 zero,2,66)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low175
  have card : (([(inputs.getD 6 zero,2,66)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior479 : Lower true (varsX 479) (qG_ 479) 10 := by
  have h := lift_ok (u := true) (ms := ([33,84]).map swapRows ++ fixRows 64 0)
    (raw := varsX 479) (T := qG_ 479) (xs := [(inputs.getD 6 zero,2,66)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low175
  have card : (([(inputs.getD 6 zero,2,66)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior447 : Lower true (varsX 447) (qG_ 447) 10 := by
  have h := lift_ok (u := true) (ms := ([33,84]).map swapRows ++ fixRows 32 0)
    (raw := varsX 447) (T := qG_ 447) (xs := [(inputs.getD 5 zero,1,33)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low175
  have card : (([(inputs.getD 5 zero,1,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior446 : Lower true (varsX 446) (qG_ 446) 9 := by
  have h := lift_ok (u := true) (ms := ([64,65,67]).map swapRows ++ fixRows 0 0)
    (raw := varsX 446) (T := qG_ 446) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low175
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior415 : Lower true (varsX 415) (qG_ 415) 9 := by
  have h := lift_ok (u := true) (ms := ([33,84]).map swapRows ++ fixRows 0 0)
    (raw := varsX 415) (T := qG_ 415) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low175
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior508 : Lower true (varsX 508) (qG_ 508) 8 := by
  have h := lift_ok (u := true) (ms := ([16,65,66,67,100,101]).map swapRows ++ fixRows 16 0)
    (raw := varsX 508) (T := qG_ 508) (xs := [(inputs.getD 4 zero,64,80)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low173
  have card : (([(inputs.getD 4 zero,64,80)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior506 : Lower true (varsX 506) (qG_ 506) 8 := by
  have h := lift_ok (u := true) (ms := ([16,66,67,100,101]).map swapRows ++ fixRows 16 0)
    (raw := varsX 506) (T := qG_ 506) (xs := [(inputs.getD 4 zero,2,18)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low173
  have card : (([(inputs.getD 4 zero,2,18)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior502 : Lower true (varsX 502) (qG_ 502) 8 := by
  have h := lift_ok (u := true) (ms := ([16,67]).map swapRows ++ fixRows 64 0)
    (raw := varsX 502) (T := qG_ 502) (xs := [(inputs.getD 6 zero,2,66)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low173
  have card : (([(inputs.getD 6 zero,2,66)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior494 : Lower true (varsX 494) (qG_ 494) 8 := by
  have h := lift_ok (u := true) (ms := ([16,66,67,100,101]).map swapRows ++ fixRows 4 0)
    (raw := varsX 494) (T := qG_ 494) (xs := [(inputs.getD 2 zero,32,36)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low173
  have card : (([(inputs.getD 2 zero,32,36)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior477 : Lower true (varsX 477) (qG_ 477) 8 := by
  have h := lift_ok (u := true) (ms := ([48,101]).map swapRows ++ fixRows 16 0)
    (raw := varsX 477) (T := qG_ 477) (xs := [(inputs.getD 4 zero,1,17)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low173
  have card : (([(inputs.getD 4 zero,1,17)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior475 : Lower true (varsX 475) (qG_ 475) 8 := by
  have h := lift_ok (u := true) (ms := ([33,84]).map swapRows ++ fixRows 64 0)
    (raw := varsX 475) (T := qG_ 475) (xs := [(inputs.getD 6 zero,2,66)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low173
  have card : (([(inputs.getD 6 zero,2,66)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior471 : Lower true (varsX 471) (qG_ 471) 8 := by
  have h := lift_ok (u := true) (ms := ([48,67,101]).map swapRows ++ fixRows 2 0)
    (raw := varsX 471) (T := qG_ 471) (xs := [(inputs.getD 1 zero,16,18)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low173
  have card : (([(inputs.getD 1 zero,16,18)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior463 : Lower true (varsX 463) (qG_ 463) 8 := by
  have h := lift_ok (u := true) (ms := ([48,33,101]).map swapRows ++ fixRows 4 0)
    (raw := varsX 463) (T := qG_ 463) (xs := [(inputs.getD 2 zero,64,68)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low173
  have card : (([(inputs.getD 2 zero,64,68)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior445 : Lower true (varsX 445) (qG_ 445) 8 := by
  have h := lift_ok (u := true) (ms := ([]).map swapRows ++ fixRows 16 0)
    (raw := varsX 445) (T := qG_ 445) (xs := [(inputs.getD 4 zero,1,17)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low173
  have card : (([(inputs.getD 4 zero,1,17)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior438 : Lower true (varsX 438) (qG_ 438) 7 := by
  have h := lift_ok (u := true) (ms := ([16,67]).map swapRows ++ fixRows 0 0)
    (raw := varsX 438) (T := qG_ 438) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low173
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior411 : Lower true (varsX 411) (qG_ 411) 7 := by
  have h := lift_ok (u := true) (ms := ([33,84]).map swapRows ++ fixRows 0 0)
    (raw := varsX 411) (T := qG_ 411) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low173
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior383 : Lower true (varsX 383) (qG_ 383) 9 := by
  have h := lift_ok (u := true) (ms := ([33]).map swapRows ++ fixRows 20 0)
    (raw := varsX 383) (T := qG_ 383) (xs := [(inputs.getD 2 zero,32,36),(inputs.getD 4 zero,1,17)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low109
  have card : (([(inputs.getD 2 zero,32,36),(inputs.getD 4 zero,1,17)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior381 : Lower true (varsX 381) (qG_ 381) 8 := by
  have h := lift_ok (u := true) (ms := ([]).map swapRows ++ fixRows 16 0)
    (raw := varsX 381) (T := qG_ 381) (xs := [(inputs.getD 4 zero,1,17)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low109
  have card : (([(inputs.getD 4 zero,1,17)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior379 : Lower true (varsX 379) (qG_ 379) 8 := by
  have h := lift_ok (u := true) (ms := ([33]).map swapRows ++ fixRows 16 0)
    (raw := varsX 379) (T := qG_ 379) (xs := [(inputs.getD 4 zero,1,17)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low109
  have card : (([(inputs.getD 4 zero,1,17)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior375 : Lower true (varsX 375) (qG_ 375) 8 := by
  have h := lift_ok (u := true) (ms := ([67]).map swapRows ++ fixRows 2 0)
    (raw := varsX 375) (T := qG_ 375) (xs := [(inputs.getD 1 zero,16,18)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low109
  have card : (([(inputs.getD 1 zero,16,18)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior367 : Lower true (varsX 367) (qG_ 367) 8 := by
  have h := lift_ok (u := true) (ms := ([33]).map swapRows ++ fixRows 4 0)
    (raw := varsX 367) (T := qG_ 367) (xs := [(inputs.getD 2 zero,32,36)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low109
  have card : (([(inputs.getD 2 zero,32,36)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior504 : Lower true (varsX 504) (qG_ 504) 6 := by
  have h := lift_ok (u := true) (ms := ([33,50,84,117,118]).map swapRows ++ fixRows 48 0)
    (raw := varsX 504) (T := qG_ 504) (xs := [(inputs.getD 4 zero,64,80),(inputs.getD 5 zero,128,160)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 4 zero,64,80),(inputs.getD 5 zero,128,160)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior486 : Lower true (varsX 486) (qG_ 486) 6 := by
  have h := lift_ok (u := true) (ms := ([84,118]).map swapRows ++ fixRows 68 0)
    (raw := varsX 486) (T := qG_ 486) (xs := [(inputs.getD 2 zero,32,36),(inputs.getD 6 zero,2,66)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 2 zero,32,36),(inputs.getD 6 zero,2,66)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior478 : Lower true (varsX 478) (qG_ 478) 7 := by
  have h := lift_ok (u := true) (ms := ([]).map swapRows ++ fixRows 140 0)
    (raw := varsX 478) (T := qG_ 478) (xs := [(inputs.getD 2 zero,64,68),(inputs.getD 3 zero,64,72),(inputs.getD 7 zero,2,130)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 2 zero,64,68),(inputs.getD 3 zero,64,72),(inputs.getD 7 zero,2,130)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 3 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior476 : Lower true (varsX 476) (qG_ 476) 6 := by
  have h := lift_ok (u := true) (ms := ([33,84,117,118]).map swapRows ++ fixRows 24 0)
    (raw := varsX 476) (T := qG_ 476) (xs := [(inputs.getD 3 zero,64,72),(inputs.getD 4 zero,64,80)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 3 zero,64,72),(inputs.getD 4 zero,64,80)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior474 : Lower true (varsX 474) (qG_ 474) 6 := by
  have h := lift_ok (u := true) (ms := ([]).map swapRows ++ fixRows 136 0)
    (raw := varsX 474) (T := qG_ 474) (xs := [(inputs.getD 3 zero,64,72),(inputs.getD 7 zero,2,130)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 3 zero,64,72),(inputs.getD 7 zero,2,130)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior473 : Lower true (varsX 473) (qG_ 473) 6 := by
  have h := lift_ok (u := true) (ms := ([16,67,118]).map swapRows ++ fixRows 80 0)
    (raw := varsX 473) (T := qG_ 473) (xs := [(inputs.getD 4 zero,1,17),(inputs.getD 6 zero,8,72)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 4 zero,1,17),(inputs.getD 6 zero,8,72)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior472 : Lower true (varsX 472) (qG_ 472) 5 := by
  have h := lift_ok (u := true) (ms := ([33,50,84,117,118]).map swapRows ++ fixRows 16 0)
    (raw := varsX 472) (T := qG_ 472) (xs := [(inputs.getD 4 zero,64,80)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 4 zero,64,80)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior470 : Lower true (varsX 470) (qG_ 470) 6 := by
  have h := lift_ok (u := true) (ms := ([]).map swapRows ++ fixRows 132 0)
    (raw := varsX 470) (T := qG_ 470) (xs := [(inputs.getD 2 zero,64,68),(inputs.getD 7 zero,2,130)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 2 zero,64,68),(inputs.getD 7 zero,2,130)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior462 : Lower true (varsX 462) (qG_ 462) 6 := by
  have h := lift_ok (u := true) (ms := ([84,117,118]).map swapRows ++ fixRows 12 0)
    (raw := varsX 462) (T := qG_ 462) (xs := [(inputs.getD 2 zero,64,68),(inputs.getD 3 zero,64,72)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 2 zero,64,68),(inputs.getD 3 zero,64,72)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior455 : Lower true (varsX 455) (qG_ 455) 6 := by
  have h := lift_ok (u := true) (ms := ([84,117,118]).map swapRows ++ fixRows 5 0)
    (raw := varsX 455) (T := qG_ 455) (xs := [(inputs.getD 0 zero,128,129),(inputs.getD 2 zero,64,68)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 0 zero,128,129),(inputs.getD 2 zero,64,68)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior454 : Lower true (varsX 454) (qG_ 454) 5 := by
  have h := lift_ok (u := true) (ms := ([84,117,118]).map swapRows ++ fixRows 4 0)
    (raw := varsX 454) (T := qG_ 454) (xs := [(inputs.getD 2 zero,64,68)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 2 zero,64,68)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior414 : Lower true (varsX 414) (qG_ 414) 6 := by
  have h := lift_ok (u := true) (ms := ([118]).map swapRows ++ fixRows 12 0)
    (raw := varsX 414) (T := qG_ 414) (xs := [(inputs.getD 2 zero,128,132),(inputs.getD 3 zero,128,136)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 2 zero,128,132),(inputs.getD 3 zero,128,136)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior410 : Lower true (varsX 410) (qG_ 410) 5 := by
  have h := lift_ok (u := true) (ms := ([118]).map swapRows ++ fixRows 8 0)
    (raw := varsX 410) (T := qG_ 410) (xs := [(inputs.getD 3 zero,128,136)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 3 zero,128,136)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior406 : Lower true (varsX 406) (qG_ 406) 5 := by
  have h := lift_ok (u := true) (ms := ([118]).map swapRows ++ fixRows 4 0)
    (raw := varsX 406) (T := qG_ 406) (xs := [(inputs.getD 2 zero,128,132)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 2 zero,128,132)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior382 : Lower true (varsX 382) (qG_ 382) 7 := by
  have h := lift_ok (u := true) (ms := ([]).map swapRows ++ fixRows 44 0)
    (raw := varsX 382) (T := qG_ 382) (xs := [(inputs.getD 2 zero,32,36),(inputs.getD 3 zero,64,72),(inputs.getD 5 zero,2,34)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 2 zero,32,36),(inputs.getD 3 zero,64,72),(inputs.getD 5 zero,2,34)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 3 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior378 : Lower true (varsX 378) (qG_ 378) 6 := by
  have h := lift_ok (u := true) (ms := ([]).map swapRows ++ fixRows 40 0)
    (raw := varsX 378) (T := qG_ 378) (xs := [(inputs.getD 3 zero,64,72),(inputs.getD 5 zero,2,34)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 3 zero,64,72),(inputs.getD 5 zero,2,34)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior374 : Lower true (varsX 374) (qG_ 374) 6 := by
  have h := lift_ok (u := true) (ms := ([]).map swapRows ++ fixRows 36 0)
    (raw := varsX 374) (T := qG_ 374) (xs := [(inputs.getD 2 zero,32,36),(inputs.getD 5 zero,2,34)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 2 zero,32,36),(inputs.getD 5 zero,2,34)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior351 : Lower true (varsX 351) (qG_ 351) 7 := by
  have h := lift_ok (u := true) (ms := ([]).map swapRows ++ fixRows 13 0)
    (raw := varsX 351) (T := qG_ 351) (xs := [(inputs.getD 0 zero,8,9),(inputs.getD 2 zero,64,68),(inputs.getD 3 zero,1,9)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 0 zero,8,9),(inputs.getD 2 zero,64,68),(inputs.getD 3 zero,1,9)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 3 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior350 : Lower true (varsX 350) (qG_ 350) 6 := by
  have h := lift_ok (u := true) (ms := ([]).map swapRows ++ fixRows 12 0)
    (raw := varsX 350) (T := qG_ 350) (xs := [(inputs.getD 2 zero,64,68),(inputs.getD 3 zero,64,72)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 2 zero,64,68),(inputs.getD 3 zero,64,72)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior347 : Lower true (varsX 347) (qG_ 347) 6 := by
  have h := lift_ok (u := true) (ms := ([]).map swapRows ++ fixRows 9 0)
    (raw := varsX 347) (T := qG_ 347) (xs := [(inputs.getD 0 zero,8,9),(inputs.getD 3 zero,1,9)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 0 zero,8,9),(inputs.getD 3 zero,1,9)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior346 : Lower true (varsX 346) (qG_ 346) 5 := by
  have h := lift_ok (u := true) (ms := ([]).map swapRows ++ fixRows 8 0)
    (raw := varsX 346) (T := qG_ 346) (xs := [(inputs.getD 3 zero,64,72)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 3 zero,64,72)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior343 : Lower true (varsX 343) (qG_ 343) 6 := by
  have h := lift_ok (u := true) (ms := ([]).map swapRows ++ fixRows 5 0)
    (raw := varsX 343) (T := qG_ 343) (xs := [(inputs.getD 0 zero,16,17),(inputs.getD 2 zero,64,68)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 0 zero,16,17),(inputs.getD 2 zero,64,68)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior380 : Lower true (varsX 380) (qG_ 380) 5 := by
  have h := lift_ok (u := true) (ms := ([16,65,66,67,100,101]).map swapRows ++ fixRows 16 0)
    (raw := varsX 380) (T := qG_ 380) (xs := [(inputs.getD 4 zero,64,80)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low45
  have card : (([(inputs.getD 4 zero,64,80)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior366 : Lower true (varsX 366) (qG_ 366) 5 := by
  have h := lift_ok (u := true) (ms := ([16,66,67,100,101]).map swapRows ++ fixRows 4 0)
    (raw := varsX 366) (T := qG_ 366) (xs := [(inputs.getD 2 zero,32,36)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low45
  have card : (([(inputs.getD 2 zero,32,36)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior319 : Lower true (varsX 319) (qG_ 319) 6 := by
  have h := lift_ok (u := true) (ms := ([33,84]).map swapRows ++ fixRows 36 0)
    (raw := varsX 319) (T := qG_ 319) (xs := [(inputs.getD 2 zero,32,36),(inputs.getD 5 zero,1,33)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low45
  have card : (([(inputs.getD 2 zero,32,36),(inputs.getD 5 zero,1,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior310 : Lower true (varsX 310) (qG_ 310) 4 := by
  have h := lift_ok (u := true) (ms := ([16,67]).map swapRows ++ fixRows 0 0)
    (raw := varsX 310) (T := qG_ 310) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low45
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior283 : Lower true (varsX 283) (qG_ 283) 4 := by
  have h := lift_ok (u := true) (ms := ([33,84]).map swapRows ++ fixRows 0 0)
    (raw := varsX 283) (T := qG_ 283) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low45
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
def generatedKnown : List (Nat × Nat) := [(509,12),(507,12),(503,12),(495,12),(510,10),(479,10),(447,10),(446,9),(415,9),(508,8),(506,8),(502,8),(494,8),(477,8),(475,8),(471,8),(463,8),(445,8),(438,7),(411,7),(383,9),(381,8),(379,8),(375,8),(367,8),(504,6),(486,6),(478,7),(476,6),(474,6),(473,6),(472,5),(470,6),(462,6),(455,6),(454,5),(414,6),(410,5),(406,5),(382,7),(378,6),(374,6),(351,7),(350,6),(347,6),(346,5),(343,6),(380,5),(366,5),(319,6),(310,4),(283,4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem generatedPrior : Known true generatedKnown := by
  intro e h
  simp only [generatedKnown, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact prior509
  · exact prior507
  · exact prior503
  · exact prior495
  · exact prior510
  · exact prior479
  · exact prior447
  · exact prior446
  · exact prior415
  · exact prior508
  · exact prior506
  · exact prior502
  · exact prior494
  · exact prior477
  · exact prior475
  · exact prior471
  · exact prior463
  · exact prior445
  · exact prior438
  · exact prior411
  · exact prior383
  · exact prior381
  · exact prior379
  · exact prior375
  · exact prior367
  · exact prior504
  · exact prior486
  · exact prior478
  · exact prior476
  · exact prior474
  · exact prior473
  · exact prior472
  · exact prior470
  · exact prior462
  · exact prior455
  · exact prior454
  · exact prior414
  · exact prior410
  · exact prior406
  · exact prior382
  · exact prior378
  · exact prior374
  · exact prior351
  · exact prior350
  · exact prior347
  · exact prior346
  · exact prior343
  · exact prior380
  · exact prior366
  · exact prior319
  · exact prior310
  · exact prior283
def generatedSamples : Array (Bits × Bits) := #[(BitVec.ofNat 152 (0x707fc400f400014980c412cc1106932673ff), BitVec.ofNat 152 (0x89088555474000148804412cc000291023155)),(BitVec.ofNat 152 (0x78f80000d0000298e0100a30f229b1cdb9ccc), BitVec.ofNat 152 (0x199188c0000000298a0000a305008b144a94cc)),(BitVec.ofNat 152 (0xf800000032000531f00228c3f0cce3e0e3e0f0), BitVec.ofNat 152 (0x399399c000000531d00028c35044a3a0e3e0f0)),(BitVec.ofNat 152 (0x7c0c010a63e004c30fc00f0fc00fc00ff), BitVec.ofNat 152 (0x732733800000a63a004430e400f0fc00fc00aa)),(BitVec.ofNat 152 (0xff8030020c7c000703f0000ff0000ffff00), BitVec.ofNat 152 (0x622633000000c7400050390000ff0000b54a00)),(BitVec.ofNat 152 (0xfff0000803c8f800007fc00000ffffff000000), BitVec.ofNat 152 (0x4224222aab88e800007f800000bb544a000000)),(BitVec.ofNat 152 (0x33fc0f0000007fffffff000000000000), BitVec.ofNat 152 (0x3ffffd0000002bc618aa000000000000)),(BitVec.ofNat 152 (0x3c000fffffff80000000000000000000), BitVec.ofNat 152 (0x84484400000210842500000000000000000000)),(BitVec.ofNat 152 0, BitVec.ofNat 152 0)]
def generatedColumns : List ColumnInfo := [(2,0,509,0,12),(4,0,507,0,12),(8,0,503,0,12),(16,0,495,0,12),(1,0,510,0,10),(32,0,479,0,10),(64,0,447,0,10),(65,0,446,0,9),(96,0,415,0,9),(3,0,508,0,8),(5,0,506,0,8),(9,0,502,0,8),(17,0,494,0,8),(34,0,477,0,8),(36,0,475,0,8),(40,0,471,0,8),(48,0,463,0,8),(66,0,445,0,8),(73,0,438,0,7),(100,0,411,0,7),(128,0,383,0,9),(130,0,381,0,8),(132,0,379,0,8),(136,0,375,0,8),(144,0,367,0,8),(7,0,504,0,6),(25,0,486,0,6),(33,0,478,0,7),(35,0,476,0,6),(37,0,474,0,6),(38,0,473,0,6),(39,0,472,0,5),(41,0,470,0,6),(49,0,462,0,6),(56,0,455,0,6),(57,0,454,0,5),(97,0,414,0,6),(101,0,410,0,5),(105,0,406,0,5),(129,0,382,0,7),(133,0,378,0,6),(137,0,374,0,6),(160,0,351,0,7),(161,0,350,0,6),(164,0,347,0,6),(165,0,346,0,5),(168,0,343,0,6),(131,0,380,0,5),(145,0,366,0,5),(192,0,319,0,6),(201,0,310,0,4),(228,0,283,0,4)]
def genData7 (j : Nat) : Nat := if 1 ≤ j then 0 else (0xe583fe1fe109e11c0f786f85f802e43fe1fe106145911b87f802643fe005c11c0ff87f84f83780304d28c643ee1fe00bb0d56933d98c96330d50873915c90210038dae97a0e89985d950e36ba5e43a2659875438dae57a0e899661d50dc6bb5ec9965c1755834f8f01b95d59260660c3cfb3ec9a99e176542ed8f15ba41d9260660b3e3c06d59764981983c58565705d59260660d199c36d07941d865433586d5b2684905d570cd19b76cda4255075433466d5b3690905d570c8e5c26c4a75a1765431666ddb3690905d570)
def genData8 (j : Nat) : Nat := if 3 ≤ j then 0 else (if j<1 then (0x35f5d0744cab0eb06beb90e899561d60d7b761d1b2ac3ac1af6e83a3655875835edd034bc9b0eb06bdb90e8d9561d60d79f47d1330bb2a1af3e8fa2661755835e7d1f44cbb0ca86bcfa3e899661d50d79f47d132ac3ac1adee97a065d865435bdd2f40cb30ea86b6fb5e89985d560d6df4bd1330baac1adbe97a265d865435b7d2f44cb30ea86b5fb5e8d985d560d6bf4bd1b30baac19faec3a2661765433f5d0744cc2eca867eb90e899561970cfb740d2f26c32e19f6e43a3655865c33e7d1f44cc2eca8677ba5e81985d950cef34ad0730bb2a19dbe97a2661765431f7dc744cc2eca863efb26a6785d950c7df51d1330bb2a17baec9a55d907582f3cd874acb2eab05bf3b06959760660b7b760d2f26c3ac16f6ec195e4d87582de7d934bc9b0eb05bcfb26579361d60b5f36144ad0bb2a16bbec9a75a176542bedd834bc9b0cb857dbb06579361970afb36bd0726c32e15f66d790e4d865c2be7d934bc9b0cb857cfb26979360176af9f64caf26c32e15f3ec995e4d805dabe7d930bc9b00bb53efb26a196a1d5097df64d4cf0bb2a1e785c37564981983cf0b82eac9303307971595c17560660f0f2d0baae0bb2a1cf85e507649819839f083b2ac9303307365595d59260660e63b0ad1b2842ae1cb6e5b90e4d875838f2bceeac93033071e5795d59260660e2f730baae0bb2a1c5d65d595d58198378cd9b484aa0ea86de1b2684905d570db3366d2120baae1b5c6d5a1241755c36acbaf46cb20ea86d39b76909541d50da736ad2120baae19f86c9a1241755c33f0d0344c890ab86799b3690905d570cf3340d1b2842ae196e6dda4241755c32dcd3b40ca10ab8659da768d9421570c7cb64d092ec32a18f969da2644855c31f2d3344c890ea863cfa3e89985d950c73b4ed1b2842ae18dee97a0661765431bdd2f20cb30ea86379a5683985d950b8f76acb2e0baac171e6db955c175582df0d86eac9303305be1b0a9d9260660b6e760acaeac0cc16d9ed5a764981142cbcdb730baa0ea853e7b565d9260660a7cb73bab24c0cc14f96e6a7649819829f2dcd4ec93022853e5b95d59260660a79f64d2f26c3ac14f3ec995e4d875829e7d930bc9b00bb4debb269b905d5709af76ad3700baae135e6d7a061b755c25f9d8352bab03304bf1b7e81956066096f361d2aecc2ee12d7ecda8dd57558247f5c94eb42eca847ebb269b905d57087df64d4cf0bb2a18dce61a125d501431b5cc3444baa028627b986989754050c2f75354aa0c38a185ee9ea7e61501430bdcbb514baa0285971b12a55061c50b2e36253aa0c38a165a6c8a954187142cb4d914ea830e285879b62a55061c50b0f36c53aa0c38a14dc6c4a7e61501429b4d914fcc2a0285279b629f9854050a3b3663ca0ec32a146e6d07941d8654247ad894eb42eca848edb229d685d950) else (if j<2 then (0x2f801fc3f85f0030d409243b45f87f0be0fc020350240a8a1ea2fc3f85f07e01249d04d8860ec13e1fc2d83d00924e07c0ca0960ec13e1fc2d83d00a09a42662fc3f85f046c13c1f827c3f85b07a00e0a813854510c1fe1fc2f83f00905e4ae0ca93812e2383f04f87f08a24e826c4707e09f0fe16c1209381f03282783f04f87f0b60f40280ca09e0fc17827c3f85b07a0120bc9581cb11c1f827c3f85b049e0ff0f617c013e1fc00be1fc00819c2b85552243e84f87f0be0120a8a4487f87f0be0fc01c127c3f85f004038425827c3f85f04609b027e1fc2f822fc3f85f003b0f917e1fc1f802fc3f85f07e009523427c3f85f005f87f0be00609c0dcd59a842583b04f87f0be0dc02c1381b9ad35085307609f0fe15c1f80582703735083b04f87f0be0fc0241381bc0ff0fe17c1f80382703781fe1fc2f83f00703741e827c3f85f07e00e09c0e01bc0ff0fe17c1780401c03655303e04f87f0be0bc0241381d03781fe1fc2783f00803a06caa607c09f0fe13c1f80482704806d03fc3f85f07e0100900d95440f813e1fc2f83f00904e06cea607f87f0be0bc0201381b3a981fe1fc2783f00804e06cea207f87f0be0fc02013708c0fd1bc2fc3785f07e01229f84607e8de15e1fc2f83f00906582303f85f09f0fe17c17804825c1181fc2f84f87f09e0fc02650893de4c5927a477914243490363fc8fae3c48ea23768d6a3288c322f08b7e2c38a4625f88e221c885a1fa87a61d886f21ab866a173855e146847e10383ca0d682be0a9828e092823207b817e043809e0167fbdfd37f09fb17e55f797d75f4c7cc1f1f7c39efd7b85edb7afdeb97aa1e8c79ede5478e1e1c782dde47721da17615d697561d4774d9d3074a9d247479d1872bdc306ef1b3d6b25a55678596d64ed8dd61a58215eb57235abd63b56f1548537d4604fdd3834c1129b48711a844d10e1418900f3fccf7f3d60f313c28eac390cdda3598d1e332cc622fb8b902c70ab32928a1827f09e025dc92423c88aa21b484620247d71e687731bd067518305b9159851312d444c0fb83850c9c2be0980202069013b03480690003eacbaf46cb20ea87cebb2659705d560f8f76acb2e0baac1ef86e90764981983df0bd20ec9303307b67b569d9260450edd764cb2e0baac1d9bed7a265975583b37d2f44cb2eab073ebb0e89985d950e7d741d1330bb2a1cfae43a2659875439f2dab2ec93033073dbb35e3905d560e7b760caf26c3ac1cf3ec9a5e4d875839e7d932bc9b0eb073cfb26179360176e79f47d1330bb2a1cdee97a0661765439bdd2f20cb30ea8736fa5e89985d950e6df2bd132cc3aa1b9be97a2659755836edd8746c32eab86ddba0e8d865d570d7e760d4aeac0cc1afaec3a265d865435f5d8744cb30ea86bebb0e899561d60d7d741d132ec32a1afae83a26598754) else (0x64a2303dc21243821a884487f82202803e064303235a04870a20cb050e844870819a08b821a0806e0828ad127c00d12287081781c711c10406521c20644ac927c012c43c10a133c109e082f0ae0840ac127c2f82202b049f0be0888ad127c00d12687080064a1c20640b0407845c10ae0837041448e13e0068afe005f001456c1fe006892e105f001249b082456c1fe006001c1c101e10209283840ae4384892e085f001448e17e0068afe0057081f800f08b821384f80122bf8011240515fc00b838341c1a0e0b85f80101f09e084060706042870904820c983ec20c197c00b83ec20b610209103b840e126070819307d841832f801032a0e1032078383c1c1000000009391b41362183fc3f85b07a0124ac9381f41362183b04f87f0b60f402c15c2703842683ac5f87f0be0f4028158248a842103d85d09f0fe17c1f80592b24e06404d07a09f0fe16c1e80512b03806404d8860ec13e1fc2d82512b03e0710ca09e0e717827c3f84522a44e0850d850491b0ee17c1f805107f87b0be00849c0e219b11c1f827c3f84402f24e07d0ca09b11c1f827c3f845508c0ff0fe17c1f8032270384264470798bc13e1fc2f82542704628a0d890911217825c3785f07e01909c0f81c11321e427c3f84f06e01509c1182111921e425c3785f07e0140aa1381c22a22643b45f87f0be0dc02c1922b44ea2303b85e09f0fe0fc02813c1b121223825c3f85f07e0120aa1382123023243b45b87f0be0fc02e1381c11321e427c3f84f06e01289c0f85e03992322b84f87f0b601509c1182113423243c84b86f0be0fc02d138230c408724645709b0fe01209c1091862823243c84b87f0be0fc02c1382113192322d84d87f0be0fc0281822704618810e48c8bb0fe0fc0286af08e0ff0fe13c1b803a2703e1794aa89c91917e1fc2b83b00b03e155c4387f87f0ae08ff0fe00489c31021530a3324645d8770be015f0fe17c00fe1fc)))
def genIndex8 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x377e085c0fc03cf0782d3e0f8783c172f02d38ec8f0493456af04ba822d504d7c1e0b6097c1e073783c13e0c8)
def genData9 (j : Nat) : Nat := if 7 ≤ j then 0 else (if j<3 then (if j<1 then (0x7661770adf6a3755d560abf69a9761950abf69a785d950abf2a5685d950a7f69e985d9509fee9596dc1709fee81985d9509fee8196dd5709fe69b905d5709fe697905d9709fe683985d9509fe683955db709fbe89985d9509f7e8d96e15708ffaa4985d9508ffaa4785d9508ff6a6785d950f1e559705d560ef841d9260660e7c5c37560660e7c5c17560660e7c5c17560470e7a5c37560a60e7a5c17560a60e7a5c17560870e765c17560c70e6e5c17561070e5eea55061c50e5ee9d5061c50e5ee617541d50e5ede275c1d50e5eaa55061c50e5e6a55061c50e5e5d507e1950e5e5d50761950e5e561705d660e5e2a55061c50e5e29d5061c50e5e2617541d50e3e5c1865d470d5ee5e9754050d5e2617541d50cfc6419121d50cfa6419221d50cf96899121d50cf96899121570cf965d9260660cf965d9260450cf96559260660cf96559260470cf96499121d50cf564d9121d50cf364d9221d50ced6519121d50ce768d9421570ce76559361070cdeea55061c50cdee9f9854050cdee639754050cdee629754050cdee619754050cdee609754050cdee579061d50cdea9f9854050cde69f9854050cde65590a1d50cde6559021d50cde2a55061c50cde29f9854050cde2617541d50cdd6559121d50cdb6559221d50cd76159321570ccf6159421570cbee5b9061d60cbe65990a1d60cbe6419621d50cbda599121d50cbd6599121d50cbba599221d50cbb6599221d50c7e66195dc270c7e1e50761950c5f9e39541d50bdc6849754050bda6889754050bd668c9541d50bce6909541d50b9e6989754050b7c684905d570b7a688905d570b7668c905d570b7668c7841d50b6e690905d570b6e6907841d50b5e69e7541d50b5e2a57541d50b3e698905d570afce819560660afc68478c1d50afc6847841d50afc6837560660afc6829760660afa68878c1d50afa6887841d50afa6837560a60afa6829760a60af668c78c1d50af668c7841d50aee69078c1d50aee6907841d50adeea19754050ade6a29754050ade69f9854050abe69878c1d50abe6987841d50a7eea1705d470a7768c7881d50a7768c7841d50a6f6907881d50a6f6907841d50a3f29d685d9509fc684905d5709fa688905d5709f668c905d5709ee690905d5709deaa09541d509de2a57541d509de2959081d509d768c9541d509cf6909541d509be698905d5708feaa77841d508feaa47841d508fd68697a1d508fd68498dd9508fd68497619508fd68497616608fd6849561e708fbe89985d9508fb68a97a1d508fb68898dd9508fb68897619508fb68897616608fb6889561e708f7e8d98dd5608f7e8d96e15708f768c97616608f768c9561e708ef69097616608ef6909561e708dfea585215708bfa9a97a1d508bf6989561e708bf2a5685d95087fea58721d5095e2a57541d50) else (if j<2 then (0xef7e8d9561d60ef7e8d8661570ef7e8d785d560ef76979361d60ef76579361d60ef76179360176edfe95985d560ebfa25685d950ebf69d685d950dfee81985d950dfee419561970dfe683985d950dfbe89985d950df76979361970df76979360176df76579361970df76579360176df76179360176cffea1985d950cff6a196a1d50bfee819561970bfe6979061970bfe683985d950bfbe89985d950bfbe899561970bfbe899560176bfbe89955d970bf7e8d9561970bf7e8d9560176aff6a6785d950f9e55b905d560f9e559705d560f5ee95705d560f5ee55705d560f5e5d59641d50f5e5d5705d950f5e5d50761950f3e65970dd560f3e659705d560f3e5d970dd560f3e5d9705d560efc5e50760660efc41d9560660ef9dd59260660ef9a9d9260660ef9a9d9260450ef969d9260660ef969d9260450ef95d59260660ef6e839361d60ef6e439361d60edee950761950ede5d50761950edd5657560660ebee5b9061d60ebe9a3905d970ebe5a1705d950eb7e9b9361d60eb7e5b9361d60e7d5e77560660e7d5e57560660dfc6819121570df96899121570df6e839361970df6e439361970df6dc39361970dee6819421570de768d9421570dbee8196dd560dbee81965d560dbee439559d60dbee419559d60dbe69b905d560dbe6839559d60dbe65b905d560dbe65990dd560dbe65970dd560dbe659705d560dbe5db905d560dbe5d990dd560dbbe89965d560db7e9b9360176db7e5b9360176db7ddb9360176d9fe95965d560d6f69d9421570cfee8198dd560cfee81985d950cfee61705d950cfee419661d50cfe683985d950cfe6839561b70cfe64196a1d50cfe5e3905d560cfd69d9121570cfd6999121d50cfd65d9560660cfbe89985d950cf7e979361d60cf7e8d98dd560cf7e8d96e1570cf7e579361d60cf7e179360176cf76979361d60cf76579361d60cf76179360176cef69d9421570bf6e8d9641d50bdee959641d50bde683755d560bbee957641d60bbee819559d60bbe6839559d60bbe68376e0176bbbe899559d60b9fe95765d560b9f69b755d560b7ee8196dd570b7ee8186dd570b7ee81865d570b7e69b905d570b7e69b805d570b77e8d86dd570b77e8d865d570b5fe95865d570afee819761950afee819661d50afee819561d60afee818761950afe69b7841d50afe6987841d50afe68395e0176afe6839561b70afe6829761950afe6828761950afde959760660afd6a77560660afd6a57560660afd684785d950afbe89985d950afbe89985d560afbe899761950afbe899661d50afbe899661770afbe899561d60afbe899561b70afb688785d950af7e8d98dd560af7e8d985d560af7e8d96e1570af7e8d9561d60af7e8d86e1570af7e8d8661570af7e8d78dd560af7e8d785d560adfe959661770adfe95785d560adfe95) else (0x784f0fc2707c02c54c2307d1b85e13c3f09c1f00a0acd4c2307d1b85e13c3f09c1f00b09cd4c2307e1b45c13c3f09c1f00b09c1dc50ce42b0731704f0fc2707c03254c2287e1b45e13c370bc1f00a09a48a1ec6d1784f0dc2f07c0282735308c1f86d1704f0dc2f07c02c270831433d0bc1cc5c13c370bc1f00c09c2135308c1f86d170470fc2f07c03027087143410cc1cc5c11c3f0bc1f00c0a82706c48e1c45e13c3f0bc1f00b6218771b85e13c3f0bc1f00909cc841cc5c13c3f0bc1f0090ad548220791b85e13c3f0bc1f00b0a8270901be2387e1784f0fc2f07c0302706d07413c3f0bc1f008851484d2849a8462841683d483a68364832282d6829e8252820681d881aa8172813080ee80c0807e80327ffa7fa47f4e7f027eb67e887e327df07dae7d947d707d247ce27caa7c7c7c447c027bca7b887b507b2c7b127ae47ab67a7e7a507a2279f4798a791678b6783877ba771e76aa763675c2754e74c6744873c0733872ba725071c8715470c27080703e6fca6f4c6ed86e786e186d906d3a6ce46c666be86b6a6ae26a8c6a3669e0696c68e4687a681067a6672866be665465ea6580650c648e642e63c4635062f06290623a61d0615c60fc60a660325fdc5f865f265ec65e705dde5d6a5cec5c965c225bc25b585aee5a7a5a1a59ba595a58c8584a57ea577656f85698562455ce555a54f05486541253a8533e52d4525651d85164510e50a4504e4ff84f844f244eb04e504de64d724cf44c764bf84b7a4b064a924a1e49b4495448d648804802478e472446ba464645e6457244fe448a441643b6436a430a42a0422241e0416c411640b640563fec3f823f183eae3e583de43d703d103ca63c463bdc3b543acc3a4e39da395238ca385637e2376e371836b8364e35f835a2355634ec3482341833cc336c32ee328e323831c4315a30fa307c2ffe2f6c2f022e7a2e062d882d0a2c8c2c0e2b902b262ac62a702a1a29b0295a28fa289a283a27ee2784272e26ce26782604259a253a24b2242a23c0234c22ec22782204219a212620c6205c20101fb01f501ed21e5e1dfe1d8a1d0c1c8e1bfc1b881af61a821a2219cc195818e4186617e8176a16f6167815fa157c15121494142a13ac135612f612a0124a11d6116c1102108e10240fb00f500edc0e680dea0d760d0c0cac0c560be20b6e0b0e0aae0a4409d0095c08e8086a07ec0782070e06a4063005bc053e04d4046a03f6037802fa027c020801a8014800d400560000ff6e8d9641d50fbe6957641d60fbbe89965d560fbbe899559d60f9fe95965d560f7ee81865d570f77e8d865d570efee819761950efee819661d50efee819561d60efee818661570efee419561d60efd6959760660efbe89985d950efbe89985d560efbe899761950efbe899661d50efbe899561d60ef7e8d985d56))) else (if j<5 then (if j<4 then (0xf07c0202706d5481e04f0fc2f07c0242706dd481fc3f0bc1f00809c1b15088c1c85c13c3f0bc1f00b06c551518761584f0fc2f06c0281b1518761584f0fc2b07c0242a0a4270801b13c48e1f84f0ec2f07c0342b0a8270841b14048e1f84b0fc2f07c0342b09d8801d86a13c3f0bc1f00a0ac271518801d86a13c3f0bc1f00b1508821d85613c3f0bc1f009154546218771b85e13c3f0bc1b00b06c551518861f85e13c3f0bc1b00b1518861dc6e1784f0fc2b07c0281b1585462187e1784f0fc2b07c02c2705107b1504f0fc2f07c0242b0930881f46e17c3f0bc1f00a06f07c13c3f0bc1f00709c1b35307c13c3f0bc1700909c1b35307c13c3f09c1f0090a42706c8f2230721704f0dc2f07c0302706c90223072170470fc2f07c02c2706cd441f04f0fc2f07c0242a09c1c22487d1484f0fc2f05c02c2c0a8270748a21f45213c3f09c1f00c0b82a09c2022c87d1484f0dc2f07c030270902006c5715388c1f85c13c370bc1f00e0a8270848c21f45211c3f0bc1f00b09c240841b16054e2307e170470fc2f07c0382a06c542230721704f0fc2f07c02c2706d0721504f0fc2f07c0242721f45213c3f0bc1f00813409a2107e1ac5413c3f0bc1d00b06c5515109c1f85c13c3f0bc1700b0a82715454e2307e1704f0fc2f05c0302735109a2107e1ac5413c3f0bc1d00c0ac2735009e2107e1904f0fc2f0740301b1585442b07e1704f0fc2707c02c2a09c5615388c1f85c13c3f09c1f00c09cd442a8841f86b1504f0fc2d07c0302b09cd402b8841f86413c3f0b41f00c15c5442f07e1704f0dc2f07c0282a09c5715388c1f85c13c370bc1f00c1605443307e170470fc2f07c0282a09c5815388c1f85c11c3f0bc1f00c09c1b41d04f0fc2f07c0202706cd441d04f0fc2f07c0242706e07813c3f0bc1f00815107e1704f0fc2f07c0202a09c2415107e1704f0fc2f07c02c2706c1421f45213c3f0bc1f00a15c5442f07e1704f0dc2f07c0282006c5442f07e1704f0dc2f07c02c581510cc1f85c11c3f0bc1f00a0841b1510cc1f85c11c3f0bc1f00b0920881f85e13c3f0bc1f00909c1cc508921f45213c3f0bc1700b09c1dc508a21f45213c3f09c1f00b0a4270831422c87d1484f0dc2f07c030270871423087d148470fc2f07c02c2706c88c1c85c13c3f0bc1f00a09c1b95107413c3f0bc1f00906e0761604f0fc2f07c0202006c8f42f0721704f0dc2f07c02c2106c90433072170470fc2f07c02c27c5087d1484f0fc2f07c024546230761704f0fc2f07c0242715388c1f85c13c3f0bc1f00a06c5515388e1f85e13c3f0bc1700b15454c2307d1b85e13c3f0bc1700b0acd4c2307d1b85e13c3f0bc1700b09c1c35308c1f86d1704f0fc2f05c030270731433509c1cc5c13c3f0bc1700c89308c1f46e1784f0fc2707c0281b15854e2387e1) else (0x70bc1f00a8af08a1f86d1784f0dc2f07c0283289e48a1ec6d1784f0dc2f07c02e2b89288c1ec5f0dc2f07c0243289e48a1ec6d1784f0dc2f07c02c328ae2709a2492287b1bc3f07c02e2495308a1f86d1784f0dc2f07c02c3209a54c2287e1b45e13c3f07c02c310ab14a1d45f0fc2f07c0246aa1d45f0fc2f07c01c310aa14a1d45f0fc2f07c024320c46a09d87917c3f0bc1f00a0ac243510841d46e1784f0fc2f07c0310751bc3f0bc1f0060ad548220791b85e13c3f0bc1f00b0af08c1f46f0fc2f07c02031850c881f04f0fc2f07c02424c2107e1584f0fc2f07c0243109e1492087613c3f0bc1f00a0cc2a89d4821e84f0fc2f07c0283189f1452207a13c3f0bc1f00a0ac24c2107e1584f0fc2f07c02b1492107613c3f0bc1f0088ae24c2307d1b85e13c3f09c1f00b0ca2709a48a1ec6d1784f0fc1f00b0c82bc2307d1bc3f0bc1f00915308c1f46e1784f0fc2f07c028330c82bc2307f0fc2f07c0242b4208761945a13c3f0bc1f00a4ad2707c190278841f86413c3f0ac1d00d09c1b35109a2107e1ac5413c3f0bc1d00d0ac274268841f86b1504f0fc2f074030270541442507b1504f0fc2f07402c2706cd442a8841f86b1504f0fc2d07c0342d0ac2742a8841f86b1504f0fc2d07c034270581442907b1504f0fc2d07c02c2705c1442d07b1504f0f42f07c02c270601443107b1504d0fc2f07c02c2b09c1b81fc3f0bc1f0080ac2706e07813c3f0bc1f0090a82715307a1704f0fc2f07c02854c1e85c13c3f0bc1f0080ac2706e07f0fc2f07c0202706e07f0fc2f07c01c2b42207d1985a13c3f0bc1f00a0ad0881f4661684f0fc2f07c0282742087e1945213c3f0bc1f00a09c1b81fc3f0bc1f00709c1b55207813c3f0bc1f0090a82706c542230721704f0fc2f07c0302705087d1484f0fc2f07c0242706f07c13c3f0bc1f0080a81b15088c1c85c13c3f0bc1f00b154546218761584f0fc2f06c028546218761584f0fc2b07c0241f0705595388e1f85e13c3f09c1b00c07c5e0704d9238791784f0fc2706c0302f4ad2707c1902788c1f86c13c3f0ac1d00e49c1902707c1704f0fc2b0740281f0701902588c1f8671704f0fc2b07403419057140270771704f0fc2b07402c1b1585515388e1f85e13c3f09c1b00c06c5715454e2387e1784f0dc2f06c0301b15c5615388e1f85e13c370ac1f00c06c5815454e2387e178470fc2f06c030231882114248e1e45e12c370bc1f00c06818c500cc1dc5c12c2f07c0282b09c1b81e04f0fc2f07c0242b09c1b81fc3f0bc1f0080ac1b41d04f0fc2f07c0202b09c1bb5107413c3f0bc1f00a09c1b41d04f0fc2f07c0202706ed441d04f0fc2f07c0242a09e8761684f0fc2f07c0242b09c1b75207f0fc2f07c0242706e07f0fc2f07c01c2a09c54a1d85a13c3f0bc1f00a1508721484f0fc2)) else (if j<6 then (0xbc1f00c0cd0821d86d1684f0fc2f07c0283282107c1ac5613c3f0bc1f00a0cd0821d86d1684f0fc2f07c028544208761b45a13c3f0bc1f00a090544208761b45a13c3f0bc1f00b0c86a89d0821d86d1684f0fc2f07c0310821d86d1684f0fc2f07c024544208761b45a13c3f0bc1f00a0ce2b82287a1b45e13c3f09c1f00b4ad270490761bc3b0bc1f0090c92b49d0761bc3b0bc1f0094ad9441d86f0ec2f07c020330c82b02287a1bc3f0bc1f00a0c0270845092245e12c3f0bc1f00b0c83109f0821fc3f0bc1f0090ac24c2107f0fc2f07c020320ac249530881e84f0fc2f07c02c2b0928821fc3f0bc1f0080c824c2107f0fc2f07c02031c524841d84f0fc2f07c024271528821d84f0fc2f07c0243209f0821fc3f0bc1f00809c1c25594134899238791784f0fc2f06c038559518861dc6e1784f0fc2f06c02c2f0ad2707009a2307b1704f0fc2f04c8ae24c2307f0fc2707c0203209988c1f8671784f0ec2f07c02c3289f08a1f45f0dc2f07c0243289e48a1f45e13c370bc1f00a0c988c1f8671784f0ec2f07c0283249188c1f8671744f0ec2f07c02c3249188c1dc5f0ec2f07c024324ac2649188c1fc3f07c024324ac2662307d13c3f07c02427084986505023248e1e45e12c3f0bc1f00e0ca2b89e24a2207e1704f0dc2f07c030242220761704f0fc2f07c0242b1a8271518791584f0fc2f07c02c320ac2422207a19c5c13c3f0bc1f00c82107c1ac5613c3f0bc1f0090c86a82107c1ac5613c3f0bc1f00b0ac07a1944f0fc2f07c020338ae08c1f06b1784f0fc2707c02c320ac6aa1e86517c3f0bc1f00a0c46a1518761a45f0fc2f07c0283109c248524821d84f0fc2f07c02c3109c2492087613c3f0bc1f00a0c4270924821d84f0fc2f07c028330ac2a52087a13c3f0bc1f00a0c42a09c240514821e84f0fc2f07c0303289e24c5248a1f45e13c370bc1f00c0ca2b89e48a1f45e13c370bc1f00b0c82ba1d45f0fc2f07c020330930841f85613c3f0bc1f00a0ac24a2087f0fc2f07c020320ae8841fc3f0bc1f0082a82406f0841f85613c3f0bc1f00b09c5462107c13c3f0bc1f00909c546210771b85c13c3f0bc1f00b0c42ba2107513c3f0bc1f0090c42bc524841d84f0fc2f07c0282b090d4c2107e1584f0fc2f07c02c2b0901b3530841f85613c3f0bc1f00c0bc2b82588c1f8671704f0fc2f0740302735109a2307e1ac5c13c3f0bc1d00c0bc2b07109a2307e1b04f0fc2f0740305515308c1f46e1784f0fc2f05c02e2b89308c1f46e1784f0fc2707c02e2b89308a1f86d1784f0fc2707c02e2b89308c1f85e13c3f09c1f00a8ae24a2287b1bc3f09c1f0090ce2ac5248a1ec6d1784f0fc2707c0322ba2307b17c3f09c1f0080ce2ac5248c1f46b1784f0fc2707c0305615308c1f46e1784f0fc2707c02e54c2287e1b45e13c3) else (0x32a220770840c86a22207a1bc118338ae08a1e8614338ae08c1dc114330ac6a02287f07c01c3209e4821fc2f0060ca48a1dc2102b09184f0bc1f0060ac2421fc2f07c018320ac24a23c2f07c01c2b09e4821fc0142b0928841fc2f07c01c2f0ac1c82588717041e2b893c2704489287f09c1122b89307f09c1162b89287b1bc270468ae24a22c5f09c11a24a1dc2f0448ae24a22c570bc118328ae48a1ec6d15c21c32c2287d15c214324ad2462307716c2f0480c92b09924621c5b0bc120326230771744b0bc11c330ac24a1fc2f07c01c2426e0791840cc320909b55207f0bc1202b09184f0bc1f0060ac24923c2f07c01984f002c1fc270430c92452307d1ac2f0474ad2462307b0bc1183209924523c1152b09924f0440c92b621c5f0450ac24c1fc2f07c0182b09287f0bc114320ae4841fc2f0060c94881e84f08509184f003893070a2bc1f46f0848af07d13c210338af07d1b84162bc1f4670848af07d11c2102bc1fc2f0441a90821d8651684f0fc2f07c0286a89d0821d8651684f0fc2f07c02c2b09e8751684f0fc2f07c0242b1a82709054a1d45a13c3f0bc1f00c0c82b09c8881ec661704f0fc2f07c030320ac2a09c241510881f4661684f0fc2f07c03c2b06d0881f4661684f0fc2f07c02c241510821d86d1684f0fc2f07c02c2b1a90821d86d1684f0fc2f07c02c241510821d86d1684f0fc2f07c02c321a8271510821d86d1684f0fc2f07c0342b09cd40278881f86813c3f0bc1d00c0ad2707009a2107e1ac5413c3f0bc1d00d49c1f8660962307e19c5c13c3f0ac1d00d49c1f06609e2307e1b04f0fc2b0740312706609c1f05c13c3f0ac1d00a0a12707c1982788c1f86c13c3f0ac1d00d0a12706609c1f05c13c3f0ac1d00b4ad2707e1982588c1f8671704f0fc2b0740383241fc3b0bc1f0060c907f0ec2f07c0182b29c244220761684f0fc2f07c02c2b090d442207d1985a13c3f0bc1f00c0ae2707109c1cc5c13c3f0bc1d00b0c82b09d8801fc3f0bc1f0090ad4801d46a13c3f0bc1f0090ae27092544200751b85a13c3f0bc1f00d0c92b49d07f0ec2f07c020324ad2741fc3b0bc1f00809c1c35109a2307b1704f0fc2f0740302f0ac2742688c1ec5c13c3f0bc1d00c09c1c2544d9218791584f0fc2f06c0322707c5e0704d9238791784f0fc2706c0343204907613c3b0bc1f0080c92741d84f0ec2f07c0212b65107613c3b0bc1f00809c212605092245612c3f0bc1f00b89c231882114248e1e45e12c370bc1f00d0c60821e86d1584f0fc2f07c0283382087a1b45613c3f0bc1f00a0c60841f06b1584f0fc2f07c028330c42482107c1ac5613c3f))))
def genIndex9 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x3c78b9b143f800526a0603ff80108fe0053d7803c0144048df643c0140cf0029abc01e00f00198bc00564f39f8024a5d114d01a41e0be00f007803275e00c1af803c01e00dcff80143de00832f0cfc0104ba110e2bc01e004298073c01e00f33e937c01208f0018a20f290cd366a67c01e00ba011c9021464c01780385a484ac611c3c00c2a44c393881c11aa1cba55e5be0083f388300b2a0324d22f0d27121160427c0061b94a2217c00e2f92e992acafe002454932eb757144750a7c00c66209217ea01e00f0018e88f6c07040f80084a87561a2cd9111e00e187803605e00f3a7803c0049743e7803c00c15f007803c01e00f0012082b5289321f80381be00981c853c01e00f002c2f654842e15a0f7c00538f00188fc00c26f007087e1443b0cce1ade9ea5132e096208880ba1ff803c01e86548f803c01880b0cae6bc0033f530887646cb72389906bc0049b4c5f8020b5211f0068600b7e76b303807c01e00e46f800cdde002237801924445f1884afc00761f004d99f1ac9ca24405fc9e600f007803c01c3e34d7803849e00f006a0ccd1e0059d865f12d613620d543c01e0040b780384fe00f00682bc01e00f007802a29e00bb1f803c0049dc3bf803c01e0031c015391f609f0009b7c01e00f007802c64a2e98e607ca7dc04d80d00e119c7825098de0de450b3ed957c00e9ef007803c0005e6078a7fc00306f00198d4b3071a2b00280004d060c00d020008008004010014007280c18402403820400001040c30206141850c00680000c2010010082)
def genData10 (j : Nat) : Nat := if 7 ≤ j then 0 else (if j<3 then (if j<1 then (0x74bb04286fba55821c37dceac10e1bed9760a60df6cbb04286fb655829837db2ac10e1bed9221d50df6bab05306fb5d5821c37bf26c3ac1bde9560c70def3ab06386f7655831c37baeac18e1bbe9561070ddf3ab08386ef655841c377aeac20e1b7f85a1570dbfac2ea386df962755c36fb0a42ae1b7d589d470dbeac2eb306bfe61761db5ff30b3ec1aff9661d60d7fcb30ca86bfde167d835fef0b3ac1afe9621d50d7f432ea386bf9a1765c35fb2d43ac1afd9621d50d7ec34ea386bf619751c35fad0bb2a19ff9761d50cffc3d0ea867fde3759833fef12bca19ff785d660cffbc2ea3867fde1579433fd31baae19fe9721d50cff3c40ea867f9e1075433fb0e43aa19fd78dd660cfebc4af2867f5e1759833faf0abca19fc7881d50cfe3c20ea85fee41765c2ff720bacc17fb905d570bfdc82eab05fee4157942ff53183aa17fa909d570bfd4810ea85fea40855c2ff32db82e17f995dc270bfccaee0b85fe64376542ff321bacc17f990dd560bfcc84eb385fe642755c2ff3212bca17f99081d50bfc4c20ea85fe241755c2feb2243aa17f59121570bf6c910ea85fb648855c2fbf26c32e17df9360176beec990ab85ef650855c2eff2a83aa177e9581d50bbecac0ea85df25507542dff2ab3ac16fe9621d50b7f4b10ab85bf65b75582dfb2cbaac16fd9621d50b7ecb10ab85bf643765dabfd31baae15fd979d570afe4c2eab84ffe63765427ff31bacc13ff985d9509ffcc2eb304ffe61755827ff30ba8e13ff9841d509ffcbb0ca84ffe5d859827ff2cc3aa13ff96617709ffcab0f304ffe55875827ff2ac36e13ff95603769ffc830ea84ffa63765427fd313aae13fe9881d509ff4c2eca84ffa60875427fd2fc32a13fe97a1d509ff4b90ab84ffa56871c27fd2ac3ce13fd98dd9509fecc6eb304ff663755827fb313a8e13fd985d9509fecc2eb304ff661075427fb2fc32a13fd97614709fecb70ea84ff65b855c27fb2d43aa13fd9621d509fecaf0cb84ff657805da7fb2b43cc13fd95a1d609fec850ea84ff263765427f930bb2a13fc985d5709fe4c20ea84ff25d865427f92ec2cc13fc9561e70ebcbaa0ea86fc5c1811c37e20ec0cc1be97060870df483b05306f9649819837cb24c08edbe59260470df2c9302286f65c1831c3772e0c20e1b9d9361070dbdcc2a0286de5c1851c36f2a0c38a1af97660076d7cb830c386bd5d9811db5daecc10eda7d6761760cfccc6e13863f663769daef12a83aa15fa90dd7709fdcc2e0384fe261075427eb2243aa13f591217709fac890ab84fb648875427db2442ee13ed92215709efc9b0eb04f764c85dc27bb2642ae13bd94217709deca10ab84bfe61761da5fd2c43aa12fe962177097f4b10ab84bf658875425fb2c42ee12fd96215708fecc6ebb847f261755c32f2a0c38a137b9854050) else (if j<2 then (0xf314d30d2306930002fa92f402ee92e772e0e2dae2d2a2cc12c3d2bcb2b622b0b2a992a3029d92979291028b9286227f02799273926d92667261025a7253e24cc247e241e23be235e22fe229e225021f92199213020c7206720071fb01f501ef01e991e301deb1d941d2b1cb91c471bde1b871b391aeb1a701a1019b0196218f91887182717c71779171016b0165015f0157e152714be145513f51395132c12e71290121e11ac115511071095102c0fba0f3f0ed60e760e040dad0d3b0cc90c570c120bb20b640b1f0abf0a680a1109c3096c093008d00882082207cb075006f00687060305a3053104e30483041103b10348030302ac025e0210019e014700f000ab006600330000fffcc2eca87ff66176543ffb2ac32e1ffd9560176ffecaaecb87ff615805dbff72a83ac1ffb9061970ffdc82ecb87fee4175583ff700c02edffb7061970ffccb20ea87fe65507583ff321baac1ff970dd560ffcb82eca87fe5c175583ff20ec32a1fdf9361970fefc9b00bb7dfdd575583dff2dc02edeff9660176f7fcaaceb07bfddb805dbdfeecc02edefd96dd560f7ecb2eab07bf65567583dfaedbaac1efd765d560f7eb42eca877f65b755c3bfb0dbaae1dfd865d570efebb6eab877f5d9755c37ff30bb2a1bff95e0176dffcab0eb06ffe5586dc37ff0bc02edbff8560176dffbc2eca86ffa61765437fd2ec32a1bfe8761950dff3c2eca86ff663755837fb30bb2a1bfd985d560dfecbb0ca86ff65b855c37fb2d43aa1bfd9661d50dfecb30bb86ff657805db7fb2ac3ac1bfd9561b70dfec3b0ca86ff61b855c37fb0cc2ee1bfd8661570dfec2b00bb6ff5e3755837faf0bb2a1bfd785d560dfebb70ab86ff5d985dc37f930bb2a1bfc785d950bffcc2eca85ffe5586dc2fff2ac32e17ff9560176bffcaaedb85ffe55765c2ffb30bb2a17fd96e1570bfecb6eab85ff65a87542ffb2bc02edf7b9754050fbdcaa0ea87dea5d50143ef4eb83aa1f7a7541d50fbccbaa0287de5d507543ef12ea80a1f789541d50f7dcb20eb07bee4167583df2ec83ac1e7d565d560efdc82eab877ee01755c3bf6ea83ca1dfb7541d50efdb84eb3877ea57709c3bf4f083aa1df995dc270efcbaa0f2877e5d507543bf2e1bacc1df970dd560efcb82eb3077e5c175583bf2e0ba8e1df8905d570efc3c20ea875fdd6755c37f730b80e1bfb9841e60dfdcc20f286fee41875837f720c3aa1bfb78c1d50dfdbc20f306fede1079437f6f083ac1bfb7841d50dfcc850eb06fe642875437f32043aa1bf97061470dfc83f0ca86fe41d865437f20ec2cc1bf89841d50dfc3c60ea86fe1e1075437eeeac0cc1bf69760660dfb4bb02286fda55811c37eceac08e1bf59760660dfacbb02286fd655819837eb2ac08e1bf59121d50dfabab03306fd5d5811c37deeac14c1bee9760a60df) else (0x91a90883d1b0b84e1f0b83c0304e1b6a4220f86a2c1387c2e0f00c13c520ec58270f85c1e0122b83a1609c3e17078040ac54270a85012070270f85c1a0182b138271007c301387c2e0d00b158a84e160a0280e04e1f0a83c0305a2b1409c158803e1809c3e150780687c3209c441f0d04e1f0983402c2b1408c220f06e1f098340283e1c0c856280983c1387c260d00c0c8260f058270f84c1a0122b1509c2e140581c09c3a17078060ac54270c05018070250f85c1e018231086831140641e0943617078060ac3607e1f0b83c01c562a138500e04e1f0b83c02856270381387c2e0f0080401c0dc3e17078038ac54270a01c09c3e170780505428080381b87c2e0d0090b05010070370f8541e012080381b09c3e17078040ac54270a01f87c2e0f0090401f87c2e0f0061386d110742c1387c2e0f00a0a21e8a84e1f0b83c020562a138500e04e1f0b83c028a88883a1609c3e17078048a84e1c2a9531187c2e1387c2e0b00d0a850918722e1387c2e0b00a138709a48c391709c3e17058058a84e250e958a988c3e1709c3e13078070582848c391709c3e13078050a04e1d271230e45c270f84c1e0198883e1b09c36170780405c2848c391709c3617078050a44e20279230e45c270d85c1e018180a1230e45c230f85c1e0142710940918722e1187c2e0f00b0401c0dc3e1707803a210ec6c2e1387c2e0f00943b188b84e1f0b83c0210ec622e1387c2e0f0081509c48544421f0b84e1f0b83c03028484391709c3e170780489c908722e1387c2e0f0094391509c3e1707803a1c8a84e1f0b83c01c0fc3e170780281f87c2e0f0058850880287ab874b86eb868b862b85cb855984f98490841e83a3833182c8825681d2815780e58085802e7fc57f5c7ef37e817e187da67d3d7ccb7c597bf07b6c7afa7a7f7a04799279177893782177b8774f76e6767d76027599753074c7744c73da735f72e47269720971a0714070e97077700e6fae6f336ec16e586de66d746d026c7e6bfa6b766b046a926a2069b7694568dc6873680a67a1671d66b4664b65d0655e64ec6495643e63de637e630c62b5624c61f5618c612c60cc605a5ffa5f9a5f285ec85e565e085dba5d515d035cac5c435bd15b5f5af65a965a2d59cd595258f25892583257db5772571256bb565255f25589552054b7544e53ee537c531352aa523851cf5178510f509d502b4fd44f744f1d4eab4e544de24d824d104c9e4c3e4bc34b514afa4a9a4a4349d1497a48f64896482447a0474046e94689463245d24572451244bb445b43fb43a4435642f64284423641cd4188413a40da407140233fc33f633f033e9a3e3a3dda3d8c3d3e3cd53c6c3bfa3b9a3b4c3ada3a833a2339ba395a38fa389a381637ad375636ed3696363f35df356435043492343b33e4338d333632d63288320d31b))) else (if j<5 then (if j<4 then (0x98c456270a3200ec68270f85c1e01a1483b1609c3e17078040ac54270a3220ec58270f85c1e0182b13890a90803d1b0a84e1f0b83c0344e548421f0d454270f85c1e016272a4210f86a2a1387c2e0f00b1586d0e454270f85c1e012270dc50908722a1387c2e0f00b139510f054270f85c1e0122b1509c365403e1409c3e17078060ac36544441d0b04e1f0b83c02c54278a21e8a84e1f0b83c02856240e06caa54c461f0b84e1f0b82c0384e1c269230e45c270f85c160162b1207436562a6230f85c270f84c1e01c28138749c48c391709c3e13078060ca5727a441e8d84e1b0b83c02c658883e1a89c3617078048a44e20279230e45c270d85c1e0182710940918722e1187c2e0f00b1386e0e858270f85c1e0122b0d9520e858270f85c1e0142b1506ca90742c1387c2e0f00b1386e0e858270f85c1e0120883c198b84e1f0b83c024561b2a2210ec6c2e1387c2e0f00c13a1d8c45c270f85c1e012540421d0d45c270f85c1e0142b0421d0d45c270f85c1e0142b1206ca88843e1709c3e170780609c908722e1387c2e0f0091589c290803c1989c3e17078058903614a461e8b84e1f0b83c02c562a13850918722e1387c2e0f00c13a1c8a84e1f0b83c020a90883d1b0b84e1f0b83c028a90843e1a8a84e1f0b83c028490883d1b0b84e1f0b83c028570843e1a8a84e1f0b83c028570843e1a8b84e1f0b83c0282887a2a1387c2e0f008151520f858270f85c1e012248441e8d85c270f85c1e0142b0dc220f86a2c1387c2e0f00b1589110876361709c3e17078058a890876351709c3e170780509d1107c331609c3e17078052220f8662e1387c2e0f0098a1220f4662e1387c2e0f00a13a220f8662d1387c2e0f00a1509d0f854270f85c1e0122b124220f46c2e1387c2e0f00b4391509c3e17078038ac370742c1387c2e0f009158921107a361709c3e17078058ac481b2a6230f85c270f85c1e0182b0db521107a361709c3e17078060903654c461f0b84e1f0b83c02d2848c391709c3e17078048520ec58270f85c1e0102a83b1609c3e17078040ac5427124220f46c2e1387c2e0f00d13c210f86a2a1387c2e0f00a13c210f86a2e1387c2e0f00a0a21c8a84e1f0b83c02056248441e8d85c270f85c1e0162b1386e1087c351509c3e17078060a84e1b83a1609c3e170780506e1107a361709c3e17078050520e458270f85c1e010240da210ec6c2e1387c2e0f00b139210ec6a2e1387c2e0f00a2a2210ec6c2e1387c2e0f00a2a2210ec6c2e1387c2e0f00a1589c484883d198b84e1f0b83c0311107c331689c3e17078048aca88883e198b04e1f0b83c02c56544441f0cc5c270f85c1e0162b139510f854270f85c1e014548441e8d85c270f85c1e0142b124220f46c2e1387c2e0f00b4391509c3e170780389ca90742c1387c2e0f009158) else (0xf86a281387c2e0f00c1386ca88883a1609c3e170780586ca907c2c1387c2e0f0091509ca98883e1609c3e170780589da9094441f0cc58270f85c1a0182b13b50138883e1a09c3e170680609c130782c1387c2e0d0090ac50130762c1387c2e0d00a0a8520ec58270f85c1a0122f1589c138883e1a09c3e170680609c130782c1387c2e0d00915870128883e198b04e1f0b8340302b1404c1d8b04e1f0b834028481b2a9531187c2e1387c2e0b00c1589e128883e198b04e1f0b8340302a1484c1d8b04e1f0b83402850276a4291107c331609c3e15078068ac4ed4056220f868270f8541e018270541e0b04e1f0a83c0242d140541d8b04e1f0a83c0282c1483b1609c3e15078048b45027056220f868270f8541e018270541e0b04e1f0a83c0245a280e84c148883e198b04e1f0a83c0382d140541d8b04e1f0a83c028481b2b1531187c2e1387c260f00c168ac5027852220f8662c1387c2a0f00e0b052150762c1387c2a0f00a196220f86c270d85c1e012178a02e0ec58270e85c1e014170a41d8b04e1d0b83c0242f1405c1d8b04e1d0b83c0282e1485c1d8b04e1d0b83c02831140641d8b04a1f0b83c028301483b160943e1707804862280c83b160943e1707805060290c83b160943e170780509c918722e1387c2e0f0090a21c8a84e1f0b83c0204f142461c8b84e1f0b83c028562a1386c918722e1387c2e0f00c0a21c8a84e1f0b83c02056270da1f0c454270f85c1e016080381b87c2e0f0070401c0d84e1f0b83c02056274401d0d84e1f0b83c02856240d8200f85c270f85c1e016080381b09c3e17078040aca90803c1b09c3e170780515110876361709c3e170780505090876351509c3e17078050ac4f142401c8d84e1f0b83c02c56544401d0d84e1f0b83c02836544421f0b84e1f0b83c0282887a2a1387c2e0f0080a21e8a84e1f0b83c02056240401c8d85c270f85c1e0162b1206f1187c2e1387c2e0f00b158903654c461f0b84e1f0b83c030a90843e1a8a84e1f0b83c028a88782a1387c2e0f0081586ca90843e1a8a84e1f0b83c030361443d1509c3e17078048a8365443c1509c3e17078050903614a461e8b84e1f0b83c02c3654c461f0b84e1f0b83c028561b2a41f0b04e1f0b83c02856270dc1f0b04e1f0b83c028562a138903654c461f0b84e1f0b83c0384e1b8421f0d454270f85c1e016270da1e0a84e1f0b83c02456278421f0d454270f85c1e0162a13a1e0a84e1f0b83c024365483e1609c3e170780489c365483e1609c3e17078050cc622b13c529007a321387c2e0f00d15c210f86a2a1387c2e0f00a158a84f14a421e8a84e1f0b83c0321087c351509c3e17078048a84e8782a1387c2e0f0091506c0f850270f85c1e012278a21c8a84e1f0b83c024561b2a21f0a84e1f0b83c0284e8722a1387c2e0f0081)) else (if j<6 then (0x5c1e01a2b124220f85c270f85c1e01432139210ec6a2e1387c2e0f00b2a2210ec6c2e1387c2e0f00a1589110876370f85c1e012331545090876351709c3e17078060cc628883e198b44e1f0b83c02c642b122220ec5e1f0b83c0286631154509107a331709c3e17078068ac481b8441e8d85c270f85c1e01832139210ec6a2e1387c2e0f00b188a8284843b1a8b84e1f0b83c030642b1389090876351787c2e0f00c198c8568883e198b44e1f0b83c030643113890a90843e1a8b84e1f0b83c038562a13890a90883d1b0b84e1f0b83c03866323509ca90843e1a8b84e1f0b83c03864274a1210ec6a2e1387c2e0f00c188a8284843b1a8b84e1f0b83c030642b124220f46c2e1387c2e0f00c191521107a361709c3e17078058ac489b8441e8d85c270f85c1e018318a1220f4662e1387c2e0f00b190ac9107a331709c3e17078058c8568883e198b44e1f0b83c02c63142441e8cc5c270f85c1e01632188ac49142441e8cc5c270f85c1e01c2b124220f46c2e1387c2e0f00b1909c90876351709c3e17078058c44e240a1210ec6a2e1387c2e0f00d15890a88843b1b0b84e1f0b83c030663115a220f8662d1387c2e0f00c1589c37078270f85c1e0122b13c1d0b04e1f0b83c02456270db520f04e1f0b83c028561b2a41d0b04e1f0b83c02856270d951110742c1387c2e0f00c1589c37078270f85c1e0122b1509ca90742c1387c2e0f00b1386da9078270f85c1e0122b1386d110742c1387c2e0f00b1589d10074341387c2e0f00a198c610078321387c2e0f00a190ac4e544401d0d04e1f0b83c030560843a188b84e1f0b83c028562aa421e8a84e1f0b83c028562a138529087a2a1387c2e0f00c1386ca90742c1387c2e0f00a1589c36544441d0b04e1f0b83c0302887a2a1387c2e0f0080a41d8b04e1f0b83c02056240de220f858270f85c1e0161483b1609c3e17078040a84f0742c1387c2e0f009158a8368883a1609c3e170780589c36548421f0d454270f85c1e01827121521087c351509c3e17078060ac4f0843e1a8a84e1f0b83c02c570843e1a8a84e1f0b83c028562a138510f454270f85c1e0162b1509d0f454270f85c1e0142b138903654c441f0b04e1f0b83c03436142461c8b84e1f0b83c028562a138500e04e1f0b83c0285627c401f0c04e1f0b83c028542703e1409c3e17078048cc6431c401f0c84e1f0b83c02c562ac421f0a84e1f0b83c028545483e1609c3e17078048ac4e54c401f0c04e1f0b83c02c54272a01f0a04e1f0b83c02856272a6200f868270f85c1e0162a139531107c2c1387c2e0f00b1589ca98803e1909c3e17078058a84e54c421f0a84e1f0b83c02c36544421d0a84e1f0b83c028562a1386c2807a281387c2e0f00c1586e1007a361509c3e17078058ac490803d1b0a84e1f0b83c02c56270dc20) else (0x56244dc1c4198c856244dc1f85c120642b121220f4662f0b8248cc642b122220ec5a270b8250cc642b151220f4662e138250cc642b4441f0cc5a270b82509d1107c331609c3e17078050c84f4803d1909c3e17078050cc62278a5200f464270f85c1e0186a8421f0d454270f85c1e01433190c71007c311387c2e0f00b190ac4e94a401e8c84e1f0b83c030642b1389110076361609c3e17078068ac4e244441f0cc58270f85c1e018272a4210f86a2a1387c2e0f00b13890a90843e1a8a84e1f0b83c030642b13890a90803d1b0a84e1f0b83c038566a139521087c351509c3e17078068ac481b8401e8d854270f85c1e0183293d220f46c270d85c1e01432c441f0d44e1b0b83c024566a2a61f0c45c270f85c1e0163115a5110074351387c2e0f00b190ac4e8803a1a89c3e17078058c8622b0441e0cc5c270f85c1e0183115a5110074351387c2e0f00b190c456944401d0d44e1f0b83c03062540421d0d45c270f85c1e01633159a810874351709c3e17078060cc642b0441e0cc5c270f85c1e018312a0210e86a2e1387c2e0f00b198c8566a2a0210e86a2e1387c2e0f00e1589136080391b0b84e1f0b83c03062271205090876351709c3e17078068c84e248a1210ec6a2e1387c2e0f00d190ac4e4843b1a8b84e1f0b83c03062271205090876351709c3e17078068cc642a1385090876351709c3e17078070c856248441e8d85c270f85c1e01831122220f8662d1387c2e0f00b190ad1107c331709c3e17078058c6284883d198b84e1f0b83c02c622b4441f0cc5a270f85c1e01632188ac488883e198b44e1f0b83c03448548441e8d85c270f85c1e0162b124220f46c2e1387c2e0f00b15891a90883e1709c3e17078058ac481b6a4220f46c2e1387c2e0f00d15890a90883d1b0b84e1f0b83c0306431139521087c351709c3e17078068cc642b124220f46c2e1387c2e0f00d198acd4248421f0d45c270f8))))
def genIndex10 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (0x3c00faebc00e463c00f003c00f003c008303c00f003c00836d8dcf00144a0494610944c438133bc00f003c00c30bc00f19fc00142c44f18c6ae2baa0c44c07ea25f001137f003c64f002817f003c00f003934225a4e87b93c00f003c00f003c00f003c00f003c00f003c00f003c00f2d7c00490fc00f00083a50c7c00f003c00845b53374e40c9410fc0084f7c00f003c0093f3c00f00188db018c8241f3c00f0004ed08bf506f003c00f000450b206eed4867c00b533c000b7bc007176ef422dbc10f0032495b2e4b46a4151900a687af000c535ad7c00f00110002740abcd2fc00e9380550c8d93143df824f003c00f003c0092a3c00887d621f00111bf003c2b39d8cf1f003c0010dc89f73bfc00f001cc3e17fc00f003e48417b8e59006211122fc00e23fc0030d7c002abfc00eaefc00838fc00f0038a0e3e7c0092efe2af003c00bbcfc00e8a2320f0000aee05bc56ea5bc00050bc005a73c0082c3c320bd7c00acbb046f003c00f003c00404d433bbafc00010bc84c3a6e1552e7c00f001c3ef000cbd2a53c00f003c00f003656f417c00f000d22725fc00f00012b2347c00533f02ef000839f003c00c5218740cd72d9f001087c93fc60d290932f001b40f00383c91a0b31618f0c4d513c00747b8d4f387c005250d3803768f444fd2e33147c00301d6c13357c002b46ec708f3c00f000c52d008ca1e9430faf001d012105c997ab7503f003c00f003c00f001d46a38bc00f003c00903d941f000cbc831a8ba9223c00136bc000c640f6f003149005794bf003329f00294d81a7c00b50fc0013fae0fd08bc0084b453a60a38b3f00042a9b23e22f003425f002823abdbc00b35cccaf003c00f003485bb0fc009905476c167a40f003c00617143bfaf7c0051950c1f00000c906c0bef83b109f00086e38c2f3e841034979cfc007ab3c0011bf018e31fc00d16bc007516cf8f003c00829ceb8f0038f3c95e4b2f003c006114eb0c4a788983168806c4a0787933c00985b5114242c04e48f4df934363e916cb023bbd2ea4455c26f003c00cadd91a63fda4ac19bc00e8534a961ab4ebed2bc0041eef3de4bca2ef00380df00342fb0d8f466bb16b4891fc00faf3c00742bc0091afc00602ac149086cb141b140e6046cf57239927f003c00f001d3540fc691f0000aff003c00221bc00c1c00e061d54defb75130f003c00f003c002127c008246c7df003d1001fa2c684b8714fcbfc0033638f2f003c00f002a3bf003c005187c0001020cd241caf202090402000a050109209d01180009081d0708070600030400000401041e000301010001300600020104093f0f03000300050915050605020113020103001e0001010006010a001102000a11010301051f02011501010e0005010300091801050109120402050000020e010301010101040103) else (0xf000003012c5268491ee6845250d08a565550142f040c06f1413201dc261acae248b45b256a4273498cbf003c8a511d24d14a82e093670d6a4a0408d8fdc09a2a84f0a080d40f001400dc1e00b9b11a26b43e71c7c61121f003c001c6881a4449acd73ba218229bc00f003c004b85012f003c00bb17c00f0010adf43bc00e0b0cbf52dfc0031384e6f000ceac4dbe92c3f6083507bc0030b4ca3f00393cd52ac79f00272444714a5a1cfc0094b349c31c407ff003d20f003419c4310485890e2090f506231b56b97b0ac93547fcd3f0034ec9153c00509fc57345fc00639c834f00289eb233c00d333c005393c007a550ac213426964ef89bb89c8b8f003c00f001058526951d21cbc00f003c00228bc00f32213ef003cfb207214731dfc008420502f003c00f0))
def genData11 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (0x14130f0b070071448074684c3c2c1c02490201d1a16130f0b0700a2b2a1448874584c3c2c1c02cac6c1d14130f0b070092b1b0807864504c3c2c1c02cac6c1c14130f0b070092a14074504c3c2c1c024ac9c52201e19130f0b0700b2a27241b5488878584c3c2c1c03451221d16130f0b070092748874584c3c2c1c0241c14130f0b070070704c3c2c1c0182018130f0b07007140704c3c2c1c01c201c1b0f0b0700708070644c3c2c1c020201c1b0f0b070070988078604c3c2c1402450201c1b0f0b0500814090704c3c2c14020241c14130f0b050080a88078604c3c241c02450201c1b0f0907008140a0704c3c241c020281c14130f0907008140b0704c342c1c02050301c110f0b070080807064584c3c2c1c024501d14130f0b0700808070684c3c2c1c020501c130f0b070071448074604c3c2c1c0241d1814130f0b07008140704c3c2c1c01c1c14130f0b07007070504c3c2c1c01c1c14130f0b0700796ba55893ea4a4913a4108eca34c8bfa2a0890a1ec865a120832a06c8079fc07dc9f247b19e687829dac7519ce87249c346f99b886c89ac46999a0066a995c64198b061297fc5ef97685c696c459b9620576958c55194f852c946c50993d84e093244b5927848891c445b9128438908c40f8fe83e28f443c18ec83a28e3437d8da83588d1c3358c8830c8be42e78b502c48ad42a18a30274898424988d8222882c1ef87701c886e41ab867018c85f416b857014884dc125845010083bc0dd83300ba82a40958210072818c04f80f802e807c00f8000fff87543ffe1970fff86543ffe1570fff805dbffdd976fff765c3ffdd950fff759c3ffdd660fff755c3ffdd560fff705c3ffa1d50ffe85dc3ffa1570ffe759c3ff9d570ffe751c3ff95e50ffe07543ff61d50ffd86dc3ff61970ffd86543ff61770ffd855c3ff60376ffd805dbff5db70ffd765c3ff5d950ffd75983ff5d570ffd75583ff5d470ffd57943ff41d50ffc87543ff21570ffb709c3fedc170ffb07543fe5c070ff907983fe41e50ff907583fe41d50eff769dbbfdd976efd761dbbf59f60efd67583bf59560dff75dc37fdd570dfd755c2ffe1d50bff865c2ffe1950bff855c2ffe0176bfe87d82ffa1e60bfe87942ffa1d60bfe87542ffa1c76bfe871c2ffa1c60bfe87142ffa1770bfe859c2ffa1570bfe851c2ff61f60bfd879daff61e70bfd87982ff61e50bfd87582ff61d50bfd87182ff61c50bfd86dc2ff61950bfd85dc2ff61670bfd85982ff61650bfd851c2ff60376bfc87542ff21770bfc855c3ded4250f7950143bed8260dfb709c33fdda76bfa801dafe60076bf581982fd60476bf5811c2fd60450bed82982fb60876bed821c2fb60850bdd831c2ef61070b7e85d82dfa1470b7d85d82df61470afe861c2bfa1850afd861c2bf618509fe871427f61c50) else (0x2b241b88878584c3c2c1c02cac9d201d1a130f0b0700a2b1b0807468584c3c2c1c02cac9d221d16130f0b0700a333188078644c3c2c1c028201c1b0f0b070072b271448074684c3c2c1c02cac9150201d1a16130f0b0700c2b14874584c3c2c1c0249d50221e1916130f0b0700b2b271448874584c3c2c1c02d50221e1916130f0b0700a2b2a27140704c3c2c1c028aca89c906d52221e16130f0b0700e2b1448874584c3c2c1c028aca89d221d16130f0b0700b2b14874584c3c2c1c024ac9c51221d16130f0b0700b1448874584c3c2c1c0249d521c16130f0b070092b2a1b54078504c3c2c1c02cac906e221e16130f0b0700b33311448074684c3c2c1c02cc8ac9d201d1a130f0b0700b2b241b0807468584c3c2c1c030aca851221d16130f0b0700b2b2748874584c3c2c1c028ac9c52201e19130f0b0700b3288078644c3c2c1c024ccc451201d1a130f0b0700b322b271448074684c3c2c1c030ac90201d1a16130f0b0700b2b270887864584c3c2c1c02caca89c51221d16130f0b0700c2b0887864584c3c2c1c028a8521d16130f0b070092b2a27870584c3c2c1c028ac9c6c1e14130f0b0700a2b241b5488878584c3c2c1c0309d221d16130f0b07009140704c3c2c1c01caca89c501c130f0b0700a2b1b078504c3c2c1c024aca89c501c130f0b0700a2b2788078604c3c2c1c028ac9c1e14130f0b0700988078604c3c2c1c020ae201e14130f0b0700914080706c3c2c1c020ac50201c1b0f0b0700914080706c3c2c1c020201c1a130f0b0700808070684c3c2c1c020201c1916130f0b070092b1448874584c3c2c1c028ac9c51221d16130f0b0700b2b48874584c3c2c1c024ac906e221e16130f0b0700b2b2748074684c3c2c1c028ac6c201d1a16130f0b0700b2b2748874584c3c2c1c02a201e19130f0b0700808070684c3c2c1c020ad52201e18130f0b0700a2a54078504c3c2c1c024ad52201e1a130f0b0700a2a275488878584c3c2c1c02c50201c1b0f0b07008140704c3c2c1c01c2018130f0b07007070504c3c2c1c01cac51221d16130f0b0700a074504c3c2c1c01ca9221d16130f0b0700914074504c3c2c1c020201c1a130f0b0700814080706c3c2c1c020ac9c501c130f0b070092b2788078604c3c2c1c028ac9c1e14130f0b0700988078684c3c2c1c020ae221e16130f0b07009080604c3c2c1c01c1c))
def genIndex11 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (0x7801e00780119f481ba35725d537f801285f801e007801e000a0ea86f80025924947484160a45e21080862725a4904ec419ceeb3d92b261d89f80a3703e462b1b1c38b939026e887298f14a0967a41185e20af607800466f80010ea86c08ccdba0747953d7678358007a53a7a40dbc321c6fe00780080f1866a4711a1692ee94424fdea89fb20564118f3e007801e0020bbe00693f271f801e00116665fd8080147801499352385bf800870225724b7800a73221de00428860ca005e007801865f03786fe94fe004014aa2d0e673e6043e79f800e6628ec20e7800d107279e007801e00780022e24bc8983a27e0060d1e0078013957801e0050f663609f6f6b1a9360a00cb49b95f8a79695a41f0a99e487801e0060bde000134d46f801b2001a7e578149e002e84660b80fe007801e0071bb13fd075e003951d4532a883f0a6a07af801e63f801e0056afe007800889005d408c882e7502b0c12381fe9c1909c431977e005063e003249da07800809da15e947801a4ae0ced4791c5e0022000467801f9ef800228252fe0028c6b407db0e6778012a0780009150e1e0020f9e007801e0011fe2377801a2985dde0065bd96d9e71f72a02f1467801e00485f06b7801e0071ee478f801e001a1964c9e08a70e90be007801e007801035f80046108468ad497de4a4097e0078002727801eaa9947e0021e107d78024627801e00196a341100be002285e007801c4541fc06ca88aa263e61e003971e007126a4dc0eaa2b7801e000a3b015d10341aa8f1e00780172e922de002007e00420de007801f36b0d3a23ba87376f801d87c17a216a87e8a9f801687f801a9b2294938da9c06e7801e006055e00780067ec943e0034cd6197800b54f801e00780004be9b68a8c08d8405c2b07629d223f8a3fea0f80058c425aaa7a0b0093dd1097bfcfc5a5ec67837f800e573223e001024a5e7801e007801230f80030f7801e001236097bde4d29b2b7e0075f4c67f80128d2497e00780145cd4d3e000830027a430e1c090f21e7801e007140f4b780045890cde007801e002e8da2df801e002890844ca13e005cf4005f80109d7053b724a90c99a9ae8111e83e0038f5e007801e0022a5e0029a3e007800a77912522fb0e8421415762048c4b75201c22278005237800e0ef801e007800728f801d6d09a9291fc25451780030b7801e000923e006203e007801c6d7800940f059e007801a6378018551a97f77b8afe00624d21ce175e00309d0a8061d4567800e12e8aae77780193ede7fe007801e003cd5e000400084000a24384d41c2000210001162401a102938e1e84282062c7842404083060400124085a40000304280058a1a1148202400000258f82080018102080040000009004818800084001a1c1880200000020840004282010200004000c0000c0c701) else (0x1e0064a1e00218684f14c6d79ddf7e5a316de0075d642cf800872e48ac8f51bde0061306647801e82702be007801e007801e007801e007801e005d37e007801e007801e0030b468a7801e007800f458e51e739675e00780167b78a26880193047c22b943f80079bf8019a690a84306a77e007012225380d87cee87f3cba9a89f282c695328f01849aa61b92387665a30290f800c3ba9da16bda7be007801c130869e00780118d78010047801e007801e007801e007801e0002afe0011f0e537801e007801460693b081f800a107800646f80119e6df109a20fbe007801e441dc1e0078002397801e75a8a40ab7801e007800c1ef8016657801e06222fe0078011a979a5e))
def genData12 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x504070d0e141804140e121c283007101c304870a0c0204070d0e14180387090e141803080e1824385060101c284870a0c01c4070d0e14180387090e141803080e18243850601020385090e141804080e1a1c283007281c243850600e20304870a0c01c385090e141803e216cd3732468fb37ec42b08d1b8528dc1b801ffddbffb87ff60ffcedff9c3ff307fe50ffaedff5c3feb07fd50ff8edff1c3fe307fc50)
def genIndex12 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x876f68e56f00e54f00f00f00f00f005c5f00060f00312f00f0071d42f49e352b51ce6514f0058e762f000418dc55721522534af00f002108ee524f00f00f00dddf00f00f0eb1c30ff00f00272653f8cb0473321ef054efad9523b69d70f00c40b19f00edb303f00290b73b4c8a9727f00f00f00f37f00f0085cc47f00f00f00461f00f00d67439702f4f11f2e5f00f6b508f00359f00b79f00f00f00f00d31a49600f00d2d3357f5f00a22f00f00d0c9d5a07094f00b6fe6cf00130b17b950dee43a668d4f005d7432a4e1b0f00f00028f002bcf0033ef003f1b3ac5a265f009cab2bf0010970af00238f0002c158206f00f00b114c67014c2055e5e13d93f44614b775b6d4d6f64f0033455b277771720b92f00e1af00f00c48c1bf00f0055d921f001b8ef0f00f00f005f305085ff00f00c13c0dc45f0023c53b12ef00f00f00029d44f00de8f00f007cf974f00f00f4df0000b178a16b42e1806e0e786a42a726336e63c801b93412040451c100118014a1410031400802c50c400e014100000080)
def genData13 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3081004ff
def genIndex13 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x7a1c0a49de0e3289fa39f07800200f0780eb96f5783c1e0f02c8e34833f80c6c4b28f1562cf0783c14d210d06)
def generatedLevels : Nat → Packing
  | 7 => (15,6,6,0,0,9,0,genData7)
  | 8 => (162,5,6,0,0,14,0,genData8)
  | 9 => (334,4,6,0,0,16,0,genData9)
  | 10 => (348,3,6,0,0,16,0,genData10)
  | 11 => (122,2,6,0,0,14,0,genData11)
  | 12 => (15,1,6,0,0,10,0,genData12)
  | 13 => (1,0,6,0,0,0,0,genData13)
  | _ => emptyPacking
def generatedIndex : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 6 38 2 9 4 1 genIndex8
  | 9 => lookupWord 53 319 7 13 8 1 genIndex9
  | 10 => lookupWord 115 688 8 14 9 1 genIndex10
  | 11 => lookupWord 113 677 7 14 9 1 genIndex11
  | 12 => lookupWord 40 238 6 12 7 1 genIndex12
  | 13 => lookupWord 6 37 4 9 4 1 genIndex13
  | _ => fun _ => none
def qF_ : Forest := ⟨511,13,fun i => generatedSamples[i]?.getD (0,0),generatedColumns,[[], [80,65,50]],generatedLevels,generatedIndex⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_0 : block qF_ 7 0 7 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 0)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_7 : block qF_ 7 7 8 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 1)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB7 : block qF_ 7 0 15 = true := (@block_merge qF_ 7 0 7 8 genP7_0 genP7_7)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_0 : block qF_ 8 0 19 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 2)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_19 : block qF_ 8 19 60 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 3)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_79 : block qF_ 8 79 83 = true := by
  apply cellsBlock (ar := 9) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB8 : block qF_ 8 0 162 = true := (@block_merge qF_ 8 0 19 143 genP8_0 (@block_merge qF_ 8 19 60 83 genP8_19 genP8_79))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_0 : block qF_ 9 0 1 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 0)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_1 : block qF_ 9 1 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_97 : block qF_ 9 97 43 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 3)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_140 : block qF_ 9 140 96 = true := by
  apply cellsBlock (ar := 9) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_236 : block qF_ 9 236 49 = true := by
  apply cellsBlock (ar := 9) (rows := 0) (d := 3)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_285 : block qF_ 9 285 49 = true := by
  apply cellsBlock (ar := 10) (rows := 0) (d := 3)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB9 : block qF_ 9 0 334 = true := (@block_merge qF_ 9 0 140 194 (@block_merge qF_ 9 0 1 139 genP9_0 (@block_merge qF_ 9 1 96 43 genP9_1 genP9_97)) (@block_merge qF_ 9 140 96 98 genP9_140 (@block_merge qF_ 9 236 49 49 genP9_236 genP9_285)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP10_0 : block qF_ 10 0 2 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 0)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP10_2 : block qF_ 10 2 46 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 3)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP10_48 : block qF_ 10 48 96 = true := by
  apply cellsBlock (ar := 9) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP10_144 : block qF_ 10 144 96 = true := by
  apply cellsBlock (ar := 9) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP10_240 : block qF_ 10 240 25 = true := by
  apply cellsBlock (ar := 9) (rows := 0) (d := 2)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP10_265 : block qF_ 10 265 77 = true := by
  apply cellsBlock (ar := 10) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP10_342 : block qF_ 10 342 6 = true := by
  apply cellsBlock (ar := 11) (rows := 0) (d := 0)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB10 : block qF_ 10 0 348 = true := (@block_merge qF_ 10 0 144 204 (@block_merge qF_ 10 0 2 142 genP10_0 (@block_merge qF_ 10 2 46 96 genP10_2 genP10_48)) (@block_merge qF_ 10 144 121 83 (@block_merge qF_ 10 144 96 25 genP10_144 genP10_240) (@block_merge qF_ 10 265 77 6 genP10_265 genP10_342)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP11_0 : block qF_ 11 0 27 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 2)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP11_27 : block qF_ 11 27 55 = true := by
  apply cellsBlock (ar := 9) (rows := 0) (d := 3)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP11_82 : block qF_ 11 82 40 = true := by
  apply cellsBlock (ar := 10) (rows := 0) (d := 3)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB11 : block qF_ 11 0 122 = true := (@block_merge qF_ 11 0 27 95 genP11_0 (@block_merge qF_ 11 27 55 40 genP11_27 genP11_82))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP12_0 : block qF_ 12 0 15 = true := by
  apply cellsBlock (ar := 9) (rows := 0) (d := 1)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB12 : block qF_ 12 0 15 = true := genP12_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP13_0 : block qF_ 13 0 1 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 0)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB13 : block qF_ 13 0 1 = true := genP13_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genTables : checkedTables qF_ 13 := by
  intro k hk
  interval_cases k
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact genB7
  · exact genB8
  · exact genB9
  · exact genB10
  · exact genB11
  · exact genB12
  · exact genB13
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genGeometry : graphValid qF_ (boundsBefore generatedKnown) = true := by
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowGenerated : Lower true (varsX 511) (qG_ 511) 14 :=
  lower_forest (g := qF_) (i := 0) (hints := 16778563)
    (before_sound generatedKnown generatedPrior) genGeometry genTables
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
end PEqualNP.Outside.L_meta_51582.ForestCore
namespace PEqualNP.Outside.L_meta_51582
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds ForestCore
def graph (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0,3,0,4,1,4,0,5,1,5,2,5,1,6,2,6,3,6,4,6,0,7,1,7,2,7,3,7,4,7,5,7,6,7] : List ℕ).length / 2,(List.ofFn x).getD (([0,3,0,4,1,4,0,5,1,5,2,5,1,6,2,6,3,6,4,6,0,7,1,7,2,7,3,7,4,7,5,7,6,7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0,3,0,4,1,4,0,5,1,5,2,5,1,6,2,6,3,6,4,6,0,7,1,7,2,7,3,7,4,7,5,7,6,7] : List ℕ).getD (2 * i + 1) 0) false = true)
def coding : Fin 8 → Nat := ![0,1,2,3,4,5,6,7]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def roots : List Sig := List.ofFn (fun i : Fin 8 => inputs.getD (coding i) zero)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def codedGraph : Sig := 0xfffffffffffffffffffffffffffffffefffffffefffffffcfefefefeeeeeaa00fffffffffffffffffffffffffffffffefffffffefffffffcfefefefeeeeeaa00
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wholeBound : Lower true roots codedGraph 14 := by
  have h := lift_ok (u := true) (ms := fixRows 0 0) (raw := roots) (T := codedGraph)
    (xs := []) (by decide +kernel) (qP_ _ (by decide +kernel))
    (qP_ _ (by decide +kernel)) lowGenerated
  have count : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
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
    14 ≤ C.gates.countP (fun g => !signedNot g) := by
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
def upperGates : List Gate := [⟨.or, [4,3]⟩, ⟨.or, [6,5]⟩, ⟨.or, [7,5]⟩, ⟨.or, [2,1]⟩, ⟨.or, [11,0]⟩, ⟨.or, [11,7]⟩, ⟨.or, [7,6]⟩, ⟨.or, [14,0]⟩, ⟨.and, [8,15]⟩, ⟨.and, [12,10]⟩, ⟨.and, [1,4]⟩, ⟨.and, [9,13]⟩, ⟨.or, [16,17]⟩, ⟨.or, [20,18]⟩, ⟨.or, [21,19]⟩]
theorem upper_shape : ∀ g ∈ upperGates,(g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [upperGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem upper_sem : ∀ x : Fin 8 → Bool,
    Circuit.eval ⟨upperGates,22⟩ (List.ofFn x) = graph x := by
  decide +kernel
end PEqualNP.Outside.L_meta_51582
open PEqualNP.Outside.L_meta_51582 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_51582 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gs o legal _ computes
  by_cases neg : ∃ g ∈ gs, g.op = .not
  · obtain ⟨g, hg, eq⟩ := neg
    have fan : FanInTwo ⟨gs, o⟩ := fun t ht => ⟨(legal t ht).1,(legal t ht).2⟩
    have low := binaryLower ⟨gs, o⟩ fan computes
    change 14 ≤ gs.countP (fun g => !signedNot g) at low
    have lt : gs.countP (fun g => !signedNot g) < gs.length := by
      rw [List.countP_eq_length_filter]
      apply List.length_filter_lt_length_iff_exists.mpr
      exact ⟨g, hg, by simp [eq, signedNot]⟩
    refine ⟨upperGates,22, upper_shape, ?_, upper_sem⟩
    change 15 ≤ gs.length
    omega
  · refine ⟨gs, o, ?_, le_rfl, computes⟩
    intro g hg
    obtain ⟨op, cap⟩ := legal g hg
    exact ⟨op.imp_right (fun h => h.resolve_right (fun eq => neg ⟨g, hg, eq⟩)), cap⟩
