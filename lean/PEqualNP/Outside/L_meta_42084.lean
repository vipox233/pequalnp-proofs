import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_42084_aux.Upper

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open scoped BigOperators

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276808392 * 2 ^ 32 + 4203260040)
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def witness : Circuit :=
  ⟨[⟨.or, [1, 0]⟩,
    ⟨.or, [3, 0]⟩,
    ⟨.and, [4, 7]⟩,
    ⟨.and, [5, 6]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.and, [8, 9]⟩,
    ⟨.or, [10, 2]⟩,
    ⟨.and, [10, 2]⟩,
    ⟨.or, [0, 13]⟩,
    ⟨.and, [12, 3]⟩,
    ⟨.or, [15, 1]⟩,
    ⟨.and, [16, 14]⟩,
    ⟨.or, [11, 17]⟩], 18⟩

theorem witness_size : witness.size = 13 := rfl

theorem witness_monotone : Monotone2 witness := by
  simp [Monotone2, witness]

def assignment (i : Fin 64) (j : Fin 6) : Bool :=
  (BitVec.ofFin i : BitVec 6).getLsbD j.val

theorem assignment_surjective (x : Fin 6 → Bool) :
    ∃ i, assignment i = x := by
  let word : BitVec 6 := (BitVec.ofBoolListLE (List.ofFn x)).cast List.length_ofFn
  refine ⟨word.toFin, ?_⟩
  funext j
  change word.getLsbD j.val = x j
  simp only [word, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [j.isLt]

set_option maxHeartbeats 8000000 in
private theorem check :
    ∀ i : Fin 64, witness.eval (List.ofFn (assignment i)) = target (assignment i) :=
  by decide +kernel

theorem witness_correct (x : Fin 6 → Bool) :
    witness.eval (List.ofFn x) = target x := by
  obtain ⟨i, rfl⟩ := assignment_surjective x
  exact check i

theorem bounded_replacement {s : ℕ} (floor : 13 ≤ s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧
      ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x :=
  ⟨witness, witness_monotone, witness_size.symm ▸ floor, witness_correct⟩

end PEqualNP.Outside.L_meta_42084_aux.Upper

namespace PEqualNP.Outside.L_meta_42084_aux.Frontier
open PEqualNP.CircuitLowerBounds

abbrev Sig := BitVec 64
abbrev Row := Fin 64
abbrev Bits := BitVec 128

def zero : Sig := 0
def one : Sig := BitVec.allOnes 64
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d = 0 then a &&& b else if d = 1 then a ||| b else if d = 2 then a &&& ~~~b else ~~~a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def allowed (d : Nat) : Prop := d < 4
def flipOp (d : Nat) : Nat := if d = 2 then 3 else if d = 3 then 2 else d

private theorem allowed_four {d} (h : allowed d) : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by
  unfold allowed at h; omega

private theorem bin_flip {d} (h : allowed d) (a b : Sig) : bin d a b = bin (flipOp d) b a := by
  rcases allowed_four h with rfl | rfl | rfl | rfl <;>
    simp [bin, flipOp, BitVec.and_comm, BitVec.or_comm]

private theorem flip_flip {d} (h : allowed d) : allowed (flipOp d) ∧ flipOp (flipOp d) = d := by
  rcases allowed_four h with rfl | rfl | rfl | rfl <;> simp [flipOp, allowed]

def Live (target : Sig) : Nat → Finset Sig → Prop
  | 0, S => S = {target} ∧ proper target
  | k + 1, S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), allowed d ∧ S = insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live target k (insert (bin d a b) U)

private theorem Live.stop {target : Sig} (hp : proper target) : Live target 0 {target} := ⟨rfl, hp⟩

private theorem Live.binary {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat}
    (hd : allowed d) (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k (insert (bin d a b) U)) :
    Live target (k + 1) (insert a (insert b U)) :=
  ⟨U, a, b, d, hd, rfl, ha, hb, hab, hfresh, tail⟩

private theorem Live.ind {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Live target k S → Prop}
    (stop : ∀ (hp : proper target), motive 0 {target} (Live.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed d)
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k + 1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset Sig} (h : Live target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl, hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U, a, b, d, hd, rfl, ha, hb, hab, hf, tail⟩ := h
    exact binary hd ha hb hab hf tail (ih tail)

private lemma live_proper {target k S} (h : Live target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary _ ha hb _ _ _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha, hb, fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {target k S} (h : Live target k S) : S.card ≤ k + 1 := by
  induction h using Live.ind with
  | stop _ => simp
  | @binary k U a b d _ _ _ _ hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

def bit (i : Row) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i : Row) : bit i zero = false := by simp [bit, zero]
private lemma bit_one (i : Row) : bit i one = true := by
  unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i : Row) (a : Sig) : bit i (neg a) = !(bit i a) := by
  simp [bit, neg, i.isLt]
private lemma bit_bin (i : Row) (d : Nat) (a b : Sig) : bit i (bin d a b) =
    (if d = 0 then bit i a && bit i b else if d = 1 then bit i a || bit i b else
      if d = 2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
private theorem bit_ext {a b : Sig} (h : ∀ i : Row, bit i a = bit i b) : a = b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j, hj⟩

def nrm (a : Sig) : Sig := if bit 0 a then neg a else a
private theorem nrm_bit (a : Sig) : bit 0 (nrm a) = false := by
  cases h : bit 0 a <;> simp [nrm, h, bit_neg]
private theorem nrm_id {a : Sig} (h : bit 0 a = false) : nrm a = a := by simp [nrm, h]
private theorem neg_neg' (a : Sig) : neg (neg a) = a := by simp [neg]
private theorem nrm_neg (a : Sig) : nrm (neg a) = nrm a := by
  cases h : bit 0 a <;> simp [nrm, h, bit_neg, neg_neg']
private theorem proper_neg {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨?_, ?_⟩
  · rintro rfl; exact h.2 (by simp [neg, zero, one])
  · rintro rfl; exact h.1 (by simp [neg, zero, one])
private theorem proper_nrm {a : Sig} (h : proper (nrm a)) : proper a := by
  unfold nrm at h; split at h
  · exact proper_neg h
  · exact h

def prime (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
private theorem bit_prime (i : Row) (d : Bool) (a b : Sig) :
    bit i (prime d a b) = (if d then bit i a || bit i b else bit i a && bit i b) := by
  cases d <;> simp [prime, bit]

private theorem nrm_prime (d : Bool) (a b : Sig) :
    ∃ e, allowed e ∧ nrm (prime d a b) = bin e (nrm a) (nrm b) := by
  refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
    else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)), ?_, ?_⟩
  · unfold allowed; split_ifs <;> omega
  · apply bit_ext; intro i
    cases d <;> cases ha : bit 0 a <;> cases hb : bit 0 b <;>
      simp only [nrm, bit_prime, ha, hb, bit_bin, bit_neg, Bool.true_and, Bool.false_and,
        Bool.and_true, Bool.and_false, Bool.false_or, Bool.or_false, Bool.true_or, Bool.or_true,
        Bool.false_eq_true, ite_true, ite_false] <;>
      cases hx : bit i a <;> cases hy : bit i b <;> simp [hx, hy, bit_neg, bit_prime]

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
def Repr (w : List Sig) (v : Sig) : Prop := represented w (nrm v)

private lemma bin_laws (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧
    bin 1 zero a = a ∧ bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    apply bit_ext <;> intro i <;> simp [bit_bin, bit_zero, bit_one]

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg, zero, one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz, ho⟩), hz, ho⟩)

def witness (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, allowed d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

private lemma bin_rep {w a b} (d : Nat) (hd : allowed d) (ha : represented w a) (hb : represented w b)
    (no : a ≠ one ∧ b ≠ one) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩ := bin_laws a
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16⟩ := bin_laws b
  by_cases he : a = b
  · subst b; left
    rcases allowed_four hd with rfl | rfl | rfl | rfl
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases operand_cases ha with rfl | rfl | ⟨ham, hap⟩
  · left
    rcases allowed_four hd with rfl | rfl | rfl | rfl
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · exact absurd rfl no.1
  rcases operand_cases hb with rfl | rfl | ⟨hbm, hbp⟩
  · left
    rcases allowed_four hd with rfl | rfl | rfl | rfl
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · exact absurd rfl no.2
  exact Or.inr ⟨d, a, b, hd, ham, hbm, hap, hbp, he, rfl⟩

private theorem norm_ne_one (a : Sig) : nrm a ≠ one := by
  intro h; have := nrm_bit a; rw [h, bit_one] at this; exact Bool.noConfusion this

private theorem prime_rep {w a b} (d : Bool) (ha : Repr w a) (hb : Repr w b) :
    Repr w (prime d a b) ∨ witness w (nrm (prime d a b)) := by
  obtain ⟨e, he, eq⟩ := nrm_prime d a b
  unfold Repr; rw [eq]
  exact bin_rep e he ha hb ⟨norm_ne_one a, norm_ne_one b⟩

private theorem repr_const {w} {v : Sig} (h : v = zero ∨ v = one) : Repr w v := by
  refine Or.inr fun hp => ?_
  have := proper_nrm hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl

private lemma get_rep (w : List Sig) (i : Nat) : Repr (w.map nrm) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact repr_const (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))

private theorem repr_neg {w a} (h : Repr w a) : Repr w (neg a) := by
  unfold Repr; rwa [nrm_neg]

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false

private lemma gate_rep (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    Repr (w.map nrm) (gv w g) ∨ (isNot g = false ∧ witness (w.map nrm) (nrm (gv w g))) := by
  obtain ⟨o, l⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  obtain ⟨ho, hl⟩ := h
  have prim (d : Bool) :
      Repr (w.map nrm) ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one)) ∨
      witness (w.map nrm) (nrm ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one))) := by
    have unit (v : Sig) : prime d v (if d then zero else one) = v := by
      apply bit_ext; intro i; cases d <;> simp [bit_prime, bit_zero, bit_one]
    cases l with
    | nil => exact Or.inl (repr_const (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, unit]
        exact Or.inl (get_rep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, unit]
          exact prime_rep d (get_rep w i) (get_rep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl, h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl, h⟩)
  · left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv, neg_laws]))
    | cons i l => exact repr_neg (get_rep w i)

private lemma pull_gate {target} {w : List Sig} {z : Sig} {k S c} (h : Live target k S)
    (hz : represented w z ∨ (c = 1 ∧ witness w z)) (sub : ∀ a ∈ S, a ∈ w ++ [z]) :
    ∃ k' S', k' ≤ k + c ∧ Live target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k, S, by omega, h, ?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨rfl, d, a, b, hd, ha, hb, pa, pb, hab, eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live target k (insert (bin d a b) U) := by
          simpa [U, Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_, _, Nat.le_refl _, Live.binary hd pa pb hab hf ht,
          by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k, S, by omega, h, ?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract {target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hp : proper target) (hout : target ∈ (execute gs w).map nrm) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ Live target k S ∧ ∀ a ∈ S, a ∈ w.map nrm := by
  induction gs generalizing w with
  | nil => exact ⟨0, {target}, by simp, Live.stop hp, by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k, S, hk, ht, hs⟩ := ih (w ++ [gv w g]) (fun a ha => legal a (by simp [ha])) hout
    have rep := gate_rep w g (legal g (by simp))
    rw [List.map_append] at hs
    have rep' : represented (w.map nrm) (nrm (gv w g)) ∨
        ((if isNot g then 0 else 1) = 1 ∧ witness (w.map nrm) (nrm (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1], h.2⟩)
    obtain ⟨l, T, hl, hu, hT⟩ := pull_gate ht rep' hs
    refine ⟨l, T, ?_, hu, hT⟩
    rw [List.countP_cons]
    cases hn : isNot g <;> simp [hn] at hl ⊢ <;> omega

private lemma b_read (i : Row) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some _ => rfl

private lemma run_bit (i : Row) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o, l⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
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
      rw [bit_neg, bit_zero]
    | cons a l => exact bit_neg _ _

private lemma execute_bits (gs : List Gate) (i : Row) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l ++ [g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w ++ [gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons, List.map_append, List.map_singleton, run_bit i g w (hg g (by simp))]

abbrev Wire (R : Type) := R → Bool
def inv {R} (a : Wire R) : Wire R := fun r => !(a r)
def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb {R} (d : Nat) (a b : Wire R) : Wire R :=
  if d = 0 then combine false a b else if d = 1 then combine true a b else
    if d = 2 then combine false a (inv b) else combine false (inv a) b
def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b
noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0
noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum
def Available {R} (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ inv v ∈ pool
def supply {R} (pool xs : List (Wire R)) : Prop := ∀ a ∈ xs, Available pool a

def Reach {R} (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0, b => b = roots
  | p + 1, c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R),
      Reach roots p bank ∧ Available bank a ∧ Available bank b ∧ c = combine op a b :: bank

private theorem Reach.start {R} {roots : List (Wire R)} : Reach roots 0 roots := rfl
private theorem Reach.two {R} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) : Reach roots (p + 1) (combine op a b :: bank) :=
  ⟨op, bank, a, b, h, ha, hb, rfl⟩
private theorem Reach.ind {R} {roots : List (Wire R)} {motive : ∀ p bank, Reach roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (two : ∀ {p bank a b} (op : Bool) (h : Reach roots p bank) (ha : Available bank a)
      (hb : Available bank b), motive p bank h →
      motive (p + 1) (combine op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero => obtain rfl := h; exact start
  | succ p ih => obtain ⟨op, bank, a, b, h, ha, hb, rfl⟩ := h; exact two op h ha hb (ih h)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x :: xs else xs

def Run {R} (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0, zs => List.Perm [goal] zs
  | s + 1, zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire R) (rest : List (Wire R)),
      allowed op ∧ (a :: b :: rest).Perm zs ∧
      Run goal s (comb op a b :: kept ka a (kept kb b rest))

private theorem Run.stop {R} {goal : Wire R} : Run goal 0 [goal] := List.Perm.refl _
private theorem Run.perm {R} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run goal s xs) : Run goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s => obtain ⟨op, ka, kb, a, b, rest, hd, q, h⟩ := h; exact ⟨op, ka, kb, a, b, rest, hd, q.trans p, h⟩
private theorem Run.two {R} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)}
    (op : Nat) (hd : allowed op) (ka kb : Bool)
    (h : Run goal s (comb op a b :: kept ka a (kept kb b rest))) : Run goal (s + 1) (a :: b :: rest) :=
  ⟨op, ka, kb, a, b, rest, hd, List.Perm.refl _, h⟩
private theorem Run.ind {R} {goal : Wire R} {motive : ∀ s ws, Run goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : allowed op) (ka kb : Bool)
      (h : Run goal s (comb op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s + 1) (a :: b :: rest) (Run.two op hd ka kb h))
    {s ws} (h : Run goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih => obtain ⟨op, ka, kb, a, b, rest, hd, p, h⟩ := h; exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))

private theorem mass_cons {R} (a : Wire R) (xs) : mass (a :: xs) = cost a + mass xs := by simp [mass]
private theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept, mass_cons]
private theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v, rfl⟩ := h; exact ⟨!v, rfl⟩
private theorem inv_inv' {R} (a : Wire R) : inv (inv a) = a := by funext r; simp [inv]
private theorem cost_inv {R} (a : Wire R) : cost (inv a) = cost a := by
  have : Constant (inv a) ↔ Constant a := ⟨fun h => inv_inv' a ▸ inv_constant h, inv_constant⟩
  by_cases h : Constant a
  · simp only [cost, if_pos h, if_pos (this.mpr h)]
  · simp only [cost, if_neg h, if_neg (fun x => h (this.mp x))]
private theorem avail_inv {R} {bank : List (Wire R)} {a} (h : Available bank a) : Available bank (inv a) := by
  rcases h with h | h | h
  · exact Or.inr (Or.inr ((inv_inv' a).symm ▸ h))
  · exact Or.inr (Or.inl (inv_constant h))
  · exact Or.inl h
private theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v, rfl⟩ := h; obtain ⟨w, rfl⟩ := g; cases op <;> exact ⟨_, rfl⟩
private theorem from_constant {R} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available bank a) (hb : Available bank b) :
    Available bank (combine op a b) := by
  rcases h with ⟨v, rfl⟩ | ⟨v, rfl⟩
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
private theorem available_cons {R} {bank v} (w : Wire R) (h : Available bank v) :
    Available (w :: bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (List.mem_cons_of_mem _))

private theorem extend_two {R} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ q next, Reach roots q next ∧ Available next (combine op a b) ∧
      (∀ v, Available bank v → Available next v) ∧
      q + cost a + cost b ≤ p + 1 + cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p, bank, hp, from_constant op c ha hb, fun _ h => h, ?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost, ca, cb, both_constant op ca cb]
    · simp [cost, ca, cb]
    · simp [cost, ca, cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p + 1, _, Reach.two op hp ha hb, Or.inl (by simp), fun _ h => available_cons _ h,
      by simp [cost, ca, cb]⟩

private theorem comb_prime {R} {bank : List (Wire R)} {d a b} (hd : allowed d)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ op x y, comb d a b = combine op x y ∧ Available bank x ∧ Available bank y ∧
      cost x = cost a ∧ cost y = cost b := by
  rcases allowed_four hd with rfl | rfl | rfl | rfl
  · exact ⟨false, a, b, rfl, ha, hb, rfl, rfl⟩
  · exact ⟨true, a, b, rfl, ha, hb, rfl, rfl⟩
  · exact ⟨false, a, inv b, rfl, ha, avail_inv hb, rfl, cost_inv b⟩
  · exact ⟨false, inv a, b, rfl, avail_inv ha, hb, cost_inv a, rfl⟩

private theorem extend_comb {R} (roots : List (Wire R)) {p bank a b} (d) (hd : allowed d)
    (hp : Reach roots p bank) (ha : Available bank a) (hb : Available bank b) :
    ∃ q next, Reach roots q next ∧ Available next (comb d a b) ∧
      (∀ v, Available bank v → Available next v) ∧
      q + cost a + cost b ≤ p + 1 + cost (comb d a b) := by
  obtain ⟨op, x, y, e, hx, hy, cx, cy⟩ := comb_prime hd ha hb
  rw [e, ← cx, ← cy]
  exact extend_two roots op hp hx hy

private theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x = a ∨ x ∈ xs := by cases k <;> simp_all [kept]

private theorem contraction {R} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach roots p bank) (hs : supply bank ws) :
    ∃ q next, Reach roots q next ∧ Available next goal ∧ q + mass ws ≤ p + s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop => exact ⟨p, bank, hp, hs _ (by simp), by simp [mass, cost, nc]⟩
  | perm eq _ ih =>
    have hsub : supply bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q, W, hW, hv, hl⟩ := ih hp hsub
    exact ⟨q, W, hW, hv, by simpa only [mass, ← (eq.map cost).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r, T, hT, hz, inc, le⟩ := extend_comb roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : supply T (comb op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v; apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q, W, hW, hv, hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q, W, hW, hv, ?_⟩
    rw [mass_cons, mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S := fun r => a (rows r)
private theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by cases k <;> simp [kept]
private theorem restrict_comb {R S : Type} (rows : S → R) (d) (a b : Wire R) :
    restrictRows rows (comb d a b) = comb d (restrictRows rows a) (restrictRows rows b) := by
  unfold comb; split_ifs <;> rfl
private theorem restrict_run {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws) :
    Run (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons, restrict_kept, restrict_comb] at ih ⊢
    exact Run.two op hd ka kb ih

private theorem projected_bound {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach roots p bank) (hs : supply bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach roots q bs → Available bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p + s := by
  obtain ⟨q, bs, hq, ht, hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega

def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn
private theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit, table, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [r.isLt]
private theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj; exact bit_table (observe v) ⟨j, hj⟩
private theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r; exact bit_table f r
private theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r; exact bit_neg _ _
private theorem obs_bin (d : Nat) (a b : Sig) :
    observe (bin d a b) = comb d (observe a) (observe b) := by
  funext r; simp only [observe, bit_bin, comb]; split_ifs <;> rfl

private theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl
private theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept, hn, ha]
private theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

private theorem list_run {T : Sig} {k S} (h : Live T k S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run (observe T) k (v.map observe) := by
  classical
  induction h using Live.ind generalizing v with
  | stop _ =>
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
    have am : a ∉ mid := by cases h : kb <;> simp [mid, kept, h, hab, ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin, kept_fin, er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j = a <;>
        by_cases bj : j = b <;> simp_all [ka, kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b :: tail) (List.nodup_cons.mpr ⟨hf, nd⟩) (by simp [ht])
    change Run _ _ ((bin d a b :: kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons, map_kept, map_kept, obs_bin] at progress
    have perm : (a :: b :: rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab, ar, br, hr]) hv
      ext j
      by_cases ja : j = a <;> by_cases jb : j = b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)

private theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [← table_observe (neg (table f)), obs_neg, observe_table]
private theorem table_prime (d : Bool) (f g : Wire Row) :
    table (combine d f g) = prime d (table f) (table g) := by
  apply bit_ext; intro r; rw [bit_table, bit_prime, bit_table, bit_table]; cases d <;> rfl

private theorem available_rep {bank : List (Wire Row)} {a} (h : Available bank a) :
    Repr ((bank.map table).map nrm) (table a) := by
  rcases h with hm | ⟨b, rfl⟩ | hm
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (bit_table _ i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (bit_table _ i).trans (bit_one i).symm)
  · have := table_inv a
    refine Or.inl ?_
    rw [← nrm_neg, ← this]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)

private theorem reach_live_sub {roots : List (Wire Row)} {p bank}
    (h : Reach roots p bank) {T k S} (run : Live T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map table).map nrm) :
    ∃ l V, l ≤ p + k ∧ Live T l V ∧ ∀ a ∈ V, a ∈ (roots.map table).map nrm := by
  induction h using Reach.ind generalizing k S with
  | start => exact ⟨k, S, by omega, run, sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons, List.map_cons, table_prime] at sub
    have rep := prime_rep d (available_rep ha) (available_rep hb)
    obtain ⟨k', S', hk, run', sub'⟩ := pull_gate (c := 1) run (rep.imp id (fun h => ⟨rfl, h⟩))
      (fun a hm => by simpa [or_comm] using sub a hm)
    obtain ⟨l, V, hl, hr, hs⟩ := ih run' sub'
    exact ⟨l, V, by omega, hr, hs⟩

def plainWord (a : Sig) : Bool := !(bit 0 a)
private theorem nrm_map {w : List Sig} (h : w.all plainWord = true) : w.map nrm = w := by
  have e : w.map nrm = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact nrm_id (by simpa [plainWord] using List.all_eq_true.mp h a ha)
  rw [e, List.map_id]

private theorem reach_live {roots : List Sig} {p bank T} (hp : proper T)
    (nT : plainWord T = true) (nR : roots.all plainWord = true)
    (h : Reach (roots.map observe) p bank) (hit : Available bank (observe T)) :
    ∃ k S, k ≤ p ∧ Live T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  unfold Repr at hm
  rw [nrm_id (by simpa [plainWord] using nT)] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l, V, hl, hr, hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l, V, by omega, hr, ?_⟩
  have e : (roots.map observe).map table = roots := by simp [List.map_map, Function.comp_def, table_observe]
  rw [e, nrm_map nR] at hs
  exact hs

private theorem live_row_difference {T k S} (h : Live T k S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop _ => exact ⟨_, by simp, diff⟩
  | @binary k U a b d _ _ _ _ _ _ ih =>
    obtain ⟨v, hv, hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b, by simp, ?_⟩
        intro beq
        exact hd (by rw [bit_bin, bit_bin, aeq, beq])
      · exact ⟨a, by simp, aeq⟩
    · exact ⟨v, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu), hd⟩

private theorem raw_required {T k S} (h : Live T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v, hv, hd⟩ := live_row_difference h diff
  by_cases veq : v = a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig :=
  [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0,
   0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
def target : Sig := 0xfeeaeac8fa88a888
def targetFun (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276808392 * 2 ^ 32 + 4203260040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def sample (r : Row) (j : Fin 6) : Bool := bit r (inputs.getD j.val zero)

private theorem coordinate0 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
private theorem coordinate1 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
private theorem coordinate2 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
private theorem coordinate3 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
private theorem coordinate4 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
private theorem coordinate5 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
private theorem input_coords : ∀ (j : Fin 6) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r; fin_cases j
  · exact coordinate0 r
  · exact coordinate1 r
  · exact coordinate2 r
  · exact coordinate3 r
  · exact coordinate4 r
  · exact coordinate5 r

private theorem input_list : List.ofFn (fun j : Fin 6 => inputs.getD j.val zero) = inputs := rfl
private theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [← input_list, List.map_ofFn]; rfl
private theorem target_table : ∀ r : Row, bit r target = targetFun (sample r) := by
  intro r
  have h1 : ∀ r : Row, bit r target =
      Nat.testBit (4276808392 * 2 ^ 32 + 4203260040)
        ((if sample r 0 then 1 else 0) + (if sample r 1 then 2 else 0) +
         (if sample r 2 then 4 else 0) + (if sample r 3 then 8 else 0) +
         (if sample r 4 then 16 else 0) + (if sample r 5 then 32 else 0)) := by decide +kernel
  rw [h1 r]
  unfold targetFun
  congr 1
  simp [Fin.sum_univ_six, add_assoc]

private theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [← b_read, execute_bits _ _ _ (fun g hg => (h g hg).1), sampled]
  rfl

def rename (f : Row → Row) (a : Sig) : Sig := table fun r => bit (f r) a
private theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
private theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
private theorem rename_bin (f : Row → Row) (d : Nat) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply bit_ext; intro r; simp only [bit_rename, bit_bin]
private theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  obtain ⟨r, hr⟩ := onto ⟨j, hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j, hj⟩ a = bit ⟨j, hj⟩ b
  rw [bit_rename, bit_rename, hr] at he
  exact he
private theorem rename_constants (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j, hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j, hj⟩).symm)
  · exact (bit_rename f one ⟨j, hj⟩).trans ((bit_one _).trans (bit_one ⟨j, hj⟩).symm)

private theorem live_rename {T k S} (h : Live T k S) (f : Row → Row) (onto : Function.Surjective f) :
    Live (rename f T) k (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz, fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)), fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.ind with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm; obtain ⟨v, hv, eq⟩ := Finset.mem_image.mp hm; exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert, rename_bin] at fresh ih ⊢
    exact Live.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

def Lower (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map observe) p bank → Available bank (observe T) → L ≤ p
def Impossible (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live T k S
def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

private theorem lower_impossible {roots T L} (hp : proper T) (nT : plainWord T = true)
    (nR : roots.all plainWord = true) (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible T L roots.toFinset) : Lower roots T (L + 1) := by
  intro p bank h ha
  obtain ⟨k, S, hk, run, hs⟩ := reach_live hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a; rw [List.mem_toFinset]
    refine ⟨fun hm => ?_, hs a⟩
    obtain ⟨r, s, hd, iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)

private theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b, h⟩
  have hr : represented [] v := by
    cases b
    · exact Or.inr (fun hp => hp.1 (bit_ext fun i => (congrFun h i).trans (bit_zero i).symm))
    · exact Or.inr (fun hp => hp.2 (bit_ext fun i => (congrFun h i).trans (bit_one i).symm))
  exact (hr.resolve_left (by simp)) hv

private theorem mass_append {R} (a b : List (Wire R)) : mass (a ++ b) = mass a + mass b := by simp [mass]
private theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons, List.length_cons, cost, if_pos ha, ih (fun x hx => hc x (by simp [hx]))]
    omega

private theorem restrict_of_sameUpToNeg {f : Row → Row} {T G : Sig}
    (eq : rename f T = G ∨ rename f T = neg G) (pG : proper G) :
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ bank, Available bank (restrictRows f (observe T)) → Available bank (observe G) := by
  rcases eq with h | h
  · have gc : restrictRows f (observe T) = observe G := (observe_rename _ _).symm.trans (congrArg observe h)
    rw [gc]; exact ⟨observe_proper pG, fun _ ha => ha⟩
  · have gc : restrictRows f (observe T) = inv (observe G) :=
      (observe_rename _ _).symm.trans ((congrArg observe h).trans (obs_neg G))
    rw [gc]
    refine ⟨fun hc => observe_proper pG (inv_inv' (observe G) ▸ inv_constant hc), fun bank ha => ?_⟩
    simpa only [inv_inv'] using avail_inv ha

private theorem lower_slice {roots other : List Sig} {T G : Sig} (pT : proper T)
    (nT : plainWord T = true) (nR : roots.all plainWord = true) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G ∨ rename r T = neg G)
    (covered : ∀ a ∈ roots, Available (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k, S, hk, run, sub⟩ := reach_live pT nT nR hh ha
  have subS : singles ⊆ S := by
    intro a hs; obtain ⟨i, j, hd, hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front, List.nodup_append]
    refine ⟨Finset.nodup_toList _, Finset.nodup_toList _, ?_⟩
    intro a ha b hb he; subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset = S := by ext a; simp [front, Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  obtain ⟨nc, imp⟩ := restrict_of_sameUpToNeg eq pG
  have supp : supply (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
    obtain ⟨a, hmem, rfl⟩ := List.mem_map.mp hm
    rw [← observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' nc Reach.start supp
    (L := L) (fun q bs hr ha' => prior q bs hr (imp bs ha'))
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front, List.map_append, mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
      obtain ⟨a, hmem, rfl⟩ := List.mem_map.mp hm
      rw [← observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs, List.length_map, Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]; omega
  omega

def childTwo (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

private theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) :
    (l.erase a).toFinset = l.toFinset.erase a := by ext x; simp [h.mem_erase_iff]

private theorem enum_step {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, allowed d → ∀ ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible T (cap - 1) (childTwo ws a b d ka kb).toFinset) :
    Impossible T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  induction h using Live.ind with
  | stop _ =>
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
      rw [show rest = (ws.erase a).erase b by rfl, erase_fin (hn.erase _) b, erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin, kept_fin, er, he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j = a <;>
        by_cases jb : j = b <;> simp_all [ka, kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => hn.not_mem_erase (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept, ar, hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_, kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b :: kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := live_size tail
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [← List.toFinset_card_of_nodup nd, eq]; omega
    exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)

def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧ (asig w).2.getLsbD i.val = bit (negRow i) w

def column {n} (s : BitVec n × BitVec n) : BitVec n := s.1 ^^^ s.2
def covered {n} (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a :: ws => column (sig a) ||| covered sig ws

private theorem covered_bit {n : Nat} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered sig ws).getLsbD i.val = true ↔ ∃ a ∈ ws, (column (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered, BitVec.getLsbD_or, Bool.or_eq_true, ih, List.mem_cons, exists_eq_or_imp]

private theorem cover_required {T ws k} (h : Live T k (List.toFinset ws)) {n : Nat}
    {r s : Fin n → Row} {sig} (correct : Sep T n r s sig) :
    covered sig ws = BitVec.allOnes n := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  let i : Fin n := ⟨j, hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj, decide_true]
  apply (covered_bit (i := i)).mpr
  obtain ⟨a, ha, hd⟩ := live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes, no])
  refine ⟨a, List.mem_toFinset.mp ha, ?_⟩
  simp only [column, BitVec.getLsbD_xor, (correct.2 a i).1, (correct.2 a i).2]
  cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all

def Slice (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach (roots.map observe) p bank → Available bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) : Sig := a &&& d
def availableB (d : Sig) (pool : List Sig) (a : Sig) : Bool :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v == m) ||
    (let c := masked d (neg a); (pool.map (masked d)).any (fun v => v == c))

private theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) : restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit, masked, BitVec.getLsbD_and, show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

private theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit, masked, BitVec.getLsbD_and, show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

private theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit, masked, BitVec.getLsbD_and, show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def poolSupply (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) : Prop :=
  ∀ a ∈ pool, Available bank (restrictRows f (observe a))

private theorem availableB_sound {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply f bank pool)
    (check : availableB d pool a = true) : Available bank (restrictRows f (observe a)) := by
  simp only [availableB, List.any_map, Function.comp_def, Bool.or_eq_true, beq_iff_eq,
    List.any_eq_true] at check
  rcases check with ((hz | ho) | ⟨v, hv, he⟩) | ⟨v, hv, he⟩
  · exact Or.inr (Or.inl ⟨false, masked_zero dom hz⟩)
  · exact Or.inr (Or.inl ⟨true, masked_one dom ho⟩)
  · exact masked_eq dom he ▸ supplyB v hv
  · have h := avail_inv (masked_eq dom he ▸ supplyB v hv)
    rw [obs_neg] at h
    have e : inv (restrictRows f (inv (observe a))) = restrictRows f (observe a) := by
      funext r; simp [inv, restrictRows]
    rwa [e] at h

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) : Sig := bin c.1 c.2.1 c.2.2
def choiceOK (d : Sig) (pool : List Sig) (c : Choice) : Bool :=
  decide (c.1 < 4) && (availableB d pool c.2.1 && availableB d pool c.2.2)

private theorem pay_choice {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (c : Choice) (valid : choiceOK d pool c = true) :
    ∃ next, Reach roots (q + 1) next ∧ poolSupply f next (choiceVal c :: pool) := by
  simp only [choiceOK, Bool.and_eq_true, decide_eq_true_eq] at valid
  obtain ⟨op, x, y, e, hx, hy, _, _⟩ :=
    comb_prime valid.1 (availableB_sound dom hs valid.2.1) (availableB_sound dom hs valid.2.2)
  refine ⟨_, Reach.two op hp hx hy, ?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · rw [choiceVal, obs_bin, restrict_comb, e]; exact Or.inl (by simp)
  · exact available_cons _ (hs _ hm)

def makePool (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c :: cs => if choiceOK d pool c then makePool d (choiceVal c :: pool) cs else none

private theorem makePool_sound {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (cs : List Choice) {result} (ok : makePool d pool cs = some result) :
    ∃ next, Reach roots (q + cs.length) next ∧ poolSupply f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_, hp, hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next, hr, sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out, hr', sh'⟩ := ih hr sh ok
      exact ⟨out, by simpa [Nat.add_assoc, Nat.add_comm 1] using hr', sh'⟩
    next => contradiction

def isMaskedConstant (d a : Sig) : Bool := masked d a == zero || masked d a == d

private theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons, List.map_cons, mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)) := by
        have hh : masked d a = zero ∨ masked d a = d := by
          simpa only [isMaskedConstant, Bool.or_eq_true, beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false, masked_zero dom hz⟩
        · exact ⟨true, masked_one dom ho⟩
      simpa [cost, hc, Nat.add_comm] using Nat.succ_le_succ ih

abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 64 - d.val then ⟨d.val + r.val, by omega⟩ else ⟨r.val - (64 - d.val), by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 64 (64 - d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) : Sig := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) : Sig :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

private theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 64 - d.val <;> simp [shifted, h, r.isLt]

private theorem bool_mux (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by
  cases p <;> simp
private theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit, mux, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, r.isLt,
    decide_true, Bool.true_and]
  exact bool_mux _ _ _
private theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a) = bit (rowMove m r) a := by
  simp only [wordMove, bit_mux, bit_shift, rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl

def movedRow (ms : List Move) (r : Row) : Row := ms.foldl (fun j m => rowMove m j) r
def movedWord (ms : List Move) (a : Sig) : Sig := ms.foldr wordMove a
private theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a) = bit (movedRow ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
private theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a = rename (movedRow ms) a := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  exact (bit_moved ms a ⟨j, hj⟩).trans (bit_rename _ _ ⟨j, hj⟩).symm

def freeWord (roots : List Sig) (w : Sig) : Bool := w == zero || w == one || roots.contains w
private theorem freeWord_ok {roots w} (ok : freeWord roots w = true) :
    Available (roots.map observe) (observe w) := by
  simp only [freeWord, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr (Or.inl ⟨false, funext bit_zero⟩)
  · exact Or.inr (Or.inl ⟨true, funext bit_one⟩)
  · exact Or.inl (List.mem_map_of_mem hm)

def sameUpToNeg (a b : Sig) : Bool := a == b || a == neg b
def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) : Bool :=
  sameUpToNeg (movedWord ms T) G && raw.all (fun a => freeWord base (movedWord ms a))

private theorem map_correct {ms raw T base G} (ok : checkMap ms raw T base G = true) :
    (rename (movedRow ms) T = G ∨ rename (movedRow ms) T = neg G) ∧
    ∀ a ∈ raw, Available (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap, sameUpToNeg, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    List.all_eq_true, moved_eq_rename] at ok
  exact ⟨ok.1, fun a ha => freeWord_ok (ok.2 a ha)⟩

private theorem lower_map {ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (nT : plainWord T = true) (nR : raw.all plainWord = true) (pG : proper G)
    (hL : Lower base G L) : Lower raw T L := by
  obtain ⟨eq, supp⟩ := map_correct ok
  simpa using lower_slice pT nT nR pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

private theorem slice_correct {ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower base G L) :
    Slice raw T d L := by
  obtain ⟨eq, supp⟩ := map_correct ok
  obtain ⟨nc, imp⟩ := restrict_of_sameUpToNeg eq properG
  refine ⟨movedRow ms, base, ?_, ?_, nc, ?_⟩
  · intro r; rw [← bit_moved, all, bit_one]
  · intro a ha; rw [← observe_rename]; exact supp a ha
  · intro p bank hr ha; exact hL p bank hr (imp bank ha)

def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) : Bool :=
  (bit rs.1 T != bit rs.2 T) && roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
private theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs = true) :
    Essential T roots a := by
  simp only [witnessB, Bool.and_eq_true, bne_iff_ne, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at ok
  exact ⟨rs.1, rs.2, ok.1, fun w hw hne => (ok.2 w hw).resolve_left hne⟩

def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) : Bool :=
  plainWord T && raw.all plainWord && xs.all (fun a => witnessB T raw a.1 a.2)
private theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  simp only [checkEssential, Bool.and_eq_true] at ok
  intro a ha
  obtain ⟨⟨a, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok.2 _ hm)
private theorem essential_plain {T raw xs} (ok : checkEssential T raw xs = true) :
    plainWord T = true ∧ raw.all plainWord = true := by
  simp only [checkEssential, Bool.and_eq_true] at ok; exact ok.1

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) : Bool :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

private theorem lift_ok {ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower base G L) :
    Lower raw T (L + (xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift, Bool.and_eq_true] at ok
  obtain ⟨eq, supp⟩ := map_correct ok.1.1
  apply lower_slice properT (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 properG _ eq supp _
    (essential_ok ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true, beq_iff_eq, moved_eq_rename] at hh
  rcases hh with h | h
  · rw [h]; exact ⟨false, funext bit_zero⟩
  · rw [h]; exact ⟨true, funext bit_one⟩

def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 6).filterMap fun i => if m.testBit i then some (i, inputs.getD i zero) else none
def freeMask (z o : Nat) : Nat := 63 ^^^ (z ||| o)
def freeVars (z o : Nat) : List Sig := (selected (freeMask z o)).map Prod.snd
def subcube (z o : Nat) : Sig :=
  (List.range 6).foldl (fun acc j =>
    let x := inputs.getD j zero
    if z.testBit j then acc &&& ~~~x
    else if o.testBit j then acc &&& x
    else acc) one
def fixRows (z o : Nat) : List Move :=
  (List.range 6).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 64 (1 <<< j)
    if z.testBit j then some (zero, x, step)
    else if o.testBit j then some (~~~x, zero, step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j) - (1 <<< i)
  (a &&& ~~~b, b &&& ~~~a, Fin.ofNat 64 d)
def subGoal (z o : Nat) : Sig := nrm (movedWord (fixRows z o) target)
def properB (T : Sig) : Bool := T != zero && T != one
private theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB, proper, Bool.and_eq_true, bne_iff_ne] using h

def carryOK (z o z' o' : Nat) (swaps : List Nat) : Bool :=
  (properB (subGoal z o) && plainWord (subGoal z o) && (freeVars z o).all plainWord) &&
    properB (subGoal z' o') &&
    checkMap (swaps.map swapRows) (freeVars z o) (subGoal z o) (freeVars z' o') (subGoal z' o')
private theorem carry_of {z o z' o' L swaps} (ok : carryOK z o z' o' swaps = true)
    (h : Lower (freeVars z' o') (subGoal z' o') L) : Lower (freeVars z o) (subGoal z o) L := by
  simp only [carryOK, Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1.1.1) ok.1.1.1.2 ok.1.1.2 (proper_of _ ok.1.2) h

abbrev BoundPool := Sig × Nat × Nat × List Sig
def BoundPool.domain (c : BoundPool) : Sig := c.1
def BoundPool.bound (c : BoundPool) : Nat := c.2.1
def BoundPool.paid (c : BoundPool) : Nat := c.2.2.1
def BoundPool.wires (c : BoundPool) : List Sig := c.2.2.2

def ValidPool (raw : List Sig) (T : Sig) (c : BoundPool) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach (roots.map observe) q ws → Available ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach (roots.map observe) c.paid bank ∧ poolSupply f bank c.wires

private theorem build_valid {raw T d lb} (h : Slice raw T d lb) (cs : List Choice) {ws}
    (build : makePool d raw cs = some ws) : ValidPool raw T ⟨d, lb, cs.length, ws⟩ := by
  obtain ⟨f, roots, dom, sup, nc, prior⟩ := h
  obtain ⟨bank, hr, hs⟩ := makePool_sound dom (Reach.start (roots := roots.map observe)) sup cs build
  exact ⟨f, roots, bank, dom, nc, prior, by simpa [BoundPool.paid] using hr, hs⟩

private theorem valid_exclude {raw T c} (valid : ValidPool raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB c.domain c.wires a = true)
    (buy : if paid then choiceOK c.domain c.wires choice = true
       else availableB c.domain c.wires (choiceVal choice) = true)
    (bound : k + c.paid + paid.toNat <
      c.bound + (choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible T k (choiceVal choice :: rest).toFinset := by
  intro t ht run
  obtain ⟨f, roots, bank, dom, nc, lo, hp, hs⟩ := valid
  let ws := choiceVal choice :: rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach (roots.map observe) n out)
      (zs : poolSupply f out (choiceVal choice :: rest)) (le : n = c.paid + paid.toNat) : False := by
    have covered : supply out ((ws.map observe).map (restrictRows f)) := by
      intro v hv
      obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := projected_bound f (list_run run ws nd rfl) nc reach covered lo
    have cm := count_constants dom ws
    change k + c.paid + paid.toNat < c.bound + ws.countP (isMaskedConstant c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact availableB_sound dom hs buy
    · exact availableB_sound dom hs (known _ hm)
  | true =>
    obtain ⟨out, hr, hc⟩ := pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have point : ∀ v ∈ c.wires, Available out (restrictRows f (observe v)) :=
        fun v hu => hc v (List.mem_cons_of_mem _ hu)
      exact availableB_sound dom point (known _ hm)

def scalarPoolCut (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) : Bool :=
  let z := choiceVal op
  let extra := !(availableB c.domain c.wires z)
  ((k + c.paid + extra.toNat < c.bound + (z :: rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB c.domain c.wires)) && (!extra || choiceOK c.domain c.wires op)

private theorem scalarPoolCut_sound {raw T c} (valid : ValidPool raw T c) {k rest op}
    (nd : (choiceVal op :: rest).Nodup) (cut : scalarPoolCut c k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  let extra := !(availableB c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut, Bool.and_eq_true, List.all_eq_true] at cut; exact cut.1.2
  · simp only [scalarPoolCut, Bool.and_eq_true, Bool.or_eq_true] at cut
    cases he : availableB c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut, Bool.and_eq_true, decide_eq_true_eq] at cut; exact cut.1.1

def materialize (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool d raw cs).map (fun pool => ⟨d, lb, cs.length, pool⟩)
private theorem materialize_sound {raw T d L cs c} (slice : Slice raw T d L)
    (h : materialize raw cs d L = some c) : ValidPool raw T c := by
  unfold materialize at h
  cases he : makePool d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he, Option.map_some, Option.some.injEq] at h
    subst c; exact build_valid slice cs he

abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
private theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 128 → Row) (a : Sig) : Signals := (ofRows r a, ofRows s a)
def properPairs (T : Sig) (r s : Fin 128 → Row) : Prop :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
private theorem properPairs_of_ofRows {T : Sig} {r s : Fin 128 → Row}
    (h : ((ofRows r T == BitVec.allOnes 128) && (ofRows s T == 0)) = true) :
    properPairs T r s := by
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  intro i
  have h1 := congrArg (fun v => v.getLsbD i.val) h.1
  have h2 := congrArg (fun v => v.getLsbD i.val) h.2
  rw [ofRows_bit, BitVec.getLsbD_allOnes] at h1
  rw [ofRows_bit] at h2
  simp [i.isLt] at h1 h2
  exact ⟨h1, h2⟩
private theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 128 r s (pairSig r s) :=
  ⟨h, fun _ _ => ⟨ofRows_bit _ _ _, ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 128 → Row) (x : Decor) : Prop := x.2 = pairSig r s x.1
def bv {n : Nat} (d : Nat) (a b : BitVec n) : BitVec n :=
  if d = 0 then a &&& b else if d = 1 then a ||| b else if d = 2 then a &&& ~~~b else ~~~a &&& b
def dbin (d : Nat) (x y : Decor) : Decor := (bin d x.1 y.1, bv d x.2.1 y.2.1, bv d x.2.2 y.2.2)

private theorem ofRows_bin {n : Nat} (r : Fin n → Row) (d : Nat) (a b : Sig) :
    ofRows r (bin d a b) = bv d (ofRows r a) (ofRows r b) := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j, hj⟩
  rw [bit_bin, ← ofRows_bit r a ⟨j, hj⟩, ← ofRows_bit r b ⟨j, hj⟩] at h
  rw [h]; unfold bv; split_ifs <;> simp [hj]
private theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx; change y.2 = _ at hy
  simp only [faithful, dbin, pairSig, ofRows_bin, hx, hy]

def defaultDecor : Decor := (zero, 0, 0)
private theorem faithful_default (r s) : faithful r s defaultDecor := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j = (ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j = bit (r ⟨j, hj⟩) zero from ofRows_bit _ _ ⟨j, hj⟩, bit_zero]; simp
  · change (0 : Bits).getLsbD j = (ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j = bit (s ⟨j, hj⟩) zero from ofRows_bit _ _ ⟨j, hj⟩, bit_zero]; simp
private theorem faithful_get {r s} {ws : List Decor} (all : ∀ v ∈ ws, faithful r s v) (i : Nat) :
    faithful r s (ws.getD i defaultDecor) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact faithful_default _ _
  | some v => exact all _ (List.mem_of_getElem? e)

def decodeBank (ws : List Decor) : List (Nat × Nat × Nat) → List Decor
  | [] => ws
  | (op, i, j) :: rest =>
    let a := ws.getD i defaultDecor
    let b := ws.getD j defaultDecor
    decodeBank (ws ++ [dbin op a b]) rest

private theorem decode_faithful {r s} (ws : List Decor) (steps : List (Nat × Nat × Nat))
    (base : ∀ v ∈ ws, faithful r s v) : ∀ v ∈ decodeBank ws steps, faithful r s v := by
  induction steps generalizing ws with
  | nil => exact base
  | cons st steps ih =>
    obtain ⟨op, i, j⟩ := st
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      exact faithful_bin op (faithful_get base i) (faithful_get base j)

def asRow (cols : Nat → Bits) (i : Fin 128) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 6 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
private theorem asRow_bit (cols : Nat → Bits) (i : Fin 128) (j : Fin 6) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 6 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j, a) => (a, p j, q j))
private theorem selected_entry {m j a} (h : (j, a) ∈ selected m) :
    j < 6 ∧ a = inputs.getD j zero := by
  obtain ⟨v, hv, hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next => cases hh; exact ⟨hv, rfl⟩
  next => contradiction
private theorem raw_faithful (m) (p q : Nat → Bits) :
    ∀ a ∈ rawDecor m p q, faithful (asRow p) (asRow q) a := by
  intro a ha
  obtain ⟨⟨j, v⟩, hv, rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj, rfl⟩ := selected_entry hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (asRow_bit p ⟨i, hi⟩ ⟨j, hj⟩).symm.trans (ofRows_bit _ _ ⟨i, hi⟩).symm
  · exact (asRow_bit q ⟨i, hi⟩ ⟨j, hj⟩).symm.trans (ofRows_bit _ _ ⟨i, hi⟩).symm

abbrev Cov := Bits × Bits × Bits
def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z), (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))
def coverage (v : List Decor) : Cov := v.foldr (fun a c => addCov (column a.2) c) (0, 0, 0)
def takeOne (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a = c.1 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [takeOne, addCov, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, hi,
    decide_true, Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl
private theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b = c.1 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [takeTwo, addCov, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, hi,
    decide_true, Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl
private theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c) = addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [addCov, BitVec.getLsbD_or]; cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, hi,
        decide_true, Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl
private theorem cov_perm {l r : List Decor} (h : l.Perm r) : coverage l = coverage r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (column a.2)) ih
  | swap _ _ _ => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2
private theorem cov_word (v : List Decor) {r s} (good : ∀ a ∈ v, faithful r s a) :
    (coverage v).1 = covered (pairSig r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column a.2 ||| (coverage v).1) = column (pairSig r s a.1) ||| _
    rw [show a.2 = pairSig r s a.1 from good _ (by simp), ih (fun a ha => good a (by simp [ha]))]

def delOne (ws : List Decor) (a : Decor) (keep : Bool) : List Decor := if keep then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) : List Decor := delOne (delOne ws a ka) b kb
private theorem delOne_perm {ws : List Decor} (a : Decor) (ha : a ∈ ws) : ws.Perm (a :: ws.erase a) :=
  List.perm_cons_erase ha
private theorem cover_one {ws : List Decor} (a : Decor) (ha : a ∈ ws) (keep : Bool) :
    (coverage (delOne ws a keep)).1 = (if keep then (coverage ws).1 else takeOne (coverage ws) (column a.2)) := by
  cases keep
  · change (coverage (ws.erase a)).1 = takeOne (coverage ws) _
    rw [cov_perm (delOne_perm a ha)]; exact (cov_one _ _).symm
  · rfl
private theorem delTwo_perm {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ws.Perm (a :: b :: (ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (delOne_perm a ha).trans (List.Perm.cons _ (delOne_perm b hm))
private theorem cover_two {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (ka kb : Bool) :
    (coverage (delTwo ws a b ka kb)).1 =
      (if ka then (if kb then (coverage ws).1 else takeOne (coverage ws) (column b.2))
       else if kb then takeOne (coverage ws) (column a.2)
       else takeTwo (coverage ws) (column a.2) (column b.2)) := by
  cases ka <;> cases kb
  · change (coverage ((ws.erase a).erase b)).1 = takeTwo (coverage ws) _ _
    rw [cov_perm (delTwo_perm a b ha hb ne)]; exact (cov_two _ _ _).symm
  · exact cover_one a ha false
  · exact cover_one b hb false
  · rfl

def sameWords (a b : List Sig) : Bool := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
private theorem sameWords_sound {xs ys} (h : sameWords xs ys = true) : xs.toFinset = ys.toFinset := by
  simp only [sameWords, Bool.and_eq_true, List.all_eq_true, List.contains_eq_mem, decide_eq_true_eq] at h
  ext a; simp only [List.mem_toFinset]; exact ⟨h.1 a, h.2 a⟩

def keyWord (v : Sig) : Nat :=
  let n := v.toNat
  (n * 11400714819323198485 + (n >>> 17)) % 4294967291
def keySet (xs : List Sig) : Nat := xs.foldl (fun v x => v + keyWord x) 0

def closeChild (pools : List BoundPool) (links : Nat → List (Nat × List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) : Bool :=
  pools.any (fun p => scalarPoolCut p k rest op) ||
    (let ws := choiceVal op :: rest
     let tag := keySet ws
     (links tag).any (fun p => p.1 == tag && sameWords ws p.2))

private theorem closeChild_sound {raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ tag p, p ∈ links tag → Impossible T k p.2.toFinset)
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at h
  rcases h with ⟨p, hp, ok⟩ | ⟨p, hp, _, ok⟩
  · exact scalarPoolCut_sound (pValid _ hp) nd ok
  · rw [sameWords_sound ok]; exact lValid _ _ hp

def restCov (v : Cov) (a b : Bits) (ka kb : Bool) : Bits :=
  if ka then (if kb then v.1 else takeOne v b) else if kb then takeOne v a else takeTwo v a b

private theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
private theorem keep_sub (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    (delTwo ws a b ka kb).Sublist ws := (delOne_sub _ _ _).trans (delOne_sub _ _ _)
private theorem len_keep (ws : List Decor) (a b : Decor) (ka kb : Bool)
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) :
    (delTwo ws a b ka kb).length = ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  cases ka <;> cases kb <;>
    simp [delTwo, delOne, List.length_erase_of_mem ha, List.length_erase_of_mem hb, List.length_erase_of_mem hm]

def movedChoice (op : Nat) (a b : Decor) : Choice := (op, a.1, b.1)
abbrev NodeContext := Nat × Nat × List Decor × Cov × List BoundPool × (Nat → List (Nat × List Sig))

def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) : Bool :=
  let (cap, n, ws, cov, pools, links) := c
  let len := 1 + (n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len > cap then true else
    let rs := restCov cov (column a.2) (column b.2) ka kb
    if (rs ||| column z.2) != BitVec.allOnes 128 then true else
    if !properB z.1 || ws.any (fun v => v.1 == z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChild pools links (cap - 1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) : List Sig :=
  (dbin op a b).1 :: (delTwo ws a b ka kb).map Prod.fst

private theorem evalMove_sound {raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) (hcap : 0 < cap)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag p, p ∈ links tag → Impossible T (cap - 1) p.2.toFinset)
    (pro : proper (dbin op a b).1) (fresh : (dbin op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap, ws.length, ws, coverage ws, pools, links) op a b (dbin op a b) ka kb = true) :
    Impossible T (cap - 1) (moveFront ws op a b ka kb).toFinset := by
  let z := dbin op a b
  let rest := delTwo ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm), nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1 == z.1) = false := by
    apply Bool.eq_false_iff.mpr; intro hh
    obtain ⟨x, hx, he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB, proper] using pro
  have leq : 1 + (ws.length - (if ka then 0 else 1) - (if kb then 0 else 1)) = child.length := by
    change _ = (z.1 :: rest.map Prod.fst).length
    rw [List.length_cons, List.length_map, len_keep _ _ _ _ _ ha hb ne, Nat.add_comm 1]
  intro k hk h
  have hsz := live_size h
  change child.toFinset.card ≤ k + 1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1 + (ws.length - _ - _) > cap then true else _) = true at test
  rw [leq, if_neg (by omega)] at test
  have sep := cover_required h (pair_sep pairs)
  have g : (coverage rest).1 = covered (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ (fun v hv => faith _ (sub.subset hv))
  have rz : (coverage rest).1 = restCov (coverage ws) (column a.2) (column b.2) ka kb :=
    cover_two a b ha hb ne ka kb
  have hf := faithful_bin op (faith _ ha) (faith _ hb)
  change column (pairSig r s z.1) ||| covered (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [← hf, ← g, rz, BitVec.or_comm] at sep
  have be : ((restCov (coverage ws) (column a.2) (column b.2) ka kb ||| column z.2) != BitVec.allOnes 128) = false := by
    simpa using sep
  change (if (restCov (coverage ws) (column a.2) (column b.2) ka kb ||| column z.2) != BitVec.allOnes 128 then true
    else if !properB z.1 || ws.any (fun v => v.1 == z.1) then true else _) = true at test
  rw [be, pp, fr] at test
  exact closeChild_sound (op := movedChoice op a b) (rest := rest.map Prod.fst) pv lv ndc test k hk h

def testPair (ctx : NodeContext) (a b : Decor) (op : Nat) : Bool :=
  let z := dbin op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) : Bool :=
  bs.all (fun b => [0, 1, 2, 3].all (testPair ctx a b))
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a :: bs => testRow ctx a bs && testAll ctx bs

private theorem ops_mem {d} (h : allowed d) : d ∈ ([0, 1, 2, 3] : List Nat) := by
  rcases allowed_four h with rfl | rfl | rfl | rfl <;> simp

private theorem all_binary {ctx ws} (h : testAll ctx ws = true) {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) : (∀ d, allowed d → testPair ctx a b d = true) ∨ (∀ d, allowed d → testPair ctx b a d = true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll, Bool.and_eq_true, testRow, List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (ops_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (ops_mem hd)
      · exact ih h.2 haTail hbTail

private theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx d a b (dbin d a b) ka kb = true := by
  simp only [testPair, Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

private theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w = a ∧ k = true) ∨ w ∈ v := by cases k <;> simp [kept]
private theorem mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w ∈ v ∧ (w ≠ a ∨ k = true) := by
  cases k <;> simp [delOne, nd.mem_erase_iff, and_comm]
private theorem unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (eq : a.1 = b.1) : a = b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn, ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail
private theorem kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v ≠ a.1 ∨ ka = true) ∧ (v ≠ b.1 ∨ kb = true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  simp only [delTwo, List.mem_map, mem_delone wn, mem_delone dn]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨⟨_, hw.1.1, rfl⟩, hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
      hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w, hm, rfl⟩, h1, h2⟩
    exact ⟨w, ⟨⟨hm, h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
      h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩, rfl⟩
private theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : a.1 ≠ b.1) (d : Nat) (ka kb : Bool) :
    (moveFront ws d a b ka kb).toFinset = (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f := Prod.fst) ha
  have bv' := List.mem_map_of_mem (f := Prod.fst) hb
  simp only [moveFront, childTwo, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset,
    kept_value nd ha hb, keep_mem, (nd.erase _).mem_erase_iff, nd.mem_erase_iff, dbin]
  by_cases va : v = a.1 <;> by_cases vb : v = b.1 <;> cases ka <;> cases kb <;> simp_all
private theorem childTwo_swap (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : allowed d)
    (ka kb : Bool) : (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset,
    keep_mem, (nd.erase _).mem_erase_iff, nd.mem_erase_iff, bin_flip hd a b]
  tauto

private theorem node_sound {raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag p, p ∈ links tag → Impossible T (cap - 1) p.2.toFinset)
    (checks : testAll (cap, ws.length, ws, coverage ws, pools, links) ws = true) :
    Impossible T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap = 0
  · intro k hk h
    have ke : k = 0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    obtain ⟨hS, _⟩ := h
    exact out (List.mem_toFinset.mp (by rw [he, hS]; exact Finset.mem_singleton_self _))
  have hc' : 0 < cap := by omega
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne fresh pro _
  obtain ⟨a, haW, rfl⟩ := List.mem_map.mp ha
  obtain ⟨b, hbW, rfl⟩ := List.mem_map.mp hb
  have ab : a ≠ b := fun e => ne (congrArg Prod.fst e)
  have one (a b : Decor) (d : Nat) (aa : a ∈ ws) (bb : b ∈ ws) (ne' : a.1 ≠ b.1) (ka kb : Bool)
      (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
      (test : testPair (cap, ws.length, ws, coverage ws, pools, links) a b d = true) :
      Impossible T (cap - 1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [← binary_front nd aa bb ne']
    exact evalMove_sound pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (testPair_at test ka kb)
  rcases all_binary checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    exact one b a (flipOp d) hbW haW (Ne.symm ne) kb ka (bin_flip hd a.1 b.1 ▸ pro)
      (bin_flip hd a.1 b.1 ▸ fresh) (hh _ (flip_flip hd).1)

private theorem agree_inputs (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r = s := by
  apply Fin.ext; apply Nat.eq_of_testBit_eq; intro j
  by_cases hj : j < 6
  · let i : Fin 6 := ⟨j, hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]; exact List.mem_ofFn.mpr ⟨i, rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 64 ≤ 2 ^ j := by
      change 2 ^ 6 ≤ 2 ^ j; exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm

def composedOK (p q : List Move) : Bool := inputs.all (fun a => movedWord p (movedWord q a) == a)
private theorem composed_id {p q} (h : composedOK p q = true) (r : Row) :
    movedRow q (movedRow p r) = r := by
  apply agree_inputs; intro a ha
  rw [← bit_moved, ← bit_moved]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]

def autoOK (T : Sig) (p : List Move) : Bool :=
  (movedWord p T == T) && composedOK p p.reverse && composedOK p.reverse p
private theorem rotate_excluded {T n} {ws : List Sig} (hi : Impossible T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK, Bool.and_eq_true, beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r, composed_id ok.2 r⟩
  intro k hk h
  have run := live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T = T := (moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    change bit ⟨j, hj⟩ _ = bit ⟨j, hj⟩ _
    rw [bit_rename, bit_moved, composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p)) = ws.toFinset := by
    ext a; simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨v, ⟨w, hw, rfl⟩, rfl⟩; simpa only [inv] using hw
    · intro ha; exact ⟨_, ⟨a, ha, rfl⟩, inv a⟩
  rw [goal, back] at run
  exact hi k hk run

def mk128 (hi lo : Nat) : Bits := (BitVec.ofNat 128 hi <<< 64) ||| BitVec.ofNat 128 lo

def Trie : Nat → Type
  | 0 => List (Nat × List Sig)
  | d + 1 => Trie d × Trie d

def Trie.empty : (d : Nat) → Trie d
  | 0 => []
  | d + 1 => (Trie.empty d, Trie.empty d)

def Trie.insert : (d : Nat) → Nat → (Nat × List Sig) → Trie d → Trie d
  | 0, _, v, xs => v :: xs
  | d + 1, k, v, t =>
    if k % 2 = 0 then (Trie.insert d (k / 2) v t.1, t.2)
    else (t.1, Trie.insert d (k / 2) v t.2)

def Trie.get : (d : Nat) → Nat → Trie d → List (Nat × List Sig)
  | 0, _, xs => xs
  | d + 1, k, t =>
    if k % 2 = 0 then Trie.get d (k / 2) t.1 else Trie.get d (k / 2) t.2

private theorem Trie.empty_mem (d k : Nat) (p : Nat × List Sig) : p ∉ Trie.get d k (Trie.empty d) := by
  induction d generalizing k with
  | zero => simp [Trie.empty, Trie.get]
  | succ d ih =>
    simp only [Trie.empty, Trie.get]
    split <;> exact ih (k / 2)

private theorem Trie.insert_mem {P : Nat × List Sig → Prop} (d k : Nat) (v : Nat × List Sig) (t : Trie d)
    (ht : ∀ q p, p ∈ Trie.get d q t → P p) (hv : P v) :
    ∀ q p, p ∈ Trie.get d q (Trie.insert d k v t) → P p := by
  induction d generalizing k with
  | zero =>
    intro q p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hv
    · exact ht q p hp
  | succ d ih =>
    intro q p hp
    by_cases hk : k % 2 = 0 <;> by_cases hq : q % 2 = 0
    · simp [Trie.get, Trie.insert, hk, hq] at hp
      exact ih (k / 2) t.1 (fun q' p' hp' => ht (2 * q') p' (by simp [Trie.get, hp'])) (q / 2) p hp
    · simp [Trie.get, Trie.insert, hk, hq] at hp
      exact ht q p (by simp [Trie.get, hq, hp])
    · simp [Trie.get, Trie.insert, hk, hq] at hp
      exact ht q p (by simp [Trie.get, hq, hp])
    · simp [Trie.get, Trie.insert, hk, hq] at hp
      exact ih (k / 2) t.2 (fun q' p' hp' => ht (2 * q' + 1) p' (by simp [Trie.get, show (2 * q' + 1) / 2 = q' by omega, hp'])) (q / 2) p hp

def buildTrie (xs : List (List Sig)) : Trie 6 :=
  xs.foldl (fun t ws => let tag := keySet ws; Trie.insert 6 tag (tag, ws) t) (Trie.empty 6)

private theorem buildTrie_sound {P : List Sig → Prop} {xs : List (List Sig)}
    (hxs : ∀ ws ∈ xs, P ws) : ∀ tag p, p ∈ Trie.get 6 tag (buildTrie xs) → P p.2 := by
  suffices ∀ (t : Trie 6) (ys : List (List Sig)),
      (∀ q p, p ∈ Trie.get 6 q t → P p.2) → (∀ ws ∈ ys, P ws) →
      ∀ q p, p ∈ Trie.get 6 q (ys.foldl (fun t ws => let tag := keySet ws; Trie.insert 6 tag (tag, ws) t) t) → P p.2 by
    exact this (Trie.empty 6) xs (fun q p hp => False.elim (Trie.empty_mem 6 q p hp)) hxs
  intro t ys ht hys
  induction ys generalizing t with
  | nil => exact ht
  | cons ws ys ih =>
    apply ih
    · exact Trie.insert_mem (P := fun p => P p.2) 6 (keySet ws) (keySet ws, ws) t ht (hys ws (by simp))
    · exact fun w hw => hys w (by simp [hw])

def rotatedLevel (autos : List (List Move)) (prev : List (List Sig)) : List (List Sig) :=
  match autos with
  | [[]] => prev
  | _ => prev.flatMap fun ws => autos.map fun p => ws.map (movedWord p.reverse)

private theorem rotatedLevel_sound {T cap autos prev}
    (ha : ∀ p ∈ autos, autoOK T p = true)
    (hp : ∀ ws ∈ prev, Impossible T cap ws.toFinset) :
    ∀ xs ∈ rotatedLevel autos prev, Impossible T cap xs.toFinset := by
  intro xs hxs
  unfold rotatedLevel at hxs
  split at hxs
  · exact hp xs hxs
  · obtain ⟨ws, hws, h1⟩ := List.mem_flatMap.mp hxs
    obtain ⟨p, hp', rfl⟩ := List.mem_map.mp h1
    exact rotate_excluded (hp ws hws) p (ha p hp')

abbrev NodeSpec := List (Nat × Nat × Nat) × List Nat × List (Nat × List Nat)

private structure ChartFormat where
  raw : Nat
  depth : Nat
  depthBits : Nat
  poolBits : Nat
  sliceBits : Nat

private def splitBits (tape width : Nat) : Nat × Nat :=
  (tape % 2^width, tape / 2^width)

private def chartGates (raw : Nat) : Nat → Nat → Nat → List (Nat × Nat × Nat) × Nat
  | 0, _, tape => ([], tape)
  | n+1, i, tape =>
    let width := Nat.log2 (raw+i-1)+1
    let (d,tape) := splitBits tape 2
    let (a,tape) := splitBits tape width
    let (b,tape) := splitBits tape width
    let (gs,tape) := chartGates raw n (i+1) tape
    ((d,a,b) :: gs,tape)

private def chartSlots (width : Nat) : Nat → Nat → List Nat × Nat
  | 0, tape => ([], tape)
  | n+1, tape =>
    let (i,tape) := splitBits tape width
    let (is,tape) := chartSlots width n tape
    (i :: is,tape)

private def chartPools (h sw : Nat) : Nat → Nat → List (Nat × List Nat) × Nat
  | 0, tape => ([], tape)
  | n+1, tape =>
    let (s,tape) := splitBits tape sw
    let (deps,tape) := splitBits tape h
    let (rest,tape) := chartPools h sw n tape
    ((s,(List.range h).filter deps.testBit) :: rest,tape)

private def chartNodes (f : ChartFormat) : Nat → Nat → List NodeSpec
  | 0, _ => []
  | n+1, tape =>
    let (h,tape) := if f.depthBits == 0 then (f.depth,tape) else splitBits tape f.depthBits
    let (gates,tape) := chartGates f.raw h 0 tape
    let (m,tape) := splitBits tape 4
    let (slots,tape) := chartSlots (Nat.log2 (f.raw+h-1)+1) m tape
    let (c,tape) := splitBits tape f.poolBits
    let (pools,tape) := chartPools h f.sliceBits c tape
    (gates,slots,pools) :: chartNodes f n tape

private def gammaZeros : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, tape => if tape.testBit 0 then 0 else 1 + gammaZeros n (tape / 2)

private def gammaRead (tape : Nat) : Nat × Nat :=
  let z := gammaZeros 16 tape
  let (low,rest) := splitBits (tape / 2^(z+1)) z
  (2^z+low,rest)

private def chartGaps : Nat → Nat → Nat → List Nat
  | 0, _, _ => []
  | n+1, base, tape =>
    let (delta,rest) := gammaRead tape
    let next := base+delta
    (next-1) :: chartGaps n next rest

private def chartPicks (tape : Nat) : List Nat :=
  let (count,rest) := gammaRead tape
  chartGaps (count-1) 0 rest

def nodeWires (rawD : List Decor) (spec : NodeSpec) : List Decor :=
  let bank := decodeBank rawD spec.1
  spec.2.1.map fun idx => bank.getD idx defaultDecor

def nodeSigs (rawD : List Decor) (spec : NodeSpec) : List Sig :=
  (nodeWires rawD spec).map Prod.fst

def choiceAt (bank : List Decor) (st : Nat × Nat × Nat) : Choice :=
  (st.1, (bank.getD st.2.1 defaultDecor).1, (bank.getD st.2.2 defaultDecor).1)

def choicesOf (bank : List Decor) (hist : List (Nat × Nat × Nat)) (idxs : List Nat) : List Choice :=
  idxs.map fun k => choiceAt bank (hist.getD k (0, 0, 0))

def buildPools (raw : List Sig) (slices : List (Sig × Nat)) (bank : List Decor)
    (hist : List (Nat × Nat × Nat)) : List (Nat × List Nat) → Option (List BoundPool)
  | [] => some []
  | (si, idxs) :: rest =>
    match slices[si]? with
    | none => none
    | some (d, lb) =>
      match materialize raw (choicesOf bank hist idxs) d lb, buildPools raw slices bank hist rest with
      | some p, some ps => some (p :: ps)
      | _, _ => none

private theorem buildPools_sound {raw T slices bank hist specs pools}
    (hs : ∀ s ∈ slices, Slice raw T s.1 s.2)
    (hb : buildPools raw slices bank hist specs = some pools) :
    ∀ p ∈ pools, ValidPool raw T p := by
  induction specs generalizing pools with
  | nil =>
    cases hb; intro _ h; exact False.elim (List.not_mem_nil h)
  | cons sp rest ih =>
    obtain ⟨si, idxs⟩ := sp
    simp only [buildPools] at hb
    cases hget : slices[si]? with
    | none => simp [hget] at hb
    | some sl =>
      obtain ⟨d, lb⟩ := sl
      simp only [hget] at hb
      cases hm : materialize raw (choicesOf bank hist idxs) d lb with
      | none => simp [hm] at hb
      | some p =>
        cases hr : buildPools raw slices bank hist rest with
        | none => simp [hm, hr] at hb
        | some ps =>
          simp only [hm, hr, Option.some.injEq] at hb
          subst pools
          intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · exact materialize_sound (hs (d, lb) (List.mem_of_getElem? hget)) hm
          · exact ih hr q hq

def nodupB : List Sig → Bool
  | [] => true
  | x :: xs => !(xs.contains x) && nodupB xs

private theorem nodupB_sound : ∀ {xs : List Sig}, nodupB xs = true → xs.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    simp only [nodupB, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at h
    exact List.nodup_cons.mpr ⟨h.1, nodupB_sound h.2⟩

def nodeCheck (raw : List Sig) (rawD : List Decor) (T : Sig) (slices : List (Sig × Nat))
    (links : Nat → List (Nat × List Sig)) (cap : Nat) (spec : NodeSpec) : Bool :=
  let bank := decodeBank rawD spec.1
  let ws := spec.2.1.map fun idx => bank.getD idx defaultDecor
  let sigs := ws.map Prod.fst
  nodupB sigs && !(sigs.contains T) &&
  match buildPools raw slices bank spec.1 spec.2.2 with
  | none => false
  | some pools => testAll (cap, ws.length, ws, coverage ws, pools, links) ws

private theorem nodeCheck_sound {raw rawD T r s slices links cap spec}
    (pairs : properPairs T r s) (baseF : ∀ v ∈ rawD, faithful r s v)
    (hs : ∀ sl ∈ slices, Slice raw T sl.1 sl.2)
    (lv : ∀ tag p, p ∈ links tag → Impossible T (cap - 1) p.2.toFinset)
    (ok : nodeCheck raw rawD T slices links cap spec = true) :
    Impossible T cap (nodeSigs rawD spec).toFinset := by
  unfold nodeCheck at ok
  dsimp only at ok
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not] at ok
  obtain ⟨⟨hnd, hout⟩, hmatch⟩ := ok
  cases hbp : buildPools raw slices (decodeBank rawD spec.1) spec.1 spec.2.2 with
  | none => simp [hbp] at hmatch
  | some pools =>
    simp only [hbp] at hmatch
    have bf := decode_faithful rawD spec.1 baseF
    have wf : ∀ w ∈ nodeWires rawD spec, faithful r s w := by
      intro w hw
      obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hw
      exact faithful_get bf idx
    exact node_sound pairs wf (nodupB_sound hnd) hout (buildPools_sound hs hbp) lv hmatch

def LevelOK (rawD : List Decor) (T : Sig) (cap : Nat) (nodes : List NodeSpec) : Prop :=
  ∀ spec ∈ nodes, Impossible T cap (nodeSigs rawD spec).toFinset

def levelCheck (raw : List Sig) (rawD : List Decor) (T : Sig) (slices : List (Sig × Nat))
    (autos : List (List Move)) (prev : List NodeSpec) (cap : Nat) (nodes : List NodeSpec) : Bool :=
  let tbl := buildTrie (rotatedLevel autos (prev.map (nodeSigs rawD)))
  nodes.all (nodeCheck raw rawD T slices (fun h => Trie.get 6 h tbl) cap)

private def selectFrom (k : Nat) (ids : List Nat) : List NodeSpec → List NodeSpec
  | [] => []
  | node :: rest =>
    match ids with
    | [] => []
    | i :: more =>
      if i = k then node :: selectFrom (k + 1) more rest
      else selectFrom (k + 1) ids rest

private theorem selectFrom_mem {node : NodeSpec} {k ids prev} (h : node ∈ selectFrom k ids prev) :
    node ∈ prev := by
  induction prev generalizing k ids with
  | nil => simp [selectFrom] at h
  | cons x xs ih =>
    cases ids with
    | nil => simp [selectFrom] at h
    | cons i is =>
      simp only [selectFrom] at h
      split at h
      · rcases List.mem_cons.mp h with he | hm
        · exact List.mem_cons.mpr (Or.inl he)
        · exact List.mem_cons_of_mem _ (ih hm)
      · exact List.mem_cons_of_mem _ (ih h)

private theorem levelCheck_join {raw rawD T slices autos prev cap a b}
    (ha : levelCheck raw rawD T slices autos prev cap a = true)
    (hb : levelCheck raw rawD T slices autos prev cap b = true) :
    levelCheck raw rawD T slices autos prev cap (a ++ b) = true := by
  simp only [levelCheck, List.all_append, Bool.and_eq_true] at ha hb ⊢
  exact ⟨ha, hb⟩

private theorem levelCheck_sound {raw rawD T r s slices autos prev cap nodes}
    (pairs : properPairs T r s) (baseF : ∀ v ∈ rawD, faithful r s v)
    (hs : ∀ sl ∈ slices, Slice raw T sl.1 sl.2)
    (ha : ∀ p ∈ autos, autoOK T p = true)
    (hprev : LevelOK rawD T (cap - 1) prev)
    (ok : levelCheck raw rawD T slices autos prev cap nodes = true) :
    LevelOK rawD T cap nodes := by
  unfold levelCheck at ok
  dsimp only at ok
  have hpm : ∀ ws ∈ prev.map (nodeSigs rawD), Impossible T (cap - 1) ws.toFinset := by
    intro ws hws
    obtain ⟨sp, hsp, rfl⟩ := List.mem_map.mp hws
    exact hprev sp hsp
  have lv := buildTrie_sound (rotatedLevel_sound ha hpm)
  intro sp hsp
  exact nodeCheck_sound pairs baseF hs lv (List.all_eq_true.mp ok sp hsp)

private structure ChartBatch where
  count : Nat
  data : Nat
  picks : Nat

private def ChartBatch.nodes (f : ChartFormat) (c : ChartBatch) : List NodeSpec :=
  chartNodes f c.count c.data

private def flattenBatches (f : ChartFormat) (prev : List ChartBatch) : List NodeSpec :=
  prev.flatMap (fun c => c.nodes f)

private def blockPicks (f : ChartFormat) (autos : List (List Move)) (start : Nat)
    (ids : List Nat) (c : ChartBatch) : List (List Move × NodeSpec) :=
  ids.filterMap fun i => do
    let p ← autos[(i-start)%autos.length]?
    let spec ← (c.nodes f)[(i-start)/autos.length]?
    return (p,spec)

private theorem blockPicks_mem {f autos start ids c p spec}
    (h : (p,spec) ∈ blockPicks f autos start ids c) :
    p ∈ autos ∧ spec ∈ c.nodes f := by
  obtain ⟨i, _, hi⟩ := List.mem_filterMap.mp h
  cases ha : autos[(i-start)%autos.length]? with
  | none => simp [ha] at hi
  | some a =>
    cases hs : (c.nodes f)[(i-start)/autos.length]? with
    | none => simp [ha, hs] at hi
    | some s =>
      simp [ha, hs] at hi
      rcases hi with ⟨rfl, rfl⟩
      exact ⟨List.mem_of_getElem? ha, List.mem_of_getElem? hs⟩

private def selectOriented (f : ChartFormat) (autos : List (List Move)) (start : Nat)
    (ids : List Nat) : List ChartBatch → List (List Move × NodeSpec)
  | [] => []
  | c :: rest => match ids with
    | [] => []
    | i :: _ =>
      let stop := start + c.count * autos.length
      if i < stop then
        blockPicks f autos start (ids.takeWhile fun j => j < stop) c ++
          selectOriented f autos stop (ids.dropWhile fun j => j < stop) rest
      else selectOriented f autos stop ids rest

private theorem selectOriented_mem {f autos start ids prev p spec}
    (h : (p,spec) ∈ selectOriented f autos start ids prev) :
    p ∈ autos ∧ spec ∈ flattenBatches f prev := by
  induction prev generalizing start ids with
  | nil => simp [selectOriented] at h
  | cons c rest ih =>
    cases ids with
    | nil => simp [selectOriented] at h
    | cons i is =>
      simp only [selectOriented] at h
      split at h
      · rcases List.mem_append.mp h with h | h
        · obtain ⟨hp,hc⟩ := blockPicks_mem h
          exact ⟨hp,List.mem_flatMap.mpr ⟨c, by simp, hc⟩⟩
        · obtain ⟨hp,hs⟩ := ih h
          rcases List.mem_flatMap.mp hs with ⟨b,hb,hn⟩
          exact ⟨hp,List.mem_flatMap.mpr ⟨b, by simp [hb], hn⟩⟩
      · obtain ⟨hp,hs⟩ := ih h
        rcases List.mem_flatMap.mp hs with ⟨b,hb,hn⟩
        exact ⟨hp,List.mem_flatMap.mpr ⟨b, by simp [hb], hn⟩⟩

private def rotatedSpec (rd : List Decor) (q : List Move × NodeSpec) : List Sig :=
  (nodeSigs rd q.2).map (movedWord q.1.reverse)

private def checkOriented (raw : List Sig) (rd : List Decor) (T : Sig) (slices : List (Sig × Nat))
    (cap : Nat) (picks : List (List Move × NodeSpec)) (nodes : List NodeSpec) : Bool :=
  let tbl := buildTrie (picks.map (rotatedSpec rd))
  nodes.all (nodeCheck raw rd T slices (fun h => Trie.get 6 h tbl) cap)

private abbrev CheckedBatch (raw : List Sig) (rd : List Decor) (T : Sig)
    (slices : List (Sig × Nat)) (autos : List (List Move)) (cap : Nat)
    (pf : ChartFormat) (prev : List ChartBatch) (f : ChartFormat) :=
  { c : ChartBatch // checkOriented raw rd T slices cap
      (selectOriented pf autos 0 (chartPicks c.picks) prev) (c.nodes f) = true }

private theorem checkedBatches {raw rd T r s slices autos cap pf prev f}
    (pairs : properPairs T r s) (baseF : ∀ v ∈ rd, faithful r s v)
    (hs : ∀ sl ∈ slices, Slice raw T sl.1 sl.2)
    (ha : autos.all (autoOK T) = true)
    (hprev : LevelOK rd T (cap-1) (flattenBatches pf prev))
    (chunks : List (CheckedBatch raw rd T slices autos cap pf prev f)) :
    LevelOK rd T cap (flattenBatches f (chunks.map Subtype.val)) := by
  intro sp hsp
  obtain ⟨b,hb,hc⟩ := List.mem_flatMap.mp hsp
  obtain ⟨c,_,rfl⟩ := List.mem_map.mp hb
  have links : ∀ ws ∈ (selectOriented pf autos 0 (chartPicks c.val.picks) prev).map (rotatedSpec rd),
      Impossible T (cap-1) ws.toFinset := by
    intro ws hw
    obtain ⟨⟨p,spec⟩,hm,rfl⟩ := List.mem_map.mp hw
    obtain ⟨hp,hsp⟩ := selectOriented_mem hm
    exact rotate_excluded (hprev spec hsp) p (List.all_eq_true.mp ha p hp)
  exact nodeCheck_sound pairs baseF hs (buildTrie_sound links)
    (List.all_eq_true.mp c.property sp hc)

private theorem emptyLevelOK (rawD : List Decor) (T : Sig) (cap : Nat) : LevelOK rawD T cap [] :=
  fun _ h => False.elim (List.not_mem_nil h)

private theorem levelOK_append {rawD T cap a b}
    (ha : LevelOK rawD T cap a) (hb : LevelOK rawD T cap b) : LevelOK rawD T cap (a ++ b) := by
  intro sp hsp
  rcases List.mem_append.mp hsp with h | h
  · exact ha sp h
  · exact hb sp h

private theorem impossible_of_top {rawD T cap spec nodes raw}
    (hok : LevelOK rawD T cap nodes) (hm : spec ∈ nodes) (heq : sameWords (nodeSigs rawD spec) raw = true) :
    Impossible T cap raw.toFinset := by
  rw [← sameWords_sound heq]
  exact hok spec hm

private theorem lower_of_search_at {z o T cap rawD nodes spec xs}
    (hok : LevelOK rawD T cap nodes) (hm : spec ∈ nodes)
    (heq : sameWords (nodeSigs rawD spec) (freeVars z o) = true)
    (hp : properB T = true)
    (hess : checkEssential T (freeVars z o) xs = true)
    (hcov : (freeVars z o).all (fun a => (xs.map Prod.fst).contains a) = true) :
    Lower (freeVars z o) T (cap + 1) := by
  apply lower_impossible (proper_of _ hp) (essential_plain hess).1 (essential_plain hess).2
  · intro a ha
    have h1 := List.all_eq_true.mp hcov a ha
    simp only [List.contains_eq_mem, decide_eq_true_eq] at h1
    exact essential_ok hess a (List.mem_toFinset.mpr h1)
  · exact impossible_of_top hok hm heq

private theorem lower_of_search {z o cap rawD nodes spec xs}
    (hok : LevelOK rawD (subGoal z o) cap nodes) (hm : spec ∈ nodes)
    (heq : sameWords (nodeSigs rawD spec) (freeVars z o) = true)
    (hp : properB (subGoal z o) = true)
    (hess : checkEssential (subGoal z o) (freeVars z o) xs = true)
    (hcov : (freeVars z o).all (fun a => (xs.map Prod.fst).contains a) = true) :
    Lower (freeVars z o) (subGoal z o) (cap + 1) := by
  apply lower_impossible (proper_of _ hp) (essential_plain hess).1 (essential_plain hess).2
  · intro a ha
    have h1 := List.all_eq_true.mp hcov a ha
    simp only [List.contains_eq_mem, decide_eq_true_eq] at h1
    exact essential_ok hess a (List.mem_toFinset.mpr h1)
  · exact impossible_of_top hok hm heq

private theorem lower_count {raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower raw T ((xs.map Prod.fst).toFinset.card - 1) := by
  intro p bank hr hit
  obtain ⟨k, S, hk, run, sub⟩ := reach_live properT (essential_plain ok).1 (essential_plain ok).2 hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r, s, hd, iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := live_size run
  omega

private theorem impossible_of_size {T cap} {raw : List Sig} (nd : nodupB raw = true)
    (hlt : cap + 1 < raw.length) : Impossible T cap raw.toFinset := by
  intro k hk h
  have hsz := live_size h
  rw [List.toFinset_card_of_nodup (nodupB_sound nd)] at hsz
  omega

private theorem no_not_monotone (C : Circuit) (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hno : ∀ g ∈ C.gates, isNot g = false) : PEqualNP.MetaComplexity.Monotone2 C := by
  intro g hg
  obtain ⟨hop, hlen⟩ := hfan g hg
  refine ⟨?_, hlen⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
  rcases hop with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · have hn := hno g hg
    simp [isNot, h] at hn

private theorem circuit_with_not_impossible (root_imp : Impossible target 11 inputs.toFinset)
    (root_ess : ∀ a ∈ inputs, Essential target inputs a)
    (C : Circuit) (hfan : PEqualNP.MetaComplexity.FanInTwo C) (hsz : C.size ≤ 12)
    (heval : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = targetFun x)
    (hhas : ¬∀ g ∈ C.gates, isNot g = false) : False := by
  have goalEq : (execute C.gates inputs).getD C.output zero = target := by
    apply bit_ext; intro r
    exact (table_eval C hfan C.output r).trans ((heval (sample r)).trans (target_table r).symm)
  have hp : proper target := proper_of target (by decide +kernel)
  have pt : bit 0 target = false := by decide +kernel
  have out := get_rep (execute C.gates inputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  rw [nrm_id pt] at out
  have targetIn := out.resolve_right (fun hn => hn hp)
  obtain ⟨k, S, hk, run, hs⟩ := extract C.gates inputs hfan hp targetIn
  have ni : inputs.all plainWord = true := by decide +kernel
  rw [nrm_map ni] at hs
  have hlt : C.gates.countP (fun g => !isNot g) < C.gates.length := by
    rcases Nat.lt_or_ge (C.gates.countP (fun g => !isNot g)) C.gates.length with h | h
    · exact h
    · exfalso; apply hhas; intro g hg
      have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
      simpa using eq
  have hlen : C.gates.length ≤ 12 := hsz
  have hS : inputs.toFinset = S := by
    ext a; rw [List.mem_toFinset]
    refine ⟨fun hm => ?_, hs a⟩
    obtain ⟨r, s, hd, iso⟩ := root_ess a hm
    exact raw_required run inputs a hs r s hd iso
  exact root_imp k (by omega) (hS.symm ▸ run)

private def essentialRows : List (Sig × Row × Row) :=
  [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 9, 13), (inputs.getD 3 zero, 5, 13), (inputs.getD 4 zero, 9, 25), (inputs.getD 5 zero, 6, 38)]

private theorem root_ess : ∀ a ∈ inputs, Essential target inputs a := by
  have h : checkEssential target inputs essentialRows = true := by decide +kernel
  have hc : inputs.all (fun a => (essentialRows.map Prod.fst).contains a) = true :=
    by decide +kernel
  intro a ha
  have h1 := List.all_eq_true.mp hc a ha
  simp only [List.contains_eq_mem, decide_eq_true_eq] at h1
  exact essential_ok h a (List.mem_toFinset.mpr h1)

theorem main_from_root (root_imp : Impossible target 11 inputs.toFinset) :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 targetFun s →
      ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧
        ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = targetFun x := by
  intro s ⟨C, hfan, hsz, heval⟩
  by_cases hs : 13 ≤ s
  · exact PEqualNP.Outside.L_meta_42084_aux.Upper.bounded_replacement hs
  · by_cases hno : ∀ g ∈ C.gates, isNot g = false
    · exact ⟨C, no_not_monotone C hfan hno, hsz, heval⟩
    · exact False.elim (circuit_with_not_impossible root_imp root_ess C hfan (by omega) heval hno)

private def decodeRows (tape : Nat) (r : Row) : Row :=
  Fin.ofNat 64 (tape >>> (6 * r.val))

private def signedFreeWord (roots : List Sig) (w : Sig) : Bool :=
  freeWord roots w || freeWord roots (neg w)

private theorem signedFreeWord_ok {roots w}
    (h : signedFreeWord roots w = true) :
    Available (roots.map observe) (observe w) := by
  simp only [signedFreeWord, Bool.or_eq_true] at h
  rcases h with h | h
  · exact freeWord_ok h
  · have h' := avail_inv (freeWord_ok h)
    rw [obs_neg, inv_inv'] at h'
    exact h'

private def signedSliceOK (f : Row → Row) (raw : List Sig) (T d : Sig)
    (base : List Sig) (G : Sig) : Bool :=
  (rename f d == one) && sameUpToNeg (rename f T) G &&
    raw.all (fun a => signedFreeWord base (rename f a))

private theorem signedSliceOf {f raw T d base G L}
    (ok : signedSliceOK f raw T d base G = true)
    (pG : proper G) (lower : Lower base G L) : Slice raw T d L := by
  simp only [signedSliceOK, sameUpToNeg, Bool.and_eq_true, Bool.or_eq_true,
    beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨nc, imp⟩ := restrict_of_sameUpToNeg ok.1.2 pG
  refine ⟨f,base,?_,?_,nc,?_⟩
  · intro r
    rw [← bit_rename, ok.1.1, bit_one]
  · intro a ha
    rw [← observe_rename]
    exact signedFreeWord_ok (ok.2 a ha)
  · intro p bank hr h
    exact lower p bank hr (imp bank h)

private theorem signedLowerOf {f raw T base G L}
    (ok : signedSliceOK f raw T one base G = true)
    (pT : proper T) (nT : plainWord T = true) (nR : raw.all plainWord = true)
    (pG : proper G) (lower : Lower base G L) : Lower raw T L := by
  simp only [signedSliceOK, sameUpToNeg, Bool.and_eq_true, Bool.or_eq_true,
    beq_iff_eq, List.all_eq_true] at ok
  simpa using lower_slice pT nT nR pG f ok.1.2
    (fun a ha => signedFreeWord_ok (ok.2 a ha)) ∅ (by simp) (by simp) L lower

namespace D2

private def childGoal (z o : Nat) : Sig :=
  nrm (movedWord (fixRows z o) 0xfa50fa50a000a000)

section Cube18_8

private def p_18_8 : Nat → Bits
  | 0 => mk128 0xbecfbecfbecfbecf 0xbecfbecfbecfbecf
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0xdf73df73df73df73 0xdf73df73df73df73
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0x0 0x0
  | 5 => mk128 0xefbcefbcefbcefbc 0xefbcefbcefbcefbc
  | _ => 0
private def q_18_8 : Nat → Bits
  | 0 => mk128 0x4205420542054205 0x4205420542054205
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0x2412241224122412 0x2412241224122412
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0x0 0x0
  | 5 => mk128 0x1828182818281828 0x1828182818281828
  | _ => 0
private theorem pp_18_8 : properPairs (childGoal 18 8) (asRow p_18_8) (asRow q_18_8) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_18_8 : List Decor := rawDecor (freeMask 18 8) p_18_8 q_18_8
private def sl_18_8 : List (Sig × Nat) := []
set_option maxHeartbeats 0 in
private theorem sl_18_8_ok : ∀ s ∈ sl_18_8, Slice (freeVars 18 8) (childGoal 18 8) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private noncomputable def lv_18_8_3_0 : List NodeSpec := [([], [0, 1, 2], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_18_8_3_0 : LevelOK rd_18_8 (childGoal 18 8) 3 lv_18_8_3_0 :=
  levelCheck_sound pp_18_8 (raw_faithful _ _ _) sl_18_8_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_18_8 (childGoal 18 8) 2)
    (by decide +kernel : levelCheck (freeVars 18 8) rd_18_8 (childGoal 18 8) sl_18_8 [[]] [] 3 lv_18_8_3_0 = true)
private noncomputable def lv_18_8_3 : List NodeSpec := lv_18_8_3_0
private theorem ok_18_8_3 : LevelOK rd_18_8 (childGoal 18 8) 3 lv_18_8_3 := ok_18_8_3_0
set_option maxHeartbeats 0 in
private theorem lower_18_8 : Lower (freeVars 18 8) (childGoal 18 8) 4 :=
  lower_of_search_at (z := 18) (o := 8) (T := childGoal 18 8) (xs := [(inputs.getD 0 zero, 4, 5), (inputs.getD 2 zero, 1, 5), (inputs.getD 5 zero, 1, 33)]) ok_18_8_3 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube18_8

section Cube18_4

private def p_18_4 : Nat → Bits
  | 0 => mk128 0xb0e3b0e3b0e3b0e3 0xb0e3b0e3b0e3b0e3
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 3 => mk128 0xfcf3fcf3fcf3fcf3 0xfcf3fcf3fcf3fcf3
  | 4 => mk128 0x0 0x0
  | 5 => mk128 0xff3cff3cff3cff3c 0xff3cff3cff3cff3c
  | _ => 0
private def q_18_4 : Nat → Bits
  | 0 => mk128 0x59a959a959a959a9 0x59a959a959a959a9
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 3 => mk128 0x2212221222122212 0x2212221222122212
  | 4 => mk128 0x0 0x0
  | 5 => mk128 0x8a808a808a808a8 0x8a808a808a808a8
  | _ => 0
private theorem pp_18_4 : properPairs (childGoal 18 4) (asRow p_18_4) (asRow q_18_4) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_18_4 : List Decor := rawDecor (freeMask 18 4) p_18_4 q_18_4
private def sl_18_4 : List (Sig × Nat) := []
set_option maxHeartbeats 0 in
private theorem sl_18_4_ok : ∀ s ∈ sl_18_4, Slice (freeVars 18 4) (childGoal 18 4) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private noncomputable def lv_18_4_2_0 : List NodeSpec := [([], [0, 1, 2], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_18_4_2_0 : LevelOK rd_18_4 (childGoal 18 4) 2 lv_18_4_2_0 :=
  levelCheck_sound pp_18_4 (raw_faithful _ _ _) sl_18_4_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_18_4 (childGoal 18 4) 1)
    (by decide +kernel : levelCheck (freeVars 18 4) rd_18_4 (childGoal 18 4) sl_18_4 [[]] [] 2 lv_18_4_2_0 = true)
private noncomputable def lv_18_4_2 : List NodeSpec := lv_18_4_2_0
private theorem ok_18_4_2 : LevelOK rd_18_4 (childGoal 18 4) 2 lv_18_4_2 := ok_18_4_2_0
set_option maxHeartbeats 0 in
private theorem lower_18_4 : Lower (freeVars 18 4) (childGoal 18 4) 3 :=
  lower_of_search_at (z := 18) (o := 4) (T := childGoal 18 4) (xs := [(inputs.getD 0 zero, 8, 9), (inputs.getD 3 zero, 1, 9), (inputs.getD 5 zero, 0, 32)]) ok_18_4_2 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube18_4

section Cube18_32

private def p_18_32 : Nat → Bits
  | 0 => mk128 0xb32cb32cb32cb32c 0xb32cb32cb32cb32c
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0xfcf3fcf3fcf3fcf3 0xfcf3fcf3fcf3fcf3
  | 3 => mk128 0xff3cff3cff3cff3c 0xff3cff3cff3cff3c
  | 4 => mk128 0x0 0x0
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private def q_18_32 : Nat → Bits
  | 0 => mk128 0x5a665a665a665a66 0x5a665a665a665a66
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0xa220a220a220a22 0xa220a220a220a22
  | 3 => mk128 0x2098209820982098 0x2098209820982098
  | 4 => mk128 0x0 0x0
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private theorem pp_18_32 : properPairs (childGoal 18 32) (asRow p_18_32) (asRow q_18_32) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_18_32 : List Decor := rawDecor (freeMask 18 32) p_18_32 q_18_32
private def sl_18_32 : List (Sig × Nat) := []
set_option maxHeartbeats 0 in
private theorem sl_18_32_ok : ∀ s ∈ sl_18_32, Slice (freeVars 18 32) (childGoal 18 32) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private noncomputable def lv_18_32_2_0 : List NodeSpec := [([], [0, 1, 2], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_18_32_2_0 : LevelOK rd_18_32 (childGoal 18 32) 2 lv_18_32_2_0 :=
  levelCheck_sound pp_18_32 (raw_faithful _ _ _) sl_18_32_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_18_32 (childGoal 18 32) 1)
    (by decide +kernel : levelCheck (freeVars 18 32) rd_18_32 (childGoal 18 32) sl_18_32 [[]] [] 2 lv_18_32_2_0 = true)
private noncomputable def lv_18_32_2 : List NodeSpec := lv_18_32_2_0
private theorem ok_18_32_2 : LevelOK rd_18_32 (childGoal 18 32) 2 lv_18_32_2 := ok_18_32_2_0
set_option maxHeartbeats 0 in
private theorem lower_18_32 : Lower (freeVars 18 32) (childGoal 18 32) 3 :=
  lower_of_search_at (z := 18) (o := 32) (T := childGoal 18 32) (xs := [(inputs.getD 0 zero, 4, 5), (inputs.getD 2 zero, 0, 4), (inputs.getD 3 zero, 1, 9)]) ok_18_32_2 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube18_32

section Cube18_0

private def p_18_0 : Nat → Bits
  | 0 => mk128 0x3e71ebe1cff0f07c 0xe3d7c39fe1e0f9c7
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0xff8ff7fe3fff0fff 0x1feffc7ffe1ffe3f
  | 3 => mk128 0x3ff1fbffcffff07f 0xe3f7ff9fffe0ffc7
  | 4 => mk128 0x0 0x0
  | 5 => mk128 0xc3fe3dfff1ffff87 0xfc7bffe3ffff0ff8
  | _ => 0
private def q_18_0 : Nat → Bits
  | 0 => mk128 0xa638d43c94b8954c 0x71a87929712a98e3
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0xaa8b484580598355 0x16908b00b306aa2d
  | 3 => mk128 0x11d1848929622a23 0xa3091252c4544746
  | 4 => mk128 0x0 0x0
  | 5 => mk128 0x236c03100d8ccc46 0xd806201b19988db0
  | _ => 0
private theorem pp_18_0 : properPairs (childGoal 18 0) (asRow p_18_0) (asRow q_18_0) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_18_0 : List Decor := rawDecor (freeMask 18 0) p_18_0 q_18_0
private def sl_18_0 : List (Sig × Nat) := [(subcube 18 8, 4), (subcube 18 4, 3), (subcube 18 32, 3)]
set_option maxHeartbeats 0 in
private theorem sl_18_0_ok : ∀ s ∈ sl_18_0, Slice (freeVars 18 0) (childGoal 18 0) s.1 s.2 := by
  intro s hs
  simp only [sl_18_0, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact slice_correct (ms := fixRows 18 8) (base := freeVars 18 8) (G := childGoal 18 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_18_8
  · exact slice_correct (ms := fixRows 18 4) (base := freeVars 18 4) (G := childGoal 18 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_18_4
  · exact slice_correct (ms := fixRows 18 32) (base := freeVars 18 32) (G := childGoal 18 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_18_32
private noncomputable def lv_18_0_2_0 : List NodeSpec := [([(0, 1, 0), (0, 2, 0), (2, 3, 4)], [6, 5, 1], []), ([(0, 2, 0), (0, 3, 0), (2, 1, 5)], [6, 4, 3], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_18_0_2_0 : LevelOK rd_18_0 (childGoal 18 0) 2 lv_18_0_2_0 :=
  levelCheck_sound pp_18_0 (raw_faithful _ _ _) sl_18_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_18_0 (childGoal 18 0) 1)
    (by decide +kernel : levelCheck (freeVars 18 0) rd_18_0 (childGoal 18 0) sl_18_0 [[]] [] 2 lv_18_0_2_0 = true)
private noncomputable def lv_18_0_2 : List NodeSpec := lv_18_0_2_0
private theorem ok_18_0_2 : LevelOK rd_18_0 (childGoal 18 0) 2 lv_18_0_2 := ok_18_0_2_0
private noncomputable def lv_18_0_3_0 : List NodeSpec := [([(0, 1, 0), (0, 2, 0)], [4, 5, 1, 3], []), ([(0, 1, 0), (2, 3, 4)], [5, 0, 1, 2], []), ([(2, 1, 0), (2, 2, 4)], [0, 5, 1, 3], []), ([(2, 1, 0), (0, 2, 0)], [4, 5, 1, 3], []), ([(0, 2, 0), (0, 3, 0)], [4, 5, 1, 3], []), ([(0, 2, 0), (2, 3, 0)], [5, 4, 1, 3], []), ([(0, 3, 0), (2, 1, 4)], [5, 0, 2, 3], []), ([(2, 3, 0), (2, 2, 4)], [5, 0, 1, 3], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_18_0_3_0 : LevelOK rd_18_0 (childGoal 18 0) 3 lv_18_0_3_0 :=
  levelCheck_sound pp_18_0 (raw_faithful _ _ _) sl_18_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) ok_18_0_2
    (by decide +kernel : levelCheck (freeVars 18 0) rd_18_0 (childGoal 18 0) sl_18_0 [[]] lv_18_0_2 3 lv_18_0_3_0 = true)
private noncomputable def lv_18_0_3 : List NodeSpec := lv_18_0_3_0
private theorem ok_18_0_3 : LevelOK rd_18_0 (childGoal 18 0) 3 lv_18_0_3 := ok_18_0_3_0
private noncomputable def lv_18_0_4_0 : List NodeSpec := [([(0, 1, 0)], [4, 0, 1, 2, 3], [(2, [])]), ([(2, 1, 0)], [4, 0, 1, 2, 3], [(0, [])]), ([(0, 2, 0)], [4, 0, 1, 3], [(0, [])]), ([(0, 3, 0)], [4, 0, 1, 2, 3], [(1, [])]), ([(2, 3, 0)], [4, 0, 1, 2, 3], [(0, [])]), ([(0, 3, 1)], [0, 4, 1, 2, 3], [(1, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_18_0_4_0 : LevelOK rd_18_0 (childGoal 18 0) 4 lv_18_0_4_0 :=
  levelCheck_sound pp_18_0 (raw_faithful _ _ _) sl_18_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) ok_18_0_3
    (by decide +kernel : levelCheck (freeVars 18 0) rd_18_0 (childGoal 18 0) sl_18_0 [[]] lv_18_0_3 4 lv_18_0_4_0 = true)
private noncomputable def lv_18_0_4 : List NodeSpec := lv_18_0_4_0
private theorem ok_18_0_4 : LevelOK rd_18_0 (childGoal 18 0) 4 lv_18_0_4 := ok_18_0_4_0
private noncomputable def lv_18_0_5_0 : List NodeSpec := [([], [0, 1, 2, 3], [(0, []), (1, []), (2, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_18_0_5_0 : LevelOK rd_18_0 (childGoal 18 0) 5 lv_18_0_5_0 :=
  levelCheck_sound pp_18_0 (raw_faithful _ _ _) sl_18_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) ok_18_0_4
    (by decide +kernel : levelCheck (freeVars 18 0) rd_18_0 (childGoal 18 0) sl_18_0 [[]] lv_18_0_4 5 lv_18_0_5_0 = true)
private noncomputable def lv_18_0_5 : List NodeSpec := lv_18_0_5_0
private theorem ok_18_0_5 : LevelOK rd_18_0 (childGoal 18 0) 5 lv_18_0_5 := ok_18_0_5_0
set_option maxHeartbeats 0 in
private theorem lower_18_0 : Lower (freeVars 18 0) (childGoal 18 0) 6 :=
  lower_of_search_at (z := 18) (o := 0) (T := childGoal 18 0) (xs := [(inputs.getD 0 zero, 12, 13), (inputs.getD 2 zero, 9, 13), (inputs.getD 3 zero, 5, 13), (inputs.getD 5 zero, 4, 36)]) ok_18_0_5 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube18_0

end D2

namespace D3

private def childGoal (z o : Nat) : Sig :=
  nrm (movedWord (fixRows z o) 0xfefee8e8fefee8e8)

section Cube41_0

private def p_41_0 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0xbecfbecfbecfbecf 0xbecfbecfbecfbecf
  | 2 => mk128 0xdf73df73df73df73 0xdf73df73df73df73
  | 3 => mk128 0x0 0x0
  | 4 => mk128 0xefbcefbcefbcefbc 0xefbcefbcefbcefbc
  | 5 => mk128 0x0 0x0
  | _ => 0
private def q_41_0 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0x4205420542054205 0x4205420542054205
  | 2 => mk128 0x2412241224122412 0x2412241224122412
  | 3 => mk128 0x0 0x0
  | 4 => mk128 0x1828182818281828 0x1828182818281828
  | 5 => mk128 0x0 0x0
  | _ => 0
private theorem pp_41_0 : properPairs (childGoal 41 0) (asRow p_41_0) (asRow q_41_0) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_41_0 : List Decor := rawDecor (freeMask 41 0) p_41_0 q_41_0
private def sl_41_0 : List (Sig × Nat) := []
set_option maxHeartbeats 0 in
private theorem sl_41_0_ok : ∀ s ∈ sl_41_0, Slice (freeVars 41 0) (childGoal 41 0) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private noncomputable def lv_41_0_3_0 : List NodeSpec := [([], [0, 1, 2], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_41_0_3_0 : LevelOK rd_41_0 (childGoal 41 0) 3 lv_41_0_3_0 :=
  levelCheck_sound pp_41_0 (raw_faithful _ _ _) sl_41_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_41_0 (childGoal 41 0) 2)
    (by decide +kernel : levelCheck (freeVars 41 0) rd_41_0 (childGoal 41 0) sl_41_0 [[]] [] 3 lv_41_0_3_0 = true)
private noncomputable def lv_41_0_3 : List NodeSpec := lv_41_0_3_0
private theorem ok_41_0_3 : LevelOK rd_41_0 (childGoal 41 0) 3 lv_41_0_3 := ok_41_0_3_0
set_option maxHeartbeats 0 in
private theorem lower_41_0 : Lower (freeVars 41 0) (childGoal 41 0) 4 :=
  lower_of_search_at (z := 41) (o := 0) (T := childGoal 41 0) (xs := [(inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 4 zero, 2, 18)]) ok_41_0_3 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube41_0

section Cube42_0

private def p_42_0 : Nat → Bits
  | 0 => mk128 0xbecfbecfbecfbecf 0xbecfbecfbecfbecf
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0xdf73df73df73df73 0xdf73df73df73df73
  | 3 => mk128 0x0 0x0
  | 4 => mk128 0xefbcefbcefbcefbc 0xefbcefbcefbcefbc
  | 5 => mk128 0x0 0x0
  | _ => 0
private def q_42_0 : Nat → Bits
  | 0 => mk128 0x4205420542054205 0x4205420542054205
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0x2412241224122412 0x2412241224122412
  | 3 => mk128 0x0 0x0
  | 4 => mk128 0x1828182818281828 0x1828182818281828
  | 5 => mk128 0x0 0x0
  | _ => 0
private theorem pp_42_0 : properPairs (childGoal 42 0) (asRow p_42_0) (asRow q_42_0) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_42_0 : List Decor := rawDecor (freeMask 42 0) p_42_0 q_42_0
private def sl_42_0 : List (Sig × Nat) := []
set_option maxHeartbeats 0 in
private theorem sl_42_0_ok : ∀ s ∈ sl_42_0, Slice (freeVars 42 0) (childGoal 42 0) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private noncomputable def lv_42_0_3_0 : List NodeSpec := [([], [0, 1, 2], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_42_0_3_0 : LevelOK rd_42_0 (childGoal 42 0) 3 lv_42_0_3_0 :=
  levelCheck_sound pp_42_0 (raw_faithful _ _ _) sl_42_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_42_0 (childGoal 42 0) 2)
    (by decide +kernel : levelCheck (freeVars 42 0) rd_42_0 (childGoal 42 0) sl_42_0 [[]] [] 3 lv_42_0_3_0 = true)
private noncomputable def lv_42_0_3 : List NodeSpec := lv_42_0_3_0
private theorem ok_42_0_3 : LevelOK rd_42_0 (childGoal 42 0) 3 lv_42_0_3 := ok_42_0_3_0
set_option maxHeartbeats 0 in
private theorem lower_42_0 : Lower (freeVars 42 0) (childGoal 42 0) 4 :=
  lower_of_search_at (z := 42) (o := 0) (T := childGoal 42 0) (xs := [(inputs.getD 0 zero, 4, 5), (inputs.getD 2 zero, 1, 5), (inputs.getD 4 zero, 1, 17)]) ok_42_0_3 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube42_0

section Cube44_0

private def p_44_0 : Nat → Bits
  | 0 => mk128 0xbecfbecfbecfbecf 0xbecfbecfbecfbecf
  | 1 => mk128 0xdf73df73df73df73 0xdf73df73df73df73
  | 2 => mk128 0x0 0x0
  | 3 => mk128 0x0 0x0
  | 4 => mk128 0xefbcefbcefbcefbc 0xefbcefbcefbcefbc
  | 5 => mk128 0x0 0x0
  | _ => 0
private def q_44_0 : Nat → Bits
  | 0 => mk128 0x4205420542054205 0x4205420542054205
  | 1 => mk128 0x2412241224122412 0x2412241224122412
  | 2 => mk128 0x0 0x0
  | 3 => mk128 0x0 0x0
  | 4 => mk128 0x1828182818281828 0x1828182818281828
  | 5 => mk128 0x0 0x0
  | _ => 0
private theorem pp_44_0 : properPairs (childGoal 44 0) (asRow p_44_0) (asRow q_44_0) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_44_0 : List Decor := rawDecor (freeMask 44 0) p_44_0 q_44_0
private def sl_44_0 : List (Sig × Nat) := []
set_option maxHeartbeats 0 in
private theorem sl_44_0_ok : ∀ s ∈ sl_44_0, Slice (freeVars 44 0) (childGoal 44 0) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private noncomputable def lv_44_0_3_0 : List NodeSpec := [([], [0, 1, 2], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_44_0_3_0 : LevelOK rd_44_0 (childGoal 44 0) 3 lv_44_0_3_0 :=
  levelCheck_sound pp_44_0 (raw_faithful _ _ _) sl_44_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_44_0 (childGoal 44 0) 2)
    (by decide +kernel : levelCheck (freeVars 44 0) rd_44_0 (childGoal 44 0) sl_44_0 [[]] [] 3 lv_44_0_3_0 = true)
private noncomputable def lv_44_0_3 : List NodeSpec := lv_44_0_3_0
private theorem ok_44_0_3 : LevelOK rd_44_0 (childGoal 44 0) 3 lv_44_0_3 := ok_44_0_3_0
set_option maxHeartbeats 0 in
private theorem lower_44_0 : Lower (freeVars 44 0) (childGoal 44 0) 4 :=
  lower_of_search_at (z := 44) (o := 0) (T := childGoal 44 0) (xs := [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 4 zero, 1, 17)]) ok_44_0_3 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube44_0

section Cube56_0

private def p_56_0 : Nat → Bits
  | 0 => mk128 0xbecfbecfbecfbecf 0xbecfbecfbecfbecf
  | 1 => mk128 0xdf73df73df73df73 0xdf73df73df73df73
  | 2 => mk128 0xefbcefbcefbcefbc 0xefbcefbcefbcefbc
  | 3 => mk128 0x0 0x0
  | 4 => mk128 0x0 0x0
  | 5 => mk128 0x0 0x0
  | _ => 0
private def q_56_0 : Nat → Bits
  | 0 => mk128 0x4205420542054205 0x4205420542054205
  | 1 => mk128 0x2412241224122412 0x2412241224122412
  | 2 => mk128 0x1828182818281828 0x1828182818281828
  | 3 => mk128 0x0 0x0
  | 4 => mk128 0x0 0x0
  | 5 => mk128 0x0 0x0
  | _ => 0
private theorem pp_56_0 : properPairs (childGoal 56 0) (asRow p_56_0) (asRow q_56_0) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_56_0 : List Decor := rawDecor (freeMask 56 0) p_56_0 q_56_0
private def sl_56_0 : List (Sig × Nat) := []
set_option maxHeartbeats 0 in
private theorem sl_56_0_ok : ∀ s ∈ sl_56_0, Slice (freeVars 56 0) (childGoal 56 0) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private noncomputable def lv_56_0_3_0 : List NodeSpec := [([], [0, 1, 2], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_56_0_3_0 : LevelOK rd_56_0 (childGoal 56 0) 3 lv_56_0_3_0 :=
  levelCheck_sound pp_56_0 (raw_faithful _ _ _) sl_56_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_56_0 (childGoal 56 0) 2)
    (by decide +kernel : levelCheck (freeVars 56 0) rd_56_0 (childGoal 56 0) sl_56_0 [[]] [] 3 lv_56_0_3_0 = true)
private noncomputable def lv_56_0_3 : List NodeSpec := lv_56_0_3_0
private theorem ok_56_0_3 : LevelOK rd_56_0 (childGoal 56 0) 3 lv_56_0_3 := ok_56_0_3_0
set_option maxHeartbeats 0 in
private theorem lower_56_0 : Lower (freeVars 56 0) (childGoal 56 0) 4 :=
  lower_of_search_at (z := 56) (o := 0) (T := childGoal 56 0) (xs := [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 1, 5)]) ok_56_0_3 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube56_0

section Cube40_0

private def p_40_0 : Nat → Bits
  | 0 => mk128 0xec33efe939e3bbd8 0x67dfd273c777b0cf
  | 1 => mk128 0xf4ccf7f1ce7c3de9 0x99efe39cf87bd333
  | 2 => mk128 0xfb0f3bfe0f9fc1f6 0x1e77fc1f3f83ec3c
  | 3 => mk128 0x0 0x0
  | 4 => mk128 0x3f03dfff01ffe07 0xe07bffe03ffc0fc0
  | 5 => mk128 0x0 0x0
  | _ => 0
private def q_40_0 : Nat → Bits
  | 0 => mk128 0x2011502242008840 0x22a0448401108045
  | 1 => mk128 0x4044884410841080 0x8910882108210112
  | 2 => mk128 0x810a0480a0290102 0x1409014052020428
  | 3 => mk128 0x0 0x0
  | 4 => mk128 0x2a0030005522005 0x4006000aa4400a80
  | 5 => mk128 0x0 0x0
  | _ => 0
private theorem pp_40_0 : properPairs (childGoal 40 0) (asRow p_40_0) (asRow q_40_0) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_40_0 : List Decor := rawDecor (freeMask 40 0) p_40_0 q_40_0
private def sl_40_0 : List (Sig × Nat) := [(subcube 41 0, 4), (subcube 42 0, 4), (subcube 44 0, 4), (subcube 56 0, 4)]
set_option maxHeartbeats 0 in
private theorem sl_40_0_ok : ∀ s ∈ sl_40_0, Slice (freeVars 40 0) (childGoal 40 0) s.1 s.2 := by
  intro s hs
  simp only [sl_40_0, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact slice_correct (ms := fixRows 41 0) (base := freeVars 41 0) (G := childGoal 41 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_41_0
  · exact slice_correct (ms := fixRows 42 0) (base := freeVars 42 0) (G := childGoal 42 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_42_0
  · exact slice_correct (ms := fixRows 44 0) (base := freeVars 44 0) (G := childGoal 44 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_44_0
  · exact slice_correct (ms := fixRows 56 0) (base := freeVars 56 0) (G := childGoal 56 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_56_0
private noncomputable def lv_40_0_3_0 : List NodeSpec := [([(1, 1, 0), (1, 2, 0), (1, 2, 1)], [4, 5, 6, 3], [(0, []), (1, [])]), ([(1, 1, 0), (1, 2, 4), (3, 3, 5)], [6, 0, 1, 2], []), ([(1, 1, 0), (1, 3, 0), (1, 3, 1)], [4, 2, 5, 6], [(0, []), (1, [])]), ([(1, 1, 0), (1, 3, 4), (2, 5, 2)], [6, 0, 1, 3], []), ([(1, 2, 0), (1, 3, 0), (1, 3, 2)], [1, 4, 5, 6], [(0, []), (2, [])]), ([(1, 2, 0), (1, 3, 4), (2, 5, 1)], [6, 0, 2, 3], []), ([(1, 2, 1), (1, 3, 1), (1, 3, 2)], [0, 4, 5, 6], [(1, []), (2, [])]), ([(1, 2, 1), (1, 3, 4), (2, 5, 0)], [6, 1, 2, 3], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_40_0_3_0 : LevelOK rd_40_0 (childGoal 40 0) 3 lv_40_0_3_0 :=
  levelCheck_sound pp_40_0 (raw_faithful _ _ _) sl_40_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_40_0 (childGoal 40 0) 2)
    (by decide +kernel : levelCheck (freeVars 40 0) rd_40_0 (childGoal 40 0) sl_40_0 [[]] [] 3 lv_40_0_3_0 = true)
private noncomputable def lv_40_0_3 : List NodeSpec := lv_40_0_3_0
private theorem ok_40_0_3 : LevelOK rd_40_0 (childGoal 40 0) 3 lv_40_0_3 := ok_40_0_3_0
private noncomputable def lv_40_0_4_0 : List NodeSpec := [([(1, 1, 0), (1, 2, 0)], [1, 4, 2, 5, 3], [(1, []), (2, [])]), ([(1, 1, 0), (1, 2, 1)], [0, 4, 2, 5, 3], [(0, []), (2, [])]), ([(1, 1, 0), (1, 2, 4)], [0, 1, 2, 5, 3], [(3, [])]), ([(1, 1, 0), (3, 2, 4)], [5, 0, 1, 2, 3], []), ([(1, 1, 0), (1, 3, 0)], [1, 4, 2, 3, 5], [(1, []), (3, [])]), ([(1, 1, 0), (1, 3, 1)], [0, 4, 2, 3, 5], [(0, []), (3, [])]), ([(1, 1, 0), (1, 3, 4)], [0, 1, 2, 3, 5], [(2, [])]), ([(1, 1, 0), (3, 3, 4)], [5, 0, 1, 2, 3], []), ([(1, 2, 0), (1, 2, 1)], [0, 1, 4, 5, 3], [(0, []), (1, [])]), ([(1, 2, 0), (2, 4, 1)], [5, 0, 1, 2, 3], []), ([(1, 2, 0), (1, 3, 0)], [1, 2, 4, 3, 5], [(2, []), (3, [])]), ([(1, 2, 0), (1, 3, 2)], [0, 1, 4, 3, 5], [(0, []), (3, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_40_0_4_0 : LevelOK rd_40_0 (childGoal 40 0) 4 lv_40_0_4_0 :=
  levelCheck_sound pp_40_0 (raw_faithful _ _ _) sl_40_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) ok_40_0_3
    (by decide +kernel : levelCheck (freeVars 40 0) rd_40_0 (childGoal 40 0) sl_40_0 [[]] lv_40_0_3 4 lv_40_0_4_0 = true)
private noncomputable def lv_40_0_4_1 : List NodeSpec := [([(1, 2, 0), (1, 3, 4)], [0, 1, 2, 3, 5], [(1, [])]), ([(1, 2, 0), (3, 3, 4)], [5, 0, 1, 2, 3], []), ([(1, 2, 1), (2, 4, 0)], [5, 0, 1, 2, 3], []), ([(1, 2, 1), (1, 3, 1)], [0, 2, 4, 3, 5], [(2, []), (3, [])]), ([(1, 2, 1), (1, 3, 2)], [0, 1, 4, 3, 5], [(1, []), (3, [])]), ([(1, 2, 1), (1, 3, 4)], [0, 1, 2, 3, 5], [(0, [])]), ([(1, 2, 1), (3, 3, 4)], [5, 0, 1, 2, 3], []), ([(1, 3, 0), (1, 3, 1)], [0, 1, 2, 4, 5], [(0, []), (1, [])]), ([(1, 3, 0), (1, 3, 2)], [0, 1, 2, 4, 5], [(0, []), (2, [])]), ([(1, 3, 0), (2, 4, 1)], [5, 0, 1, 2, 3], []), ([(1, 3, 0), (2, 4, 2)], [5, 0, 1, 2, 3], []), ([(1, 3, 1), (1, 3, 2)], [0, 1, 2, 4, 5], [(1, []), (2, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_40_0_4_1 : LevelOK rd_40_0 (childGoal 40 0) 4 lv_40_0_4_1 :=
  levelCheck_sound pp_40_0 (raw_faithful _ _ _) sl_40_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) ok_40_0_3
    (by decide +kernel : levelCheck (freeVars 40 0) rd_40_0 (childGoal 40 0) sl_40_0 [[]] lv_40_0_3 4 lv_40_0_4_1 = true)
private noncomputable def lv_40_0_4_2 : List NodeSpec := [([(1, 3, 1), (2, 4, 0)], [5, 0, 1, 2, 3], []), ([(1, 3, 1), (2, 4, 2)], [5, 0, 1, 2, 3], []), ([(1, 3, 2), (2, 4, 0)], [5, 0, 1, 2, 3], []), ([(1, 3, 2), (2, 4, 1)], [5, 0, 1, 2, 3], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_40_0_4_2 : LevelOK rd_40_0 (childGoal 40 0) 4 lv_40_0_4_2 :=
  levelCheck_sound pp_40_0 (raw_faithful _ _ _) sl_40_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) ok_40_0_3
    (by decide +kernel : levelCheck (freeVars 40 0) rd_40_0 (childGoal 40 0) sl_40_0 [[]] lv_40_0_3 4 lv_40_0_4_2 = true)
private noncomputable def lv_40_0_4 : List NodeSpec := (lv_40_0_4_0 ++ (lv_40_0_4_1 ++ lv_40_0_4_2))
private theorem ok_40_0_4 : LevelOK rd_40_0 (childGoal 40 0) 4 lv_40_0_4 := (levelOK_append ok_40_0_4_0 (levelOK_append ok_40_0_4_1 ok_40_0_4_2))
private noncomputable def lv_40_0_5_0 : List NodeSpec := [([(1, 1, 0)], [0, 1, 4, 2, 3], [(0, []), (1, []), (2, []), (3, [])]), ([(1, 2, 0)], [0, 1, 2, 4, 3], [(0, []), (1, []), (2, []), (3, [])]), ([(1, 2, 1)], [0, 1, 2, 4, 3], [(0, []), (1, []), (2, []), (3, [])]), ([(1, 3, 0)], [0, 1, 2, 3, 4], [(0, []), (1, []), (2, []), (3, [])]), ([(1, 3, 1)], [0, 1, 2, 3, 4], [(0, []), (1, []), (2, []), (3, [])]), ([(1, 3, 2)], [0, 1, 2, 3, 4], [(0, []), (1, []), (2, []), (3, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_40_0_5_0 : LevelOK rd_40_0 (childGoal 40 0) 5 lv_40_0_5_0 :=
  levelCheck_sound pp_40_0 (raw_faithful _ _ _) sl_40_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) ok_40_0_4
    (by decide +kernel : levelCheck (freeVars 40 0) rd_40_0 (childGoal 40 0) sl_40_0 [[]] lv_40_0_4 5 lv_40_0_5_0 = true)
private noncomputable def lv_40_0_5 : List NodeSpec := lv_40_0_5_0
private theorem ok_40_0_5 : LevelOK rd_40_0 (childGoal 40 0) 5 lv_40_0_5 := ok_40_0_5_0
private noncomputable def lv_40_0_6_0 : List NodeSpec := [([], [0, 1, 2, 3], [(0, []), (1, []), (2, []), (3, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_40_0_6_0 : LevelOK rd_40_0 (childGoal 40 0) 6 lv_40_0_6_0 :=
  levelCheck_sound pp_40_0 (raw_faithful _ _ _) sl_40_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) ok_40_0_5
    (by decide +kernel : levelCheck (freeVars 40 0) rd_40_0 (childGoal 40 0) sl_40_0 [[]] lv_40_0_5 6 lv_40_0_6_0 = true)
private noncomputable def lv_40_0_6 : List NodeSpec := lv_40_0_6_0
private theorem ok_40_0_6 : LevelOK rd_40_0 (childGoal 40 0) 6 lv_40_0_6 := ok_40_0_6_0
set_option maxHeartbeats 0 in
private theorem lower_40_0 : Lower (freeVars 40 0) (childGoal 40 0) 7 :=
  lower_of_search_at (z := 40) (o := 0) (T := childGoal 40 0) (xs := [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 1, 5), (inputs.getD 4 zero, 1, 17)]) ok_40_0_6 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube40_0

end D3

namespace D1

private def childGoal (z o : Nat) : Sig :=
  nrm (movedWord (fixRows z o) 0xfffafa50fa00a000)

set_option maxHeartbeats 0 in
private theorem lower_6_0 : Lower (freeVars 6 0) (childGoal 6 0) 7 :=
  signedLowerOf (f := decodeRows 0x1209411619001209411619821a29c31e39821a29c31e39001209411619001209411619821a29c31e39821a29c31e39) (by decide +kernel)
    (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    (proper_of _ (by decide +kernel)) D3.lower_40_0

set_option maxHeartbeats 0 in
private theorem lower_2_8 : Lower (freeVars 2 8) (childGoal 2 8) 7 :=
  signedLowerOf (f := decodeRows 0xf7ce78b6ca68f7ce78b6ca6875c65834c24875c65834c248f7ce78b6ca68f7ce78b6ca6875c65834c24875c65834c248) (by decide +kernel)
    (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    (proper_of _ (by decide +kernel)) D3.lower_40_0

set_option maxHeartbeats 0 in
private theorem lower_2_32 : Lower (freeVars 2 32) (childGoal 2 32) 6 :=
  signedLowerOf (f := decodeRows 0x821821a29a29925925b2db2d821821a29a29925925b2db2dc31c31e39e39d35d35f3df3dc31c31e39e39d35d35f3df3d) (by decide +kernel)
    (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    (proper_of _ (by decide +kernel)) D2.lower_18_0

set_option maxHeartbeats 0 in
private theorem lower_18_0 : Lower (freeVars 18 0) (childGoal 18 0) 6 :=
  signedLowerOf (f := decodeRows 0xb6cb6ca68a68964964860860b6cb6ca68a6896496486086034c34c24824814414404004034c34c248248144144040040) (by decide +kernel)
    (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    (proper_of _ (by decide +kernel)) D2.lower_18_0

section Cube6_1

private def p_6_1 : Nat → Bits
  | 0 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0x0 0x0
  | 3 => mk128 0xbecfbecfbecfbecf 0xbecfbecfbecfbecf
  | 4 => mk128 0xdf73df73df73df73 0xdf73df73df73df73
  | 5 => mk128 0xefbcefbcefbcefbc 0xefbcefbcefbcefbc
  | _ => 0
private def q_6_1 : Nat → Bits
  | 0 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0x0 0x0
  | 3 => mk128 0x4205420542054205 0x4205420542054205
  | 4 => mk128 0x2412241224122412 0x2412241224122412
  | 5 => mk128 0x1828182818281828 0x1828182818281828
  | _ => 0
private theorem pp_6_1 : properPairs (childGoal 6 1) (asRow p_6_1) (asRow q_6_1) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_6_1 : List Decor := rawDecor (freeMask 6 1) p_6_1 q_6_1
private def sl_6_1 : List (Sig × Nat) := []
set_option maxHeartbeats 0 in
private theorem sl_6_1_ok : ∀ s ∈ sl_6_1, Slice (freeVars 6 1) (childGoal 6 1) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private noncomputable def lv_6_1_3_0 : List NodeSpec := [([], [0, 1, 2], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_6_1_3_0 : LevelOK rd_6_1 (childGoal 6 1) 3 lv_6_1_3_0 :=
  levelCheck_sound pp_6_1 (raw_faithful _ _ _) sl_6_1_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_6_1 (childGoal 6 1) 2)
    (by decide +kernel : levelCheck (freeVars 6 1) rd_6_1 (childGoal 6 1) sl_6_1 [[]] [] 3 lv_6_1_3_0 = true)
private noncomputable def lv_6_1_3 : List NodeSpec := lv_6_1_3_0
private theorem ok_6_1_3 : LevelOK rd_6_1 (childGoal 6 1) 3 lv_6_1_3 := ok_6_1_3_0
set_option maxHeartbeats 0 in
private theorem lower_6_1 : Lower (freeVars 6 1) (childGoal 6 1) 4 :=
  lower_of_search_at (z := 6) (o := 1) (T := childGoal 6 1) (xs := [(inputs.getD 3 zero, 16, 24), (inputs.getD 4 zero, 8, 24), (inputs.getD 5 zero, 8, 40)]) ok_6_1_3 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube6_1

section Cube2_1

private def p_2_1 : Nat → Bits
  | 0 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0xed78999e38e73e49 0xdaf1333c71ce7c93
  | 3 => mk128 0xf7ff1fffc0fff87f 0xeffe3fff81fff0ff
  | 4 => mk128 0x39ffe1e7ff07c78e 0x73ffc3cffe0f8f1c
  | 5 => mk128 0x3e7ffe07fff807f0 0x7cfffc0ffff00fe0
  | _ => 0
private def q_2_1 : Nat → Bits
  | 0 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0x528e33260e31b648 0xa51c664c1c636c91
  | 3 => mk128 0x8810400040420013 0x1020800080840026
  | 4 => mk128 0x622140a9204928c 0xc44281524092518
  | 5 => mk128 0x1c4015524902560 0x38802aa49204ac0
  | _ => 0
private theorem pp_2_1 : properPairs (childGoal 2 1) (asRow p_2_1) (asRow q_2_1) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_2_1 : List Decor := rawDecor (freeMask 2 1) p_2_1 q_2_1
private def sl_2_1 : List (Sig × Nat) := [(subcube 6 1, 4)]
set_option maxHeartbeats 0 in
private theorem sl_2_1_ok : ∀ s ∈ sl_2_1, Slice (freeVars 2 1) (childGoal 2 1) s.1 s.2 := by
  intro s hs
  simp only [sl_2_1, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 6 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_6_1
private noncomputable def lv_2_1_4_0 : List NodeSpec := [([], [0, 1, 2, 3], [(0, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_2_1_4_0 : LevelOK rd_2_1 (childGoal 2 1) 4 lv_2_1_4_0 :=
  levelCheck_sound pp_2_1 (raw_faithful _ _ _) sl_2_1_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_2_1 (childGoal 2 1) 3)
    (by decide +kernel : levelCheck (freeVars 2 1) rd_2_1 (childGoal 2 1) sl_2_1 [[]] [] 4 lv_2_1_4_0 = true)
private noncomputable def lv_2_1_4 : List NodeSpec := lv_2_1_4_0
private theorem ok_2_1_4 : LevelOK rd_2_1 (childGoal 2 1) 4 lv_2_1_4 := ok_2_1_4_0
set_option maxHeartbeats 0 in
private theorem lower_2_1 : Lower (freeVars 2 1) (childGoal 2 1) 5 :=
  lower_of_search_at (z := 2) (o := 1) (T := childGoal 2 1) (xs := [(inputs.getD 2 zero, 8, 12), (inputs.getD 3 zero, 4, 12), (inputs.getD 4 zero, 8, 24), (inputs.getD 5 zero, 8, 40)]) ok_2_1_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube2_1

section Cube34_8

private def p_34_8 : Nat → Bits
  | 0 => mk128 0xbecfbecfbecfbecf 0xbecfbecfbecfbecf
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0xdf73df73df73df73 0xdf73df73df73df73
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0xefbcefbcefbcefbc 0xefbcefbcefbcefbc
  | 5 => mk128 0x0 0x0
  | _ => 0
private def q_34_8 : Nat → Bits
  | 0 => mk128 0x4205420542054205 0x4205420542054205
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0x2412241224122412 0x2412241224122412
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0x1828182818281828 0x1828182818281828
  | 5 => mk128 0x0 0x0
  | _ => 0
private theorem pp_34_8 : properPairs (childGoal 34 8) (asRow p_34_8) (asRow q_34_8) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_34_8 : List Decor := rawDecor (freeMask 34 8) p_34_8 q_34_8
private def sl_34_8 : List (Sig × Nat) := []
set_option maxHeartbeats 0 in
private theorem sl_34_8_ok : ∀ s ∈ sl_34_8, Slice (freeVars 34 8) (childGoal 34 8) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private noncomputable def lv_34_8_3_0 : List NodeSpec := [([], [0, 1, 2], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_34_8_3_0 : LevelOK rd_34_8 (childGoal 34 8) 3 lv_34_8_3_0 :=
  levelCheck_sound pp_34_8 (raw_faithful _ _ _) sl_34_8_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_34_8 (childGoal 34 8) 2)
    (by decide +kernel : levelCheck (freeVars 34 8) rd_34_8 (childGoal 34 8) sl_34_8 [[]] [] 3 lv_34_8_3_0 = true)
private noncomputable def lv_34_8_3 : List NodeSpec := lv_34_8_3_0
private theorem ok_34_8_3 : LevelOK rd_34_8 (childGoal 34 8) 3 lv_34_8_3 := ok_34_8_3_0
set_option maxHeartbeats 0 in
private theorem lower_34_8 : Lower (freeVars 34 8) (childGoal 34 8) 4 :=
  lower_of_search_at (z := 34) (o := 8) (T := childGoal 34 8) (xs := [(inputs.getD 0 zero, 4, 5), (inputs.getD 2 zero, 1, 5), (inputs.getD 4 zero, 1, 17)]) ok_34_8_3 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube34_8

section Cube34_0

private def p_34_0 : Nat → Bits
  | 0 => mk128 0xffc3fe3fbf0fffc3 0xfe3fbf0fffc3fe3f
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0xfffc3fc7dff0fffc 0x3fc7dff0fffc3fc7
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0xfffc3f8efff0fff 0xc3f8efff0fffc3f8
  | 5 => mk128 0x0 0x0
  | _ => 0
private def q_34_0 : Nat → Bits
  | 0 => mk128 0x22e2661b41e222e2 0x661b41e222e2661b
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0x45662ac5222e4566 0x2ac5222e45662ac5
  | 3 => mk128 0x8988916e04448988 0x916e04448988916e
  | 4 => mk128 0xee3323b01888ee33 0x23b01888ee3323b0
  | 5 => mk128 0x0 0x0
  | _ => 0
private theorem pp_34_0 : properPairs (childGoal 34 0) (asRow p_34_0) (asRow q_34_0) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_34_0 : List Decor := rawDecor (freeMask 34 0) p_34_0 q_34_0
private def sl_34_0 : List (Sig × Nat) := [(subcube 34 8, 4)]
set_option maxHeartbeats 0 in
private theorem sl_34_0_ok : ∀ s ∈ sl_34_0, Slice (freeVars 34 0) (childGoal 34 0) s.1 s.2 := by
  intro s hs
  simp only [sl_34_0, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 34 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_34_8
private noncomputable def lv_34_0_4_0 : List NodeSpec := [([], [0, 1, 2, 3], [(0, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_34_0_4_0 : LevelOK rd_34_0 (childGoal 34 0) 4 lv_34_0_4_0 :=
  levelCheck_sound pp_34_0 (raw_faithful _ _ _) sl_34_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_34_0 (childGoal 34 0) 3)
    (by decide +kernel : levelCheck (freeVars 34 0) rd_34_0 (childGoal 34 0) sl_34_0 [[]] [] 4 lv_34_0_4_0 = true)
private noncomputable def lv_34_0_4 : List NodeSpec := lv_34_0_4_0
private theorem ok_34_0_4 : LevelOK rd_34_0 (childGoal 34 0) 4 lv_34_0_4 := ok_34_0_4_0
set_option maxHeartbeats 0 in
private theorem lower_34_0 : Lower (freeVars 34 0) (childGoal 34 0) 5 :=
  lower_of_search_at (z := 34) (o := 0) (T := childGoal 34 0) (xs := [(inputs.getD 0 zero, 12, 13), (inputs.getD 2 zero, 9, 13), (inputs.getD 3 zero, 5, 13), (inputs.getD 4 zero, 9, 25)]) ok_34_0_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube34_0

section Cube3_16

private def p_3_16 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0xbecfbecfbecfbecf 0xbecfbecfbecfbecf
  | 3 => mk128 0xdf73df73df73df73 0xdf73df73df73df73
  | 4 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 5 => mk128 0xefbcefbcefbcefbc 0xefbcefbcefbcefbc
  | _ => 0
private def q_3_16 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0x4205420542054205 0x4205420542054205
  | 3 => mk128 0x2412241224122412 0x2412241224122412
  | 4 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 5 => mk128 0x1828182818281828 0x1828182818281828
  | _ => 0
private theorem pp_3_16 : properPairs (childGoal 3 16) (asRow p_3_16) (asRow q_3_16) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_3_16 : List Decor := rawDecor (freeMask 3 16) p_3_16 q_3_16
private def sl_3_16 : List (Sig × Nat) := []
set_option maxHeartbeats 0 in
private theorem sl_3_16_ok : ∀ s ∈ sl_3_16, Slice (freeVars 3 16) (childGoal 3 16) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private noncomputable def lv_3_16_3_0 : List NodeSpec := [([], [0, 1, 2], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_3_16_3_0 : LevelOK rd_3_16 (childGoal 3 16) 3 lv_3_16_3_0 :=
  levelCheck_sound pp_3_16 (raw_faithful _ _ _) sl_3_16_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_3_16 (childGoal 3 16) 2)
    (by decide +kernel : levelCheck (freeVars 3 16) rd_3_16 (childGoal 3 16) sl_3_16 [[]] [] 3 lv_3_16_3_0 = true)
private noncomputable def lv_3_16_3 : List NodeSpec := lv_3_16_3_0
private theorem ok_3_16_3 : LevelOK rd_3_16 (childGoal 3 16) 3 lv_3_16_3 := ok_3_16_3_0
set_option maxHeartbeats 0 in
private theorem lower_3_16 : Lower (freeVars 3 16) (childGoal 3 16) 4 :=
  lower_of_search_at (z := 3) (o := 16) (T := childGoal 3 16) (xs := [(inputs.getD 2 zero, 8, 12), (inputs.getD 3 zero, 4, 12), (inputs.getD 5 zero, 4, 36)]) ok_3_16_3 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube3_16

section Cube2_16

private def p_2_16 : Nat → Bits
  | 0 => mk128 0x73afcc9ce3b9f327 0x3afcc9ce3b9f3273
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0x9ccff0e73c3e7c39 0xccff0e73c3e7c39c
  | 3 => mk128 0x1ff7ff07ffc07fc1 0xff7ff07ffc07fc1f
  | 4 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 5 => mk128 0xe0fbfff83fff80fe 0xfbfff83fff80fe0
  | _ => 0
private def q_2_16 : Nat → Bits
  | 0 => mk128 0x31506921208d1a23 0x1506921208d1a231
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0x9430aa0864152a29 0x430aa0864152a294
  | 3 => mk128 0xa09005009004040 0xa09005009004040a
  | 4 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 5 => mk128 0x4006000292200094 0x60002922000940
  | _ => 0
private theorem pp_2_16 : properPairs (childGoal 2 16) (asRow p_2_16) (asRow q_2_16) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_2_16 : List Decor := rawDecor (freeMask 2 16) p_2_16 q_2_16
private def sl_2_16 : List (Sig × Nat) := [(subcube 3 16, 4)]
set_option maxHeartbeats 0 in
private theorem sl_2_16_ok : ∀ s ∈ sl_2_16, Slice (freeVars 2 16) (childGoal 2 16) s.1 s.2 := by
  intro s hs
  simp only [sl_2_16, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 3 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_3_16
private noncomputable def lv_2_16_4_0 : List NodeSpec := [([], [0, 1, 2, 3], [(0, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_2_16_4_0 : LevelOK rd_2_16 (childGoal 2 16) 4 lv_2_16_4_0 :=
  levelCheck_sound pp_2_16 (raw_faithful _ _ _) sl_2_16_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_2_16 (childGoal 2 16) 3)
    (by decide +kernel : levelCheck (freeVars 2 16) rd_2_16 (childGoal 2 16) sl_2_16 [[]] [] 4 lv_2_16_4_0 = true)
private noncomputable def lv_2_16_4 : List NodeSpec := lv_2_16_4_0
private theorem ok_2_16_4 : LevelOK rd_2_16 (childGoal 2 16) 4 lv_2_16_4 := ok_2_16_4_0
set_option maxHeartbeats 0 in
private theorem lower_2_16 : Lower (freeVars 2 16) (childGoal 2 16) 5 :=
  lower_of_search_at (z := 2) (o := 16) (T := childGoal 2 16) (xs := [(inputs.getD 0 zero, 8, 9), (inputs.getD 2 zero, 8, 12), (inputs.getD 3 zero, 1, 9), (inputs.getD 5 zero, 1, 33)]) ok_2_16_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube2_16

section Cube18_4

private def p_18_4 : Nat → Bits
  | 0 => mk128 0xb0e3b0e3b0e3b0e3 0xb0e3b0e3b0e3b0e3
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 3 => mk128 0xfcf3fcf3fcf3fcf3 0xfcf3fcf3fcf3fcf3
  | 4 => mk128 0x0 0x0
  | 5 => mk128 0xff3cff3cff3cff3c 0xff3cff3cff3cff3c
  | _ => 0
private def q_18_4 : Nat → Bits
  | 0 => mk128 0x59a959a959a959a9 0x59a959a959a959a9
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 3 => mk128 0x2212221222122212 0x2212221222122212
  | 4 => mk128 0x0 0x0
  | 5 => mk128 0x8a808a808a808a8 0x8a808a808a808a8
  | _ => 0
private theorem pp_18_4 : properPairs (childGoal 18 4) (asRow p_18_4) (asRow q_18_4) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_18_4 : List Decor := rawDecor (freeMask 18 4) p_18_4 q_18_4
private def sl_18_4 : List (Sig × Nat) := []
set_option maxHeartbeats 0 in
private theorem sl_18_4_ok : ∀ s ∈ sl_18_4, Slice (freeVars 18 4) (childGoal 18 4) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private noncomputable def lv_18_4_2_0 : List NodeSpec := [([], [0, 1, 2], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_18_4_2_0 : LevelOK rd_18_4 (childGoal 18 4) 2 lv_18_4_2_0 :=
  levelCheck_sound pp_18_4 (raw_faithful _ _ _) sl_18_4_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_18_4 (childGoal 18 4) 1)
    (by decide +kernel : levelCheck (freeVars 18 4) rd_18_4 (childGoal 18 4) sl_18_4 [[]] [] 2 lv_18_4_2_0 = true)
private noncomputable def lv_18_4_2 : List NodeSpec := lv_18_4_2_0
private theorem ok_18_4_2 : LevelOK rd_18_4 (childGoal 18 4) 2 lv_18_4_2 := ok_18_4_2_0
set_option maxHeartbeats 0 in
private theorem lower_18_4 : Lower (freeVars 18 4) (childGoal 18 4) 3 :=
  lower_of_search_at (z := 18) (o := 4) (T := childGoal 18 4) (xs := [(inputs.getD 0 zero, 8, 9), (inputs.getD 3 zero, 1, 9), (inputs.getD 5 zero, 0, 32)]) ok_18_4_2 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube18_4

section Cube2_4

private def p_2_4 : Nat → Bits
  | 0 => mk128 0x13b3898dcc60e7d1 0x3b3898dcc60e7d13
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 3 => mk128 0x9fdff1eff078ff19 0xfdff1eff078ff19f
  | 4 => mk128 0x1ce7fe0eff80f8e1 0xce7fe0eff80f8e1c
  | 5 => mk128 0xe0fbfff0ffff00fe 0xfbfff0ffff00fe0
  | _ => 0
private def q_2_4 : Nat → Bits
  | 0 => mk128 0x514ce33ac73136d5 0x14ce33ac73136d51
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 3 => mk128 0x8621040010424008 0x6210400104240086
  | 4 => mk128 0x181a215169049261 0x81a2151690492618
  | 5 => mk128 0x4004400882100494 0x44008821004940
  | _ => 0
private theorem pp_2_4 : properPairs (childGoal 2 4) (asRow p_2_4) (asRow q_2_4) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_2_4 : List Decor := rawDecor (freeMask 2 4) p_2_4 q_2_4
private def sl_2_4 : List (Sig × Nat) := [(subcube 18 4, 3)]
set_option maxHeartbeats 0 in
private theorem sl_2_4_ok : ∀ s ∈ sl_2_4, Slice (freeVars 2 4) (childGoal 2 4) s.1 s.2 := by
  intro s hs
  simp only [sl_2_4, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 18 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_18_4
private noncomputable def lv_2_4_4_0 : List NodeSpec := [([], [0, 1, 2, 3], [(0, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_2_4_4_0 : LevelOK rd_2_4 (childGoal 2 4) 4 lv_2_4_4_0 :=
  levelCheck_sound pp_2_4 (raw_faithful _ _ _) sl_2_4_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_2_4 (childGoal 2 4) 3)
    (by decide +kernel : levelCheck (freeVars 2 4) rd_2_4 (childGoal 2 4) sl_2_4 [[]] [] 4 lv_2_4_4_0 = true)
private noncomputable def lv_2_4_4 : List NodeSpec := lv_2_4_4_0
private theorem ok_2_4_4 : LevelOK rd_2_4 (childGoal 2 4) 4 lv_2_4_4 := ok_2_4_4_0
set_option maxHeartbeats 0 in
private theorem lower_2_4 : Lower (freeVars 2 4) (childGoal 2 4) 5 :=
  lower_of_search_at (z := 2) (o := 4) (T := childGoal 2 4) (xs := [(inputs.getD 0 zero, 8, 9), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 8, 24), (inputs.getD 5 zero, 0, 32)]) ok_2_4_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube2_4

section Cube3_8

private def p_3_8 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0xbecfbecfbecfbecf 0xbecfbecfbecfbecf
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0xdf73df73df73df73 0xdf73df73df73df73
  | 5 => mk128 0xefbcefbcefbcefbc 0xefbcefbcefbcefbc
  | _ => 0
private def q_3_8 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0x4205420542054205 0x4205420542054205
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0x2412241224122412 0x2412241224122412
  | 5 => mk128 0x1828182818281828 0x1828182818281828
  | _ => 0
private theorem pp_3_8 : properPairs (childGoal 3 8) (asRow p_3_8) (asRow q_3_8) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_3_8 : List Decor := rawDecor (freeMask 3 8) p_3_8 q_3_8
private def sl_3_8 : List (Sig × Nat) := []
set_option maxHeartbeats 0 in
private theorem sl_3_8_ok : ∀ s ∈ sl_3_8, Slice (freeVars 3 8) (childGoal 3 8) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private noncomputable def lv_3_8_3_0 : List NodeSpec := [([], [0, 1, 2], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_3_8_3_0 : LevelOK rd_3_8 (childGoal 3 8) 3 lv_3_8_3_0 :=
  levelCheck_sound pp_3_8 (raw_faithful _ _ _) sl_3_8_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_3_8 (childGoal 3 8) 2)
    (by decide +kernel : levelCheck (freeVars 3 8) rd_3_8 (childGoal 3 8) sl_3_8 [[]] [] 3 lv_3_8_3_0 = true)
private noncomputable def lv_3_8_3 : List NodeSpec := lv_3_8_3_0
private theorem ok_3_8_3 : LevelOK rd_3_8 (childGoal 3 8) 3 lv_3_8_3 := ok_3_8_3_0
set_option maxHeartbeats 0 in
private theorem lower_3_8 : Lower (freeVars 3 8) (childGoal 3 8) 4 :=
  lower_of_search_at (z := 3) (o := 8) (T := childGoal 3 8) (xs := [(inputs.getD 2 zero, 16, 20), (inputs.getD 4 zero, 4, 20), (inputs.getD 5 zero, 4, 36)]) ok_3_8_3 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube3_8

section Cube3_0

private def p_3_0 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0xffbfc7fffe3fff1f 0xfbfc7fffe3fff1ff
  | 3 => mk128 0x67d7f879ffc707e6 0x7d7f879ffc707e67
  | 4 => mk128 0x87e7ff81fff807f8 0x7e7ff81fff807f87
  | 5 => mk128 0xf8fbfffe3ffff8ff 0x8fbfffe3ffff8ff8
  | _ => 0
private def q_3_0 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0xab4071100609310a 0xb4071100609310ab
  | 3 => mk128 0x652897229a425266 0x52897229a4252665
  | 4 => mk128 0x861922752c90a4b8 0x61922752c90a4b86
  | 5 => mk128 0x50060441b124c0d5 0x60441b124c0d50
  | _ => 0
private theorem pp_3_0 : properPairs (childGoal 3 0) (asRow p_3_0) (asRow q_3_0) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_3_0 : List Decor := rawDecor (freeMask 3 0) p_3_0 q_3_0
private def sl_3_0 : List (Sig × Nat) := [(subcube 3 8, 4)]
set_option maxHeartbeats 0 in
private theorem sl_3_0_ok : ∀ s ∈ sl_3_0, Slice (freeVars 3 0) (childGoal 3 0) s.1 s.2 := by
  intro s hs
  simp only [sl_3_0, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 3 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_3_8
private noncomputable def lv_3_0_4_0 : List NodeSpec := [([], [0, 1, 2, 3], [(0, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_3_0_4_0 : LevelOK rd_3_0 (childGoal 3 0) 4 lv_3_0_4_0 :=
  levelCheck_sound pp_3_0 (raw_faithful _ _ _) sl_3_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_3_0 (childGoal 3 0) 3)
    (by decide +kernel : levelCheck (freeVars 3 0) rd_3_0 (childGoal 3 0) sl_3_0 [[]] [] 4 lv_3_0_4_0 = true)
private noncomputable def lv_3_0_4 : List NodeSpec := lv_3_0_4_0
private theorem ok_3_0_4 : LevelOK rd_3_0 (childGoal 3 0) 4 lv_3_0_4 := ok_3_0_4_0
set_option maxHeartbeats 0 in
private theorem lower_3_0 : Lower (freeVars 3 0) (childGoal 3 0) 5 :=
  lower_of_search_at (z := 3) (o := 0) (T := childGoal 3 0) (xs := [(inputs.getD 2 zero, 24, 28), (inputs.getD 3 zero, 20, 28), (inputs.getD 4 zero, 12, 28), (inputs.getD 5 zero, 4, 36)]) ok_3_0_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube3_0

section Cube10_0

private def p_10_0 : Nat → Bits
  | 0 => mk128 0x3e0f8338af0e3e0f 0x8338af0e3e0f8338
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0xfff07fc7dff1fff0 0x7fc7dff1fff07fc7
  | 3 => mk128 0x0 0x0
  | 4 => mk128 0x3fff83f8effe3fff 0x83f8effe3fff83f8
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private def q_10_0 : Nat → Bits
  | 0 => mk128 0x574aab1c51e5574a 0xab1c51e5574aab1c
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0xb5a1b45222d0b5a 0x1b45222d0b5a1b45
  | 3 => mk128 0x0 0x0
  | 4 => mk128 0xac6351e81449ac63 0x51e81449ac6351e8
  | 5 => mk128 0x318c62b60880318c 0x62b60880318c62b6
  | _ => 0
private theorem pp_10_0 : properPairs (childGoal 10 0) (asRow p_10_0) (asRow q_10_0) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_10_0 : List Decor := rawDecor (freeMask 10 0) p_10_0 q_10_0
private def sl_10_0 : List (Sig × Nat) := []
set_option maxHeartbeats 0 in
private theorem sl_10_0_ok : ∀ s ∈ sl_10_0, Slice (freeVars 10 0) (childGoal 10 0) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private noncomputable def lv_10_0_3_0 : List NodeSpec := [([], [0, 1, 2, 3], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_10_0_3_0 : LevelOK rd_10_0 (childGoal 10 0) 3 lv_10_0_3_0 :=
  levelCheck_sound pp_10_0 (raw_faithful _ _ _) sl_10_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_10_0 (childGoal 10 0) 2)
    (by decide +kernel : levelCheck (freeVars 10 0) rd_10_0 (childGoal 10 0) sl_10_0 [[]] [] 3 lv_10_0_3_0 = true)
private noncomputable def lv_10_0_3 : List NodeSpec := lv_10_0_3_0
private theorem ok_10_0_3 : LevelOK rd_10_0 (childGoal 10 0) 3 lv_10_0_3 := ok_10_0_3_0
set_option maxHeartbeats 0 in
private theorem lower_10_0 : Lower (freeVars 10 0) (childGoal 10 0) 4 :=
  lower_of_search_at (z := 10) (o := 0) (T := childGoal 10 0) (xs := [(inputs.getD 0 zero, 36, 37), (inputs.getD 2 zero, 32, 36), (inputs.getD 4 zero, 33, 49), (inputs.getD 5 zero, 4, 36)]) ok_10_0_3 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube10_0

section Cube10_32

private def p_10_32 : Nat → Bits
  | 0 => mk128 0xb32cb32cb32cb32c 0xb32cb32cb32cb32c
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0xfcf3fcf3fcf3fcf3 0xfcf3fcf3fcf3fcf3
  | 3 => mk128 0x0 0x0
  | 4 => mk128 0xff3cff3cff3cff3c 0xff3cff3cff3cff3c
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private def q_10_32 : Nat → Bits
  | 0 => mk128 0x5a665a665a665a66 0x5a665a665a665a66
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0xa220a220a220a22 0xa220a220a220a22
  | 3 => mk128 0x0 0x0
  | 4 => mk128 0x2098209820982098 0x2098209820982098
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private theorem pp_10_32 : properPairs (childGoal 10 32) (asRow p_10_32) (asRow q_10_32) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_10_32 : List Decor := rawDecor (freeMask 10 32) p_10_32 q_10_32
private def sl_10_32 : List (Sig × Nat) := []
set_option maxHeartbeats 0 in
private theorem sl_10_32_ok : ∀ s ∈ sl_10_32, Slice (freeVars 10 32) (childGoal 10 32) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private noncomputable def lv_10_32_2_0 : List NodeSpec := [([], [0, 1, 2], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_10_32_2_0 : LevelOK rd_10_32 (childGoal 10 32) 2 lv_10_32_2_0 :=
  levelCheck_sound pp_10_32 (raw_faithful _ _ _) sl_10_32_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_10_32 (childGoal 10 32) 1)
    (by decide +kernel : levelCheck (freeVars 10 32) rd_10_32 (childGoal 10 32) sl_10_32 [[]] [] 2 lv_10_32_2_0 = true)
private noncomputable def lv_10_32_2 : List NodeSpec := lv_10_32_2_0
private theorem ok_10_32_2 : LevelOK rd_10_32 (childGoal 10 32) 2 lv_10_32_2 := ok_10_32_2_0
set_option maxHeartbeats 0 in
private theorem lower_10_32 : Lower (freeVars 10 32) (childGoal 10 32) 3 :=
  lower_of_search_at (z := 10) (o := 32) (T := childGoal 10 32) (xs := [(inputs.getD 0 zero, 4, 5), (inputs.getD 2 zero, 0, 4), (inputs.getD 4 zero, 1, 17)]) ok_10_32_2 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube10_32

section Cube2_0

private def p_2_0 : Nat → Bits
  | 0 => mk128 0x87c0fffe0fc7c1ff 0x8780fc3fe33ce23f
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0x7fff01fff007fe0f 0xf87fffc3e3c71fc7
  | 3 => mk128 0x87fffffffff8000f 0xff80fffffc07e3ff
  | 4 => mk128 0x7fffe07fffffff0 0xfffc1ff803f8
  | 5 => mk128 0xf8000007ffffffff 0xffff00001ffffc00
  | _ => 0
private def q_2_0 : Nat → Bits
  | 0 => mk128 0x4c4e249602c2e955 0xc4922e27231c721b
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0x44821c2630016b42 0xcc0e5663434516c5
  | 3 => mk128 0x11144940d548000b 0x112498888c03a16e
  | 4 => mk128 0x6228907369958c60 0x48e33115e803b0
  | 5 => mk128 0x430e1858e26318c 0x667000021ab6d800
  | _ => 0
private theorem pp_2_0 : properPairs (childGoal 2 0) (asRow p_2_0) (asRow q_2_0) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_2_0 : List Decor := rawDecor (freeMask 2 0) p_2_0 q_2_0
private def sl_2_0 : List (Sig × Nat) := [(subcube 6 0, 7), (subcube 2 8, 7), (subcube 2 32, 6), (subcube 18 0, 6), (subcube 2 1, 5), (subcube 34 0, 5), (subcube 2 16, 5), (subcube 2 4, 5), (subcube 3 0, 5), (subcube 10 0, 4), (subcube 10 32, 3)]
set_option maxHeartbeats 0 in
private theorem sl_2_0_ok : ∀ s ∈ sl_2_0, Slice (freeVars 2 0) (childGoal 2 0) s.1 s.2 := by
  intro s hs
  simp only [sl_2_0, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact slice_correct (ms := fixRows 6 0) (base := freeVars 6 0) (G := childGoal 6 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_6_0
  · exact slice_correct (ms := fixRows 2 8) (base := freeVars 2 8) (G := childGoal 2 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_2_8
  · exact slice_correct (ms := fixRows 2 32) (base := freeVars 2 32) (G := childGoal 2 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_2_32
  · exact slice_correct (ms := fixRows 18 0) (base := freeVars 18 0) (G := childGoal 18 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_18_0
  · exact slice_correct (ms := fixRows 2 1) (base := freeVars 2 1) (G := childGoal 2 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_2_1
  · exact slice_correct (ms := fixRows 34 0) (base := freeVars 34 0) (G := childGoal 34 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_34_0
  · exact slice_correct (ms := fixRows 2 16) (base := freeVars 2 16) (G := childGoal 2 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_2_16
  · exact slice_correct (ms := fixRows 2 4) (base := freeVars 2 4) (G := childGoal 2 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_2_4
  · exact slice_correct (ms := fixRows 3 0) (base := freeVars 3 0) (G := childGoal 3 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_3_0
  · exact slice_correct (ms := fixRows 10 0) (base := freeVars 10 0) (G := childGoal 10 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_10_0
  · exact slice_correct (ms := fixRows 10 32) (base := freeVars 10 32) (G := childGoal 10 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_10_32
private noncomputable def lv_2_0_6_0 : List NodeSpec := [([(1, 3, 0), (0, 5, 2)], [0, 1, 6, 3, 4], [(0, [0, 1]), (1, [0]), (2, [0, 1]), (3, [1]), (4, []), (9, []), (10, [])]), ([(0, 4, 0), (1, 1, 5)], [0, 6, 2, 3, 4], [(0, [0]), (1, [0, 1]), (2, [1]), (3, [0, 1]), (4, [1]), (7, []), (8, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_2_0_6_0 : LevelOK rd_2_0 (childGoal 2 0) 6 lv_2_0_6_0 :=
  levelCheck_sound pp_2_0 (raw_faithful _ _ _) sl_2_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_2_0 (childGoal 2 0) 5)
    (by decide +kernel : levelCheck (freeVars 2 0) rd_2_0 (childGoal 2 0) sl_2_0 [[]] [] 6 lv_2_0_6_0 = true)
private noncomputable def lv_2_0_6 : List NodeSpec := lv_2_0_6_0
private theorem ok_2_0_6 : LevelOK rd_2_0 (childGoal 2 0) 6 lv_2_0_6 := ok_2_0_6_0
private noncomputable def lv_2_0_7_0 : List NodeSpec := [([(1, 3, 0)], [0, 1, 2, 3, 5, 4], [(0, []), (0, [0]), (1, []), (1, [0]), (2, []), (2, [0]), (3, []), (4, []), (5, [])]), ([(3, 3, 0)], [5, 0, 1, 2, 3, 4], [(0, []), (0, [0]), (1, []), (1, [0]), (2, []), (2, [0]), (3, []), (4, []), (5, []), (6, []), (8, [])]), ([(0, 4, 0)], [5, 0, 1, 2, 3, 4], [(0, []), (0, [0]), (1, []), (1, [0]), (2, []), (3, []), (3, [0]), (4, []), (5, []), (6, []), (8, [])]), ([(2, 4, 0)], [5, 0, 1, 2, 3, 4], [(0, []), (0, [0]), (1, []), (1, [0]), (2, []), (3, []), (3, [0]), (4, []), (6, [])]), ([(2, 4, 3)], [5, 0, 1, 2, 3, 4], [(0, []), (0, [0]), (1, []), (1, [0]), (2, []), (3, []), (4, []), (5, []), (8, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_2_0_7_0 : LevelOK rd_2_0 (childGoal 2 0) 7 lv_2_0_7_0 :=
  levelCheck_sound pp_2_0 (raw_faithful _ _ _) sl_2_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) ok_2_0_6
    (by decide +kernel : levelCheck (freeVars 2 0) rd_2_0 (childGoal 2 0) sl_2_0 [[]] lv_2_0_6 7 lv_2_0_7_0 = true)
private noncomputable def lv_2_0_7 : List NodeSpec := lv_2_0_7_0
private theorem ok_2_0_7 : LevelOK rd_2_0 (childGoal 2 0) 7 lv_2_0_7 := ok_2_0_7_0
private noncomputable def lv_2_0_8_0 : List NodeSpec := [([], [0, 1, 2, 3, 4], [(0, []), (1, []), (2, []), (3, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_2_0_8_0 : LevelOK rd_2_0 (childGoal 2 0) 8 lv_2_0_8_0 :=
  levelCheck_sound pp_2_0 (raw_faithful _ _ _) sl_2_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) ok_2_0_7
    (by decide +kernel : levelCheck (freeVars 2 0) rd_2_0 (childGoal 2 0) sl_2_0 [[]] lv_2_0_7 8 lv_2_0_8_0 = true)
private noncomputable def lv_2_0_8 : List NodeSpec := lv_2_0_8_0
private theorem ok_2_0_8 : LevelOK rd_2_0 (childGoal 2 0) 8 lv_2_0_8 := ok_2_0_8_0
set_option maxHeartbeats 0 in
private theorem lower_2_0 : Lower (freeVars 2 0) (childGoal 2 0) 9 :=
  lower_of_search_at (z := 2) (o := 0) (T := childGoal 2 0) (xs := [(inputs.getD 0 zero, 12, 13), (inputs.getD 2 zero, 9, 13), (inputs.getD 3 zero, 5, 13), (inputs.getD 4 zero, 9, 25), (inputs.getD 5 zero, 4, 36)]) ok_2_0_8 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube2_0

end D1

section Cube4_32

private def p_4_32 : Nat → Bits
  | 0 => mk128 0xbff7fffe3ffff1ff 0xbff7fffe3ffff1ff
  | 1 => mk128 0xd5f8e73fc71c7e93 0xd5f8e73fc71c7e93
  | 2 => mk128 0x0 0x0
  | 3 => mk128 0xe6ff07cff81f8f1c 0xe6ff07cff81f8f1c
  | 4 => mk128 0xf8fff80fffe00fe0 0xf8fff80fffe00fe0
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private def q_4_32 : Nat → Bits
  | 0 => mk128 0x4010000009040025 0x4010000009040025
  | 1 => mk128 0x2a264a4642496692 0x2a264a4642496692
  | 2 => mk128 0x0 0x0
  | 3 => mk128 0x1942d41a90932b18 0x1942d41a90932b18
  | 4 => mk128 0x78486ad24c24dc0 0x78486ad24c24dc0
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private theorem pp_4_32 : properPairs (subGoal 4 32) (asRow p_4_32) (asRow q_4_32) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_4_32 : List Decor := rawDecor (freeMask 4 32) p_4_32 q_4_32
private def sl_4_32 : List (Sig × Nat) := []
private theorem sl_4_32_ok : ∀ s ∈ sl_4_32, Slice (freeVars 4 32) (subGoal 4 32) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private def fmt_4_32_3 : ChartFormat := ⟨4, 2, 0, 0, 1⟩
private abbrev Batch_4_32_3 := CheckedBatch (freeVars 4 32) rd_4_32 (subGoal 4 32) sl_4_32 [[]] 3 fmt_4_32_3 [] fmt_4_32_3
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_4_32_3_0 : List Batch_4_32_3 := [
  ⟨⟨2,0x64548a11d212244,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x44548e12a212344,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x64548b15d212205,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x44548f155212305,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x68548621aa12148,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x44548e22a212348,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x68543225aa10c09,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x44548f26a212309,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xa8848d69d810a58,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xa8848d6d521239a,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x6a848532a21239b,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x74848931a15218c,0x1⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_4_32_3_1 : List Batch_4_32_3 := [
  ⟨⟨2,0x6a843035915228c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x74845035a150c8d,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xaa042d71915148d,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x66848a79d21225e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x74848a7dd21225f,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x6a8485bac21136c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x6a8485bdaa121ae,0x1⟩,by decide +kernel⟩,
  ⟨⟨1,0x1aa121af,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_4_32_3 : List Batch_4_32_3 := (ch_4_32_3_0 ++ ch_4_32_3_1)
private noncomputable def lv_4_32_3 : List NodeSpec := flattenBatches fmt_4_32_3 (ch_4_32_3.map Subtype.val)
private theorem ok_4_32_3 : LevelOK rd_4_32 (subGoal 4 32) 3 lv_4_32_3 :=
  @checkedBatches (freeVars 4 32) rd_4_32 _ _ _ sl_4_32 [[]] 3 fmt_4_32_3 [] fmt_4_32_3 pp_4_32 (raw_faithful (freeMask 4 32) p_4_32 q_4_32) sl_4_32_ok (by decide +kernel) (emptyLevelOK rd_4_32 (subGoal 4 32) 2) ch_4_32_3

private def fmt_4_32_4 : ChartFormat := ⟨4, 1, 0, 0, 1⟩
private abbrev Batch_4_32_4 := CheckedBatch (freeVars 4 32) rd_4_32 (subGoal 4 32) sl_4_32 [[]] 4 fmt_4_32_3 (ch_4_32_3.map Subtype.val) fmt_4_32_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_4_32_4_0 : List Batch_4_32_4 := [
  ⟨⟨2,0x1a8428ad11144,0x7f98⟩,by decide +kernel⟩,
  ⟨⟨2,0x1a2228ed11146,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1c44292d11148,0x1fcc18⟩,by decide +kernel⟩,
  ⟨⟨2,0x1a22296d1114a,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1c442b2d18158,0x182⟩,by decide +kernel⟩,
  ⟨⟨2,0x1a222b6d1115a,0x1ca0c⟩,by decide +kernel⟩,
  ⟨⟨2,0x234429ad1114c,0x7f6818⟩,by decide +kernel⟩,
  ⟨⟨2,0x1a2229ed1114e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x23442bad1815c,0xe82⟩,by decide +kernel⟩,
  ⟨⟨2,0x1a222bed1115e,0x1fe0c⟩,by decide +kernel⟩,
  ⟨⟨2,0x23442dad4216c,0x702⟩,by decide +kernel⟩,
  ⟨⟨2,0x1a222ded1116e,0x7240c⟩,by decide +kernel⟩]
private noncomputable def ch_4_32_4 : List Batch_4_32_4 := ch_4_32_4_0
private noncomputable def lv_4_32_4 : List NodeSpec := flattenBatches fmt_4_32_4 (ch_4_32_4.map Subtype.val)
private theorem ok_4_32_4 : LevelOK rd_4_32 (subGoal 4 32) 4 lv_4_32_4 :=
  @checkedBatches (freeVars 4 32) rd_4_32 _ _ _ sl_4_32 [[]] 4 fmt_4_32_3 (ch_4_32_3.map Subtype.val) fmt_4_32_4 pp_4_32 (raw_faithful (freeMask 4 32) p_4_32 q_4_32) sl_4_32_ok (by decide +kernel) ok_4_32_3 ch_4_32_4

private def fmt_4_32_5 : ChartFormat := ⟨4, 0, 0, 0, 1⟩
private abbrev Batch_4_32_5 := CheckedBatch (freeVars 4 32) rd_4_32 (subGoal 4 32) sl_4_32 [[]] 5 fmt_4_32_4 (ch_4_32_4.map Subtype.val) fmt_4_32_5
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_4_32_5_0 : List Batch_4_32_5 := [
  ⟨⟨1,0xe44,0x1ffffff30⟩,by decide +kernel⟩]
private noncomputable def ch_4_32_5 : List Batch_4_32_5 := ch_4_32_5_0
private noncomputable def lv_4_32_5 : List NodeSpec := flattenBatches fmt_4_32_5 (ch_4_32_5.map Subtype.val)
private theorem ok_4_32_5 : LevelOK rd_4_32 (subGoal 4 32) 5 lv_4_32_5 :=
  @checkedBatches (freeVars 4 32) rd_4_32 _ _ _ sl_4_32 [[]] 5 fmt_4_32_4 (ch_4_32_4.map Subtype.val) fmt_4_32_5 pp_4_32 (raw_faithful (freeMask 4 32) p_4_32 q_4_32) sl_4_32_ok (by decide +kernel) ok_4_32_4 ch_4_32_5
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_4_32 : Lower (freeVars 4 32) (subGoal 4 32) 6 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 1, 17)]) ok_4_32_5 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube4_32

section Cube1_40

private def p_1_40 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0xbecfbecfbecfbecf 0xbecfbecfbecfbecf
  | 2 => mk128 0xdf73df73df73df73 0xdf73df73df73df73
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0xefbcefbcefbcefbc 0xefbcefbcefbcefbc
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private def q_1_40 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0x4205420542054205 0x4205420542054205
  | 2 => mk128 0x2412241224122412 0x2412241224122412
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0x1828182818281828 0x1828182818281828
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private theorem pp_1_40 : properPairs (subGoal 1 40) (asRow p_1_40) (asRow q_1_40) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_1_40 : List Decor := rawDecor (freeMask 1 40) p_1_40 q_1_40
private def sl_1_40 : List (Sig × Nat) := []
private theorem sl_1_40_ok : ∀ s ∈ sl_1_40, Slice (freeVars 1 40) (subGoal 1 40) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private def fmt_1_40_3 : ChartFormat := ⟨3, 0, 0, 0, 1⟩
private abbrev Batch_1_40_3 := CheckedBatch (freeVars 1 40) rd_1_40 (subGoal 1 40) sl_1_40 [[]] 3 fmt_1_40_3 [] fmt_1_40_3
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_1_40_3_0 : List Batch_1_40_3 := [
  ⟨⟨1,0x243,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_1_40_3 : List Batch_1_40_3 := ch_1_40_3_0
private noncomputable def lv_1_40_3 : List NodeSpec := flattenBatches fmt_1_40_3 (ch_1_40_3.map Subtype.val)
private theorem ok_1_40_3 : LevelOK rd_1_40 (subGoal 1 40) 3 lv_1_40_3 :=
  @checkedBatches (freeVars 1 40) rd_1_40 _ _ _ sl_1_40 [[]] 3 fmt_1_40_3 [] fmt_1_40_3 pp_1_40 (raw_faithful (freeMask 1 40) p_1_40 q_1_40) sl_1_40_ok (by decide +kernel) (emptyLevelOK rd_1_40 (subGoal 1 40) 2) ch_1_40_3
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_1_40 : Lower (freeVars 1 40) (subGoal 1 40) 4 :=
  lower_of_search (xs := [(inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 4 zero, 2, 18)]) ok_1_40_3 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube1_40

section Cube1_32

private def p_1_32 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0xffbfc7fffe3fff1f 0xfbfc7fffe3fff1ff
  | 2 => mk128 0x3fdff8ffffc7ffe3 0xfdff8ffffc7ffe3f
  | 3 => mk128 0xccebff0f3ff8e0fc 0xcebff0f3ff8e0fcc
  | 4 => mk128 0xf0f3fff03fff00ff 0xf3fff03fff00ff0
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private def q_1_32 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0xd54070220a092a0d 0x54070220a092a0d5
  | 2 => mk128 0x2a20864414425462 0xa20864414425462a
  | 3 => mk128 0x4c1512e8669086b4 0xc1512e8669086b4c
  | 4 => mk128 0xb00e248eb92418db 0xe248eb92418db0
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private theorem pp_1_32 : properPairs (subGoal 1 32) (asRow p_1_32) (asRow q_1_32) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_1_32 : List Decor := rawDecor (freeMask 1 32) p_1_32 q_1_32
private def sl_1_32 : List (Sig × Nat) := [(subcube 1 40, 4)]
private theorem sl_1_32_ok : ∀ s ∈ sl_1_32, Slice (freeVars 1 32) (subGoal 1 32) s.1 s.2 := by
  intro s hs
  simp only [sl_1_32, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 1 40) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_1_40
private def fmt_1_32_4 : ChartFormat := ⟨4, 0, 0, 1, 0⟩
private abbrev Batch_1_32_4 := CheckedBatch (freeVars 1 32) rd_1_32 (subGoal 1 32) sl_1_32 [[]] 4 fmt_1_32_4 [] fmt_1_32_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_1_32_4_0 : List Batch_1_32_4 := [
  ⟨⟨1,0x1e44,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_1_32_4 : List Batch_1_32_4 := ch_1_32_4_0
private noncomputable def lv_1_32_4 : List NodeSpec := flattenBatches fmt_1_32_4 (ch_1_32_4.map Subtype.val)
private theorem ok_1_32_4 : LevelOK rd_1_32 (subGoal 1 32) 4 lv_1_32_4 :=
  @checkedBatches (freeVars 1 32) rd_1_32 _ _ _ sl_1_32 [[]] 4 fmt_1_32_4 [] fmt_1_32_4 pp_1_32 (raw_faithful (freeMask 1 32) p_1_32 q_1_32) sl_1_32_ok (by decide +kernel) (emptyLevelOK rd_1_32 (subGoal 1 32) 3) ch_1_32_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_1_32 : Lower (freeVars 1 32) (subGoal 1 32) 5 :=
  lower_of_search (xs := [(inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 3 zero, 18, 26), (inputs.getD 4 zero, 10, 26)]) ok_1_32_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube1_32

section Cube2_36

private def p_2_36 : Nat → Bits
  | 0 => mk128 0xbecfbecfbecfbecf 0xbecfbecfbecfbecf
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 3 => mk128 0xdf73df73df73df73 0xdf73df73df73df73
  | 4 => mk128 0xefbcefbcefbcefbc 0xefbcefbcefbcefbc
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private def q_2_36 : Nat → Bits
  | 0 => mk128 0x4205420542054205 0x4205420542054205
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 3 => mk128 0x2412241224122412 0x2412241224122412
  | 4 => mk128 0x1828182818281828 0x1828182818281828
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private theorem pp_2_36 : properPairs (subGoal 2 36) (asRow p_2_36) (asRow q_2_36) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_2_36 : List Decor := rawDecor (freeMask 2 36) p_2_36 q_2_36
private def sl_2_36 : List (Sig × Nat) := []
private theorem sl_2_36_ok : ∀ s ∈ sl_2_36, Slice (freeVars 2 36) (subGoal 2 36) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private def fmt_2_36_3 : ChartFormat := ⟨3, 0, 0, 0, 1⟩
private abbrev Batch_2_36_3 := CheckedBatch (freeVars 2 36) rd_2_36 (subGoal 2 36) sl_2_36 [[]] 3 fmt_2_36_3 [] fmt_2_36_3
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_2_36_3_0 : List Batch_2_36_3 := [
  ⟨⟨1,0x243,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_2_36_3 : List Batch_2_36_3 := ch_2_36_3_0
private noncomputable def lv_2_36_3 : List NodeSpec := flattenBatches fmt_2_36_3 (ch_2_36_3.map Subtype.val)
private theorem ok_2_36_3 : LevelOK rd_2_36 (subGoal 2 36) 3 lv_2_36_3 :=
  @checkedBatches (freeVars 2 36) rd_2_36 _ _ _ sl_2_36 [[]] 3 fmt_2_36_3 [] fmt_2_36_3 pp_2_36 (raw_faithful (freeMask 2 36) p_2_36 q_2_36) sl_2_36_ok (by decide +kernel) (emptyLevelOK rd_2_36 (subGoal 2 36) 2) ch_2_36_3
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_2_36 : Lower (freeVars 2 36) (subGoal 2 36) 4 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 8, 9), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 1, 17)]) ok_2_36_3 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube2_36

section Cube2_32

private def p_2_32 : Nat → Bits
  | 0 => mk128 0xeff9ffff8ffff8ff 0xdff3ffff1ffff1ff
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0x357e1ce7f1c38766 0x6afc39cfe3870ecc
  | 3 => mk128 0xf9ffe0fffe03ff87 0xf3ffc1fffc07ff0f
  | 4 => mk128 0x3e7fff07fffc07f8 0x7cfffe0ffff80ff0
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private def q_2_32 : Nat → Bits
  | 0 => mk128 0x500c40008248902a 0xa018800104912055
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0xa95c94b90993366 0x152b9297213266cc
  | 3 => mk128 0x86209a8524226585 0xc41350a4844cb0a
  | 4 => mk128 0x1c110d6493046d0 0x38221ac92608da0
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private theorem pp_2_32 : properPairs (subGoal 2 32) (asRow p_2_32) (asRow q_2_32) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_2_32 : List Decor := rawDecor (freeMask 2 32) p_2_32 q_2_32
private def sl_2_32 : List (Sig × Nat) := [(subcube 2 36, 4)]
private theorem sl_2_32_ok : ∀ s ∈ sl_2_32, Slice (freeVars 2 32) (subGoal 2 32) s.1 s.2 := by
  intro s hs
  simp only [sl_2_32, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 2 36) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_2_36
private def fmt_2_32_4 : ChartFormat := ⟨4, 0, 0, 1, 0⟩
private abbrev Batch_2_32_4 := CheckedBatch (freeVars 2 32) rd_2_32 (subGoal 2 32) sl_2_32 [[]] 4 fmt_2_32_4 [] fmt_2_32_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_2_32_4_0 : List Batch_2_32_4 := [
  ⟨⟨1,0x1e44,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_2_32_4 : List Batch_2_32_4 := ch_2_32_4_0
private noncomputable def lv_2_32_4 : List NodeSpec := flattenBatches fmt_2_32_4 (ch_2_32_4.map Subtype.val)
private theorem ok_2_32_4 : LevelOK rd_2_32 (subGoal 2 32) 4 lv_2_32_4 :=
  @checkedBatches (freeVars 2 32) rd_2_32 _ _ _ sl_2_32 [[]] 4 fmt_2_32_4 [] fmt_2_32_4 pp_2_32 (raw_faithful (freeMask 2 32) p_2_32 q_2_32) sl_2_32_ok (by decide +kernel) (emptyLevelOK rd_2_32 (subGoal 2 32) 3) ch_2_32_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_2_32 : Lower (freeVars 2 32) (subGoal 2 32) 5 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 8, 9), (inputs.getD 2 zero, 24, 28), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 1, 17)]) ok_2_32_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube2_32

section Cube0_36

private def p_0_36 : Nat → Bits
  | 0 => mk128 0x73b7606ebea673b7 0x606ebea673b7606e
  | 1 => mk128 0xbc3bbc93ff3bbc3b 0xbc93ff3bbc3bbc93
  | 2 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 3 => mk128 0xcfc3c31cdfc3cfc3 0xc31cdfc3cfc3c31c
  | 4 => mk128 0xffc03e0effc0ffc 0x3e0effc0ffc03e0
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private def q_0_36 : Nat → Bits
  | 0 => mk128 0x8091042642488091 0x426424880910426
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 3 => mk128 0x1502091824141502 0x918241415020918
  | 4 => mk128 0x6a2012c018016a20 0x12c018016a2012c0
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private theorem pp_0_36 : properPairs (subGoal 0 36) (asRow p_0_36) (asRow q_0_36) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_0_36 : List Decor := rawDecor (freeMask 0 36) p_0_36 q_0_36
private def sl_0_36 : List (Sig × Nat) := [(subcube 2 36, 4)]
private theorem sl_0_36_ok : ∀ s ∈ sl_0_36, Slice (freeVars 0 36) (subGoal 0 36) s.1 s.2 := by
  intro s hs
  simp only [sl_0_36, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 2 36) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_2_36
private def fmt_0_36_4 : ChartFormat := ⟨4, 0, 0, 1, 0⟩
private abbrev Batch_0_36_4 := CheckedBatch (freeVars 0 36) rd_0_36 (subGoal 0 36) sl_0_36 [[]] 4 fmt_0_36_4 [] fmt_0_36_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_36_4_0 : List Batch_0_36_4 := [
  ⟨⟨1,0x1e44,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_0_36_4 : List Batch_0_36_4 := ch_0_36_4_0
private noncomputable def lv_0_36_4 : List NodeSpec := flattenBatches fmt_0_36_4 (ch_0_36_4.map Subtype.val)
private theorem ok_0_36_4 : LevelOK rd_0_36 (subGoal 0 36) 4 lv_0_36_4 :=
  @checkedBatches (freeVars 0 36) rd_0_36 _ _ _ sl_0_36 [[]] 4 fmt_0_36_4 [] fmt_0_36_4 pp_0_36 (raw_faithful (freeMask 0 36) p_0_36 q_0_36) sl_0_36_ok (by decide +kernel) (emptyLevelOK rd_0_36 (subGoal 0 36) 3) ch_0_36_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_0_36 : Lower (freeVars 0 36) (subGoal 0 36) 5 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 8, 9), (inputs.getD 1 zero, 0, 2), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 1, 17)]) ok_0_36_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube0_36

section Cube0_40

private def p_0_40 : Nat → Bits
  | 0 => mk128 0xf1b77c27feaef1b7 0x7c27feaef1b77c27
  | 1 => mk128 0x3e3ba0dabf333e3b 0xa0dabf333e3ba0da
  | 2 => mk128 0xcfc3c31cdfc3cfc3 0xc31cdfc3cfc3c31c
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0xffc03e0effc0ffc 0x3e0effc0ffc03e0
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private def q_0_40 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0x4211044a42444211 0x44a42444211044a
  | 2 => mk128 0x1482091424181482 0x914241814820914
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0xa92012a01801a920 0x12a01801a92012a0
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private theorem pp_0_40 : properPairs (subGoal 0 40) (asRow p_0_40) (asRow q_0_40) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_0_40 : List Decor := rawDecor (freeMask 0 40) p_0_40 q_0_40
private def sl_0_40 : List (Sig × Nat) := [(subcube 1 40, 4)]
private theorem sl_0_40_ok : ∀ s ∈ sl_0_40, Slice (freeVars 0 40) (subGoal 0 40) s.1 s.2 := by
  intro s hs
  simp only [sl_0_40, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 1 40) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_1_40
private def fmt_0_40_4 : ChartFormat := ⟨4, 0, 0, 1, 0⟩
private abbrev Batch_0_40_4 := CheckedBatch (freeVars 0 40) rd_0_40 (subGoal 0 40) sl_0_40 [[]] 4 fmt_0_40_4 [] fmt_0_40_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_40_4_0 : List Batch_0_40_4 := [
  ⟨⟨1,0x1e44,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_0_40_4 : List Batch_0_40_4 := ch_0_40_4_0
private noncomputable def lv_0_40_4 : List NodeSpec := flattenBatches fmt_0_40_4 (ch_0_40_4.map Subtype.val)
private theorem ok_0_40_4 : LevelOK rd_0_40 (subGoal 0 40) 4 lv_0_40_4 :=
  @checkedBatches (freeVars 0 40) rd_0_40 _ _ _ sl_0_40 [[]] 4 fmt_0_40_4 [] fmt_0_40_4 pp_0_40 (raw_faithful (freeMask 0 40) p_0_40 q_0_40) sl_0_40_ok (by decide +kernel) (emptyLevelOK rd_0_40 (subGoal 0 40) 3) ch_0_40_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_0_40 : Lower (freeVars 0 40) (subGoal 0 40) 5 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 0, 1), (inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 4 zero, 2, 18)]) ok_0_40_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube0_40

section Cube1_48

private def p_1_48 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0xbecfbecfbecfbecf 0xbecfbecfbecfbecf
  | 2 => mk128 0xdf73df73df73df73 0xdf73df73df73df73
  | 3 => mk128 0xefbcefbcefbcefbc 0xefbcefbcefbcefbc
  | 4 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private def q_1_48 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0x4205420542054205 0x4205420542054205
  | 2 => mk128 0x2412241224122412 0x2412241224122412
  | 3 => mk128 0x1828182818281828 0x1828182818281828
  | 4 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private theorem pp_1_48 : properPairs (subGoal 1 48) (asRow p_1_48) (asRow q_1_48) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_1_48 : List Decor := rawDecor (freeMask 1 48) p_1_48 q_1_48
private def sl_1_48 : List (Sig × Nat) := []
private theorem sl_1_48_ok : ∀ s ∈ sl_1_48, Slice (freeVars 1 48) (subGoal 1 48) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private def fmt_1_48_3 : ChartFormat := ⟨3, 0, 0, 0, 1⟩
private abbrev Batch_1_48_3 := CheckedBatch (freeVars 1 48) rd_1_48 (subGoal 1 48) sl_1_48 [[]] 3 fmt_1_48_3 [] fmt_1_48_3
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_1_48_3_0 : List Batch_1_48_3 := [
  ⟨⟨1,0x243,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_1_48_3 : List Batch_1_48_3 := ch_1_48_3_0
private noncomputable def lv_1_48_3 : List NodeSpec := flattenBatches fmt_1_48_3 (ch_1_48_3.map Subtype.val)
private theorem ok_1_48_3 : LevelOK rd_1_48 (subGoal 1 48) 3 lv_1_48_3 :=
  @checkedBatches (freeVars 1 48) rd_1_48 _ _ _ sl_1_48 [[]] 3 fmt_1_48_3 [] fmt_1_48_3 pp_1_48 (raw_faithful (freeMask 1 48) p_1_48 q_1_48) sl_1_48_ok (by decide +kernel) (emptyLevelOK rd_1_48 (subGoal 1 48) 2) ch_1_48_3
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_1_48 : Lower (freeVars 1 48) (subGoal 1 48) 4 :=
  lower_of_search (xs := [(inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 3 zero, 2, 10)]) ok_1_48_3 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube1_48

section Cube0_48

private def p_0_48 : Nat → Bits
  | 0 => mk128 0xf1b77c27feaef1b7 0x7c27feaef1b77c27
  | 1 => mk128 0x3e3ba0dabf333e3b 0xa0dabf333e3ba0da
  | 2 => mk128 0xcfc3c31cdfc3cfc3 0xc31cdfc3cfc3c31c
  | 3 => mk128 0xffc03e0effc0ffc 0x3e0effc0ffc03e0
  | 4 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private def q_0_48 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0x4211044a42444211 0x44a42444211044a
  | 2 => mk128 0x1482091424181482 0x914241814820914
  | 3 => mk128 0xa92012a01801a920 0x12a01801a92012a0
  | 4 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private theorem pp_0_48 : properPairs (subGoal 0 48) (asRow p_0_48) (asRow q_0_48) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_0_48 : List Decor := rawDecor (freeMask 0 48) p_0_48 q_0_48
private def sl_0_48 : List (Sig × Nat) := [(subcube 1 48, 4)]
private theorem sl_0_48_ok : ∀ s ∈ sl_0_48, Slice (freeVars 0 48) (subGoal 0 48) s.1 s.2 := by
  intro s hs
  simp only [sl_0_48, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 1 48) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_1_48
private def fmt_0_48_4 : ChartFormat := ⟨4, 0, 0, 1, 0⟩
private abbrev Batch_0_48_4 := CheckedBatch (freeVars 0 48) rd_0_48 (subGoal 0 48) sl_0_48 [[]] 4 fmt_0_48_4 [] fmt_0_48_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_48_4_0 : List Batch_0_48_4 := [
  ⟨⟨1,0x1e44,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_0_48_4 : List Batch_0_48_4 := ch_0_48_4_0
private noncomputable def lv_0_48_4 : List NodeSpec := flattenBatches fmt_0_48_4 (ch_0_48_4.map Subtype.val)
private theorem ok_0_48_4 : LevelOK rd_0_48 (subGoal 0 48) 4 lv_0_48_4 :=
  @checkedBatches (freeVars 0 48) rd_0_48 _ _ _ sl_0_48 [[]] 4 fmt_0_48_4 [] fmt_0_48_4 pp_0_48 (raw_faithful (freeMask 0 48) p_0_48 q_0_48) sl_0_48_ok (by decide +kernel) (emptyLevelOK rd_0_48 (subGoal 0 48) 3) ch_0_48_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_0_48 : Lower (freeVars 0 48) (subGoal 0 48) 5 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 0, 1), (inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 3 zero, 2, 10)]) ok_0_48_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube0_48

section Cube8_32

private def p_8_32 : Nat → Bits
  | 0 => mk128 0xbfcffcf8fff873f3 0xbfcffcf8fff873f3
  | 1 => mk128 0xdff39fff1c3ffc9f 0xdff39fff1c3ffc9f
  | 2 => mk128 0xebfc1f3fe03f8f1c 0xebfc1f3fe03f8f1c
  | 3 => mk128 0x0 0x0
  | 4 => mk128 0xf3ffe03fffc00fe0 0xf3ffe03fffc00fe0
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private def q_8_32 : Nat → Bits
  | 0 => mk128 0x4061010824892131 0x4061010824892131
  | 1 => mk128 0x2088281109124486 0x2088281109124486
  | 2 => mk128 0x1523506a42a52b18 0x1523506a42a52b18
  | 3 => mk128 0x0 0x0
  | 4 => mk128 0xe0a1ab493064ec0 0xe0a1ab493064ec0
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private theorem pp_8_32 : properPairs (subGoal 8 32) (asRow p_8_32) (asRow q_8_32) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_8_32 : List Decor := rawDecor (freeMask 8 32) p_8_32 q_8_32
private def sl_8_32 : List (Sig × Nat) := []
private theorem sl_8_32_ok : ∀ s ∈ sl_8_32, Slice (freeVars 8 32) (subGoal 8 32) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private def fmt_8_32_3 : ChartFormat := ⟨4, 0, 0, 0, 1⟩
private abbrev Batch_8_32_3 := CheckedBatch (freeVars 8 32) rd_8_32 (subGoal 8 32) sl_8_32 [[]] 3 fmt_8_32_3 [] fmt_8_32_3
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_8_32_3_0 : List Batch_8_32_3 := [
  ⟨⟨1,0xe44,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_8_32_3 : List Batch_8_32_3 := ch_8_32_3_0
private noncomputable def lv_8_32_3 : List NodeSpec := flattenBatches fmt_8_32_3 (ch_8_32_3.map Subtype.val)
private theorem ok_8_32_3 : LevelOK rd_8_32 (subGoal 8 32) 3 lv_8_32_3 :=
  @checkedBatches (freeVars 8 32) rd_8_32 _ _ _ sl_8_32 [[]] 3 fmt_8_32_3 [] fmt_8_32_3 pp_8_32 (raw_faithful (freeMask 8 32) p_8_32 q_8_32) sl_8_32_ok (by decide +kernel) (emptyLevelOK rd_8_32 (subGoal 8 32) 2) ch_8_32_3
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_8_32 : Lower (freeVars 8 32) (subGoal 8 32) 4 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 2, 6), (inputs.getD 4 zero, 1, 17)]) ok_8_32_3 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube8_32

section Cube16_32

private def p_16_32 : Nat → Bits
  | 0 => mk128 0xbfcffcf8fff873f3 0xbfcffcf8fff873f3
  | 1 => mk128 0xdff39fff1c3ffc9f 0xdff39fff1c3ffc9f
  | 2 => mk128 0xebfc1f3fe03f8f1c 0xebfc1f3fe03f8f1c
  | 3 => mk128 0xf3ffe03fffc00fe0 0xf3ffe03fffc00fe0
  | 4 => mk128 0x0 0x0
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private def q_16_32 : Nat → Bits
  | 0 => mk128 0x4061010824892131 0x4061010824892131
  | 1 => mk128 0x2088281109124486 0x2088281109124486
  | 2 => mk128 0x1523506a42a52b18 0x1523506a42a52b18
  | 3 => mk128 0xe0a1ab493064ec0 0xe0a1ab493064ec0
  | 4 => mk128 0x0 0x0
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private theorem pp_16_32 : properPairs (subGoal 16 32) (asRow p_16_32) (asRow q_16_32) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_16_32 : List Decor := rawDecor (freeMask 16 32) p_16_32 q_16_32
private def sl_16_32 : List (Sig × Nat) := []
private theorem sl_16_32_ok : ∀ s ∈ sl_16_32, Slice (freeVars 16 32) (subGoal 16 32) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private def fmt_16_32_3 : ChartFormat := ⟨4, 0, 0, 0, 1⟩
private abbrev Batch_16_32_3 := CheckedBatch (freeVars 16 32) rd_16_32 (subGoal 16 32) sl_16_32 [[]] 3 fmt_16_32_3 [] fmt_16_32_3
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_16_32_3_0 : List Batch_16_32_3 := [
  ⟨⟨1,0xe44,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_16_32_3 : List Batch_16_32_3 := ch_16_32_3_0
private noncomputable def lv_16_32_3 : List NodeSpec := flattenBatches fmt_16_32_3 (ch_16_32_3.map Subtype.val)
private theorem ok_16_32_3 : LevelOK rd_16_32 (subGoal 16 32) 3 lv_16_32_3 :=
  @checkedBatches (freeVars 16 32) rd_16_32 _ _ _ sl_16_32 [[]] 3 fmt_16_32_3 [] fmt_16_32_3 pp_16_32 (raw_faithful (freeMask 16 32) p_16_32 q_16_32) sl_16_32_ok (by decide +kernel) (emptyLevelOK rd_16_32 (subGoal 16 32) 2) ch_16_32_3
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_16_32 : Lower (freeVars 16 32) (subGoal 16 32) 4 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 2, 6), (inputs.getD 3 zero, 1, 9)]) ok_16_32_3 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube16_32

section Cube0_32

private def p_0_32 : Nat → Bits
  | 0 => mk128 0xfc1ffff1c1e38fc7 0xffe3fff03c09f3f3
  | 1 => mk128 0x3fe1f1fffe03f1f8 0xe0fc707ffc764c9f
  | 2 => mk128 0x3ffe01fe3ffc01ff 0xff807fc3878f1c
  | 3 => mk128 0x3ffffe003ffffe00 0xffff8003f80fe0
  | 4 => mk128 0xc00000003fffffff 0xff00000003fff000
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private def q_0_32 : Nat → Bits
  | 0 => mk128 0x440200200200241 0x2220911088009131
  | 1 => mk128 0x488482a00a019088 0x4444222530324486
  | 2 => mk128 0x9148654054e40152 0xaa9054a89858b18
  | 3 => mk128 0x22154064a74aa400 0x10d24e0312d80ec0
  | 4 => mk128 0x3998989399349a4 0x9c00080c236f6000
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private theorem pp_0_32 : properPairs (subGoal 0 32) (asRow p_0_32) (asRow q_0_32) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_0_32 : List Decor := rawDecor (freeMask 0 32) p_0_32 q_0_32
private def sl_0_32 : List (Sig × Nat) := [(subcube 4 32, 6), (subcube 1 32, 5), (subcube 2 32, 5), (subcube 0 36, 5), (subcube 0 40, 5), (subcube 0 48, 5), (subcube 2 36, 4), (subcube 8 32, 4), (subcube 1 40, 4), (subcube 16 32, 4), (subcube 1 48, 4)]
private theorem sl_0_32_ok : ∀ s ∈ sl_0_32, Slice (freeVars 0 32) (subGoal 0 32) s.1 s.2 := by
  intro s hs
  simp only [sl_0_32, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact slice_correct (ms := fixRows 4 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_4_32
  · exact slice_correct (ms := fixRows 1 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_1_32
  · exact slice_correct (ms := fixRows 2 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_2_32
  · exact slice_correct (ms := fixRows 0 36) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_0_36
  · exact slice_correct (ms := fixRows 0 40) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_0_40
  · exact slice_correct (ms := fixRows 0 48) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_0_48
  · exact slice_correct (ms := fixRows 2 36) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_2_36
  · exact slice_correct (ms := fixRows 8 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_8_32
  · exact slice_correct (ms := fixRows 1 40) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_1_40
  · exact slice_correct (ms := fixRows 16 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_16_32
  · exact slice_correct (ms := fixRows 1 48) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_1_48
private def fmt_0_32_4 : ChartFormat := ⟨5, 4, 0, 1, 4⟩
private abbrev Batch_0_32_4 := CheckedBatch (freeVars 0 32) rd_0_32 (subGoal 0 32) sl_0_32 [[], [swapRows 67]] 4 fmt_0_32_4 [] fmt_0_32_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_32_4_0 : List Batch_0_32_4 := [
  ⟨⟨2,0x2906c2b7ae0120a4836553d700905,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x86a30bc3a05c12436185bf700905,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x870a0a7ba158132b4851651d702e09,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x86a30a7c32e0132b4856151d70ac09,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x86300b7c72e01401438105bc397009,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x10c420be01b5c5682107571bb7029,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x10e40ca7b605c1a682105be71702b,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xc6210abc73601a7206853fb02e0d,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x10a20eae2b46ae04638151d583570,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xa4210bbce26ae06520853e713570,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xa410ca7ce26ee0852105de713770,0x1⟩,by decide +kernel⟩,
  ⟨⟨1,0x528105e5ba7170,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_0_32_4 : List Batch_0_32_4 := ch_0_32_4_0
private noncomputable def lv_0_32_4 : List NodeSpec := flattenBatches fmt_0_32_4 (ch_0_32_4.map Subtype.val)
private theorem ok_0_32_4 : LevelOK rd_0_32 (subGoal 0 32) 4 lv_0_32_4 :=
  @checkedBatches (freeVars 0 32) rd_0_32 _ _ _ sl_0_32 [[], [swapRows 67]] 4 fmt_0_32_4 [] fmt_0_32_4 pp_0_32 (raw_faithful (freeMask 0 32) p_0_32 q_0_32) sl_0_32_ok (by decide +kernel) (emptyLevelOK rd_0_32 (subGoal 0 32) 3) ch_0_32_4

private def fmt_0_32_5 : ChartFormat := ⟨5, 3, 0, 3, 4⟩
private abbrev Batch_0_32_5 := CheckedBatch (freeVars 0 32) rd_0_32 (subGoal 0 32) sl_0_32 [[], [swapRows 67]] 5 fmt_0_32_4 (ch_0_32_4.map Subtype.val) fmt_0_32_5
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_32_5_0 : List Batch_0_32_5 := [
  ⟨⟨2,0x418f53dab8241442202e3d796ac0905,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x18d53db04b81450844e3fa96700905,0x1244⟩,by decide +kernel⟩,
  ⟨⟨2,0x121c0b9daa18e5c01450804e76a96197005,0x12⟩,by decide +kernel⟩,
  ⟨⟨2,0x4688ed76e00a1420301276886b97005,0x226⟩,by decide +kernel⟩,
  ⟨⟨2,0x13b42b1cb8030300a76886b97006,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x23bc86d22e090263a476d02e09,0x42⟩,by decide +kernel⟩,
  ⟨⟨2,0x4808071de436856049524a7a466702e09,0x18c6⟩,by decide +kernel⟩,
  ⟨⟨2,0x2a0d4f710ce1581223a476d2ac09,0x2c2⟩,by decide +kernel⟩,
  ⟨⟨2,0x22ad403277a961970091422ad442034ee95197009,0x2eb09c⟩,by decide +kernel⟩,
  ⟨⟨2,0x8051d23b5db8048302a77486397009,0x34244⟩,by decide +kernel⟩,
  ⟨⟨2,0x131a23b5db8048800a77516197009,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x4645eda05c142322f6d22c0a,0x1⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_32_5_1 : List Batch_0_32_5 := [
  ⟨⟨2,0x2a494e45cce05c1423e456d22e0a,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x3c400e3ab86c50c290067645639700a,0x482⟩,by decide +kernel⟩,
  ⟨⟨2,0x3c45dd443688614e000a34476d60c29,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x47d10d701a521d4476d20c29,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x3a88eda61a523ba886d00d29,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x6674466ac0f290063e886d60f29,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x39f32219c6b0a448506e3e88619ac29,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x234476bb702900677506397029,0x682⟩,by decide +kernel⟩,
  ⟨⟨2,0x23e886b871290e7ea886717029,0x682⟩,by decide +kernel⟩,
  ⟨⟨2,0x47d10c335c5623e886d67229,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x4c88ece55c5627c8860dae2b,0x782⟩,by decide +kernel⟩,
  ⟨⟨2,0x11ae2b628615e000a34786b90c2b,0x1⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_32_5_2 : List Batch_0_32_5 := [
  ⟨⟨2,0x3447ada418563b4456d10c2b,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x10f688ada01a5623e886ba0d2b,0x782⟩,by decide +kernel⟩,
  ⟨⟨2,0xc688edaa1e561a22f6d30d2b,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x67685639702b06676886b9702b,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x23e886ba712b087e445671702b,0xa82⟩,by decide +kernel⟩,
  ⟨⟨2,0xe9147d60d934a18234476d5722b,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x4478cdac5c1a235876cba50c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x54ce88cd605c1a284150906f4465b02e0d,0x2b86⟩,by decide +kernel⟩,
  ⟨⟨2,0x12654476ce300d04656b9619300d,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x12654786ce320d08634476d6300d,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x12655c86ce520d08634786d6320d,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x24a84613e688639b00da0635c86d6520d,0x4b86⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_32_5_3 : List Batch_0_32_5 := [
  ⟨⟨2,0x1f34432cd8068a08b344763bb00d,0xd82⟩,by decide +kernel⟩,
  ⟨⟨2,0x60146b90d8b601c242030127688639b00d,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x404b5e88670312d08634786c1b22c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x6014ed10d70625a376886b0312d,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x404af446670322dc0654786ce322d,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x234786c1b02e08664476d6702d,0x42⟩,by decide +kernel⟩,
  ⟨⟨2,0x404ba235670322e08635c8619b22e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x43111eb6ab9174508a7445619702e,0xc2⟩,by decide +kernel⟩,
  ⟨⟨2,0x2344763a15700863e88619b24e,0x82⟩,by decide +kernel⟩,
  ⟨⟨2,0x3333e432c1ab80300a344761a3570,0x502⟩,by decide +kernel⟩,
  ⟨⟨2,0x23a4765a3570006664765a3570,0x902⟩,by decide +kernel⟩,
  ⟨⟨2,0x21f51199c4ddc0384a0fea886713570,0x4922414⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_32_5_4 : List Batch_0_32_5 := [
  ⟨⟨2,0x80845d44753a7170a07ea886715570,0x92340c⟩,by decide +kernel⟩,
  ⟨⟨1,0x40422c254475ba7170,0x51106⟩,by decide +kernel⟩]
private noncomputable def ch_0_32_5 : List Batch_0_32_5 := ((ch_0_32_5_0 ++ ch_0_32_5_1) ++ (ch_0_32_5_2 ++ (ch_0_32_5_3 ++ ch_0_32_5_4)))
private noncomputable def lv_0_32_5 : List NodeSpec := flattenBatches fmt_0_32_5 (ch_0_32_5.map Subtype.val)
private theorem ok_0_32_5 : LevelOK rd_0_32 (subGoal 0 32) 5 lv_0_32_5 :=
  @checkedBatches (freeVars 0 32) rd_0_32 _ _ _ sl_0_32 [[], [swapRows 67]] 5 fmt_0_32_4 (ch_0_32_4.map Subtype.val) fmt_0_32_5 pp_0_32 (raw_faithful (freeMask 0 32) p_0_32 q_0_32) sl_0_32_ok (by decide +kernel) ok_0_32_4 ch_0_32_5

private def fmt_0_32_6 : ChartFormat := ⟨5, 2, 0, 4, 4⟩
private abbrev Batch_0_32_6 := CheckedBatch (freeVars 0 32) rd_0_32 (subGoal 0 32) sl_0_32 [[], [swapRows 67]] 6 fmt_0_32_5 (ch_0_32_5.map Subtype.val) fmt_0_32_6
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_32_6_0 : List Batch_0_32_6 := [
  ⟨⟨2,0x184081c166442d682101840a00347885a904,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xa2064e20500223d4a84829038c1038344465ae04,0x5f4⟩,by decide +kernel⟩,
  ⟨⟨2,0xa20696488140098e91982814a2069640e205002a3d4860905,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x49038aa0610380151ac4356028e328202b1aa4672e05,0xe2⟩,by decide +kernel⟩,
  ⟨⟨2,0x1240e2a8180f1a233570290388102b1ab887ac05,0xa⟩,by decide +kernel⟩,
  ⟨⟨2,0x28920714408188f2a43b8029038871aa467ae05,0x125bb08⟩,by decide +kernel⟩,
  ⟨⟨2,0x28896488140088c8d582818a2481c61440c205003235886a106,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x51240e28813c79115dc018920718550308102a34706ae06,0x2286⟩,by decide +kernel⟩,
  ⟨⟨2,0x819388158f1aa120e40c1c40a003c7885a907,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x2065540d20600263b886ac092065548c34818263a4662e09,0xb95a1c⟩,by decide +kernel⟩,
  ⟨⟨2,0x92071850c206002a3c886ac092885540d28418263d4867009,0x492e5c10a48⟩,by decide +kernel⟩,
  ⟨⟨2,0x2060c10163c42d0851240e28818300131ea8877009,0x9506⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_32_6_1 : List Batch_0_32_6 := [
  ⟨⟨2,0x20655448180088c8b98b8288195512060022338562c0a,0x2e6c0c⟩,by decide +kernel⟩,
  ⟨⟨2,0x91c61440e206002a3446616292885544a10600263c456700a,0x2e840c⟩,by decide +kernel⟩,
  ⟨⟨2,0x40ca67510e1a52388184080d1d44670c29,0x4924af008⟩,by decide +kernel⟩,
  ⟨⟨2,0x10304048ea23387949038671d44670e29,0x21606⟩,by decide +kernel⟩,
  ⟨⟨2,0xe1840247aa21dc0a491c614388206002a3c886ac29,0x9648781c⟩,by decide +kernel⟩,
  ⟨⟨2,0x24510348ea233b9148a2067a3a8877129,0xaa4b814⟩,by decide +kernel⟩,
  ⟨⟨2,0x91c50c20600223c886ae2b2471440c206002634706a12b,0x497804⟩,by decide +kernel⟩,
  ⟨⟨2,0x40c20126688ae1a5618408091a23570c2b,0x24924466018⟩,by decide +kernel⟩,
  ⟨⟨2,0x30810123445ce1e5640e206100d1a23570e2b,0xae02⟩,by decide +kernel⟩,
  ⟨⟨2,0x1030804d1a22bb8959238a206100f1e4457702b,0x24ae80c⟩,by decide +kernel⟩,
  ⟨⟨2,0x2881e407068d60b4a1820610091a22e7722b,0x9541b80c⟩,by decide +kernel⟩,
  ⟨⟨2,0xe3481038346865a60c2892071640c207002e35886a50c,0x882f06⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_32_6_2 : List Batch_0_32_6 := [
  ⟨⟨2,0x71640705cd10b621838d2060a003c7885a90c,0x683706⟩,by decide +kernel⟩,
  ⟨⟨2,0x103aa246102f2a23317069448f2038334465b20c,0x12881a0ec14⟩,by decide +kernel⟩,
  ⟨⟨2,0x48a2040acad1c1cc03492071440c207002a34466360d,0x1203004⟩,by decide +kernel⟩,
  ⟨⟨2,0x91440d25688cea41a51228892b4467320d,0x920f00c⟩,by decide +kernel⟩,
  ⟨⟨2,0x51240ea881850838019334435806944902438366885b00d,0x92082681a006018⟩,by decide +kernel⟩,
  ⟨⟨2,0x40ea891840bc445cc5c1c40a24382b4465b30d,0x1a00e06⟩,by decide +kernel⟩,
  ⟨⟨2,0x1038812468e15cc038a2481d59030a102a34466b00e,0xc402⟩,by decide +kernel⟩,
  ⟨⟨2,0x81c40d23445cea41c51240e288d1a22e7320e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x308182800d1e216a43ca24510308102235886a50f,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x9207185103081400b8d119ab8b0920718590308102a35886152c,0x1402⟩,by decide +kernel⟩,
  ⟨⟨2,0x40c207120d1919558b491c610308102234466b22c,0x160bc06c04⟩,by decide +kernel⟩,
  ⟨⟨2,0x91c614481a5688ce645a30a205020da56887312d,0xab3901c⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_32_6_3 : List Batch_0_32_6 := [
  ⟨⟨2,0x920710308102266886b02d2071444c285e5c886702d,0x16d39014⟩,by decide +kernel⟩,
  ⟨⟨2,0x3c82040ac68e15e84b8920716410308102a34706a12e,0xe2⟩,by decide +kernel⟩,
  ⟨⟨2,0x1238a204ba34457b12e2470c101634466b02e,0x8c20541a0c⟩,by decide +kernel⟩,
  ⟨⟨2,0xe2881246b115ec8b891c40c207002235886b22e,0x39505e0541e14⟩,by decide +kernel⟩,
  ⟨⟨2,0x40e2889850bcc88ace05c48e28891a2357322e,0x88c60542614⟩,by decide +kernel⟩,
  ⟨⟨2,0x1030a2058366885b12f2071444c285e222e6722e,0x17c02⟩,by decide +kernel⟩,
  ⟨⟨2,0x103081840e0044cd10d645e40c20582e6885b22f,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x91c614308180098d1c1a853881840c206002266886b04d,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x2892079459040c24410366688615702471840c20600263c886b24e,0x368608a0084811428⟩,by decide +kernel⟩,
  ⟨⟨2,0x1238a206102044cd10c6ae040f28b208883133a8871570,0x121a00a0880410428a448⟩,by decide +kernel⟩,
  ⟨⟨2,0x2471440963a88ce6ee048e288120d33a8873570,0x25904100c⟩,by decide +kernel⟩,
  ⟨⟨2,0x207111c175442b8b806800733a8875570,0x4923200204a008⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_32_6_4 : List Batch_0_32_6 := [
  ⟨⟨2,0x2481c40c207002635886a57220510308101e344663671,0x22402⟩,by decide +kernel⟩,
  ⟨⟨1,0x92071440c205002a3c886b272,0x10402⟩,by decide +kernel⟩]
private noncomputable def ch_0_32_6 : List Batch_0_32_6 := ((ch_0_32_6_0 ++ ch_0_32_6_1) ++ (ch_0_32_6_2 ++ (ch_0_32_6_3 ++ ch_0_32_6_4)))
private noncomputable def lv_0_32_6 : List NodeSpec := flattenBatches fmt_0_32_6 (ch_0_32_6.map Subtype.val)
private theorem ok_0_32_6 : LevelOK rd_0_32 (subGoal 0 32) 6 lv_0_32_6 :=
  @checkedBatches (freeVars 0 32) rd_0_32 _ _ _ sl_0_32 [[], [swapRows 67]] 6 fmt_0_32_5 (ch_0_32_5.map Subtype.val) fmt_0_32_6 pp_0_32 (raw_faithful (freeMask 0 32) p_0_32 q_0_32) sl_0_32_ok (by decide +kernel) ok_0_32_5 ch_0_32_6

private def fmt_0_32_7 : ChartFormat := ⟨5, 1, 0, 4, 4⟩
private abbrev Batch_0_32_7 := CheckedBatch (freeVars 0 32) rd_0_32 (subGoal 0 32) sl_0_32 [[], [swapRows 67]] 7 fmt_0_32_6 (ch_0_32_6.map Subtype.val) fmt_0_32_7
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_32_7_0 : List Batch_0_32_7 := [
  ⟨⟨2,0x520c520c41802a3548605520c520c41802a3445604,0x17fe92f490⟩,by decide +kernel⟩,
  ⟨⟨2,0x520c520c41802a3445607520c520c41802a3445606,0x125aa808⟩,by decide +kernel⟩,
  ⟨⟨2,0x520c520c4104c7510c12a41861034748509,0x16bea08448⟩,by decide +kernel⟩,
  ⟨⟨2,0xa418a4104111a22b05a90102464550a,0x2f48042418⟩,by decide +kernel⟩,
  ⟨⟨2,0x520c41034688ac56629062081e3a88629,0x697feb4bffc41f0⟩,by decide +kernel⟩,
  ⟨⟨2,0x290520c418026568860d520e520c41802a344560c,0x924924924a42282cc070⟩,by decide +kernel⟩,
  ⟨⟨2,0x14520c418022344560f520e520c41802a344560e,0x925c4811412a03858⟩,by decide +kernel⟩,
  ⟨⟨2,0x20c520c418026568862d41cc520c41802a346862c,0x4b9246021b823048⟩,by decide +kernel⟩,
  ⟨⟨2,0x20c520c418026344562f41cc520c41802a344562e,0x492e4b930a1c31ca41a0a14b0d0⟩,by decide +kernel⟩,
  ⟨⟨2,0x8398a41882098d11593906290620822568864d,0x49b00430814⟩,by decide +kernel⟩,
  ⟨⟨2,0x20a4188300458d10ce2a4a0e520c41802e3a88670,0x492490426045e02810416810450222110⟩,by decide +kernel⟩,
  ⟨⟨1,0x250520c4180263445672,0xdd03201407814⟩,by decide +kernel⟩]
private noncomputable def ch_0_32_7 : List Batch_0_32_7 := ch_0_32_7_0
private noncomputable def lv_0_32_7 : List NodeSpec := flattenBatches fmt_0_32_7 (ch_0_32_7.map Subtype.val)
private theorem ok_0_32_7 : LevelOK rd_0_32 (subGoal 0 32) 7 lv_0_32_7 :=
  @checkedBatches (freeVars 0 32) rd_0_32 _ _ _ sl_0_32 [[], [swapRows 67]] 7 fmt_0_32_6 (ch_0_32_6.map Subtype.val) fmt_0_32_7 pp_0_32 (raw_faithful (freeMask 0 32) p_0_32 q_0_32) sl_0_32_ok (by decide +kernel) ok_0_32_6 ch_0_32_7

private def fmt_0_32_8 : ChartFormat := ⟨5, 0, 0, 1, 4⟩
private abbrev Batch_0_32_8 := CheckedBatch (freeVars 0 32) rd_0_32 (subGoal 0 32) sl_0_32 [[], [swapRows 67]] 8 fmt_0_32_7 (ch_0_32_7.map Subtype.val) fmt_0_32_8
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_32_8_0 : List Batch_0_32_8 := [
  ⟨⟨1,0xc6885,0x1a5ffffe92492490e0⟩,by decide +kernel⟩]
private noncomputable def ch_0_32_8 : List Batch_0_32_8 := ch_0_32_8_0
private noncomputable def lv_0_32_8 : List NodeSpec := flattenBatches fmt_0_32_8 (ch_0_32_8.map Subtype.val)
private theorem ok_0_32_8 : LevelOK rd_0_32 (subGoal 0 32) 8 lv_0_32_8 :=
  @checkedBatches (freeVars 0 32) rd_0_32 _ _ _ sl_0_32 [[], [swapRows 67]] 8 fmt_0_32_7 (ch_0_32_7.map Subtype.val) fmt_0_32_8 pp_0_32 (raw_faithful (freeMask 0 32) p_0_32 q_0_32) sl_0_32_ok (by decide +kernel) ok_0_32_7 ch_0_32_8
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_0_32 : Lower (freeVars 0 32) (subGoal 0 32) 9 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 2, 6), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 1, 17)]) ok_0_32_8 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube0_32

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_0_16 : Lower (freeVars 0 16) (subGoal 0 16) 9 :=
  lower_map (ms := [swapRows 49, swapRows 84])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide +kernel)) lower_0_32

section Cube4_8

private def p_4_8 : Nat → Bits
  | 0 => mk128 0xbff7fffe3ffff1ff 0xbff7fffe3ffff1ff
  | 1 => mk128 0xd5f8e73fc71c7e93 0xd5f8e73fc71c7e93
  | 2 => mk128 0x0 0x0
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0xe6ff07cff81f8f1c 0xe6ff07cff81f8f1c
  | 5 => mk128 0xf8fff80fffe00fe0 0xf8fff80fffe00fe0
  | _ => 0
private def q_4_8 : Nat → Bits
  | 0 => mk128 0x4010000009040025 0x4010000009040025
  | 1 => mk128 0x2a264a4642496692 0x2a264a4642496692
  | 2 => mk128 0x0 0x0
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0x1942d41a90932b18 0x1942d41a90932b18
  | 5 => mk128 0x78486ad24c24dc0 0x78486ad24c24dc0
  | _ => 0
private theorem pp_4_8 : properPairs (subGoal 4 8) (asRow p_4_8) (asRow q_4_8) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_4_8 : List Decor := rawDecor (freeMask 4 8) p_4_8 q_4_8
private def sl_4_8 : List (Sig × Nat) := []
private theorem sl_4_8_ok : ∀ s ∈ sl_4_8, Slice (freeVars 4 8) (subGoal 4 8) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private def fmt_4_8_3 : ChartFormat := ⟨4, 2, 0, 0, 1⟩
private abbrev Batch_4_8_3 := CheckedBatch (freeVars 4 8) rd_4_8 (subGoal 4 8) sl_4_8 [[]] 3 fmt_4_8_3 [] fmt_4_8_3
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_4_8_3_0 : List Batch_4_8_3 := [
  ⟨⟨2,0x64548a11d212244,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x44548e12a212344,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x64548b15d212205,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x44548f155212305,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x68548621aa12148,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x44548e22a212348,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x68543225aa10c09,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x44548f26a212309,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xa8848d69d810a58,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xa8848d6d521239a,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x6a848532a21239b,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x74848931a15218c,0x1⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_4_8_3_1 : List Batch_4_8_3 := [
  ⟨⟨2,0x6a843035915228c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x74845035a150c8d,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xaa042d71915148d,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x66848a79d21225e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x74848a7dd21225f,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x6a8485bac21136c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x6a8485bdaa121ae,0x1⟩,by decide +kernel⟩,
  ⟨⟨1,0x1aa121af,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_4_8_3 : List Batch_4_8_3 := (ch_4_8_3_0 ++ ch_4_8_3_1)
private noncomputable def lv_4_8_3 : List NodeSpec := flattenBatches fmt_4_8_3 (ch_4_8_3.map Subtype.val)
private theorem ok_4_8_3 : LevelOK rd_4_8 (subGoal 4 8) 3 lv_4_8_3 :=
  @checkedBatches (freeVars 4 8) rd_4_8 _ _ _ sl_4_8 [[]] 3 fmt_4_8_3 [] fmt_4_8_3 pp_4_8 (raw_faithful (freeMask 4 8) p_4_8 q_4_8) sl_4_8_ok (by decide +kernel) (emptyLevelOK rd_4_8 (subGoal 4 8) 2) ch_4_8_3

private def fmt_4_8_4 : ChartFormat := ⟨4, 1, 0, 0, 1⟩
private abbrev Batch_4_8_4 := CheckedBatch (freeVars 4 8) rd_4_8 (subGoal 4 8) sl_4_8 [[]] 4 fmt_4_8_3 (ch_4_8_3.map Subtype.val) fmt_4_8_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_4_8_4_0 : List Batch_4_8_4 := [
  ⟨⟨2,0x1a8428ad11144,0x7f98⟩,by decide +kernel⟩,
  ⟨⟨2,0x1a2228ed11146,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1c44292d11148,0x1fcc18⟩,by decide +kernel⟩,
  ⟨⟨2,0x1a22296d1114a,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1c442b2d18158,0x182⟩,by decide +kernel⟩,
  ⟨⟨2,0x1a222b6d1115a,0x1ca0c⟩,by decide +kernel⟩,
  ⟨⟨2,0x234429ad1114c,0x7f6818⟩,by decide +kernel⟩,
  ⟨⟨2,0x1a2229ed1114e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x23442bad1815c,0xe82⟩,by decide +kernel⟩,
  ⟨⟨2,0x1a222bed1115e,0x1fe0c⟩,by decide +kernel⟩,
  ⟨⟨2,0x23442dad4216c,0x702⟩,by decide +kernel⟩,
  ⟨⟨2,0x1a222ded1116e,0x7240c⟩,by decide +kernel⟩]
private noncomputable def ch_4_8_4 : List Batch_4_8_4 := ch_4_8_4_0
private noncomputable def lv_4_8_4 : List NodeSpec := flattenBatches fmt_4_8_4 (ch_4_8_4.map Subtype.val)
private theorem ok_4_8_4 : LevelOK rd_4_8 (subGoal 4 8) 4 lv_4_8_4 :=
  @checkedBatches (freeVars 4 8) rd_4_8 _ _ _ sl_4_8 [[]] 4 fmt_4_8_3 (ch_4_8_3.map Subtype.val) fmt_4_8_4 pp_4_8 (raw_faithful (freeMask 4 8) p_4_8 q_4_8) sl_4_8_ok (by decide +kernel) ok_4_8_3 ch_4_8_4

private def fmt_4_8_5 : ChartFormat := ⟨4, 0, 0, 0, 1⟩
private abbrev Batch_4_8_5 := CheckedBatch (freeVars 4 8) rd_4_8 (subGoal 4 8) sl_4_8 [[]] 5 fmt_4_8_4 (ch_4_8_4.map Subtype.val) fmt_4_8_5
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_4_8_5_0 : List Batch_4_8_5 := [
  ⟨⟨1,0xe44,0x1ffffff30⟩,by decide +kernel⟩]
private noncomputable def ch_4_8_5 : List Batch_4_8_5 := ch_4_8_5_0
private noncomputable def lv_4_8_5 : List NodeSpec := flattenBatches fmt_4_8_5 (ch_4_8_5.map Subtype.val)
private theorem ok_4_8_5 : LevelOK rd_4_8 (subGoal 4 8) 5 lv_4_8_5 :=
  @checkedBatches (freeVars 4 8) rd_4_8 _ _ _ sl_4_8 [[]] 5 fmt_4_8_4 (ch_4_8_4.map Subtype.val) fmt_4_8_5 pp_4_8 (raw_faithful (freeMask 4 8) p_4_8 q_4_8) sl_4_8_ok (by decide +kernel) ok_4_8_4 ch_4_8_5
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_4_8 : Lower (freeVars 4 8) (subGoal 4 8) 6 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 4 zero, 1, 17), (inputs.getD 5 zero, 1, 33)]) ok_4_8_5 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube4_8

section Cube4_16

private def p_4_16 : Nat → Bits
  | 0 => mk128 0xbff7fffe3ffff1ff 0xbff7fffe3ffff1ff
  | 1 => mk128 0xd5f8e73fc71c7e93 0xd5f8e73fc71c7e93
  | 2 => mk128 0x0 0x0
  | 3 => mk128 0xe6ff07cff81f8f1c 0xe6ff07cff81f8f1c
  | 4 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 5 => mk128 0xf8fff80fffe00fe0 0xf8fff80fffe00fe0
  | _ => 0
private def q_4_16 : Nat → Bits
  | 0 => mk128 0x4010000009040025 0x4010000009040025
  | 1 => mk128 0x2a264a4642496692 0x2a264a4642496692
  | 2 => mk128 0x0 0x0
  | 3 => mk128 0x1942d41a90932b18 0x1942d41a90932b18
  | 4 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 5 => mk128 0x78486ad24c24dc0 0x78486ad24c24dc0
  | _ => 0
private theorem pp_4_16 : properPairs (subGoal 4 16) (asRow p_4_16) (asRow q_4_16) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_4_16 : List Decor := rawDecor (freeMask 4 16) p_4_16 q_4_16
private def sl_4_16 : List (Sig × Nat) := []
private theorem sl_4_16_ok : ∀ s ∈ sl_4_16, Slice (freeVars 4 16) (subGoal 4 16) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private def fmt_4_16_3 : ChartFormat := ⟨4, 2, 0, 0, 1⟩
private abbrev Batch_4_16_3 := CheckedBatch (freeVars 4 16) rd_4_16 (subGoal 4 16) sl_4_16 [[]] 3 fmt_4_16_3 [] fmt_4_16_3
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_4_16_3_0 : List Batch_4_16_3 := [
  ⟨⟨2,0x64548a11d212244,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x44548e12a212344,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x64548b15d212205,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x44548f155212305,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x68548621aa12148,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x44548e22a212348,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x68543225aa10c09,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x44548f26a212309,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xa8848d69d810a58,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xa8848d6d521239a,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x6a848532a21239b,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x74848931a15218c,0x1⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_4_16_3_1 : List Batch_4_16_3 := [
  ⟨⟨2,0x6a843035915228c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x74845035a150c8d,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xaa042d71915148d,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x66848a79d21225e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x74848a7dd21225f,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x6a8485bac21136c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x6a8485bdaa121ae,0x1⟩,by decide +kernel⟩,
  ⟨⟨1,0x1aa121af,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_4_16_3 : List Batch_4_16_3 := (ch_4_16_3_0 ++ ch_4_16_3_1)
private noncomputable def lv_4_16_3 : List NodeSpec := flattenBatches fmt_4_16_3 (ch_4_16_3.map Subtype.val)
private theorem ok_4_16_3 : LevelOK rd_4_16 (subGoal 4 16) 3 lv_4_16_3 :=
  @checkedBatches (freeVars 4 16) rd_4_16 _ _ _ sl_4_16 [[]] 3 fmt_4_16_3 [] fmt_4_16_3 pp_4_16 (raw_faithful (freeMask 4 16) p_4_16 q_4_16) sl_4_16_ok (by decide +kernel) (emptyLevelOK rd_4_16 (subGoal 4 16) 2) ch_4_16_3

private def fmt_4_16_4 : ChartFormat := ⟨4, 1, 0, 0, 1⟩
private abbrev Batch_4_16_4 := CheckedBatch (freeVars 4 16) rd_4_16 (subGoal 4 16) sl_4_16 [[]] 4 fmt_4_16_3 (ch_4_16_3.map Subtype.val) fmt_4_16_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_4_16_4_0 : List Batch_4_16_4 := [
  ⟨⟨2,0x1a8428ad11144,0x7f98⟩,by decide +kernel⟩,
  ⟨⟨2,0x1a2228ed11146,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1c44292d11148,0x1fcc18⟩,by decide +kernel⟩,
  ⟨⟨2,0x1a22296d1114a,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1c442b2d18158,0x182⟩,by decide +kernel⟩,
  ⟨⟨2,0x1a222b6d1115a,0x1ca0c⟩,by decide +kernel⟩,
  ⟨⟨2,0x234429ad1114c,0x7f6818⟩,by decide +kernel⟩,
  ⟨⟨2,0x1a2229ed1114e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x23442bad1815c,0xe82⟩,by decide +kernel⟩,
  ⟨⟨2,0x1a222bed1115e,0x1fe0c⟩,by decide +kernel⟩,
  ⟨⟨2,0x23442dad4216c,0x702⟩,by decide +kernel⟩,
  ⟨⟨2,0x1a222ded1116e,0x7240c⟩,by decide +kernel⟩]
private noncomputable def ch_4_16_4 : List Batch_4_16_4 := ch_4_16_4_0
private noncomputable def lv_4_16_4 : List NodeSpec := flattenBatches fmt_4_16_4 (ch_4_16_4.map Subtype.val)
private theorem ok_4_16_4 : LevelOK rd_4_16 (subGoal 4 16) 4 lv_4_16_4 :=
  @checkedBatches (freeVars 4 16) rd_4_16 _ _ _ sl_4_16 [[]] 4 fmt_4_16_3 (ch_4_16_3.map Subtype.val) fmt_4_16_4 pp_4_16 (raw_faithful (freeMask 4 16) p_4_16 q_4_16) sl_4_16_ok (by decide +kernel) ok_4_16_3 ch_4_16_4

private def fmt_4_16_5 : ChartFormat := ⟨4, 0, 0, 0, 1⟩
private abbrev Batch_4_16_5 := CheckedBatch (freeVars 4 16) rd_4_16 (subGoal 4 16) sl_4_16 [[]] 5 fmt_4_16_4 (ch_4_16_4.map Subtype.val) fmt_4_16_5
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_4_16_5_0 : List Batch_4_16_5 := [
  ⟨⟨1,0xe44,0x1ffffff30⟩,by decide +kernel⟩]
private noncomputable def ch_4_16_5 : List Batch_4_16_5 := ch_4_16_5_0
private noncomputable def lv_4_16_5 : List NodeSpec := flattenBatches fmt_4_16_5 (ch_4_16_5.map Subtype.val)
private theorem ok_4_16_5 : LevelOK rd_4_16 (subGoal 4 16) 5 lv_4_16_5 :=
  @checkedBatches (freeVars 4 16) rd_4_16 _ _ _ sl_4_16 [[]] 5 fmt_4_16_4 (ch_4_16_4.map Subtype.val) fmt_4_16_5 pp_4_16 (raw_faithful (freeMask 4 16) p_4_16 q_4_16) sl_4_16_ok (by decide +kernel) ok_4_16_4 ch_4_16_5
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_4_16 : Lower (freeVars 4 16) (subGoal 4 16) 6 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 3 zero, 1, 9), (inputs.getD 5 zero, 1, 33)]) ok_4_16_5 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube4_16

section Cube6_1

private def p_6_1 : Nat → Bits
  | 0 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0x0 0x0
  | 3 => mk128 0xbecfbecfbecfbecf 0xbecfbecfbecfbecf
  | 4 => mk128 0xdf73df73df73df73 0xdf73df73df73df73
  | 5 => mk128 0xefbcefbcefbcefbc 0xefbcefbcefbcefbc
  | _ => 0
private def q_6_1 : Nat → Bits
  | 0 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0x0 0x0
  | 3 => mk128 0x4205420542054205 0x4205420542054205
  | 4 => mk128 0x2412241224122412 0x2412241224122412
  | 5 => mk128 0x1828182818281828 0x1828182818281828
  | _ => 0
private theorem pp_6_1 : properPairs (subGoal 6 1) (asRow p_6_1) (asRow q_6_1) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_6_1 : List Decor := rawDecor (freeMask 6 1) p_6_1 q_6_1
private def sl_6_1 : List (Sig × Nat) := []
private theorem sl_6_1_ok : ∀ s ∈ sl_6_1, Slice (freeVars 6 1) (subGoal 6 1) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private def fmt_6_1_3 : ChartFormat := ⟨3, 0, 0, 0, 1⟩
private abbrev Batch_6_1_3 := CheckedBatch (freeVars 6 1) rd_6_1 (subGoal 6 1) sl_6_1 [[]] 3 fmt_6_1_3 [] fmt_6_1_3
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_6_1_3_0 : List Batch_6_1_3 := [
  ⟨⟨1,0x243,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_6_1_3 : List Batch_6_1_3 := ch_6_1_3_0
private noncomputable def lv_6_1_3 : List NodeSpec := flattenBatches fmt_6_1_3 (ch_6_1_3.map Subtype.val)
private theorem ok_6_1_3 : LevelOK rd_6_1 (subGoal 6 1) 3 lv_6_1_3 :=
  @checkedBatches (freeVars 6 1) rd_6_1 _ _ _ sl_6_1 [[]] 3 fmt_6_1_3 [] fmt_6_1_3 pp_6_1 (raw_faithful (freeMask 6 1) p_6_1 q_6_1) sl_6_1_ok (by decide +kernel) (emptyLevelOK rd_6_1 (subGoal 6 1) 2) ch_6_1_3
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_6_1 : Lower (freeVars 6 1) (subGoal 6 1) 4 :=
  lower_of_search (xs := [(inputs.getD 3 zero, 16, 24), (inputs.getD 4 zero, 8, 24), (inputs.getD 5 zero, 8, 40)]) ok_6_1_3 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube6_1

section Cube4_1

private def p_4_1 : Nat → Bits
  | 0 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 1 => mk128 0xf1b77c27feaef1b7 0x7c27feaef1b77c27
  | 2 => mk128 0x0 0x0
  | 3 => mk128 0x3e3ba0dabf333e3b 0xa0dabf333e3ba0da
  | 4 => mk128 0xcfc3c31cdfc3cfc3 0xc31cdfc3cfc3c31c
  | 5 => mk128 0xffc03e0effc0ffc 0x3e0effc0ffc03e0
  | _ => 0
private def q_4_1 : Nat → Bits
  | 0 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0x0 0x0
  | 3 => mk128 0x4211044a42444211 0x44a42444211044a
  | 4 => mk128 0x1482091424181482 0x914241814820914
  | 5 => mk128 0xa92012a01801a920 0x12a01801a92012a0
  | _ => 0
private theorem pp_4_1 : properPairs (subGoal 4 1) (asRow p_4_1) (asRow q_4_1) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_4_1 : List Decor := rawDecor (freeMask 4 1) p_4_1 q_4_1
private def sl_4_1 : List (Sig × Nat) := [(subcube 6 1, 4)]
private theorem sl_4_1_ok : ∀ s ∈ sl_4_1, Slice (freeVars 4 1) (subGoal 4 1) s.1 s.2 := by
  intro s hs
  simp only [sl_4_1, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 6 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_6_1
private def fmt_4_1_4 : ChartFormat := ⟨4, 0, 0, 1, 0⟩
private abbrev Batch_4_1_4 := CheckedBatch (freeVars 4 1) rd_4_1 (subGoal 4 1) sl_4_1 [[]] 4 fmt_4_1_4 [] fmt_4_1_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_4_1_4_0 : List Batch_4_1_4 := [
  ⟨⟨1,0x1e44,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_4_1_4 : List Batch_4_1_4 := ch_4_1_4_0
private noncomputable def lv_4_1_4 : List NodeSpec := flattenBatches fmt_4_1_4 (ch_4_1_4.map Subtype.val)
private theorem ok_4_1_4 : LevelOK rd_4_1 (subGoal 4 1) 4 lv_4_1_4 :=
  @checkedBatches (freeVars 4 1) rd_4_1 _ _ _ sl_4_1 [[]] 4 fmt_4_1_4 [] fmt_4_1_4 pp_4_1 (raw_faithful (freeMask 4 1) p_4_1 q_4_1) sl_4_1_ok (by decide +kernel) (emptyLevelOK rd_4_1 (subGoal 4 1) 3) ch_4_1_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_4_1 : Lower (freeVars 4 1) (subGoal 4 1) 5 :=
  lower_of_search (xs := [(inputs.getD 1 zero, 0, 2), (inputs.getD 3 zero, 16, 24), (inputs.getD 4 zero, 8, 24), (inputs.getD 5 zero, 8, 40)]) ok_4_1_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube4_1

section Cube6_0

private def p_6_0 : Nat → Bits
  | 0 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0x0 0x0
  | 3 => mk128 0xffc3fe3fbf0fffc3 0xfe3fbf0fffc3fe3f
  | 4 => mk128 0xfffc3fc7dff0fffc 0x3fc7dff0fffc3fc7
  | 5 => mk128 0xfffc3f8efff0fff 0xc3f8efff0fffc3f8
  | _ => 0
private def q_6_0 : Nat → Bits
  | 0 => mk128 0x22c444db012222c4 0x44db012222c444db
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0x0 0x0
  | 3 => mk128 0x4562aa2d42e44562 0xaa2d42e44562aa2d
  | 4 => mk128 0x89aa3346244e89aa 0x3346244e89aa3346
  | 5 => mk128 0xee3323b01888ee33 0x23b01888ee3323b0
  | _ => 0
private theorem pp_6_0 : properPairs (subGoal 6 0) (asRow p_6_0) (asRow q_6_0) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_6_0 : List Decor := rawDecor (freeMask 6 0) p_6_0 q_6_0
private def sl_6_0 : List (Sig × Nat) := [(subcube 6 1, 4)]
private theorem sl_6_0_ok : ∀ s ∈ sl_6_0, Slice (freeVars 6 0) (subGoal 6 0) s.1 s.2 := by
  intro s hs
  simp only [sl_6_0, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 6 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_6_1
private def fmt_6_0_4 : ChartFormat := ⟨4, 0, 0, 1, 0⟩
private abbrev Batch_6_0_4 := CheckedBatch (freeVars 6 0) rd_6_0 (subGoal 6 0) sl_6_0 [[]] 4 fmt_6_0_4 [] fmt_6_0_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_6_0_4_0 : List Batch_6_0_4 := [
  ⟨⟨1,0x1e44,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_6_0_4 : List Batch_6_0_4 := ch_6_0_4_0
private noncomputable def lv_6_0_4 : List NodeSpec := flattenBatches fmt_6_0_4 (ch_6_0_4.map Subtype.val)
private theorem ok_6_0_4 : LevelOK rd_6_0 (subGoal 6 0) 4 lv_6_0_4 :=
  @checkedBatches (freeVars 6 0) rd_6_0 _ _ _ sl_6_0 [[]] 4 fmt_6_0_4 [] fmt_6_0_4 pp_6_0 (raw_faithful (freeMask 6 0) p_6_0 q_6_0) sl_6_0_ok (by decide +kernel) (emptyLevelOK rd_6_0 (subGoal 6 0) 3) ch_6_0_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_6_0 : Lower (freeVars 6 0) (subGoal 6 0) 5 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 24, 25), (inputs.getD 3 zero, 17, 25), (inputs.getD 4 zero, 9, 25), (inputs.getD 5 zero, 9, 41)]) ok_6_0_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube6_0

section Cube4_0

private def p_4_0 : Nat → Bits
  | 0 => mk128 0xfffffffffe07ffff 0xfffffffffe1fffff
  | 1 => mk128 0xff81fffffff81f07 0xc1ff83ffffe88e3f
  | 2 => mk128 0x0 0x0
  | 3 => mk128 0x3ffe03f81fffe007 0xfe0ffc1f01f0f3cc
  | 4 => mk128 0x3ffffc001ffffff8 0xfffe001ff03f0
  | 5 => mk128 0xc00000001fffffff 0xfff0000001fffc00
  | _ => 0
private def q_4_0 : Nat → Bits
  | 0 => mk128 0x8090489000016509 0x42128421540334d5
  | 1 => mk128 0x190c91268e580a42 0x91a5235aa8e88a2a
  | 2 => mk128 0x0 0x0
  | 3 => mk128 0xaa243a42b6aaa084 0xf489e91c0d70d34c
  | 4 => mk128 0x34492074db34d3d0 0x210e738831bd03b0
  | 5 => mk128 0x3871c3871dc71ce7 0x39c04210c1deec00
  | _ => 0
private theorem pp_4_0 : properPairs (subGoal 4 0) (asRow p_4_0) (asRow q_4_0) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_4_0 : List Decor := rawDecor (freeMask 4 0) p_4_0 q_4_0
private def sl_4_0 : List (Sig × Nat) := [(subcube 4 8, 6), (subcube 4 16, 6), (subcube 4 32, 6), (subcube 4 1, 5), (subcube 6 0, 5), (subcube 6 1, 4)]
private theorem sl_4_0_ok : ∀ s ∈ sl_4_0, Slice (freeVars 4 0) (subGoal 4 0) s.1 s.2 := by
  intro s hs
  simp only [sl_4_0, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · exact slice_correct (ms := fixRows 4 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_4_8
  · exact slice_correct (ms := fixRows 4 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_4_16
  · exact slice_correct (ms := fixRows 4 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_4_32
  · exact slice_correct (ms := fixRows 4 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_4_1
  · exact slice_correct (ms := fixRows 6 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_6_0
  · exact slice_correct (ms := fixRows 6 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_6_1
private def fmt_4_0_3 : ChartFormat := ⟨5, 5, 0, 0, 3⟩
private abbrev Batch_4_0_3 := CheckedBatch (freeVars 4 0) rd_4_0 (subGoal 4 0) sl_4_0 [[], [swapRows 84], [swapRows 67], [swapRows 83, swapRows 67], [swapRows 67, swapRows 83], [swapRows 83]] 3 fmt_4_0_3 [] fmt_4_0_3
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_4_0_3_0 : List Batch_4_0_3 := [
  ⟨⟨1,0x261c10d050c5ac08,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_4_0_3 : List Batch_4_0_3 := ch_4_0_3_0
private noncomputable def lv_4_0_3 : List NodeSpec := flattenBatches fmt_4_0_3 (ch_4_0_3.map Subtype.val)
private theorem ok_4_0_3 : LevelOK rd_4_0 (subGoal 4 0) 3 lv_4_0_3 :=
  @checkedBatches (freeVars 4 0) rd_4_0 _ _ _ sl_4_0 [[], [swapRows 84], [swapRows 67], [swapRows 83, swapRows 67], [swapRows 67, swapRows 83], [swapRows 83]] 3 fmt_4_0_3 [] fmt_4_0_3 pp_4_0 (raw_faithful (freeMask 4 0) p_4_0 q_4_0) sl_4_0_ok (by decide +kernel) (emptyLevelOK rd_4_0 (subGoal 4 0) 2) ch_4_0_3

private def fmt_4_0_4 : ChartFormat := ⟨5, 4, 0, 1, 3⟩
private abbrev Batch_4_0_4 := CheckedBatch (freeVars 4 0) rd_4_0 (subGoal 4 0) sl_4_0 [[], [swapRows 84], [swapRows 67], [swapRows 83, swapRows 67], [swapRows 67, swapRows 83], [swapRows 83]] 4 fmt_4_0_3 (ch_4_0_3.map Subtype.val) fmt_4_0_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_4_0_4_0 : List Batch_4_0_4 := [
  ⟨⟨2,0x6500abe5985408432805f5cc2a04,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x870c0a7b99500a438065bd4c2a04,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x86500a7b99500a4836053d70a805,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x64210be599540c4386053d4ca805,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x6500abe598540e328105f2cca807,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x86e10b958b581043870550c5ac08,0x32⟩,by decide +kernel⟩,
  ⟨⟨2,0x64e10ba58b5810832705d1c5ac08,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x6410eba58d5810832075d1c6ac08,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x86500bcba15810831075d1caac08,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xb0e20cae0a15810431085ead0ac08,0x32⟩,by decide +kernel⟩,
  ⟨⟨2,0x690c20b7ae098104817054cd52e08,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x86300bd5a15c50432805e5d0ae0a,0x1⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_4_0_4_1 : List Batch_4_0_4 := [
  ⟨⟨2,0x6e500ba58b5854437805cac5ac2a,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xb0e20cae0a15854831705d1caac2a,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x4860553d704c2a03486105bd704c2a,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x65020be18a2e98432185de15144c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x86410bbc6a68988710657050174c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x10ce20ae0a06a98321085f218354c,0x1⟩,by decide +kernel⟩,
  ⟨⟨1,0x328075d237364c,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_4_0_4 : List Batch_4_0_4 := (ch_4_0_4_0 ++ ch_4_0_4_1)
private noncomputable def lv_4_0_4 : List NodeSpec := flattenBatches fmt_4_0_4 (ch_4_0_4.map Subtype.val)
private theorem ok_4_0_4 : LevelOK rd_4_0 (subGoal 4 0) 4 lv_4_0_4 :=
  @checkedBatches (freeVars 4 0) rd_4_0 _ _ _ sl_4_0 [[], [swapRows 84], [swapRows 67], [swapRows 83, swapRows 67], [swapRows 67, swapRows 83], [swapRows 83]] 4 fmt_4_0_3 (ch_4_0_3.map Subtype.val) fmt_4_0_4 pp_4_0 (raw_faithful (freeMask 4 0) p_4_0 q_4_0) sl_4_0_ok (by decide +kernel) ok_4_0_3 ch_4_0_4

private def fmt_4_0_5 : ChartFormat := ⟨5, 3, 0, 3, 3⟩
private abbrev Batch_4_0_5 := CheckedBatch (freeVars 4 0) rd_4_0 (subGoal 4 0) sl_4_0 [[], [swapRows 84], [swapRows 67], [swapRows 83, swapRows 67], [swapRows 67, swapRows 83], [swapRows 83]] 5 fmt_4_0_4 (ch_4_0_4.map Subtype.val) fmt_4_0_5
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_4_0_5_0 : List Batch_4_0_5 := [
  ⟨⟨2,0x1191f367550232632376ccaa04,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x2831a23b6655023263e46670aa04,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x131f23326550232634476ceaa04,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x11a17b66150200635c66d52a04,0x536⟩,by decide +kernel⟩,
  ⟨⟨2,0x47c5cc985408235c56ce2a04,0x2c2⟩,by decide +kernel⟩,
  ⟨⟨2,0x51951ee4366540287400e3e886b94c04,0x22b04⟩,by decide +kernel⟩,
  ⟨⟨2,0x146547f10ce1500a23c476cea805,0xa82⟩,by decide +kernel⟩,
  ⟨⟨2,0x1931a23b675402d0635c86cca805,0x302⟩,by decide +kernel⟩,
  ⟨⟨2,0x47d50c72980aa02a3f8864ca805,0x89ba0c⟩,by decide +kernel⟩,
  ⟨⟨2,0x409468f0d99540d400a34476bb4c05,0x1b02⟩,by decide +kernel⟩,
  ⟨⟨2,0x4c7ce0c99540c234476ceaa06,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x47d0ac72980c23e886b94c06,0x32⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_4_0_5_1 : List Batch_4_0_5 := [
  ⟨⟨2,0x31ae3362d403806347e6c2a807,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x11ae4367540384634476cca807,0x140306⟩,by decide +kernel⟩,
  ⟨⟨2,0x2431afab6115038263e4664ca807,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x11ae2b671503866343d6cc2a07,0x3302⟩,by decide +kernel⟩,
  ⟨⟨2,0x4688ed76980e23e3564c2a07,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xcc688ed9d4a10235c86cca508,0x302⟩,by decide +kernel⟩,
  ⟨⟨2,0x31a37b61538418c82e3f8864ca508,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xc68eed855810234476c2ac08,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x8d721b16b0229c146b85c5ac08,0xbb06⟩,by decide +kernel⟩,
  ⟨⟨2,0x11a1bb63560408635c66c5ac08,0xa529442803008⟩,by decide +kernel⟩,
  ⟨⟨2,0x431a23b68560400632376caac08,0x1c9c740381c⟩,by decide +kernel⟩,
  ⟨⟨2,0x688eba558103b4466d1ac08,0x3c25120b814⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_4_0_5_2 : List Batch_4_0_5 := [
  ⟨⟨2,0x8b446eda55810234476d2ac08,0x484606⟩,by decide +kernel⟩,
  ⟨⟨2,0x31a37b6156040463e46650ac08,0x1883b06⟩,by decide +kernel⟩,
  ⟨⟨2,0x31917b65560452635c56c5ac08,0x1602⟩,by decide +kernel⟩,
  ⟨⟨2,0x46b90d8b5c101a22f6d2ac08,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x2931a23b685704086223762eae08,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1a0947c8cca15c10234476d2ae08,0xc602⟩,by decide +kernel⟩,
  ⟨⟨2,0x405391ab260604026722e64cae08,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x10c688edac5c10234786d52e08,0xe602⟩,by decide +kernel⟩,
  ⟨⟨2,0x4053917326170406633c56ca2e08,0xe602⟩,by decide +kernel⟩,
  ⟨⟨2,0x478dec36981023f8d6194c08,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x11917b6926040663e456d04c08,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x30a9064ed10d72e01027c456704c08,0x2636804⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_4_0_5_3 : List Batch_4_0_5 := [
  ⟨⟨2,0x10c68f0da15c14234476bb7008,0x110ba06⟩,by decide +kernel⟩,
  ⟨⟨2,0x8ce8e0ce15c14234476d2ae0a,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x4645ecb6e014276886b9700a,0xba02⟩,by decide +kernel⟩,
  ⟨⟨2,0x11a3c369571400634476d0ae28,0x6402⟩,by decide +kernel⟩,
  ⟨⟨2,0x13b4435cb8140467446670ae28,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x4668ecb6e050276a86397028,0x6402⟩,by decide +kernel⟩,
  ⟨⟨2,0x11a23b67511500635c56c5a02a,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x11a23b6156150263e4664ca22a,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xc7d0cd8b585423e886c5ac2a,0xa223004⟩,by decide +kernel⟩,
  ⟨⟨2,0x11a23b68561500633c66caac2a,0x91e19014⟩,by decide +kernel⟩,
  ⟨⟨2,0x6b90ba558543b4466d1ac2a,0x1585e0420314⟩,by decide +kernel⟩,
  ⟨⟨2,0x8b5c8cda55854235c86d2ac2a,0xcc02⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_4_0_5_4 : List Batch_4_0_5 := [
  ⟨⟨2,0x31f42b62d6150463e46650ac2a,0x1409c06⟩,by decide +kernel⟩,
  ⟨⟨2,0xd722b69561500633c56caac2a,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x290146b90da15c542344761bae2a,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1a0947f10ca15c54234476d2ae2a,0x7c02⟩,by decide +kernel⟩,
  ⟨⟨2,0x405391ab2617150267c4564cae2a,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x4785ec76985423f856394c2a,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x11917b6926150863e456d04c2a,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x40a9064ed10d72e05427c456704c2a,0xce4d00c⟩,by decide +kernel⟩,
  ⟨⟨2,0xced0ac72e054234476bb702a,0x57c06⟩,by decide +kernel⟩,
  ⟨⟨2,0x3031aa3b630a2660635786c5144c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xc748ed94289823e8e615144c,0x1bc02⟩,by decide +kernel⟩,
  ⟨⟨2,0x3031abc31c0aa6605aa476d2144c,0x1⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_4_0_5_5 : List Batch_4_0_5 := [
  ⟨⟨2,0x302faa43680aa6606354763a154c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x468eec2e2c98204a34476d6164c,0x5808c00c04⟩,by decide +kernel⟩,
  ⟨⟨2,0x204071ae43628ba60063a476ca164c,0x1ec02⟩,by decide +kernel⟩,
  ⟨⟨2,0x8c7c8cca02e9823e886d2174c,0x21c02⟩,by decide +kernel⟩,
  ⟨⟨2,0x3031f5831a9a2604634476d6344c,0x19808406⟩,by decide +kernel⟩,
  ⟨⟨2,0x204071a23b0c1aa60063a476ca344c,0xba00306⟩,by decide +kernel⟩,
  ⟨⟨2,0x11f443681aa60463dc8650354c,0x3819406⟩,by decide +kernel⟩,
  ⟨⟨2,0xc74f0d946c9823437637364c,0x2862023004⟩,by decide +kernel⟩,
  ⟨⟨2,0x302faa43691ba6605abc86d2364c,0x500cc06⟩,by decide +kernel⟩,
  ⟨⟨2,0x47d10c7360982344761bb04c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x31d23b6558260063c476cab04c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x46b90d8b6498234476c2b24c,0x1d0ca06⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_4_0_5_6 : List Batch_4_0_5 := [
  ⟨⟨2,0x1220c005fa90ae0a0981009fa46650b24c,0x2f85b82b605d6058⟩,by decide +kernel⟩]
private noncomputable def ch_4_0_5 : List Batch_4_0_5 := ((ch_4_0_5_0 ++ (ch_4_0_5_1 ++ ch_4_0_5_2)) ++ ((ch_4_0_5_3 ++ ch_4_0_5_4) ++ (ch_4_0_5_5 ++ ch_4_0_5_6)))
private noncomputable def lv_4_0_5 : List NodeSpec := flattenBatches fmt_4_0_5 (ch_4_0_5.map Subtype.val)
private theorem ok_4_0_5 : LevelOK rd_4_0 (subGoal 4 0) 5 lv_4_0_5 :=
  @checkedBatches (freeVars 4 0) rd_4_0 _ _ _ sl_4_0 [[], [swapRows 84], [swapRows 67], [swapRows 83, swapRows 67], [swapRows 67, swapRows 83], [swapRows 83]] 5 fmt_4_0_4 (ch_4_0_4.map Subtype.val) fmt_4_0_5 pp_4_0 (raw_faithful (freeMask 4 0) p_4_0 q_4_0) sl_4_0_ok (by decide +kernel) ok_4_0_4 ch_4_0_5

private def fmt_4_0_6 : ChartFormat := ⟨5, 2, 0, 4, 3⟩
private abbrev Batch_4_0_6 := CheckedBatch (freeVars 4 0) rd_4_0 (subGoal 4 0) sl_4_0 [[], [swapRows 84], [swapRows 67], [swapRows 83, swapRows 67], [swapRows 67, swapRows 83], [swapRows 83]] 6 fmt_4_0_5 (ch_4_0_5.map Subtype.val) fmt_4_0_6
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_4_0_6_0 : List Batch_4_0_6 := [
  ⟨⟨2,0x524c7a16428054688cd5408524f594346465aa04,0xb3bca59c8⟩,by decide +kernel⟩,
  ⟨⟨2,0x920a00b1ac4574c0429263401a342e62a04,0xa6cef189462868⟩,by decide +kernel⟩,
  ⟨⟨2,0x2d07a1642804c6b10d500a5a0f594347885a805,0xb3bca590e048⟩,by decide +kernel⟩,
  ⟨⟨2,0x10620a00d1a383550310720a00d1ad4874c05,0x59da52894652058⟩,by decide +kernel⟩,
  ⟨⟨2,0xb49882868d119aa01c830a00b1ac4574c06,0x2cef28ca5128d6068⟩,by decide +kernel⟩,
  ⟨⟨2,0xa40a00b1ac4574c0729263401a343562a07,0x536778c4a0fc058⟩,by decide +kernel⟩,
  ⟨⟨2,0xa498c0b1ac457a5082b263d0b21802a35886a508,0x2cb3580c4008⟩,by decide +kernel⟩,
  ⟨⟨2,0x824c1234466ac08292671a22e7a708,0x894a531844a5294a70181c310070⟩,by decide +kernel⟩,
  ⟨⟨2,0x9a1243003c688cd5c105524291a22e7ac08,0x519ca508a944418829c058⟩,by decide +kernel⟩,
  ⟨⟨2,0x1800e3446ae18103484091a22e7ae08,0x422054802e014⟩,by decide +kernel⟩,
  ⟨⟨2,0x1834840b1e22b260404051a22e72e08,0x1467294a528410c380e05605150283f0070⟩,by decide +kernel⟩,
  ⟨⟨2,0x14831243004468e0d5c142484091e44577008,0x5194a52e028088370148058⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_4_0_6_1 : List Batch_4_0_6 := [
  ⟨⟨2,0x290624860088d119ab8a0624840b1e4457700a,0x1465294b8b88018⟩,by decide +kernel⟩,
  ⟨⟨2,0xb419c688b9e80a8824840b1e46877028,0x5294a5c2240094018⟩,by decide +kernel⟩,
  ⟨⟨2,0xb420e0068d11abd115168458c41802634466a22a,0x1640c066c074094018⟩,by decide +kernel⟩,
  ⟨⟨2,0x14909c688b9eb0a8624c1234466ac2a,0x14a111294a630894a2b402219406c070⟩,by decide +kernel⟩,
  ⟨⟨2,0x8908123588af5c543d0921801e35886ae2a,0x29467144203901485002a023048⟩,by decide +kernel⟩,
  ⟨⟨2,0x116908163c4564c2a0c0071a23572e2a,0x146728410cd8271d83c81220221940bc030⟩,by decide +kernel⟩,
  ⟨⟨2,0x6a81c6a919c5130824840b1e4457702a,0x28894a7294a5c2a0c86e07700db0050⟩,by decide +kernel⟩,
  ⟨⟨2,0x38146a919c59306a0c00b1e5487154c,0x11294a50a0590049a033c048⟩,by decide +kernel⟩,
  ⟨⟨2,0x30c0091aa467174c20a21801a34466174c,0x44a48a14c003024d004824c048⟩,by decide +kernel⟩,
  ⟨⟨2,0xc510c00d1e4431aa612051aa707344c,0xa2251128bc0a0d803c05300e4048298010⟩,by decide +kernel⟩,
  ⟨⟨2,0x4540e3548ce6c9840c0091e5487354c,0x5113a02a014900330018⟩,by decide +kernel⟩,
  ⟨⟨2,0x41aa3058d621ac1308a0c00b1aa467374c,0x72a18281980e626e02c3581c1a00520070⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_4_0_6_2 : List Batch_4_0_6 := [
  ⟨⟨2,0x41aa21801e34466b24c50a071ab887b04c,0xa5154402c11780241d05829f8068⟩,by decide +kernel⟩,
  ⟨⟨2,0xa1442058f52194131420c00b1aa467b24c,0x319c2907618e055813301e604b60050⟩,by decide +kernel⟩]
private noncomputable def ch_4_0_6 : List Batch_4_0_6 := (ch_4_0_6_0 ++ (ch_4_0_6_1 ++ ch_4_0_6_2))
private noncomputable def lv_4_0_6 : List NodeSpec := flattenBatches fmt_4_0_6 (ch_4_0_6.map Subtype.val)
private theorem ok_4_0_6 : LevelOK rd_4_0 (subGoal 4 0) 6 lv_4_0_6 :=
  @checkedBatches (freeVars 4 0) rd_4_0 _ _ _ sl_4_0 [[], [swapRows 84], [swapRows 67], [swapRows 83, swapRows 67], [swapRows 67, swapRows 83], [swapRows 83]] 6 fmt_4_0_5 (ch_4_0_5.map Subtype.val) fmt_4_0_6 pp_4_0 (raw_faithful (freeMask 4 0) p_4_0 q_4_0) sl_4_0_ok (by decide +kernel) ok_4_0_5 ch_4_0_6

private def fmt_4_0_7 : ChartFormat := ⟨5, 1, 0, 4, 3⟩
private abbrev Batch_4_0_7 := CheckedBatch (freeVars 4 0) rd_4_0 (subGoal 4 0) sl_4_0 [[], [swapRows 84], [swapRows 67], [swapRows 83, swapRows 67], [swapRows 67, swapRows 83], [swapRows 83]] 7 fmt_4_0_6 (ch_4_0_6.map Subtype.val) fmt_4_0_7
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_4_0_7_0 : List Batch_4_0_7 := [
  ⟨⟨2,0x543a2918098d52181550e8a460263445604,0x1772e4bb972e4d0⟩,by decide +kernel⟩,
  ⟨⟨2,0x543a2918098d11581d0e8a460223445606,0x5dcb92ee64010⟩,by decide +kernel⟩,
  ⟨⟨2,0x543a291088d11582950e8a44223445608,0x14b296779659de52850c40f0⟩,by decide +kernel⟩,
  ⟨⟨2,0x543a291088d1158a950e8a44223468628,0x53bcb2cef294a5370f60a2a0d130⟩,by decide +kernel⟩,
  ⟨⟨1,0x10e8841a354864c,0x665298c5294a5294a5318590584890610a088142414161f0⟩,by decide +kernel⟩]
private noncomputable def ch_4_0_7 : List Batch_4_0_7 := ch_4_0_7_0
private noncomputable def lv_4_0_7 : List NodeSpec := flattenBatches fmt_4_0_7 (ch_4_0_7.map Subtype.val)
private theorem ok_4_0_7 : LevelOK rd_4_0 (subGoal 4 0) 7 lv_4_0_7 :=
  @checkedBatches (freeVars 4 0) rd_4_0 _ _ _ sl_4_0 [[], [swapRows 84], [swapRows 67], [swapRows 83, swapRows 67], [swapRows 67, swapRows 83], [swapRows 83]] 7 fmt_4_0_6 (ch_4_0_6.map Subtype.val) fmt_4_0_7 pp_4_0 (raw_faithful (freeMask 4 0) p_4_0 q_4_0) sl_4_0_ok (by decide +kernel) ok_4_0_6 ch_4_0_7

private def fmt_4_0_8 : ChartFormat := ⟨5, 0, 0, 2, 3⟩
private abbrev Batch_4_0_8 := CheckedBatch (freeVars 4 0) rd_4_0 (subGoal 4 0) sl_4_0 [[], [swapRows 84], [swapRows 67], [swapRows 83, swapRows 67], [swapRows 67, swapRows 83], [swapRows 83]] 8 fmt_4_0_7 (ch_4_0_7.map Subtype.val) fmt_4_0_8
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_4_0_8_0 : List Batch_4_0_8 := [
  ⟨⟨1,0x111c6885,0x5dcb972e54a52890⟩,by decide +kernel⟩]
private noncomputable def ch_4_0_8 : List Batch_4_0_8 := ch_4_0_8_0
private noncomputable def lv_4_0_8 : List NodeSpec := flattenBatches fmt_4_0_8 (ch_4_0_8.map Subtype.val)
private theorem ok_4_0_8 : LevelOK rd_4_0 (subGoal 4 0) 8 lv_4_0_8 :=
  @checkedBatches (freeVars 4 0) rd_4_0 _ _ _ sl_4_0 [[], [swapRows 84], [swapRows 67], [swapRows 83, swapRows 67], [swapRows 67, swapRows 83], [swapRows 83]] 8 fmt_4_0_7 (ch_4_0_7.map Subtype.val) fmt_4_0_8 pp_4_0 (raw_faithful (freeMask 4 0) p_4_0 q_4_0) sl_4_0_ok (by decide +kernel) ok_4_0_7 ch_4_0_8
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_4_0 : Lower (freeVars 4 0) (subGoal 4 0) 9 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 3 zero, 17, 25), (inputs.getD 4 zero, 9, 25), (inputs.getD 5 zero, 9, 41)]) ok_4_0_8 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube4_0

section Cube16_8

private def p_16_8 : Nat → Bits
  | 0 => mk128 0xbff7fffe3ffff1ff 0xbff7fffe3ffff1ff
  | 1 => mk128 0xd5f8e73fc71c7e93 0xd5f8e73fc71c7e93
  | 2 => mk128 0xe6ff07cff81f8f1c 0xe6ff07cff81f8f1c
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0x0 0x0
  | 5 => mk128 0xf8fff80fffe00fe0 0xf8fff80fffe00fe0
  | _ => 0
private def q_16_8 : Nat → Bits
  | 0 => mk128 0x4010000009040025 0x4010000009040025
  | 1 => mk128 0x2a264a4642496692 0x2a264a4642496692
  | 2 => mk128 0x1942d41a90932b18 0x1942d41a90932b18
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0x0 0x0
  | 5 => mk128 0x78486ad24c24dc0 0x78486ad24c24dc0
  | _ => 0
private theorem pp_16_8 : properPairs (subGoal 16 8) (asRow p_16_8) (asRow q_16_8) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_16_8 : List Decor := rawDecor (freeMask 16 8) p_16_8 q_16_8
private def sl_16_8 : List (Sig × Nat) := []
private theorem sl_16_8_ok : ∀ s ∈ sl_16_8, Slice (freeVars 16 8) (subGoal 16 8) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private def fmt_16_8_3 : ChartFormat := ⟨4, 2, 0, 0, 1⟩
private abbrev Batch_16_8_3 := CheckedBatch (freeVars 16 8) rd_16_8 (subGoal 16 8) sl_16_8 [[]] 3 fmt_16_8_3 [] fmt_16_8_3
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_16_8_3_0 : List Batch_16_8_3 := [
  ⟨⟨2,0x64548a11d212244,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x44548e12a212344,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x64548b15d212205,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x44548f155212305,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x68548621aa12148,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x44548e22a212348,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x68543225aa10c09,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x44548f26a212309,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xa8848d69d810a58,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xa8848d6d521239a,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x6a848532a21239b,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x74848931a15218c,0x1⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_16_8_3_1 : List Batch_16_8_3 := [
  ⟨⟨2,0x6a843035915228c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x74845035a150c8d,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xaa042d71915148d,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x66848a79d21225e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x74848a7dd21225f,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x6a8485bac21136c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x6a8485bdaa121ae,0x1⟩,by decide +kernel⟩,
  ⟨⟨1,0x1aa121af,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_16_8_3 : List Batch_16_8_3 := (ch_16_8_3_0 ++ ch_16_8_3_1)
private noncomputable def lv_16_8_3 : List NodeSpec := flattenBatches fmt_16_8_3 (ch_16_8_3.map Subtype.val)
private theorem ok_16_8_3 : LevelOK rd_16_8 (subGoal 16 8) 3 lv_16_8_3 :=
  @checkedBatches (freeVars 16 8) rd_16_8 _ _ _ sl_16_8 [[]] 3 fmt_16_8_3 [] fmt_16_8_3 pp_16_8 (raw_faithful (freeMask 16 8) p_16_8 q_16_8) sl_16_8_ok (by decide +kernel) (emptyLevelOK rd_16_8 (subGoal 16 8) 2) ch_16_8_3

private def fmt_16_8_4 : ChartFormat := ⟨4, 1, 0, 0, 1⟩
private abbrev Batch_16_8_4 := CheckedBatch (freeVars 16 8) rd_16_8 (subGoal 16 8) sl_16_8 [[]] 4 fmt_16_8_3 (ch_16_8_3.map Subtype.val) fmt_16_8_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_16_8_4_0 : List Batch_16_8_4 := [
  ⟨⟨2,0x1a8428ad11144,0x7f98⟩,by decide +kernel⟩,
  ⟨⟨2,0x1a2228ed11146,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1c44292d11148,0x1fcc18⟩,by decide +kernel⟩,
  ⟨⟨2,0x1a22296d1114a,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1c442b2d18158,0x182⟩,by decide +kernel⟩,
  ⟨⟨2,0x1a222b6d1115a,0x1ca0c⟩,by decide +kernel⟩,
  ⟨⟨2,0x234429ad1114c,0x7f6818⟩,by decide +kernel⟩,
  ⟨⟨2,0x1a2229ed1114e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x23442bad1815c,0xe82⟩,by decide +kernel⟩,
  ⟨⟨2,0x1a222bed1115e,0x1fe0c⟩,by decide +kernel⟩,
  ⟨⟨2,0x23442dad4216c,0x702⟩,by decide +kernel⟩,
  ⟨⟨2,0x1a222ded1116e,0x7240c⟩,by decide +kernel⟩]
private noncomputable def ch_16_8_4 : List Batch_16_8_4 := ch_16_8_4_0
private noncomputable def lv_16_8_4 : List NodeSpec := flattenBatches fmt_16_8_4 (ch_16_8_4.map Subtype.val)
private theorem ok_16_8_4 : LevelOK rd_16_8 (subGoal 16 8) 4 lv_16_8_4 :=
  @checkedBatches (freeVars 16 8) rd_16_8 _ _ _ sl_16_8 [[]] 4 fmt_16_8_3 (ch_16_8_3.map Subtype.val) fmt_16_8_4 pp_16_8 (raw_faithful (freeMask 16 8) p_16_8 q_16_8) sl_16_8_ok (by decide +kernel) ok_16_8_3 ch_16_8_4

private def fmt_16_8_5 : ChartFormat := ⟨4, 0, 0, 0, 1⟩
private abbrev Batch_16_8_5 := CheckedBatch (freeVars 16 8) rd_16_8 (subGoal 16 8) sl_16_8 [[]] 5 fmt_16_8_4 (ch_16_8_4.map Subtype.val) fmt_16_8_5
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_16_8_5_0 : List Batch_16_8_5 := [
  ⟨⟨1,0xe44,0x1ffffff30⟩,by decide +kernel⟩]
private noncomputable def ch_16_8_5 : List Batch_16_8_5 := ch_16_8_5_0
private noncomputable def lv_16_8_5 : List NodeSpec := flattenBatches fmt_16_8_5 (ch_16_8_5.map Subtype.val)
private theorem ok_16_8_5 : LevelOK rd_16_8 (subGoal 16 8) 5 lv_16_8_5 :=
  @checkedBatches (freeVars 16 8) rd_16_8 _ _ _ sl_16_8 [[]] 5 fmt_16_8_4 (ch_16_8_4.map Subtype.val) fmt_16_8_5 pp_16_8 (raw_faithful (freeMask 16 8) p_16_8 q_16_8) sl_16_8_ok (by decide +kernel) ok_16_8_4 ch_16_8_5
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_16_8 : Lower (freeVars 16 8) (subGoal 16 8) 6 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 1, 5), (inputs.getD 5 zero, 1, 33)]) ok_16_8_5 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube16_8

section Cube1_10

private def p_1_10 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 2 => mk128 0xbecfbecfbecfbecf 0xbecfbecfbecfbecf
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0xdf73df73df73df73 0xdf73df73df73df73
  | 5 => mk128 0xefbcefbcefbcefbc 0xefbcefbcefbcefbc
  | _ => 0
private def q_1_10 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 2 => mk128 0x4205420542054205 0x4205420542054205
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0x2412241224122412 0x2412241224122412
  | 5 => mk128 0x1828182818281828 0x1828182818281828
  | _ => 0
private theorem pp_1_10 : properPairs (subGoal 1 10) (asRow p_1_10) (asRow q_1_10) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_1_10 : List Decor := rawDecor (freeMask 1 10) p_1_10 q_1_10
private def sl_1_10 : List (Sig × Nat) := []
private theorem sl_1_10_ok : ∀ s ∈ sl_1_10, Slice (freeVars 1 10) (subGoal 1 10) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private def fmt_1_10_3 : ChartFormat := ⟨3, 0, 0, 0, 1⟩
private abbrev Batch_1_10_3 := CheckedBatch (freeVars 1 10) rd_1_10 (subGoal 1 10) sl_1_10 [[]] 3 fmt_1_10_3 [] fmt_1_10_3
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_1_10_3_0 : List Batch_1_10_3 := [
  ⟨⟨1,0x243,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_1_10_3 : List Batch_1_10_3 := ch_1_10_3_0
private noncomputable def lv_1_10_3 : List NodeSpec := flattenBatches fmt_1_10_3 (ch_1_10_3.map Subtype.val)
private theorem ok_1_10_3 : LevelOK rd_1_10 (subGoal 1 10) 3 lv_1_10_3 :=
  @checkedBatches (freeVars 1 10) rd_1_10 _ _ _ sl_1_10 [[]] 3 fmt_1_10_3 [] fmt_1_10_3 pp_1_10 (raw_faithful (freeMask 1 10) p_1_10 q_1_10) sl_1_10_ok (by decide +kernel) (emptyLevelOK rd_1_10 (subGoal 1 10) 2) ch_1_10_3
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_1_10 : Lower (freeVars 1 10) (subGoal 1 10) 4 :=
  lower_of_search (xs := [(inputs.getD 2 zero, 16, 20), (inputs.getD 4 zero, 4, 20), (inputs.getD 5 zero, 4, 36)]) ok_1_10_3 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube1_10

section Cube1_8

private def p_1_8 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0xfcbbc3ff3e3fe03f 0xcbbc3ff3e3fe03fc
  | 2 => mk128 0x7fdffc7fffc7ffc7 0xfdffc7fffc7ffc7f
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0x8fefff8ffff8fff8 0xfefff8ffff8fff8f
  | 5 => mk128 0xf0f3fff03fff00ff 0xf3fff03fff00ff0
  | _ => 0
private def q_1_8 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0xbc4479224e09261b 0xc4479224e09261bc
  | 2 => mk128 0x55208b0412424a45 0x5208b0412424a455
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0x8a111068249094a8 0xa111068249094a8a
  | 5 => mk128 0x600e224eb92418f6 0xe224eb92418f60
  | _ => 0
private theorem pp_1_8 : properPairs (subGoal 1 8) (asRow p_1_8) (asRow q_1_8) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_1_8 : List Decor := rawDecor (freeMask 1 8) p_1_8 q_1_8
private def sl_1_8 : List (Sig × Nat) := [(subcube 1 10, 4)]
private theorem sl_1_8_ok : ∀ s ∈ sl_1_8, Slice (freeVars 1 8) (subGoal 1 8) s.1 s.2 := by
  intro s hs
  simp only [sl_1_8, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 1 10) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_1_10
private def fmt_1_8_4 : ChartFormat := ⟨4, 0, 0, 1, 0⟩
private abbrev Batch_1_8_4 := CheckedBatch (freeVars 1 8) rd_1_8 (subGoal 1 8) sl_1_8 [[]] 4 fmt_1_8_4 [] fmt_1_8_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_1_8_4_0 : List Batch_1_8_4 := [
  ⟨⟨1,0x1e44,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_1_8_4 : List Batch_1_8_4 := ch_1_8_4_0
private noncomputable def lv_1_8_4 : List NodeSpec := flattenBatches fmt_1_8_4 (ch_1_8_4.map Subtype.val)
private theorem ok_1_8_4 : LevelOK rd_1_8 (subGoal 1 8) 4 lv_1_8_4 :=
  @checkedBatches (freeVars 1 8) rd_1_8 _ _ _ sl_1_8 [[]] 4 fmt_1_8_4 [] fmt_1_8_4 pp_1_8 (raw_faithful (freeMask 1 8) p_1_8 q_1_8) sl_1_8_ok (by decide +kernel) (emptyLevelOK rd_1_8 (subGoal 1 8) 3) ch_1_8_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_1_8 : Lower (freeVars 1 8) (subGoal 1 8) 5 :=
  lower_of_search (xs := [(inputs.getD 1 zero, 36, 38), (inputs.getD 2 zero, 16, 20), (inputs.getD 4 zero, 4, 20), (inputs.getD 5 zero, 6, 38)]) ok_1_8_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube1_8

section Cube34_8

private def p_34_8 : Nat → Bits
  | 0 => mk128 0xbecfbecfbecfbecf 0xbecfbecfbecfbecf
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0xdf73df73df73df73 0xdf73df73df73df73
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0xefbcefbcefbcefbc 0xefbcefbcefbcefbc
  | 5 => mk128 0x0 0x0
  | _ => 0
private def q_34_8 : Nat → Bits
  | 0 => mk128 0x4205420542054205 0x4205420542054205
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0x2412241224122412 0x2412241224122412
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0x1828182818281828 0x1828182818281828
  | 5 => mk128 0x0 0x0
  | _ => 0
private theorem pp_34_8 : properPairs (subGoal 34 8) (asRow p_34_8) (asRow q_34_8) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_34_8 : List Decor := rawDecor (freeMask 34 8) p_34_8 q_34_8
private def sl_34_8 : List (Sig × Nat) := []
private theorem sl_34_8_ok : ∀ s ∈ sl_34_8, Slice (freeVars 34 8) (subGoal 34 8) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private def fmt_34_8_3 : ChartFormat := ⟨3, 0, 0, 0, 1⟩
private abbrev Batch_34_8_3 := CheckedBatch (freeVars 34 8) rd_34_8 (subGoal 34 8) sl_34_8 [[]] 3 fmt_34_8_3 [] fmt_34_8_3
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_34_8_3_0 : List Batch_34_8_3 := [
  ⟨⟨1,0x243,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_34_8_3 : List Batch_34_8_3 := ch_34_8_3_0
private noncomputable def lv_34_8_3 : List NodeSpec := flattenBatches fmt_34_8_3 (ch_34_8_3.map Subtype.val)
private theorem ok_34_8_3 : LevelOK rd_34_8 (subGoal 34 8) 3 lv_34_8_3 :=
  @checkedBatches (freeVars 34 8) rd_34_8 _ _ _ sl_34_8 [[]] 3 fmt_34_8_3 [] fmt_34_8_3 pp_34_8 (raw_faithful (freeMask 34 8) p_34_8 q_34_8) sl_34_8_ok (by decide +kernel) (emptyLevelOK rd_34_8 (subGoal 34 8) 2) ch_34_8_3
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_34_8 : Lower (freeVars 34 8) (subGoal 34 8) 4 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 4, 5), (inputs.getD 2 zero, 1, 5), (inputs.getD 4 zero, 1, 17)]) ok_34_8_3 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube34_8

section Cube2_8

private def p_2_8 : Nat → Bits
  | 0 => mk128 0xeffbfe7e3ffc79e7 0xdff7fcfc7ff8f3cf
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0xf6fccf9fc71f9e99 0xedf99f3f8e3f3d33
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0x3b7f0fe7f81fe71e 0x76fe1fcff03fce3c
  | 5 => mk128 0x3c7ff007ffe007e0 0x78ffe00fffc00fc0
  | _ => 0
private def q_2_8 : Nat → Bits
  | 0 => mk128 0x5008008009040022 0xa010010012080045
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0x8912142242491289 0x1224284484922512
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0x4a0a80c90924514 0x941501921248a28
  | 5 => mk128 0x3c28d5724c357c0 0x7851aae4986af80
  | _ => 0
private theorem pp_2_8 : properPairs (subGoal 2 8) (asRow p_2_8) (asRow q_2_8) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_2_8 : List Decor := rawDecor (freeMask 2 8) p_2_8 q_2_8
private def sl_2_8 : List (Sig × Nat) := [(subcube 34 8, 4)]
private theorem sl_2_8_ok : ∀ s ∈ sl_2_8, Slice (freeVars 2 8) (subGoal 2 8) s.1 s.2 := by
  intro s hs
  simp only [sl_2_8, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 34 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_34_8
private def fmt_2_8_4 : ChartFormat := ⟨4, 0, 0, 1, 0⟩
private abbrev Batch_2_8_4 := CheckedBatch (freeVars 2 8) rd_2_8 (subGoal 2 8) sl_2_8 [[]] 4 fmt_2_8_4 [] fmt_2_8_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_2_8_4_0 : List Batch_2_8_4 := [
  ⟨⟨1,0x1e44,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_2_8_4 : List Batch_2_8_4 := ch_2_8_4_0
private noncomputable def lv_2_8_4 : List NodeSpec := flattenBatches fmt_2_8_4 (ch_2_8_4.map Subtype.val)
private theorem ok_2_8_4 : LevelOK rd_2_8 (subGoal 2 8) 4 lv_2_8_4 :=
  @checkedBatches (freeVars 2 8) rd_2_8 _ _ _ sl_2_8 [[]] 4 fmt_2_8_4 [] fmt_2_8_4 pp_2_8 (raw_faithful (freeMask 2 8) p_2_8 q_2_8) sl_2_8_ok (by decide +kernel) (emptyLevelOK rd_2_8 (subGoal 2 8) 3) ch_2_8_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_2_8 : Lower (freeVars 2 8) (subGoal 2 8) 5 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 4, 5), (inputs.getD 2 zero, 1, 5), (inputs.getD 4 zero, 1, 17), (inputs.getD 5 zero, 1, 33)]) ok_2_8_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube2_8

section Cube0_10

private def p_0_10 : Nat → Bits
  | 0 => mk128 0xf1b77c27feaef1b7 0x7c27feaef1b77c27
  | 1 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 2 => mk128 0x3e3ba0dabf333e3b 0xa0dabf333e3ba0da
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0xcfc3c31cdfc3cfc3 0xc31cdfc3cfc3c31c
  | 5 => mk128 0xffc03e0effc0ffc 0x3e0effc0ffc03e0
  | _ => 0
private def q_0_10 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 2 => mk128 0x4211044a42444211 0x44a42444211044a
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0x1482091424181482 0x914241814820914
  | 5 => mk128 0xa92012a01801a920 0x12a01801a92012a0
  | _ => 0
private theorem pp_0_10 : properPairs (subGoal 0 10) (asRow p_0_10) (asRow q_0_10) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_0_10 : List Decor := rawDecor (freeMask 0 10) p_0_10 q_0_10
private def sl_0_10 : List (Sig × Nat) := [(subcube 1 10, 4)]
private theorem sl_0_10_ok : ∀ s ∈ sl_0_10, Slice (freeVars 0 10) (subGoal 0 10) s.1 s.2 := by
  intro s hs
  simp only [sl_0_10, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 1 10) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_1_10
private def fmt_0_10_4 : ChartFormat := ⟨4, 0, 0, 1, 0⟩
private abbrev Batch_0_10_4 := CheckedBatch (freeVars 0 10) rd_0_10 (subGoal 0 10) sl_0_10 [[]] 4 fmt_0_10_4 [] fmt_0_10_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_10_4_0 : List Batch_0_10_4 := [
  ⟨⟨1,0x1e44,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_0_10_4 : List Batch_0_10_4 := ch_0_10_4_0
private noncomputable def lv_0_10_4 : List NodeSpec := flattenBatches fmt_0_10_4 (ch_0_10_4.map Subtype.val)
private theorem ok_0_10_4 : LevelOK rd_0_10 (subGoal 0 10) 4 lv_0_10_4 :=
  @checkedBatches (freeVars 0 10) rd_0_10 _ _ _ sl_0_10 [[]] 4 fmt_0_10_4 [] fmt_0_10_4 pp_0_10 (raw_faithful (freeMask 0 10) p_0_10 q_0_10) sl_0_10_ok (by decide +kernel) (emptyLevelOK rd_0_10 (subGoal 0 10) 3) ch_0_10_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_0_10 : Lower (freeVars 0 10) (subGoal 0 10) 5 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 0, 1), (inputs.getD 2 zero, 16, 20), (inputs.getD 4 zero, 4, 20), (inputs.getD 5 zero, 4, 36)]) ok_0_10_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube0_10

section Cube32_8

private def p_32_8 : Nat → Bits
  | 0 => mk128 0xeffb9ffe38fff87f 0xdff73ffc71fff0ff
  | 1 => mk128 0xf57c199fc0e73e49 0xeaf8333f81ce7c93
  | 2 => mk128 0x39ffe1e7ff07c78e 0x73ffc3cffe0f8f1c
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0x3e7ffe07fff807f0 0x7cfffc0ffff00fe0
  | 5 => mk128 0x0 0x0
  | _ => 0
private def q_32_8 : Nat → Bits
  | 0 => mk128 0x5008200008210012 0xa010400010420025
  | 1 => mk128 0x8a9353264652b649 0x1526a64c8ca56c92
  | 2 => mk128 0x621140a9204928c 0xc42281524092518
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0x1c2015524902560 0x38402aa49204ac0
  | 5 => mk128 0x0 0x0
  | _ => 0
private theorem pp_32_8 : properPairs (subGoal 32 8) (asRow p_32_8) (asRow q_32_8) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_32_8 : List Decor := rawDecor (freeMask 32 8) p_32_8 q_32_8
private def sl_32_8 : List (Sig × Nat) := [(subcube 34 8, 4)]
private theorem sl_32_8_ok : ∀ s ∈ sl_32_8, Slice (freeVars 32 8) (subGoal 32 8) s.1 s.2 := by
  intro s hs
  simp only [sl_32_8, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 34 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_34_8
private def fmt_32_8_4 : ChartFormat := ⟨4, 0, 0, 1, 0⟩
private abbrev Batch_32_8_4 := CheckedBatch (freeVars 32 8) rd_32_8 (subGoal 32 8) sl_32_8 [[]] 4 fmt_32_8_4 [] fmt_32_8_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_32_8_4_0 : List Batch_32_8_4 := [
  ⟨⟨1,0x1e44,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_32_8_4 : List Batch_32_8_4 := ch_32_8_4_0
private noncomputable def lv_32_8_4 : List NodeSpec := flattenBatches fmt_32_8_4 (ch_32_8_4.map Subtype.val)
private theorem ok_32_8_4 : LevelOK rd_32_8 (subGoal 32 8) 4 lv_32_8_4 :=
  @checkedBatches (freeVars 32 8) rd_32_8 _ _ _ sl_32_8 [[]] 4 fmt_32_8_4 [] fmt_32_8_4 pp_32_8 (raw_faithful (freeMask 32 8) p_32_8 q_32_8) sl_32_8_ok (by decide +kernel) (emptyLevelOK rd_32_8 (subGoal 32 8) 3) ch_32_8_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_32_8 : Lower (freeVars 32 8) (subGoal 32 8) 5 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 1, 5), (inputs.getD 4 zero, 1, 17)]) ok_32_8_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube32_8

section Cube0_8

private def p_0_8 : Nat → Bits
  | 0 => mk128 0xffc3e3fffe0c71f8 0xfff1c1fffe08f0ff
  | 1 => mk128 0xe3fc03c78ff07e3f 0x1c3e01c71e774c93
  | 2 => mk128 0x3fffc07f1ff803f 0xe03ffe07e1878f1c
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0x3fffff801ffffc0 0x3ffff801f80fe0
  | 5 => mk128 0xfc00000001ffffff 0xffc0000001fff000
  | _ => 0
private def q_0_8 : Nat → Bits
  | 0 => mk128 0x40040000000040 0x2400404100001025
  | 1 => mk128 0xc488c98b10703219 0x8b20c925c334c92
  | 2 => mk128 0x491140940294802a 0x41149404c4858518
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0x9222820125295480 0x229293009580ac0
  | 5 => mk128 0x3b132649ce6934 0x9380302091eee000
  | _ => 0
private theorem pp_0_8 : properPairs (subGoal 0 8) (asRow p_0_8) (asRow q_0_8) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_0_8 : List Decor := rawDecor (freeMask 0 8) p_0_8 q_0_8
private def sl_0_8 : List (Sig × Nat) := [(subcube 4 8, 6), (subcube 16 8, 6), (subcube 1 8, 5), (subcube 2 8, 5), (subcube 0 10, 5), (subcube 32 8, 5), (subcube 0 40, 5), (subcube 1 10, 4), (subcube 1 40, 4), (subcube 34 8, 4)]
private theorem sl_0_8_ok : ∀ s ∈ sl_0_8, Slice (freeVars 0 8) (subGoal 0 8) s.1 s.2 := by
  intro s hs
  simp only [sl_0_8, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact slice_correct (ms := fixRows 4 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_4_8
  · exact slice_correct (ms := fixRows 16 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_16_8
  · exact slice_correct (ms := fixRows 1 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_1_8
  · exact slice_correct (ms := fixRows 2 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_2_8
  · exact slice_correct (ms := fixRows 0 10) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_0_10
  · exact slice_correct (ms := fixRows 32 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_32_8
  · exact slice_correct (ms := fixRows 0 40) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_0_40
  · exact slice_correct (ms := fixRows 1 10) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_1_10
  · exact slice_correct (ms := fixRows 1 40) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_1_40
  · exact slice_correct (ms := fixRows 34 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_34_8
private def fmt_0_8_4 : ChartFormat := ⟨5, 4, 0, 1, 4⟩
private abbrev Batch_0_8_4 := CheckedBatch (freeVars 0 8) rd_0_8 (subGoal 0 8) sl_0_8 [[], [swapRows 66], [swapRows 81], [swapRows 66, swapRows 81]] 4 fmt_0_8_4 [] fmt_0_8_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_8_4_0 : List Batch_0_8_4 := [
  ⟨⟨2,0x64e10ba6715a124370855a38ad09,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x84210bdfaa6012320785d33aad09,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x86430bbc2a289a8270657130af29,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x270640cbe26e6c9a432085de35344d,0x1⟩,by decide +kernel⟩,
  ⟨⟨1,0x1383207531d6304d,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_0_8_4 : List Batch_0_8_4 := ch_0_8_4_0
private noncomputable def lv_0_8_4 : List NodeSpec := flattenBatches fmt_0_8_4 (ch_0_8_4.map Subtype.val)
private theorem ok_0_8_4 : LevelOK rd_0_8 (subGoal 0 8) 4 lv_0_8_4 :=
  @checkedBatches (freeVars 0 8) rd_0_8 _ _ _ sl_0_8 [[], [swapRows 66], [swapRows 81], [swapRows 66, swapRows 81]] 4 fmt_0_8_4 [] fmt_0_8_4 pp_0_8 (raw_faithful (freeMask 0 8) p_0_8 q_0_8) sl_0_8_ok (by decide +kernel) (emptyLevelOK rd_0_8 (subGoal 0 8) 3) ch_0_8_4

private def fmt_0_8_5 : ChartFormat := ⟨5, 3, 0, 3, 4⟩
private abbrev Batch_0_8_5 := CheckedBatch (freeVars 0 8) rd_0_8 (subGoal 0 8) sl_0_8 [[], [swapRows 66], [swapRows 81], [swapRows 66, swapRows 81]] 5 fmt_0_8_4 (ch_0_8_4.map Subtype.val) fmt_0_8_5
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_8_5_0 : List Batch_0_8_5 := [
  ⟨⟨2,0x8f11db3ea41120362e77886cda904,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xe829da21b36a41120302e778864da904,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x5000a34476ba4d0462634476cfa904,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x281cd11dac93412203a0fe6886b14d04,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x234376af2b0512676a86cd2b05,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xa0634476cfab0562676886cdab05,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x121d079ae4358268282a0a35c86b84d05,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x26778864da907a0734476b34d05,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x8d11db3ea41c30508e76886cda907,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xc751ed826e12235c86ba4d07,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x233547b578684b668088814003cfa954d0d09,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x19911dabc342410100e7d4864d0d09,0x1⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_8_5_1 : List Batch_0_8_5 := [
  ⟨⟨2,0x8c7790d925e1223bd16d60f09,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x263e886d62f090863e886d52f09,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x100a6a476af4d09086223e6af2f09,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x6674f61a4d09006674f6184d09,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x2344761aad09006668f61aad09,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x333343b1d56848908a66b8638ad09,0x22274⟩,by decide +kernel⟩,
  ⟨⟨2,0x63a8f61aad09006664765aad09,0x2e⟩,by decide +kernel⟩,
  ⟨⟨2,0x40700e3ab96193009a263ab8638ad09,0x12⟩,by decide +kernel⟩,
  ⟨⟨2,0x80c0b8fa21b54c02428304e3f486c93009,0x3c2⟩,by decide +kernel⟩,
  ⟨⟨2,0x18c6b8cc615e52234476d63009,0x182⟩,by decide +kernel⟩,
  ⟨⟨2,0x677506cd3029087c446671af29,0x182⟩,by decide +kernel⟩,
  ⟨⟨2,0x23e886b87129087bab06713029,0x6186⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_8_5_2 : List Batch_0_8_5 := [
  ⟨⟨2,0x4688ec355a56234476cfa12b,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xc0656876c6144dc0656b86c5144d,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x180cad70c702a9a2768e615144d,0x882⟩,by decide +kernel⟩,
  ⟨⟨2,0x6564765a154dc06568763a154d,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x468eec2e2c9a1828407276886c1164d,0x882⟩,by decide +kernel⟩,
  ⟨⟨2,0xc0676b0635344d00657c86c9174d,0xa82⟩,by decide +kernel⟩,
  ⟨⟨2,0x1263437637364d006564765a354d,0x4a86⟩,by decide +kernel⟩,
  ⟨⟨2,0x484c0eb5c86d2364dc07d6886d1364d,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1e05eb443689ba68300a57c86c9374d,0xe82⟩,by decide +kernel⟩,
  ⟨⟨2,0x2657c86c9304dc07d6886d2374d,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x80d4688edac609a276886d5304d,0x902⟩,by decide +kernel⟩,
  ⟨⟨2,0x7814ed10daa649a24203c13d6b0631304d,0x902⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_8_5_3 : List Batch_0_8_5 := [
  ⟨⟨2,0x11a23b658a9804c0a34786d6324d,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x4688ed9f52602344761aa930,0x1⟩,by decide +kernel⟩,
  ⟨⟨1,0x62634476cfa932,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_0_8_5 : List Batch_0_8_5 := ((ch_0_8_5_0 ++ ch_0_8_5_1) ++ (ch_0_8_5_2 ++ ch_0_8_5_3))
private noncomputable def lv_0_8_5 : List NodeSpec := flattenBatches fmt_0_8_5 (ch_0_8_5.map Subtype.val)
private theorem ok_0_8_5 : LevelOK rd_0_8 (subGoal 0 8) 5 lv_0_8_5 :=
  @checkedBatches (freeVars 0 8) rd_0_8 _ _ _ sl_0_8 [[], [swapRows 66], [swapRows 81], [swapRows 66, swapRows 81]] 5 fmt_0_8_4 (ch_0_8_4.map Subtype.val) fmt_0_8_5 pp_0_8 (raw_faithful (freeMask 0 8) p_0_8 q_0_8) sl_0_8_ok (by decide +kernel) ok_0_8_4 ch_0_8_5

private def fmt_0_8_6 : ChartFormat := ⟨5, 2, 0, 4, 4⟩
private abbrev Batch_0_8_6 := CheckedBatch (freeVars 0 8) rd_0_8 (subGoal 0 8) sl_0_8 [[], [swapRows 66], [swapRows 81], [swapRows 66, swapRows 81]] 6 fmt_0_8_5 (ch_0_8_5.map Subtype.val) fmt_0_8_6
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_8_6_0 : List Batch_0_8_6 := [
  ⟨⟨2,0x40e30a18588280151e4435482103861628347885a904,0xcc2134⟩,by decide +kernel⟩,
  ⟨⟨2,0x60c2c705cd10b6208206102800d3344574d04,0x10820931c⟩,by decide +kernel⟩,
  ⟨⟨2,0x12b4a2061200446a8cc560a28616382b4465b204,0x9ba04⟩,by decide +kernel⟩,
  ⟨⟨2,0x20681ccd521d341471851030b105002a34466ab05,0x108466341c⟩,by decide +kernel⟩,
  ⟨⟨2,0x1c61238b1c1da232d9829238a2471638435885b005,0x12d06⟩,by decide +kernel⟩,
  ⟨⟨2,0x1030a2040a00447910d520e3881a093344574d06,0xccec04⟩,by decide +kernel⟩,
  ⟨⟨2,0x1c40c20163a8e0e6812206102800d3344574d07,0x209ec0c⟩,by decide +kernel⟩,
  ⟨⟨2,0x10384883000f33a8b06848e20671d44673709,0x770d80c⟩,by decide +kernel⟩,
  ⟨⟨2,0x10384883000f1d473078484883000b33a8870d09,0x1b9c80c⟩,by decide +kernel⟩,
  ⟨⟨2,0xb28122080d33a4326848e206080b1d44672f09,0x21284210c0852028⟩,by decide +kernel⟩,
  ⟨⟨2,0x103a20a4cea21eb42461440d181a66886ad09,0x96e492212082058⟩,by decide +kernel⟩,
  ⟨⟨2,0x1220c002c75119ebc2461440d106002234466af09,0x6c088a021781c⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_8_6_1 : List Batch_0_8_6 := [
  ⟨⟨2,0x40e30a2061220c005ccd10d5a1640e30a20610111d47073009,0x10843f00c⟩,by decide +kernel⟩,
  ⟨⟨2,0x1c614409106002634466af291e55440d10600263a8662f29,0x116c06⟩,by decide +kernel⟩,
  ⟨⟨2,0x30a206080da3a88771291d51038a001e3ab063029,0x139c45b01c⟩,by decide +kernel⟩,
  ⟨⟨2,0x91850c2441800999a21ab4ac71850c206002234706a12b,0x22f0082c00c14⟩,by decide +kernel⟩,
  ⟨⟨2,0x280a6ad10e2a9a10300092b4467144d,0x392488920a01047b8010⟩,by decide +kernel⟩,
  ⟨⟨2,0x40c0024ad119c593461440e106002234466164d,0x904027f814⟩,by decide +kernel⟩,
  ⟨⟨2,0x10380e568e0e689a14052b4467174d,0x5c4c9014⟩,by decide +kernel⟩,
  ⟨⟨2,0x40e0395a2339b26881c07356887354d,0x1084edd01c⟩,by decide +kernel⟩,
  ⟨⟨2,0x61440c1800795a3839826881c072b4467374d,0x4212c212e3b4038⟩,by decide +kernel⟩,
  ⟨⟨2,0x1851038165688ce649a48c2881c0da56887314d,0x8872004⟩,by decide +kernel⟩,
  ⟨⟨2,0x1440c205001e3c886a9302071440d2081026358861530,0x9a7062f0168934fc068⟩,by decide +kernel⟩,
  ⟨⟨2,0x48e2891861620a005c7910d526448e20696383e6a853130,0xe0872004⟩,by decide +kernel⟩]
private noncomputable def ch_0_8_6 : List Batch_0_8_6 := (ch_0_8_6_0 ++ ch_0_8_6_1)
private noncomputable def lv_0_8_6 : List NodeSpec := flattenBatches fmt_0_8_6 (ch_0_8_6.map Subtype.val)
private theorem ok_0_8_6 : LevelOK rd_0_8 (subGoal 0 8) 6 lv_0_8_6 :=
  @checkedBatches (freeVars 0 8) rd_0_8 _ _ _ sl_0_8 [[], [swapRows 66], [swapRows 81], [swapRows 66, swapRows 81]] 6 fmt_0_8_5 (ch_0_8_5.map Subtype.val) fmt_0_8_6 pp_0_8 (raw_faithful (freeMask 0 8) p_0_8 q_0_8) sl_0_8_ok (by decide +kernel) ok_0_8_5 ch_0_8_6

private def fmt_0_8_7 : ChartFormat := ⟨5, 1, 0, 4, 4⟩
private abbrev Batch_0_8_7 := CheckedBatch (freeVars 0 8) rd_0_8 (subGoal 0 8) sl_0_8 [[], [swapRows 66], [swapRows 81], [swapRows 66, swapRows 81]] 7 fmt_0_8_6 (ch_0_8_6.map Subtype.val) fmt_0_8_7
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_8_7_0 : List Batch_0_8_7 := [
  ⟨⟨2,0x128398a418a218032354860541cc518a21802a3445604,0x1084ee2109df8⟩,by decide +kernel⟩,
  ⟨⟨2,0x1062906288600a8d11581d28398a418a2180323445606,0x4e540c⟩,by decide +kernel⟩,
  ⟨⟨2,0x41cc520c51082a344560b41cc520c51082a3a88609,0x21084cc22f11892ac050⟩,by decide +kernel⟩,
  ⟨⟨2,0x24e628c510826344562b49cc520c51082a3a88629,0x2784df85605828⟩,by decide +kernel⟩,
  ⟨⟨2,0x8394831443005468d0c60629062081e568864d,0x138891089249244210810f63e09b82a2508a0941e0⟩,by decide +kernel⟩,
  ⟨⟨2,0x93948314430054688ac649398a418a21802ec688631,0xf4259014⟩,by decide +kernel⟩]
private noncomputable def ch_0_8_7 : List Batch_0_8_7 := ch_0_8_7_0
private noncomputable def lv_0_8_7 : List NodeSpec := flattenBatches fmt_0_8_7 (ch_0_8_7.map Subtype.val)
private theorem ok_0_8_7 : LevelOK rd_0_8 (subGoal 0 8) 7 lv_0_8_7 :=
  @checkedBatches (freeVars 0 8) rd_0_8 _ _ _ sl_0_8 [[], [swapRows 66], [swapRows 81], [swapRows 66, swapRows 81]] 7 fmt_0_8_6 (ch_0_8_6.map Subtype.val) fmt_0_8_7 pp_0_8 (raw_faithful (freeMask 0 8) p_0_8 q_0_8) sl_0_8_ok (by decide +kernel) ok_0_8_6 ch_0_8_7

private def fmt_0_8_8 : ChartFormat := ⟨5, 0, 0, 2, 4⟩
private abbrev Batch_0_8_8 := CheckedBatch (freeVars 0 8) rd_0_8 (subGoal 0 8) sl_0_8 [[], [swapRows 66], [swapRows 81], [swapRows 66, swapRows 81]] 8 fmt_0_8_7 (ch_0_8_7.map Subtype.val) fmt_0_8_8
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_8_8_0 : List Batch_0_8_8 := [
  ⟨⟨1,0x2146885,0x122109ffdc92492550⟩,by decide +kernel⟩]
private noncomputable def ch_0_8_8 : List Batch_0_8_8 := ch_0_8_8_0
private noncomputable def lv_0_8_8 : List NodeSpec := flattenBatches fmt_0_8_8 (ch_0_8_8.map Subtype.val)
private theorem ok_0_8_8 : LevelOK rd_0_8 (subGoal 0 8) 8 lv_0_8_8 :=
  @checkedBatches (freeVars 0 8) rd_0_8 _ _ _ sl_0_8 [[], [swapRows 66], [swapRows 81], [swapRows 66, swapRows 81]] 8 fmt_0_8_7 (ch_0_8_7.map Subtype.val) fmt_0_8_8 pp_0_8 (raw_faithful (freeMask 0 8) p_0_8 q_0_8) sl_0_8_ok (by decide +kernel) ok_0_8_7 ch_0_8_8
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_0_8 : Lower (freeVars 0 8) (subGoal 0 8) 9 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 1, 5), (inputs.getD 4 zero, 1, 17), (inputs.getD 5 zero, 1, 33)]) ok_0_8_8 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube0_8

section Cube2_1

private def p_2_1 : Nat → Bits
  | 0 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0xed78999e38e73e49 0xdaf1333c71ce7c93
  | 3 => mk128 0xf7ff1fffc0fff87f 0xeffe3fff81fff0ff
  | 4 => mk128 0x39ffe1e7ff07c78e 0x73ffc3cffe0f8f1c
  | 5 => mk128 0x3e7ffe07fff807f0 0x7cfffc0ffff00fe0
  | _ => 0
private def q_2_1 : Nat → Bits
  | 0 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0x528e33260e31b648 0xa51c664c1c636c91
  | 3 => mk128 0x8810400040420013 0x1020800080840026
  | 4 => mk128 0x622140a9204928c 0xc44281524092518
  | 5 => mk128 0x1c4015524902560 0x38802aa49204ac0
  | _ => 0
private theorem pp_2_1 : properPairs (subGoal 2 1) (asRow p_2_1) (asRow q_2_1) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_2_1 : List Decor := rawDecor (freeMask 2 1) p_2_1 q_2_1
private def sl_2_1 : List (Sig × Nat) := [(subcube 6 1, 4)]
private theorem sl_2_1_ok : ∀ s ∈ sl_2_1, Slice (freeVars 2 1) (subGoal 2 1) s.1 s.2 := by
  intro s hs
  simp only [sl_2_1, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 6 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_6_1
private def fmt_2_1_4 : ChartFormat := ⟨4, 0, 0, 1, 0⟩
private abbrev Batch_2_1_4 := CheckedBatch (freeVars 2 1) rd_2_1 (subGoal 2 1) sl_2_1 [[]] 4 fmt_2_1_4 [] fmt_2_1_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_2_1_4_0 : List Batch_2_1_4 := [
  ⟨⟨1,0x1e44,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_2_1_4 : List Batch_2_1_4 := ch_2_1_4_0
private noncomputable def lv_2_1_4 : List NodeSpec := flattenBatches fmt_2_1_4 (ch_2_1_4.map Subtype.val)
private theorem ok_2_1_4 : LevelOK rd_2_1 (subGoal 2 1) 4 lv_2_1_4 :=
  @checkedBatches (freeVars 2 1) rd_2_1 _ _ _ sl_2_1 [[]] 4 fmt_2_1_4 [] fmt_2_1_4 pp_2_1 (raw_faithful (freeMask 2 1) p_2_1 q_2_1) sl_2_1_ok (by decide +kernel) (emptyLevelOK rd_2_1 (subGoal 2 1) 3) ch_2_1_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_2_1 : Lower (freeVars 2 1) (subGoal 2 1) 5 :=
  lower_of_search (xs := [(inputs.getD 2 zero, 8, 12), (inputs.getD 3 zero, 4, 12), (inputs.getD 4 zero, 8, 24), (inputs.getD 5 zero, 8, 40)]) ok_2_1_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube2_1

section Cube2_4

private def p_2_4 : Nat → Bits
  | 0 => mk128 0xeef8ff9f8ff879f9 0xddf1ff3f1ff0f3f3
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 3 => mk128 0xf7ff3ffff1fffe3f 0xeffe7fffe3fffc7f
  | 4 => mk128 0x3b7fc7e7fe3f87ce 0x76ff8fcffc7f0f9c
  | 5 => mk128 0x3c7ff807ffc007f0 0x78fff00fff800fe0
  | _ => 0
private def q_2_4 : Nat → Bits
  | 0 => mk128 0x510e1121824930d8 0xa21c2243049261b1
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 3 => mk128 0x8810820210924223 0x1021040421248446
  | 4 => mk128 0x4a2340ca425154c 0x9446819484a2a98
  | 5 => mk128 0x3c4a757490667b0 0x7894eae920ccf60
  | _ => 0
private theorem pp_2_4 : properPairs (subGoal 2 4) (asRow p_2_4) (asRow q_2_4) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_2_4 : List Decor := rawDecor (freeMask 2 4) p_2_4 q_2_4
private def sl_2_4 : List (Sig × Nat) := [(subcube 2 36, 4)]
private theorem sl_2_4_ok : ∀ s ∈ sl_2_4, Slice (freeVars 2 4) (subGoal 2 4) s.1 s.2 := by
  intro s hs
  simp only [sl_2_4, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 2 36) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_2_36
private def fmt_2_4_4 : ChartFormat := ⟨4, 0, 0, 1, 0⟩
private abbrev Batch_2_4_4 := CheckedBatch (freeVars 2 4) rd_2_4 (subGoal 2 4) sl_2_4 [[]] 4 fmt_2_4_4 [] fmt_2_4_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_2_4_4_0 : List Batch_2_4_4 := [
  ⟨⟨1,0x1e44,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_2_4_4 : List Batch_2_4_4 := ch_2_4_4_0
private noncomputable def lv_2_4_4 : List NodeSpec := flattenBatches fmt_2_4_4 (ch_2_4_4.map Subtype.val)
private theorem ok_2_4_4 : LevelOK rd_2_4 (subGoal 2 4) 4 lv_2_4_4 :=
  @checkedBatches (freeVars 2 4) rd_2_4 _ _ _ sl_2_4 [[]] 4 fmt_2_4_4 [] fmt_2_4_4 pp_2_4 (raw_faithful (freeMask 2 4) p_2_4 q_2_4) sl_2_4_ok (by decide +kernel) (emptyLevelOK rd_2_4 (subGoal 2 4) 3) ch_2_4_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_2_4 : Lower (freeVars 2 4) (subGoal 2 4) 5 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 8, 9), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 8, 24), (inputs.getD 5 zero, 17, 49)]) ok_2_4_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube2_4

section Cube34_0

private def p_34_0 : Nat → Bits
  | 0 => mk128 0xffc3fe3fbf0fffc3 0xfe3fbf0fffc3fe3f
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0xfffc3fc7dff0fffc 0x3fc7dff0fffc3fc7
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0xfffc3f8efff0fff 0xc3f8efff0fffc3f8
  | 5 => mk128 0x0 0x0
  | _ => 0
private def q_34_0 : Nat → Bits
  | 0 => mk128 0x22e2661b41e222e2 0x661b41e222e2661b
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0x45662ac5222e4566 0x2ac5222e45662ac5
  | 3 => mk128 0x8988916e04448988 0x916e04448988916e
  | 4 => mk128 0xee3323b01888ee33 0x23b01888ee3323b0
  | 5 => mk128 0x0 0x0
  | _ => 0
private theorem pp_34_0 : properPairs (subGoal 34 0) (asRow p_34_0) (asRow q_34_0) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_34_0 : List Decor := rawDecor (freeMask 34 0) p_34_0 q_34_0
private def sl_34_0 : List (Sig × Nat) := [(subcube 34 8, 4)]
private theorem sl_34_0_ok : ∀ s ∈ sl_34_0, Slice (freeVars 34 0) (subGoal 34 0) s.1 s.2 := by
  intro s hs
  simp only [sl_34_0, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 34 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_34_8
private def fmt_34_0_4 : ChartFormat := ⟨4, 0, 0, 1, 0⟩
private abbrev Batch_34_0_4 := CheckedBatch (freeVars 34 0) rd_34_0 (subGoal 34 0) sl_34_0 [[]] 4 fmt_34_0_4 [] fmt_34_0_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_34_0_4_0 : List Batch_34_0_4 := [
  ⟨⟨1,0x1e44,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_34_0_4 : List Batch_34_0_4 := ch_34_0_4_0
private noncomputable def lv_34_0_4 : List NodeSpec := flattenBatches fmt_34_0_4 (ch_34_0_4.map Subtype.val)
private theorem ok_34_0_4 : LevelOK rd_34_0 (subGoal 34 0) 4 lv_34_0_4 :=
  @checkedBatches (freeVars 34 0) rd_34_0 _ _ _ sl_34_0 [[]] 4 fmt_34_0_4 [] fmt_34_0_4 pp_34_0 (raw_faithful (freeMask 34 0) p_34_0 q_34_0) sl_34_0_ok (by decide +kernel) (emptyLevelOK rd_34_0 (subGoal 34 0) 3) ch_34_0_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_34_0 : Lower (freeVars 34 0) (subGoal 34 0) 5 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 12, 13), (inputs.getD 2 zero, 9, 13), (inputs.getD 3 zero, 5, 13), (inputs.getD 4 zero, 9, 25)]) ok_34_0_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube34_0

section Cube2_16

private def p_2_16 : Nat → Bits
  | 0 => mk128 0xbfcffcf8fff873f3 0xbfcffcf8fff873f3
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0xdbf19f3f1c3f8d9c 0xdbf19f3f1c3f8d9c
  | 3 => mk128 0xeffe1fffe03ffe1f 0xeffe1fffe03ffe1f
  | 4 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 5 => mk128 0xf3ffe03fffc00fe0 0xf3ffe03fffc00fe0
  | _ => 0
private def q_2_16 : Nat → Bits
  | 0 => mk128 0x40640108248920b1 0x40640108248920b1
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0x24ac285909932594 0x24ac285909932594
  | 3 => mk128 0x1101502242244a0a 0x1101502242244a0a
  | 4 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 5 => mk128 0xe091ab493064f40 0xe091ab493064f40
  | _ => 0
private theorem pp_2_16 : properPairs (subGoal 2 16) (asRow p_2_16) (asRow q_2_16) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_2_16 : List Decor := rawDecor (freeMask 2 16) p_2_16 q_2_16
private def sl_2_16 : List (Sig × Nat) := []
private theorem sl_2_16_ok : ∀ s ∈ sl_2_16, Slice (freeVars 2 16) (subGoal 2 16) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private def fmt_2_16_3 : ChartFormat := ⟨4, 0, 0, 0, 1⟩
private abbrev Batch_2_16_3 := CheckedBatch (freeVars 2 16) rd_2_16 (subGoal 2 16) sl_2_16 [[]] 3 fmt_2_16_3 [] fmt_2_16_3
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_2_16_3_0 : List Batch_2_16_3 := [
  ⟨⟨1,0xe44,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_2_16_3 : List Batch_2_16_3 := ch_2_16_3_0
private noncomputable def lv_2_16_3 : List NodeSpec := flattenBatches fmt_2_16_3 (ch_2_16_3.map Subtype.val)
private theorem ok_2_16_3 : LevelOK rd_2_16 (subGoal 2 16) 3 lv_2_16_3 :=
  @checkedBatches (freeVars 2 16) rd_2_16 _ _ _ sl_2_16 [[]] 3 fmt_2_16_3 [] fmt_2_16_3 pp_2_16 (raw_faithful (freeMask 2 16) p_2_16 q_2_16) sl_2_16_ok (by decide +kernel) (emptyLevelOK rd_2_16 (subGoal 2 16) 2) ch_2_16_3
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_2_16 : Lower (freeVars 2 16) (subGoal 2 16) 4 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 8, 9), (inputs.getD 2 zero, 8, 12), (inputs.getD 3 zero, 1, 9), (inputs.getD 5 zero, 1, 33)]) ok_2_16_3 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube2_16

section Cube2_0

private def p_2_0 : Nat → Bits
  | 0 => mk128 0xffff01ffffc0ffff 0xfffff80ffe3ffe3f
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0x80fffe03ffff03f0 0x1f81fff07fdc63c7
  | 3 => mk128 0xfffffffffffffc00 0x1fffffffffe07fff
  | 4 => mk128 0xfffffc07ffffff 0xe001ffff81ff83f8
  | 5 => mk128 0xff00000007ffffff 0xfffe000001fffc00
  | _ => 0
private def q_2_0 : Nat → Bits
  | 0 => mk128 0x8a111c4890c02cb2 0xa5925884b20dae1b
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0x2672243923cb0156 0x8ab0ab9474dc62c5
  | 3 => mk128 0x14a4489245155408 0x136535294960556e
  | 4 => mk128 0x58c8912076669a6c 0xc041c6ce11b683b0
  | 5 => mk128 0x60f0e1c387b8e38f 0x1c78070861fb7800
  | _ => 0
private theorem pp_2_0 : properPairs (subGoal 2 0) (asRow p_2_0) (asRow q_2_0) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_2_0 : List Decor := rawDecor (freeMask 2 0) p_2_0 q_2_0
private def sl_2_0 : List (Sig × Nat) := [(subcube 2 1, 5), (subcube 6 0, 5), (subcube 2 4, 5), (subcube 2 8, 5), (subcube 34 0, 5), (subcube 2 32, 5), (subcube 6 1, 4), (subcube 2 16, 4), (subcube 2 36, 4), (subcube 34 8, 4)]
private theorem sl_2_0_ok : ∀ s ∈ sl_2_0, Slice (freeVars 2 0) (subGoal 2 0) s.1 s.2 := by
  intro s hs
  simp only [sl_2_0, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact slice_correct (ms := fixRows 2 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_2_1
  · exact slice_correct (ms := fixRows 6 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_6_0
  · exact slice_correct (ms := fixRows 2 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_2_4
  · exact slice_correct (ms := fixRows 2 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_2_8
  · exact slice_correct (ms := fixRows 34 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_34_0
  · exact slice_correct (ms := fixRows 2 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_2_32
  · exact slice_correct (ms := fixRows 6 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_6_1
  · exact slice_correct (ms := fixRows 2 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_2_16
  · exact slice_correct (ms := fixRows 2 36) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_2_36
  · exact slice_correct (ms := fixRows 34 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_34_8
private def fmt_2_0_4 : ChartFormat := ⟨5, 3, 0, 0, 4⟩
private abbrev Batch_2_0_4 := CheckedBatch (freeVars 2 0) rd_2_0 (subGoal 2 0) sl_2_0 [[]] 4 fmt_2_0_4 [] fmt_2_0_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_2_0_4_0 : List Batch_2_0_4 := [
  ⟨⟨2,0x235c2dc86154e7554c0c08,0x1⟩,by decide +kernel⟩,
  ⟨⟨1,0x35c85d5134c,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_2_0_4 : List Batch_2_0_4 := ch_2_0_4_0
private noncomputable def lv_2_0_4 : List NodeSpec := flattenBatches fmt_2_0_4 (ch_2_0_4.map Subtype.val)
private theorem ok_2_0_4 : LevelOK rd_2_0 (subGoal 2 0) 4 lv_2_0_4 :=
  @checkedBatches (freeVars 2 0) rd_2_0 _ _ _ sl_2_0 [[]] 4 fmt_2_0_4 [] fmt_2_0_4 pp_2_0 (raw_faithful (freeMask 2 0) p_2_0 q_2_0) sl_2_0_ok (by decide +kernel) (emptyLevelOK rd_2_0 (subGoal 2 0) 3) ch_2_0_4

private def fmt_2_0_5 : ChartFormat := ⟨5, 2, 0, 3, 4⟩
private abbrev Batch_2_0_5 := CheckedBatch (freeVars 2 0) rd_2_0 (subGoal 2 0) sl_2_0 [[]] 5 fmt_2_0_4 (ch_2_0_4.map Subtype.val) fmt_2_0_5
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_2_0_5_0 : List Batch_2_0_5 := [
  ⟨⟨2,0x4688cd5c10288103234466ac08,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x9014788ac9810306a347560c08,0xa⟩,by decide +kernel⟩,
  ⟨⟨2,0x11a1730795046343560c2a,0x12⟩,by decide +kernel⟩,
  ⟨⟨2,0x8151a233550602635856a50c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x11117327860062c4564c0c,0xa⟩,by decide +kernel⟩,
  ⟨⟨2,0x4588ac981e288a35886aa0f,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x14b548cc2698288a34466174c,0x32⟩,by decide +kernel⟩,
  ⟨⟨2,0x8151a233512788735486b14c,0x1⟩,by decide +kernel⟩,
  ⟨⟨1,0x1a22e6134f,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_2_0_5 : List Batch_2_0_5 := ch_2_0_5_0
private noncomputable def lv_2_0_5 : List NodeSpec := flattenBatches fmt_2_0_5 (ch_2_0_5.map Subtype.val)
private theorem ok_2_0_5 : LevelOK rd_2_0 (subGoal 2 0) 5 lv_2_0_5 :=
  @checkedBatches (freeVars 2 0) rd_2_0 _ _ _ sl_2_0 [[]] 5 fmt_2_0_4 (ch_2_0_4.map Subtype.val) fmt_2_0_5 pp_2_0 (raw_faithful (freeMask 2 0) p_2_0 q_2_0) sl_2_0_ok (by decide +kernel) ok_2_0_4 ch_2_0_5

private def fmt_2_0_6 : ChartFormat := ⟨5, 1, 0, 4, 4⟩
private abbrev Batch_2_0_6 := CheckedBatch (freeVars 2 0) rd_2_0 (subGoal 2 0) sl_2_0 [[]] 6 fmt_2_0_5 (ch_2_0_5.map Subtype.val) fmt_2_0_6
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_2_0_6_0 : List Batch_2_0_6 := [
  ⟨⟨2,0x1ab41883078d50a509398b420c51082e3445608,0x1ec⟩,by decide +kernel⟩,
  ⟨⟨2,0xe629062884131a22b062515a0c4184468552a,0x7d298⟩,by decide +kernel⟩,
  ⟨⟨2,0x1272d083104131aa43261cc520c510826344560f,0xf596a8⟩,by decide +kernel⟩,
  ⟨⟨2,0x931272881da22a8824e5a10620826344564f,0x34504⟩,by decide +kernel⟩,
  ⟨⟨1,0x20c524e51043445513,0x1b46⟩,by decide +kernel⟩]
private noncomputable def ch_2_0_6 : List Batch_2_0_6 := ch_2_0_6_0
private noncomputable def lv_2_0_6 : List NodeSpec := flattenBatches fmt_2_0_6 (ch_2_0_6.map Subtype.val)
private theorem ok_2_0_6 : LevelOK rd_2_0 (subGoal 2 0) 6 lv_2_0_6 :=
  @checkedBatches (freeVars 2 0) rd_2_0 _ _ _ sl_2_0 [[]] 6 fmt_2_0_5 (ch_2_0_5.map Subtype.val) fmt_2_0_6 pp_2_0 (raw_faithful (freeMask 2 0) p_2_0 q_2_0) sl_2_0_ok (by decide +kernel) ok_2_0_5 ch_2_0_6

private def fmt_2_0_7 : ChartFormat := ⟨5, 0, 0, 3, 4⟩
private abbrev Batch_2_0_7 := CheckedBatch (freeVars 2 0) rd_2_0 (subGoal 2 0) sl_2_0 [[]] 7 fmt_2_0_6 (ch_2_0_6.map Subtype.val) fmt_2_0_7
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_2_0_7_0 : List Batch_2_0_7 := [
  ⟨⟨1,0x150c84346885,0xffa8⟩,by decide +kernel⟩]
private noncomputable def ch_2_0_7 : List Batch_2_0_7 := ch_2_0_7_0
private noncomputable def lv_2_0_7 : List NodeSpec := flattenBatches fmt_2_0_7 (ch_2_0_7.map Subtype.val)
private theorem ok_2_0_7 : LevelOK rd_2_0 (subGoal 2 0) 7 lv_2_0_7 :=
  @checkedBatches (freeVars 2 0) rd_2_0 _ _ _ sl_2_0 [[]] 7 fmt_2_0_6 (ch_2_0_6.map Subtype.val) fmt_2_0_7 pp_2_0 (raw_faithful (freeMask 2 0) p_2_0 q_2_0) sl_2_0_ok (by decide +kernel) ok_2_0_6 ch_2_0_7
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_2_0 : Lower (freeVars 2 0) (subGoal 2 0) 8 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 12, 13), (inputs.getD 2 zero, 9, 13), (inputs.getD 3 zero, 5, 13), (inputs.getD 4 zero, 9, 25), (inputs.getD 5 zero, 9, 41)]) ok_2_0_7 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube2_0

section Cube8_20

private def p_8_20 : Nat → Bits
  | 0 => mk128 0xbecfbecfbecfbecf 0xbecfbecfbecfbecf
  | 1 => mk128 0xdf73df73df73df73 0xdf73df73df73df73
  | 2 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 3 => mk128 0x0 0x0
  | 4 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 5 => mk128 0xefbcefbcefbcefbc 0xefbcefbcefbcefbc
  | _ => 0
private def q_8_20 : Nat → Bits
  | 0 => mk128 0x4205420542054205 0x4205420542054205
  | 1 => mk128 0x2412241224122412 0x2412241224122412
  | 2 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 3 => mk128 0x0 0x0
  | 4 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 5 => mk128 0x1828182818281828 0x1828182818281828
  | _ => 0
private theorem pp_8_20 : properPairs (subGoal 8 20) (asRow p_8_20) (asRow q_8_20) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_8_20 : List Decor := rawDecor (freeMask 8 20) p_8_20 q_8_20
private def sl_8_20 : List (Sig × Nat) := []
private theorem sl_8_20_ok : ∀ s ∈ sl_8_20, Slice (freeVars 8 20) (subGoal 8 20) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private def fmt_8_20_3 : ChartFormat := ⟨3, 0, 0, 0, 1⟩
private abbrev Batch_8_20_3 := CheckedBatch (freeVars 8 20) rd_8_20 (subGoal 8 20) sl_8_20 [[]] 3 fmt_8_20_3 [] fmt_8_20_3
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_8_20_3_0 : List Batch_8_20_3 := [
  ⟨⟨1,0x243,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_8_20_3 : List Batch_8_20_3 := ch_8_20_3_0
private noncomputable def lv_8_20_3 : List NodeSpec := flattenBatches fmt_8_20_3 (ch_8_20_3.map Subtype.val)
private theorem ok_8_20_3 : LevelOK rd_8_20 (subGoal 8 20) 3 lv_8_20_3 :=
  @checkedBatches (freeVars 8 20) rd_8_20 _ _ _ sl_8_20 [[]] 3 fmt_8_20_3 [] fmt_8_20_3 pp_8_20 (raw_faithful (freeMask 8 20) p_8_20 q_8_20) sl_8_20_ok (by decide +kernel) (emptyLevelOK rd_8_20 (subGoal 8 20) 2) ch_8_20_3
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_8_20 : Lower (freeVars 8 20) (subGoal 8 20) 4 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 5 zero, 1, 33)]) ok_8_20_3 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube8_20

section Cube8_4

private def p_8_4 : Nat → Bits
  | 0 => mk128 0xedf8fcff8fc3f9e7 0xdbf1f9ff1f87f3cf
  | 1 => mk128 0xf7ff3ffff1fffe3f 0xeffe7fffe3fffc7f
  | 2 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 3 => mk128 0x0 0x0
  | 4 => mk128 0x397fc0e7fe0387c6 0x72ff81cffc070f8c
  | 5 => mk128 0x3e7fff07fffc07f8 0x7cfffe0ffff80ff0
  | _ => 0
private def q_8_4 : Nat → Bits
  | 0 => mk128 0x520e09428250d0e2 0xa41c128504a1a1c5
  | 1 => mk128 0x881090011089220d 0x102120022112441a
  | 2 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 3 => mk128 0x0 0x0
  | 4 => mk128 0x6a2ba8da42a3746 0xd45751b48546e8c
  | 5 => mk128 0x1c420d6493045b0 0x38841ac92608b60
  | _ => 0
private theorem pp_8_4 : properPairs (subGoal 8 4) (asRow p_8_4) (asRow q_8_4) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_8_4 : List Decor := rawDecor (freeMask 8 4) p_8_4 q_8_4
private def sl_8_4 : List (Sig × Nat) := [(subcube 8 20, 4)]
private theorem sl_8_4_ok : ∀ s ∈ sl_8_4, Slice (freeVars 8 4) (subGoal 8 4) s.1 s.2 := by
  intro s hs
  simp only [sl_8_4, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 8 20) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_8_20
private def fmt_8_4_4 : ChartFormat := ⟨4, 0, 0, 1, 0⟩
private abbrev Batch_8_4_4 := CheckedBatch (freeVars 8 4) rd_8_4 (subGoal 8 4) sl_8_4 [[]] 4 fmt_8_4_4 [] fmt_8_4_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_8_4_4_0 : List Batch_8_4_4 := [
  ⟨⟨1,0x1e44,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_8_4_4 : List Batch_8_4_4 := ch_8_4_4_0
private noncomputable def lv_8_4_4 : List NodeSpec := flattenBatches fmt_8_4_4 (ch_8_4_4.map Subtype.val)
private theorem ok_8_4_4 : LevelOK rd_8_4 (subGoal 8 4) 4 lv_8_4_4 :=
  @checkedBatches (freeVars 8 4) rd_8_4 _ _ _ sl_8_4 [[]] 4 fmt_8_4_4 [] fmt_8_4_4 pp_8_4 (raw_faithful (freeMask 8 4) p_8_4 q_8_4) sl_8_4_ok (by decide +kernel) (emptyLevelOK rd_8_4 (subGoal 8 4) 3) ch_8_4_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_8_4 : Lower (freeVars 8 4) (subGoal 8 4) 5 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 4 zero, 33, 49), (inputs.getD 5 zero, 2, 34)]) ok_8_4_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube8_4

section Cube0_20

private def p_0_20 : Nat → Bits
  | 0 => mk128 0x7377446bbe967377 0x446bbe967377446b
  | 1 => mk128 0x9c7b8593df1b9c7b 0x8593df1b9c7b8593
  | 2 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 3 => mk128 0xef83fa1cffe3ef83 0xfa1cffe3ef83fa1c
  | 4 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 5 => mk128 0xffc03e0effc0ffc 0x3e0effc0ffc03e0
  | _ => 0
private def q_0_20 : Nat → Bits
  | 0 => mk128 0x8111082942288111 0x829422881110829
  | 1 => mk128 0x2422109224442422 0x1092244424221092
  | 2 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 3 => mk128 0x0 0x0
  | 4 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 5 => mk128 0x5a40234018015a40 0x234018015a402340
  | _ => 0
private theorem pp_0_20 : properPairs (subGoal 0 20) (asRow p_0_20) (asRow q_0_20) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_0_20 : List Decor := rawDecor (freeMask 0 20) p_0_20 q_0_20
private def sl_0_20 : List (Sig × Nat) := [(subcube 8 20, 4)]
private theorem sl_0_20_ok : ∀ s ∈ sl_0_20, Slice (freeVars 0 20) (subGoal 0 20) s.1 s.2 := by
  intro s hs
  simp only [sl_0_20, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 8 20) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_8_20
private def fmt_0_20_4 : ChartFormat := ⟨4, 0, 0, 1, 0⟩
private abbrev Batch_0_20_4 := CheckedBatch (freeVars 0 20) rd_0_20 (subGoal 0 20) sl_0_20 [[]] 4 fmt_0_20_4 [] fmt_0_20_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_20_4_0 : List Batch_0_20_4 := [
  ⟨⟨1,0x1e44,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_0_20_4 : List Batch_0_20_4 := ch_0_20_4_0
private noncomputable def lv_0_20_4 : List NodeSpec := flattenBatches fmt_0_20_4 (ch_0_20_4.map Subtype.val)
private theorem ok_0_20_4 : LevelOK rd_0_20 (subGoal 0 20) 4 lv_0_20_4 :=
  @checkedBatches (freeVars 0 20) rd_0_20 _ _ _ sl_0_20 [[]] 4 fmt_0_20_4 [] fmt_0_20_4 pp_0_20 (raw_faithful (freeMask 0 20) p_0_20 q_0_20) sl_0_20_ok (by decide +kernel) (emptyLevelOK rd_0_20 (subGoal 0 20) 3) ch_0_20_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_0_20 : Lower (freeVars 0 20) (subGoal 0 20) 5 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 3 zero, 0, 8), (inputs.getD 5 zero, 1, 33)]) ok_0_20_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube0_20

section Cube16_4

private def p_16_4 : Nat → Bits
  | 0 => mk128 0xbfcf9ff8fc3ff39f 0xbfcf9ff8fc3ff39f
  | 1 => mk128 0xdff3fcff1ff87cf3 0xdff3fcff1ff87cf3
  | 2 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 3 => mk128 0xebfc1f3fe03f8f1c 0xebfc1f3fe03f8f1c
  | 4 => mk128 0x0 0x0
  | 5 => mk128 0xf3ffe03fffc00fe0 0xf3ffe03fffc00fe0
  | _ => 0
private def q_16_4 : Nat → Bits
  | 0 => mk128 0x40602810250a4185 0x40602810250a4185
  | 1 => mk128 0x2089010908912432 0x2089010908912432
  | 2 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 3 => mk128 0x150b506a42a52e18 0x150b506a42a52e18
  | 4 => mk128 0x0 0x0
  | 5 => mk128 0xe221ab493064bc0 0xe221ab493064bc0
  | _ => 0
private theorem pp_16_4 : properPairs (subGoal 16 4) (asRow p_16_4) (asRow q_16_4) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_16_4 : List Decor := rawDecor (freeMask 16 4) p_16_4 q_16_4
private def sl_16_4 : List (Sig × Nat) := []
private theorem sl_16_4_ok : ∀ s ∈ sl_16_4, Slice (freeVars 16 4) (subGoal 16 4) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private def fmt_16_4_3 : ChartFormat := ⟨4, 0, 0, 0, 1⟩
private abbrev Batch_16_4_3 := CheckedBatch (freeVars 16 4) rd_16_4 (subGoal 16 4) sl_16_4 [[]] 3 fmt_16_4_3 [] fmt_16_4_3
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_16_4_3_0 : List Batch_16_4_3 := [
  ⟨⟨1,0xe44,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_16_4_3 : List Batch_16_4_3 := ch_16_4_3_0
private noncomputable def lv_16_4_3 : List NodeSpec := flattenBatches fmt_16_4_3 (ch_16_4_3.map Subtype.val)
private theorem ok_16_4_3 : LevelOK rd_16_4 (subGoal 16 4) 3 lv_16_4_3 :=
  @checkedBatches (freeVars 16 4) rd_16_4 _ _ _ sl_16_4 [[]] 3 fmt_16_4_3 [] fmt_16_4_3 pp_16_4 (raw_faithful (freeMask 16 4) p_16_4 q_16_4) sl_16_4_ok (by decide +kernel) (emptyLevelOK rd_16_4 (subGoal 16 4) 2) ch_16_4_3
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_16_4 : Lower (freeVars 16 4) (subGoal 16 4) 4 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 3 zero, 1, 9), (inputs.getD 5 zero, 2, 34)]) ok_16_4_3 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube16_4

section Cube32_4

private def p_32_4 : Nat → Bits
  | 0 => mk128 0xbfce7ff8e1fff27f 0xbfce7ff8e1fff27f
  | 1 => mk128 0xdbf07cff01f8fc73 0xdbf07cff01f8fc73
  | 2 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 3 => mk128 0xefff9f3ffe3f0f9c 0xefff9f3ffe3f0f9c
  | 4 => mk128 0xf3ffe03fffc00fe0 0xf3ffe03fffc00fe0
  | 5 => mk128 0x0 0x0
  | _ => 0
private def q_32_4 : Nat → Bits
  | 0 => mk128 0x40608810284c4225 0x40608810284c4225
  | 1 => mk128 0x248d51291492ac52 0x248d51291492ac52
  | 2 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 3 => mk128 0x1104404a44222498 0x1104404a44222498
  | 4 => mk128 0xe281ab49904cb60 0xe281ab49904cb60
  | 5 => mk128 0x0 0x0
  | _ => 0
private theorem pp_32_4 : properPairs (subGoal 32 4) (asRow p_32_4) (asRow q_32_4) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_32_4 : List Decor := rawDecor (freeMask 32 4) p_32_4 q_32_4
private def sl_32_4 : List (Sig × Nat) := []
private theorem sl_32_4_ok : ∀ s ∈ sl_32_4, Slice (freeVars 32 4) (subGoal 32 4) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private def fmt_32_4_3 : ChartFormat := ⟨4, 0, 0, 0, 1⟩
private abbrev Batch_32_4_3 := CheckedBatch (freeVars 32 4) rd_32_4 (subGoal 32 4) sl_32_4 [[]] 3 fmt_32_4_3 [] fmt_32_4_3
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_32_4_3_0 : List Batch_32_4_3 := [
  ⟨⟨1,0xe44,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_32_4_3 : List Batch_32_4_3 := ch_32_4_3_0
private noncomputable def lv_32_4_3 : List NodeSpec := flattenBatches fmt_32_4_3 (ch_32_4_3.map Subtype.val)
private theorem ok_32_4_3 : LevelOK rd_32_4 (subGoal 32 4) 3 lv_32_4_3 :=
  @checkedBatches (freeVars 32 4) rd_32_4 _ _ _ sl_32_4 [[]] 3 fmt_32_4_3 [] fmt_32_4_3 pp_32_4 (raw_faithful (freeMask 32 4) p_32_4 q_32_4) sl_32_4_ok (by decide +kernel) (emptyLevelOK rd_32_4 (subGoal 32 4) 2) ch_32_4_3
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_32_4 : Lower (freeVars 32 4) (subGoal 32 4) 4 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 8, 24)]) ok_32_4_3 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube32_4

section Cube0_4

private def p_0_4 : Nat → Bits
  | 0 => mk128 0xf0fc7fff0f1e3f1f 0x81c703fffc39c27f
  | 1 => mk128 0xff007fc7f01fc7e3 0xfff803f07cc67c73
  | 2 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 3 => mk128 0xffff87f8ffe007fc 0x1fffc7f83078f9c
  | 4 => mk128 0xfffff800fffff800 0x1ffff8003f80fe0
  | 5 => mk128 0xffffffff 0xfe00000003fff000
  | _ => 0
private def q_0_4 : Nat → Bits
  | 0 => mk128 0x1220a280030a0a04 0x908110965018c225
  | 1 => mk128 0x2019110830044121 0xd48292128421c52
  | 2 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 3 => mk128 0x4448140154200548 0x2452484909070498
  | 4 => mk128 0x8a904192a9569000 0x49a4b20232e80b60
  | 5 => mk128 0xce26624ce992692 0x7000c00c43b5e000
  | _ => 0
private theorem pp_0_4 : properPairs (subGoal 0 4) (asRow p_0_4) (asRow q_0_4) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_0_4 : List Decor := rawDecor (freeMask 0 4) p_0_4 q_0_4
private def sl_0_4 : List (Sig × Nat) := [(subcube 2 4, 5), (subcube 8 4, 5), (subcube 0 20, 5), (subcube 0 36, 5), (subcube 16 4, 4), (subcube 8 20, 4), (subcube 32 4, 4), (subcube 2 36, 4)]
private theorem sl_0_4_ok : ∀ s ∈ sl_0_4, Slice (freeVars 0 4) (subGoal 0 4) s.1 s.2 := by
  intro s hs
  simp only [sl_0_4, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact slice_correct (ms := fixRows 2 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_2_4
  · exact slice_correct (ms := fixRows 8 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_8_4
  · exact slice_correct (ms := fixRows 0 20) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_0_20
  · exact slice_correct (ms := fixRows 0 36) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_0_36
  · exact slice_correct (ms := fixRows 16 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_16_4
  · exact slice_correct (ms := fixRows 8 20) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_8_20
  · exact slice_correct (ms := fixRows 32 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_32_4
  · exact slice_correct (ms := fixRows 2 36) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_2_36
private def fmt_0_4_4 : ChartFormat := ⟨5, 3, 0, 0, 3⟩
private abbrev Batch_0_4_4 := CheckedBatch (freeVars 0 4) rd_0_4 (subGoal 0 4) sl_0_4 [[]] 4 fmt_0_4_4 [] fmt_0_4_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_4_4_0 : List Batch_0_4_4 := [
  ⟨⟨2,0x1e5c2d81482b5c65b00705,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x26e42d61484ce465ac0b09,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_0_4_4 : List Batch_0_4_4 := ch_0_4_4_0
private noncomputable def lv_0_4_4 : List NodeSpec := flattenBatches fmt_0_4_4 (ch_0_4_4.map Subtype.val)
private theorem ok_0_4_4 : LevelOK rd_0_4 (subGoal 0 4) 4 lv_0_4_4 :=
  @checkedBatches (freeVars 0 4) rd_0_4 _ _ _ sl_0_4 [[]] 4 fmt_0_4_4 [] fmt_0_4_4 pp_0_4 (raw_faithful (freeMask 0 4) p_0_4 q_0_4) sl_0_4_ok (by decide +kernel) (emptyLevelOK rd_0_4 (subGoal 0 4) 3) ch_0_4_4

private def fmt_0_4_5 : ChartFormat := ⟨5, 2, 0, 3, 3⟩
private abbrev Batch_0_4_5 := CheckedBatch (freeVars 0 4) rd_0_4 (subGoal 0 4) sl_0_4 [[]] 5 fmt_0_4_4 (ch_0_4_4.map Subtype.val) fmt_0_4_5
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_4_5_0 : List Batch_0_4_5 := [
  ⟨⟨2,0x98f2a18a41406354660705,0x1e⟩,by decide +kernel⟩,
  ⟨⟨2,0x4688cd560a620c523c886a905,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x65ab886b0055c135885b005,0x1e⟩,by decide +kernel⟩,
  ⟨⟨2,0x11a2335583904a3c886a907,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x18f5218a424063a4660b09,0x76⟩,by decide +kernel⟩,
  ⟨⟨2,0xa8a9910b58122344663609,0x76⟩,by decide +kernel⟩,
  ⟨⟨2,0x61a8d621a942c465c886ac09,0x32⟩,by decide +kernel⟩,
  ⟨⟨2,0x11a2330b1498831041a344661429,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x11ac435287186a35886a50c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x6181c688cd445c234706a12e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x11e4435489104a3c886a910,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x4105c688cd44a4234706a152,0x1⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_4_5_1 : List Batch_0_4_5 := [
  ⟨⟨2,0x1894688cc2ee02668861570,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_0_4_5 : List Batch_0_4_5 := (ch_0_4_5_0 ++ ch_0_4_5_1)
private noncomputable def lv_0_4_5 : List NodeSpec := flattenBatches fmt_0_4_5 (ch_0_4_5.map Subtype.val)
private theorem ok_0_4_5 : LevelOK rd_0_4 (subGoal 0 4) 5 lv_0_4_5 :=
  @checkedBatches (freeVars 0 4) rd_0_4 _ _ _ sl_0_4 [[]] 5 fmt_0_4_4 (ch_0_4_4.map Subtype.val) fmt_0_4_5 pp_0_4 (raw_faithful (freeMask 0 4) p_0_4 q_0_4) sl_0_4_ok (by decide +kernel) ok_0_4_4 ch_0_4_5

private def fmt_0_4_6 : ChartFormat := ⟨5, 1, 0, 4, 3⟩
private abbrev Batch_0_4_6 := CheckedBatch (freeVars 0 4) rd_0_4 (subGoal 0 4) sl_0_4 [[]] 6 fmt_0_4_5 (ch_0_4_5.map Subtype.val) fmt_0_4_6
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_4_6_0 : List Batch_0_4_6 := [
  ⟨⟨2,0x764b321088d11581dd92cc84223548605,0x7f98⟩,by decide +kernel⟩,
  ⟨⟨2,0x6543a21088d11582d950e884223a88609,0x1fb318⟩,by decide +kernel⟩,
  ⟨⟨2,0x6543291088d115831d952ce8842a3a88629,0x3626508⟩,by decide +kernel⟩,
  ⟨⟨2,0x654b3291098d1158b9950c841e344560e,0xca04⟩,by decide +kernel⟩,
  ⟨⟨2,0x764321078d115849d90c860223445610,0x1586⟩,by decide +kernel⟩,
  ⟨⟨2,0x7654329180a8ea219c1d90e8860263445652,0x1de0c⟩,by decide +kernel⟩]
private noncomputable def ch_0_4_6 : List Batch_0_4_6 := ch_0_4_6_0
private noncomputable def lv_0_4_6 : List NodeSpec := flattenBatches fmt_0_4_6 (ch_0_4_6.map Subtype.val)
private theorem ok_0_4_6 : LevelOK rd_0_4 (subGoal 0 4) 6 lv_0_4_6 :=
  @checkedBatches (freeVars 0 4) rd_0_4 _ _ _ sl_0_4 [[]] 6 fmt_0_4_5 (ch_0_4_5.map Subtype.val) fmt_0_4_6 pp_0_4 (raw_faithful (freeMask 0 4) p_0_4 q_0_4) sl_0_4_ok (by decide +kernel) ok_0_4_5 ch_0_4_6

private def fmt_0_4_7 : ChartFormat := ⟨5, 0, 0, 3, 3⟩
private abbrev Batch_0_4_7 := CheckedBatch (freeVars 0 4) rd_0_4 (subGoal 0 4) sl_0_4 [[]] 7 fmt_0_4_6 (ch_0_4_6.map Subtype.val) fmt_0_4_7
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_4_7_0 : List Batch_0_4_7 := [
  ⟨⟨1,0xf5a2346885,0x7ffd8⟩,by decide +kernel⟩]
private noncomputable def ch_0_4_7 : List Batch_0_4_7 := ch_0_4_7_0
private noncomputable def lv_0_4_7 : List NodeSpec := flattenBatches fmt_0_4_7 (ch_0_4_7.map Subtype.val)
private theorem ok_0_4_7 : LevelOK rd_0_4 (subGoal 0 4) 7 lv_0_4_7 :=
  @checkedBatches (freeVars 0 4) rd_0_4 _ _ _ sl_0_4 [[]] 7 fmt_0_4_6 (ch_0_4_6.map Subtype.val) fmt_0_4_7 pp_0_4 (raw_faithful (freeMask 0 4) p_0_4 q_0_4) sl_0_4_ok (by decide +kernel) ok_0_4_6 ch_0_4_7
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_0_4 : Lower (freeVars 0 4) (subGoal 0 4) 8 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 8, 24), (inputs.getD 5 zero, 2, 34)]) ok_0_4_7 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube0_4

section Cube16_0

private def p_16_0 : Nat → Bits
  | 0 => mk128 0xffffffffe07ffffe 0x3fffffffe3f8fff
  | 1 => mk128 0xf81fffffff81f03f 0xffff03ffffc8fe3f
  | 2 => mk128 0xffe03f81fffe003f 0xfc1ffc1f01f0f3cc
  | 3 => mk128 0xffffc001ffffffc0 0x1fffe001ff03f0
  | 4 => mk128 0x0 0x0
  | 5 => mk128 0x1ffffffff 0xffe0000001fffc00
  | _ => 0
private def q_16_0 : Nat → Bits
  | 0 => mk128 0x890489204016524a 0x41254431541384d5
  | 1 => mk128 0x10c91248a580a414 0x964a234aa8c83a2a
  | 2 => mk128 0xa243a42b6aaa0a27 0x5913e91c0d70d34c
  | 3 => mk128 0x4492074db34d3c81 0x921cb38831ed03b0
  | 4 => mk128 0x0 0x0
  | 5 => mk128 0x871c3871dc71cf39 0xe380c210c1beec00
  | _ => 0
private theorem pp_16_0 : properPairs (subGoal 16 0) (asRow p_16_0) (asRow q_16_0) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_16_0 : List Decor := rawDecor (freeMask 16 0) p_16_0 q_16_0
private def sl_16_0 : List (Sig × Nat) := [(subcube 16 8, 6)]
private theorem sl_16_0_ok : ∀ s ∈ sl_16_0, Slice (freeVars 16 0) (subGoal 16 0) s.1 s.2 := by
  intro s hs
  simp only [sl_16_0, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 16 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_16_8
private def fmt_16_0_6 : ChartFormat := ⟨5, 0, 0, 1, 0⟩
private abbrev Batch_16_0_6 := CheckedBatch (freeVars 16 0) rd_16_0 (subGoal 16 0) sl_16_0 [[]] 6 fmt_16_0_6 [] fmt_16_0_6
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_16_0_6_0 : List Batch_16_0_6 := [
  ⟨⟨1,0xc6885,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_16_0_6 : List Batch_16_0_6 := ch_16_0_6_0
private noncomputable def lv_16_0_6 : List NodeSpec := flattenBatches fmt_16_0_6 (ch_16_0_6.map Subtype.val)
private theorem ok_16_0_6 : LevelOK rd_16_0 (subGoal 16 0) 6 lv_16_0_6 :=
  @checkedBatches (freeVars 16 0) rd_16_0 _ _ _ sl_16_0 [[]] 6 fmt_16_0_6 [] fmt_16_0_6 pp_16_0 (raw_faithful (freeMask 16 0) p_16_0 q_16_0) sl_16_0_ok (by decide +kernel) (emptyLevelOK rd_16_0 (subGoal 16 0) 5) ch_16_0_6
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_16_0 : Lower (freeVars 16 0) (subGoal 16 0) 7 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 9, 13), (inputs.getD 3 zero, 5, 13), (inputs.getD 5 zero, 6, 38)]) ok_16_0_6 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube16_0

section Cube32_16

private def p_32_16 : Nat → Bits
  | 0 => mk128 0xbfce7ff8e1fff27f 0xbfce7ff8e1fff27f
  | 1 => mk128 0xd7f073ff01c7fc4f 0xd7f073ff01c7fc4f
  | 2 => mk128 0xe7ff833ffe070f8c 0xe7ff833ffe070f8c
  | 3 => mk128 0xfbfffc3ffff80ff0 0xfbfffc3ffff80ff0
  | 4 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 5 => mk128 0x0 0x0
  | _ => 0
private def q_32_16 : Nat → Bits
  | 0 => mk128 0x4060a00824512215 0x4060a00824512215
  | 1 => mk128 0x288d463118a2cc4a 0x288d463118a2cc4a
  | 2 => mk128 0x1924685a4c14668c 0x1924685a4c14668c
  | 3 => mk128 0x60802a491208960 0x60802a491208960
  | 4 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 5 => mk128 0x0 0x0
  | _ => 0
private theorem pp_32_16 : properPairs (subGoal 32 16) (asRow p_32_16) (asRow q_32_16) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_32_16 : List Decor := rawDecor (freeMask 32 16) p_32_16 q_32_16
private def sl_32_16 : List (Sig × Nat) := []
private theorem sl_32_16_ok : ∀ s ∈ sl_32_16, Slice (freeVars 32 16) (subGoal 32 16) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private def fmt_32_16_3 : ChartFormat := ⟨4, 0, 0, 0, 1⟩
private abbrev Batch_32_16_3 := CheckedBatch (freeVars 32 16) rd_32_16 (subGoal 32 16) sl_32_16 [[]] 3 fmt_32_16_3 [] fmt_32_16_3
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_32_16_3_0 : List Batch_32_16_3 := [
  ⟨⟨1,0xe44,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_32_16_3 : List Batch_32_16_3 := ch_32_16_3_0
private noncomputable def lv_32_16_3 : List NodeSpec := flattenBatches fmt_32_16_3 (ch_32_16_3.map Subtype.val)
private theorem ok_32_16_3 : LevelOK rd_32_16 (subGoal 32 16) 3 lv_32_16_3 :=
  @checkedBatches (freeVars 32 16) rd_32_16 _ _ _ sl_32_16 [[]] 3 fmt_32_16_3 [] fmt_32_16_3 pp_32_16 (raw_faithful (freeMask 32 16) p_32_16 q_32_16) sl_32_16_ok (by decide +kernel) (emptyLevelOK rd_32_16 (subGoal 32 16) 2) ch_32_16_3
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_32_16 : Lower (freeVars 32 16) (subGoal 32 16) 4 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 8, 12), (inputs.getD 3 zero, 1, 9)]) ok_32_16_3 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube32_16

section Cube32_0

private def p_32_0 : Nat → Bits
  | 0 => mk128 0xffffffffe07e03ff 0xfffffffffe23ffff
  | 1 => mk128 0xf03fffffff8003e0 0xffff07ffffc23e3f
  | 2 => mk128 0xffc07f01fffffc00 0xf81ff83f01fc33cc
  | 3 => mk128 0xffff8001ffffffff 0x1fffc001ffc3f0
  | 4 => mk128 0x1ffffffff 0xffe0000001fffc00
  | 5 => mk128 0x0 0x0
  | _ => 0
private def q_32_0 : Nat → Bits
  | 0 => mk128 0x12091220401640a9 0x292588515420d4d5
  | 1 => mk128 0x219224c9a5819150 0x564a46aaa9c22a2a
  | 2 => mk128 0x4487486aeaaad408 0x9b13d23c0cec334c
  | 3 => mk128 0x89240e8d334d1a72 0x41c6708315743b0
  | 4 => mk128 0xe3870f1dc71e39c 0xe7808430c1bbbc00
  | 5 => mk128 0x0 0x0
  | _ => 0
private theorem pp_32_0 : properPairs (subGoal 32 0) (asRow p_32_0) (asRow q_32_0) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_32_0 : List Decor := rawDecor (freeMask 32 0) p_32_0 q_32_0
private def sl_32_0 : List (Sig × Nat) := [(subcube 34 0, 5), (subcube 32 8, 5), (subcube 32 4, 4), (subcube 32 16, 4)]
private theorem sl_32_0_ok : ∀ s ∈ sl_32_0, Slice (freeVars 32 0) (subGoal 32 0) s.1 s.2 := by
  intro s hs
  simp only [sl_32_0, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact slice_correct (ms := fixRows 34 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_34_0
  · exact slice_correct (ms := fixRows 32 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_32_8
  · exact slice_correct (ms := fixRows 32 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_32_4
  · exact slice_correct (ms := fixRows 32 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_32_16
private def fmt_32_0_4 : ChartFormat := ⟨5, 2, 0, 0, 2⟩
private abbrev Batch_32_0_4 := CheckedBatch (freeVars 32 0) rd_32_0 (subGoal 32 0) sl_32_0 [[]] 4 fmt_32_0_4 [] fmt_32_0_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_32_0_4_0 : List Batch_32_0_4 := [
  ⟨⟨2,0x23582d28534465b208,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x23582d28946465aa10,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_32_0_4 : List Batch_32_0_4 := ch_32_0_4_0
private noncomputable def lv_32_0_4 : List NodeSpec := flattenBatches fmt_32_0_4 (ch_32_0_4.map Subtype.val)
private theorem ok_32_0_4 : LevelOK rd_32_0 (subGoal 32 0) 4 lv_32_0_4 :=
  @checkedBatches (freeVars 32 0) rd_32_0 _ _ _ sl_32_0 [[]] 4 fmt_32_0_4 [] fmt_32_0_4 pp_32_0 (raw_faithful (freeMask 32 0) p_32_0 q_32_0) sl_32_0_ok (by decide +kernel) (emptyLevelOK rd_32_0 (subGoal 32 0) 3) ch_32_0_4

private def fmt_32_0_5 : ChartFormat := ⟨5, 1, 0, 2, 2⟩
private abbrev Batch_32_0_5 := CheckedBatch (freeVars 32 0) rd_32_0 (subGoal 32 0) sl_32_0 [[]] 5 fmt_32_0_4 (ch_32_0_4.map Subtype.val) fmt_32_0_5
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_32_0_5_0 : List Batch_32_0_5 := [
  ⟨⟨2,0x1b1a22b04514685507,0xa⟩,by decide +kernel⟩,
  ⟨⟨2,0x131a22b0806344560a,0x56⟩,by decide +kernel⟩,
  ⟨⟨2,0x131aa4328063445612,0x22⟩,by decide +kernel⟩]
private noncomputable def ch_32_0_5 : List Batch_32_0_5 := ch_32_0_5_0
private noncomputable def lv_32_0_5 : List NodeSpec := flattenBatches fmt_32_0_5 (ch_32_0_5.map Subtype.val)
private theorem ok_32_0_5 : LevelOK rd_32_0 (subGoal 32 0) 5 lv_32_0_5 :=
  @checkedBatches (freeVars 32 0) rd_32_0 _ _ _ sl_32_0 [[]] 5 fmt_32_0_4 (ch_32_0_4.map Subtype.val) fmt_32_0_5 pp_32_0 (raw_faithful (freeMask 32 0) p_32_0 q_32_0) sl_32_0_ok (by decide +kernel) ok_32_0_4 ch_32_0_5

private def fmt_32_0_6 : ChartFormat := ⟨5, 0, 0, 3, 2⟩
private abbrev Batch_32_0_6 := CheckedBatch (freeVars 32 0) rd_32_0 (subGoal 32 0) sl_32_0 [[]] 6 fmt_32_0_5 (ch_32_0_5.map Subtype.val) fmt_32_0_6
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_32_0_6_0 : List Batch_32_0_6 := [
  ⟨⟨1,0x39246885,0x7fc⟩,by decide +kernel⟩]
private noncomputable def ch_32_0_6 : List Batch_32_0_6 := ch_32_0_6_0
private noncomputable def lv_32_0_6 : List NodeSpec := flattenBatches fmt_32_0_6 (ch_32_0_6.map Subtype.val)
private theorem ok_32_0_6 : LevelOK rd_32_0 (subGoal 32 0) 6 lv_32_0_6 :=
  @checkedBatches (freeVars 32 0) rd_32_0 _ _ _ sl_32_0 [[]] 6 fmt_32_0_5 (ch_32_0_5.map Subtype.val) fmt_32_0_6 pp_32_0 (raw_faithful (freeMask 32 0) p_32_0 q_32_0) sl_32_0_ok (by decide +kernel) ok_32_0_5 ch_32_0_6
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_32_0 : Lower (freeVars 32 0) (subGoal 32 0) 7 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 9, 13), (inputs.getD 3 zero, 5, 13), (inputs.getD 4 zero, 9, 25)]) ok_32_0_6 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube32_0

section Cube0_1

private def p_0_1 : Nat → Bits
  | 0 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 1 => mk128 0x71dce67f99fe7f83 0x188cf8cfc7f80c67
  | 2 => mk128 0x81e0f863e18f8e63 0xe0f0cf0cfb864a5a
  | 3 => mk128 0xfe00ff83fe0ff07c 0xff0ff0fc00739c
  | 4 => mk128 0xffff0003fff0007f 0xff000fff000783e0
  | 5 => mk128 0xfffffffc0000007f 0xfffff0000007fc00
  | _ => 0
private def q_0_1 : Nat → Bits
  | 0 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0x8c5934c4d31c11e3 0x26926926730e4a4a
  | 3 => mk128 0x1002400900200204 0x24024080101094
  | 4 => mk128 0x248811521004a4a9 0x4a000caa11228360
  | 5 => mk128 0x4910840045494952 0x94caa00022456c00
  | _ => 0
private theorem pp_0_1 : properPairs (subGoal 0 1) (asRow p_0_1) (asRow q_0_1) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_0_1 : List Decor := rawDecor (freeMask 0 1) p_0_1 q_0_1
private def sl_0_1 : List (Sig × Nat) := [(subcube 2 1, 5)]
private theorem sl_0_1_ok : ∀ s ∈ sl_0_1, Slice (freeVars 0 1) (subGoal 0 1) s.1 s.2 := by
  intro s hs
  simp only [sl_0_1, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 2 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_2_1
private def fmt_0_1_5 : ChartFormat := ⟨5, 0, 0, 1, 0⟩
private abbrev Batch_0_1_5 := CheckedBatch (freeVars 0 1) rd_0_1 (subGoal 0 1) sl_0_1 [[]] 5 fmt_0_1_5 [] fmt_0_1_5
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_1_5_0 : List Batch_0_1_5 := [
  ⟨⟨1,0xc6885,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_0_1_5 : List Batch_0_1_5 := ch_0_1_5_0
private noncomputable def lv_0_1_5 : List NodeSpec := flattenBatches fmt_0_1_5 (ch_0_1_5.map Subtype.val)
private theorem ok_0_1_5 : LevelOK rd_0_1 (subGoal 0 1) 5 lv_0_1_5 :=
  @checkedBatches (freeVars 0 1) rd_0_1 _ _ _ sl_0_1 [[]] 5 fmt_0_1_5 [] fmt_0_1_5 pp_0_1 (raw_faithful (freeMask 0 1) p_0_1 q_0_1) sl_0_1_ok (by decide +kernel) (emptyLevelOK rd_0_1 (subGoal 0 1) 4) ch_0_1_5
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_0_1 : Lower (freeVars 0 1) (subGoal 0 1) 6 :=
  lower_of_search (xs := [(inputs.getD 1 zero, 0, 2), (inputs.getD 2 zero, 8, 12), (inputs.getD 3 zero, 4, 12), (inputs.getD 4 zero, 8, 24), (inputs.getD 5 zero, 8, 40)]) ok_0_1_5 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube0_1

section Cube1_2

private def p_1_2 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 2 => mk128 0xffbfc7fffe3fff1f 0xfbfc7fffe3fff1ff
  | 3 => mk128 0x67d7f879ffc707e6 0x7d7f879ffc707e67
  | 4 => mk128 0x87e7ff81fff807f8 0x7e7ff81fff807f87
  | 5 => mk128 0xf8fbfffe3ffff8ff 0x8fbfffe3ffff8ff8
  | _ => 0
private def q_1_2 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 2 => mk128 0xab4071100609310a 0xb4071100609310ab
  | 3 => mk128 0x652897229a425266 0x52897229a4252665
  | 4 => mk128 0x861922752c90a4b8 0x61922752c90a4b86
  | 5 => mk128 0x50060441b124c0d5 0x60441b124c0d50
  | _ => 0
private theorem pp_1_2 : properPairs (subGoal 1 2) (asRow p_1_2) (asRow q_1_2) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_1_2 : List Decor := rawDecor (freeMask 1 2) p_1_2 q_1_2
private def sl_1_2 : List (Sig × Nat) := [(subcube 1 10, 4)]
private theorem sl_1_2_ok : ∀ s ∈ sl_1_2, Slice (freeVars 1 2) (subGoal 1 2) s.1 s.2 := by
  intro s hs
  simp only [sl_1_2, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 1 10) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_1_10
private def fmt_1_2_4 : ChartFormat := ⟨4, 0, 0, 1, 0⟩
private abbrev Batch_1_2_4 := CheckedBatch (freeVars 1 2) rd_1_2 (subGoal 1 2) sl_1_2 [[]] 4 fmt_1_2_4 [] fmt_1_2_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_1_2_4_0 : List Batch_1_2_4 := [
  ⟨⟨1,0x1e44,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_1_2_4 : List Batch_1_2_4 := ch_1_2_4_0
private noncomputable def lv_1_2_4 : List NodeSpec := flattenBatches fmt_1_2_4 (ch_1_2_4.map Subtype.val)
private theorem ok_1_2_4 : LevelOK rd_1_2 (subGoal 1 2) 4 lv_1_2_4 :=
  @checkedBatches (freeVars 1 2) rd_1_2 _ _ _ sl_1_2 [[]] 4 fmt_1_2_4 [] fmt_1_2_4 pp_1_2 (raw_faithful (freeMask 1 2) p_1_2 q_1_2) sl_1_2_ok (by decide +kernel) (emptyLevelOK rd_1_2 (subGoal 1 2) 3) ch_1_2_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_1_2 : Lower (freeVars 1 2) (subGoal 1 2) 5 :=
  lower_of_search (xs := [(inputs.getD 2 zero, 24, 28), (inputs.getD 3 zero, 20, 28), (inputs.getD 4 zero, 12, 28), (inputs.getD 5 zero, 4, 36)]) ok_1_2_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube1_2

section Cube1_0

private def p_1_0 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0x7fffffffffe03fc0 0xffffffff8007fff8
  | 2 => mk128 0x807fffffffffffff 0x3fffffffff87fff
  | 3 => mk128 0xff803fe03fffffff 0xfc0fc01fffff8e3f
  | 4 => mk128 0xffffc0003fffffff 0xfff0001ffffff03f
  | 5 => mk128 0xffffffffc0003fff 0xffffffe0003fffc0
  | _ => 0
private def q_1_0 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0xa954b228a238bc0 0x2cb2d5a58d03b6f8
  | 2 => mk128 0xea219145144494cb 0x15569cab5585b5b
  | 3 => mk128 0x23752289a6892755 0x54098c9359ad8e2d
  | 4 => mk128 0x4c463b16391239a6 0x9a60311c6e36f036
  | 5 => mk128 0x70783c183e1c3e38 0xe38e3e00703f6d80
  | _ => 0
private theorem pp_1_0 : properPairs (subGoal 1 0) (asRow p_1_0) (asRow q_1_0) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_1_0 : List Decor := rawDecor (freeMask 1 0) p_1_0 q_1_0
private def sl_1_0 : List (Sig × Nat) := [(subcube 1 2, 5)]
private theorem sl_1_0_ok : ∀ s ∈ sl_1_0, Slice (freeVars 1 0) (subGoal 1 0) s.1 s.2 := by
  intro s hs
  simp only [sl_1_0, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 1 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_1_2
private def fmt_1_0_5 : ChartFormat := ⟨5, 0, 0, 1, 0⟩
private abbrev Batch_1_0_5 := CheckedBatch (freeVars 1 0) rd_1_0 (subGoal 1 0) sl_1_0 [[]] 5 fmt_1_0_5 [] fmt_1_0_5
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_1_0_5_0 : List Batch_1_0_5 := [
  ⟨⟨1,0xc6885,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_1_0_5 : List Batch_1_0_5 := ch_1_0_5_0
private noncomputable def lv_1_0_5 : List NodeSpec := flattenBatches fmt_1_0_5 (ch_1_0_5.map Subtype.val)
private theorem ok_1_0_5 : LevelOK rd_1_0 (subGoal 1 0) 5 lv_1_0_5 :=
  @checkedBatches (freeVars 1 0) rd_1_0 _ _ _ sl_1_0 [[]] 5 fmt_1_0_5 [] fmt_1_0_5 pp_1_0 (raw_faithful (freeMask 1 0) p_1_0 q_1_0) sl_1_0_ok (by decide +kernel) (emptyLevelOK rd_1_0 (subGoal 1 0) 4) ch_1_0_5
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_1_0 : Lower (freeVars 1 0) (subGoal 1 0) 6 :=
  lower_of_search (xs := [(inputs.getD 1 zero, 36, 38), (inputs.getD 2 zero, 24, 28), (inputs.getD 3 zero, 20, 28), (inputs.getD 4 zero, 12, 28), (inputs.getD 5 zero, 6, 38)]) ok_1_0_5 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube1_0

section Cube0_2

private def p_0_2 : Nat → Bits
  | 0 => mk128 0xfcfc7ffffff0718f 0x1e0fc7ffffc1247f
  | 1 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 2 => mk128 0x7f1f83c78e0f81f3 0xe7f1f9861c06dbaa
  | 3 => mk128 0x801ffc07f00ffe03 0xf801fe07e038e3cc
  | 4 => mk128 0x1ffff8000ffffc 0x1fff8003f03f0
  | 5 => mk128 0xffe00000000fffff 0xfffe0000003ffc00
  | _ => 0
private def q_0_2 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 2 => mk128 0x1824188910318091 0x2260c892584249aa
  | 3 => mk128 0x2949299602d6b203 0x48a55225c898e2cc
  | 4 => mk128 0x52925303256b55a4 0x149a570912f0370
  | 5 => mk128 0x60036224498c694a 0x958c00410235b400
  | _ => 0
private theorem pp_0_2 : properPairs (subGoal 0 2) (asRow p_0_2) (asRow q_0_2) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_0_2 : List Decor := rawDecor (freeMask 0 2) p_0_2 q_0_2
private def sl_0_2 : List (Sig × Nat) := [(subcube 1 2, 5)]
private theorem sl_0_2_ok : ∀ s ∈ sl_0_2, Slice (freeVars 0 2) (subGoal 0 2) s.1 s.2 := by
  intro s hs
  simp only [sl_0_2, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 1 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_1_2
private def fmt_0_2_5 : ChartFormat := ⟨5, 0, 0, 1, 0⟩
private abbrev Batch_0_2_5 := CheckedBatch (freeVars 0 2) rd_0_2 (subGoal 0 2) sl_0_2 [[]] 5 fmt_0_2_5 [] fmt_0_2_5
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_2_5_0 : List Batch_0_2_5 := [
  ⟨⟨1,0xc6885,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_0_2_5 : List Batch_0_2_5 := ch_0_2_5_0
private noncomputable def lv_0_2_5 : List NodeSpec := flattenBatches fmt_0_2_5 (ch_0_2_5.map Subtype.val)
private theorem ok_0_2_5 : LevelOK rd_0_2 (subGoal 0 2) 5 lv_0_2_5 :=
  @checkedBatches (freeVars 0 2) rd_0_2 _ _ _ sl_0_2 [[]] 5 fmt_0_2_5 [] fmt_0_2_5 pp_0_2 (raw_faithful (freeMask 0 2) p_0_2 q_0_2) sl_0_2_ok (by decide +kernel) (emptyLevelOK rd_0_2 (subGoal 0 2) 4) ch_0_2_5
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_0_2 : Lower (freeVars 0 2) (subGoal 0 2) 6 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 0, 1), (inputs.getD 2 zero, 24, 28), (inputs.getD 3 zero, 20, 28), (inputs.getD 4 zero, 12, 28), (inputs.getD 5 zero, 4, 36)]) ok_0_2_5 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube0_2

section Cube8_0

private def p_8_0 : Nat → Bits
  | 0 => mk128 0xfffffffffe07ffff 0xf01fffffff1fe3ff
  | 1 => mk128 0xfffffffffff81f01 0xffffffffffe23fff
  | 2 => mk128 0x3f80fe03fffe001 0xffe0f81f80fc3ccc
  | 3 => mk128 0x0 0x0
  | 4 => mk128 0x3fff0003ffffffe 0xffe000ffc0f0
  | 5 => mk128 0xfc0000003fffffff 0xffff000000ffff00
  | _ => 0
private def q_8_0 : Nat → Bits
  | 0 => mk128 0x288922490a01652a 0x52092934aa0ce155
  | 1 => mk128 0x5112449214580a40 0xa4b2564954620eaa
  | 2 => mk128 0x9aa0e90b6eaaa0a9 0x3ac89b1e06bc34cc
  | 3 => mk128 0x0 0x0
  | 4 => mk128 0x634481d3b734d3cc 0xc90e78c18f740f0
  | 5 => mk128 0x83870e1c39c71cf1 0xcf1c041060dbbb00
  | _ => 0
private theorem pp_8_0 : properPairs (subGoal 8 0) (asRow p_8_0) (asRow q_8_0) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_8_0 : List Decor := rawDecor (freeMask 8 0) p_8_0 q_8_0
private def sl_8_0 : List (Sig × Nat) := [(subcube 8 4, 5)]
private theorem sl_8_0_ok : ∀ s ∈ sl_8_0, Slice (freeVars 8 0) (subGoal 8 0) s.1 s.2 := by
  intro s hs
  simp only [sl_8_0, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 8 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_8_4
private def fmt_8_0_5 : ChartFormat := ⟨5, 0, 0, 1, 0⟩
private abbrev Batch_8_0_5 := CheckedBatch (freeVars 8 0) rd_8_0 (subGoal 8 0) sl_8_0 [[]] 5 fmt_8_0_5 [] fmt_8_0_5
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_8_0_5_0 : List Batch_8_0_5 := [
  ⟨⟨1,0xc6885,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_8_0_5 : List Batch_8_0_5 := ch_8_0_5_0
private noncomputable def lv_8_0_5 : List NodeSpec := flattenBatches fmt_8_0_5 (ch_8_0_5.map Subtype.val)
private theorem ok_8_0_5 : LevelOK rd_8_0 (subGoal 8 0) 5 lv_8_0_5 :=
  @checkedBatches (freeVars 8 0) rd_8_0 _ _ _ sl_8_0 [[]] 5 fmt_8_0_5 [] fmt_8_0_5 pp_8_0 (raw_faithful (freeMask 8 0) p_8_0 q_8_0) sl_8_0_ok (by decide +kernel) (emptyLevelOK rd_8_0 (subGoal 8 0) 4) ch_8_0_5
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_8_0 : Lower (freeVars 8 0) (subGoal 8 0) 6 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 34, 38), (inputs.getD 4 zero, 33, 49), (inputs.getD 5 zero, 6, 38)]) ok_8_0_5 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube8_0

section Cube8_16

private def p_8_16 : Nat → Bits
  | 0 => mk128 0xeff9ffff8ffff8ff 0xdff3ffff1ffff1ff
  | 1 => mk128 0xf5fe3cfff1c3ff27 0xebfc79ffe387fe4f
  | 2 => mk128 0x397fc0e7fe0387c6 0x72ff81cffc070f8c
  | 3 => mk128 0x0 0x0
  | 4 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 5 => mk128 0x3e7fff07fffc07f8 0x7cfffe0ffff80ff0
  | _ => 0
private def q_8_16 : Nat → Bits
  | 0 => mk128 0x500c08008248904a 0xa018100104912095
  | 1 => mk128 0x8a11914310916325 0x142322862122c64a
  | 2 => mk128 0x6a4ba8da42a35c6 0xd49751b48546b8c
  | 3 => mk128 0x0 0x0
  | 4 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 5 => mk128 0x1c120d6493046b0 0x38241ac92608d60
  | _ => 0
private theorem pp_8_16 : properPairs (subGoal 8 16) (asRow p_8_16) (asRow q_8_16) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_8_16 : List Decor := rawDecor (freeMask 8 16) p_8_16 q_8_16
private def sl_8_16 : List (Sig × Nat) := [(subcube 8 20, 4)]
private theorem sl_8_16_ok : ∀ s ∈ sl_8_16, Slice (freeVars 8 16) (subGoal 8 16) s.1 s.2 := by
  intro s hs
  simp only [sl_8_16, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 8 20) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_8_20
private def fmt_8_16_4 : ChartFormat := ⟨4, 0, 0, 1, 0⟩
private abbrev Batch_8_16_4 := CheckedBatch (freeVars 8 16) rd_8_16 (subGoal 8 16) sl_8_16 [[]] 4 fmt_8_16_4 [] fmt_8_16_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_8_16_4_0 : List Batch_8_16_4 := [
  ⟨⟨1,0x1e44,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_8_16_4 : List Batch_8_16_4 := ch_8_16_4_0
private noncomputable def lv_8_16_4 : List NodeSpec := flattenBatches fmt_8_16_4 (ch_8_16_4.map Subtype.val)
private theorem ok_8_16_4 : LevelOK rd_8_16 (subGoal 8 16) 4 lv_8_16_4 :=
  @checkedBatches (freeVars 8 16) rd_8_16 _ _ _ sl_8_16 [[]] 4 fmt_8_16_4 [] fmt_8_16_4 pp_8_16 (raw_faithful (freeMask 8 16) p_8_16 q_8_16) sl_8_16_ok (by decide +kernel) (emptyLevelOK rd_8_16 (subGoal 8 16) 3) ch_8_16_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_8_16 : Lower (freeVars 8 16) (subGoal 8 16) 5 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 34, 38), (inputs.getD 5 zero, 1, 33)]) ok_8_16_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube8_16

section Cube1_18

private def p_1_18 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 2 => mk128 0xbecfbecfbecfbecf 0xbecfbecfbecfbecf
  | 3 => mk128 0xdf73df73df73df73 0xdf73df73df73df73
  | 4 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 5 => mk128 0xefbcefbcefbcefbc 0xefbcefbcefbcefbc
  | _ => 0
private def q_1_18 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 2 => mk128 0x4205420542054205 0x4205420542054205
  | 3 => mk128 0x2412241224122412 0x2412241224122412
  | 4 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 5 => mk128 0x1828182818281828 0x1828182818281828
  | _ => 0
private theorem pp_1_18 : properPairs (subGoal 1 18) (asRow p_1_18) (asRow q_1_18) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_1_18 : List Decor := rawDecor (freeMask 1 18) p_1_18 q_1_18
private def sl_1_18 : List (Sig × Nat) := []
private theorem sl_1_18_ok : ∀ s ∈ sl_1_18, Slice (freeVars 1 18) (subGoal 1 18) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private def fmt_1_18_3 : ChartFormat := ⟨3, 0, 0, 0, 1⟩
private abbrev Batch_1_18_3 := CheckedBatch (freeVars 1 18) rd_1_18 (subGoal 1 18) sl_1_18 [[]] 3 fmt_1_18_3 [] fmt_1_18_3
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_1_18_3_0 : List Batch_1_18_3 := [
  ⟨⟨1,0x243,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_1_18_3 : List Batch_1_18_3 := ch_1_18_3_0
private noncomputable def lv_1_18_3 : List NodeSpec := flattenBatches fmt_1_18_3 (ch_1_18_3.map Subtype.val)
private theorem ok_1_18_3 : LevelOK rd_1_18 (subGoal 1 18) 3 lv_1_18_3 :=
  @checkedBatches (freeVars 1 18) rd_1_18 _ _ _ sl_1_18 [[]] 3 fmt_1_18_3 [] fmt_1_18_3 pp_1_18 (raw_faithful (freeMask 1 18) p_1_18 q_1_18) sl_1_18_ok (by decide +kernel) (emptyLevelOK rd_1_18 (subGoal 1 18) 2) ch_1_18_3
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_1_18 : Lower (freeVars 1 18) (subGoal 1 18) 4 :=
  lower_of_search (xs := [(inputs.getD 2 zero, 8, 12), (inputs.getD 3 zero, 4, 12), (inputs.getD 5 zero, 4, 36)]) ok_1_18_3 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube1_18

section Cube0_18

private def p_0_18 : Nat → Bits
  | 0 => mk128 0xf1b77c27feaef1b7 0x7c27feaef1b77c27
  | 1 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 2 => mk128 0x3e3ba0dabf333e3b 0xa0dabf333e3ba0da
  | 3 => mk128 0xcfc3c31cdfc3cfc3 0xc31cdfc3cfc3c31c
  | 4 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 5 => mk128 0xffc03e0effc0ffc 0x3e0effc0ffc03e0
  | _ => 0
private def q_0_18 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 2 => mk128 0x4211044a42444211 0x44a42444211044a
  | 3 => mk128 0x1482091424181482 0x914241814820914
  | 4 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 5 => mk128 0xa92012a01801a920 0x12a01801a92012a0
  | _ => 0
private theorem pp_0_18 : properPairs (subGoal 0 18) (asRow p_0_18) (asRow q_0_18) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_0_18 : List Decor := rawDecor (freeMask 0 18) p_0_18 q_0_18
private def sl_0_18 : List (Sig × Nat) := [(subcube 1 18, 4)]
private theorem sl_0_18_ok : ∀ s ∈ sl_0_18, Slice (freeVars 0 18) (subGoal 0 18) s.1 s.2 := by
  intro s hs
  simp only [sl_0_18, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 1 18) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_1_18
private def fmt_0_18_4 : ChartFormat := ⟨4, 0, 0, 1, 0⟩
private abbrev Batch_0_18_4 := CheckedBatch (freeVars 0 18) rd_0_18 (subGoal 0 18) sl_0_18 [[]] 4 fmt_0_18_4 [] fmt_0_18_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_18_4_0 : List Batch_0_18_4 := [
  ⟨⟨1,0x1e44,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_0_18_4 : List Batch_0_18_4 := ch_0_18_4_0
private noncomputable def lv_0_18_4 : List NodeSpec := flattenBatches fmt_0_18_4 (ch_0_18_4.map Subtype.val)
private theorem ok_0_18_4 : LevelOK rd_0_18 (subGoal 0 18) 4 lv_0_18_4 :=
  @checkedBatches (freeVars 0 18) rd_0_18 _ _ _ sl_0_18 [[]] 4 fmt_0_18_4 [] fmt_0_18_4 pp_0_18 (raw_faithful (freeMask 0 18) p_0_18 q_0_18) sl_0_18_ok (by decide +kernel) (emptyLevelOK rd_0_18 (subGoal 0 18) 3) ch_0_18_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_0_18 : Lower (freeVars 0 18) (subGoal 0 18) 5 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 0, 1), (inputs.getD 2 zero, 8, 12), (inputs.getD 3 zero, 4, 12), (inputs.getD 5 zero, 4, 36)]) ok_0_18_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube0_18

section Cube1_16

private def p_1_16 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0xfcbbc3ff3e3fe03f 0xcbbc3ff3e3fe03fc
  | 2 => mk128 0x7fdffc7fffc7ffc7 0xfdffc7fffc7ffc7f
  | 3 => mk128 0x8fefff8ffff8fff8 0xfefff8ffff8fff8f
  | 4 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 5 => mk128 0xf0f3fff03fff00ff 0xf3fff03fff00ff0
  | _ => 0
private def q_1_16 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0xbc4479224e09261b 0xc4479224e09261bc
  | 2 => mk128 0x55208b0412424a45 0x5208b0412424a455
  | 3 => mk128 0x8a111068249094a8 0xa111068249094a8a
  | 4 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 5 => mk128 0x600e224eb92418f6 0xe224eb92418f60
  | _ => 0
private theorem pp_1_16 : properPairs (subGoal 1 16) (asRow p_1_16) (asRow q_1_16) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_1_16 : List Decor := rawDecor (freeMask 1 16) p_1_16 q_1_16
private def sl_1_16 : List (Sig × Nat) := [(subcube 1 18, 4)]
private theorem sl_1_16_ok : ∀ s ∈ sl_1_16, Slice (freeVars 1 16) (subGoal 1 16) s.1 s.2 := by
  intro s hs
  simp only [sl_1_16, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 1 18) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_1_18
private def fmt_1_16_4 : ChartFormat := ⟨4, 0, 0, 1, 0⟩
private abbrev Batch_1_16_4 := CheckedBatch (freeVars 1 16) rd_1_16 (subGoal 1 16) sl_1_16 [[]] 4 fmt_1_16_4 [] fmt_1_16_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_1_16_4_0 : List Batch_1_16_4 := [
  ⟨⟨1,0x1e44,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_1_16_4 : List Batch_1_16_4 := ch_1_16_4_0
private noncomputable def lv_1_16_4 : List NodeSpec := flattenBatches fmt_1_16_4 (ch_1_16_4.map Subtype.val)
private theorem ok_1_16_4 : LevelOK rd_1_16 (subGoal 1 16) 4 lv_1_16_4 :=
  @checkedBatches (freeVars 1 16) rd_1_16 _ _ _ sl_1_16 [[]] 4 fmt_1_16_4 [] fmt_1_16_4 pp_1_16 (raw_faithful (freeMask 1 16) p_1_16 q_1_16) sl_1_16_ok (by decide +kernel) (emptyLevelOK rd_1_16 (subGoal 1 16) 3) ch_1_16_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_1_16 : Lower (freeVars 1 16) (subGoal 1 16) 5 :=
  lower_of_search (xs := [(inputs.getD 1 zero, 36, 38), (inputs.getD 2 zero, 8, 12), (inputs.getD 3 zero, 4, 12), (inputs.getD 5 zero, 6, 38)]) ok_1_16_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube1_16

section Cube0_0

private def p_0_0 : Nat → Bits
  | 0 => mk128 0xe007ffffffffffff 0xfc047f1fc623ffff
  | 1 => mk128 0x7c0ffff80ffff 0xfc7b88e47fc23e3f
  | 2 => mk128 0xfff800f80fff03f8 0x383f0f879fc33cc
  | 3 => mk128 0xffffff000ffffc00 0x3fc00ff81ffc3f0
  | 4 => mk128 0xfffffffff0000000 0x3ffff0001fffc00
  | 5 => mk128 0x0 0x3fffffffe000000
  | _ => 0
private def q_0_0 : Nat → Bits
  | 0 => mk128 0x6081492892b1068a 0xa8003309c220d4d5
  | 1 => mk128 0x32290572508e955 0x503988641dc22a2a
  | 2 => mk128 0xada8089989fa23e0 0x1982f0b868ec334c
  | 3 => mk128 0xd634f2020e4cf040 0x62dc00f6815743b0
  | 4 => mk128 0x1bc73ce7c0104181 0x836fdd0001bbbc00
  | 5 => mk128 0x1c00200400608206 0x3f76edf76000000
  | _ => 0
private theorem pp_0_0 : properPairs (subGoal 0 0) (asRow p_0_0) (asRow q_0_0) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_0_0 : List Decor := rawDecor (freeMask 0 0) p_0_0 q_0_0
private def sl_0_0 : List (Sig × Nat) := [(subcube 0 16, 9), (subcube 0 32, 9), (subcube 4 0, 9), (subcube 0 8, 9), (BitVec.ofNat 64 0x6666666666666666, 9), (subcube 2 0, 8), (subcube 0 4, 8), (BitVec.ofNat 64 0xcc00cc0033003300, 7), (subcube 16 0, 7), (subcube 32 0, 7), (BitVec.ofNat 64 0x606060606060606, 7), (BitVec.ofNat 64 0x3030303003030303, 7), (BitVec.ofNat 64 0x55005500aa00aa00, 7), (BitVec.ofNat 64 0x6600660066006600, 7), (BitVec.ofNat 64 0x1212484812124848, 6), (BitVec.ofNat 64 0xf000f0f000f000, 6), (BitVec.ofNat 64 0x666600006666, 6), (BitVec.ofNat 64 0x3030c0c03030c0c0, 6), (subcube 4 32, 6), (BitVec.ofNat 64 0x55aa000055aa0000, 6), (subcube 16 8, 6), (subcube 4 16, 6), (BitVec.ofNat 64 0x6666666600000000, 6), (subcube 0 1, 6), (subcube 4 8, 6), (subcube 1 0, 6), (subcube 0 2, 6), (subcube 8 0, 6), (subcube 6 0, 5), (subcube 0 48, 5), (subcube 0 40, 5), (subcube 32 8, 5), (subcube 0 36, 5), (subcube 8 4, 5), (subcube 2 4, 5), (subcube 2 32, 5), (subcube 34 0, 5), (subcube 1 32, 5), (subcube 1 8, 5), (subcube 8 16, 5), (subcube 4 1, 5), (subcube 2 8, 5), (subcube 0 20, 5), (subcube 0 10, 5), (subcube 2 1, 5), (subcube 0 18, 5), (subcube 1 16, 5), (subcube 1 2, 5), (subcube 6 1, 4), (subcube 1 48, 4), (subcube 1 10, 4), (subcube 16 32, 4), (subcube 32 16, 4), (subcube 34 8, 4), (subcube 1 40, 4), (subcube 8 32, 4), (subcube 2 36, 4), (subcube 2 16, 4), (subcube 32 4, 4), (subcube 1 18, 4), (subcube 16 4, 4), (subcube 8 20, 4)]
private theorem sl_0_0_ok : ∀ s ∈ sl_0_0, Slice (freeVars 0 0) (subGoal 0 0) s.1 s.2 := by
  intro s hs
  simp only [sl_0_0, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact slice_correct (ms := fixRows 0 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_0_16
  · exact slice_correct (ms := fixRows 0 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_0_32
  · exact slice_correct (ms := fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_4_0
  · exact slice_correct (ms := fixRows 0 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_0_8
  · exact signedSliceOf (f := decodeRows 0xf7ef7ee7ae7ad76d76c72c72b6eb6ea6aa6a96696686286275e75e65a65a55655645245234e34e24a24a146146042042) (by decide +kernel) (proper_of _ (by decide +kernel)) D1.lower_2_0
  · exact slice_correct (ms := fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_2_0
  · exact slice_correct (ms := fixRows 0 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_0_4
  · exact signedSliceOf (f := decodeRows 0xffe75cefa658ffe75cefa658bee34caea248bee34caea248ffe75cefa658ffe75cefa658bee34caea248bee34caea248) (by decide +kernel) (proper_of _ (by decide +kernel)) D3.lower_40_0
  · exact slice_correct (ms := fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_16_0
  · exact slice_correct (ms := fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_32_0
  · exact signedSliceOf (f := decodeRows 0x812894916990812894916998a1aa9cb1eb98a1aa9cb1eb90812894916990812894916998a1aa9cb1eb98a1aa9cb1eb9) (by decide +kernel) (proper_of _ (by decide +kernel)) D3.lower_40_0
  · exact signedSliceOf (f := decodeRows 0x1925209b2d001925209b2d411d35619f3d411d35619f3d001925209b2d001925209b2d411d35619f3d411d35619f3d) (by decide +kernel) (proper_of _ (by decide +kernel)) D3.lower_40_0
  · exact signedSliceOf (f := decodeRows 0x7fe77c6fa6787fe77c6fa6783ee36c2ea2683ee36c2ea2687fe77c6fa6787fe77c6fa6783ee36c2ea2683ee36c2ea268) (by decide +kernel) (proper_of _ (by decide +kernel)) D3.lower_40_0
  · exact signedSliceOf (f := decodeRows 0xf7ee7ab6ea6af7ee7ab6ea6a75e65a34e24a75e65a34e24af7ee7ab6ea6af7ee7ab6ea6a75e65a34e24a75e65a34e24a) (by decide +kernel) (proper_of _ (by decide +kernel)) D3.lower_40_0
  · exact signedSliceOf (f := decodeRows 0x50650644344370e70e64b64b50650644344370e70e64b64bd26d26c63c63f2ef2ee6be6bd26d26c63c63f2ef2ee6be6b) (by decide +kernel) (proper_of _ (by decide +kernel)) D2.lower_18_0
  · exact signedSliceOf (f := decodeRows 0x90c90c94d94d98e98e9cf9cf90c90c94d94d98e98e9cf9cfd1cd1cd5dd5dd9ed9eddfddfd1cd1cd5dd5dd9ed9eddfddf) (by decide +kernel) (proper_of _ (by decide +kernel)) D2.lower_18_0
  · exact signedSliceOf (f := decodeRows 0xb6eb6ea6aa6a966966862862b6eb6ea6aa6a96696686286234e34e24a24a14614604204234e34e24a24a146146042042) (by decide +kernel) (proper_of _ (by decide +kernel)) D2.lower_18_0
  · exact signedSliceOf (f := decodeRows 0x50650654754770e70e74f74f50650654754770e70e74f74fd26d26d67d67f2ef2ef6ff6fd26d26d67d67f2ef2ef6ff6f) (by decide +kernel) (proper_of _ (by decide +kernel)) D2.lower_18_0
  · exact slice_correct (ms := fixRows 4 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_4_32
  · exact signedSliceOf (f := decodeRows 0x611611693693715715797797611611693693715715797797e31e31eb3eb3f35f35fb7fb7e31e31eb3eb3f35f35fb7fb7) (by decide +kernel) (proper_of _ (by decide +kernel)) D2.lower_18_0
  · exact slice_correct (ms := fixRows 16 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_16_8
  · exact slice_correct (ms := fixRows 4 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_4_16
  · exact signedSliceOf (f := decodeRows 0x8a18a1aa9aa99a59a5badbad8a18a1aa9aa99a59a5badbadcb1cb1eb9eb9db5db5fbdfbdcb1cb1eb9eb9db5db5fbdfbd) (by decide +kernel) (proper_of _ (by decide +kernel)) D2.lower_18_0
  · exact slice_correct (ms := fixRows 0 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_0_1
  · exact slice_correct (ms := fixRows 4 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_4_8
  · exact slice_correct (ms := fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_1_0
  · exact slice_correct (ms := fixRows 0 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_0_2
  · exact slice_correct (ms := fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_8_0
  · exact slice_correct (ms := fixRows 6 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_6_0
  · exact slice_correct (ms := fixRows 0 48) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_0_48
  · exact slice_correct (ms := fixRows 0 40) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_0_40
  · exact slice_correct (ms := fixRows 32 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_32_8
  · exact slice_correct (ms := fixRows 0 36) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_0_36
  · exact slice_correct (ms := fixRows 8 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_8_4
  · exact slice_correct (ms := fixRows 2 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_2_4
  · exact slice_correct (ms := fixRows 2 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_2_32
  · exact slice_correct (ms := fixRows 34 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_34_0
  · exact slice_correct (ms := fixRows 1 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_1_32
  · exact slice_correct (ms := fixRows 1 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_1_8
  · exact slice_correct (ms := fixRows 8 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_8_16
  · exact slice_correct (ms := fixRows 4 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_4_1
  · exact slice_correct (ms := fixRows 2 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_2_8
  · exact slice_correct (ms := fixRows 0 20) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_0_20
  · exact slice_correct (ms := fixRows 0 10) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_0_10
  · exact slice_correct (ms := fixRows 2 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_2_1
  · exact slice_correct (ms := fixRows 0 18) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_0_18
  · exact slice_correct (ms := fixRows 1 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_1_16
  · exact slice_correct (ms := fixRows 1 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_1_2
  · exact slice_correct (ms := fixRows 6 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_6_1
  · exact slice_correct (ms := fixRows 1 48) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_1_48
  · exact slice_correct (ms := fixRows 1 10) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_1_10
  · exact slice_correct (ms := fixRows 16 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_16_32
  · exact slice_correct (ms := fixRows 32 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_32_16
  · exact slice_correct (ms := fixRows 34 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_34_8
  · exact slice_correct (ms := fixRows 1 40) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_1_40
  · exact slice_correct (ms := fixRows 8 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_8_32
  · exact slice_correct (ms := fixRows 2 36) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_2_36
  · exact slice_correct (ms := fixRows 2 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_2_16
  · exact slice_correct (ms := fixRows 32 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_32_4
  · exact slice_correct (ms := fixRows 1 18) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_1_18
  · exact slice_correct (ms := fixRows 16 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_16_4
  · exact slice_correct (ms := fixRows 8 20) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_8_20
private def fmt_0_0_5 : ChartFormat := ⟨6, 6, 0, 0, 6⟩
private abbrev Batch_0_0_5 := CheckedBatch (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] 5 fmt_0_0_5 [] fmt_0_0_5
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_5_0 : List Batch_0_0_5 := [
  ⟨⟨2,0x54392b60a454680f5c02522ca41a8c925943d7005,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x54b3a1608649083e4d1c150ec81aa0095963d702b,0x1⟩,by decide +kernel⟩,
  ⟨⟨1,0x150c86da6a08420f93470,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_0_0_5 : List Batch_0_0_5 := ch_0_0_5_0
private noncomputable def lv_0_0_5 : List NodeSpec := flattenBatches fmt_0_0_5 (ch_0_0_5.map Subtype.val)
private theorem ok_0_0_5 : LevelOK rd_0_0 (subGoal 0 0) 5 lv_0_0_5 :=
  @checkedBatches (freeVars 0 0) rd_0_0 _ _ _ sl_0_0 [[]] 5 fmt_0_0_5 [] fmt_0_0_5 pp_0_0 (raw_faithful (freeMask 0 0) p_0_0 q_0_0) sl_0_0_ok (by decide +kernel) (emptyLevelOK rd_0_0 (subGoal 0 0) 4) ch_0_0_5

private def fmt_0_0_6 : ChartFormat := ⟨6, 5, 0, 3, 6⟩
private abbrev Batch_0_0_6 := CheckedBatch (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] 6 fmt_0_0_5 (ch_0_0_5.map Subtype.val) fmt_0_0_6
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_6_0 : List Batch_0_0_6 := [
  ⟨⟨2,0xd1012a541083b4a687604820543210a789cd0de0904,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x10c842a5d9678dc02412231498210a7658d0ec0904,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x58588c9260a841d94343b02414031548210a769cd0ec0905,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x10ca0429de6827503015851432a1097651e3700905,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x14228650214ef3413a8200ba1320a4a28107793209d40c05,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x124343784d02241d1483c92ca1eb80284328a10779a09d43205,0xa⟩,by decide +kernel⟩,
  ⟨⟨2,0x34201648e51420f26043a8e00a04082a432810a797c21d47005,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x40e05923d14083c9904ea38028432810a797e09d47005,0xa⟩,by decide +kernel⟩,
  ⟨⟨2,0x2cb95083c2c681966048483290a775854dd7007,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x327030c56a914420f2e8a8e1981201821a54a721079841470cc09,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x2a190d43cb42a0fb804854362a17894541f7009,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1520d8a9c25150f5c024c3154392a07151a03d7009,0x12⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_6_1 : List Batch_0_0_6 := [
  ⟨⟨2,0x14aa1950c384a2a6fb8048543210a789c54df7009,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x2a1b10d3cbe109a3804854321a8709c54df7009,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x150c85a9e5f084d1c02c03003004000045543a21076921d347009,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x2a539083cbad09a380605483a207095963d702b,0x32⟩,by decide +kernel⟩,
  ⟨⟨2,0x23948853bacd09a38060572910a7949a134700c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x29b90853b4d00ab38190572910a7939a1347010,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xa946410f2c8a87c32e084022a548732a709454391970,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1114a39948d3b2c109a0cb80432908a7658543e1970,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xc10aa194d0bbcc109a0db80547321a797a02d61970,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xe8850ca469dd96084d06dc0209432910a7659e1341b70,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x12310010018a864214f2f044b272e000800a54321a0797201563970,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x2a399503cc42b2c9cb80547320a798854593970,0x1⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_6_2 : List Batch_0_0_6 := [
  ⟨⟨2,0x620014a864340f2e403ac72e0c40882473290a765821343970,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x2e558aa441e1083074d1c003154321a0797201d65970,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x15208429e4e083e4d1c00815483a10792420f93470,0x22⟩,by decide +kernel⟩,
  ⟨⟨2,0x2a41885394c10fc9a38054a3219708420f93470,0x126⟩,by decide +kernel⟩,
  ⟨⟨1,0x543219a708c22f93470,0x62⟩,by decide +kernel⟩]
private noncomputable def ch_0_0_6 : List Batch_0_0_6 := (ch_0_0_6_0 ++ (ch_0_0_6_1 ++ ch_0_0_6_2))
private noncomputable def lv_0_0_6 : List NodeSpec := flattenBatches fmt_0_0_6 (ch_0_0_6.map Subtype.val)
private theorem ok_0_0_6 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6 :=
  @checkedBatches (freeVars 0 0) rd_0_0 _ _ _ sl_0_0 [[]] 6 fmt_0_0_5 (ch_0_0_5.map Subtype.val) fmt_0_0_6 pp_0_0 (raw_faithful (freeMask 0 0) p_0_0 q_0_0) sl_0_0_ok (by decide +kernel) ok_0_0_5 ch_0_0_6

private def fmt_0_0_7 : ChartFormat := ⟨6, 4, 0, 4, 6⟩
private abbrev Batch_0_0_7 := CheckedBatch (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] 7 fmt_0_0_6 (ch_0_0_6.map Subtype.val) fmt_0_0_7
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_7_0 : List Batch_0_0_7 := [
  ⟨⟨2,0x1b00e025080008808754392108834378241015050950ca441e20e52c204,0xa⟩,by decide +kernel⟩,
  ⟨⟨2,0x1b05e0620f02e0580620469549821068343b0241246251850d914e08425d92ec0904,0x56⟩,by decide +kernel⟩,
  ⟨⟨2,0x222431234201ac06549372108685c02412170324890189d0985b0e10e08425d96ec0904,0xe4⟩,by decide +kernel⟩,
  ⟨⟨2,0x661790e4290248919d0e1c84261967009042210601283c0b8104dd50c841a61e3700904,0x2a4⟩,by decide +kernel⟩,
  ⟨⟨2,0x340094223543109668ba4401019c16c0085152441da0910ce04,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x9525524328109765bb94812466174009510e0425996e91004,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x18520c42354382109868fb02415470c49520c825c56dd7004,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xde141705a4890189b0d0a943829107653b024142981985e058062046c0a1526098420d0ec0905,0x166⟩,by decide +kernel⟩,
  ⟨⟨2,0x1781b02624365549826108353b0241452624950e0a442194ec0905,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x2230590c0290010019d50dc84261a370090570455a20d50e4a0421d4d00905,0x62⟩,by decide +kernel⟩,
  ⟨⟨2,0x17c16854124390a400be4891a90e1ca44219470090522283c0b81a0021c29d50c984261e3700905,0x1a6⟩,by decide +kernel⟩,
  ⟨⟨2,0x51b05509c00d016643728109884b50241546c15c35081f05990dca042620ed40905,0x1⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_7_1 : List Batch_0_0_7 := [
  ⟨⟨2,0x12605f0570148a1190ca041e6212d40e0502546a1143305c2905d0e4a041e209d40c05,0x446⟩,by decide +kernel⟩,
  ⟨⟨2,0x70158518d0ca0425e212d44e05321c1800c003155209c42601670cc05,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x91b400c8d0e2441994e91005b0018018d50c841e61a3944e05,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x140521c251910e4a041e209d4100503d8391984d01c1625d50e2441d94e91005,0x142⟩,by decide +kernel⟩,
  ⟨⟨2,0x5014870946443928107882750c8170570c1f05910ca041e620ed41205,0x1c2⟩,by decide +kernel⟩,
  ⟨⟨2,0x1403c41025150ca2442194ee520561254954d0ca2441d94ee5205,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x20415018d50c841e61a374520570d55518d0ca0425e20ed45205,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1a61b43041c16259520ca41d943d7005627c2d01070bd520ca419943d7005,0x242⟩,by decide +kernel⟩,
  ⟨⟨2,0x10615c1025150c84262016df7005821c1624d520c98260963d7005,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x170250550cc15002f05a8452290dca6042021d4700570412024d50c84262096df7005,0x6c6⟩,by decide +kernel⟩,
  ⟨⟨2,0x6405d0f4001802126c185432910786bd9c014160270550d40521c251a10de4a042209d47005,0xe904⟩,by decide +kernel⟩,
  ⟨⟨2,0x304b089905cc841cc031835943927107833a7501417320c6303c2a15c305a10c9e441e0c1dd405,0x4c304⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_7_2 : List Batch_0_0_7 := [
  ⟨⟨2,0xc10550ca419e20e5207060689905cc6214c2c120935250c9e441e0ef2d405,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x4005254321069878dc0241988119856000d05d95260841a0d0ec0906,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xbc852549832068274f5c0180670895260c84209ddd7006,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1182c098d5260841a0d0ecc90702403000d524dc84221dd67006,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1881198010c2c5549821068343b0241c08d08950c841a61e370c907,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xa120950c841a61e3700907042c002742f0546251d50ca441e1ed00907,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x2502408354382910865bc9381c1222408b0400d088751a150ca441e1ed40907,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x61181254382096815bc9381c150e0a41a054f24e07,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1403c09354328910865bb9481e11f0bc106f400b19508425a0cdd1207,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x61181254328096815bb9481c150ca241a054ee5207,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x2b616038000670995260c84209ddd700751c010b0d520c825c56dd7007,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x219154837209815b75c01e197049520dca42054dd7007,0x182⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_7_3 : List Batch_0_0_7 := [
  ⟨⟨2,0x6985019c245493210882777dc01e03800097051520c84261d6dd7007,0x182⟩,by decide +kernel⟩,
  ⟨⟨2,0xc450dca01a61d634700704c08b08d50dca4421a25d7007,0x182⟩,by decide +kernel⟩,
  ⟨⟨2,0x2d4641691d10ca41d9a134d4070582d11d8586550ca619854e2d407,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x32382059c1325550ca41de162e3a090c4490c0d0c8225856dd1607,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x8821068c9304c86543829078151c0e82410b001603dc1325950ca41de16323a09,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x5214510f827054965482190775b303825010684b325150c841e6216703a09,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x3408d0c00e0ac165432109786bd8b8258402408d0c0100021e0a150c8425e1ae22e09,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x704c92543972108850f730240d02606a08c5705950e084261d63dcc09,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x3c434480945437219088584b30243605d1b0c9165c8421cd010cc09,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x991b45cc53021a50cc8859721087340cb30278202809006c0d0d950e4841e1d32cc09,0x282⟩,by decide +kernel⟩,
  ⟨⟨2,0x182704c0322065548721098051c3302433324950dca44221632cc09,0x1286⟩,by decide +kernel⟩,
  ⟨⟨2,0x6cc9320c0818c56548721908151c33024c8704c0032063259521c842601670cc09,0x482⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_7_4 : List Batch_0_0_7 := [
  ⟨⟨2,0x173140f704c9554721097859c3302506608470e11521c842605670cc09,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x306d0c08002c1e082c754392107874d330241d300328361b3219661c841d1470cc09,0x482⟩,by decide +kernel⟩,
  ⟨⟨2,0x808506809705550e4a042194e5100920b06314d50e5c84221d34cc09,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x2c101410e084c619950c8425e1af4100909010c02c111f82e19d50d8a41e05f41009,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x975168400209e09c328614e48601cd0fa32096198402740f0782099d50c8425e1ae23209,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xb0410e0847619550c8641e1af4320904305a0c3342554e18a4421d6703209,0x282⟩,by decide +kernel⟩,
  ⟨⟨2,0xd0f4061b824543921878687dc0240f0380900c01d03820ce150c8425e1af63209,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xd0c090140104186e09d50e4841e1a1f700906582618d50d886620541f7009,0x1586⟩,by decide +kernel⟩,
  ⟨⟨2,0x6989605864548362908150f5c0240961bc1d0f400bd950e4841da03d7009,0x1786⟩,by decide +kernel⟩,
  ⟨⟨2,0x21609c1025150c84262016df700904a08609c1121550c84262014df7009,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1c108c1a354321098815b7dc0241a0258200421015950c86422054df7009,0xe604⟩,by decide +kernel⟩,
  ⟨⟨2,0x108c0c43b070004806754936210887451c0274300540885164c8421d14df7009,0x382⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_7_5 : List Batch_0_0_7 := [
  ⟨⟨2,0x2c06702c19150dd886602334700914c491170290706215d50dd8a46021347009,0x6a20c⟩,by decide +kernel⟩,
  ⟨⟨2,0x1914c020191524d884221d3470090b01b00f0200022021d50dc842621a347009,0x99a04⟩,by decide +kernel⟩,
  ⟨⟨2,0x343d001a01782b044975439210786bd9c0243a08c00021150dc864221a367009,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x5d0782b005455432190786bc8d02410d0d2107514dc8425da3947009,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xd040504186e08266543921078687e502743d041a0200500186e0a150e4841e1a1f7409,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x46a07404c34593827108451c3142c4b0290181d150c9c42621670c50b,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x124459042f0a1550dca45a02134700b0bc4909428089550dca4421a134700b,0xe82⟩,by decide +kernel⟩,
  ⟨⟨2,0xb0c058ac210c55524c841de1701829064060a0d524c841a21d34700b,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x6f82d002c454921068307740a42f05d01025150c841e6216701a29,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1c0189524d884221d167029d0f400bdc16255520e481d943d7029,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x2809020010018665473921086807650a41b05c09c1484904810bc0804e950de4842021d47029,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xc26c0b0c2fc295524c9c1c6170c12b0200002401e0b05b0dd50c8425de370c12b,0x1⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_7_6 : List Batch_0_0_7 := [
  ⟨⟨2,0x128e0800825c3a14a17539218073437440aca88910dc14c046d43322165c8421cd010ce2b,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xa0809704d50c860261d6dd102b02782704d50c86026216dd102b,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x9a1b8235439210787875840ae4342494e24841e19670102b,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x20024950e484221961f702b020090074061743e09d50c8425e191f702b,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x340d0dc16251520e481d963d702bd0189d0c2fe095520e481da23d702b,0xf82⟩,by decide +kernel⟩,
  ⟨⟨2,0x2b41e0ac0151550c8641da1f2162b06e052040804d550de4842021d6702b,0xf82⟩,by decide +kernel⟩,
  ⟨⟨2,0xd07400c8d50c8425e191f942b024080034161743e09d50c8425e191f742b,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x46814446c032155208425de370c50c71bc2706c083545321d5209c25c6370c50c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x4660346a217060d321d6609c41d1470c50c46945b00c870555209c42621670c50c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x13422543210698878d3243006d08950dca4421a134c90c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x187719c2e0f403142575432890715397403187719c2e0f40095950ca241e14e5d00c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1212f258291067759c0c83287e0f4001802466c1316150ca441de134d00c,0x1⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_7_7 : List Batch_0_0_7 := [
  ⟨⟨2,0x2006054d50ca441e1a134520c037401240600ac181dd50ca441da1f6320c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x48c00403549721068858fdc030030b021d00c5921951c8641e193f700c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xc4c03c00404549721068874d1c0303b0d113c0cc50c5951ca441da134700c,0x30404⟩,by decide +kernel⟩,
  ⟨⟨2,0xd487c2120315597210668651c0330012091c8601a61d634700c,0x502⟩,by decide +kernel⟩,
  ⟨⟨2,0x19c2254328109882f74d0302c01983709150e4a042209dd340c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x8700950ca0426212dd340c1240811425701550ca2442210dd340c,0x302⟩,by decide +kernel⟩,
  ⟨⟨2,0x150209524c841e1a114520ed00060088c0b15524c841de114d00e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x651791b407058965438910765ba440bb400bc217051520ca41d96e5d02e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x37024950ca4602196e1522e2378301802d0089b05d50ca441de1d6102e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x2480ec9521c86421a21d702e313c20a740921551c8641da21d702e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x35254972106887459c0b8af14e033051520841a61d61d702e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x31009c1801b0094654321097878cb05380d487c20a448075965c8419a194702e,0x1⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_7_8 : List Batch_0_0_7 := [
  ⟨⟨2,0xe091902000e0ec1c18c5854329107784d3093833024950ca45c221632c14e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x31050dc8642205414d24e04408414c4069550dca44220514d24e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x18c4208c509c086543729108084d349388c31490dc8422605616d24e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x60062543291068784d041382081c85069150e4a042196e5104e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x600625943210687845049382081c950e4a042196e5124e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x6809309c1454392710885baf144020024950e48602196e1324e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x30801068d0c9e0426096f4c51046a07516c370554e09c42609670c510,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xc71141241d150ca5c4220e56c51002006114d50c9e44221e56c510,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x5203d43821458678070549954389107753271441c1516140bd150e1e41c60c9c510,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x20116427041a554392710885327144020516424b5150e25c42214c9c510,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x126c10684545432719088655b144145b0a1970614525950e4421dd4cac510,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x94c92543718098658f32440c430c42086c1e00c525e150de441c2134c910,0x1⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_7_9 : List Batch_0_0_7 := [
  ⟨⟨2,0x3800bcc185110de4421dd4d6c91014808d09c1325550dc41a62163cc910,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x342310423543710698878d3244042e02c1464c5451950de441da134c910,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x380313423543210698878d3244006d08950dca4421a134c910,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x2809c2c3532109668875c04380d0919b0514315950e441dda134ca10,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x2c130c5b070016d43c2215c841a5e0e3470100b126316c1d0ca5421d4dca441da1347010,0x702⟩,by decide +kernel⟩,
  ⟨⟨2,0x19c2254328109882f74d0408801980709150e4a042209dd3410,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x6dc3254328109883b74d0401b70c8851d150ca244220cdd3410,0x702⟩,by decide +kernel⟩,
  ⟨⟨2,0x41c45048c745432971088395b14480600b800c9150c8425da21d3410,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x9c14950c9c4261e37419300502d094d4ca4419a1e23212,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xc908c235439217088532704c81f048950ca45c220e56c132,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x20c1642309150e4841e214c9c232820c6e002f329550c85e5c22c9c232,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x300610409509550ca44221961ec9320be08b07800b1550ca45dc21d6c232,0x1⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_7_10 : List Batch_0_0_7 := [
  ⟨⟨2,0x5b3130310d14dc8641a20156703229457b070011c5bc21d5c84259e0e167032,0x902⟩,by decide +kernel⟩,
  ⟨⟨2,0x96100101802e011475432190768875d0c844d081b15c03d0646e02150c8425da2e15632,0x902⟩,by decide +kernel⟩,
  ⟨⟨2,0x4198206cc34543218098053b3054819450950dc86421a21d7432,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x6c0346780b0782315d50ca441de134c252419827042301d550c86026056ecc152,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x31050c9c642205414ce5231015c50d50c9e44220514ce52,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x130c524327108981585b394815050950c9e44220516ce52,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x5414254327109808cd339481b018c431415051950c9e44202134ce52,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x60088c0b1550c8425e1e141970c0ec1e00218b1551ce441e09141970,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x6c1a030090230350700914c5a549732108850e465c01b86549c0d41c02100421521cca42054391970,0xb02⟩,by decide +kernel⟩,
  ⟨⟨2,0xb0b83e00214547321970816465c01c018c50691520c842605e591970,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x219704c53543629088150f865c00c02406c0cc25070090a1525cc842214591970,0x4d06⟩,by decide +kernel⟩,
  ⟨⟨2,0x1bc000823111cc8422619616197008cc51041a81d550c842261963e1970,0xf02⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_7_11 : List Batch_0_0_7 := [
  ⟨⟨2,0x31304c4990700041083161525cc8422193419700941bb04c5021551cd8a46021341970,0x52c04⟩,by decide +kernel⟩,
  ⟨⟨2,0x2bc4e45c0108098107547932108864d865c01b91703c003204191cc86026196341970,0x4f06⟩,by decide +kernel⟩,
  ⟨⟨2,0x31ac1e003245473219780b5865c0230c8950d8864221e361970,0x1302⟩,by decide +kernel⟩,
  ⟨⟨2,0x1c104a07354328109825b946dc013e0f8030511e4c84221d4d61970,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xc18c6e0f800bc25654329177084d06dc00600ac1e0f800bd950ca441de1341b70,0xb0586⟩,by decide +kernel⟩,
  ⟨⟨2,0x38304ec2354321977089646dc01021d410251524c841e2163b1b70,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x200249524c841e214591b7004c550c8425e022591b70,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x2f06c17b04c5021950d8a45e021341b700bc1b02007b0413315d50d8a4421e1341b70,0x5706⟩,by decide +kernel⟩,
  ⟨⟨2,0x6e45020314432180978658d06dc0130409524c841e219341b70,0x5706⟩,by decide +kernel⟩,
  ⟨⟨2,0x324c1318d51cca4220545e397031ac104cd50c865de01d61b70,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xe0f8031ac10bd551cc825e1e343970116c131b83e00250bdd51cca41c21343970,0x882⟩,by decide +kernel⟩,
  ⟨⟨2,0x318551cca44221e56397011704310d51cc8642201563970,0x1b02⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_7_12 : List Batch_0_0_7 := [
  ⟨⟨2,0x45908c4354732109808964e5c02f914420191520c842601e593970,0x1d02⟩,by decide +kernel⟩,
  ⟨⟨2,0xc132541354873209815964e5c01b020c61151521cca42054593970,0x5f06⟩,by decide +kernel⟩,
  ⟨⟨2,0x4045254793210886458e5c00c51441025150c842261961e3970,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x33b18310bc1b020c9747328097658d0e5c02f06f10016c1441951cd8a42021343970,0x120b06⟩,by decide +kernel⟩,
  ⟨⟨2,0x6c0902013b055524d8842021f4397011641310d51cc8642201d63970,0x2502⟩,by decide +kernel⟩,
  ⟨⟨2,0x225084181d150c842261963e59700300610409509550c842261961e5970,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x41808d08d50d8842621e1459701248390406d09551e4c842219145970,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x6e03423547932108864d165c006d08951e4c842219165970,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x2201f423543621908878d965c03a00ac1315150d8842621e345970,0x5f06⟩,by decide +kernel⟩,
  ⟨⟨2,0x28230090184202241306151cc8426202d6597010a41018d51cc8642201d65970,0x2702⟩,by decide +kernel⟩,
  ⟨⟨2,0x6c0902045112c104dd524d8842021f459700700921cc1905551cca442205d65970,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x6e0dc2354832109828be451c0490194170980e0d95260c8420a1f91470,0x1⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_7_13 : List Batch_0_0_7 := [
  ⟨⟨2,0x717800c8d20d88642054f91470e01c50c8d20c8641c54f91470,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x21c524d8841e2193616700644908cd24c841de19361670,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x200301802d0645e01d50c8425e1b1d347004c100258660825915d50ca24422181d3470,0x2c86⟩,by decide +kernel⟩,
  ⟨⟨2,0x240826645454328109886c74d1c00304c950d8842621b1d3470,0x2c2⟩,by decide +kernel⟩,
  ⟨⟨2,0x10e0c0091417553628910884074d1c003e024505d1518a244220c1d3470,0x68346⟩,by decide +kernel⟩,
  ⟨⟨2,0x4c10125c2220456548321098083e4d1c01b4040891510d8a04261961d3470,0x19184441c⟩,by decide +kernel⟩,
  ⟨⟨2,0x4c10254832109808be4d1c013041c25058041d95260c842021f93470,0x630340c⟩,by decide +kernel⟩,
  ⟨⟨2,0x19c22549832108287e4d1c0130409520c8426023f93470,0x3302⟩,by decide +kernel⟩,
  ⟨⟨2,0x2013254362109808be4d1c0067089520c84260a2f93470,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x5803000d524d8842219e236708b408d040600a2b167458325524c841e19e23670,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x5e03411bc215549321078678959c00001410d0783919950c8425e1be15670,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x2808c323432109668874d052090bf813020c32194de4421dd0d2c914,0x1⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_7_14 : List Batch_0_0_7 := [
  ⟨⟨2,0x1b020c3701150ca60421d0ec1934c1410700d50c9c426212ec1934,0x2902⟩,by decide +kernel⟩,
  ⟨⟨2,0x21ad1419f081be04107542109683870e6501006f0570d150c9c42620ef01934,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_0_0_7 : List Batch_0_0_7 := (((ch_0_0_7_0 ++ (ch_0_0_7_1 ++ ch_0_0_7_2)) ++ ((ch_0_0_7_3 ++ ch_0_0_7_4) ++ (ch_0_0_7_5 ++ ch_0_0_7_6))) ++ (((ch_0_0_7_7 ++ ch_0_0_7_8) ++ (ch_0_0_7_9 ++ ch_0_0_7_10)) ++ ((ch_0_0_7_11 ++ ch_0_0_7_12) ++ (ch_0_0_7_13 ++ ch_0_0_7_14))))
private noncomputable def lv_0_0_7 : List NodeSpec := flattenBatches fmt_0_0_7 (ch_0_0_7.map Subtype.val)
private theorem ok_0_0_7 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7 :=
  @checkedBatches (freeVars 0 0) rd_0_0 _ _ _ sl_0_0 [[]] 7 fmt_0_0_6 (ch_0_0_6.map Subtype.val) fmt_0_0_7 pp_0_0 (raw_faithful (freeMask 0 0) p_0_0 q_0_0) sl_0_0_ok (by decide +kernel) ok_0_0_6 ch_0_0_7

private def fmt_0_0_8 : ChartFormat := ⟨6, 3, 0, 5, 6⟩
private abbrev Batch_0_0_8 := CheckedBatch (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] 8 fmt_0_0_7 (ch_0_0_7.map Subtype.val) fmt_0_0_8
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_8_0 : List Batch_0_0_8 := [
  ⟨⟨2,0x9e0a21131150ca041fbb081216070370b82198283426954321087ecc204,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x10864170981b0e02c1164158c2d62a19083c4296102060200b8401e0b0160c0180c21331856e5432107884ec204,0xa⟩,by decide +kernel⟩,
  ⟨⟨2,0x801168ac4a55432087736c2041609027066341604c280b0580071304056f54382107870c204,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x481061c14622132a1b8843876482041800d82894426543710870cc904,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x2106828c48a86e210e25920821080298705833004a85437108710c904,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x802980c1834144c75437108714c9041609020c0828c44275438710770c904,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1604187051883cca870e20ee99208c1830906245437108716c904,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1b0470e8417188e0ea864210fbc120810834146245483710794c904,0x12⟩,by decide +kernel⟩,
  ⟨⟨2,0x252058124600801b4191b0a365aa1c108347604820401742428c442654721087ce0904,0x3c4⟩,by decide +kernel⟩,
  ⟨⟨2,0xb44813834260519288543721088d2090405d09102e428da8c753721087d20904,0x32⟩,by decide +kernel⟩,
  ⟨⟨2,0x422f4244f0f802542d19286e4210fac1208174420c87814010032482350842c5438721069700904,0x7a5c⟩,by decide +kernel⟩,
  ⟨⟨2,0x2e132510b4212994c8421df482c1021404289442554210877ce0b04,0x1⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_8_1 : List Batch_0_0_8 := [
  ⟨⟨2,0x2485b1b85c10cc141a134aa1083c3f06702042802642d084a643210877d60b04,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x16c16309a0ac21809d0a8420f0fd79c08240ca5c87c113c1442854210787e3ce04,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x319842582b004c65421087710ce041204c20c0828c442754210787f0ce04,0xc2⟩,by decide +kernel⟩,
  ⟨⟨2,0x58c05dc182b004275421078752ce041242d8c970cf0b830d13c1420b5421078712ce04,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x16c2173060a2632a10843b8a67020b0330513b0442654210787f4ce04,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x9e1bc2084146265482107794ce04608c46035421078716ce04,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x2d82c613415843013a150841e1d3b3810490b6370b821982834269542108770cce04,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1204c20c0828c44275482107770ce04633098224084344e754321078812ce04,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1222e8dc2e0a1432144299083c3e906020b0330513b044265482107774ce04,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x18c4563022a194083fc870251a8425428305c643210787d60c04,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x9513c0130c0a864210efac1c082445d1b85c10a2144c853210877d20e04,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x42863044d0b80851b5192864210efac9c080b1809a85c1428528c853210877d24e04,0x1⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_8_2 : List Batch_0_0_8 := [
  ⟨⟨2,0x5b0585050a0b8ca70420efd3a4082485b1b85c18286428853210877e2d204,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xb610b9830513194c8421dc5348118cc20a0905c553210877f6d204,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x14120d86a70420eee9a408c18a0946045321078716d204,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x21046070646c2d004a854381067e910040460f022fa00944c754328067e51004,0x3304⟩,by decide +kernel⟩,
  ⟨⟨2,0x62301aa194083fc890251a842542d004c643210787d61004,0x1c2⟩,by decide +kernel⟩,
  ⟨⟨2,0x3606c2604aa541c1d50ca041a3b948104a89e18b860543210877d61204,0x38e⟩,by decide +kernel⟩,
  ⟨⟨2,0x22c120803503843142d0c20a54832107dd7004a022461c3428c68c743210877d65204,0xd284⟩,by decide +kernel⟩,
  ⟨⟨2,0x5816a321b84a542d0d821044ad50dc8422359c0105946a070912314283020943721087d67004,0x42⟩,by decide +kernel⟩,
  ⟨⟨2,0xc661024190517190c8421df8b58128d428811c625543720688367004,0x2c2⟩,by decide +kernel⟩,
  ⟨⟨2,0x3198505618c4a864210efddac083682b0862443821077e9d604,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x100fe17020ac3129d50c8421fbb58118cc282b006c543210877f2d604,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1c624918110c819e1cd858101000a081c60554328107f91604,0x1⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_8_3 : List Batch_0_0_8 := [
  ⟨⟨2,0x2071c2e02146c654832107dd74041791c70354328077f93604,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x52260da501a06c2e009248c090480178130e151543826108ec0905a00d462358432107dd9404,0xfd14⟩,by decide +kernel⟩,
  ⟨⟨2,0x1104682a16088321e050040179202f4210bd50e1c98425c024142a8982813834260519289543728108d00905,0xe4f14⟩,by decide +kernel⟩,
  ⟨⟨2,0x120803d1105e1f01094260d1912c543728108d409050b0420a0460d1913c3e050858b43728107d40905,0x364214⟩,by decide +kernel⟩,
  ⟨⟨2,0xbc2f06824151249a10d92a870e4c212e8120a20246008142c23046a8543826108f40905,0x1286⟩,by decide +kernel⟩,
  ⟨⟨2,0xc438321aa194083fd05828bc2e49834120a892450862a5483726109940905,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xf4420d014660a24508543281078d40b051d8a064343281077d40b05,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x482088a3701820a448ad2a86e50211a8520a1603d1983051682856843728107d42905,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x3314069230c46c110b0b43e0307084972a19308447b06028d476254321087fa0c05,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x146432138441a1a24628543281078d40c05a32108289e150c76743281077d40c05,0x982⟩,by decide +kernel⟩,
  ⟨⟨2,0x2bc2f041a270b884ea85020ef981c0a92293046a45432610789560c05,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x803111464370b80c106a2458b543281078d40e050b04113c01403458743281077d40e05,0xa82⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_8_4 : List Batch_0_0_8 := [
  ⟨⟨2,0x108bc4e454281077cc2e0513c10910544d0c6275483261079940e05,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x178b46a343281077d42e050b4501a0c246188d822141687c060e1092f543268108f62e05,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x17c2b03820d190404285482710770cc05633098235084344e754327108812cc05,0xb82⟩,by decide +kernel⟩,
  ⟨⟨2,0x9834176321584108689d2a9064e21129980a10633009908832160143e130458c54327108816cc05,0xb82⟩,by decide +kernel⟩,
  ⟨⟨2,0x2c10a12105089a1f030a32a32d0ca041df51381440190bc5091802050e840b60e1092d543826108f64e05,0xc82⟩,by decide +kernel⟩,
  ⟨⟨2,0x42a04565823461130642a4193083cca270289434170b04111054250f814260d1912e543281078d44e05,0xd82⟩,by decide +kernel⟩,
  ⟨⟨2,0xc091a803222a1c3083f4880282423c2e0d0064654321087fa1005,0x1e86⟩,by decide +kernel⟩,
  ⟨⟨2,0x51a844144f0a80323a194083bea0802e1b054012924646543261088f61005,0x2e86⟩,by decide +kernel⟩,
  ⟨⟨2,0x8b05245244918ca864c20f12ac200b464320a84c1a0224648543281078d41005,0xf82⟩,by decide +kernel⟩,
  ⟨⟨2,0x13a19068220841123142a194083c6a0902a260a04e18a076643281077d41205,0x302⟩,by decide +kernel⟩,
  ⟨⟨2,0x42f85c115d005e654326187e2320584410930544d006c75438261079741205,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x16a32278540158bce865020efa8640a190b0330c4682e0884c10812456c543268108f63205,0x502⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_8_5 : List Batch_0_0_8 := [
  ⟨⟨2,0x760cc6e1306282c3aa19388440b68028968c86a005b841060a2456a543281078d43205,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1b036170254c2154ea8650c211dca40a2e0b84983406122e28854327108856d005,0x22824⟩,by decide +kernel⟩,
  ⟨⟨2,0x5b0a84a00a112871dd192865020efa8a40a200c85e854060e106a8543826108f65205,0x8706⟩,by decide +kernel⟩,
  ⟨⟨2,0x10a81169548d1544c190a8704c20f2e8a40a250d05c2a0f82a13874060d1912c543281078d45205,0x8906⟩,by decide +kernel⟩,
  ⟨⟨2,0x5a090361687c2e08c820954321087df70050461b85c1a1d005e7548326073d7005,0x79c121c⟩,by decide +kernel⟩,
  ⟨⟨2,0x5c2d46c28ee0a89e101c64105a1b94083ea38029220b03609005e8924c2062a5437261089167005,0x15a431a1c⟩,by decide +kernel⟩,
  ⟨⟨2,0x1130882c1207004914892c110ad50dc98422559c0142e16a3218622d82f0a814360a2420d543728108d47005,0x54404⟩,by decide +kernel⟩,
  ⟨⟨2,0x8e064354321087fa14050c85f0c46c110a874060e1048b543261088f67005,0x1d02⟩,by decide +kernel⟩,
  ⟨⟨2,0x47c31180ac3c11083e1718a950c984223b85814123b2350464554386107e91405,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x31984091681c5e6432871073dd4050801387c004a14507432871071dd405,0x19906⟩,by decide +kernel⟩,
  ⟨⟨2,0x170831b0bc2e001c64164a1938843f76a0286820c2208a20809e00d58ca43827107e9d405,0x611be27818⟩,by decide +kernel⟩,
  ⟨⟨2,0x170081c1fc20b09cea864210fdda80a176361787c21d82420843271087f2d405,0xb04a20c⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_8_6 : List Batch_0_0_8 := [
  ⟨⟨2,0xe2da1d045e5548326073d74050ba509848c0100361f05e10a4b543286108ee5605,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1c5f41080acab0864c0e7b280a08030045785e17006c854321087df7405,0xd02⟩,by decide +kernel⟩,
  ⟨⟨2,0x270d82c21506265432610887f9405a00b70bc3e104062754321087df9405,0xd82⟩,by decide +kernel⟩,
  ⟨⟨2,0x8230d8d05189550c819e21481c18200b82c1184c0e0b186495432067884e0706,0x2502⟩,by decide +kernel⟩,
  ⟨⟨2,0x30464311aa19403beb03830b18cc282840626543820678700706,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xa82d1304e0b028485a32514a86e43011a4120c48200c8704543821068ec0906,0x2702⟩,by decide +kernel⟩,
  ⟨⟨2,0x88234150b044190d0040240bc4217a13950e1c841a5c02418541060150705543821068f00906,0x6706⟩,by decide +kernel⟩,
  ⟨⟨2,0x2e03e08d65f05600850a9042e0ee19c0c210bc144e4542170870ece06,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1d8331a04c260c142f144aa190b8440b690309c3217a1840706543821068f24e06,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1852350064454381067e91006458240dc2e0d0064754328107dd1006,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x308552a0e08a865020d1dca40d08828ba082f242168085438210769741206,0x2502⟩,by decide +kernel⟩,
  ⟨⟨2,0x17d0d0c3509f0b8340429214a906e4211bae00c8b0481b85c1a1d005e854832107dd7006,0x2b02⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_8_7 : List Batch_0_0_8 := [
  ⟨⟨2,0x45f090bc1a1d005e7548320673d70060d94c91032061464754837210691d7006,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1b2340e00320430b0a854837210695d70060df0b8235429206475483720683d7006,0x6b06⟩,by decide +kernel⟩,
  ⟨⟨2,0xe0fe1416822732a190843f76b030210c854151a8423a030464a543721808d67006,0x2f02⟩,by decide +kernel⟩,
  ⟨⟨2,0x2dc311b04420850581852a2950c8421a3c8581832080ba1785c01c01c2c954328107dd1406,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x71c2e050c482f32a4190339eba0302071c2e00bc3c654832107dd7406,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xc020e8c88b086420fbb280c270c85f0c46c110a87416061420c543210688f27406,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x28448200b06c5543821068ecc907a0090643584320673d9406,0x3102⟩,by decide +kernel⟩,
  ⟨⟨2,0x92412a0b05a5543821068f0c9070d0558025a15184c7543721088d0c907,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x108a4c116898aa86e42111a9920e212330c8048a10b04c8543872106970c907,0x7106⟩,by decide +kernel⟩,
  ⟨⟨2,0x48200b04a352aa1c108347a6483a1284c1168ac4a654372086836c907,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x35084a2c4a1550dc8422340241e8448200b06c5543821068ec0907,0x7506⟩,by decide +kernel⟩,
  ⟨⟨2,0x214882320c87022120080212406458d54387210697009072a0b0623543821068f00907,0xb506⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_8_8 : List Batch_0_0_8 := [
  ⟨⟨2,0x850c8622c22a1b904341b048381a84c1438b05c6543721088d40907,0x3b02⟩,by decide +kernel⟩,
  ⟨⟨2,0x683213109550a041dfbb301c9040160946a5543821068f40907,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x2340d000846255482107770cc078d6141bc10c84c427542108770ecc07,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x211609c8a84e210e5d9c0e0d09894424542710870cce07,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xd2411a2986c205b81c260c1686496aa19408347b170386a0cc68130858c11309ca8a54832710894ce07,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1208114c26005819a150c16495aa1c108347b2703868930720e04322ca1d0820a543821068f24e07,0x3f404⟩,by decide +kernel⟩,
  ⟨⟨2,0x28146608c08a86500cf0689c0e1a0c8611140400b284c103d1912c543281078d64e07,0x7d06⟩,by decide +kernel⟩,
  ⟨⟨2,0x60262c2208d18831d520c8419e651381e33844250a8030a3304569543208678364e07,0x202⟩,by decide +kernel⟩,
  ⟨⟨2,0x4581c0dc216094341442a194083f2e80381805850d0504a654321087e2d007,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1306a802522a190c33f168038480cc212a2e28654321078856d007,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x10f0c8c1aa0094ca87020cfd3a00e1a135004a454328067e5d007,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xc2e108c26a0094ca87020cfd2200e2c0c849854060c5116854327108856d207,0x1⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_8_9 : List Batch_0_0_8 := [
  ⟨⟨2,0x3b464350904c1a00ac589543281078d632070d8100611e10b062754321087dd1207,0x602⟩,by decide +kernel⟩,
  ⟨⟨2,0x10f85c0e10a85532a19408347729038670c466085a0bc2a012456a543281068f63207,0x610940c⟩,by decide +kernel⟩,
  ⟨⟨2,0x2ac1438ba8c2d32a190843c6a2903e105819a15006a6543821068f65207,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xa1d19823022a194033c1a29038683215078b10f4060a268ca543281078d65207,0x10a06⟩,by decide +kernel⟩,
  ⟨⟨2,0x3016c54aa8983118ea870420cf2e8a40f19c22128630a33045a8543208678365207,0x1202⟩,by decide +kernel⟩,
  ⟨⟨2,0x162250c2ee17045b400825520dc842375c01c1201a1d0060554832107dd7007,0x3c5814⟩,by decide +kernel⟩,
  ⟨⟨2,0x30083543a0094ca864210fbee00f84240b44c45483721069dd7007,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x59032014c202632a41b908348eb8038b10c48e10ac626543721088df7007,0x2a02⟩,by decide +kernel⟩,
  ⟨⟨2,0x40005b4682d08568918a550dca042359c01c364642c0e002b0421984954837210695d7007,0x906804⟩,by decide +kernel⟩,
  ⟨⟨2,0x2128d424091c626543720868367007161268d43a1214627543728068347007,0x128580c⟩,by decide +kernel⟩,
  ⟨⟨2,0x34462161b04191650d821052a1c108347a38038c04b0881b0600922912442a5437210689567007,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x4006689240c4aa86e420d13ece00e492310b0d84c10b03343a030448c543210688f67007,0x62606⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_8_10 : List Batch_0_0_8 := [
  ⟨⟨2,0x300b0a1a0481c5c754321087e2d4071689b0d82a1840627583721068947007,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x7130585a454321867e2d40703008322ca081c5a754328107e5d407,0x3602⟩,by decide +kernel⟩,
  ⟨⟨2,0x18541130b48a87020cfd3a80e04a08985a454328067e5d407,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x383f8427129550c8421fbb581c082d23a163254328067734d407,0x13606⟩,by decide +kernel⟩,
  ⟨⟨2,0x11a822e05898aa87020cfd2280e011691c4a44327086736d607,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x6c0604188c0aa864210fba2c0e04972164c443280767341407,0x3e02⟩,by decide +kernel⟩,
  ⟨⟨2,0x184020c062454328067dd34071892460343207867361607,0x13a06⟩,by decide +kernel⟩,
  ⟨⟨2,0x47118b46a8650ecfc26c0f84420a0624543280671d3407,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1328a24b1984471688d0a87040ed1d26c0e04238585a454328767e23607,0x3602⟩,by decide +kernel⟩,
  ⟨⟨2,0x6105819a102e82543aa1940834792b039208094c2600584c6182ca4a543281068ee5607,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x300a8619a08b4ca864210fbee80e080007860454832107dd7407,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x30083540a0898ca864210fbf280e1b0187460458432107dd9407,0x1⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_8_11 : List Batch_0_0_8 := [
  ⟨⟨2,0x38070427161550ca041fb8e8240e01c10bc4e554321087ec3a09,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x3178b4424543208772e3a09160ac703543280772c3a09,0x4202⟩,by decide +kernel⟩,
  ⟨⟨2,0x2f8330056454320877323a09160b470354328077303a09,0x4602⟩,by decide +kernel⟩,
  ⟨⟨2,0x8421c3e0609822c3aa19403b9a1d048bc441780b040ec01084056a543821078703a09,0x14a06⟩,by decide +kernel⟩,
  ⟨⟨2,0xbc2e106003c56383aa1c1083c3a1d048b2082d8330456654320877363a09,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x358a124904421a1783c0c113442c543628108e50c09178842ec316840707548321078943a09,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x304411a8c48a870420f1a818122fc2e02298224e184a8543621088f60c09,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x228122401b8182a1924589543621808f60e094309c58354821077cc0e09,0x5202⟩,by decide +kernel⟩,
  ⟨⟨2,0x400059431c1550c8421fe8b0251080448b06c5543821078d40e09,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x8a1220a4421e089bc0128854a86c42111c45c12170309c70454821707cc2c09,0x5602⟩,by decide +kernel⟩,
  ⟨⟨2,0xd0642f142441687c0c1304938662a1b140847b17048bc5806e00846a654321807fa2e09,0x144206⟩,by decide +kernel⟩,
  ⟨⟨2,0x1a8aa189c7055437210883fcc090b8140dc1219344e75438721083dcc09,0x15e06⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_8_12 : List Batch_0_0_8 := [
  ⟨⟨2,0x1742602c1c10b04e5442a1b90844096604b0087821b09c64654372108810cc09,0x16606⟩,by decide +kernel⟩,
  ⟨⟨2,0x1305e1b0903014870160e084e5462a1b908441966048b44c17a189c70654372180830cc09,0xdb804⟩,by decide +kernel⟩,
  ⟨⟨2,0x1520cc0844003643c130464a54372108814cc090bb141bc1833003675487210770cc09,0x7d6f8709038258⟩,by decide +kernel⟩,
  ⟨⟨2,0x2a30037088050f04c1162550dc86020d33024a8c026422014360e0858954372108816cc09,0x125f80c⟩,by decide +kernel⟩,
  ⟨⟨2,0x1224864c507d0c4e7543721088f6cc09032098308800e064754372108836cc09,0x285e06⟩,by decide +kernel⟩,
  ⟨⟨2,0x5e1b056290d8232c10744e545aa41b90844a66048d82f06608e04e65487210774cc09,0x8c0286⟩,by decide +kernel⟩,
  ⟨⟨2,0x150b8d942322a9c31083c3808049250bc1a0618646543628108e51009,0x586606⟩,by decide +kernel⟩,
  ⟨⟨2,0x18517d0093861b1950d884223d840241e44218098340266185e9543621088f41009,0x19e06⟩,by decide +kernel⟩,
  ⟨⟨2,0x903c118321e1b0540248b14a86c43011ec24122da2a160441a02246c8543821078d41009,0x486a06⟩,by decide +kernel⟩,
  ⟨⟨2,0x36031650070554321087fa3009138843b4341e0983404322458b543821078d41209,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x7839c102681c3437045e2c1ead50c8601fe8c8270540128b04c5543621088e23209,0x1a606⟩,by decide +kernel⟩,
  ⟨⟨2,0xd44d81200420a2c61e0890a15a9c31083c381904a25022ca0150726543218078fa3209,0x3a1c804⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_8_13 : List Batch_0_0_8 := [
  ⟨⟨2,0xd0642e0f82f0e8182609270cb543628108f6320982809834023e185e7543621088f43209,0x3d1211814⟩,by decide +kernel⟩,
  ⟨⟨2,0x60896802c1c0d4ca870420f1a86412334491c21821cb070c85436281079f63209,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x4110183141d9550dc842205340240e01c10505e5543821073dd009,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x153060d14161550dc86020d340243ac18345058554372108816d009,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x60a80211611520d885c75c02447060d0c4598260d0228954372108836d009,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xa18be8186129550d8842207dc0245f4312d030c5543621871f7009,0xee804⟩,by decide +kernel⟩,
  ⟨⟨2,0xd0240b82e0d0042754321087df70091a9278343a06185e75483621083d7009,0xfeb008f868e48⟩,by decide +kernel⟩,
  ⟨⟨2,0x89249220d0321c0a004012c2104210bb05ea86ec421122ce012174940e048260c008019841220cc5437621089147009,0x9485e814⟩,by decide +kernel⟩,
  ⟨⟨2,0x2c15a160482800be10861c11d6a86ec421126ce01289249220d0321c09048120c008108428b04305437621809347009,0x1fbb68e84a058⟩,by decide +kernel⟩,
  ⟨⟨2,0xb8230a4517b070543a01270cb543621088f670091005c6cc1a00846a7543782108d47009,0x321e13804⟩,by decide +kernel⟩,
  ⟨⟨2,0x85c1504762c191950d8a04239450242089c28cb054360922429583762108947009,0x42423804⟩,by decide +kernel⟩,
  ⟨⟨2,0xa8240d82a08b0a87543621088f21609086170541c31505c7543621088f21409,0x1⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_8_14 : List Batch_0_0_8 := [
  ⟨⟨2,0x61b87c0a0e08586543621871f3409e1e0b801722d070c7543628171d3409,0x1e606⟩,by decide +kernel⟩,
  ⟨⟨2,0x642e1004b030445a0e18a8a543621088f234090d82387c01650444754321087fa3409,0xcee06⟩,by decide +kernel⟩,
  ⟨⟨2,0x166080f41169550e0841cf750241e08430bc59c023e0846954321807fa3609,0xf602⟩,by decide +kernel⟩,
  ⟨⟨2,0x8a1238143a0e185e75436210881f7409c109c6a354321087eed409,0xc02⟩,by decide +kernel⟩,
  ⟨⟨2,0x1e8d84a864210fbee812248a1238143a0e185e85483621083d7409,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1250681861915610d88420f65026822fa06184c55436210881f9409,0x1402⟩,by decide +kernel⟩,
  ⟨⟨2,0x340783514502661f04142752a194083f662858400a3de1e0862654321087df9409,0xfe02⟩,by decide +kernel⟩,
  ⟨⟨2,0x422000f1b1150e09c421d3142c501a03c11870160898451a6042842d54382710870c50b,0x41c06⟩,by decide +kernel⟩,
  ⟨⟨2,0x143168c06a870420e7b9c162707c0d862d04c2862854832710894c50b,0x2402⟩,by decide +kernel⟩,
  ⟨⟨2,0x106138bc6a8e4210e5d9c161b09e085e4547210870cce0b,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xa18a070354328107dd2c0b178b4510682b158226c109ca8b54837210894ce0b,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1a0cc5091051450f05c0609270cc543281068f62e0b108a06a354321087dd2e0b,0x1⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_8_15 : List Batch_0_0_8 := [
  ⟨⟨2,0x50050381aa194083ee980581c021a0a0285c6543821073dd20b,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x4140c1224645543821078d6320ba00a064354321087dd320b,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x28021180d520c841f75c02c5182a0124645543281068f6320b,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x143a06084a4543216871f700ba0084603548321671d700b,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x2f249210a401309442304aa1b90c0349a38058a0414542d0d83401922442a543782108d6700b,0x30b004⟩,by decide +kernel⟩,
  ⟨⟨2,0x6155f82a1b0491213ac1b908344a3805e148a2f1450f054060e1892a543210688f6700b,0x41c06⟩,by decide +kernel⟩,
  ⟨⟨2,0x702e084e252aa190843f76b05820000bc101c4a6543821073dd60b,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xe1f028245141550ca059c74d02f87c0a088850554328107dd340b,0x42c06⟩,by decide +kernel⟩,
  ⟨⟨2,0x322822e0a82c0c31510a864210d1e4681645a0e084c4543218671f340b,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xfa1d0460454832107dd740bc108c64354321087dd360b,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x15e17838213898ca864210fdc30520f0187460458432107dd940b,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x90085c4e1c2aa190843f60d14a1608c315884626543821078701829,0x4402⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_8_16 : List Batch_0_0_8 := [
  ⟨⟨2,0xc184a160217618bd801010a950e0841e1c068a41201c10bc4e554321807ee1a29,0x4c02⟩,by decide +kernel⟩,
  ⟨⟨2,0x10a1586c013c0c2e2f60e0820b548321078941a290821581088005c5ec3823041eb543821078741a29,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x2861c1d8d50c8421fe830a40581168845e554362807e50c29,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x39142450f8182609245e9543621088f60c294309c5e354821077cc0c29,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x210e0d86a864210ff41c522044884764543821078d40c29,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x114091238182a19245e8543628108f62e29c109c5e354821077cc2e29,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xc04a1d86c18862fc2b0704272a31520dc84225330a41000c10ac4a5543210871fcc29,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x730540248c8aa86c42111ec205202a007064454321087fa1029,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x6c061c189150c8421fe848a44140c1224645543821078d41029,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x3b40c10ad122f32a1c1083c6a191484b054017924566543628108f63229,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1414128d50c8421c7f40a41201c1050585543821071dd029,0x5402⟩,by decide +kernel⟩,
  ⟨⟨2,0x140108c06a864210fbee05343a06085e4548362073d7029,0x5c02⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_8_17 : List Batch_0_0_8 := [
  ⟨⟨2,0x828030038c912213aa1bc10846a38148c512492410c80c1178c042a5437621089167029,0x317004⟩,by decide +kernel⟩,
  ⟨⟨2,0x188415f43c1304912142c1bb10844a38148c4502f0e50e8182609270ca543621088f67029,0x4c02⟩,by decide +kernel⟩,
  ⟨⟨2,0x1e030e0c48a864210ff42c5202a087064454321087fa1429,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x3608e1f020d41161d50e0841c7750a44a1a08072838260618a89543621088f21629,0x6c02⟩,by decide +kernel⟩,
  ⟨⟨2,0x17066145782a089cea864210fdda8520a065045c4543210871fd429,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x5e1d246188b08e6c42123b28520fa1d0460454321087df7429,0x7402⟩,by decide +kernel⟩,
  ⟨⟨2,0xa4490980b0614211da150c85c2203304ac1e03a0d0060554321087df9429,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xa849090340582c0850c92a8642e110218256320b82587c1828284e854321807ecc12b,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x800c3b60c2864654321708814c12b0b82202c11930c6b056042842b54382170870c12b,0x47c06⟩,by decide +kernel⟩,
  ⟨⟨2,0xbc3a17604286a654832170894c12b1785c190560c287a754382170874c12b,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x105c109c4c454321087eec22b048660bc106e0826754321087ecc22b,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x200017050d4aa870420e3b9c562c1204e120380b058105c10404cc54382107870c22b,0x1⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_8_18 : List Batch_0_0_8 := [
  ⟨⟨2,0x902f0d8481a0b01608a704272a3150dc842204338ac4804c109c585547210870ece2b,0x8c02⟩,by decide +kernel⟩,
  ⟨⟨2,0x2c06f046b8282b003685487210770ce2b1205e1b0982c0583821489ca8b54372108812ce2b,0x8c02⟩,by decide +kernel⟩,
  ⟨⟨2,0x178b01143e07046a8510a550c8601f7430ac5905c13044e55487210774ce2b,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x200b8310b4360a247a8543821078d60c2b178b06bc1e013442754328067e50c2b,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x5d820ca1a15123d3aa1c1083c6b07158d783c04289842654321087dd0e2b,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x120182e08321432a1908438fe9158240305c105c286543821071dd22b,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x17a009583828a090ea86e421102da456190bd01822ac145048854372108814d22b,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x162278340c1218a87543218078dd102b1e0bc58094350387c1c12147ab54321807dd102b,0x325004⟩,by decide +kernel⟩,
  ⟨⟨2,0x13881062142d0c32861660a80c144b550e0841e35840ae4843c0a8464553821076870102b,0x1d2300c⟩,by decide +kernel⟩,
  ⟨⟨2,0x60858311aa190843ee89158970489243070c65432107869f6102b,0xa402⟩,by decide +kernel⟩,
  ⟨⟨2,0xc8290bc1a00d442754832107dd702b138844086a1a0d8340c122458b543821078d6122b,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1c1a1a145f40c10d4ea90640ce7ae05649c09070540a1e145e85432106881f702b,0xfc21014⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_8_19 : List Batch_0_0_8 := [
  ⟨⟨2,0xd8220dc3e041705410ba550e0841c7758ac58200650d834042a24429543782108d6702b,0x562b00c⟩,by decide +kernel⟩,
  ⟨⟨2,0x5c198282d044e654321087eed62b040003305c10302c7543210871fd62b,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xc1504a83b22a1908434790a15820002f166086a654321807dd142b,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x17080258182a0e14a88543210868f2162bc109062354321087dd162b,0xe402⟩,by decide +kernel⟩,
  ⟨⟨2,0x22848c01030541a1e145e95432106881f742b4283c6c354832107dd742b,0xec02⟩,by decide +kernel⟩,
  ⟨⟨2,0xa0d030c3222a19083440fca158c46a258432107dd942b,0xf402⟩,by decide +kernel⟩,
  ⟨⟨2,0x120648bc12303426754381067e9c40c25f0b82192283426754321687e2c40c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x308a1310910c841a1fdb1030481125f0b8219c191426953210687f2c40c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1a8b033098240c341522f05810d10b550c9c42214b143059c2108c4645542710870ec50c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x834085e2c189550c9c42205b14325e2c41b0027c2108c45a95482710770c50c,0x73f00c⟩,by decide +kernel⟩,
  ⟨⟨2,0x41a042d1a8c4aa9064e211298a182c0d06528128411780c125c3442c54327108856c50c,0x11402⟩,by decide +kernel⟩,
  ⟨⟨2,0x12ba13081221868c4ea864e2111ad8a183a1ac5129458191783c06143442c543827108c9c50c,0x1⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_8_20 : List Batch_0_0_8 := [
  ⟨⟨2,0x4b6370b82192283426854320787c7c60c1d11b84c106924627543281068f4c50c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x2706235098a5543721806934c90c8a2501345628bf07c0a15184ab543721088d6c90c,0x51c06⟩,by decide +kernel⟩,
  ⟨⟨2,0x21098b08a8420d0fe19c1942608d4624543821068f4c90c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x2004c1f084340129d50c8421f8b403043c2e0b0064554218067f2ce0c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1c43c2e0e0e802f3aa194083f2e806087842f12e0e8065432806e5d00c,0x52c06⟩,by decide +kernel⟩,
  ⟨⟨2,0x4b1984018340b0740628954a864300f069a018240c8401fc2c18268084321086f6d00c,0x53406⟩,by decide +kernel⟩,
  ⟨⟨2,0x5e08a009442554328067e5d00ca009442354321687e2d00c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x8610bf0740129950e0419fa74030481125f0b8219c191426954320687e6d00c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x5f4012884886420d0feda0182fa009442454210687eed00c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xc66160d8b08189950c8601e0d348300c020d03462554328107e5d20c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x2002f230504a554381067e9100c240847635821067770d20c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xc00178b38414189d520c841fe448300013929225e55821076770100c,0x1⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_8_21 : List Batch_0_0_8 := [
  ⟨⟨2,0x258240dc2e08648a0d09a550c8421f7cc0309609030bb85c11660c5a954328107dd300c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x4a009442454321087fa320c048078583a00f45e754321807f9320c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x186236088481c1d00922f4aa19408347b19062878400e09225e65821067770320c,0x54406⟩,by decide +kernel⟩,
  ⟨⟨2,0x50422c189150c8601a38548304b464350904c1448be289543210878d6320c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x5f45c1d19123132a190843c6b290605c1820a00846a6543821068f6520c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x12042311aa390b438fb806214ab1509c20906543218067934520c,0x15402⟩,by decide +kernel⟩,
  ⟨⟨2,0x1136340d844860c018a3b4aa390c0341a38063060048628847665472106883f700c,0x7c83f01c⟩,by decide +kernel⟩,
  ⟨⟨2,0x90f08903122c390833ca38064015ec524084626547210688f6700c,0x1b14300c⟩,by decide +kernel⟩,
  ⟨⟨2,0x120681fc21760e8275432806e5d40c0d0101fc2c1d045c754321087e2d40c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x90321007f0b0608a0a14c8421bcb50301fc2c18b448554328107e5d40c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x24048642741109950ca019f975030121909d0442554321687e2d40c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x46098305e454381067e9d40c07f08338322d0426754320687e6d40c,0x1⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_8_22 : List Batch_0_0_8 := [
  ⟨⟨2,0x4e822f10914c841a1fcb5033800ca08bc42554210687eed40c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x48be8221171550e0419fa450300c02c18b44a554328107e5d60c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x5846c1f088a3132a19408346e9a060bc10061609785c0c1d048aa54328107dd340c,0x393711c008⟩,by decide +kernel⟩,
  ⟨⟨2,0x30c4622608841f2285c6295432810681d340c0306683c22283026754321087df340c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1c02040985842654321087fa360cc18bc70354321807f9360c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x30ec6bc2c18c4cb086420fbb28181f108b0624543218068e1560c,0x18402⟩,by decide +kernel⟩,
  ⟨⟨2,0x689c423222a19403be2e20706809410cd0042654321087df940c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x306c1180d50c9e01cd314386ac1c18b460554327108852c50e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x4181088240058266160d824b5aa19388442b62874124c2cc1b045a65432708736c50e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x28844c2722a1383439762870998cc283408342c60e0c20a54832710894c50e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x240892f85c10a1144c853210867f2c60e108984e3542076872ec60e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x9608340e270b884e865020cfed8e1c001388452454321867e1c70e,0x1⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_8_23 : List Batch_0_0_8 := [
  ⟨⟨2,0x60d084e2c22a1c108347b65870401e482370b800d6092436a543281068f6c70e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x27148846a8430cefc25c1d144a04a80c0a1230588543218078d6cb0e,0x5202⟩,by decide +kernel⟩,
  ⟨⟨2,0xb545e089c1a2132a10c33bf117070878413128b04c654210867e22e0e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x21e1704da261609cea84300efa45c1c056008458454210877d02e0e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x131692ec622b0863050a09d4a90420cf1285c1c2f1089c524542810678f62e0e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1068130442c2a023058854321087814d00e048078421c1d0058754832107e1d00e,0x1ac02⟩,by decide +kernel⟩,
  ⟨⟨2,0x84282c1aa4190b3f0e8074198d04813098223a021c58a54321078836d00e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xf2360f854024b04588543218068f6d00e1085058354210867eed00e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xd01f8226160f4ca865020fcba41c1da331a84c2a0230588543218078d6d00e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x6010b05e141b19520c841f74403a0cc6813084ec1c1c2058954321870834d20e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xed190d4241226282c42a190c03c6b09070be59c1a009842654381067e9100e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x12c1206e17048b40132150ca041f74c0381986236088583a0124589543218068f6120e,0x1⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_8_24 : List Batch_0_0_8 := [
  ⟨⟨2,0x210a0b06a8420d0fdc601c4b0481b85c12285c28854321087df300e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xd451781785401b1d50c8421fe4c8381986236088583a0124589543210688f6300e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x8c420661a0b826085c5f40039258a865020d1ec641c2b04e0e8bc10bd0042854321087fa320e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x5c1940108d4aa870420d1eca41c17465190c05425090436a022628c543210878d4320e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x115831548c4543210867914520e1685c2b4542e0c654060d1912b543218078d6520e,0x1b402⟩,by decide +kernel⟩,
  ⟨⟨2,0x12071085e822732a108433f76a070b62a55230e10e6543210687936520e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x401b85c0178b03c754832107dd140e1301b842c03d045a754328107e5d60e,0x1b402⟩,by decide +kernel⟩,
  ⟨⟨2,0x5044c301aa194083ee9a070bc97c0a089842654381067e9140e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x60250627a091442754210687ee340e0401000172285842754321087df340e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x400400171088cca864210ff46c1c080009870454321087f9360e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x28102f41a0084ca864210fbf281c060107464458432107dd940e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1305c2a0b84c0582c082b1a1ab54327108852192c0a084623542106877f940e,0x1⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_8_25 : List Batch_0_0_8 := [
  ⟨⟨2,0x2d8309808b032c082e0d8ca543210788521b2c0ec198d02610c82ec182c3528b54832710894192c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x6148d40191150e0581fa440b116070309b85c11650056954328107f9102c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x118642f464350904c1a0215131462a19083c46b091622f85c1a00b056654328107f9122c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x858240dc2e0867070509a550c8421f8b48b216090370b838382d002e954321807e1d22c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x26040b381c21c03048854328107f9142c0bc198d02615004ac1c1c2048b54321087816d22c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x200105c1d0450654321807e1d62cc189460354328107f9162c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x60121706312ac219083eeca1601805050481c5c654321087e2d62c,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xb24c168a25380c1148852a865020f1ad805c0d108a44e454321877c1c02e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1a86a1609030a88462854321078852c22e0d0561301608d608c0c1b1850b54321708852c12e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x178846a354381067e9c22e9784d0785168846275482107770c22e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x69258207108b04e743281067f6c32e000846c354328067e5c32e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x924803104804a108a50a864210d03d925d14038418236e00bc428543281078d6c32e,0x1⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_8_26 : List Batch_0_0_8 := [
  ⟨⟨2,0x2707c2e0e143421a00652a864210fc5a05d144a04a85c0608a45e8543281078d6cb2e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1ac283f8409a001ce865020deda05c0742e0f85c110d005e854832107e5d02e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x5005e211aa419033f2e81741a042563308138360d005ea54321087816d02e,0x1bc02⟩,by decide +kernel⟩,
  ⟨⟨2,0xc1a00bc42443281067f6d02ea00bc42354218067eed02e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x24038314500586543281071dd22e1487680c1108be287543281078d6d02e,0x1bc02⟩,by decide +kernel⟩,
  ⟨⟨2,0x4e211a8d609c419dc348b80c02c18945a5543210871fd22e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xe01a00bc42554321087df102ea00bc6a354321807dd102e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x302210a0bc8a84210cfdc205d81a00bc42454381067e9102e,0x1c402⟩,by decide +kernel⟩,
  ⟨⟨2,0x1a0c85e8c8682a0a854060a2628c543281078d6102e1aa8407c2e09225e75821076770102e,0x5c406⟩,by decide +kernel⟩,
  ⟨⟨2,0x38043421171550c8421f7c48b80c05010a462554321087dd122e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x7046a05244bcab0420ecee0645c1a0bd190d05a12085d4060a2628c543281078d6122e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x5249c090458212a9d50c8601a38548b83b464350904c1448be289543281078d6322e,0x1d402⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_8_27 : List Batch_0_0_8 := [
  ⟨⟨2,0xc512c18a9560c213aa1908433c8b29170b85015828bf074060d1912a543281078d6522e,0x1d402⟩,by decide +kernel⟩,
  ⟨⟨2,0x20035e0920423b32a43908340eb81708407c2e08b0766548210671d702e,0x377004⟩,by decide +kernel⟩,
  ⟨⟨2,0x1dd006bc142850427547206873f702e24084763548720673d702e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x316330982481a8ecea8e4210d02ce05cc114884764547281068d6702e,0x1f402⟩,by decide +kernel⟩,
  ⟨⟨2,0x3157c8784481a9961c8419e51c0bb8540240dc6a5547210688f6702e,0x9ec06⟩,by decide +kernel⟩,
  ⟨⟨2,0x650a0407f0b074116a1520c841f9750b8100fe17030a1aa081c32954321087e2d42e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1c421aa089caa84300cfdda85c07a08bc4e454832067e5d42e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x18042f06d045c6543210871fd62e04010018314504587543281071dd62e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xa08a476354321807dd142e241188440178a46e75432810681dd62e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x4c045e211a9550e0419fa450b84c041385842554321087df142e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xc02148c48a864210fba2c5c09a08bc4e454210867ee142e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x24100423522a190c03470ab1702306000d0844a654321087df162e,0x1⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_8_28 : List Batch_0_0_8 := [
  ⟨⟨2,0x190260c3541a0084ea864210fbf285c06010a462458432107dd942e,0x1fc02⟩,by decide +kernel⟩,
  ⟨⟨2,0x8213c1858362aa190b8440860a71188429c31130583a0d0058a5843210681d942e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x40948420a00c0830b118954321708814c14e1305e12058240583066046128b54321708832c14e,0x60406⟩,by decide +kernel⟩,
  ⟨⟨2,0x742f0682b16083260c6128a54832170894c14e4a4200d0460c018023c121c58b54321708836c14e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x4a422070060316302542a190c03c1a612701e0c04128605a654328107e5c24e,0x21402⟩,by decide +kernel⟩,
  ⟨⟨2,0x844004a9446411811a11419831862a19388440b62a702001450d0604a6543210871cc54e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1201c160e802c32a1c10838ee9270943a09820c05f0660a5230a54832710894c54e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xe01c160e802f32a1c10839ee9270400982c1d004a6543210871fd24e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xbe0a10463144a17c1e0983085aa1b908440b692705c0d05628bc4f8260c2118a54372108814d24e,0x387004⟩,by decide +kernel⟩,
  ⟨⟨2,0x58250320a10871c1d50dc84220db493858250809f04c1c1c218a954372180834d24e,0x30901fc14⟩,by decide +kernel⟩,
  ⟨⟨2,0x168642f4542d00418244c514a870420f1ac209c2c0c0500e852209b05c1a061856c543281068e5104e,0x23c02⟩,by decide +kernel⟩,
  ⟨⟨2,0x1204e988c4198a6543218076934104e17e170540c31246c7543210868f6104e,0x24402⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_8_29 : List Batch_0_0_8 := [
  ⟨⟨2,0x5a200c85e8a85a0609131452a1c1083c6b092700b0340c30ac606543281068e5124e,0x24c02⟩,by decide +kernel⟩,
  ⟨⟨2,0x231064c2188a864210ed228249c250c05f04c1a06186a8543218068f6124e,0x25402⟩,by decide +kernel⟩,
  ⟨⟨2,0x300b24e04838322d030c2852a19408340e98270ae3098430e10e6543210786936124e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x689305c1e0482440c5030c285aa190c0347099270601649c09070445a06184ca5432108681f304e,0x25c02⟩,by decide +kernel⟩,
  ⟨⟨2,0x6c2e1640a802005a26289543821078d6324e220ac3145a06186c7543210868e2324e,0x25c02⟩,by decide +kernel⟩,
  ⟨⟨2,0x3624b0491184c4190c8543210876916324e14060190517e09834003e1892b543281068f6324e,0x20c02⟩,by decide +kernel⟩,
  ⟨⟨2,0x3404c1e0a822e32a1908438feb270200183c1504586543821071dd64e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x160308848130903582e05040f8662a1940834728a270640983c15045a6543821073dd64e,0x21c02⟩,by decide +kernel⟩,
  ⟨⟨2,0x250b84300482009035832260a83866aa1940834728b270b0504420e024d8224e198aa43218076834144e,0x22402⟩,by decide +kernel⟩,
  ⟨⟨2,0x9044c1e008018a09170c2852a19408340e9a270330c45c021c60643210786836164e,0x62c06⟩,by decide +kernel⟩,
  ⟨⟨2,0x2cc3116838213995084219fb8d1382048c01003045a0e184c95432108681f344e,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x5e2b0c6148982a05070c2652a19083440fca270630741a06186065843210681d944e,0x1⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_8_30 : List Batch_0_0_8 := [
  ⟨⟨2,0x74c6617045f80159d50c9c4223af14403140a0e186455843210683d944e,0x26402⟩,by decide +kernel⟩,
  ⟨⟨2,0x2f0a0c06a64e210e258a20c3c008464454328107ecc510,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x106810b04a322aa19388440b628801d87c2e08206465382710770c510,0x26c02⟩,by decide +kernel⟩,
  ⟨⟨2,0x4812c6228c042250d70d85806092daa864e2110ad8a203a60b1b842f12e00568543278108f4c510,0x79b00c⟩,by decide +kernel⟩,
  ⟨⟨2,0x1098dc10a0bcaa870e20f938a2106634098407c00ac6c854382710874c510,0x3a3004⟩,by decide +kernel⟩,
  ⟨⟨2,0x1c1610505e454371087cac5101d11585c1630505e7543827108c9c510,0x6a406⟩,by decide +kernel⟩,
  ⟨⟨2,0x1d11a8a45e160232c124c514a865020d1e98a2146635098409178504a8543271088d6c510,0x1a9406⟩,by decide +kernel⟩,
  ⟨⟨2,0x2f0a0886a87020ef938c202d2491460c2294218c8543271068956c510,0x2b402⟩,by decide +kernel⟩,
  ⟨⟨2,0x94184cc1c00bcca86e210e29922145610505e454310877cac610,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x17ab043c312c19838062a550dc601cd32441580f62b07862f836004a95437108716c910,0x2bc02⟩,by decide +kernel⟩,
  ⟨⟨2,0x6001e361aa1c3883ba64880858706c03045e65437108736c910,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x6290a8c2f0a094ca86e210fad922010a110b8380233162885437180683cc910,0x7ca300c⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_8_31 : List Batch_0_0_8 := [
  ⟨⟨2,0x111088cc5c00be84c18a2550de041a3d324408d4262c504a554371806834c910,0x7ca700c⟩,by decide +kernel⟩,
  ⟨⟨2,0x220c46a1314aa86e4300d269922009a2b145f42a30504a8543721088d6c910,0x6ec06⟩,by decide +kernel⟩,
  ⟨⟨2,0x628be8414129550c421df5b28405a19059158380a1126289543821068f4c910,0x2a402⟩,by decide +kernel⟩,
  ⟨⟨2,0x8331a04c20db0700c5192550c8601e0d338420d4262c504a554318067834ca10,0x2fc02⟩,by decide +kernel⟩,
  ⟨⟨2,0x2600140b04c5583210671d701060c5060353210678856d210,0x30402⟩,by decide +kernel⟩,
  ⟨⟨2,0x6340d84c162c20647537218068347010040d86a353721087d67010,0x70c06⟩,by decide +kernel⟩,
  ⟨⟨2,0x601507000c179950c8421f8b50415ec5819846c5537210688567010,0x26c02⟩,by decide +kernel⟩,
  ⟨⟨2,0x180038bc48454328107e5d4101206833c2a0e000e75432806e5d410,0x9e02⟩,by decide +kernel⟩,
  ⟨⟨2,0x18041ac001c4a654328107e5d6100c8401fc2126001875421086eed410,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x548c2fc05044c654381067e91410038141fc2c030c4a754321087eed610,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x5e1b030b04bc3e1602824552a194083ee9a08018042c17e006c658432107f91610,0x75309101c⟩,by decide +kernel⟩,
  ⟨⟨2,0x30c462160b00250b8c90a865020d03a68202c4c91b8580a0915288543281068dd3410,0x4244af014⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_8_32 : List Batch_0_0_8 := [
  ⟨⟨2,0xc008c64354321807f936100b9308c42808848b820f89d28b543210688ee3410,0x31402⟩,by decide +kernel⟩,
  ⟨⟨2,0x1021511858362aa190c03470ab080b4978023149286543218068f95610,0x2b402⟩,by decide +kernel⟩,
  ⟨⟨2,0x680a3de16006c654832107dd74100d85c9847036148a1fc014928b543281068ee5610,0x28402⟩,by decide +kernel⟩,
  ⟨⟨2,0x300c1180d50c9e01cd314480e01c008458554328107ecc512,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x31986218240c5c2c61601824b5aa19388442b62894125c2cc03045665432708736c512,0x34402⟩,by decide +kernel⟩,
  ⟨⟨2,0x188c04a84210cfdd8c2506810b83c1703b1a08c260e0056c54382710874c512,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x14128b06a64210cfc464250663409841360c5058854321807834ce12,0x34c02⟩,by decide +kernel⟩,
  ⟨⟨2,0xa04a085050558432107e1d412170952f0060c50967532106788563212,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x7f0b001b170d4ca864210fddac241a030bb842cc001c2c854328107e5d612,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x10e0c962f235045c754381067e914120d81b87c2178b03a758432107dd1412,0x25402⟩,by decide +kernel⟩,
  ⟨⟨2,0x4c0741c00c0aa865020fba68244c138b9284543210688ee1412,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1b018b870454321087f936120b9330c46c110a02450f89d28b543210688ee3412,0x1⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_8_33 : List Batch_0_0_8 := [
  ⟨⟨2,0x7c2e4c23e148b80292512a865020d1dcac241ac341705412389d288543218068ee3612,0x34402⟩,by decide +kernel⟩,
  ⟨⟨2,0x641704b0f8380828850a865020fd83260060107876454832107dd7412,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x380140d48a864f0211e832602163707843582e002e8543278108ec1930,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x120312e020a2132a194083f70d980318cc21dc1a041761e0048a543827108741930,0x35402⟩,by decide +kernel⟩,
  ⟨⟨2,0x6004a301aa194083fc8b18018042e166006a654328107f91430,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x18041982e0018163aa190843f16b1806c0705c050450654321807e1d630,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x180485c00d8aa906420fbae860170603f858082d0436854321807eed630,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x108498d0361b07008b142550c85c2215b04c81201c00845e554321807ecc132,0x35c02⟩,by decide +kernel⟩,
  ⟨⟨2,0x608518c2f181550e085c232704c81809833190b02614102ec317b0700d54382170874c132,0x36402⟩,by decide +kernel⟩,
  ⟨⟨2,0x958314181150c8421a3db04c86616a35098cc2608505e9543281708d6c132,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x88085e25c03184c7543821078e9c232129488cc1800e6107543217068956c132,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x12fc28ac10362a9c1083bb861190af0bc1c00844c654321087eec232,0x1⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_8_34 : List Batch_0_0_8 := [
  ⟨⟨2,0xea82c121318282f3aa1c1083c64e1190258412c022c6c654321078856c232,0x76c06⟩,by decide +kernel⟩,
  ⟨⟨2,0x7446e1304922f8a1d50c8421a3db08c86746a13198409608505e9543281078d6c232,0x37c02⟩,by decide +kernel⟩,
  ⟨⟨2,0x93c1a10b22855432108681ec932294120049608e6107543210768956c232,0x1b6c06⟩,by decide +kernel⟩,
  ⟨⟨2,0x1c8220cc1188c0ca86e4210d22d926409c00c18342178528c8543728108d6c932,0x38402⟩,by decide +kernel⟩,
  ⟨⟨2,0x106816004ac642b082ec117c516a8642e1102d9c642e1602d838024d0a288543821068f4c932,0xb6406⟩,by decide +kernel⟩,
  ⟨⟨2,0x38432040d48a6e5020face064000450c604583210671d7032,0x760ae06⟩,by decide +kernel⟩,
  ⟨⟨2,0x36182be86c18422cc285372106885670321b15e0ac642b0862c1a1abe10b537210868167032,0x78c06⟩,by decide +kernel⟩,
  ⟨⟨2,0x300a8380038bccb086420fcba86406016143541c001c32854321087e2d432,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x180541c00305e6543210871fd6320d810078014504587543281071dd632,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x22506283022a19408340eeb1905c182bc281c1fc2c050436a54321087eed632,0x37c02⟩,by decide +kernel⟩,
  ⟨⟨2,0x11a8380191150e0419fa450c80c02a0e0064554321807dd1432,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x8c84210bd283932a19084346e8b190185f85e16006c654321087dd1632,0x1⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_8_35 : List Batch_0_0_8 := [
  ⟨⟨2,0xb858061ca50aa864210d1f2ac64250f85c8f86230170442a089d28c543210868ee1632,0x38c02⟩,by decide +kernel⟩,
  ⟨⟨2,0xd8581b266003e0b292512a865020d1dcac64391390c4a212360caf8522600a4c543218068e15632,0x3cd7004⟩,by decide +kernel⟩,
  ⟨⟨2,0x250b9270c46029130442a0e0099146aa41908340eba190ac0d85e16006c654832107dd7432,0x3a402⟩,by decide +kernel⟩,
  ⟨⟨2,0x4837822c0d854ca864300fd982a42e4407892454837210691d7432,0x3eb004⟩,by decide +kernel⟩,
  ⟨⟨2,0x206218330c4704608b22a954321708836c152818858706100b22a754321708814c152,0x7b406⟩,by decide +kernel⟩,
  ⟨⟨2,0x7020942a2b2aa194083f2e12905c190562c1076c36083e2aa54382170874c152,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x182c58a8c88a864300f06984a41bc160064454321087eec252,0x3c402⟩,by decide +kernel⟩,
  ⟨⟨2,0xd85464354328107ecc5520d81807450d0544a7543210871cc552,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1287a083017b0d820f8aa550e09c421d315484b0460c5464554327108816c552,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x31098c560c522a654327108816ce520d8198ac18a45498754327108814ce52,0x7f300c⟩,by decide +kernel⟩,
  ⟨⟨2,0x1a2915238e0aa864e21106d9ca4c18a3162a454327180834ce52,0x69b404381c⟩,by decide +kernel⟩,
  ⟨⟨2,0x680982c003282193aa1908438feb2906c0782c0504586543821071dd652,0x1⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_8_36 : List Batch_0_0_8 := [
  ⟨⟨2,0x1bc16006a454321087eed6520c813058003d04347543821073dd652,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x210c95888241870e838616a950ca041a394514b014126218765543218078dd1452,0x3cc02⟩,by decide +kernel⟩,
  ⟨⟨2,0x160a0898320e025cc5c31254864300ed06828a441c0130604432107868f61452,0x3d402⟩,by decide +kernel⟩,
  ⟨⟨2,0xc18c07034321078683616521285f0621218903444c05070cb543281068e51652,0x7dc06⟩,by decide +kernel⟩,
  ⟨⟨2,0x1831090c5819c011683864aa19084340f9a29084898321e002b4122e1850a5432810681d3452,0x7ec06⟩,by decide +kernel⟩,
  ⟨⟨2,0x2f168570a44a1d070c2e4aa19083440fba290570143a0e186065483210681d7452,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x20cc6813098380130b10a8e6421102832e015a18ec7045483210683d7452,0x7fc06⟩,by decide +kernel⟩,
  ⟨⟨2,0x206c109600423032a39908442b0cb84118223c021c606547321088361970,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x62d09841037884101318a551cc842206c65c1838314600585547832108f41970,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x18b44608e86413a2d0707806102042d548732108591970043098235a150426101908476b548732108391970,0x3c06014⟩,by decide +kernel⟩,
  ⟨⟨2,0x1b09a0f002c080c8ea8e6c421127c32e02f0d84c8c2c0391383c2c042056c5436210883e1970,0x380e004⟩,by decide +kernel⟩,
  ⟨⟨2,0xd866264981c0026c1842551cd8842245865c066210cc4d84c1802321095473621089141970,0x8802⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_8_37 : List Batch_0_0_8 := [
  ⟨⟨2,0x5913081158300840c90a8e6c421126c32e0250dc4c93034184c20c18031610c5473621809341970,0xfcc018008⟩,by decide +kernel⟩,
  ⟨⟨2,0x3a2360063c260c206a8548362108f4197089d106613048228ac5a1308658310e0182f547321088d61970,0x1da5407b01c⟩,by decide +kernel⟩,
  ⟨⟨2,0x3a198948c0309f0b01081aa950d884223d865c02631c03061055478362109f41970,0xf802⟩,by decide +kernel⟩,
  ⟨⟨2,0x10bf078063094ca870420f1d236e0060081f85c1c1e005e854328107e51b70,0x10802⟩,by decide +kernel⟩,
  ⟨⟨2,0x178498b04c060d8c2542a190843c2b0db80260cc6813080383c03144aa543218078341b70,0x68602f80c⟩,by decide +kernel⟩,
  ⟨⟨2,0x5158ac11d5045f830830b00c65aa419083c2c8db809284c2a0b0476210831464a5432108783b1b70,0xf2600a814⟩,by decide +kernel⟩,
  ⟨⟨2,0x5e2c0d925064180316103152a1b10c03c9a0db80eb8400840d4626548362108f61b70,0x1c5e00c⟩,by decide +kernel⟩,
  ⟨⟨2,0x48200206015143583c00954a864210e3872e03308516074217b1584092088462c543210878d61b70,0x11a806⟩,by decide +kernel⟩,
  ⟨⟨2,0x960cc622c098580178d52a8e6421102c72e03a1a80b8383c03185e85473210885e3970,0x1c802⟩,by decide +kernel⟩,
  ⟨⟨2,0x31b0780608bcaa8e6410e6c72e0c612f0b078017b048a854732807343970,0x6aa03280c⟩,by decide +kernel⟩,
  ⟨⟨2,0xe98dc260e005e353aa3c190847a1cb804a1025820bf018360b1896a547321088563970,0xf6804c04⟩,by decide +kernel⟩,
  ⟨⟨2,0x2da29248c44e17045f8009e0e10c5436210881e39701ab047445a08bf0610616018cb548732108593970,0x3ebc0242d008⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_8_38 : List Batch_0_0_8 := [
  ⟨⟨2,0x19b1b84310de01823b22c214a8e6c50106872e0310d91582081d8d46485473621089163970,0x3c28006014⟩,by decide +kernel⟩,
  ⟨⟨2,0x3122b085f421084182354aa39908446b1cb83180bc260c20646547362088363970,0x749200c⟩,by decide +kernel⟩,
  ⟨⟨2,0x6d06c11a8b61065478362109f439701d06c8d45e160183831d92610b548362108f43970,0x22002806⟩,by decide +kernel⟩,
  ⟨⟨2,0x5822080308d80e111706c124c218a906c4211ec76e022230b3842622c20628543621088e23b70,0x4f016406⟩,by decide +kernel⟩,
  ⟨⟨2,0x2f1588a1044c190842314aa1b108440e2cb80ec58220831b84c1194206aa543620878363b70,0x4802⟩,by decide +kernel⟩,
  ⟨⟨2,0x8401c45c1c00846475436210883e59701104c92452260f8308a160042b5436210881e5970,0x262c452014⟩,by decide +kernel⟩,
  ⟨⟨2,0xc4364941a001046a130474a5473621089165970248220c41235091875473621089145970,0xcb6004⟩,by decide +kernel⟩,
  ⟨⟨2,0x49231068438439951cd884224d965c0368360a007408235098a95473621809345970,0xe448e014⟩,by decide +kernel⟩,
  ⟨⟨2,0x64218380108d4ca906c4211e8b2e0310481a8ac5a1304748547321088d65970,0x7e56030058018⟩,by decide +kernel⟩,
  ⟨⟨2,0x185c1e028232109950da041fa451c2822c1301f0d82170ac6a9543628108e51470,0x3fc02⟩,by decide +kernel⟩,
  ⟨⟨2,0x11b0035e1504760c4421520d88423e451c07688030d419c2c050464954832107f91470,0x750d603881c⟩,by decide +kernel⟩,
  ⟨⟨2,0x361a0be1b040023108ca242d507061072a1b14084728b381130d82c0314646436218078341470,0x139806⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_8_39 : List Batch_0_0_8 := [
  ⟨⟨2,0x26102360f85411ae01109548362108f916700801b07c21ae004a754832107f91670,0x18a204a01900c⟩,by decide +kernel⟩,
  ⟨⟨2,0xcc311705801a8c8e86c420f106c2ce0070488462454621087ee1670,0x2540e3004⟩,by decide +kernel⟩,
  ⟨⟨2,0xd84c1244196188d82210206217c1e02824582a1b140840e9a380e8360ca3708838018a206aa436210788d61670,0x7ed050ca188280b06c064030⟩,by decide +kernel⟩,
  ⟨⟨2,0x190b81b07c2c05048a854832107f9347009e188c03c11085845a08404cb5436210881f3470,0x3ef601c2ea028⟩,by decide +kernel⟩,
  ⟨⟨2,0x580c04d048b80109d5188421fb8d1c027830811b8541c0115109548362108f93470,0x541e1e1105205d01c⟩,by decide +kernel⟩,
  ⟨⟨2,0x3786c10005e46829082f83a09bc20d543621808e136701d0c83746e10070049c1a228ab436217088d63470,0x5c34787204700c81c⟩,by decide +kernel⟩,
  ⟨⟨2,0x642180c18e0aa906420ff26ce02b231081986c1600114516d044cc543621088e23670,0x840ee004⟩,by decide +kernel⟩,
  ⟨⟨2,0x2e09046148a441b60f0021292d50d8860238559c0703b0811b8432a081d109548362108f93670,0x186c0e150e5014⟩,by decide +kernel⟩,
  ⟨⟨2,0x18600de4b29084ca86c50211caace02bc2910df80a08844c8543621088e25670,0x4e802⟩,by decide +kernel⟩,
  ⟨⟨2,0x2043840fc1d07001942a1908438fea380081f83a0e00586548321071dd470,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xa04c1e02822832a190c03f0eb3803f841ac1e00486548321073dd470,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x18058003d045e654328107e5d670030081383c05045e754321087e2d670,0x1⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_8_40 : List Batch_0_0_8 := [
  ⟨⟨2,0x611b8541840c8ca86c42111c5ace031121188a4420f0b078009c206ec543621808e1d670,0xa8d1603a014⟩,by decide +kernel⟩,
  ⟨⟨2,0x18228232229b108438fca380908dc2a0c20646543628108e5d670,0x35802⟩,by decide +kernel⟩,
  ⟨⟨2,0x145028998627c0884ea865020fd98a280304504644583621073d9470,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x2418241d9150e1c41f2714538045120306054327108716c514,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x2418c2120bcaa86e210f958a280906090764543827108c9c514,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x2484c0120bc1981172150dc421f4b24528a0c616045e554310877cac614,0x4f802⟩,by decide +kernel⟩,
  ⟨⟨2,0x1208a2b145f810650a8c2e52a1b9084469648a1198142c0c30766543781068f0c914,0x4f802⟩,by decide +kernel⟩,
  ⟨⟨2,0x18a2f0650b022e32a18843be9650a300918186508766543821068f0c914,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x11450321a19408338e9a0a018041ac08505c654328107e5d214,0x50802⟩,by decide +kernel⟩,
  ⟨⟨2,0xb005183022190843beb630b031870413e0442654328107ecc516,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x8c4212890645543281068e5d2160300b022c1286828754328107e5d216,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x305c2c1a1908433f11b0b0bf842e048307064321866e23616,0x1⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_8_41 : List Batch_0_0_8 := [
  ⟨⟨2,0xe030f0305141550c9e0423b064d1870513e0442554328107ec1934,0x84081d007c14⟩,by decide +kernel⟩,
  ⟨⟨2,0x82e04422622a194083f70d9a04386c0c0c14506543278108f01934,0x10830f600c⟩,by decide +kernel⟩,
  ⟨⟨2,0x300a0b810b850ca864300fc3a4680810f0b8105c0d0c2e854321807e1ce34,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x6887022722a190c03f6609b0180505c086428654321087e2d234,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x10924110804a8388cea864210d03d926c27c08844c454321087eec236,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x1281810a0a0aa865020e3ba46c2d160961248a141c468543821068f0c936,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x68b0242722a190c03f660ab0180419c08505a6543210871fd236,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x27090986a864210fdd84ac0b1684856454328107e5c256,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x50260b02170a1950e0841c7749581000a1848585543821071dce56,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x200405e04281132a1c10839ee92b0400982c0864286543210871fd256,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x18042dc1e045e654328107e51b74241188044e14243c75436210883e1974,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x94904621100481e3aa1b14084728dba0085f83c0b185c6543821078e91b74,0x1⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_8_42 : List Batch_0_0_8 := [
  ⟨⟨2,0x25241188942200ac481e4aa1b108441f2cba0200e000300a8a1ac1e045ca543210871c3974,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x200c02c0e0e802f3aa190843f1693a0140983c0d0050654321807e1d274,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xd1660700212aa1c1083be0cca0180581c1d005e654328107e5d274,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x8c44e14503a55463210883e199410b1987c2c0e005875743821087c1994,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x42fc0e018c2632a1c1083c748dca018042f0860456654328107e51b94,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0xe06015143580c08990a864210e38732981c00844c454382107ee1b94,0x54802⟩,by decide +kernel⟩,
  ⟨⟨2,0x4b1004918894216c503a95463210883e59940c8368a1ac0e00427543821077c3994,0x1⟩,by decide +kernel⟩]
private noncomputable def ch_0_0_8 : List Batch_0_0_8 := (((((ch_0_0_8_0 ++ ch_0_0_8_1) ++ (ch_0_0_8_2 ++ (ch_0_0_8_3 ++ ch_0_0_8_4))) ++ ((ch_0_0_8_5 ++ ch_0_0_8_6) ++ (ch_0_0_8_7 ++ (ch_0_0_8_8 ++ ch_0_0_8_9)))) ++ (((ch_0_0_8_10 ++ ch_0_0_8_11) ++ (ch_0_0_8_12 ++ (ch_0_0_8_13 ++ ch_0_0_8_14))) ++ ((ch_0_0_8_15 ++ (ch_0_0_8_16 ++ ch_0_0_8_17)) ++ (ch_0_0_8_18 ++ (ch_0_0_8_19 ++ ch_0_0_8_20))))) ++ ((((ch_0_0_8_21 ++ ch_0_0_8_22) ++ (ch_0_0_8_23 ++ (ch_0_0_8_24 ++ ch_0_0_8_25))) ++ ((ch_0_0_8_26 ++ (ch_0_0_8_27 ++ ch_0_0_8_28)) ++ (ch_0_0_8_29 ++ (ch_0_0_8_30 ++ ch_0_0_8_31)))) ++ (((ch_0_0_8_32 ++ ch_0_0_8_33) ++ (ch_0_0_8_34 ++ (ch_0_0_8_35 ++ ch_0_0_8_36))) ++ ((ch_0_0_8_37 ++ (ch_0_0_8_38 ++ ch_0_0_8_39)) ++ (ch_0_0_8_40 ++ (ch_0_0_8_41 ++ ch_0_0_8_42))))))
private noncomputable def lv_0_0_8 : List NodeSpec := flattenBatches fmt_0_0_8 (ch_0_0_8.map Subtype.val)
private theorem ok_0_0_8 : LevelOK rd_0_0 (subGoal 0 0) 8 lv_0_0_8 :=
  @checkedBatches (freeVars 0 0) rd_0_0 _ _ _ sl_0_0 [[]] 8 fmt_0_0_7 (ch_0_0_7.map Subtype.val) fmt_0_0_8 pp_0_0 (raw_faithful (freeMask 0 0) p_0_0 q_0_0) sl_0_0_ok (by decide +kernel) ok_0_0_7 ch_0_0_8

private def fmt_0_0_9 : ChartFormat := ⟨6, 2, 0, 5, 6⟩
private abbrev Batch_0_0_9 := CheckedBatch (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] 9 fmt_0_0_8 (ch_0_0_8.map Subtype.val) fmt_0_0_9
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_9_0 : List Batch_0_0_9 := [
  ⟨⟨2,0x18783800c0a5b1f21b24102c24b020181004001f08d814c5b634477c204,0xfffe10⟩,by decide +kernel⟩,
  ⟨⟨2,0x2160e06001808b8982895563446f0160842200d0703018685805870bb1f44680904,0x1ff0838⟩,by decide +kernel⟩,
  ⟨⟨2,0x4c12100c066a438583800a1acb1a23be7020586e160e0029ac4476ce04,0x3fffea04290⟩,by decide +kernel⟩,
  ⟨⟨2,0x52100e0a0600c0d9163446f01c090c8c85030007050a5c1a4abb1a23e80c04,0x7b141c34b8⟩,by decide +kernel⟩,
  ⟨⟨2,0xb40c2c1140535688eda4083028210300604c0c8509808670db1a23784e04,0x1fd6268604378⟩,by decide +kernel⟩,
  ⟨⟨2,0x432341c084412112c2a0132ec688fa040102c2418070900c414513634477d204,0x1cc143831c⟩,by decide +kernel⟩,
  ⟨⟨2,0x84220e04c0b8541a130d00e1963446f0a408110502010662607b1a23781204,0xe70e5614228⟩,by decide +kernel⟩,
  ⟨⟨2,0x4109c3c2c00534688edac085849170c8d0411028184630a8620eb1f44687004,0x7fa4616de354518b0⟩,by decide +kernel⟩,
  ⟨⟨2,0xb4341c00584c1211742a09332c688fa05010d8201800e30f0904c414257634477d604,0x2920a0d0914⟩,by decide +kernel⟩,
  ⟨⟨2,0x2e120991c42189ec686ee6c08130d0701090482626a9b1a23781604,0x1d24141a1ca18⟩,by decide +kernel⟩,
  ⟨⟨2,0x2618120c04020820c4d5567688d1280870290c0807840301041380486cdb1f44687404,0x290b0c587408⟩,by decide +kernel⟩,
  ⟨⟨2,0xee04c4a0c8b63588f0160a42200a09028d8781828458bb1f58880905,0x3ff32048⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_9_1 : List Batch_0_0_9 := [
  ⟨⟨2,0x2191a12070b050ced163588f0180a140d02845a56607b1f58882905,0x3f5e008⟩,by decide +kernel⟩,
  ⟨⟨2,0x2191a04d40f0b04bc34b5563588f05c0a280b820703801a50649b1ac4780e05,0x7eec098⟩,by decide +kernel⟩,
  ⟨⟨2,0xc0a08409442a1a160e042192336c6b11e138142420180c8707021708c8357635c87cc05,0x7fc46e02d8⟩,by decide +kernel⟩,
  ⟨⟨2,0x201204170f0500a0ed363588f0240b0c8c8503858280648b1ac4781005,0x7f8896038⟩,by decide +kernel⟩,
  ⟨⟨2,0x48342e160a01d8a22c6b90fa00a170c8c09021185825e8056bb1ac4783205,0xfa6036008⟩,by decide +kernel⟩,
  ⟨⟨2,0x5e1918141204ed0022170b050cc841f63eb110e00a43022a510b87828108768cbb1ac4785205,0x1ffda1102604830⟩,by decide +kernel⟩,
  ⟨⟨2,0x402410170f00a104b1363588f02c0a130c8d04847682648b1ac4781405,0x1b0c1c2781c⟩,by decide +kernel⟩,
  ⟨⟨2,0x41090485c2c0073c6b90da80a2d0c8c080f845a56825eab1ac4783605,0x7f29466a518422a1302870⟩,by decide +kernel⟩,
  ⟨⟨2,0x1790890804a31461e02120c205b6c6b11e1581420180c130b0104d4253635c87d405,0x2a342262d1c6915108050⟩,by decide +kernel⟩,
  ⟨⟨2,0xbc5e1918141100c4b426170f090441f676b111280a290c2e20128c0a868385806449086cfb1f58887405,0x1e5070609cd14a058⟩,by decide +kernel⟩,
  ⟨⟨2,0x1083028261e0210b9c26c7d11a024182cb3041308d814c516343770706,0x1fcbc018⟩,by decide +kernel⟩,
  ⟨⟨2,0x2108484030002e1609aa19db2c68f0f9c0c146250644b1a23780b06,0x4fc06⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_9_2 : List Batch_0_0_9 := [
  ⟨⟨2,0xd4170413010ca0c9163447d01c0c1a8c850a6b8286768b1a23e80c06,0xfc02⟩,by decide +kernel⟩,
  ⟨⟨2,0x5848317a06160828a26c68f0fa40c30280d088464510b808670bb1a23784e06,0x58c2f00c⟩,by decide +kernel⟩,
  ⟨⟨2,0x20170c130500a0ed163447d0240c49168c850b858280649b1a23e81006,0x347004⟩,by decide +kernel⟩,
  ⟨⟨2,0xee1a105d2118210f0b04d4c90215d63e88d0e00c422a0d0876500b868070ab1a23785206,0x7fa264c4058⟩,by decide +kernel⟩,
  ⟨⟨2,0x5c2a11d92191ac688fa05018ec20180ce1070b0014c8257634787d606,0x6703500c⟩,by decide +kernel⟩,
  ⟨⟨2,0xd85c50261a10c814e30b010c91b63e88d0e80c120a098082506a7b1a23e81606,0x1dc64501c⟩,by decide +kernel⟩,
  ⟨⟨2,0xd88707011b0cc508b1363e88d1920e625e2e110d08700b84806abb3b44689406,0x3fda4028⟩,by decide +kernel⟩,
  ⟨⟨2,0xd8842a011b070cc508b1563e88d0120e0c144c845a4a6b1a2378cb07,0xfdec008⟩,by decide +kernel⟩,
  ⟨⟨2,0x281810b508acc0f63e88d0520e0d0a08145c4c844a8b1a23780b07,0x1⟩,by decide +kernel⟩,
  ⟨⟨2,0x10a306e12196929ec688de3301c682420180402148437090cc59634477cc07,0x389004⟩,by decide +kernel⟩,
  ⟨⟨2,0x2198959812c6b91a3381cac24201810870b070098b10d9635c87ce07,0x1e8900c⟩,by decide +kernel⟩,
  ⟨⟨2,0x340cc4c8c0b63447d01c0e570c8c081b850a5c864aab1a23e80c07,0xa2c06⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_9_3 : List Batch_0_0_9 := [
  ⟨⟨2,0x1e146050ad0b0613010cc09919b63446f09c0e4d0c8c581a0a086b8384865acb1a23e82e07,0x3f5180bc028⟩,by decide +kernel⟩,
  ⟨⟨2,0x42361210d132012a2c688de3401c24080500186a170894515634477d007,0x1f3871bc018⟩,by decide +kernel⟩,
  ⟨⟨2,0x420189812c6b91a3481c2418b8b70b0500b0513635c87d207,0x2bc02⟩,by decide +kernel⟩,
  ⟨⟨2,0x2000c4c0963447d0240e110c8d0808845b850a4c804acb1a23e81007,0xeab004⟩,by decide +kernel⟩,
  ⟨⟨2,0x2148454bb0e130500c0b519763446f0a40e16110c8c085c0a5983848056cb1a23e83207,0x3fe9c80c4048⟩,by decide +kernel⟩,
  ⟨⟨2,0x4840100030d42e1209703aec688efa80e5a4c0f0c8d02110858809087850a56630b1f44687007,0xffff64419e020330110⟩,by decide +kernel⟩,
  ⟨⟨2,0x1a84030112a0e0039804aac6b90fac0e0e8d8484824c5a7b1a2378d407,0x1ea1c32c1c1d4038⟩,by decide +kernel⟩,
  ⟨⟨2,0x26191a081108b89904bd563447d0280e0e088262605b1ae468d607,0x64eb00c⟩,by decide +kernel⟩,
  ⟨⟨2,0x61e160209602929ec6b8ce680e120a088262606b1a23e81607,0x3c921c14274028⟩,by decide +kernel⟩,
  ⟨⟨2,0x3c323161282610296a095aec688fa0d81cb414130904c8c4f6343e73607,0xf11821c142c71dc048⟩,by decide +kernel⟩,
  ⟨⟨2,0x52191a1024ae170b00d9563e88d0e80e8c42250987808482604a16bb1a23785607,0x3ac2e1c129c028⟩,by decide +kernel⟩,
  ⟨⟨2,0x484618260e017964126c688ee74130c8d08105b0b8784629b3b44689407,0x3ffda1ba1c930050⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_9_4 : List Batch_0_0_9 := [
  ⟨⟨2,0x180f0608b0f4d63c88f01c120d0a043182585e7a8b1e44780c09,0x7c5201c⟩,by decide +kernel⟩,
  ⟨⟨2,0xd50c16081b04bcb0f5363c88f05c1206040c0a587a707b1e47882c09,0x7e8a098018⟩,by decide +kernel⟩,
  ⟨⟨2,0x42908aa1a097c116201b432ec7911e04024341824201403049e090d563e887cc09,0x3ffff21341702280f81a80a190⟩,by decide +kernel⟩,
  ⟨⟨2,0x84201b0e0814b100e1363c8f106012107b0d87828104588b1e44781209,0x1f8ac03601c⟩,by decide +kernel⟩,
  ⟨⟨2,0x4828860a0030a1ec7d10fa012100a7b058782585e810cab1e44783209,0x7ff8c1a07c08603b0070⟩,by decide +kernel⟩,
  ⟨⟨2,0x13214844900be0b0cb0b90619963c88f028122f0a8a100c8705828042ab1fc8887009,0x7ffc943111681d022810819816170⟩,by decide +kernel⟩,
  ⟨⟨2,0x8424160b0f010618b1363c8f10681242130d87810482588b1e44781609,0x1fc88bc2f0108058⟩,by decide +kernel⟩,
  ⟨⟨2,0x4030281e0209ac104a6c7d10fa8121e0e0a825e0c5905878070bb1e44783609,0x6a2619a88404330e81e10118070⟩,by decide +kernel⟩,
  ⟨⟨2,0x26145c210d00e208f50550c619b677911128126c2f0a0612700d04827aab1fc8887409,0xfb84828d885fc0528010⟩,by decide +kernel⟩,
  ⟨⟨2,0xa09080605c1c0823243305d8fa21f382c24200818a1170f0700bc297635c87c50b,0x7f5e8018⟩,by decide +kernel⟩,
  ⟨⟨2,0x60bcb0a0c49884f63447d01c160c065f044a425c7b1a23e80c0b,0x63802⟩,by decide +kernel⟩,
  ⟨⟨2,0xd4280c1b0484ecf63447d05c16280d000a70646b1a3c682c0b,0x699200c⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_9_5 : List Batch_0_0_9 := [
  ⟨⟨2,0x4031792c120131ec688fa0402c241608ef0500c051163e887d20b,0x69802⟩,by decide +kernel⟩,
  ⟨⟨2,0x84190c1500e0c0f63478d060162a585e50625b1a23e8120b,0x6a802⟩,by decide +kernel⟩,
  ⟨⟨2,0xa02215150e041a0900c8c485963e88d0e0161182810c645b1a23e8320b,0xffc85f8048⟩,by decide +kernel⟩,
  ⟨⟨2,0x48317134120979ec688fa0502c20140ca0950700d60825563e887d60b,0x1231b200c⟩,by decide +kernel⟩,
  ⟨⟨2,0x84170f021904c0f63478d068162482585e50626b1a23e8160b,0x3b1ca014⟩,by decide +kernel⟩,
  ⟨⟨2,0xe0c85026141b003cd9363e88d0e8160c76821270646b1a23e8360b,0xdc182004⟩,by decide +kernel⟩,
  ⟨⟨2,0x484018100801783429b188532c688ee30521e110a7671870c628b3b4468940b,0x663c118601c⟩,by decide +kernel⟩,
  ⟨⟨2,0x50281816083109da2c7911e030a4242214130f07005cbe0956344771a29,0x1ff808038⟩,by decide +kernel⟩,
  ⟨⟨2,0xd4180f0608b484bd163c88f05c52640c7a604b1e44780e29,0x6a20200c⟩,by decide +kernel⟩,
  ⟨⟨2,0x10460a043191ac7911e040a4342824201b070208c90cc1763e887cc29,0x1e89c808018⟩,by decide +kernel⟩,
  ⟨⟨2,0x201b04ae0900bcf63c88f064527a11860d8276607b1e44781229,0xe4a004⟩,by decide +kernel⟩,
  ⟨⟨2,0x1804428302a1c160992010aec7f2221c0a42608ef0500c050f63e887d029,0x7f3867f8038⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_9_6 : List Batch_0_0_9 := [
  ⟨⟨2,0x84270f021904c0f63c88f02c52041276830c646b1e44781429,0x1926600c⟩,by decide +kernel⟩,
  ⟨⟨2,0x1a8420e003c11804a2c7d10fa8520e0c5a5704825e7b1e44783629,0x3a5308898008⟩,by decide +kernel⟩,
  ⟨⟨2,0x2100c10e08f4c6150550ee199677911128526c12600d0464827a8b1fc8887429,0x3e6851838008⟩,by decide +kernel⟩,
  ⟨⟨2,0x908030100360582314d8d11df08ac2420185f0f070014293634787c12b,0x1ffa68038⟩,by decide +kernel⟩,
  ⟨⟨2,0xca19ae0c29e9ac688fa030ac34282420010f04149e08d5763e887ce2b,0xffdca68048⟩,by decide +kernel⟩,
  ⟨⟨2,0x4a06082c10a1ac7d10fa4564814060b82587a7b1a23e80e2b,0xf88b18008⟩,by decide +kernel⟩,
  ⟨⟨2,0x920823070d0218f4b1363447d02456105e4886810459827b0aa90ccb1a23e8102b,0x1fc8a8a88038⟩,by decide +kernel⟩,
  ⟨⟨2,0x40320e1e002c104a2c7d10fac565810866b82810a428b1f4468702b,0xffbc44652a60010⟩,by decide +kernel⟩,
  ⟨⟨2,0x250700b218d4d63447d02c565812045e83810c6a8b1a23e8142b,0xfe270aa8008⟩,by decide +kernel⟩,
  ⟨⟨2,0xc4b02404210218d5167688d128566c580612830a7a7b1f4468742b,0xf9031ab8008⟩,by decide +kernel⟩,
  ⟨⟨2,0x4840301a2e061609d86aac6b90f8a181a8482808a264a428b1a2378c40c,0x3ffd09418c0df0048210⟩,by decide +kernel⟩,
  ⟨⟨2,0x9088352f0b05160ced363446f18c18084385821a766b1ae468c50c,0x3d366014⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_9_7 : List Batch_0_0_9 := [
  ⟨⟨2,0x881917060d08bc94f5363e88d192188a1a264a425b1a2378c70c,0xf86200a2c008⟩,by decide +kernel⟩,
  ⟨⟨2,0x136117908196189ec446ef9c18300d065e84264a7b1a2378cb0c,0xd8da01e808b014⟩,by decide +kernel⟩,
  ⟨⟨2,0x4212097a012909ec688de340302408181004bc8708960c217634477d00c,0x3ffe88048⟩,by decide +kernel⟩,
  ⟨⟨2,0x4201d9e9896c688de3483024181404f4ef0900c60c217634477d20c,0x7639a00c⟩,by decide +kernel⟩,
  ⟨⟨2,0x2180e08c450ecd63446f024190c8c070484004a285e9b1a23e8100c,0xd8e39a014⟩,by decide +kernel⟩,
  ⟨⟨2,0x21800f70b0450bcf63446f0641848970d85828b06768b1a3c68300c,0x3ff98008⟩,by decide +kernel⟩,
  ⟨⟨2,0x981e11d90a0189ece88cee0190a8b022a766228428b1a2378520c,0x7fea2f0e229008d0030⟩,by decide +kernel⟩,
  ⟨⟨2,0x4a12009a097909ec688de35030902008181000bc3f08ba0c259634477d40c,0x7fc130038⟩,by decide +kernel⟩,
  ⟨⟨2,0x1204a297a090e14198a6c688de3583020181400930904c60c255634477d60c,0x30d90cc40ce03b806a018⟩,by decide +kernel⟩,
  ⟨⟨2,0x3219191504d4bf0a0cc5563446f02c190c8c070484825c185e9b1a23e8140c,0xd58372004⟩,by decide +kernel⟩,
  ⟨⟨2,0x26191b09041cecf63446f06c185e288d0d0059848306628abb1a3c68340c,0xff8de0408e48048⟩,by decide +kernel⟩,
  ⟨⟨2,0xee18d70850c4d67688d128185e8a4a25069612827a9b1a2378560c,0xce0a83010076008⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_9_8 : List Batch_0_0_9 := [
  ⟨⟨2,0x4840313026160e00d1641aec6b90f8a1c1a4e42644b1a2378c40e,0xfbfc00fc008⟩,by decide +kernel⟩,
  ⟨⟨2,0x50100d0084370b00b0d9563447d18c1c420a08078580586c8b1ae468c50e,0x1d16600aa02e1c⟩,by decide +kernel⟩,
  ⟨⟨2,0x1908c0d8963e88d1921c0a1a824e42646b1a2378c70e,0x1e4c01e80c⟩,by decide +kernel⟩,
  ⟨⟨2,0x616081939082961922c446ee5c1c300d82844e586b1a2378cb0e,0x7fb21b004a02a80b878⟩,by decide +kernel⟩,
  ⟨⟨2,0x60a0108a1616c688de340382418141100870b04b20c217634477d00e,0xfc84c0e68028⟩,by decide +kernel⟩,
  ⟨⟨2,0x10846160a013991ec68f1a34838d824181500f70b060cc8217634787d20e,0x5413039e00c⟩,by decide +kernel⟩,
  ⟨⟨2,0xf0400a050b0d63447d0241c110c8d04846c80648b1a23e8100e,0xec1bc014⟩,by decide +kernel⟩,
  ⟨⟨2,0x21800f70b0450c8f63446f0641c48970c8c0b8582810658ab1a3c68300e,0x1fc810018⟩,by decide +kernel⟩,
  ⟨⟨2,0x1b060403028207e160164184b2c688efa81d0a642a0d07826080429b1a2378520e,0x7a200fc01c⟩,by decide +kernel⟩,
  ⟨⟨2,0x403029220e160419904aac68f0fac1c184e8242585b1a2378d40e,0x39c1340062014⟩,by decide +kernel⟩,
  ⟨⟨2,0x5219190b0b0104c9163447d0281c281243858082647b1a3c68d60e,0x483061815c01c⟩,by decide +kernel⟩,
  ⟨⟨2,0x502700160d04c0f63478d0681c12065082586c6b1a23e8160e,0x190617010401c⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_9_9 : List Batch_0_0_9 := [
  ⟨⟨2,0x214c8481a0cc104f5163446f0ac1c290c8c0a0f858082649b1a2378360e,0x44340e110c01c⟩,by decide +kernel⟩,
  ⟨⟨2,0x5848403011960e0140286aec6b90e3258642e8b08070c63847a6a6c28cb3b4468940e,0x78e0f1850086018⟩,by decide +kernel⟩,
  ⟨⟨2,0x1245a3612160c28a1926c68e1e040b02cb024201804030a0c14c576344771b2c,0x32d4004⟩,by decide +kernel⟩,
  ⟨⟨2,0x483201ee16082c199042ac688efa45849170c8c0a0185822858ab1a3878122c,0xf2ec014⟩,by decide +kernel⟩,
  ⟨⟨2,0xe0501f082d0b021504c9563470f0285864582a0c0b0680708b1a3878522c,0x422c4004⟩,by decide +kernel⟩,
  ⟨⟨2,0x48403606119209c03a6c688efac58280b80130682607b1a3878162c,0xd62f4014⟩,by decide +kernel⟩,
  ⟨⟨2,0xd7043484bc9cd63446f1805c6462590c7184830a289b3b4708942c,0x3b1230091014⟩,by decide +kernel⟩,
  ⟨⟨2,0x281869d9a96c68f1a304b82420180b001304be0ca0d57634787c12e,0x16e0164004⟩,by decide +kernel⟩,
  ⟨⟨2,0x2302820186a11d9aa2c688fa308b824200c080400bc181308d4c435b634477c22e,0xf9044600370088⟩,by decide +kernel⟩,
  ⟨⟨2,0x501908ec84d4d63e88d1925c6b821a82425e4e7b1a2378c32e,0x1c17004303c⟩,by decide +kernel⟩,
  ⟨⟨2,0x48342820090e16097c1842ec688efa05c6a300d82844e5e7b1a2378cb2e,0x1f9a022e01c⟩,by decide +kernel⟩,
  ⟨⟨2,0x1e84836120609dc19a842ac6b90fa45c6a118282805e427b1a2378d02e,0x1f3b401c⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_9_10 : List Batch_0_0_9 := [
  ⟨⟨2,0xd6180d08f70b0450bd363447d0205c100a4384804e6a7b1ae468d22e,0xfcf90008⟩,by decide +kernel⟩,
  ⟨⟨2,0x219180cd708030450bd363447d0645c7b0c07858228767b1a23e8122e,0x3e411005f0008⟩,by decide +kernel⟩,
  ⟨⟨2,0x6101e0c290a01d9ece88cee05c6a2a0d0b07828076429b1a2378522e,0x3ff4c60c3d40d3008d0090⟩,by decide +kernel⟩,
  ⟨⟨2,0x390a0979396c688de350b8201810003f0904ec1d3634477d42e,0x749c00c⟩,by decide +kernel⟩,
  ⟨⟨2,0xa03e010e11da094a2c6b91a358b8201906170b020c251635c87d62e,0x622896302172f025802405405204f0238070⟩,by decide +kernel⟩,
  ⟨⟨2,0xbc9452191908250700c0d5763447d02c5c8c060284126a767b1a23e8142e,0xfa8a2c0eb0028⟩,by decide +kernel⟩,
  ⟨⟨2,0xbd044824d4f4d63446f0ac5d0c8c0784825a0e5e8b1a23e8362e,0xa12d006⟩,by decide +kernel⟩,
  ⟨⟨2,0x48403028260e0160c26c68f0f829c625f0d087b84286a8b3b4468942e,0x1ffc4100650038⟩,by decide +kernel⟩,
  ⟨⟨2,0x90845040006c13b184d8d721f1538242010040018ecc4613634477c24e,0xf54c014⟩,by decide +kernel⟩,
  ⟨⟨2,0x1b0c42a2a0416099430a2ac688fa04138241443060e0820f63e887d24e,0x7fea36600a810c078⟩,by decide +kernel⟩,
  ⟨⟨2,0xecb0601a08160d00e1363478d0609c308a77048182610c289b1a23e8124e,0xfd730008⟩,by decide +kernel⟩,
  ⟨⟨2,0x405e041c1049ac7d10fac9c308105828a650c288b1a23e8324e,0xff420c366011c0a6068⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_9_11 : List Batch_0_0_9 := [
  ⟨⟨2,0x110605031160b020d04c0da19963447d02c9c30288a6b058064830c18ab1a23e8144e,0x7208516514d0038⟩,by decide +kernel⟩,
  ⟨⟨2,0x60c81a0b001ce0f63447d06c9c302904618106830c8a9b1a3c68344e,0x3a90c24c6d880674068⟩,by decide +kernel⟩,
  ⟨⟨2,0x4840322e1e160c01926c6b90f8a2062308b046a830c288b3b4468944e,0x1ffd404315028c01880c920560bc0b0⟩,by decide +kernel⟩,
  ⟨⟨2,0x90892d170b0450bd163446f18c208c098582285e6b1ae468c510,0x1fe80280294038⟩,by decide +kernel⟩,
  ⟨⟨2,0x1828c85005e4a287b1f233e48861e0834012c7c86c910,0xff546e00e0f80f007a01482d05a0c4090⟩,by decide +kernel⟩,
  ⟨⟨2,0x360c01792a10a1ec646ef9420448b83005e844a8c289b1f4468c910,0x7a865b70018⟩,by decide +kernel⟩,
  ⟨⟨2,0xc2c1002f2c1435688ddf4840d824181600870b04c8515634477ce10,0x720a4043603c601c⟩,by decide +kernel⟩,
  ⟨⟨2,0x3c2060402412f24800c558d11df50400308d90cc820d5f44677010,0x7fd829005405a025012e8078⟩,by decide +kernel⟩,
  ⟨⟨2,0x1223228097e10a12a2c688de3584018140cd90708d600253634477d610,0x1e33670683a404e08204180be058⟩,by decide +kernel⟩,
  ⟨⟨2,0x21919160904b0bf0a00d9563446f02c2012110c8d04845f00824cab1a23e81410,0x330c86b4014⟩,by decide +kernel⟩,
  ⟨⟨2,0x2219190a08260104c9363446f06c205f28108d050c59878483004a8adb1a3c683410,0x7a827625904c80ec8078⟩,by decide +kernel⟩,
  ⟨⟨2,0xbc251a151608f70850d9563e88d0e8205e8a25067a849683006c8cbb1a23785610,0x1f411c72902c010c0ca058⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_9_12 : List Batch_0_0_9 := [
  ⟨⟨2,0x28004181896c6b91a314482418b81c130b04b0ae015635c87c512,0x3ce81581090008⟩,by decide +kernel⟩,
  ⟨⟨2,0x8b850c0963e88d192248c0884008a28627b1a23e8c612,0x219002⟩,by decide +kernel⟩,
  ⟨⟨2,0xc2c100052f2c143d688ddcc84824181404ec860308c4515634477ce12,0x313006c01bc014⟩,by decide +kernel⟩,
  ⟨⟨2,0x60503c24135803b094d8d1e1f58481814100904c050f634477d412,0x6ac0f2006c00ca01c⟩,by decide +kernel⟩,
  ⟨⟨2,0x219190b0f0904ecf63447d028248c848228765b1a3c68d612,0x35e008801a4014⟩,by decide +kernel⟩,
  ⟨⟨2,0x24230c150600c0f63478d06824121000508258627b1a23e81612,0x130c84400c⟩,by decide +kernel⟩,
  ⟨⟨2,0xee11084a14f70d0600c0c519963446f0ac24110c8c0a0f878482769b1a23783612,0xcc3310a4022006b0028⟩,by decide +kernel⟩,
  ⟨⟨2,0x584830161e08294401daac6b90e3260130a2e8c8b007683847a6c28cb1f44687412,0x7840d81ec09c80420d6038⟩,by decide +kernel⟩,
  ⟨⟨2,0x9063521c2c10514458d11df38c02cb024180c07081600d956344771b30,0x2181ec08f03ea014⟩,by decide +kernel⟩,
  ⟨⟨2,0x15042600d4c0d63470f02c60128416766a5b1a38781430,0x643006⟩,by decide +kernel⟩,
  ⟨⟨2,0x1d9b1604c3029c6121c0122ec7d1c21d0c01b0d0708e200ec251634477d630,0x725c8021c01c⟩,by decide +kernel⟩,
  ⟨⟨2,0x230061608a179ac68f1a304c824180a14130f04bca2015634787c132,0x7f3c0ee03a4028c038⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_9_13 : List Batch_0_0_9 := [
  ⟨⟨2,0x23020061608a179ec688fa308c8102420180c04be170a00d97634477c232,0xfe080d8116023c04301e802c08c010⟩,by decide +kernel⟩,
  ⟨⟨2,0x4830010c2e160990a26c68f0f9c650a8501825e8c287b1f4468c932,0x790433809404c0fc8038⟩,by decide +kernel⟩,
  ⟨⟨2,0x68504c2412f8007458d11df50c8030b06150cc820f5f44677032,0x3ee154009808901388048⟩,by decide +kernel⟩,
  ⟨⟨2,0x4299a4a3406120978a26c6b91a358c8180d0708d60024f635c87d632,0x76309cd103d80440ae01a09417e0490378070⟩,by decide +kernel⟩,
  ⟨⟨2,0x24221918160d0a00bd0650c4c1b63447d02c650c8d041284108300649b1a23e81432,0x788ca45100f80e808f0058⟩,by decide +kernel⟩,
  ⟨⟨2,0xbd1a104a0e010a5104f42d763446f0ac64100f0c8d845683005e9b1a23e83632,0x1c8304232603c8029c038⟩,by decide +kernel⟩,
  ⟨⟨2,0x483028261e0960aa2c68f0f82a413006c8c0a7b8482644828bb1f44687432,0xfc9021800600f00010048⟩,by decide +kernel⟩,
  ⟨⟨2,0x906450403c13215458d721f15482418100c04d8c8551634477c252,0xfea90008⟩,by decide +kernel⟩,
  ⟨⟨2,0x50335828009358fa21f594b0450547635c87ce52,0x7f13800f009201b40982040e4030⟩,by decide +kernel⟩,
  ⟨⟨2,0x1108455170e0104c0c619563447d02ca4990b0442702b870082770cbb1a23e81452,0xff284478002036402f4068⟩,by decide +kernel⟩,
  ⟨⟨2,0x3d1104ec541b0e00e1363447d06ca4422a10618683010c8a9b1a3c683452,0xd08f080f0022011402af4068⟩,by decide +kernel⟩,
  ⟨⟨2,0x984840302820160c1c0182eced10e32e06d0a2a0c708683001e9b1f44687452,0x1f8c39102604f007200d82081140010030⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_9_14 : List Batch_0_0_9 := [
  ⟨⟨2,0x48403020097e14192c02ac688ee36e0588a2621018384430610ab3bc8881970,0x1ffff9a012400605e0320b701760530170⟩,by decide +kernel⟩,
  ⟨⟨2,0x4840322826160c197c02aced10e72e07620188b0683018462426410cb1e44781b70,0x7ff181fc01f07208c09407a07902600300f0⟩,by decide +kernel⟩,
  ⟨⟨2,0xb08842008708d7060c2115763c88f076e00e76208b838500426410ab3bc8883970,0xffe40432c06a17401e80720570090⟩,by decide +kernel⟩,
  ⟨⟨2,0x211915080218d4ca230904ec31b63c88f028e0448a210685018210429b3bc8885970,0x3ffee1c58d43a806d807a0760590110⟩,by decide +kernel⟩,
  ⟨⟨2,0x2518b0221a230a0e010515763c8f1068e0886c2e18130c8c8b1011078483006a630b1e44781670,0x1ffe2323491999dc04c09205c2f81504e01e04c176051001c0160⟩,by decide +kernel⟩,
  ⟨⟨2,0x1144a0d2c26010485163c88f0ace0108c0a010c648b118482760ecb1e44783670,0x3f112394a5408518c04c08101ae01d819a00b0018150⟩,by decide +kernel⟩,
  ⟨⟨2,0x6052441c2838009458d11df59c0901814403f0a0d0421363e887d470,0x7c41002203c0ec0cf003c058⟩,by decide +kernel⟩,
  ⟨⟨2,0x86120c19a841af7910f28e020180e668b07018482426a10cb1e4478d670,0xfd149162c18da60226035c0440781c81e100d0⟩,by decide +kernel⟩,
  ⟨⟨2,0x6104a286121d9ac6b91a31450ec5810902019141f0b0204c99635c87c514,0x1e383f01c806c09b00660530064058⟩,by decide +kernel⟩,
  ⟨⟨2,0xbc3c006812d8f90d922984168a1812766b1a2378c614,0xf03d02504420806c0dc03500e55004c048⟩,by decide +kernel⟩,
  ⟨⟨2,0x584e01217a11740a3062ac7d11a324502c251b009108bcba0431563e467c914,0x7de4401c⟩,by decide +kernel⟩,
  ⟨⟨2,0x3508060521c2c032810c558d11df385090241b00bcb90a04313632377ca14,0x196b01c4042a00230008⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_9_15 : List Batch_0_0_9 := [
  ⟨⟨2,0x23006140861d9ac688de3485018170900ee0450f634477d214,0x52fe807f013e01c⟩,by decide +kernel⟩,
  ⟨⟨2,0x4012f2cc3c2c009454c68f19cd050905f080700bc243111a2377d614,0x9c0200604e4067403dc018⟩,by decide +kernel⟩,
  ⟨⟨2,0x2c084981896c6b91a31458201894130f0b0068b2055635c87c516,0x1700300ec02e04fc014⟩,by decide +kernel⟩,
  ⟨⟨2,0x1a0508c0c4b63e88d1922c086b021260626b1a23e8c616,0x3a9002⟩,by decide +kernel⟩,
  ⟨⟨2,0x4c0a1980f989ac688fa33858241c20181400860708d50cc59634477ce16,0x2280aa01381850015014⟩,by decide +kernel⟩,
  ⟨⟨2,0x23409804a01b1ac688fa3485840181500970a04511634477d216,0x40b004603e020806101c⟩,by decide +kernel⟩,
  ⟨⟨2,0x4080602c3c02805814d8d721c64d30c04170b00bcb02511a23773616,0xf612041c0d102907a819810401e04a02ca00700880d0⟩,by decide +kernel⟩,
  ⟨⟨2,0xc08061fc2c021058143558d11df38d020180f0b00b0149a0536344771b34,0x154185809c0684e0f703a80f401e0528078⟩,by decide +kernel⟩,
  ⟨⟨2,0x80602c3c028042f8138558d1e1f04d8190308160450d634477d234,0xd5030402d401a0548008⟩,by decide +kernel⟩,
  ⟨⟨2,0xb42970403021783e16013409c36c688ef846c120a020e5e706b1a3c68c136,0xc4504dc006a012130800a028⟩,by decide +kernel⟩,
  ⟨⟨2,0x2518ed081c8cd63e88d1926d0a0813020e76707b1a23e8c236,0x5c10040600c⟩,by decide +kernel⟩,
  ⟨⟨2,0x62d81c24038143d8d1e1f48d8201a14870b00ca041d3634787ce36,0x65c003800a06a00d401c⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_9_16 : List Batch_0_0_9 := [
  ⟨⟨2,0x402820361e0160922c68f0f82ac12005a0e705b1a3c68d236,0xe82d803c092005800dc01c⟩,by decide +kernel⟩,
  ⟨⟨2,0x3b320b12258d721f1558b8200cbf002c98491634477c256,0x16c1dcc00c⟩,by decide +kernel⟩,
  ⟨⟨2,0x100b8281142d8d721f495830201c2f010c48f635c87ce56,0x1cec04a05800600e5008c038⟩,by decide +kernel⟩,
  ⟨⟨2,0xa1207e160049b1ecef222065d0d824201814100b0204c03176768871974,0x1406428b0004c014⟩,by decide +kernel⟩,
  ⟨⟨2,0xa0620191207e104988f2ac7911e06dd024201810030a0e04ed36344771b74,0xc1404d403a80940068008⟩,by decide +kernel⟩,
  ⟨⟨2,0x784e103e0121b1ecef2220e5d090201c1810030a0e04ed56768873974,0x4800a4009c05200202501c⟩,by decide +kernel⟩,
  ⟨⟨2,0x191508f4d8b6779110b2e8281f8580128a6c7b1e44783b74,0x2f40129006⟩,by decide +kernel⟩,
  ⟨⟨2,0x407e120139b1ac7911e349d04018150308f604d8213634477d274,0x1d02006700c⟩,by decide +kernel⟩,
  ⟨⟨2,0x2312610a1896f99a2206650c4201814100b0e0600c157c68871994,0x180400f03203603280a48018⟩,by decide +kernel⟩,
  ⟨⟨2,0x1d882312610a189eccd11e06e502018100f0a0600c916344771b94,0x7581a4001019c013039809c0088038⟩,by decide +kernel⟩,
  ⟨⟨2,0x2920a1892f99a220e6509018101f0a0600c917c68873994,0x3783a403e046802901380180a4028⟩,by decide +kernel⟩,
  ⟨⟨2,0x1150850c497ccd110b3288c848a28625b3344783b94,0xfa0281006⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_9_17 : List Batch_0_0_9 := [
  ⟨⟨1,0xd41814c4870a045116344777b94,0xb81cc10f002d014⟩,by decide +kernel⟩]
private noncomputable def ch_0_0_9 : List Batch_0_0_9 := ((((ch_0_0_9_0 ++ ch_0_0_9_1) ++ (ch_0_0_9_2 ++ ch_0_0_9_3)) ++ ((ch_0_0_9_4 ++ ch_0_0_9_5) ++ (ch_0_0_9_6 ++ (ch_0_0_9_7 ++ ch_0_0_9_8)))) ++ (((ch_0_0_9_9 ++ ch_0_0_9_10) ++ (ch_0_0_9_11 ++ ch_0_0_9_12)) ++ ((ch_0_0_9_13 ++ ch_0_0_9_14) ++ (ch_0_0_9_15 ++ (ch_0_0_9_16 ++ ch_0_0_9_17)))))
private noncomputable def lv_0_0_9 : List NodeSpec := flattenBatches fmt_0_0_9 (ch_0_0_9.map Subtype.val)
private theorem ok_0_0_9 : LevelOK rd_0_0 (subGoal 0 0) 9 lv_0_0_9 :=
  @checkedBatches (freeVars 0 0) rd_0_0 _ _ _ sl_0_0 [[]] 9 fmt_0_0_8 (ch_0_0_8.map Subtype.val) fmt_0_0_9 pp_0_0 (raw_faithful (freeMask 0 0) p_0_0 q_0_0) sl_0_0_ok (by decide +kernel) ok_0_0_8 ch_0_0_9

private def fmt_0_0_10 : ChartFormat := ⟨6, 1, 0, 4, 6⟩
private abbrev Batch_0_0_10 := CheckedBatch (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] 10 fmt_0_0_9 (ch_0_0_9.map Subtype.val) fmt_0_0_10
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_10_0 : List Batch_0_0_10 := [
  ⟨⟨2,0x3010b0e14180122c6b10e0a2c3040608080870a0c00b963446704,0x7ffffffffffb60⟩,by decide +kernel⟩,
  ⟨⟨2,0x6090e1418015ec688ce0e2c304870a0c00b163446706,0xffffffffffffdb0520⟩,by decide +kernel⟩,
  ⟨⟨2,0x28287060066b1a2338585050e0c00cd63c88709,0x7fffffffffe1185a13873e0⟩,by decide +kernel⟩,
  ⟨⟨2,0x14383002866b1a23395820b0e0c00cd63c88729,0x3fffffff120260980a0⟩,by decide +kernel⟩,
  ⟨⟨1,0x60b0a0c006d6344670c,0x3ffffffb8281c121502141e070e1a0⟩,by decide +kernel⟩,
  ⟨⟨2,0x161a141800c2bd8d1c1cb02060b0a0c006f6344670e,0x1ffffffffeb018140a1386a0d0781c04460⟩,by decide +kernel⟩,
  ⟨⟨2,0x14141800c3358d119d382060b0a0c006f6344672e,0xffffffffffd0f4050485434082c11c0c520⟩,by decide +kernel⟩,
  ⟨⟨1,0x8305070a08029163446710,0x1ffffa828240619020406050483c08d0681c240e0⟩,by decide +kernel⟩,
  ⟨⟨2,0xb0d0e1410015ec68e0e6010305070a08029163446712,0x1fffff70109412010b1a1480c061385e150681c2c2e0⟩,by decide +kernel⟩,
  ⟨⟨2,0x161c100196c688cea4103030b0a08029163446732,0xffffff187c0a1a58086e134030483c34482411c343a0⟩,by decide +kernel⟩,
  ⟨⟨1,0x305110a08300f63c88770,0x7fff9c0d006010580e063478281c22170482c3c060⟩,by decide +kernel⟩,
  ⟨⟨1,0x8305070a00c03163446714,0x1ffcc5851a0c78de344c245c08d0080c1209025416070280e0⟩,by decide +kernel⟩]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_10_1 : List Batch_0_0_10 := [
  ⟨⟨2,0xd0e1400215ac68e0e6810305130e14003163446716,0x7ffe30c8a8d02245118744c1c58b0d4020109c270f416070383e0⟩,by decide +kernel⟩,
  ⟨⟨2,0x5042e1c00219ec688ceac103030b0a00703163446736,0x7ffb261b0a2c08744a1a34d86a15c01048143e2a0c70482e0⟩,by decide +kernel⟩,
  ⟨⟨2,0xc141c20004a3d99a21e50305130a00302f63c88774,0x3ffff3c1b428e08e08e0871a041414182818386c421284a10c108561585a0⟩,by decide +kernel⟩]
private noncomputable def ch_0_0_10 : List Batch_0_0_10 := (ch_0_0_10_0 ++ ch_0_0_10_1)
private noncomputable def lv_0_0_10 : List NodeSpec := flattenBatches fmt_0_0_10 (ch_0_0_10.map Subtype.val)
private theorem ok_0_0_10 : LevelOK rd_0_0 (subGoal 0 0) 10 lv_0_0_10 :=
  @checkedBatches (freeVars 0 0) rd_0_0 _ _ _ sl_0_0 [[]] 10 fmt_0_0_9 (ch_0_0_9.map Subtype.val) fmt_0_0_10 pp_0_0 (raw_faithful (freeMask 0 0) p_0_0 q_0_0) sl_0_0_ok (by decide +kernel) ok_0_0_9 ch_0_0_10

private def fmt_0_0_11 : ChartFormat := ⟨6, 0, 0, 3, 6⟩
private abbrev Batch_0_0_11 := CheckedBatch (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] 11 fmt_0_0_10 (ch_0_0_10.map Subtype.val) fmt_0_0_11
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private noncomputable def ch_0_0_11_0 : List Batch_0_0_11 := [
  ⟨⟨1,0x1840812c6886,0x7ffffff70⟩,by decide +kernel⟩]
private noncomputable def ch_0_0_11 : List Batch_0_0_11 := ch_0_0_11_0
private noncomputable def lv_0_0_11 : List NodeSpec := flattenBatches fmt_0_0_11 (ch_0_0_11.map Subtype.val)
private theorem ok_0_0_11 : LevelOK rd_0_0 (subGoal 0 0) 11 lv_0_0_11 :=
  @checkedBatches (freeVars 0 0) rd_0_0 _ _ _ sl_0_0 [[]] 11 fmt_0_0_10 (ch_0_0_10.map Subtype.val) fmt_0_0_11 pp_0_0 (raw_faithful (freeMask 0 0) p_0_0 q_0_0) sl_0_0_ok (by decide +kernel) ok_0_0_10 ch_0_0_11
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lower_0_0 : Lower (freeVars 0 0) (subGoal 0 0) 12 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 9, 13), (inputs.getD 3 zero, 5, 13), (inputs.getD 4 zero, 9, 25), (inputs.getD 5 zero, 6, 38)]) ok_0_0_11 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube0_0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem rootCertificate : Impossible target 11 inputs.toFinset := by
  have ht : subGoal 0 0 = target := by decide +kernel
  have hraw : (freeVars 0 0).toFinset = inputs.toFinset := by decide +kernel
  have hc : Impossible (subGoal 0 0) 11 (freeVars 0 0).toFinset :=
    impossible_of_top ok_0_0_11 List.mem_cons_self (by decide +kernel)
  simpa only [ht, hraw] using hc

theorem compactMain :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 targetFun s →
      ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧
        ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = targetFun x :=
  main_from_root rootCertificate

end PEqualNP.Outside.L_meta_42084_aux.Frontier

theorem PEqualNP.Outside.L_meta_42084 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808392 * 2 ^ 32 + 4203260040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808392 * 2 ^ 32 + 4203260040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  exact PEqualNP.Outside.L_meta_42084_aux.Frontier.compactMain
