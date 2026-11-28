import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39687_aux.Upper

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open scoped BigOperators

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4008372904 * 2 ^ 32 + 3939027080)
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def witness : Circuit :=
  ⟨[⟨.or, [4, 3]⟩,
    ⟨.and, [4, 3]⟩,
    ⟨.or, [7, 1]⟩,
    ⟨.and, [6, 1]⟩,
    ⟨.or, [6, 2]⟩,
    ⟨.and, [5, 7]⟩,
    ⟨.or, [2, 11]⟩,
    ⟨.and, [12, 9]⟩,
    ⟨.or, [0, 13]⟩,
    ⟨.and, [5, 10]⟩,
    ⟨.or, [8, 15]⟩,
    ⟨.and, [16, 14]⟩], 17⟩

theorem witness_size : witness.size = 12 := rfl

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

theorem bounded_replacement {s : ℕ} (floor : 12 ≤ s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧
      ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x :=
  ⟨witness, witness_monotone, witness_size.symm ▸ floor, witness_correct⟩

end PEqualNP.Outside.L_meta_39687_aux.Upper

namespace PEqualNP.Outside.L_meta_39687_aux.Frontier
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
def target : Sig := 0xeeeaeaa8eac8c888
def targetFun (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4008372904 * 2 ^ 32 + 3939027080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
      Nat.testBit (4008372904 * 2 ^ 32 + 3939027080)
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

private def selectPrev (ids : List Nat) (prev : List NodeSpec) : List NodeSpec :=
  selectFrom 0 ids prev

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

private theorem selectPrevOK {rawD T cap prev} (is : List Nat) (h : LevelOK rawD T cap prev) :
    LevelOK rawD T cap (selectPrev is prev) :=
  fun node hm => h node (selectFrom_mem hm)

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

private theorem circuit_with_not_impossible (root_imp : Impossible target 10 inputs.toFinset)
    (root_ess : ∀ a ∈ inputs, Essential target inputs a)
    (C : Circuit) (hfan : PEqualNP.MetaComplexity.FanInTwo C) (hsz : C.size ≤ 11)
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
  have hlen : C.gates.length ≤ 11 := hsz
  have hS : inputs.toFinset = S := by
    ext a; rw [List.mem_toFinset]
    refine ⟨fun hm => ?_, hs a⟩
    obtain ⟨r, s, hd, iso⟩ := root_ess a hm
    exact raw_required run inputs a hs r s hd iso
  exact root_imp k (by omega) (hS.symm ▸ run)

private def essentialRows : List (Sig × Row × Row) :=
  [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 10, 14), (inputs.getD 3 zero, 6, 14), (inputs.getD 4 zero, 6, 22), (inputs.getD 5 zero, 5, 37)]

private theorem root_ess : ∀ a ∈ inputs, Essential target inputs a := by
  have h : checkEssential target inputs essentialRows = true := by decide +kernel
  have hc : inputs.all (fun a => (essentialRows.map Prod.fst).contains a) = true :=
    by decide +kernel
  intro a ha
  have h1 := List.all_eq_true.mp hc a ha
  simp only [List.contains_eq_mem, decide_eq_true_eq] at h1
  exact essential_ok h a (List.mem_toFinset.mpr h1)

theorem main_from_root (root_imp : Impossible target 10 inputs.toFinset) :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 targetFun s →
      ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧
        ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = targetFun x := by
  intro s ⟨C, hfan, hsz, heval⟩
  by_cases hs : 12 ≤ s
  · exact PEqualNP.Outside.L_meta_39687_aux.Upper.bounded_replacement hs
  · by_cases hno : ∀ g ∈ C.gates, isNot g = false
    · exact ⟨C, no_not_monotone C hfan hno, hsz, heval⟩
    · exact False.elim (circuit_with_not_impossible root_imp root_ess C hfan (by omega) heval hno)

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
private def ck0 := levelCheck (freeVars 4 32) rd_4_32 (subGoal 4 32) sl_4_32 [[]] [] 3
private def d0 : List NodeSpec := [([(0,1,0),(1,2,4)],[0,1,5,3],[]),([(0,1,0),(2,2,4)],[5,0,1,3],[]),([(0,1,0),(1,3,4)],[0,1,2,5],[]),([(0,1,0),(2,3,4)],[5,0,1,2],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q0 : ck0 d0 = true := by decide +kernel
private def d1 : List NodeSpec := [([(1,1,0),(0,2,4)],[0,1,5,3],[]),([(1,1,0),(3,2,4)],[5,0,1,3],[]),([(1,1,0),(0,3,4)],[0,1,5,2],[]),([(1,1,0),(3,3,4)],[5,0,1,2],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q1 : ck0 d1 = true := by decide +kernel
private def d2 : List NodeSpec := [([(0,2,0),(1,1,4)],[0,5,2,3],[]),([(0,2,0),(2,1,4)],[5,0,2,3],[]),([(0,2,0),(1,3,4)],[0,1,2,5],[]),([(0,2,0),(2,3,4)],[5,0,1,2],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q2 : ck0 d2 = true := by decide +kernel
private def lv_4_32_3_0 : List NodeSpec := (d0 ++ (d1 ++ d2))

private theorem ok_4_32_3_0 : LevelOK rd_4_32 (subGoal 4 32) 3 lv_4_32_3_0 :=
  levelCheck_sound pp_4_32 (raw_faithful _ _ _) sl_4_32_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_4_32 (subGoal 4 32) 2)
    (levelCheck_join q0 (levelCheck_join q1 q2))
private def ck3 := levelCheck (freeVars 4 32) rd_4_32 (subGoal 4 32) sl_4_32 [[]] [] 3
private def d3 : List NodeSpec := [([(1,2,0),(0,4,1)],[0,5,2,3],[]),([(1,2,0),(2,4,1)],[5,0,2,3],[]),([(1,2,0),(0,3,4)],[0,1,2,5],[]),([(1,2,0),(3,3,4)],[5,0,1,2],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q3 : ck3 d3 = true := by decide +kernel
private def d4 : List NodeSpec := [([(0,2,1),(1,2,1)],[0,4,5,3],[]),([(2,2,1),(1,3,4)],[0,1,2,5],[]),([(2,2,1),(2,3,4)],[0,1,5,2],[]),([(3,2,1),(1,3,4)],[0,1,2,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q4 : ck3 d4 = true := by decide +kernel
private def d5 : List NodeSpec := [([(3,2,1),(2,3,4)],[0,1,2,5],[]),([(0,3,0),(1,1,4)],[0,5,2,3],[]),([(0,3,0),(2,1,4)],[5,0,2,3],[]),([(0,3,0),(1,2,4)],[0,1,5,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q5 : ck3 d5 = true := by decide +kernel
private def lv_4_32_3_1 : List NodeSpec := (d3 ++ (d4 ++ d5))

private theorem ok_4_32_3_1 : LevelOK rd_4_32 (subGoal 4 32) 3 lv_4_32_3_1 :=
  levelCheck_sound pp_4_32 (raw_faithful _ _ _) sl_4_32_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_4_32 (subGoal 4 32) 2)
    (levelCheck_join q3 (levelCheck_join q4 q5))
private def ck6 := levelCheck (freeVars 4 32) rd_4_32 (subGoal 4 32) sl_4_32 [[]] [] 3
private def d6 : List NodeSpec := [([(0,3,0),(2,2,4)],[5,0,1,3],[]),([(1,3,0),(0,4,1)],[0,5,2,3],[]),([(1,3,0),(2,4,1)],[5,0,2,3],[]),([(1,3,0),(0,4,2)],[0,1,5,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q6 : ck6 d6 = true := by decide +kernel
private def d7 : List NodeSpec := [([(1,3,0),(2,4,2)],[5,0,1,3],[]),([(0,3,1),(1,3,1)],[0,4,2,5],[]),([(2,3,1),(1,2,4)],[0,1,5,3],[]),([(2,3,1),(2,2,4)],[0,5,1,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q7 : ck6 d7 = true := by decide +kernel
private def d8 : List NodeSpec := [([(3,3,1),(1,2,4)],[0,1,5,3],[]),([(3,3,1),(2,2,4)],[0,1,5,3],[]),([(0,3,2),(1,3,2)],[0,1,4,5],[]),([(2,3,2),(1,1,4)],[0,5,2,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q8 : ck6 d8 = true := by decide +kernel
private def lv_4_32_3_2 : List NodeSpec := (d6 ++ (d7 ++ d8))

private theorem ok_4_32_3_2 : LevelOK rd_4_32 (subGoal 4 32) 3 lv_4_32_3_2 :=
  levelCheck_sound pp_4_32 (raw_faithful _ _ _) sl_4_32_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_4_32 (subGoal 4 32) 2)
    (levelCheck_join q6 (levelCheck_join q7 q8))
private def lv_4_32_3_3 : List NodeSpec := [([(2, 3, 2), (2, 1, 4)], [0, 5, 2, 3], []), ([(3, 3, 2), (1, 1, 4)], [0, 5, 2, 3], []), ([(3, 3, 2), (2, 1, 4)], [0, 5, 2, 3], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_4_32_3_3 : LevelOK rd_4_32 (subGoal 4 32) 3 lv_4_32_3_3 :=
  levelCheck_sound pp_4_32 (raw_faithful _ _ _) sl_4_32_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_4_32 (subGoal 4 32) 2)
    (by decide +kernel : levelCheck (freeVars 4 32) rd_4_32 (subGoal 4 32) sl_4_32 [[]] [] 3 lv_4_32_3_3 = true)
private def lv_4_32_3 : List NodeSpec := ((lv_4_32_3_0 ++ lv_4_32_3_1) ++ (lv_4_32_3_2 ++ lv_4_32_3_3))
private theorem ok_4_32_3 : LevelOK rd_4_32 (subGoal 4 32) 3 lv_4_32_3 := (levelOK_append (levelOK_append ok_4_32_3_0 ok_4_32_3_1) (levelOK_append ok_4_32_3_2 ok_4_32_3_3))
private def ck9 (ids : List Nat) := levelCheck (freeVars 4 32) rd_4_32 (subGoal 4 32) sl_4_32 [[]] (selectPrev ids lv_4_32_3) 4
private def d9 : List NodeSpec := [([(0,1,0)],[4,0,1,2,3],[]),([(1,1,0)],[0,1,4,2,3],[]),([(2,1,0)],[4,0,1,2,3],[]),([(3,1,0)],[4,0,1,2,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q9 : ck9 [0,1,2,3,4,5,6,7] d9 = true := by decide +kernel
private def d10 : List NodeSpec := [([(0,2,0)],[4,0,1,2,3],[]),([(1,2,0)],[0,1,2,4,3],[]),([(2,2,0)],[4,0,1,2,3],[]),([(3,2,0)],[4,0,1,2,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q10 : ck9 [8,9,10,11,12,13,14,15] d10 = true := by decide +kernel
private def d11 : List NodeSpec := [([(0,2,1)],[0,4,1,2,3],[]),([(1,2,1)],[0,1,2,4,3],[]),([(2,2,1)],[4,0,1,2,3],[]),([(3,2,1)],[4,0,1,2,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q11 : ck9 [16,17,18,19,20] d11 = true := by decide +kernel
private def lv_4_32_4_0 : List NodeSpec := (d9 ++ (d10 ++ d11))

private theorem ok_4_32_4_0 : LevelOK rd_4_32 (subGoal 4 32) 4 lv_4_32_4_0 := by
  have go {ids ds} (h : ck9 ids ds = true) : LevelOK rd_4_32 (subGoal 4 32) 4 ds :=
    levelCheck_sound pp_4_32 (raw_faithful _ _ _) sl_4_32_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_4_32_3) h
  exact (levelOK_append (go q9) (levelOK_append (go q10) (go q11)))
private def ck12 (ids : List Nat) := levelCheck (freeVars 4 32) rd_4_32 (subGoal 4 32) sl_4_32 [[]] (selectPrev ids lv_4_32_3) 4
private def d12 : List NodeSpec := [([(0,3,0)],[4,0,1,2,3],[]),([(1,3,0)],[0,1,2,3,4],[]),([(2,3,0)],[4,0,1,2,3],[]),([(3,3,0)],[4,0,1,2,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q12 : ck12 [21,22,23,24,25,26,27,28] d12 = true := by decide +kernel
private def d13 : List NodeSpec := [([(0,3,1)],[0,4,1,2,3],[]),([(1,3,1)],[0,1,2,3,4],[]),([(2,3,1)],[4,0,1,2,3],[]),([(3,3,1)],[4,0,1,2,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q13 : ck12 [29,30,31,32,33] d13 = true := by decide +kernel
private def d14 : List NodeSpec := [([(0,3,2)],[0,1,4,2,3],[]),([(1,3,2)],[0,1,2,3,4],[]),([(2,3,2)],[4,0,1,2,3],[]),([(3,3,2)],[4,0,1,2,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q14 : ck12 [34,35,36,37,38] d14 = true := by decide +kernel
private def lv_4_32_4_1 : List NodeSpec := (d12 ++ (d13 ++ d14))

private theorem ok_4_32_4_1 : LevelOK rd_4_32 (subGoal 4 32) 4 lv_4_32_4_1 := by
  have go {ids ds} (h : ck12 ids ds = true) : LevelOK rd_4_32 (subGoal 4 32) 4 ds :=
    levelCheck_sound pp_4_32 (raw_faithful _ _ _) sl_4_32_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_4_32_3) h
  exact (levelOK_append (go q12) (levelOK_append (go q13) (go q14)))
private def lv_4_32_4 : List NodeSpec := (lv_4_32_4_0 ++ lv_4_32_4_1)
private theorem ok_4_32_4 : LevelOK rd_4_32 (subGoal 4 32) 4 lv_4_32_4 := (levelOK_append ok_4_32_4_0 ok_4_32_4_1)
private def lv_4_32_5_0 : List NodeSpec := [([], [0, 1, 2, 3], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_4_32_5_0 : LevelOK rd_4_32 (subGoal 4 32) 5 lv_4_32_5_0 :=
  levelCheck_sound pp_4_32 (raw_faithful _ _ _) sl_4_32_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] ok_4_32_4)
    (by decide +kernel : levelCheck (freeVars 4 32) rd_4_32 (subGoal 4 32) sl_4_32 [[]] (selectPrev [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] lv_4_32_4) 5 lv_4_32_5_0 = true)
private def lv_4_32_5 : List NodeSpec := lv_4_32_5_0
private theorem ok_4_32_5 : LevelOK rd_4_32 (subGoal 4 32) 5 lv_4_32_5 := ok_4_32_5_0
private theorem lower_4_32 : Lower (freeVars 4 32) (subGoal 4 32) 6 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 1, 17)]) ok_4_32_5 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube4_32

private theorem lower_8_32 : Lower (freeVars 8 32) (subGoal 8 32) 6 :=
  carry_of (swaps := [50]) (by decide +kernel) lower_4_32

private theorem lower_16_32 : Lower (freeVars 16 32) (subGoal 16 32) 6 :=
  carry_of (swaps := [66]) (by decide +kernel) lower_4_32

section Cube1_34

private def p_1_34 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 2 => mk128 0xbecfbecfbecfbecf 0xbecfbecfbecfbecf
  | 3 => mk128 0xdf73df73df73df73 0xdf73df73df73df73
  | 4 => mk128 0xefbcefbcefbcefbc 0xefbcefbcefbcefbc
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private def q_1_34 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 2 => mk128 0x4205420542054205 0x4205420542054205
  | 3 => mk128 0x2412241224122412 0x2412241224122412
  | 4 => mk128 0x1828182818281828 0x1828182818281828
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private theorem pp_1_34 : properPairs (subGoal 1 34) (asRow p_1_34) (asRow q_1_34) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_1_34 : List Decor := rawDecor (freeMask 1 34) p_1_34 q_1_34
private def sl_1_34 : List (Sig × Nat) := []
private theorem sl_1_34_ok : ∀ s ∈ sl_1_34, Slice (freeVars 1 34) (subGoal 1 34) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private def lv_1_34_3_0 : List NodeSpec := [([], [0, 1, 2], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_1_34_3_0 : LevelOK rd_1_34 (subGoal 1 34) 3 lv_1_34_3_0 :=
  levelCheck_sound pp_1_34 (raw_faithful _ _ _) sl_1_34_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_1_34 (subGoal 1 34) 2)
    (by decide +kernel : levelCheck (freeVars 1 34) rd_1_34 (subGoal 1 34) sl_1_34 [[]] [] 3 lv_1_34_3_0 = true)
private def lv_1_34_3 : List NodeSpec := lv_1_34_3_0
private theorem ok_1_34_3 : LevelOK rd_1_34 (subGoal 1 34) 3 lv_1_34_3 := ok_1_34_3_0
private theorem lower_1_34 : Lower (freeVars 1 34) (subGoal 1 34) 4 :=
  lower_of_search (xs := [(inputs.getD 2 zero, 8, 12), (inputs.getD 3 zero, 4, 12), (inputs.getD 4 zero, 4, 20)]) ok_1_34_3 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube1_34

section Cube1_32

private def p_1_32 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 2 => mk128 0xffc3fe3fbf0fffc3 0xfe3fbf0fffc3fe3f
  | 3 => mk128 0xfffc3fc7dff0fffc 0x3fc7dff0fffc3fc7
  | 4 => mk128 0xfffc3f8efff0fff 0xc3f8efff0fffc3f8
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private def q_1_32 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0x22c444db012222c4 0x44db012222c444db
  | 2 => mk128 0x4562aa2d42e44562 0xaa2d42e44562aa2d
  | 3 => mk128 0x89aa3346244e89aa 0x3346244e89aa3346
  | 4 => mk128 0xee3323b01888ee33 0x23b01888ee3323b0
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private theorem pp_1_32 : properPairs (subGoal 1 32) (asRow p_1_32) (asRow q_1_32) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_1_32 : List Decor := rawDecor (freeMask 1 32) p_1_32 q_1_32
private def sl_1_32 : List (Sig × Nat) := [(subcube 1 34, 4)]
private theorem sl_1_32_ok : ∀ s ∈ sl_1_32, Slice (freeVars 1 32) (subGoal 1 32) s.1 s.2 := by
  intro s hs
  simp only [sl_1_32, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 1 34) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_1_34
private def lv_1_32_4_0 : List NodeSpec := [([], [0, 1, 2, 3], [(0, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_1_32_4_0 : LevelOK rd_1_32 (subGoal 1 32) 4 lv_1_32_4_0 :=
  levelCheck_sound pp_1_32 (raw_faithful _ _ _) sl_1_32_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_1_32 (subGoal 1 32) 3)
    (by decide +kernel : levelCheck (freeVars 1 32) rd_1_32 (subGoal 1 32) sl_1_32 [[]] [] 4 lv_1_32_4_0 = true)
private def lv_1_32_4 : List NodeSpec := lv_1_32_4_0
private theorem ok_1_32_4 : LevelOK rd_1_32 (subGoal 1 32) 4 lv_1_32_4 := ok_1_32_4_0
private theorem lower_1_32 : Lower (freeVars 1 32) (subGoal 1 32) 5 :=
  lower_of_search (xs := [(inputs.getD 1 zero, 12, 14), (inputs.getD 2 zero, 10, 14), (inputs.getD 3 zero, 6, 14), (inputs.getD 4 zero, 6, 22)]) ok_1_32_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube1_32

section Cube0_34

private def p_0_34 : Nat → Bits
  | 0 => mk128 0xf1b77c27feaef1b7 0x7c27feaef1b77c27
  | 1 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 2 => mk128 0x3e3ba0dabf333e3b 0xa0dabf333e3ba0da
  | 3 => mk128 0xcfc3c31cdfc3cfc3 0xc31cdfc3cfc3c31c
  | 4 => mk128 0xffc03e0effc0ffc 0x3e0effc0ffc03e0
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private def q_0_34 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 2 => mk128 0x4211044a42444211 0x44a42444211044a
  | 3 => mk128 0x1482091424181482 0x914241814820914
  | 4 => mk128 0xa92012a01801a920 0x12a01801a92012a0
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private theorem pp_0_34 : properPairs (subGoal 0 34) (asRow p_0_34) (asRow q_0_34) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_0_34 : List Decor := rawDecor (freeMask 0 34) p_0_34 q_0_34
private def sl_0_34 : List (Sig × Nat) := [(subcube 1 34, 4)]
private theorem sl_0_34_ok : ∀ s ∈ sl_0_34, Slice (freeVars 0 34) (subGoal 0 34) s.1 s.2 := by
  intro s hs
  simp only [sl_0_34, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 1 34) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_1_34
private def lv_0_34_4_0 : List NodeSpec := [([], [0, 1, 2, 3], [(0, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_0_34_4_0 : LevelOK rd_0_34 (subGoal 0 34) 4 lv_0_34_4_0 :=
  levelCheck_sound pp_0_34 (raw_faithful _ _ _) sl_0_34_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_0_34 (subGoal 0 34) 3)
    (by decide +kernel : levelCheck (freeVars 0 34) rd_0_34 (subGoal 0 34) sl_0_34 [[]] [] 4 lv_0_34_4_0 = true)
private def lv_0_34_4 : List NodeSpec := lv_0_34_4_0
private theorem ok_0_34_4 : LevelOK rd_0_34 (subGoal 0 34) 4 lv_0_34_4 := ok_0_34_4_0
private theorem lower_0_34 : Lower (freeVars 0 34) (subGoal 0 34) 5 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 0, 1), (inputs.getD 2 zero, 8, 12), (inputs.getD 3 zero, 4, 12), (inputs.getD 4 zero, 4, 20)]) ok_0_34_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube0_34

section Cube0_32

private def p_0_32 : Nat → Bits
  | 0 => mk128 0xf87ffffff03f0fe1 0xfff87ffffe88f1ff
  | 1 => mk128 0xff83e1f0ffc7f0fe 0x1c3f870e1f774e93
  | 2 => mk128 0xfffc01ff1ff800ff 0xe03ff80fe1878f1c
  | 3 => mk128 0xfffffe001fffff00 0x3ffff001f80fe0
  | 4 => mk128 0x1fffffff 0xffc0000001fff000
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private def q_0_32 : Nat → Bits
  | 0 => mk128 0x800000000000100 0x2400090200001025
  | 1 => mk128 0x111942a102c31062 0x89882245c334692
  | 2 => mk128 0xa228d548355888b5 0x412d5049c5858b18
  | 3 => mk128 0xc452906a59adaa11 0x23664e089d80dc0
  | 4 => mk128 0x8763198c9e36ccd9 0x9384408111eee000
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private theorem pp_0_32 : properPairs (subGoal 0 32) (asRow p_0_32) (asRow q_0_32) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_0_32 : List Decor := rawDecor (freeMask 0 32) p_0_32 q_0_32
private def sl_0_32 : List (Sig × Nat) := [(subcube 4 32, 6), (subcube 8 32, 6), (subcube 16 32, 6), (subcube 1 32, 5), (subcube 0 34, 5), (subcube 1 34, 4)]
private theorem sl_0_32_ok : ∀ s ∈ sl_0_32, Slice (freeVars 0 32) (subGoal 0 32) s.1 s.2 := by
  intro s hs
  simp only [sl_0_32, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · exact slice_correct (ms := fixRows 4 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_4_32
  · exact slice_correct (ms := fixRows 8 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_8_32
  · exact slice_correct (ms := fixRows 16 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_16_32
  · exact slice_correct (ms := fixRows 1 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_1_32
  · exact slice_correct (ms := fixRows 0 34) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_0_34
  · exact slice_correct (ms := fixRows 1 34) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_1_34
private def autos_0_32 : List (List Move) := [[], [swapRows 50], [swapRows 67], [swapRows 50, swapRows 67], [swapRows 67, swapRows 50], [swapRows 50, swapRows 67, swapRows 50]]
private theorem autos_0_32_ok : ∀ m ∈ autos_0_32, autoOK (subGoal 0 32) m = true := by
  intro m hm
  simp only [autos_0_32, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
private def lv_0_32_3_0 : List NodeSpec := [([(1, 2, 0), (1, 3, 2), (1, 4, 5), (1, 4, 3), (0, 7, 1)], [0, 9, 6, 8], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_0_32_3_0 : LevelOK rd_0_32 (subGoal 0 32) 3 lv_0_32_3_0 :=
  levelCheck_sound pp_0_32 (raw_faithful _ _ _) sl_0_32_ok autos_0_32_ok (emptyLevelOK rd_0_32 (subGoal 0 32) 2)
    (by decide +kernel : levelCheck (freeVars 0 32) rd_0_32 (subGoal 0 32) sl_0_32 autos_0_32 [] 3 lv_0_32_3_0 = true)
private def lv_0_32_3 : List NodeSpec := lv_0_32_3_0
private theorem ok_0_32_3 : LevelOK rd_0_32 (subGoal 0 32) 3 lv_0_32_3 := ok_0_32_3_0
private def ck15 (ids : List Nat) := levelCheck (freeVars 0 32) rd_0_32 (subGoal 0 32) sl_0_32 autos_0_32 (selectPrev ids lv_0_32_3) 4
private def d15 : List NodeSpec := [([(0,1,0),(1,2,5),(1,3,6),(0,7,1)],[0,8,6,3,4],[]),([(0,1,0),(1,2,5),(1,4,3),(0,7,1)],[0,8,6,3,4],[]),([(0,1,0),(1,2,5),(1,3,2),(0,7,1)],[0,8,6,3,4],[]),([(0,1,0),(1,2,5),(1,3,6),(0,7,1)],[0,8,2,3,4],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q15 : ck15 [] d15 = true := by decide +kernel
private def d16 : List NodeSpec := [([(1,1,0),(3,2,1),(3,3,6),(2,5,7)],[0,8,2,3,4],[]),([(1,1,0),(3,2,1),(3,3,6),(1,4,7)],[0,5,2,3,8],[]),([(1,1,0),(3,2,1),(1,3,2),(0,7,5)],[6,0,8,3,4],[]),([(2,1,0),(3,2,5),(3,3,6),(1,4,7)],[0,1,2,3,8],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q16 : ck15 [] d16 = true := by decide +kernel
private def d17 : List NodeSpec := [([(2,1,0),(3,2,1),(3,3,6),(1,4,7)],[5,0,2,3,8],[]),([(3,1,0),(1,2,5),(1,3,6),(3,4,7)],[8,0,1,2,3],[]),([(1,2,0),(3,3,1),(2,5,6),(1,3,2)],[0,1,7,8,4],[]),([(1,2,0),(1,3,2),(1,4,5),(1,4,3)],[0,1,6,7,8],[(1,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q17 : ck15 [0] d17 = true := by decide +kernel
private def lv_0_32_4_0 : List NodeSpec := (d15 ++ (d16 ++ d17))

private theorem ok_0_32_4_0 : LevelOK rd_0_32 (subGoal 0 32) 4 lv_0_32_4_0 := by
  have go {ids ds} (h : ck15 ids ds = true) : LevelOK rd_0_32 (subGoal 0 32) 4 ds :=
    levelCheck_sound pp_0_32 (raw_faithful _ _ _) sl_0_32_ok autos_0_32_ok (selectPrevOK ids ok_0_32_3) h
  exact (levelOK_append (go q15) (levelOK_append (go q16) (go q17)))
private def ck18 (ids : List Nat) := levelCheck (freeVars 0 32) rd_0_32 (subGoal 0 32) sl_0_32 autos_0_32 (selectPrev ids lv_0_32_3) 4
private def d18 : List NodeSpec := [([(1,2,0),(1,3,2),(1,4,5),(0,7,1)],[0,8,3,6,4],[]),([(1,2,0),(1,3,2),(1,4,3),(0,7,5)],[0,1,8,6,4],[(1,[])]),([(1,2,0),(1,3,5),(0,6,1),(2,6,2)],[8,0,7,3,4],[]),([(1,2,0),(1,3,5),(0,6,1),(0,4,6)],[0,7,2,3,8],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q18 : ck18 [0] d18 = true := by decide +kernel
private def d19 : List NodeSpec := [([(1,2,0),(1,3,5),(0,6,1),(3,4,6)],[8,0,7,2,3],[]),([(1,2,0),(1,3,5),(2,6,1),(0,4,6)],[7,0,2,3,8],[]),([(1,2,0),(1,3,5),(2,6,1),(3,4,6)],[8,7,0,2,3],[]),([(1,2,0),(1,3,5),(2,6,2),(0,4,6)],[7,0,1,3,8],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q19 : ck18 [] d19 = true := by decide +kernel
private def d20 : List NodeSpec := [([(1,2,0),(1,3,5),(0,4,6),(2,6,7)],[8,0,1,2,3],[]),([(1,2,0),(1,3,5),(1,4,6),(0,7,1)],[0,8,2,3,4],[]),([(3,2,0),(1,3,5),(1,4,6),(0,7,1)],[0,8,2,3,4],[]),([(1,2,1),(3,3,5),(3,4,6),(1,2,7)],[0,1,8,3,4],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q20 : ck18 [] d20 = true := by decide +kernel
private def lv_0_32_4_1 : List NodeSpec := (d18 ++ (d19 ++ d20))

private theorem ok_0_32_4_1 : LevelOK rd_0_32 (subGoal 0 32) 4 lv_0_32_4_1 := by
  have go {ids ds} (h : ck18 ids ds = true) : LevelOK rd_0_32 (subGoal 0 32) 4 ds :=
    levelCheck_sound pp_0_32 (raw_faithful _ _ _) sl_0_32_ok autos_0_32_ok (selectPrevOK ids ok_0_32_3) h
  exact (levelOK_append (go q18) (levelOK_append (go q19) (go q20)))
private def ck21 (ids : List Nat) := levelCheck (freeVars 0 32) rd_0_32 (subGoal 0 32) sl_0_32 autos_0_32 (selectPrev ids lv_0_32_3) 4
private def d21 : List NodeSpec := [([(3,2,1),(1,3,5),(2,6,3),(2,1,7)],[0,8,2,6,4],[]),([(3,2,1),(3,3,5),(2,1,6),(1,4,6)],[0,7,2,3,8],[]),([(3,2,1),(3,3,5),(2,4,6),(1,2,6)],[0,1,8,3,7],[]),([(3,2,1),(3,3,5),(1,4,2),(1,4,3)],[6,0,1,7,8],[(2,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q21 : ck21 [] d21 = true := by decide +kernel
private def d22 : List NodeSpec := [([(3,2,1),(1,3,2),(1,4,3),(2,7,5)],[0,1,8,6,4],[(1,[])]),([(3,2,1),(1,3,2),(1,4,3),(0,7,1)],[5,0,8,6,4],[]),([(1,3,2),(0,5,0),(1,5,0),(2,7,6)],[8,1,2,3,4],[]),([(1,3,2),(2,5,0),(2,1,6),(1,4,7)],[0,1,2,3,8],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q22 : ck21 [] d22 = true := by decide +kernel
private def d23 : List NodeSpec := [([(1,3,2),(2,5,0),(1,4,2),(1,4,3)],[6,0,1,7,8],[]),([(1,3,2),(0,5,1),(1,6,0),(3,4,7)],[8,0,1,2,3],[]),([(1,3,2),(0,5,1),(1,4,2),(1,4,3)],[0,6,1,7,8],[]),([(1,3,2),(0,5,1),(1,5,1),(2,7,6)],[8,0,2,3,4],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q23 : ck21 [] d23 = true := by decide +kernel
private def lv_0_32_4_2 : List NodeSpec := (d21 ++ (d22 ++ d23))

private theorem ok_0_32_4_2 : LevelOK rd_0_32 (subGoal 0 32) 4 lv_0_32_4_2 := by
  have go {ids ds} (h : ck21 ids ds = true) : LevelOK rd_0_32 (subGoal 0 32) 4 ds :=
    levelCheck_sound pp_0_32 (raw_faithful _ _ _) sl_0_32_ok autos_0_32_ok (selectPrevOK ids ok_0_32_3) h
  exact (levelOK_append (go q21) (levelOK_append (go q22) (go q23)))
private def lv_0_32_4_3 : List NodeSpec := [([(1, 3, 2), (2, 5, 1), (3, 5, 1), (1, 4, 7)], [6, 0, 2, 3, 8], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_0_32_4_3 : LevelOK rd_0_32 (subGoal 0 32) 4 lv_0_32_4_3 :=
  levelCheck_sound pp_0_32 (raw_faithful _ _ _) sl_0_32_ok autos_0_32_ok (selectPrevOK [] ok_0_32_3)
    (by decide +kernel : levelCheck (freeVars 0 32) rd_0_32 (subGoal 0 32) sl_0_32 autos_0_32 (selectPrev [] lv_0_32_3) 4 lv_0_32_4_3 = true)
private def lv_0_32_4 : List NodeSpec := ((lv_0_32_4_0 ++ lv_0_32_4_1) ++ (lv_0_32_4_2 ++ lv_0_32_4_3))
private theorem ok_0_32_4 : LevelOK rd_0_32 (subGoal 0 32) 4 lv_0_32_4 := (levelOK_append (levelOK_append ok_0_32_4_0 ok_0_32_4_1) (levelOK_append ok_0_32_4_2 ok_0_32_4_3))
private def ck24 (ids : List Nat) := levelCheck (freeVars 0 32) rd_0_32 (subGoal 0 32) sl_0_32 autos_0_32 (selectPrev ids lv_0_32_4) 5
private def d24 : List NodeSpec := [([(0,1,0),(1,2,5),(1,3,6)],[0,1,6,3,7,4],[(1,[0,1]),(4,[1])]),([(0,1,0),(1,2,5),(3,3,6)],[7,0,1,6,3,4],[]),([(0,1,0),(1,2,5),(1,4,3)],[0,1,6,3,4,7],[(1,[0,1]),(4,[1])]),([(0,1,0),(1,2,5),(1,3,2)],[0,1,6,3,7,4],[(1,[]),(4,[1])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q24 : ck24 [0,1,2] d24 = true := by decide +kernel
private def d25 : List NodeSpec := [([(0,1,0),(1,2,5),(1,3,6)],[0,1,2,3,7,4],[(0,[0,2])]),([(0,1,0),(1,2,5),(3,3,6)],[7,0,1,2,3,4],[(1,[0,1])]),([(0,1,0),(1,3,2),(2,6,5)],[7,0,1,2,3,4],[(0,[]),(0,[0,2])]),([(0,1,0),(1,3,2),(0,6,1)],[5,0,7,2,3,4],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q25 : ck24 [1,2,3] d25 = true := by decide +kernel
private def d26 : List NodeSpec := [([(1,1,0),(3,2,1),(2,5,6)],[6,0,7,2,3,4],[(0,[])]),([(1,1,0),(3,2,1),(1,3,6)],[0,5,2,3,7,4],[]),([(1,1,0),(3,2,1),(3,3,6)],[7,0,5,2,3,4],[]),([(1,1,0),(3,2,1),(1,3,2)],[6,0,5,3,7,4],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q26 : ck24 [4,5,6] d26 = true := by decide +kernel
private def lv_0_32_5_0 : List NodeSpec := (d24 ++ (d25 ++ d26))

private theorem ok_0_32_5_0 : LevelOK rd_0_32 (subGoal 0 32) 5 lv_0_32_5_0 := by
  have go {ids ds} (h : ck24 ids ds = true) : LevelOK rd_0_32 (subGoal 0 32) 5 ds :=
    levelCheck_sound pp_0_32 (raw_faithful _ _ _) sl_0_32_ok autos_0_32_ok (selectPrevOK ids ok_0_32_4) h
  exact (levelOK_append (go q24) (levelOK_append (go q25) (go q26)))
private def ck27 (ids : List Nat) := levelCheck (freeVars 0 32) rd_0_32 (subGoal 0 32) sl_0_32 autos_0_32 (selectPrev ids lv_0_32_4) 5
private def d27 : List NodeSpec := [([(1,1,0),(3,2,5),(1,3,6)],[6,0,1,3,7,4],[]),([(1,1,0),(3,2,5),(3,3,6)],[7,6,0,1,3,4],[(1,[0,1])]),([(1,1,0),(3,2,5),(1,4,3)],[6,0,1,3,4,7],[(1,[0,1])]),([(1,1,0),(3,2,5),(1,3,6)],[0,1,2,3,7,4],[(1,[0,1])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q27 : ck27 [] d27 = true := by decide +kernel
private def d28 : List NodeSpec := [([(1,1,0),(3,2,5),(3,3,6)],[7,0,1,2,3,4],[(0,[0,2])]),([(1,1,0),(3,2,5),(1,3,2)],[6,0,1,3,7,4],[(1,[])]),([(1,1,0),(1,3,2),(0,6,5)],[0,1,7,2,3,4],[(0,[]),(0,[0,2]),(3,[])]),([(2,1,0),(3,2,5),(1,0,6)],[6,7,1,2,3,4],[(0,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q28 : ck27 [6] d28 = true := by decide +kernel
private def d29 : List NodeSpec := [([(2,1,0),(3,2,5),(2,1,6)],[6,0,7,2,3,4],[(0,[])]),([(2,1,0),(3,2,5),(1,3,6)],[0,1,2,3,7,4],[]),([(2,1,0),(3,2,5),(3,3,6)],[7,0,1,2,3,4],[(2,[])]),([(2,1,0),(3,2,5),(1,3,2)],[6,0,1,3,7,4],[(1,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q29 : ck27 [3,7] d29 = true := by decide +kernel
private def lv_0_32_5_1 : List NodeSpec := (d27 ++ (d28 ++ d29))

private theorem ok_0_32_5_1 : LevelOK rd_0_32 (subGoal 0 32) 5 lv_0_32_5_1 := by
  have go {ids ds} (h : ck27 ids ds = true) : LevelOK rd_0_32 (subGoal 0 32) 5 ds :=
    levelCheck_sound pp_0_32 (raw_faithful _ _ _) sl_0_32_ok autos_0_32_ok (selectPrevOK ids ok_0_32_4) h
  exact (levelOK_append (go q27) (levelOK_append (go q28) (go q29)))
private def ck30 (ids : List Nat) := levelCheck (freeVars 0 32) rd_0_32 (subGoal 0 32) sl_0_32 autos_0_32 (selectPrev ids lv_0_32_4) 5
private def d30 : List NodeSpec := [([(2,1,0),(3,2,1),(1,0,6)],[6,5,7,2,3,4],[(4,[2])]),([(2,1,0),(3,2,1),(1,3,6)],[5,0,2,3,7,4],[]),([(2,1,0),(3,2,1),(3,3,6)],[7,5,0,2,3,4],[(3,[])]),([(2,1,0),(3,2,1),(1,3,2)],[6,5,0,3,7,4],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q30 : ck30 [8] d30 = true := by decide +kernel
private def d31 : List NodeSpec := [([(2,1,0),(1,3,2),(0,6,5)],[7,0,1,2,3,4],[]),([(3,1,0),(1,2,5),(1,3,2)],[0,1,6,3,7,4],[(1,[])]),([(3,1,0),(1,2,5),(1,3,6)],[0,1,2,3,7,4],[(2,[]),(4,[])]),([(3,1,0),(1,2,5),(3,3,6)],[7,0,1,2,3,4],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q31 : ck30 [9] d31 = true := by decide +kernel
private def d32 : List NodeSpec := [([(3,1,0),(1,3,2),(2,6,5)],[0,1,7,2,3,4],[]),([(3,1,0),(1,3,2),(0,6,1)],[5,0,7,2,3,4],[]),([(1,2,0),(0,5,1),(1,3,6)],[0,1,2,3,7,4],[]),([(1,2,0),(0,5,1),(3,3,6)],[7,0,1,2,3,4],[(3,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q32 : ck30 [3,4] d32 = true := by decide +kernel
private def lv_0_32_5_2 : List NodeSpec := (d30 ++ (d31 ++ d32))

private theorem ok_0_32_5_2 : LevelOK rd_0_32 (subGoal 0 32) 5 lv_0_32_5_2 := by
  have go {ids ds} (h : ck30 ids ds = true) : LevelOK rd_0_32 (subGoal 0 32) 5 ds :=
    levelCheck_sound pp_0_32 (raw_faithful _ _ _) sl_0_32_ok autos_0_32_ok (selectPrevOK ids ok_0_32_4) h
  exact (levelOK_append (go q30) (levelOK_append (go q31) (go q32)))
private def ck33 (ids : List Nat) := levelCheck (freeVars 0 32) rd_0_32 (subGoal 0 32) sl_0_32 autos_0_32 (selectPrev ids lv_0_32_4) 5
private def d33 : List NodeSpec := [([(1,2,0),(0,5,1),(1,3,2)],[0,6,1,3,7,4],[(1,[]),(1,[0,1]),(4,[0])]),([(1,2,0),(3,5,1),(1,0,6)],[7,1,2,5,3,4],[(0,[])]),([(1,2,0),(1,3,0),(1,3,2)],[0,1,5,6,7,4],[(0,[]),(1,[]),(3,[])]),([(1,2,0),(1,3,0),(3,3,5)],[7,0,1,2,6,4],[(0,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q33 : ck33 [] d33 = true := by decide +kernel
private def d34 : List NodeSpec := [([(1,2,0),(3,3,1),(1,2,6)],[0,1,7,5,3,4],[(3,[])]),([(1,2,0),(3,3,1),(1,5,6)],[0,1,2,7,3,4],[(4,[])]),([(1,2,0),(3,3,1),(2,5,6)],[0,1,2,7,3,4],[]),([(1,2,0),(3,3,1),(1,3,2)],[6,0,1,5,7,4],[(0,[]),(1,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q34 : ck33 [10] d34 = true := by decide +kernel
private def d35 : List NodeSpec := [([(1,2,0),(3,3,1),(3,3,5)],[6,7,0,1,2,4],[(4,[])]),([(1,2,0),(1,3,2),(3,3,5)],[7,0,1,5,6,4],[(1,[])]),([(1,2,0),(1,3,2),(0,6,0)],[7,1,5,3,6,4],[]),([(1,2,0),(1,3,2),(2,6,0)],[7,1,5,3,6,4],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q35 : ck33 [] d35 = true := by decide +kernel
private def lv_0_32_5_3 : List NodeSpec := (d33 ++ (d34 ++ d35))

private theorem ok_0_32_5_3 : LevelOK rd_0_32 (subGoal 0 32) 5 lv_0_32_5_3 := by
  have go {ids ds} (h : ck33 ids ds = true) : LevelOK rd_0_32 (subGoal 0 32) 5 ds :=
    levelCheck_sound pp_0_32 (raw_faithful _ _ _) sl_0_32_ok autos_0_32_ok (selectPrevOK ids ok_0_32_4) h
  exact (levelOK_append (go q33) (levelOK_append (go q34) (go q35)))
private def ck36 (ids : List Nat) := levelCheck (freeVars 0 32) rd_0_32 (subGoal 0 32) sl_0_32 autos_0_32 (selectPrev ids lv_0_32_4) 5
private def d36 : List NodeSpec := [([(1,2,0),(1,3,2),(1,4,5)],[0,1,3,6,4,7],[(1,[])]),([(1,2,0),(1,3,2),(3,4,5)],[7,0,1,3,6,4],[(1,[]),(1,[0,2])]),([(1,2,0),(1,3,2),(1,4,3)],[0,1,5,6,4,7],[]),([(1,2,0),(1,3,2),(1,4,6)],[0,1,5,3,4,7],[(3,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q36 : ck36 [11,12,13] d36 = true := by decide +kernel
private def d37 : List NodeSpec := [([(1,2,0),(1,3,2),(3,4,6)],[7,0,1,5,3,4],[]),([(1,2,0),(1,3,5),(2,6,0)],[7,1,2,3,6,4],[(0,[])]),([(1,2,0),(1,3,5),(2,6,0)],[7,0,1,2,3,4],[]),([(1,2,0),(1,3,5),(0,6,1)],[0,7,2,3,4],[(0,[1,2]),(1,[0,2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q37 : ck36 [12] d37 = true := by decide +kernel
private def d38 : List NodeSpec := [([(1,2,0),(1,3,5),(0,6,1)],[0,7,2,3,6,4],[(4,[])]),([(1,2,0),(1,3,5),(0,6,1)],[0,7,1,2,3,4],[]),([(1,2,0),(1,3,5),(2,6,1)],[7,0,2,3,6,4],[]),([(1,2,0),(1,3,5),(2,6,2)],[7,0,1,3,6,4],[(0,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q38 : ck36 [3,14,15,16,17,18,19] d38 = true := by decide +kernel
private def lv_0_32_5_4 : List NodeSpec := (d36 ++ (d37 ++ d38))

private theorem ok_0_32_5_4 : LevelOK rd_0_32 (subGoal 0 32) 5 lv_0_32_5_4 := by
  have go {ids ds} (h : ck36 ids ds = true) : LevelOK rd_0_32 (subGoal 0 32) 5 ds :=
    levelCheck_sound pp_0_32 (raw_faithful _ _ _) sl_0_32_ok autos_0_32_ok (selectPrevOK ids ok_0_32_4) h
  exact (levelOK_append (go q36) (levelOK_append (go q37) (go q38)))
private def ck39 (ids : List Nat) := levelCheck (freeVars 0 32) rd_0_32 (subGoal 0 32) sl_0_32 autos_0_32 (selectPrev ids lv_0_32_4) 5
private def d39 : List NodeSpec := [([(1,2,0),(1,3,5),(0,4,6)],[0,1,2,3,7,6],[]),([(1,2,0),(1,3,5),(1,4,6)],[0,1,2,3,4,7],[(4,[])]),([(1,2,0),(1,3,5),(3,4,6)],[7,0,1,2,3],[]),([(1,2,0),(1,3,5),(3,4,6)],[7,0,1,2,3,4],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q39 : ck39 [15,17,19,20,21] d39 = true := by decide +kernel
private def d40 : List NodeSpec := [([(1,2,0),(1,3,5),(3,4,6)],[7,0,1,2,3,6],[(2,[])]),([(1,2,0),(1,3,5),(2,6,0)],[7,1,2,5,3,4],[(0,[])]),([(1,2,0),(1,3,5),(0,6,1)],[0,7,2,5,3,4],[(1,[0,2])]),([(1,2,0),(1,3,5),(3,4,6)],[7,0,1,2,5,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q40 : ck39 [14,16,18] d40 = true := by decide +kernel
private def d41 : List NodeSpec := [([(1,2,0),(3,3,5),(2,1,6)],[0,7,1,2,3,4],[]),([(1,2,0),(3,3,5),(1,4,6)],[0,1,2,3,4,7],[]),([(1,2,0),(3,3,5),(3,4,6)],[7,0,1,2,3,4],[(1,[0,2])]),([(1,2,0),(1,4,3),(0,6,5)],[0,1,2,7,3,4],[(1,[]),(1,[0,2]),(2,[]),(3,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q41 : ck39 [13,20] d41 = true := by decide +kernel
private def lv_0_32_5_5 : List NodeSpec := (d39 ++ (d40 ++ d41))

private theorem ok_0_32_5_5 : LevelOK rd_0_32 (subGoal 0 32) 5 lv_0_32_5_5 := by
  have go {ids ds} (h : ck39 ids ds = true) : LevelOK rd_0_32 (subGoal 0 32) 5 ds :=
    levelCheck_sound pp_0_32 (raw_faithful _ _ _) sl_0_32_ok autos_0_32_ok (selectPrevOK ids ok_0_32_4) h
  exact (levelOK_append (go q39) (levelOK_append (go q40) (go q41)))
private def ck42 (ids : List Nat) := levelCheck (freeVars 0 32) rd_0_32 (subGoal 0 32) sl_0_32 autos_0_32 (selectPrev ids lv_0_32_4) 5
private def d42 : List NodeSpec := [([(1,2,0),(1,4,3),(2,6,5)],[7,0,1,2,3,4],[]),([(3,2,0),(1,3,5),(1,4,3)],[0,1,2,6,4,7],[(2,[])]),([(3,2,0),(1,3,5),(1,4,6)],[0,1,2,3,4,7],[(4,[])]),([(3,2,0),(1,3,5),(3,4,6)],[7,0,1,2,3,4],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q42 : ck42 [20,22] d42 = true := by decide +kernel
private def d43 : List NodeSpec := [([(3,2,0),(1,4,3),(2,6,5)],[0,1,2,7,3,4],[]),([(3,2,0),(1,4,3),(2,6,2)],[5,7,0,1,3,4],[]),([(1,2,1),(3,3,5),(1,4,6)],[0,1,2,3,4,7],[]),([(1,2,1),(3,3,5),(3,4,6)],[7,0,1,2,3,4],[(0,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q43 : ck42 [20,23] d43 = true := by decide +kernel
private def d44 : List NodeSpec := [([(1,2,1),(3,3,5),(1,4,3)],[6,0,1,2,4,7],[(2,[])]),([(1,2,1),(1,4,3),(0,6,1)],[0,7,2,5,3,4],[]),([(1,2,1),(1,4,3),(2,6,2)],[7,0,1,5,3,4],[]),([(1,2,1),(1,4,3),(0,6,5)],[0,1,2,7,3,4],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q44 : ck42 [23] d44 = true := by decide +kernel
private def lv_0_32_5_6 : List NodeSpec := (d42 ++ (d43 ++ d44))

private theorem ok_0_32_5_6 : LevelOK rd_0_32 (subGoal 0 32) 5 lv_0_32_5_6 := by
  have go {ids ds} (h : ck42 ids ds = true) : LevelOK rd_0_32 (subGoal 0 32) 5 ds :=
    levelCheck_sound pp_0_32 (raw_faithful _ _ _) sl_0_32_ok autos_0_32_ok (selectPrevOK ids ok_0_32_4) h
  exact (levelOK_append (go q42) (levelOK_append (go q43) (go q44)))
private def ck45 (ids : List Nat) := levelCheck (freeVars 0 32) rd_0_32 (subGoal 0 32) sl_0_32 autos_0_32 (selectPrev ids lv_0_32_4) 5
private def d45 : List NodeSpec := [([(3,2,1),(1,0,5),(3,3,6)],[7,0,1,2,3,4],[]),([(3,2,1),(1,0,5),(1,3,2)],[0,6,1,3,7,4],[(1,[])]),([(3,2,1),(3,0,5),(2,1,6)],[5,0,7,2,3,4],[(0,[])]),([(3,2,1),(1,3,5),(3,3,1)],[7,0,1,2,6,4],[(0,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q45 : ck45 [] d45 = true := by decide +kernel
private def d46 : List NodeSpec := [([(3,2,1),(1,3,5),(2,6,0)],[7,0,1,2,3,4],[]),([(3,2,1),(1,3,5),(2,6,3)],[7,0,1,2,6,4],[(0,[]),(2,[0,1])]),([(3,2,1),(1,3,5),(1,4,2)],[0,1,3,6,4,7],[(2,[]),(2,[0,1])]),([(3,2,1),(1,3,5),(1,4,6)],[0,1,2,3,4,7],[(0,[]),(1,[0,2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q46 : ck45 [24] d46 = true := by decide +kernel
private def d47 : List NodeSpec := [([(3,2,1),(1,3,5),(3,4,6)],[7,0,1,2,3,4],[]),([(3,2,1),(1,3,5),(1,3,2)],[5,0,1,6,7,4],[(1,[])]),([(3,2,1),(3,3,5),(1,0,6)],[0,7,1,2,3,4],[]),([(3,2,1),(3,3,5),(2,1,6)],[0,7,1,2,3,4],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q47 : ck45 [23] d47 = true := by decide +kernel
private def lv_0_32_5_7 : List NodeSpec := (d45 ++ (d46 ++ d47))

private theorem ok_0_32_5_7 : LevelOK rd_0_32 (subGoal 0 32) 5 lv_0_32_5_7 := by
  have go {ids ds} (h : ck45 ids ds = true) : LevelOK rd_0_32 (subGoal 0 32) 5 ds :=
    levelCheck_sound pp_0_32 (raw_faithful _ _ _) sl_0_32_ok autos_0_32_ok (selectPrevOK ids ok_0_32_4) h
  exact (levelOK_append (go q45) (levelOK_append (go q46) (go q47)))
private def ck48 (ids : List Nat) := levelCheck (freeVars 0 32) rd_0_32 (subGoal 0 32) sl_0_32 autos_0_32 (selectPrev ids lv_0_32_4) 5
private def d48 : List NodeSpec := [([(3,2,1),(3,3,5),(2,1,6)],[6,0,7,2,3,4],[(0,[])]),([(3,2,1),(3,3,5),(1,4,6)],[0,1,2,3,7],[]),([(3,2,1),(3,3,5),(1,4,6)],[0,1,2,3,4,7],[]),([(3,2,1),(3,3,5),(1,4,6)],[6,0,1,2,3,7],[(2,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q48 : ck48 [5,8,24,25] d48 = true := by decide +kernel
private def d49 : List NodeSpec := [([(3,2,1),(3,3,5),(2,4,6)],[6,0,1,2,3,7],[]),([(3,2,1),(3,3,5),(3,4,6)],[7,0,1,2,3,4],[]),([(3,2,1),(3,3,5),(1,4,2)],[6,0,1,3,4,7],[(2,[])]),([(3,2,1),(3,3,5),(2,1,6)],[5,0,7,2,3,4],[(0,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q49 : ck48 [23,24,26,27] d49 = true := by decide +kernel
private def d50 : List NodeSpec := [([(3,2,1),(3,3,5),(1,4,6)],[5,0,1,2,3,7],[]),([(3,2,1),(3,3,1),(1,3,2)],[6,5,0,1,7,4],[(0,[]),(1,[])]),([(3,2,1),(1,3,2),(0,6,1)],[5,0,7,3,6,4],[]),([(3,2,1),(1,3,2),(2,6,1)],[5,7,0,3,6,4],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q50 : ck48 [] d50 = true := by decide +kernel
private def lv_0_32_5_8 : List NodeSpec := (d48 ++ (d49 ++ d50))

private theorem ok_0_32_5_8 : LevelOK rd_0_32 (subGoal 0 32) 5 lv_0_32_5_8 := by
  have go {ids ds} (h : ck48 ids ds = true) : LevelOK rd_0_32 (subGoal 0 32) 5 ds :=
    levelCheck_sound pp_0_32 (raw_faithful _ _ _) sl_0_32_ok autos_0_32_ok (selectPrevOK ids ok_0_32_4) h
  exact (levelOK_append (go q48) (levelOK_append (go q49) (go q50)))
private def ck51 (ids : List Nat) := levelCheck (freeVars 0 32) rd_0_32 (subGoal 0 32) sl_0_32 autos_0_32 (selectPrev ids lv_0_32_4) 5
private def d51 : List NodeSpec := [([(3,2,1),(1,3,2),(1,4,3)],[5,0,1,6,4,7],[]),([(3,2,1),(1,3,2),(1,4,6)],[5,0,1,3,4,7],[(4,[])]),([(3,2,1),(1,3,2),(3,4,6)],[7,5,0,1,3,4],[]),([(3,2,1),(1,4,3),(0,6,5)],[7,0,1,2,3,4],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q51 : ck51 [27,28,29] d51 = true := by decide +kernel
private def d52 : List NodeSpec := [([(3,2,1),(1,4,3),(2,6,5)],[0,1,2,7,3,4],[(1,[]),(1,[0,2]),(2,[]),(4,[])]),([(3,2,1),(1,4,3),(0,6,1)],[5,0,7,2,3,4],[(0,[])]),([(1,3,2),(0,5,0),(1,1,6)],[0,7,2,3,5,4],[(0,[1,2])]),([(1,3,2),(0,5,0),(2,1,6)],[7,0,2,3,5,4],[(0,[1,2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q52 : ck51 [28,29] d52 = true := by decide +kernel
private def d53 : List NodeSpec := [([(1,3,2),(0,5,0),(1,5,0)],[6,1,2,3,7,4],[]),([(1,3,2),(0,5,0),(1,4,6)],[0,1,2,3,5,7],[(0,[1,2])]),([(1,3,2),(1,5,0),(0,6,1)],[0,7,2,3,5,4],[(0,[1,2])]),([(1,3,2),(1,5,0),(2,6,1)],[7,0,2,3,5,4],[(0,[1,2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q53 : ck51 [30] d53 = true := by decide +kernel
private def lv_0_32_5_9 : List NodeSpec := (d51 ++ (d52 ++ d53))

private theorem ok_0_32_5_9 : LevelOK rd_0_32 (subGoal 0 32) 5 lv_0_32_5_9 := by
  have go {ids ds} (h : ck51 ids ds = true) : LevelOK rd_0_32 (subGoal 0 32) 5 ds :=
    levelCheck_sound pp_0_32 (raw_faithful _ _ _) sl_0_32_ok autos_0_32_ok (selectPrevOK ids ok_0_32_4) h
  exact (levelOK_append (go q51) (levelOK_append (go q52) (go q53)))
private def ck54 (ids : List Nat) := levelCheck (freeVars 0 32) rd_0_32 (subGoal 0 32) sl_0_32 autos_0_32 (selectPrev ids lv_0_32_4) 5
private def d54 : List NodeSpec := [([(1,3,2),(1,5,0),(2,6,2)],[7,0,1,3,5,4],[(0,[])]),([(1,3,2),(1,5,0),(3,4,6)],[7,0,1,2,3,5],[(0,[1,2])]),([(1,3,2),(2,5,0),(1,0,6)],[0,1,2,3,7,4],[(2,[]),(4,[])]),([(1,3,2),(2,5,0),(2,1,6)],[7,0,1,2,3,4],[(0,[]),(1,[]),(2,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q54 : ck54 [3,20,31] d54 = true := by decide +kernel
private def d55 : List NodeSpec := [([(1,3,2),(2,5,0),(1,4,6)],[0,1,2,3,4,7],[]),([(1,3,2),(2,5,0),(1,4,2)],[6,0,1,3,4,7],[(2,[])]),([(1,3,2),(2,5,0),(3,5,0)],[7,6,1,2,3,4],[]),([(1,3,2),(3,5,0),(1,2,6)],[0,1,7,3,5,4],[(0,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q55 : ck54 [30,32] d55 = true := by decide +kernel
private def d56 : List NodeSpec := [([(1,3,2),(0,5,1),(1,6,0)],[0,1,7,2,3,4],[(0,[]),(1,[]),(2,[])]),([(1,3,2),(0,5,1),(2,1,6)],[7,0,1,2,3,4],[(2,[])]),([(1,3,2),(0,5,1),(1,4,6)],[0,1,2,3,4,7],[]),([(1,3,2),(0,5,1),(1,4,2)],[0,6,1,3,4,7],[(2,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q56 : ck54 [3,23,29,33,34] d56 = true := by decide +kernel
private def lv_0_32_5_10 : List NodeSpec := (d54 ++ (d55 ++ d56))

private theorem ok_0_32_5_10 : LevelOK rd_0_32 (subGoal 0 32) 5 lv_0_32_5_10 := by
  have go {ids ds} (h : ck54 ids ds = true) : LevelOK rd_0_32 (subGoal 0 32) 5 ds :=
    levelCheck_sound pp_0_32 (raw_faithful _ _ _) sl_0_32_ok autos_0_32_ok (selectPrevOK ids ok_0_32_4) h
  exact (levelOK_append (go q54) (levelOK_append (go q55) (go q56)))
private def ck57 (ids : List Nat) := levelCheck (freeVars 0 32) rd_0_32 (subGoal 0 32) sl_0_32 autos_0_32 (selectPrev ids lv_0_32_4) 5
private def d57 : List NodeSpec := [([(1,3,2),(0,5,1),(1,5,1)],[0,6,2,3,7,4],[(0,[1,2])]),([(1,3,2),(1,5,1),(2,6,2)],[7,0,1,3,5,4],[(0,[])]),([(1,3,2),(2,5,1),(3,5,1)],[7,6,0,2,3,4],[]),([(1,3,2),(2,5,1),(1,4,6)],[0,1,2,3,5,7],[(0,[1,2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q57 : ck57 [35,36] d57 = true := by decide +kernel
private def d58 : List NodeSpec := [([(1,3,2),(3,5,1),(1,2,6)],[0,1,7,3,5,4],[(0,[])]),([(1,3,2),(3,5,1),(1,4,6)],[0,1,2,3,5,7],[(0,[1,2])]),([(1,3,2),(1,4,2),(1,4,3)],[0,1,5,6,7],[(0,[]),(0,[2]),(1,[]),(1,[1]),(2,[])]),([(1,3,2),(1,4,2),(3,4,5)],[7,0,1,3,5,6],[(0,[]),(2,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q58 : ck57 [11,24,25,27,32,34,36] d58 = true := by decide +kernel
private def d59 : List NodeSpec := [([(1,3,2),(1,4,5),(2,6,0)],[7,0,1,2,3,4],[]),([(1,3,2),(1,4,5),(0,6,1)],[0,7,1,2,3,4],[]),([(1,3,2),(1,4,5),(2,6,2)],[7,0,1,3,4,6],[(0,[])]),([(1,3,2),(1,4,5),(2,6,2)],[7,0,1,3,5,4],[(0,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q59 : ck57 [] d59 = true := by decide +kernel
private def lv_0_32_5_11 : List NodeSpec := (d57 ++ (d58 ++ d59))

private theorem ok_0_32_5_11 : LevelOK rd_0_32 (subGoal 0 32) 5 lv_0_32_5_11 := by
  have go {ids ds} (h : ck57 ids ds = true) : LevelOK rd_0_32 (subGoal 0 32) 5 ds :=
    levelCheck_sound pp_0_32 (raw_faithful _ _ _) sl_0_32_ok autos_0_32_ok (selectPrevOK ids ok_0_32_4) h
  exact (levelOK_append (go q57) (levelOK_append (go q58) (go q59)))
private def lv_0_32_5_12 : List NodeSpec := [([(1, 3, 2), (3, 4, 5), (1, 0, 6)], [0, 7, 1, 2, 3, 4], []), ([(1, 3, 2), (3, 4, 5), (2, 1, 6)], [0, 7, 1, 2, 3, 4], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_0_32_5_12 : LevelOK rd_0_32 (subGoal 0 32) 5 lv_0_32_5_12 :=
  levelCheck_sound pp_0_32 (raw_faithful _ _ _) sl_0_32_ok autos_0_32_ok (selectPrevOK [20,23] ok_0_32_4)
    (by decide +kernel : levelCheck (freeVars 0 32) rd_0_32 (subGoal 0 32) sl_0_32 autos_0_32 (selectPrev [20,23] lv_0_32_4) 5 lv_0_32_5_12 = true)
private def lv_0_32_5 : List NodeSpec := (((lv_0_32_5_0 ++ (lv_0_32_5_1 ++ lv_0_32_5_2)) ++ (lv_0_32_5_3 ++ (lv_0_32_5_4 ++ lv_0_32_5_5))) ++ ((lv_0_32_5_6 ++ (lv_0_32_5_7 ++ lv_0_32_5_8)) ++ ((lv_0_32_5_9 ++ lv_0_32_5_10) ++ (lv_0_32_5_11 ++ lv_0_32_5_12))))
private theorem ok_0_32_5 : LevelOK rd_0_32 (subGoal 0 32) 5 lv_0_32_5 := (levelOK_append (levelOK_append (levelOK_append ok_0_32_5_0 (levelOK_append ok_0_32_5_1 ok_0_32_5_2)) (levelOK_append ok_0_32_5_3 (levelOK_append ok_0_32_5_4 ok_0_32_5_5))) (levelOK_append (levelOK_append ok_0_32_5_6 (levelOK_append ok_0_32_5_7 ok_0_32_5_8)) (levelOK_append (levelOK_append ok_0_32_5_9 ok_0_32_5_10) (levelOK_append ok_0_32_5_11 ok_0_32_5_12))))
private def ck60 (ids : List Nat) := levelCheck (freeVars 0 32) rd_0_32 (subGoal 0 32) sl_0_32 autos_0_32 (selectPrev ids lv_0_32_5) 6
private def d60 : List NodeSpec := [([(0,1,0),(1,2,5)],[0,1,6,3,4],[(0,[0]),(1,[0,1]),(2,[0,1]),(3,[]),(4,[1]),(5,[])]),([(0,1,0),(1,2,5)],[0,1,2,6,3,4],[(0,[]),(0,[0]),(1,[]),(1,[0,1]),(2,[]),(2,[0,1]),(3,[]),(4,[1]),(5,[])]),([(0,1,0),(1,3,2)],[5,0,1,2,3,6,4],[(0,[]),(0,[0]),(1,[]),(2,[1]),(3,[]),(4,[])]),([(1,1,0),(3,2,1)],[6,0,5,2,3,4],[(0,[]),(0,[0]),(3,[]),(3,[1]),(4,[]),(5,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q60 : ck60 [0,1,2,3,4,5,6,7,8,9,10,11] d60 = true := by decide +kernel
private def d61 : List NodeSpec := [([(1,1,0),(3,2,5)],[6,0,1,3,4],[(0,[0]),(1,[0,1]),(2,[0,1]),(3,[1]),(4,[]),(5,[])]),([(1,1,0),(3,2,5)],[6,0,1,2,3,4],[(0,[]),(0,[0]),(1,[]),(1,[0,1]),(2,[]),(2,[0,1]),(3,[]),(3,[1]),(4,[]),(5,[])]),([(1,1,0),(1,3,2)],[0,1,5,2,3,6,4],[(0,[]),(0,[0]),(1,[]),(2,[1]),(4,[])]),([(2,1,0),(3,2,5)],[6,0,1,2,3,4],[(0,[0]),(1,[]),(2,[]),(3,[1]),(4,[1]),(5,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q61 : ck60 [10,11,12,13,14,15,16,17,18,19,20,21,22,23] d61 = true := by decide +kernel
private def d62 : List NodeSpec := [([(2,1,0),(3,2,1)],[6,5,0,2,3,4],[(0,[]),(0,[0]),(3,[]),(3,[1]),(4,[]),(5,[])]),([(2,1,0),(1,3,2)],[5,0,1,2,3,6,4],[(0,[]),(0,[0]),(1,[]),(4,[]),(5,[])]),([(3,1,0),(1,2,5)],[0,1,2,6,3,4],[(0,[]),(0,[0]),(1,[]),(2,[]),(3,[]),(4,[])]),([(3,1,0),(1,3,2)],[5,0,1,2,3,6,4],[(0,[]),(0,[0]),(1,[]),(3,[]),(4,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q62 : ck60 [22,23,24,25,26,27,28,29,30,31,32,33] d62 = true := by decide +kernel
private def lv_0_32_6_0 : List NodeSpec := (d60 ++ (d61 ++ d62))

private theorem ok_0_32_6_0 : LevelOK rd_0_32 (subGoal 0 32) 6 lv_0_32_6_0 := by
  have go {ids ds} (h : ck60 ids ds = true) : LevelOK rd_0_32 (subGoal 0 32) 6 ds :=
    levelCheck_sound pp_0_32 (raw_faithful _ _ _) sl_0_32_ok autos_0_32_ok (selectPrevOK ids ok_0_32_5) h
  exact (levelOK_append (go q60) (levelOK_append (go q61) (go q62)))
private def ck63 (ids : List Nat) := levelCheck (freeVars 0 32) rd_0_32 (subGoal 0 32) sl_0_32 autos_0_32 (selectPrev ids lv_0_32_5) 6
private def d63 : List NodeSpec := [([(1,2,0),(0,5,1)],[0,6,1,2,3,4],[(0,[]),(0,[1]),(1,[]),(1,[0,1]),(2,[]),(2,[0,1]),(3,[]),(3,[1]),(4,[0]),(5,[])]),([(1,2,0),(0,5,1)],[0,6,1,2,5,3,4],[(0,[]),(3,[]),(3,[1]),(4,[]),(5,[])]),([(1,2,0),(3,5,1)],[6,0,1,2,5,3,4],[(3,[1]),(4,[]),(5,[])]),([(1,2,0),(1,3,0)],[0,1,2,5,3,6,4],[(0,[]),(0,[1]),(1,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q63 : ck63 [20,34,35,36,37,38,39] d63 = true := by decide +kernel
private def d64 : List NodeSpec := [([(1,2,0),(3,3,1)],[6,0,1,2,5,3,4],[(0,[]),(1,[])]),([(1,2,0),(1,3,2)],[0,1,5,3,6,4],[(0,[]),(1,[]),(1,[0]),(3,[]),(4,[0])]),([(1,2,0),(1,3,5)],[0,1,2,3,6,4],[(0,[1]),(1,[0]),(2,[]),(4,[])]),([(1,2,0),(1,3,5)],[0,1,2,5,3,6,4],[(1,[]),(1,[0]),(2,[0]),(5,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q64 : ck63 [22,23,35,36,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67] d64 = true := by decide +kernel
private def d65 : List NodeSpec := [([(1,2,0),(3,3,5)],[6,0,1,2,3,4],[(0,[]),(0,[1]),(1,[]),(1,[0]),(2,[]),(2,[0,1]),(4,[])]),([(1,2,0),(3,3,5)],[6,0,1,2,5,3,4],[(0,[]),(1,[]),(1,[0]),(3,[])]),([(1,2,0),(1,4,3)],[0,1,2,5,3,4,6],[(0,[]),(1,[]),(1,[0]),(2,[])]),([(3,2,0),(1,3,5)],[0,1,2,3,6,4],[(0,[]),(0,[1]),(1,[]),(1,[0]),(2,[]),(3,[]),(4,[]),(5,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q65 : ck63 [35,39,44,45,48,49,50,51,59,61,68,69,70,71,72,73,74,75] d65 = true := by decide +kernel
private def lv_0_32_6_1 : List NodeSpec := (d63 ++ (d64 ++ d65))

private theorem ok_0_32_6_1 : LevelOK rd_0_32 (subGoal 0 32) 6 lv_0_32_6_1 := by
  have go {ids ds} (h : ck63 ids ds = true) : LevelOK rd_0_32 (subGoal 0 32) 6 ds :=
    levelCheck_sound pp_0_32 (raw_faithful _ _ _) sl_0_32_ok autos_0_32_ok (selectPrevOK ids ok_0_32_5) h
  exact (levelOK_append (go q63) (levelOK_append (go q64) (go q65)))
private def ck66 (ids : List Nat) := levelCheck (freeVars 0 32) rd_0_32 (subGoal 0 32) sl_0_32 autos_0_32 (selectPrev ids lv_0_32_5) 6
private def d66 : List NodeSpec := [([(3,2,0),(1,4,3)],[5,0,1,2,3,4,6],[(0,[]),(1,[]),(1,[0]),(2,[]),(3,[])]),([(1,2,1),(3,3,5)],[6,0,1,2,3,4],[(0,[]),(0,[1]),(1,[]),(1,[0]),(2,[]),(3,[]),(4,[]),(5,[])]),([(1,2,1),(1,4,3)],[0,1,2,5,3,4,6],[(0,[]),(1,[]),(1,[0]),(2,[]),(4,[])]),([(3,2,1),(1,0,5)],[0,6,1,2,3,4],[(0,[]),(0,[1]),(1,[]),(2,[]),(3,[]),(3,[0]),(4,[]),(4,[1]),(5,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q66 : ck66 [19,41,73,74,76,77,78,79,80,81,82,83,84,85] d66 = true := by decide +kernel
private def d67 : List NodeSpec := [([(3,2,1),(1,0,5)],[5,0,6,1,2,3,4],[(0,[]),(0,[1]),(3,[]),(4,[]),(4,[1]),(5,[])]),([(3,2,1),(3,0,5)],[6,5,0,1,2,3,4],[(3,[]),(4,[1]),(5,[])]),([(3,2,1),(1,3,5)],[0,1,2,3,6,4],[(0,[]),(0,[1]),(1,[]),(1,[0]),(2,[]),(2,[0,1]),(3,[])]),([(3,2,1),(1,3,5)],[5,0,1,2,3,6,4],[(0,[]),(1,[]),(1,[0]),(4,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q67 : ck66 [9,19,24,25,40,41,86,87,88,89,90,91,92,93] d67 = true := by decide +kernel
private def d68 : List NodeSpec := [([(3,2,1),(3,3,5)],[6,0,1,2,3,4],[(0,[1]),(1,[0]),(2,[]),(3,[])]),([(3,2,1),(3,3,5)],[6,5,0,1,2,3,4],[(1,[]),(1,[0]),(2,[0])]),([(3,2,1),(3,3,1)],[6,5,0,1,2,3,4],[(0,[]),(0,[1]),(1,[])]),([(3,2,1),(1,3,2)],[5,0,1,3,6,4],[(0,[]),(1,[]),(1,[0]),(3,[0]),(4,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q68 : ck66 [10,11,22,23,26,27,43,85,87,89,90,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110] d68 = true := by decide +kernel
private def lv_0_32_6_2 : List NodeSpec := (d66 ++ (d67 ++ d68))

private theorem ok_0_32_6_2 : LevelOK rd_0_32 (subGoal 0 32) 6 lv_0_32_6_2 := by
  have go {ids ds} (h : ck66 ids ds = true) : LevelOK rd_0_32 (subGoal 0 32) 6 ds :=
    levelCheck_sound pp_0_32 (raw_faithful _ _ _) sl_0_32_ok autos_0_32_ok (selectPrevOK ids ok_0_32_5) h
  exact (levelOK_append (go q66) (levelOK_append (go q67) (go q68)))
private def ck69 (ids : List Nat) := levelCheck (freeVars 0 32) rd_0_32 (subGoal 0 32) sl_0_32 autos_0_32 (selectPrev ids lv_0_32_5) 6
private def d69 : List NodeSpec := [([(3,2,1),(1,4,3)],[5,0,1,2,3,4,6],[(0,[]),(1,[]),(1,[0]),(2,[]),(4,[])]),([(1,3,2),(0,5,0)],[6,0,1,2,3,5,4],[(0,[]),(0,[1]),(1,[]),(2,[0]),(3,[])]),([(1,3,2),(1,5,0)],[0,1,2,3,5,6,4],[(0,[1]),(2,[0]),(3,[])]),([(1,3,2),(2,5,0)],[6,0,1,2,3,4],[(0,[]),(0,[1]),(1,[]),(1,[1]),(2,[]),(4,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q69 : ck69 [28,46,53,54,72,91,101,102,108,109,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125] d69 = true := by decide +kernel
private def d70 : List NodeSpec := [([(1,3,2),(2,5,0)],[6,0,1,2,3,5,4],[(0,[]),(0,[1]),(1,[]),(3,[])]),([(1,3,2),(3,5,0)],[6,0,1,2,3,5,4],[(0,[1]),(3,[])]),([(1,3,2),(0,5,1)],[0,6,1,2,3,4],[(0,[]),(0,[1]),(1,[]),(1,[1]),(2,[]),(3,[])]),([(1,3,2),(0,5,1)],[0,6,1,2,3,5,4],[(0,[]),(0,[1]),(1,[]),(4,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q70 : ck69 [7,28,33,47,53,81,96,106,111,113,122,126,127,128,129,130,131,132] d70 = true := by decide +kernel
private def d71 : List NodeSpec := [([(1,3,2),(1,5,1)],[0,1,2,3,5,6,4],[(0,[1]),(4,[])]),([(1,3,2),(2,5,1)],[6,0,1,2,3,5,4],[(0,[]),(0,[1]),(1,[]),(2,[0]),(4,[])]),([(1,3,2),(3,5,1)],[6,0,1,2,3,5,4],[(0,[1]),(2,[0]),(4,[])]),([(1,3,2),(1,4,2)],[0,1,3,5,4,6],[(0,[]),(1,[]),(1,[1]),(2,[]),(2,[0])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q71 : ck69 [48,50,95,96,102,107,108,125,129,131,132,133,134,135,136,137,138,139] d71 = true := by decide +kernel
private def lv_0_32_6_3 : List NodeSpec := (d69 ++ (d70 ++ d71))

private theorem ok_0_32_6_3 : LevelOK rd_0_32 (subGoal 0 32) 6 lv_0_32_6_3 := by
  have go {ids ds} (h : ck69 ids ds = true) : LevelOK rd_0_32 (subGoal 0 32) 6 ds :=
    levelCheck_sound pp_0_32 (raw_faithful _ _ _) sl_0_32_ok autos_0_32_ok (selectPrevOK ids ok_0_32_5) h
  exact (levelOK_append (go q69) (levelOK_append (go q70) (go q71)))
private def lv_0_32_6_4 : List NodeSpec := [([(1, 3, 2), (1, 4, 5)], [0, 1, 2, 3, 4, 6], [(0, [1]), (1, [1]), (2, [0]), (3, []), (4, [])]), ([(1, 3, 2), (1, 4, 5)], [0, 1, 2, 3, 5, 4, 6], [(0, [1]), (2, []), (2, [0])]), ([(1, 3, 2), (3, 4, 5)], [6, 0, 1, 2, 3, 4], [(0, []), (0, [1]), (1, []), (1, [1]), (2, [0]), (3, []), (4, [])]), ([(1, 3, 2), (3, 4, 5)], [6, 0, 1, 2, 3, 5, 4], [(0, []), (0, [1]), (1, []), (2, []), (2, [0])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_0_32_6_4 : LevelOK rd_0_32 (subGoal 0 32) 6 lv_0_32_6_4 :=
  levelCheck_sound pp_0_32 (raw_faithful _ _ _) sl_0_32_ok autos_0_32_ok (selectPrevOK [51,52,61,72,77,82,101,109,110,111,139,140,141,142,143,144,145] ok_0_32_5)
    (by decide +kernel : levelCheck (freeVars 0 32) rd_0_32 (subGoal 0 32) sl_0_32 autos_0_32 (selectPrev [51,52,61,72,77,82,101,109,110,111,139,140,141,142,143,144,145] lv_0_32_5) 6 lv_0_32_6_4 = true)
private def lv_0_32_6 : List NodeSpec := ((lv_0_32_6_0 ++ lv_0_32_6_1) ++ (lv_0_32_6_2 ++ (lv_0_32_6_3 ++ lv_0_32_6_4)))
private theorem ok_0_32_6 : LevelOK rd_0_32 (subGoal 0 32) 6 lv_0_32_6 := (levelOK_append (levelOK_append ok_0_32_6_0 ok_0_32_6_1) (levelOK_append ok_0_32_6_2 (levelOK_append ok_0_32_6_3 ok_0_32_6_4)))
private def ck72 (ids : List Nat) := levelCheck (freeVars 0 32) rd_0_32 (subGoal 0 32) sl_0_32 autos_0_32 (selectPrev ids lv_0_32_6) 7
private def d72 : List NodeSpec := [([(0,1,0)],[5,0,1,2,3,4],[(0,[]),(0,[0]),(1,[]),(1,[0]),(2,[]),(2,[0]),(3,[]),(4,[]),(5,[])]),([(1,1,0)],[0,1,5,2,3,4],[(0,[]),(0,[0]),(1,[]),(1,[0]),(2,[]),(2,[0]),(3,[]),(4,[]),(5,[])]),([(2,1,0)],[5,0,1,2,3,4],[(0,[]),(0,[0]),(1,[]),(1,[0]),(2,[]),(2,[0]),(3,[]),(4,[]),(5,[])]),([(3,1,0)],[5,0,1,2,3,4],[(0,[]),(0,[0]),(1,[]),(1,[0]),(2,[]),(2,[0]),(3,[]),(4,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q72 : ck72 [0,1,2,3,4,5,6,7,8,9,10,11] d72 = true := by decide +kernel
private def d73 : List NodeSpec := [([(1,2,0)],[0,1,2,5,3,4],[(0,[]),(1,[]),(1,[0]),(2,[]),(2,[0]),(3,[]),(4,[]),(5,[])]),([(3,2,0)],[5,0,1,2,3,4],[(0,[]),(1,[]),(1,[0]),(2,[]),(2,[0]),(3,[]),(4,[]),(5,[])]),([(1,2,1)],[0,1,2,5,3,4],[(0,[]),(1,[]),(1,[0]),(2,[]),(2,[0]),(3,[]),(4,[]),(5,[])]),([(3,2,1)],[5,0,1,2,3,4],[(0,[]),(1,[]),(1,[0]),(2,[]),(2,[0]),(3,[]),(4,[]),(5,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q73 : ck72 [3,7,8,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36] d73 = true := by decide +kernel
private def d74 : List NodeSpec := [([(1,3,2)],[0,1,2,3,5,4],[(0,[]),(1,[]),(2,[]),(2,[0]),(3,[]),(4,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q74 : ck72 [2,6,9,11,17,18,22,24,26,32,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51] d74 = true := by decide +kernel
private def lv_0_32_7_0 : List NodeSpec := (d72 ++ (d73 ++ d74))

private theorem ok_0_32_7_0 : LevelOK rd_0_32 (subGoal 0 32) 7 lv_0_32_7_0 := by
  have go {ids ds} (h : ck72 ids ds = true) : LevelOK rd_0_32 (subGoal 0 32) 7 ds :=
    levelCheck_sound pp_0_32 (raw_faithful _ _ _) sl_0_32_ok autos_0_32_ok (selectPrevOK ids ok_0_32_6) h
  exact (levelOK_append (go q72) (levelOK_append (go q73) (go q74)))
private def lv_0_32_7 : List NodeSpec := lv_0_32_7_0
private theorem ok_0_32_7 : LevelOK rd_0_32 (subGoal 0 32) 7 lv_0_32_7 := ok_0_32_7_0
private def lv_0_32_8_0 : List NodeSpec := [([], [0, 1, 2, 3, 4], [(0, []), (1, []), (2, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_0_32_8_0 : LevelOK rd_0_32 (subGoal 0 32) 8 lv_0_32_8_0 :=
  levelCheck_sound pp_0_32 (raw_faithful _ _ _) sl_0_32_ok autos_0_32_ok (selectPrevOK [0,1,2,3,4,5,6,7,8] ok_0_32_7)
    (by decide +kernel : levelCheck (freeVars 0 32) rd_0_32 (subGoal 0 32) sl_0_32 autos_0_32 (selectPrev [0,1,2,3,4,5,6,7,8] lv_0_32_7) 8 lv_0_32_8_0 = true)
private def lv_0_32_8 : List NodeSpec := lv_0_32_8_0
private theorem ok_0_32_8 : LevelOK rd_0_32 (subGoal 0 32) 8 lv_0_32_8 := ok_0_32_8_0
private theorem lower_0_32 : Lower (freeVars 0 32) (subGoal 0 32) 9 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 1, 5), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 1, 17)]) ok_0_32_8 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube0_32

private def flipRows (j : Nat) : Move :=
  let x := inputs.getD j zero
  (~~~x, x, Fin.ofNat 64 (1 <<< j))

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

private def signedCheckMap (ms : List Move) (raw : List Sig) (T : Sig)
    (base : List Sig) (G : Sig) : Bool :=
  sameUpToNeg (movedWord ms T) G &&
    raw.all (fun a => signedFreeWord base (movedWord ms a))

private theorem lower_signed_map {ms raw T base G L}
    (ok : signedCheckMap ms raw T base G = true)
    (pT : proper T) (nT : plainWord T = true) (nR : raw.all plainWord = true)
    (pG : proper G) (hL : Lower base G L) : Lower raw T L := by
  simp only [signedCheckMap, sameUpToNeg, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    List.all_eq_true] at ok
  have eq := ok.1
  rw [moved_eq_rename] at eq
  have supp : ∀ a ∈ raw, Available (base.map observe) (observe (rename (movedRow ms) a)) := by
    intro a ha
    rw [← moved_eq_rename]
    exact signedFreeWord_ok (ok.2 a ha)
  simpa using lower_slice pT nT nR pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

private theorem lower_4_0 : Lower (freeVars 4 0) (subGoal 4 0) 9 :=
  lower_signed_map (ms := [flipRows 0, flipRows 1, flipRows 2, flipRows 3, flipRows 4, flipRows 5,
      swapRows 82])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide +kernel)) lower_0_32

section Cube32_4

private def p_32_4 : Nat → Bits
  | 0 => mk128 0xb5f1e73e3f1c7793 0xb5f1e73e3f1c7793
  | 1 => mk128 0xdffeffffc7fff8ff 0xdffeffffc7fff8ff
  | 2 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 3 => mk128 0xe6ff07cff81f8f1c 0xe6ff07cff81f8f1c
  | 4 => mk128 0xf8fff80fffe00fe0 0xf8fff80fffe00fe0
  | 5 => mk128 0x0 0x0
  | _ => 0
private def q_32_4 : Nat → Bits
  | 0 => mk128 0x4a1c4a4609456391 0x4a1c4a4609456391
  | 1 => mk128 0x2020000042080026 0x2020000042080026
  | 2 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 3 => mk128 0x1944d41a90932d18 0x1944d41a90932d18
  | 4 => mk128 0x78886ad24c24ec0 0x78886ad24c24ec0
  | 5 => mk128 0x0 0x0
  | _ => 0
private theorem pp_32_4 : properPairs (subGoal 32 4) (asRow p_32_4) (asRow q_32_4) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_32_4 : List Decor := rawDecor (freeMask 32 4) p_32_4 q_32_4
private def sl_32_4 : List (Sig × Nat) := []
private theorem sl_32_4_ok : ∀ s ∈ sl_32_4, Slice (freeVars 32 4) (subGoal 32 4) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private def ck75 := levelCheck (freeVars 32 4) rd_32_4 (subGoal 32 4) sl_32_4 [[]] [] 3
private def d75 : List NodeSpec := [([(0,1,0),(1,2,4)],[0,1,5,3],[]),([(0,1,0),(2,2,4)],[5,0,1,3],[]),([(0,1,0),(1,3,4)],[0,1,2,5],[]),([(0,1,0),(2,3,4)],[5,0,1,2],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q75 : ck75 d75 = true := by decide +kernel
private def d76 : List NodeSpec := [([(1,1,0),(0,2,4)],[0,1,5,3],[]),([(1,1,0),(3,2,4)],[5,0,1,3],[]),([(1,1,0),(0,3,4)],[0,1,5,2],[]),([(1,1,0),(3,3,4)],[5,0,1,2],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q76 : ck75 d76 = true := by decide +kernel
private def d77 : List NodeSpec := [([(0,2,0),(1,2,0)],[4,1,5,3],[]),([(2,2,0),(1,3,4)],[0,1,2,5],[]),([(2,2,0),(2,3,4)],[0,5,1,2],[]),([(3,2,0),(1,3,4)],[0,1,2,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q77 : ck75 d77 = true := by decide +kernel
private def lv_32_4_3_0 : List NodeSpec := (d75 ++ (d76 ++ d77))

private theorem ok_32_4_3_0 : LevelOK rd_32_4 (subGoal 32 4) 3 lv_32_4_3_0 :=
  levelCheck_sound pp_32_4 (raw_faithful _ _ _) sl_32_4_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_32_4 (subGoal 32 4) 2)
    (levelCheck_join q75 (levelCheck_join q76 q77))
private def ck78 := levelCheck (freeVars 32 4) rd_32_4 (subGoal 32 4) sl_32_4 [[]] [] 3
private def d78 : List NodeSpec := [([(3,2,0),(2,3,4)],[0,1,2,5],[]),([(0,2,1),(1,4,0)],[1,5,2,3],[]),([(0,2,1),(3,4,0)],[5,1,2,3],[]),([(0,2,1),(1,3,4)],[0,1,2,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q78 : ck78 d78 = true := by decide +kernel
private def d79 : List NodeSpec := [([(0,2,1),(2,3,4)],[5,0,1,2],[]),([(1,2,1),(0,4,0)],[5,1,2,3],[]),([(1,2,1),(2,4,0)],[5,1,2,3],[]),([(1,2,1),(0,3,4)],[0,1,2,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q79 : ck78 d79 = true := by decide +kernel
private def d80 : List NodeSpec := [([(1,2,1),(3,3,4)],[5,0,1,2],[]),([(0,3,0),(1,3,0)],[4,1,2,5],[]),([(2,3,0),(1,2,4)],[0,1,5,3],[]),([(2,3,0),(2,2,4)],[5,0,1,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q80 : ck78 d80 = true := by decide +kernel
private def lv_32_4_3_1 : List NodeSpec := (d78 ++ (d79 ++ d80))

private theorem ok_32_4_3_1 : LevelOK rd_32_4 (subGoal 32 4) 3 lv_32_4_3_1 :=
  levelCheck_sound pp_32_4 (raw_faithful _ _ _) sl_32_4_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_32_4 (subGoal 32 4) 2)
    (levelCheck_join q78 (levelCheck_join q79 q80))
private def ck81 := levelCheck (freeVars 32 4) rd_32_4 (subGoal 32 4) sl_32_4 [[]] [] 3
private def d81 : List NodeSpec := [([(3,3,0),(1,2,4)],[0,1,5,3],[]),([(3,3,0),(2,2,4)],[0,1,5,3],[]),([(0,3,1),(1,4,0)],[1,5,2,3],[]),([(0,3,1),(3,4,0)],[5,1,2,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q81 : ck81 d81 = true := by decide +kernel
private def d82 : List NodeSpec := [([(0,3,1),(1,2,4)],[0,1,5,3],[]),([(0,3,1),(2,2,4)],[5,0,1,3],[]),([(1,3,1),(0,4,0)],[5,1,2,3],[]),([(1,3,1),(2,4,0)],[5,1,2,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q82 : ck81 d82 = true := by decide +kernel
private def d83 : List NodeSpec := [([(1,3,1),(0,4,2)],[0,1,5,3],[]),([(1,3,1),(2,4,2)],[5,0,1,3],[]),([(0,3,2),(1,3,2)],[0,1,4,5],[]),([(2,3,2),(1,0,4)],[5,1,2,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q83 : ck81 d83 = true := by decide +kernel
private def lv_32_4_3_2 : List NodeSpec := (d81 ++ (d82 ++ d83))

private theorem ok_32_4_3_2 : LevelOK rd_32_4 (subGoal 32 4) 3 lv_32_4_3_2 :=
  levelCheck_sound pp_32_4 (raw_faithful _ _ _) sl_32_4_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_32_4 (subGoal 32 4) 2)
    (levelCheck_join q81 (levelCheck_join q82 q83))
private def lv_32_4_3_3 : List NodeSpec := [([(2, 3, 2), (2, 0, 4)], [5, 1, 2, 3], []), ([(3, 3, 2), (1, 0, 4)], [5, 1, 2, 3], []), ([(3, 3, 2), (2, 0, 4)], [5, 1, 2, 3], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_32_4_3_3 : LevelOK rd_32_4 (subGoal 32 4) 3 lv_32_4_3_3 :=
  levelCheck_sound pp_32_4 (raw_faithful _ _ _) sl_32_4_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_32_4 (subGoal 32 4) 2)
    (by decide +kernel : levelCheck (freeVars 32 4) rd_32_4 (subGoal 32 4) sl_32_4 [[]] [] 3 lv_32_4_3_3 = true)
private def lv_32_4_3 : List NodeSpec := ((lv_32_4_3_0 ++ lv_32_4_3_1) ++ (lv_32_4_3_2 ++ lv_32_4_3_3))
private theorem ok_32_4_3 : LevelOK rd_32_4 (subGoal 32 4) 3 lv_32_4_3 := (levelOK_append (levelOK_append ok_32_4_3_0 ok_32_4_3_1) (levelOK_append ok_32_4_3_2 ok_32_4_3_3))
private def ck84 (ids : List Nat) := levelCheck (freeVars 32 4) rd_32_4 (subGoal 32 4) sl_32_4 [[]] (selectPrev ids lv_32_4_3) 4
private def d84 : List NodeSpec := [([(0,1,0)],[4,0,1,2,3],[]),([(1,1,0)],[0,1,4,2,3],[]),([(2,1,0)],[4,0,1,2,3],[]),([(3,1,0)],[4,0,1,2,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q84 : ck84 [0,1,2,3,4,5,6,7] d84 = true := by decide +kernel
private def d85 : List NodeSpec := [([(0,2,0)],[4,0,1,2,3],[]),([(1,2,0)],[0,1,2,4,3],[]),([(2,2,0)],[4,0,1,2,3],[]),([(3,2,0)],[4,0,1,2,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q85 : ck84 [8,9,10,11,12] d85 = true := by decide +kernel
private def d86 : List NodeSpec := [([(0,2,1)],[0,4,1,2,3],[]),([(1,2,1)],[0,1,2,4,3],[]),([(2,2,1)],[4,0,1,2,3],[]),([(3,2,1)],[4,0,1,2,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q86 : ck84 [13,14,15,16,17,18,19,20] d86 = true := by decide +kernel
private def lv_32_4_4_0 : List NodeSpec := (d84 ++ (d85 ++ d86))

private theorem ok_32_4_4_0 : LevelOK rd_32_4 (subGoal 32 4) 4 lv_32_4_4_0 := by
  have go {ids ds} (h : ck84 ids ds = true) : LevelOK rd_32_4 (subGoal 32 4) 4 ds :=
    levelCheck_sound pp_32_4 (raw_faithful _ _ _) sl_32_4_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_32_4_3) h
  exact (levelOK_append (go q84) (levelOK_append (go q85) (go q86)))
private def ck87 (ids : List Nat) := levelCheck (freeVars 32 4) rd_32_4 (subGoal 32 4) sl_32_4 [[]] (selectPrev ids lv_32_4_3) 4
private def d87 : List NodeSpec := [([(0,3,0)],[4,0,1,2,3],[]),([(1,3,0)],[0,1,2,3,4],[]),([(2,3,0)],[4,0,1,2,3],[]),([(3,3,0)],[4,0,1,2,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q87 : ck87 [21,22,23,24,25] d87 = true := by decide +kernel
private def d88 : List NodeSpec := [([(0,3,1)],[0,4,1,2,3],[]),([(1,3,1)],[0,1,2,3,4],[]),([(2,3,1)],[4,0,1,2,3],[]),([(3,3,1)],[4,0,1,2,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q88 : ck87 [26,27,28,29,30,31,32,33] d88 = true := by decide +kernel
private def d89 : List NodeSpec := [([(0,3,2)],[0,1,4,2,3],[]),([(1,3,2)],[0,1,2,3,4],[]),([(2,3,2)],[4,0,1,2,3],[]),([(3,3,2)],[4,0,1,2,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q89 : ck87 [34,35,36,37,38] d89 = true := by decide +kernel
private def lv_32_4_4_1 : List NodeSpec := (d87 ++ (d88 ++ d89))

private theorem ok_32_4_4_1 : LevelOK rd_32_4 (subGoal 32 4) 4 lv_32_4_4_1 := by
  have go {ids ds} (h : ck87 ids ds = true) : LevelOK rd_32_4 (subGoal 32 4) 4 ds :=
    levelCheck_sound pp_32_4 (raw_faithful _ _ _) sl_32_4_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_32_4_3) h
  exact (levelOK_append (go q87) (levelOK_append (go q88) (go q89)))
private def lv_32_4_4 : List NodeSpec := (lv_32_4_4_0 ++ lv_32_4_4_1)
private theorem ok_32_4_4 : LevelOK rd_32_4 (subGoal 32 4) 4 lv_32_4_4 := (levelOK_append ok_32_4_4_0 ok_32_4_4_1)
private def lv_32_4_5_0 : List NodeSpec := [([], [0, 1, 2, 3], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_32_4_5_0 : LevelOK rd_32_4 (subGoal 32 4) 5 lv_32_4_5_0 :=
  levelCheck_sound pp_32_4 (raw_faithful _ _ _) sl_32_4_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] ok_32_4_4)
    (by decide +kernel : levelCheck (freeVars 32 4) rd_32_4 (subGoal 32 4) sl_32_4 [[]] (selectPrev [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] lv_32_4_4) 5 lv_32_4_5_0 = true)
private def lv_32_4_5 : List NodeSpec := lv_32_4_5_0
private theorem ok_32_4_5 : LevelOK rd_32_4 (subGoal 32 4) 5 lv_32_4_5 := ok_32_4_5_0
private theorem lower_32_4 : Lower (freeVars 32 4) (subGoal 32 4) 6 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 3 zero, 2, 10), (inputs.getD 4 zero, 2, 18)]) ok_32_4_5 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube32_4

section Cube32_0

private def p_32_0 : Nat → Bits
  | 0 => mk128 0xf81fffffe07fffff 0x3ff03fffe7f8e3f
  | 1 => mk128 0xffffffffff81f01f 0xffffffffff88ffff
  | 2 => mk128 0xffe03f81fffe001f 0xfc1ffc1f01f0f3cc
  | 3 => mk128 0xffffc001ffffffe0 0x1fffe001ff03f0
  | 4 => mk128 0x1ffffffff 0xffe0000001fffc00
  | 5 => mk128 0x0 0x0
  | _ => 0
private def q_32_0 : Nat → Bits
  | 0 => mk128 0x88c48928601652a5 0x2125213954338615
  | 1 => mk128 0x110912408580a40a 0x464a4642a88838ea
  | 2 => mk128 0xa243a42b6aaa0a93 0xa913a91c0d70d34c
  | 3 => mk128 0x4492074db34d3cc0 0xc21cf38831dd03b0
  | 4 => mk128 0x871c3871dc71cf1c 0xf380c210c1eeec00
  | 5 => mk128 0x0 0x0
  | _ => 0
private theorem pp_32_0 : properPairs (subGoal 32 0) (asRow p_32_0) (asRow q_32_0) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_32_0 : List Decor := rawDecor (freeMask 32 0) p_32_0 q_32_0
private def sl_32_0 : List (Sig × Nat) := [(subcube 32 4, 6)]
private theorem sl_32_0_ok : ∀ s ∈ sl_32_0, Slice (freeVars 32 0) (subGoal 32 0) s.1 s.2 := by
  intro s hs
  simp only [sl_32_0, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 32 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_32_4
private def lv_32_0_6_0 : List NodeSpec := [([], [0, 1, 2, 3, 4], [(0, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_32_0_6_0 : LevelOK rd_32_0 (subGoal 32 0) 6 lv_32_0_6_0 :=
  levelCheck_sound pp_32_0 (raw_faithful _ _ _) sl_32_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_32_0 (subGoal 32 0) 5)
    (by decide +kernel : levelCheck (freeVars 32 0) rd_32_0 (subGoal 32 0) sl_32_0 [[]] [] 6 lv_32_0_6_0 = true)
private def lv_32_0_6 : List NodeSpec := lv_32_0_6_0
private theorem ok_32_0_6 : LevelOK rd_32_0 (subGoal 32 0) 6 lv_32_0_6 := ok_32_0_6_0
private theorem lower_32_0 : Lower (freeVars 32 0) (subGoal 32 0) 7 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 10, 14), (inputs.getD 3 zero, 6, 14), (inputs.getD 4 zero, 6, 22)]) ok_32_0_6 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube32_0

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
private def ck90 := levelCheck (freeVars 4 16) rd_4_16 (subGoal 4 16) sl_4_16 [[]] [] 3
private def d90 : List NodeSpec := [([(0,1,0),(1,2,4)],[0,1,5,3],[]),([(0,1,0),(2,2,4)],[5,0,1,3],[]),([(0,1,0),(1,3,4)],[0,1,2,5],[]),([(0,1,0),(2,3,4)],[5,0,1,2],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q90 : ck90 d90 = true := by decide +kernel
private def d91 : List NodeSpec := [([(1,1,0),(0,2,4)],[0,1,5,3],[]),([(1,1,0),(3,2,4)],[5,0,1,3],[]),([(1,1,0),(0,3,4)],[0,1,5,2],[]),([(1,1,0),(3,3,4)],[5,0,1,2],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q91 : ck90 d91 = true := by decide +kernel
private def d92 : List NodeSpec := [([(0,2,0),(1,1,4)],[0,5,2,3],[]),([(0,2,0),(2,1,4)],[5,0,2,3],[]),([(0,2,0),(1,3,4)],[0,1,2,5],[]),([(0,2,0),(2,3,4)],[5,0,1,2],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q92 : ck90 d92 = true := by decide +kernel
private def lv_4_16_3_0 : List NodeSpec := (d90 ++ (d91 ++ d92))

private theorem ok_4_16_3_0 : LevelOK rd_4_16 (subGoal 4 16) 3 lv_4_16_3_0 :=
  levelCheck_sound pp_4_16 (raw_faithful _ _ _) sl_4_16_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_4_16 (subGoal 4 16) 2)
    (levelCheck_join q90 (levelCheck_join q91 q92))
private def ck93 := levelCheck (freeVars 4 16) rd_4_16 (subGoal 4 16) sl_4_16 [[]] [] 3
private def d93 : List NodeSpec := [([(1,2,0),(0,4,1)],[0,5,2,3],[]),([(1,2,0),(2,4,1)],[5,0,2,3],[]),([(1,2,0),(0,3,4)],[0,1,2,5],[]),([(1,2,0),(3,3,4)],[5,0,1,2],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q93 : ck93 d93 = true := by decide +kernel
private def d94 : List NodeSpec := [([(0,2,1),(1,2,1)],[0,4,5,3],[]),([(2,2,1),(1,3,4)],[0,1,2,5],[]),([(2,2,1),(2,3,4)],[0,1,5,2],[]),([(3,2,1),(1,3,4)],[0,1,2,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q94 : ck93 d94 = true := by decide +kernel
private def d95 : List NodeSpec := [([(3,2,1),(2,3,4)],[0,1,2,5],[]),([(0,3,0),(1,1,4)],[0,5,2,3],[]),([(0,3,0),(2,1,4)],[5,0,2,3],[]),([(0,3,0),(1,2,4)],[0,1,5,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q95 : ck93 d95 = true := by decide +kernel
private def lv_4_16_3_1 : List NodeSpec := (d93 ++ (d94 ++ d95))

private theorem ok_4_16_3_1 : LevelOK rd_4_16 (subGoal 4 16) 3 lv_4_16_3_1 :=
  levelCheck_sound pp_4_16 (raw_faithful _ _ _) sl_4_16_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_4_16 (subGoal 4 16) 2)
    (levelCheck_join q93 (levelCheck_join q94 q95))
private def ck96 := levelCheck (freeVars 4 16) rd_4_16 (subGoal 4 16) sl_4_16 [[]] [] 3
private def d96 : List NodeSpec := [([(0,3,0),(2,2,4)],[5,0,1,3],[]),([(1,3,0),(0,4,1)],[0,5,2,3],[]),([(1,3,0),(2,4,1)],[5,0,2,3],[]),([(1,3,0),(0,4,2)],[0,1,5,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q96 : ck96 d96 = true := by decide +kernel
private def d97 : List NodeSpec := [([(1,3,0),(2,4,2)],[5,0,1,3],[]),([(0,3,1),(1,3,1)],[0,4,2,5],[]),([(2,3,1),(1,2,4)],[0,1,5,3],[]),([(2,3,1),(2,2,4)],[0,5,1,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q97 : ck96 d97 = true := by decide +kernel
private def d98 : List NodeSpec := [([(3,3,1),(1,2,4)],[0,1,5,3],[]),([(3,3,1),(2,2,4)],[0,1,5,3],[]),([(0,3,2),(1,3,2)],[0,1,4,5],[]),([(2,3,2),(1,1,4)],[0,5,2,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q98 : ck96 d98 = true := by decide +kernel
private def lv_4_16_3_2 : List NodeSpec := (d96 ++ (d97 ++ d98))

private theorem ok_4_16_3_2 : LevelOK rd_4_16 (subGoal 4 16) 3 lv_4_16_3_2 :=
  levelCheck_sound pp_4_16 (raw_faithful _ _ _) sl_4_16_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_4_16 (subGoal 4 16) 2)
    (levelCheck_join q96 (levelCheck_join q97 q98))
private def lv_4_16_3_3 : List NodeSpec := [([(2, 3, 2), (2, 1, 4)], [0, 5, 2, 3], []), ([(3, 3, 2), (1, 1, 4)], [0, 5, 2, 3], []), ([(3, 3, 2), (2, 1, 4)], [0, 5, 2, 3], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_4_16_3_3 : LevelOK rd_4_16 (subGoal 4 16) 3 lv_4_16_3_3 :=
  levelCheck_sound pp_4_16 (raw_faithful _ _ _) sl_4_16_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_4_16 (subGoal 4 16) 2)
    (by decide +kernel : levelCheck (freeVars 4 16) rd_4_16 (subGoal 4 16) sl_4_16 [[]] [] 3 lv_4_16_3_3 = true)
private def lv_4_16_3 : List NodeSpec := ((lv_4_16_3_0 ++ lv_4_16_3_1) ++ (lv_4_16_3_2 ++ lv_4_16_3_3))
private theorem ok_4_16_3 : LevelOK rd_4_16 (subGoal 4 16) 3 lv_4_16_3 := (levelOK_append (levelOK_append ok_4_16_3_0 ok_4_16_3_1) (levelOK_append ok_4_16_3_2 ok_4_16_3_3))
private def ck99 (ids : List Nat) := levelCheck (freeVars 4 16) rd_4_16 (subGoal 4 16) sl_4_16 [[]] (selectPrev ids lv_4_16_3) 4
private def d99 : List NodeSpec := [([(0,1,0)],[4,0,1,2,3],[]),([(1,1,0)],[0,1,4,2,3],[]),([(2,1,0)],[4,0,1,2,3],[]),([(3,1,0)],[4,0,1,2,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q99 : ck99 [0,1,2,3,4,5,6,7] d99 = true := by decide +kernel
private def d100 : List NodeSpec := [([(0,2,0)],[4,0,1,2,3],[]),([(1,2,0)],[0,1,2,4,3],[]),([(2,2,0)],[4,0,1,2,3],[]),([(3,2,0)],[4,0,1,2,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q100 : ck99 [8,9,10,11,12,13,14,15] d100 = true := by decide +kernel
private def d101 : List NodeSpec := [([(0,2,1)],[0,4,1,2,3],[]),([(1,2,1)],[0,1,2,4,3],[]),([(2,2,1)],[4,0,1,2,3],[]),([(3,2,1)],[4,0,1,2,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q101 : ck99 [16,17,18,19,20] d101 = true := by decide +kernel
private def lv_4_16_4_0 : List NodeSpec := (d99 ++ (d100 ++ d101))

private theorem ok_4_16_4_0 : LevelOK rd_4_16 (subGoal 4 16) 4 lv_4_16_4_0 := by
  have go {ids ds} (h : ck99 ids ds = true) : LevelOK rd_4_16 (subGoal 4 16) 4 ds :=
    levelCheck_sound pp_4_16 (raw_faithful _ _ _) sl_4_16_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_4_16_3) h
  exact (levelOK_append (go q99) (levelOK_append (go q100) (go q101)))
private def ck102 (ids : List Nat) := levelCheck (freeVars 4 16) rd_4_16 (subGoal 4 16) sl_4_16 [[]] (selectPrev ids lv_4_16_3) 4
private def d102 : List NodeSpec := [([(0,3,0)],[4,0,1,2,3],[]),([(1,3,0)],[0,1,2,3,4],[]),([(2,3,0)],[4,0,1,2,3],[]),([(3,3,0)],[4,0,1,2,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q102 : ck102 [21,22,23,24,25,26,27,28] d102 = true := by decide +kernel
private def d103 : List NodeSpec := [([(0,3,1)],[0,4,1,2,3],[]),([(1,3,1)],[0,1,2,3,4],[]),([(2,3,1)],[4,0,1,2,3],[]),([(3,3,1)],[4,0,1,2,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q103 : ck102 [29,30,31,32,33] d103 = true := by decide +kernel
private def d104 : List NodeSpec := [([(0,3,2)],[0,1,4,2,3],[]),([(1,3,2)],[0,1,2,3,4],[]),([(2,3,2)],[4,0,1,2,3],[]),([(3,3,2)],[4,0,1,2,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q104 : ck102 [34,35,36,37,38] d104 = true := by decide +kernel
private def lv_4_16_4_1 : List NodeSpec := (d102 ++ (d103 ++ d104))

private theorem ok_4_16_4_1 : LevelOK rd_4_16 (subGoal 4 16) 4 lv_4_16_4_1 := by
  have go {ids ds} (h : ck102 ids ds = true) : LevelOK rd_4_16 (subGoal 4 16) 4 ds :=
    levelCheck_sound pp_4_16 (raw_faithful _ _ _) sl_4_16_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_4_16_3) h
  exact (levelOK_append (go q102) (levelOK_append (go q103) (go q104)))
private def lv_4_16_4 : List NodeSpec := (lv_4_16_4_0 ++ lv_4_16_4_1)
private theorem ok_4_16_4 : LevelOK rd_4_16 (subGoal 4 16) 4 lv_4_16_4 := (levelOK_append ok_4_16_4_0 ok_4_16_4_1)
private def lv_4_16_5_0 : List NodeSpec := [([], [0, 1, 2, 3], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_4_16_5_0 : LevelOK rd_4_16 (subGoal 4 16) 5 lv_4_16_5_0 :=
  levelCheck_sound pp_4_16 (raw_faithful _ _ _) sl_4_16_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] ok_4_16_4)
    (by decide +kernel : levelCheck (freeVars 4 16) rd_4_16 (subGoal 4 16) sl_4_16 [[]] (selectPrev [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] lv_4_16_4) 5 lv_4_16_5_0 = true)
private def lv_4_16_5 : List NodeSpec := lv_4_16_5_0
private theorem ok_4_16_5 : LevelOK rd_4_16 (subGoal 4 16) 5 lv_4_16_5 := ok_4_16_5_0
private theorem lower_4_16 : Lower (freeVars 4 16) (subGoal 4 16) 6 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 3 zero, 1, 9), (inputs.getD 5 zero, 1, 33)]) ok_4_16_5 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube4_16

section Cube0_16

private def p_0_16 : Nat → Bits
  | 0 => mk128 0x83ffff0f07f0fe1f 0xffc3fff81e89f3f3
  | 1 => mk128 0xfc3e1ffff87f0fe1 0xc1fc383fff764c9f
  | 2 => mk128 0xffc01ff1ff800ffe 0x1ffc03fe1878f1c
  | 3 => mk128 0xffffe001fffff000 0x1ffffc001f80fe0
  | 4 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 5 => mk128 0x1ffffffff 0xfe00000001fff000
  | _ => 0
private def q_0_16 : Nat → Bits
  | 0 => mk128 0x8804001000801202 0x4440488844009131
  | 1 => mk128 0x10902a0028310420 0x8884111298324486
  | 2 => mk128 0x290d548353888b54 0x156a82a545858b18
  | 3 => mk128 0x42a906a59d5aa110 0x21b3270189d80ec0
  | 4 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 5 => mk128 0x733198c9e66ccd99 0x3822040611ef6000
  | _ => 0
private theorem pp_0_16 : properPairs (subGoal 0 16) (asRow p_0_16) (asRow q_0_16) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_0_16 : List Decor := rawDecor (freeMask 0 16) p_0_16 q_0_16
private def sl_0_16 : List (Sig × Nat) := [(subcube 4 16, 6)]
private theorem sl_0_16_ok : ∀ s ∈ sl_0_16, Slice (freeVars 0 16) (subGoal 0 16) s.1 s.2 := by
  intro s hs
  simp only [sl_0_16, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 4 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_4_16
private def lv_0_16_6_0 : List NodeSpec := [([], [0, 1, 2, 3, 4], [(0, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_0_16_6_0 : LevelOK rd_0_16 (subGoal 0 16) 6 lv_0_16_6_0 :=
  levelCheck_sound pp_0_16 (raw_faithful _ _ _) sl_0_16_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_0_16 (subGoal 0 16) 5)
    (by decide +kernel : levelCheck (freeVars 0 16) rd_0_16 (subGoal 0 16) sl_0_16 [[]] [] 6 lv_0_16_6_0 = true)
private def lv_0_16_6 : List NodeSpec := lv_0_16_6_0
private theorem ok_0_16_6 : LevelOK rd_0_16 (subGoal 0 16) 6 lv_0_16_6 := ok_0_16_6_0
private theorem lower_0_16 : Lower (freeVars 0 16) (subGoal 0 16) 7 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 2, 6), (inputs.getD 3 zero, 1, 9), (inputs.getD 5 zero, 1, 33)]) ok_0_16_6 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube0_16

section Cube0_4

private def p_0_4 : Nat → Bits
  | 0 => mk128 0x81fe1f0f0ff0fe1f 0xffe1fc1c1e99f793
  | 1 => mk128 0xfe3ffffff07f0fe1 0xc0fe1fffff6648ff
  | 2 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 3 => mk128 0xffc01ff1ff800ffe 0xffe01fe1878f1c
  | 4 => mk128 0xffffe001fffff000 0xffffe001f80fe0
  | 5 => mk128 0x1ffffffff 0xff00000001fff000
  | _ => 0
private def q_0_4 : Nat → Bits
  | 0 => mk128 0x8c04221001901202 0x466024444c089391
  | 1 => mk128 0x1010080020210420 0x8802090910224026
  | 2 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 3 => mk128 0x248d548356888b54 0x12b54092c5858d18
  | 4 => mk128 0x492906a59b5aa110 0x24d992c089d80ec0
  | 5 => mk128 0x71b198c9ec6ccd99 0x3811030311f76000
  | _ => 0
private theorem pp_0_4 : properPairs (subGoal 0 4) (asRow p_0_4) (asRow q_0_4) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_0_4 : List Decor := rawDecor (freeMask 0 4) p_0_4 q_0_4
private def sl_0_4 : List (Sig × Nat) := [(subcube 32 4, 6)]
private theorem sl_0_4_ok : ∀ s ∈ sl_0_4, Slice (freeVars 0 4) (subGoal 0 4) s.1 s.2 := by
  intro s hs
  simp only [sl_0_4, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 32 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_32_4
private def lv_0_4_6_0 : List NodeSpec := [([], [0, 1, 2, 3, 4], [(0, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_0_4_6_0 : LevelOK rd_0_4 (subGoal 0 4) 6 lv_0_4_6_0 :=
  levelCheck_sound pp_0_4 (raw_faithful _ _ _) sl_0_4_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_0_4 (subGoal 0 4) 5)
    (by decide +kernel : levelCheck (freeVars 0 4) rd_0_4 (subGoal 0 4) sl_0_4 [[]] [] 6 lv_0_4_6_0 = true)
private def lv_0_4_6 : List NodeSpec := lv_0_4_6_0
private theorem ok_0_4_6 : LevelOK rd_0_4 (subGoal 0 4) 6 lv_0_4_6 := ok_0_4_6_0
private theorem lower_0_4 : Lower (freeVars 0 4) (subGoal 0 4) 7 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 3 zero, 2, 10), (inputs.getD 4 zero, 2, 18), (inputs.getD 5 zero, 1, 33)]) ok_0_4_6 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube0_4

section Cube16_0

private def p_16_0 : Nat → Bits
  | 0 => mk128 0xf81fffffe07fffff 0xfffe03fffe3ffe3f
  | 1 => mk128 0xffffffffff81f03e 0x7ffffffffc88fff
  | 2 => mk128 0xffe03f81fffe003f 0xf83ffc1f01f0f3cc
  | 3 => mk128 0xffffc001ffffffc0 0x3fffe001ff03f0
  | 4 => mk128 0x0 0x0
  | 5 => mk128 0x1ffffffff 0xffc0000001fffc00
  | _ => 0
private def q_16_0 : Nat → Bits
  | 0 => mk128 0x8c489082016514a 0x284a212954133615
  | 1 => mk128 0x91091260c580a414 0x8694c652a8c888ea
  | 2 => mk128 0xa243a42b6aaa0927 0xb227691c0d70d34c
  | 3 => mk128 0x4492074db34d3d81 0x2439b38831bd03b0
  | 4 => mk128 0x0 0x0
  | 5 => mk128 0x871c3871dc71ce39 0xc701c210c1eeec00
  | _ => 0
private theorem pp_16_0 : properPairs (subGoal 16 0) (asRow p_16_0) (asRow q_16_0) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_16_0 : List Decor := rawDecor (freeMask 16 0) p_16_0 q_16_0
private def sl_16_0 : List (Sig × Nat) := [(subcube 16 32, 6)]
private theorem sl_16_0_ok : ∀ s ∈ sl_16_0, Slice (freeVars 16 0) (subGoal 16 0) s.1 s.2 := by
  intro s hs
  simp only [sl_16_0, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 16 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_16_32
private def lv_16_0_6_0 : List NodeSpec := [([], [0, 1, 2, 3, 4], [(0, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_16_0_6_0 : LevelOK rd_16_0 (subGoal 16 0) 6 lv_16_0_6_0 :=
  levelCheck_sound pp_16_0 (raw_faithful _ _ _) sl_16_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_16_0 (subGoal 16 0) 5)
    (by decide +kernel : levelCheck (freeVars 16 0) rd_16_0 (subGoal 16 0) sl_16_0 [[]] [] 6 lv_16_0_6_0 = true)
private def lv_16_0_6 : List NodeSpec := lv_16_0_6_0
private theorem ok_16_0_6 : LevelOK rd_16_0 (subGoal 16 0) 6 lv_16_0_6 := ok_16_0_6_0
private theorem lower_16_0 : Lower (freeVars 16 0) (subGoal 16 0) 7 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 10, 14), (inputs.getD 3 zero, 6, 14), (inputs.getD 5 zero, 5, 37)]) ok_16_0_6 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube16_0

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
private def ck105 := levelCheck (freeVars 4 8) rd_4_8 (subGoal 4 8) sl_4_8 [[]] [] 3
private def d105 : List NodeSpec := [([(0,1,0),(1,2,4)],[0,1,5,3],[]),([(0,1,0),(2,2,4)],[5,0,1,3],[]),([(0,1,0),(1,3,4)],[0,1,2,5],[]),([(0,1,0),(2,3,4)],[5,0,1,2],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q105 : ck105 d105 = true := by decide +kernel
private def d106 : List NodeSpec := [([(1,1,0),(0,2,4)],[0,1,5,3],[]),([(1,1,0),(3,2,4)],[5,0,1,3],[]),([(1,1,0),(0,3,4)],[0,1,5,2],[]),([(1,1,0),(3,3,4)],[5,0,1,2],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q106 : ck105 d106 = true := by decide +kernel
private def d107 : List NodeSpec := [([(0,2,0),(1,1,4)],[0,5,2,3],[]),([(0,2,0),(2,1,4)],[5,0,2,3],[]),([(0,2,0),(1,3,4)],[0,1,2,5],[]),([(0,2,0),(2,3,4)],[5,0,1,2],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q107 : ck105 d107 = true := by decide +kernel
private def lv_4_8_3_0 : List NodeSpec := (d105 ++ (d106 ++ d107))

private theorem ok_4_8_3_0 : LevelOK rd_4_8 (subGoal 4 8) 3 lv_4_8_3_0 :=
  levelCheck_sound pp_4_8 (raw_faithful _ _ _) sl_4_8_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_4_8 (subGoal 4 8) 2)
    (levelCheck_join q105 (levelCheck_join q106 q107))
private def ck108 := levelCheck (freeVars 4 8) rd_4_8 (subGoal 4 8) sl_4_8 [[]] [] 3
private def d108 : List NodeSpec := [([(1,2,0),(0,4,1)],[0,5,2,3],[]),([(1,2,0),(2,4,1)],[5,0,2,3],[]),([(1,2,0),(0,3,4)],[0,1,2,5],[]),([(1,2,0),(3,3,4)],[5,0,1,2],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q108 : ck108 d108 = true := by decide +kernel
private def d109 : List NodeSpec := [([(0,2,1),(1,2,1)],[0,4,5,3],[]),([(2,2,1),(1,3,4)],[0,1,2,5],[]),([(2,2,1),(2,3,4)],[0,1,5,2],[]),([(3,2,1),(1,3,4)],[0,1,2,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q109 : ck108 d109 = true := by decide +kernel
private def d110 : List NodeSpec := [([(3,2,1),(2,3,4)],[0,1,2,5],[]),([(0,3,0),(1,1,4)],[0,5,2,3],[]),([(0,3,0),(2,1,4)],[5,0,2,3],[]),([(0,3,0),(1,2,4)],[0,1,5,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q110 : ck108 d110 = true := by decide +kernel
private def lv_4_8_3_1 : List NodeSpec := (d108 ++ (d109 ++ d110))

private theorem ok_4_8_3_1 : LevelOK rd_4_8 (subGoal 4 8) 3 lv_4_8_3_1 :=
  levelCheck_sound pp_4_8 (raw_faithful _ _ _) sl_4_8_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_4_8 (subGoal 4 8) 2)
    (levelCheck_join q108 (levelCheck_join q109 q110))
private def ck111 := levelCheck (freeVars 4 8) rd_4_8 (subGoal 4 8) sl_4_8 [[]] [] 3
private def d111 : List NodeSpec := [([(0,3,0),(2,2,4)],[5,0,1,3],[]),([(1,3,0),(0,4,1)],[0,5,2,3],[]),([(1,3,0),(2,4,1)],[5,0,2,3],[]),([(1,3,0),(0,4,2)],[0,1,5,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q111 : ck111 d111 = true := by decide +kernel
private def d112 : List NodeSpec := [([(1,3,0),(2,4,2)],[5,0,1,3],[]),([(0,3,1),(1,3,1)],[0,4,2,5],[]),([(2,3,1),(1,2,4)],[0,1,5,3],[]),([(2,3,1),(2,2,4)],[0,5,1,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q112 : ck111 d112 = true := by decide +kernel
private def d113 : List NodeSpec := [([(3,3,1),(1,2,4)],[0,1,5,3],[]),([(3,3,1),(2,2,4)],[0,1,5,3],[]),([(0,3,2),(1,3,2)],[0,1,4,5],[]),([(2,3,2),(1,1,4)],[0,5,2,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q113 : ck111 d113 = true := by decide +kernel
private def lv_4_8_3_2 : List NodeSpec := (d111 ++ (d112 ++ d113))

private theorem ok_4_8_3_2 : LevelOK rd_4_8 (subGoal 4 8) 3 lv_4_8_3_2 :=
  levelCheck_sound pp_4_8 (raw_faithful _ _ _) sl_4_8_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_4_8 (subGoal 4 8) 2)
    (levelCheck_join q111 (levelCheck_join q112 q113))
private def lv_4_8_3_3 : List NodeSpec := [([(2, 3, 2), (2, 1, 4)], [0, 5, 2, 3], []), ([(3, 3, 2), (1, 1, 4)], [0, 5, 2, 3], []), ([(3, 3, 2), (2, 1, 4)], [0, 5, 2, 3], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_4_8_3_3 : LevelOK rd_4_8 (subGoal 4 8) 3 lv_4_8_3_3 :=
  levelCheck_sound pp_4_8 (raw_faithful _ _ _) sl_4_8_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_4_8 (subGoal 4 8) 2)
    (by decide +kernel : levelCheck (freeVars 4 8) rd_4_8 (subGoal 4 8) sl_4_8 [[]] [] 3 lv_4_8_3_3 = true)
private def lv_4_8_3 : List NodeSpec := ((lv_4_8_3_0 ++ lv_4_8_3_1) ++ (lv_4_8_3_2 ++ lv_4_8_3_3))
private theorem ok_4_8_3 : LevelOK rd_4_8 (subGoal 4 8) 3 lv_4_8_3 := (levelOK_append (levelOK_append ok_4_8_3_0 ok_4_8_3_1) (levelOK_append ok_4_8_3_2 ok_4_8_3_3))
private def ck114 (ids : List Nat) := levelCheck (freeVars 4 8) rd_4_8 (subGoal 4 8) sl_4_8 [[]] (selectPrev ids lv_4_8_3) 4
private def d114 : List NodeSpec := [([(0,1,0)],[4,0,1,2,3],[]),([(1,1,0)],[0,1,4,2,3],[]),([(2,1,0)],[4,0,1,2,3],[]),([(3,1,0)],[4,0,1,2,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q114 : ck114 [0,1,2,3,4,5,6,7] d114 = true := by decide +kernel
private def d115 : List NodeSpec := [([(0,2,0)],[4,0,1,2,3],[]),([(1,2,0)],[0,1,2,4,3],[]),([(2,2,0)],[4,0,1,2,3],[]),([(3,2,0)],[4,0,1,2,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q115 : ck114 [8,9,10,11,12,13,14,15] d115 = true := by decide +kernel
private def d116 : List NodeSpec := [([(0,2,1)],[0,4,1,2,3],[]),([(1,2,1)],[0,1,2,4,3],[]),([(2,2,1)],[4,0,1,2,3],[]),([(3,2,1)],[4,0,1,2,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q116 : ck114 [16,17,18,19,20] d116 = true := by decide +kernel
private def lv_4_8_4_0 : List NodeSpec := (d114 ++ (d115 ++ d116))

private theorem ok_4_8_4_0 : LevelOK rd_4_8 (subGoal 4 8) 4 lv_4_8_4_0 := by
  have go {ids ds} (h : ck114 ids ds = true) : LevelOK rd_4_8 (subGoal 4 8) 4 ds :=
    levelCheck_sound pp_4_8 (raw_faithful _ _ _) sl_4_8_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_4_8_3) h
  exact (levelOK_append (go q114) (levelOK_append (go q115) (go q116)))
private def ck117 (ids : List Nat) := levelCheck (freeVars 4 8) rd_4_8 (subGoal 4 8) sl_4_8 [[]] (selectPrev ids lv_4_8_3) 4
private def d117 : List NodeSpec := [([(0,3,0)],[4,0,1,2,3],[]),([(1,3,0)],[0,1,2,3,4],[]),([(2,3,0)],[4,0,1,2,3],[]),([(3,3,0)],[4,0,1,2,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q117 : ck117 [21,22,23,24,25,26,27,28] d117 = true := by decide +kernel
private def d118 : List NodeSpec := [([(0,3,1)],[0,4,1,2,3],[]),([(1,3,1)],[0,1,2,3,4],[]),([(2,3,1)],[4,0,1,2,3],[]),([(3,3,1)],[4,0,1,2,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q118 : ck117 [29,30,31,32,33] d118 = true := by decide +kernel
private def d119 : List NodeSpec := [([(0,3,2)],[0,1,4,2,3],[]),([(1,3,2)],[0,1,2,3,4],[]),([(2,3,2)],[4,0,1,2,3],[]),([(3,3,2)],[4,0,1,2,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q119 : ck117 [34,35,36,37,38] d119 = true := by decide +kernel
private def lv_4_8_4_1 : List NodeSpec := (d117 ++ (d118 ++ d119))

private theorem ok_4_8_4_1 : LevelOK rd_4_8 (subGoal 4 8) 4 lv_4_8_4_1 := by
  have go {ids ds} (h : ck117 ids ds = true) : LevelOK rd_4_8 (subGoal 4 8) 4 ds :=
    levelCheck_sound pp_4_8 (raw_faithful _ _ _) sl_4_8_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_4_8_3) h
  exact (levelOK_append (go q117) (levelOK_append (go q118) (go q119)))
private def lv_4_8_4 : List NodeSpec := (lv_4_8_4_0 ++ lv_4_8_4_1)
private theorem ok_4_8_4 : LevelOK rd_4_8 (subGoal 4 8) 4 lv_4_8_4 := (levelOK_append ok_4_8_4_0 ok_4_8_4_1)
private def lv_4_8_5_0 : List NodeSpec := [([], [0, 1, 2, 3], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_4_8_5_0 : LevelOK rd_4_8 (subGoal 4 8) 5 lv_4_8_5_0 :=
  levelCheck_sound pp_4_8 (raw_faithful _ _ _) sl_4_8_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] ok_4_8_4)
    (by decide +kernel : levelCheck (freeVars 4 8) rd_4_8 (subGoal 4 8) sl_4_8 [[]] (selectPrev [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] lv_4_8_4) 5 lv_4_8_5_0 = true)
private def lv_4_8_5 : List NodeSpec := lv_4_8_5_0
private theorem ok_4_8_5 : LevelOK rd_4_8 (subGoal 4 8) 5 lv_4_8_5 := ok_4_8_5_0
private theorem lower_4_8 : Lower (freeVars 4 8) (subGoal 4 8) 6 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 4 zero, 1, 17), (inputs.getD 5 zero, 1, 33)]) ok_4_8_5 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube4_8

section Cube0_8

private def p_0_8 : Nat → Bits
  | 0 => mk128 0x83ffff0f07f0fe1f 0xffc3fff81e89f3f3
  | 1 => mk128 0xfc3e1ffff87f0fe1 0xc1fc383fff764c9f
  | 2 => mk128 0xffc01ff1ff800ffe 0x1ffc03fe1878f1c
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0xffffe001fffff000 0x1ffffc001f80fe0
  | 5 => mk128 0x1ffffffff 0xfe00000001fff000
  | _ => 0
private def q_0_8 : Nat → Bits
  | 0 => mk128 0x8804001000801202 0x4440488844009131
  | 1 => mk128 0x10902a0028310420 0x8884111298324486
  | 2 => mk128 0x290d548353888b54 0x156a82a545858b18
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0x42a906a59d5aa110 0x21b3270189d80ec0
  | 5 => mk128 0x733198c9e66ccd99 0x3822040611ef6000
  | _ => 0
private theorem pp_0_8 : properPairs (subGoal 0 8) (asRow p_0_8) (asRow q_0_8) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_0_8 : List Decor := rawDecor (freeMask 0 8) p_0_8 q_0_8
private def sl_0_8 : List (Sig × Nat) := [(subcube 4 8, 6)]
private theorem sl_0_8_ok : ∀ s ∈ sl_0_8, Slice (freeVars 0 8) (subGoal 0 8) s.1 s.2 := by
  intro s hs
  simp only [sl_0_8, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 4 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_4_8
private def lv_0_8_6_0 : List NodeSpec := [([], [0, 1, 2, 3, 4], [(0, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_0_8_6_0 : LevelOK rd_0_8 (subGoal 0 8) 6 lv_0_8_6_0 :=
  levelCheck_sound pp_0_8 (raw_faithful _ _ _) sl_0_8_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_0_8 (subGoal 0 8) 5)
    (by decide +kernel : levelCheck (freeVars 0 8) rd_0_8 (subGoal 0 8) sl_0_8 [[]] [] 6 lv_0_8_6_0 = true)
private def lv_0_8_6 : List NodeSpec := lv_0_8_6_0
private theorem ok_0_8_6 : LevelOK rd_0_8 (subGoal 0 8) 6 lv_0_8_6 := ok_0_8_6_0
private theorem lower_0_8 : Lower (freeVars 0 8) (subGoal 0 8) 7 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 2, 6), (inputs.getD 4 zero, 1, 17), (inputs.getD 5 zero, 1, 33)]) ok_0_8_6 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube0_8

section Cube8_0

private def p_8_0 : Nat → Bits
  | 0 => mk128 0xf81fffffe07fffff 0xfffe03fffe3ffe3f
  | 1 => mk128 0xffffffffff81f03e 0x7ffffffffc88fff
  | 2 => mk128 0xffe03f81fffe003f 0xf83ffc1f01f0f3cc
  | 3 => mk128 0x0 0x0
  | 4 => mk128 0xffffc001ffffffc0 0x3fffe001ff03f0
  | 5 => mk128 0x1ffffffff 0xffc0000001fffc00
  | _ => 0
private def q_8_0 : Nat → Bits
  | 0 => mk128 0x8c489082016514a 0x284a212954133615
  | 1 => mk128 0x91091260c580a414 0x8694c652a8c888ea
  | 2 => mk128 0xa243a42b6aaa0927 0xb227691c0d70d34c
  | 3 => mk128 0x0 0x0
  | 4 => mk128 0x4492074db34d3d81 0x2439b38831bd03b0
  | 5 => mk128 0x871c3871dc71ce39 0xc701c210c1eeec00
  | _ => 0
private theorem pp_8_0 : properPairs (subGoal 8 0) (asRow p_8_0) (asRow q_8_0) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_8_0 : List Decor := rawDecor (freeMask 8 0) p_8_0 q_8_0
private def sl_8_0 : List (Sig × Nat) := [(subcube 8 32, 6)]
private theorem sl_8_0_ok : ∀ s ∈ sl_8_0, Slice (freeVars 8 0) (subGoal 8 0) s.1 s.2 := by
  intro s hs
  simp only [sl_8_0, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 8 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_8_32
private def lv_8_0_6_0 : List NodeSpec := [([], [0, 1, 2, 3, 4], [(0, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_8_0_6_0 : LevelOK rd_8_0 (subGoal 8 0) 6 lv_8_0_6_0 :=
  levelCheck_sound pp_8_0 (raw_faithful _ _ _) sl_8_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_8_0 (subGoal 8 0) 5)
    (by decide +kernel : levelCheck (freeVars 8 0) rd_8_0 (subGoal 8 0) sl_8_0 [[]] [] 6 lv_8_0_6_0 = true)
private def lv_8_0_6 : List NodeSpec := lv_8_0_6_0
private theorem ok_8_0_6 : LevelOK rd_8_0 (subGoal 8 0) 6 lv_8_0_6 := ok_8_0_6_0
private theorem lower_8_0 : Lower (freeVars 8 0) (subGoal 8 0) 7 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 18, 22), (inputs.getD 4 zero, 6, 22), (inputs.getD 5 zero, 5, 37)]) ok_8_0_6 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube8_0

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
private def lv_6_1_3_0 : List NodeSpec := [([], [0, 1, 2], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_6_1_3_0 : LevelOK rd_6_1 (subGoal 6 1) 3 lv_6_1_3_0 :=
  levelCheck_sound pp_6_1 (raw_faithful _ _ _) sl_6_1_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_6_1 (subGoal 6 1) 2)
    (by decide +kernel : levelCheck (freeVars 6 1) rd_6_1 (subGoal 6 1) sl_6_1 [[]] [] 3 lv_6_1_3_0 = true)
private def lv_6_1_3 : List NodeSpec := lv_6_1_3_0
private theorem ok_6_1_3 : LevelOK rd_6_1 (subGoal 6 1) 3 lv_6_1_3 := ok_6_1_3_0
private theorem lower_6_1 : Lower (freeVars 6 1) (subGoal 6 1) 4 :=
  lower_of_search (xs := [(inputs.getD 3 zero, 16, 24), (inputs.getD 4 zero, 8, 24), (inputs.getD 5 zero, 8, 40)]) ok_6_1_3 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube6_1

section Cube2_1

private def p_2_1 : Nat → Bits
  | 0 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0x2af8cce639cfc49e 0x55f199cc739f893c
  | 3 => mk128 0xf3ff0f3fc1f1f8e7 0xe7fe1e7f83e3f1cf
  | 4 => mk128 0xfcfff03ffe01ff07 0xf9ffe07ffc03fe0f
  | 5 => mk128 0x3f7fffc7fffe07f8 0x7effff8ffffc0ff0
  | _ => 0
private def q_2_1 : Nat → Bits
  | 0 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0x150e990e0c6c748e 0x2a1d321c18d8e91c
  | 3 => mk128 0x4c12a04240a490a2 0x9825408481492145
  | 4 => mk128 0x83240a8494092505 0x648150928124a0a
  | 5 => mk128 0xc0001121000250 0x1800022420004a0
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
private def lv_2_1_4_0 : List NodeSpec := [([], [0, 1, 2, 3], [(0, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_2_1_4_0 : LevelOK rd_2_1 (subGoal 2 1) 4 lv_2_1_4_0 :=
  levelCheck_sound pp_2_1 (raw_faithful _ _ _) sl_2_1_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_2_1 (subGoal 2 1) 3)
    (by decide +kernel : levelCheck (freeVars 2 1) rd_2_1 (subGoal 2 1) sl_2_1 [[]] [] 4 lv_2_1_4_0 = true)
private def lv_2_1_4 : List NodeSpec := lv_2_1_4_0
private theorem ok_2_1_4 : LevelOK rd_2_1 (subGoal 2 1) 4 lv_2_1_4 := ok_2_1_4_0
private theorem lower_2_1 : Lower (freeVars 2 1) (subGoal 2 1) 5 :=
  lower_of_search (xs := [(inputs.getD 2 zero, 32, 36), (inputs.getD 3 zero, 16, 24), (inputs.getD 4 zero, 8, 24), (inputs.getD 5 zero, 4, 36)]) ok_2_1_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube2_1

section Cube0_1

private def p_0_1 : Nat → Bits
  | 0 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 1 => mk128 0x71cce673f73fff82 0x32331c63fff8043f
  | 2 => mk128 0x81f0f87c78318e63 0xc3c3ef8333849b2a
  | 3 => mk128 0xfe00ff807fc1f07c 0x3fc0ffc3c00e3cc
  | 4 => mk128 0xffff00007ffe007f 0xfc000fffc00703f0
  | 5 => mk128 0xffffffff8000007f 0xfffff0000007fc00
  | _ => 0
private def q_0_1 : Nat → Bits
  | 0 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0x8c6934e0966311e2 0x4a49cc999b0c8b2a
  | 3 => mk128 0x14224425222402a4 0x29845282910a14c
  | 4 => mk128 0x2888114a4401254a 0x98008a52822502b0
  | 5 => mk128 0x4100800000884811 0x2122000000425400
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
private def lv_0_1_5_0 : List NodeSpec := [([], [0, 1, 2, 3, 4], [(0, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_0_1_5_0 : LevelOK rd_0_1 (subGoal 0 1) 5 lv_0_1_5_0 :=
  levelCheck_sound pp_0_1 (raw_faithful _ _ _) sl_0_1_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_0_1 (subGoal 0 1) 4)
    (by decide +kernel : levelCheck (freeVars 0 1) rd_0_1 (subGoal 0 1) sl_0_1 [[]] [] 5 lv_0_1_5_0 = true)
private def lv_0_1_5 : List NodeSpec := lv_0_1_5_0
private theorem ok_0_1_5 : LevelOK rd_0_1 (subGoal 0 1) 5 lv_0_1_5 := ok_0_1_5_0
private theorem lower_0_1 : Lower (freeVars 0 1) (subGoal 0 1) 6 :=
  lower_of_search (xs := [(inputs.getD 1 zero, 0, 2), (inputs.getD 2 zero, 32, 36), (inputs.getD 3 zero, 16, 24), (inputs.getD 4 zero, 8, 24), (inputs.getD 5 zero, 4, 36)]) ok_0_1_5 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube0_1

section Cube1_2

private def p_1_2 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 2 => mk128 0xeff9ffff8ffff8ff 0xdff3ffff1ffff1ff
  | 3 => mk128 0xf6fe3f9ff1f87f39 0xedfc7f3fe3f0fe73
  | 4 => mk128 0x3b7fc7e7fe3f87ce 0x76ff8fcffc7f0f9c
  | 5 => mk128 0x3c7ff807ffc007f0 0x78fff00fff800fe0
  | _ => 0
private def q_1_2 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 2 => mk128 0x500c0101024a2052 0xa0180202049440a5
  | 3 => mk128 0x8911922290915329 0x122324452122a652
  | 4 => mk128 0x4a0b40ca425158c 0x9416819484a2b18
  | 5 => mk128 0x3c52757490666f0 0x78a4eae920ccde0
  | _ => 0
private theorem pp_1_2 : properPairs (subGoal 1 2) (asRow p_1_2) (asRow q_1_2) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_1_2 : List Decor := rawDecor (freeMask 1 2) p_1_2 q_1_2
private def sl_1_2 : List (Sig × Nat) := [(subcube 1 34, 4)]
private theorem sl_1_2_ok : ∀ s ∈ sl_1_2, Slice (freeVars 1 2) (subGoal 1 2) s.1 s.2 := by
  intro s hs
  simp only [sl_1_2, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 1 34) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_1_34
private def lv_1_2_4_0 : List NodeSpec := [([], [0, 1, 2, 3], [(0, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_1_2_4_0 : LevelOK rd_1_2 (subGoal 1 2) 4 lv_1_2_4_0 :=
  levelCheck_sound pp_1_2 (raw_faithful _ _ _) sl_1_2_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_1_2 (subGoal 1 2) 3)
    (by decide +kernel : levelCheck (freeVars 1 2) rd_1_2 (subGoal 1 2) sl_1_2 [[]] [] 4 lv_1_2_4_0 = true)
private def lv_1_2_4 : List NodeSpec := lv_1_2_4_0
private theorem ok_1_2_4 : LevelOK rd_1_2 (subGoal 1 2) 4 lv_1_2_4 := ok_1_2_4_0
private theorem lower_1_2 : Lower (freeVars 1 2) (subGoal 1 2) 5 :=
  lower_of_search (xs := [(inputs.getD 2 zero, 8, 12), (inputs.getD 3 zero, 4, 12), (inputs.getD 4 zero, 4, 20), (inputs.getD 5 zero, 24, 56)]) ok_1_2_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube1_2

section Cube0_2

private def p_0_2 : Nat → Bits
  | 0 => mk128 0x3ffe1fcfe7fe1c63 0xc7fc787c3fe09d27
  | 1 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 2 => mk128 0xc38fe3f1f8e1e07c 0xf9879f8fc6036ada
  | 3 => mk128 0xfc0ffc01ff01ff80 0xfe07e00ff81c731c
  | 4 => mk128 0xffffe0001ffff 0x7fff0001f83e0
  | 5 => mk128 0xfff000000001ffff 0xfff80000001ffc00
  | _ => 0
private def q_0_2 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 2 => mk128 0x1012410281044024 0x48908a050421284a
  | 3 => mk128 0x89248895402aac80 0x9225212ab04c5314
  | 4 => mk128 0xaa4912804a533549 0x465560909683a0
  | 5 => mk128 0x3301db29949dda72 0xe5700643251bfc00
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
private def lv_0_2_5_0 : List NodeSpec := [([], [0, 1, 2, 3, 4], [(0, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_0_2_5_0 : LevelOK rd_0_2 (subGoal 0 2) 5 lv_0_2_5_0 :=
  levelCheck_sound pp_0_2 (raw_faithful _ _ _) sl_0_2_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_0_2 (subGoal 0 2) 4)
    (by decide +kernel : levelCheck (freeVars 0 2) rd_0_2 (subGoal 0 2) sl_0_2 [[]] [] 5 lv_0_2_5_0 = true)
private def lv_0_2_5 : List NodeSpec := lv_0_2_5_0
private theorem ok_0_2_5 : LevelOK rd_0_2 (subGoal 0 2) 5 lv_0_2_5 := ok_0_2_5_0
private theorem lower_0_2 : Lower (freeVars 0 2) (subGoal 0 2) 6 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 0, 1), (inputs.getD 2 zero, 8, 12), (inputs.getD 3 zero, 4, 12), (inputs.getD 4 zero, 4, 20), (inputs.getD 5 zero, 24, 56)]) ok_0_2_5 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube0_2

section Cube2_0

private def p_2_0 : Nat → Bits
  | 0 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0xff00fffe01f80f 0xe07f03fff01631f8
  | 3 => mk128 0xffff00fffffff0 0x7ffc07fff83e3f
  | 4 => mk128 0xff000000ffffffff 0xff800007ffffc03f
  | 5 => mk128 0xffffffff0001ffff 0xfffffff8001fffc0
  | _ => 0
private def q_2_0 : Nat → Bits
  | 0 => mk128 0x6090a0a022418b1 0x628b1468b2a2d6db
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0xaa5aa694651cfc0a 0xaa55537556963178
  | 3 => mk128 0xd49494a6a9496d58 0x1066d9266cd83a2d
  | 4 => mk128 0x98d8d8d8d191b66c 0xdb4082478f1f4036
  | 5 => mk128 0xe0e0e0e0e1e1c78f 0x1c78e384081dad80
  | _ => 0
private theorem pp_2_0 : properPairs (subGoal 2 0) (asRow p_2_0) (asRow q_2_0) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_2_0 : List Decor := rawDecor (freeMask 2 0) p_2_0 q_2_0
private def sl_2_0 : List (Sig × Nat) := [(subcube 2 1, 5)]
private theorem sl_2_0_ok : ∀ s ∈ sl_2_0, Slice (freeVars 2 0) (subGoal 2 0) s.1 s.2 := by
  intro s hs
  simp only [sl_2_0, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 2 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_2_1
private def lv_2_0_5_0 : List NodeSpec := [([], [0, 1, 2, 3, 4], [(0, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_2_0_5_0 : LevelOK rd_2_0 (subGoal 2 0) 5 lv_2_0_5_0 :=
  levelCheck_sound pp_2_0 (raw_faithful _ _ _) sl_2_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_2_0 (subGoal 2 0) 4)
    (by decide +kernel : levelCheck (freeVars 2 0) rd_2_0 (subGoal 2 0) sl_2_0 [[]] [] 5 lv_2_0_5_0 = true)
private def lv_2_0_5 : List NodeSpec := lv_2_0_5_0
private theorem ok_2_0_5 : LevelOK rd_2_0 (subGoal 2 0) 5 lv_2_0_5 := ok_2_0_5_0
private theorem lower_2_0 : Lower (freeVars 2 0) (subGoal 2 0) 6 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 24, 25), (inputs.getD 2 zero, 33, 37), (inputs.getD 3 zero, 17, 25), (inputs.getD 4 zero, 9, 25), (inputs.getD 5 zero, 5, 37)]) ok_2_0_5 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube2_0

section Cube1_0

private def p_1_0 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 2 => mk128 0xf807ffffffffffff 0x80fffffffffc3fff
  | 3 => mk128 0xfff803ffff807fff 0xff01fff807ffc7c7
  | 4 => mk128 0xfffffc01ffff807f 0xfffe03fff807f8f8
  | 5 => mk128 0xfffffffe0000007f 0xfffffc000007ff00
  | _ => 0
private def q_1_0 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0x5909249258890916 0x8b162c5b4b49db5b
  | 2 => mk128 0xaf424924a952522b 0x40ab56ad95942dad
  | 3 => mk128 0x325762393247644d 0xd5819b30c6e6c6c6
  | 4 => mk128 0xc46473b1c4644771 0xe6cd03c6e0c770f0
  | 5 => mk128 0x78783c1f878787e 0x78f1e2070707bf00
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
private def lv_1_0_5_0 : List NodeSpec := [([], [0, 1, 2, 3, 4], [(0, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_1_0_5_0 : LevelOK rd_1_0 (subGoal 1 0) 5 lv_1_0_5_0 :=
  levelCheck_sound pp_1_0 (raw_faithful _ _ _) sl_1_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_1_0 (subGoal 1 0) 4)
    (by decide +kernel : levelCheck (freeVars 1 0) rd_1_0 (subGoal 1 0) sl_1_0 [[]] [] 5 lv_1_0_5_0 = true)
private def lv_1_0_5 : List NodeSpec := lv_1_0_5_0
private theorem ok_1_0_5 : LevelOK rd_1_0 (subGoal 1 0) 5 lv_1_0_5 := ok_1_0_5_0
private theorem lower_1_0 : Lower (freeVars 1 0) (subGoal 1 0) 6 :=
  lower_of_search (xs := [(inputs.getD 1 zero, 12, 14), (inputs.getD 2 zero, 10, 14), (inputs.getD 3 zero, 6, 14), (inputs.getD 4 zero, 6, 22), (inputs.getD 5 zero, 26, 58)]) ok_1_0_5 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube1_0

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
private def lv_4_1_4_0 : List NodeSpec := [([], [0, 1, 2, 3], [(0, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_4_1_4_0 : LevelOK rd_4_1 (subGoal 4 1) 4 lv_4_1_4_0 :=
  levelCheck_sound pp_4_1 (raw_faithful _ _ _) sl_4_1_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_4_1 (subGoal 4 1) 3)
    (by decide +kernel : levelCheck (freeVars 4 1) rd_4_1 (subGoal 4 1) sl_4_1 [[]] [] 4 lv_4_1_4_0 = true)
private def lv_4_1_4 : List NodeSpec := lv_4_1_4_0
private theorem ok_4_1_4 : LevelOK rd_4_1 (subGoal 4 1) 4 lv_4_1_4 := ok_4_1_4_0
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
private def lv_6_0_4_0 : List NodeSpec := [([], [0, 1, 2, 3], [(0, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_6_0_4_0 : LevelOK rd_6_0 (subGoal 6 0) 4 lv_6_0_4_0 :=
  levelCheck_sound pp_6_0 (raw_faithful _ _ _) sl_6_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_6_0 (subGoal 6 0) 3)
    (by decide +kernel : levelCheck (freeVars 6 0) rd_6_0 (subGoal 6 0) sl_6_0 [[]] [] 4 lv_6_0_4_0 = true)
private def lv_6_0_4 : List NodeSpec := lv_6_0_4_0
private theorem ok_6_0_4 : LevelOK rd_6_0 (subGoal 6 0) 4 lv_6_0_4 := ok_6_0_4_0
private theorem lower_6_0 : Lower (freeVars 6 0) (subGoal 6 0) 5 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 24, 25), (inputs.getD 3 zero, 17, 25), (inputs.getD 4 zero, 9, 25), (inputs.getD 5 zero, 9, 41)]) ok_6_0_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube6_0

section Cube8_16

private def p_8_16 : Nat → Bits
  | 0 => mk128 0xbfcffcf8fff873f3 0xbfcffcf8fff873f3
  | 1 => mk128 0xdff39fff1c3ffc9f 0xdff39fff1c3ffc9f
  | 2 => mk128 0xebfc1f3fe03f8f1c 0xebfc1f3fe03f8f1c
  | 3 => mk128 0x0 0x0
  | 4 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 5 => mk128 0xf3ffe03fffc00fe0 0xf3ffe03fffc00fe0
  | _ => 0
private def q_8_16 : Nat → Bits
  | 0 => mk128 0x4061010824892131 0x4061010824892131
  | 1 => mk128 0x2088281109124486 0x2088281109124486
  | 2 => mk128 0x1523506a42a52b18 0x1523506a42a52b18
  | 3 => mk128 0x0 0x0
  | 4 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 5 => mk128 0xe0a1ab493064ec0 0xe0a1ab493064ec0
  | _ => 0
private theorem pp_8_16 : properPairs (subGoal 8 16) (asRow p_8_16) (asRow q_8_16) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_8_16 : List Decor := rawDecor (freeMask 8 16) p_8_16 q_8_16
private def sl_8_16 : List (Sig × Nat) := []
private theorem sl_8_16_ok : ∀ s ∈ sl_8_16, Slice (freeVars 8 16) (subGoal 8 16) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private def lv_8_16_3_0 : List NodeSpec := [([], [0, 1, 2, 3], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_8_16_3_0 : LevelOK rd_8_16 (subGoal 8 16) 3 lv_8_16_3_0 :=
  levelCheck_sound pp_8_16 (raw_faithful _ _ _) sl_8_16_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_8_16 (subGoal 8 16) 2)
    (by decide +kernel : levelCheck (freeVars 8 16) rd_8_16 (subGoal 8 16) sl_8_16 [[]] [] 3 lv_8_16_3_0 = true)
private def lv_8_16_3 : List NodeSpec := lv_8_16_3_0
private theorem ok_8_16_3 : LevelOK rd_8_16 (subGoal 8 16) 3 lv_8_16_3 := ok_8_16_3_0
private theorem lower_8_16 : Lower (freeVars 8 16) (subGoal 8 16) 4 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 2, 6), (inputs.getD 5 zero, 1, 33)]) ok_8_16_3 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube8_16

section Cube16_8

private def p_16_8 : Nat → Bits
  | 0 => mk128 0xbfcffcf8fff873f3 0xbfcffcf8fff873f3
  | 1 => mk128 0xdff39fff1c3ffc9f 0xdff39fff1c3ffc9f
  | 2 => mk128 0xebfc1f3fe03f8f1c 0xebfc1f3fe03f8f1c
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0x0 0x0
  | 5 => mk128 0xf3ffe03fffc00fe0 0xf3ffe03fffc00fe0
  | _ => 0
private def q_16_8 : Nat → Bits
  | 0 => mk128 0x4061010824892131 0x4061010824892131
  | 1 => mk128 0x2088281109124486 0x2088281109124486
  | 2 => mk128 0x1523506a42a52b18 0x1523506a42a52b18
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0x0 0x0
  | 5 => mk128 0xe0a1ab493064ec0 0xe0a1ab493064ec0
  | _ => 0
private theorem pp_16_8 : properPairs (subGoal 16 8) (asRow p_16_8) (asRow q_16_8) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_16_8 : List Decor := rawDecor (freeMask 16 8) p_16_8 q_16_8
private def sl_16_8 : List (Sig × Nat) := []
private theorem sl_16_8_ok : ∀ s ∈ sl_16_8, Slice (freeVars 16 8) (subGoal 16 8) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private def lv_16_8_3_0 : List NodeSpec := [([], [0, 1, 2, 3], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_16_8_3_0 : LevelOK rd_16_8 (subGoal 16 8) 3 lv_16_8_3_0 :=
  levelCheck_sound pp_16_8 (raw_faithful _ _ _) sl_16_8_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_16_8 (subGoal 16 8) 2)
    (by decide +kernel : levelCheck (freeVars 16 8) rd_16_8 (subGoal 16 8) sl_16_8 [[]] [] 3 lv_16_8_3_0 = true)
private def lv_16_8_3 : List NodeSpec := lv_16_8_3_0
private theorem ok_16_8_3 : LevelOK rd_16_8 (subGoal 16 8) 3 lv_16_8_3 := ok_16_8_3_0
private theorem lower_16_8 : Lower (freeVars 16 8) (subGoal 16 8) 4 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 2, 6), (inputs.getD 5 zero, 1, 33)]) ok_16_8_3 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube16_8

section Cube0_0

private def p_0_0 : Nat → Bits
  | 0 => mk128 0xfffffc01ffc01fff 0xff423f1ffe7f8e3f
  | 1 => mk128 0xf807fffffffffff 0xffbdc8e44788ffff
  | 2 => mk128 0xf0007ffe07ffe07e 0xc1f0f879f0f3cc
  | 3 => mk128 0xffff800007ffff80 0xfe00ff81ff03f0
  | 4 => mk128 0xfffffffff8000000 0xffff0001fffc00
  | 5 => mk128 0x0 0xfffffffe000000
  | _ => 0
private def q_0_0 : Nat → Bits
  | 0 => mk128 0xb28a9410494104b2 0xaa0013099a338615
  | 1 => mk128 0x51029a3929a3945 0x541cc864448838ea
  | 2 => mk128 0x502a4ed444ed4478 0x6c170b86970d34c
  | 3 => mk128 0x69f3006087379e10 0x18ee00de81dd03b0
  | 4 => mk128 0x8e7c7379e0060820 0x60f7bd0001eeec00
  | 5 => mk128 0x40038100381041 0x80fbeef776000000
  | _ => 0
private theorem pp_0_0 : properPairs (subGoal 0 0) (asRow p_0_0) (asRow q_0_0) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_0_0 : List Decor := rawDecor (freeMask 0 0) p_0_0 q_0_0
private def sl_0_0 : List (Sig × Nat) := [(subcube 0 32, 9), (subcube 4 0, 9), (subcube 32 0, 7), (subcube 0 16, 7), (subcube 0 4, 7), (subcube 16 0, 7), (subcube 0 8, 7), (subcube 8 0, 7), (subcube 0 1, 6), (subcube 32 4, 6), (subcube 0 2, 6), (subcube 2 0, 6), (subcube 1 0, 6), (subcube 4 1, 5), (subcube 0 34, 5), (subcube 2 1, 5), (subcube 1 2, 5), (subcube 1 32, 5), (subcube 6 0, 5), (subcube 8 16, 4), (subcube 16 8, 4)]
private theorem sl_0_0_ok : ∀ s ∈ sl_0_0, Slice (freeVars 0 0) (subGoal 0 0) s.1 s.2 := by
  intro s hs
  simp only [sl_0_0, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact slice_correct (ms := fixRows 0 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_0_32
  · exact slice_correct (ms := fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_4_0
  · exact slice_correct (ms := fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_32_0
  · exact slice_correct (ms := fixRows 0 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_0_16
  · exact slice_correct (ms := fixRows 0 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_0_4
  · exact slice_correct (ms := fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_16_0
  · exact slice_correct (ms := fixRows 0 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_0_8
  · exact slice_correct (ms := fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_8_0
  · exact slice_correct (ms := fixRows 0 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_0_1
  · exact slice_correct (ms := fixRows 32 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_32_4
  · exact slice_correct (ms := fixRows 0 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_0_2
  · exact slice_correct (ms := fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_2_0
  · exact slice_correct (ms := fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_1_0
  · exact slice_correct (ms := fixRows 4 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_4_1
  · exact slice_correct (ms := fixRows 0 34) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_0_34
  · exact slice_correct (ms := fixRows 2 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_2_1
  · exact slice_correct (ms := fixRows 1 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_1_2
  · exact slice_correct (ms := fixRows 1 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_1_32
  · exact slice_correct (ms := fixRows 6 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_6_0
  · exact slice_correct (ms := fixRows 8 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_8_16
  · exact slice_correct (ms := fixRows 16 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_16_8
private def lv_0_0_4_0 : List NodeSpec := [([(0, 1, 0), (1, 1, 0), (0, 4, 3), (1, 8, 6), (1, 4, 3), (0, 10, 7)], [0, 11, 2, 9, 5], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_0_0_4_0 : LevelOK rd_0_0 (subGoal 0 0) 4 lv_0_0_4_0 :=
  levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_0_0 (subGoal 0 0) 3)
    (by decide +kernel : levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] [] 4 lv_0_0_4_0 = true)
private def lv_0_0_4 : List NodeSpec := lv_0_0_4_0
private theorem ok_0_0_4 : LevelOK rd_0_0 (subGoal 0 0) 4 lv_0_0_4 := ok_0_0_4_0
private def ck120 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_4) 5
private def d120 : List NodeSpec := [([(0,1,0),(2,1,6),(0,4,3),(1,8,6),(1,4,3)],[7,0,2,9,10,5],[]),([(0,1,0),(1,1,0),(2,7,6),(0,4,3),(1,4,3)],[8,1,2,9,10,5],[]),([(0,1,0),(1,1,0),(2,7,6),(0,4,3),(1,4,3)],[8,0,2,9,10,5],[]),([(0,1,0),(1,1,0),(0,4,3),(1,8,6),(1,4,3)],[0,7,2,9,10,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q120 : ck120 [0] d120 = true := by decide +kernel
private def d121 : List NodeSpec := [([(0,1,0),(1,1,0),(0,4,3),(1,4,3),(0,9,7)],[6,0,10,2,8,5],[]),([(0,1,0),(1,2,6),(0,4,3),(1,8,6),(1,4,3)],[0,1,7,9,10,5],[]),([(0,1,0),(1,2,6),(0,4,3),(1,4,3),(2,9,6)],[10,0,1,7,8,5],[]),([(0,1,0),(0,4,3),(1,7,6),(1,4,3),(2,9,8)],[10,0,1,2,8,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q121 : ck120 [0] d121 = true := by decide +kernel
private def d122 : List NodeSpec := [([(0,1,0),(0,4,3),(1,7,6),(1,4,3),(2,9,6)],[10,0,1,2,8,5],[]),([(0,1,0),(0,4,3),(1,7,6),(1,4,3),(2,5,6)],[10,0,1,2,8,9],[]),([(0,1,0),(0,4,3),(1,4,3),(2,8,6),(3,7,9)],[10,9,0,1,2,5],[]),([(0,1,0),(0,4,3),(1,4,3),(2,8,6),(2,5,6)],[9,10,0,1,2,7],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q122 : ck120 [] d122 = true := by decide +kernel
private def lv_0_0_5_0 : List NodeSpec := (d120 ++ (d121 ++ d122))

private theorem ok_0_0_5_0 : LevelOK rd_0_0 (subGoal 0 0) 5 lv_0_0_5_0 := by
  have go {ids ds} (h : ck120 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 5 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_4) h
  exact (levelOK_append (go q120) (levelOK_append (go q121) (go q122)))
private def ck123 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_4) 5
private def d123 : List NodeSpec := [([(1,1,0),(3,1,0),(0,4,3),(1,4,3),(0,9,6)],[7,0,10,2,8,5],[]),([(1,1,0),(3,2,6),(0,4,3),(3,8,6),(1,4,3)],[9,7,0,1,10,5],[]),([(1,1,0),(3,2,6),(0,4,3),(1,4,3),(0,9,6)],[7,0,1,10,8,5],[]),([(1,1,0),(0,4,3),(3,7,6),(1,4,3),(0,9,8)],[10,8,0,1,2,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q123 : ck123 [] d123 = true := by decide +kernel
private def d124 : List NodeSpec := [([(1,1,0),(0,4,3),(3,7,6),(1,4,3),(0,9,6)],[8,0,1,10,2,5],[]),([(1,1,0),(0,4,3),(3,7,6),(1,4,3),(0,5,6)],[8,0,1,10,2,9],[]),([(1,1,0),(0,4,3),(1,4,3),(0,8,6),(3,7,9)],[10,0,1,9,2,5],[]),([(1,1,0),(0,4,3),(1,4,3),(0,8,6),(0,5,6)],[0,1,9,10,2,7],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q124 : ck123 [] d124 = true := by decide +kernel
private def d125 : List NodeSpec := [([(2,1,0),(1,0,6),(0,4,3),(3,8,7),(1,4,3)],[9,0,1,2,10,5],[]),([(2,1,0),(1,0,6),(0,4,3),(1,4,3),(0,9,7)],[0,1,10,2,8,5],[]),([(2,1,0),(2,1,6),(0,4,3),(1,8,7),(1,4,3)],[0,1,2,9,10,5],[]),([(2,1,0),(2,1,6),(0,4,3),(1,4,3),(2,9,7)],[10,0,1,2,8,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q125 : ck123 [] d125 = true := by decide +kernel
private def lv_0_0_5_1 : List NodeSpec := (d123 ++ (d124 ++ d125))

private theorem ok_0_0_5_1 : LevelOK rd_0_0 (subGoal 0 0) 5 lv_0_0_5_1 := by
  have go {ids ds} (h : ck123 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 5 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_4) h
  exact (levelOK_append (go q123) (levelOK_append (go q124) (go q125)))
private def ck126 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_4) 5
private def d126 : List NodeSpec := [([(0,3,0),(1,3,0),(2,7,6),(1,4,8),(2,9,2)],[10,8,0,1,4,5],[]),([(0,3,0),(1,3,0),(2,7,6),(2,4,8),(3,4,8)],[10,9,0,1,2,5],[]),([(0,3,0),(1,3,0),(2,7,6),(2,4,8),(2,5,9)],[8,10,0,1,2,4],[]),([(0,3,0),(3,3,1),(1,6,7),(0,4,8),(1,4,8)],[0,9,1,2,10,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q126 : ck126 [] d126 = true := by decide +kernel
private def d127 : List NodeSpec := [([(0,3,0),(3,3,1),(1,6,7),(0,4,8),(2,5,9)],[10,0,8,1,2,4],[]),([(0,3,0),(3,3,1),(1,6,7),(3,4,8),(1,2,9)],[0,8,1,10,4,5],[]),([(1,3,0),(2,3,1),(2,6,7),(1,4,8),(2,9,2)],[10,0,8,1,4,5],[]),([(1,3,0),(2,3,1),(2,6,7),(2,4,8),(3,4,8)],[10,9,0,1,2,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q127 : ck126 [] d127 = true := by decide +kernel
private def d128 : List NodeSpec := [([(1,3,0),(2,3,1),(2,6,7),(2,4,8),(2,5,9)],[0,8,10,1,2,4],[]),([(0,3,1),(1,3,1),(2,7,6),(0,4,8),(1,4,8)],[9,0,1,2,10,5],[]),([(0,3,1),(1,3,1),(2,7,6),(0,4,8),(2,5,9)],[8,0,10,1,2,4],[]),([(0,3,1),(1,3,1),(2,7,6),(3,4,8),(1,2,9)],[8,0,1,10,4,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q128 : ck126 [] d128 = true := by decide +kernel
private def lv_0_0_5_2 : List NodeSpec := (d126 ++ (d127 ++ d128))

private theorem ok_0_0_5_2 : LevelOK rd_0_0 (subGoal 0 0) 5 lv_0_0_5_2 := by
  have go {ids ds} (h : ck126 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 5 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_4) h
  exact (levelOK_append (go q126) (levelOK_append (go q127) (go q128)))
private def ck129 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_4) 5
private def d129 : List NodeSpec := [([(0,4,0),(1,4,0),(2,7,6),(1,3,8),(2,9,2)],[10,8,0,1,3,5],[]),([(0,4,0),(1,4,0),(2,7,6),(2,3,8),(3,3,8)],[10,9,0,1,2,5],[]),([(0,4,0),(1,4,0),(2,7,6),(2,3,8),(2,5,9)],[8,10,0,1,2,3],[]),([(0,4,0),(3,4,1),(1,6,7),(0,3,8),(1,3,8)],[9,0,1,2,10,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q129 : ck129 [] d129 = true := by decide +kernel
private def d130 : List NodeSpec := [([(0,4,0),(3,4,1),(1,6,7),(0,3,8),(2,5,9)],[10,0,8,1,2,3],[]),([(0,4,0),(3,4,1),(1,6,7),(3,3,8),(1,2,9)],[0,8,1,10,3,5],[]),([(1,4,0),(2,4,1),(2,6,7),(1,3,8),(2,9,2)],[10,0,8,1,3,5],[]),([(1,4,0),(2,4,1),(2,6,7),(2,3,8),(3,3,8)],[10,9,0,1,2,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q130 : ck129 [] d130 = true := by decide +kernel
private def d131 : List NodeSpec := [([(1,4,0),(2,4,1),(2,6,7),(2,3,8),(2,5,9)],[0,8,1,10,2,3],[]),([(0,4,1),(1,4,1),(2,7,6),(0,3,8),(1,3,8)],[9,0,1,2,10,5],[]),([(0,4,1),(1,4,1),(2,7,6),(0,3,8),(2,5,9)],[8,0,1,10,2,3],[]),([(0,4,1),(1,4,1),(2,7,6),(3,3,8),(1,2,9)],[8,0,1,10,3,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q131 : ck129 [] d131 = true := by decide +kernel
private def lv_0_0_5_3 : List NodeSpec := (d129 ++ (d130 ++ d131))

private theorem ok_0_0_5_3 : LevelOK rd_0_0 (subGoal 0 0) 5 lv_0_0_5_3 := by
  have go {ids ds} (h : ck129 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 5 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_4) h
  exact (levelOK_append (go q129) (levelOK_append (go q130) (go q131)))
private def lv_0_0_5 : List NodeSpec := ((lv_0_0_5_0 ++ lv_0_0_5_1) ++ (lv_0_0_5_2 ++ lv_0_0_5_3))
private theorem ok_0_0_5 : LevelOK rd_0_0 (subGoal 0 0) 5 lv_0_0_5 := (levelOK_append (levelOK_append ok_0_0_5_0 ok_0_0_5_1) (levelOK_append ok_0_0_5_2 ok_0_0_5_3))
private def ck132 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_5) 6
private def d132 : List NodeSpec := [([(0,1,0),(2,0,6),(0,4,3),(1,4,3)],[7,0,1,2,8,9,5],[]),([(0,1,0),(2,0,6),(0,4,3),(1,4,3)],[7,6,1,2,8,9,5],[(0,[2,3])]),([(0,1,0),(2,1,6),(0,4,3),(1,4,3)],[7,0,1,2,8,9,5],[]),([(0,1,0),(2,1,6),(0,4,3),(1,8,6)],[7,0,2,3,9,4,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q132 : ck132 [0] d132 = true := by decide +kernel
private def d133 : List NodeSpec := [([(0,1,0),(2,1,6),(0,4,3),(1,4,3)],[7,6,0,2,8,9,5],[(0,[2,3])]),([(0,1,0),(1,1,0),(2,7,6),(0,4,3)],[8,1,2,9,3,4,5],[]),([(0,1,0),(1,1,0),(2,7,6),(1,4,3)],[8,1,2,3,4,9,5],[]),([(0,1,0),(1,1,0),(2,7,6),(2,4,3)],[9,8,1,2,3,4,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q133 : ck132 [0,1] d133 = true := by decide +kernel
private def d134 : List NodeSpec := [([(0,1,0),(1,1,0),(2,7,6),(3,4,3)],[9,8,1,2,3,4,5],[]),([(0,1,0),(1,1,0),(0,4,3),(1,4,3)],[6,1,7,2,8,9,5],[]),([(0,1,0),(1,1,0),(2,7,6),(0,4,3)],[8,0,2,9,3,4,5],[]),([(0,1,0),(1,1,0),(2,7,6),(1,4,3)],[8,0,2,3,4,9,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q134 : ck132 [1,2] d134 = true := by decide +kernel
private def lv_0_0_6_0 : List NodeSpec := (d132 ++ (d133 ++ d134))

private theorem ok_0_0_6_0 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6_0 := by
  have go {ids ds} (h : ck132 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 6 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_5) h
  exact (levelOK_append (go q132) (levelOK_append (go q133) (go q134)))
private def ck135 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_5) 6
private def d135 : List NodeSpec := [([(0,1,0),(1,1,0),(2,7,6),(2,4,3)],[9,8,0,2,3,4,5],[]),([(0,1,0),(1,1,0),(2,7,6),(3,4,3)],[9,8,0,2,3,4,5],[]),([(0,1,0),(1,1,0),(0,4,3),(1,8,6)],[0,7,2,3,9,4,5],[]),([(0,1,0),(1,1,0),(0,4,3),(1,4,3)],[6,0,7,2,8,9,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q135 : ck135 [2,3,4] d135 = true := by decide +kernel
private def d136 : List NodeSpec := [([(0,1,0),(1,1,0),(1,4,3),(0,8,7)],[6,0,9,2,3,4,5],[]),([(0,1,0),(1,2,6),(0,4,3),(1,4,3)],[0,1,7,8,9,5],[(3,[0,1]),(5,[0,1])]),([(0,1,0),(1,2,6),(1,3,6),(0,4,8)],[0,1,7,9,8,4,5],[(6,[0,1])]),([(0,1,0),(1,2,6),(1,3,6),(3,4,8)],[9,0,1,7,8,4,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q136 : ck135 [4] d136 = true := by decide +kernel
private def d137 : List NodeSpec := [([(0,1,0),(1,2,6),(1,3,6),(0,4,3)],[0,1,7,9,8,4,5],[(3,[0,1])]),([(0,1,0),(1,2,6),(1,3,6),(3,4,3)],[9,0,1,7,8,4,5],[]),([(0,1,0),(1,2,6),(2,3,6),(1,4,8)],[8,0,1,7,4,9,5],[(7,[0,1])]),([(0,1,0),(1,2,6),(2,3,6),(2,4,8)],[8,9,0,1,7,4,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q137 : ck135 [] d137 = true := by decide +kernel
private def lv_0_0_6_1 : List NodeSpec := (d135 ++ (d136 ++ d137))

private theorem ok_0_0_6_1 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6_1 := by
  have go {ids ds} (h : ck135 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 6 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_5) h
  exact (levelOK_append (go q135) (levelOK_append (go q136) (go q137)))
private def ck138 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_5) 6
private def d138 : List NodeSpec := [([(0,1,0),(1,2,6),(2,3,6),(1,4,3)],[8,0,1,7,4,9,5],[(5,[0,1])]),([(0,1,0),(1,2,6),(2,3,6),(2,4,3)],[9,8,0,1,7,4,5],[]),([(0,1,0),(1,2,6),(1,4,6),(0,8,3)],[0,1,7,9,3,8,5],[(3,[0,1])]),([(0,1,0),(1,2,6),(1,4,6),(2,8,3)],[9,0,1,7,3,8,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q138 : ck138 [] d138 = true := by decide +kernel
private def d139 : List NodeSpec := [([(0,1,0),(1,2,6),(1,4,6),(0,4,3)],[0,1,7,9,3,8,5],[(3,[0,1])]),([(0,1,0),(1,2,6),(1,4,6),(2,4,3)],[9,0,1,7,3,8,5],[]),([(0,1,0),(1,2,6),(2,4,6),(1,3,8)],[8,0,1,7,3,9,5],[(5,[0,1])]),([(0,1,0),(1,2,6),(2,4,6),(2,3,8)],[8,9,0,1,7,3,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q139 : ck138 [] d139 = true := by decide +kernel
private def d140 : List NodeSpec := [([(0,1,0),(1,2,6),(2,4,6),(1,4,3)],[8,0,1,7,3,9,5],[(5,[0,1])]),([(0,1,0),(1,2,6),(2,4,6),(3,4,3)],[9,8,0,1,7,3,5],[]),([(0,1,0),(1,2,6),(0,4,3),(1,8,6)],[0,1,7,3,9,4,5],[(3,[0,1]),(6,[0,1])]),([(0,1,0),(1,2,6),(0,4,3),(1,4,3)],[6,0,1,7,8,9,5],[(0,[0,1,2,3]),(1,[2,3]),(3,[0,1]),(5,[0,1]),(9,[2,3])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q140 : ck138 [5,6] d140 = true := by decide +kernel
private def lv_0_0_6_2 : List NodeSpec := (d138 ++ (d139 ++ d140))

private theorem ok_0_0_6_2 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6_2 := by
  have go {ids ds} (h : ck138 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 6 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_5) h
  exact (levelOK_append (go q138) (levelOK_append (go q139) (go q140)))
private def ck141 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_5) 6
private def d141 : List NodeSpec := [([(0,1,0),(1,2,6),(1,4,3),(2,8,6)],[9,0,1,7,3,4,5],[(5,[0,1]),(7,[0,1])]),([(0,1,0),(1,2,6),(2,4,3),(1,6,8)],[9,0,1,7,3,4,5],[(3,[0,1]),(7,[0,1])]),([(0,1,0),(1,2,6),(3,4,3),(1,6,8)],[9,0,1,7,3,4,5],[(5,[0,1]),(6,[0,1])]),([(0,1,0),(1,3,6),(2,7,6),(0,4,7)],[8,0,1,2,9,4,5],[(3,[0,1])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q141 : ck141 [6] d141 = true := by decide +kernel
private def d142 : List NodeSpec := [([(0,1,0),(1,3,6),(1,4,6),(0,8,7)],[0,1,2,9,7,8,5],[(3,[0,1])]),([(0,1,0),(1,3,6),(1,4,6),(0,4,7)],[0,1,2,9,7,8,5],[(3,[0,1])]),([(0,1,0),(1,3,6),(1,4,6),(0,8,7)],[0,1,2,9,7,4,5],[(0,[0,1,2]),(3,[0,1])]),([(0,1,0),(1,3,6),(0,4,7),(2,5,6)],[9,0,1,2,8,7,4],[(6,[0,3])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q142 : ck141 [] d142 = true := by decide +kernel
private def d143 : List NodeSpec := [([(0,1,0),(1,3,6),(3,4,7),(2,5,6)],[8,9,0,1,2,7,4],[]),([(0,1,0),(1,3,6),(1,4,6),(0,8,3)],[0,1,2,9,7,8,5],[(3,[])]),([(0,1,0),(1,3,6),(1,4,6),(0,8,7)],[0,1,2,3,9,8,5],[(0,[0,1,2]),(3,[0,1])]),([(0,1,0),(1,3,6),(1,4,6),(0,4,3)],[0,1,2,9,7,8,5],[(3,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q143 : ck141 [] d143 = true := by decide +kernel
private def lv_0_0_6_3 : List NodeSpec := (d141 ++ (d142 ++ d143))

private theorem ok_0_0_6_3 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6_3 := by
  have go {ids ds} (h : ck141 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 6 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_5) h
  exact (levelOK_append (go q141) (levelOK_append (go q142) (go q143)))
private def ck144 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_5) 6
private def d144 : List NodeSpec := [([(0,1,0),(1,3,6),(0,4,3),(2,5,6)],[9,0,1,2,8,7,4],[(3,[0,3])]),([(0,1,0),(1,3,6),(3,4,3),(2,5,6)],[8,9,0,1,2,7,4],[]),([(0,1,0),(2,3,6),(1,4,7),(1,6,7)],[0,1,2,9,4,8,5],[(5,[0,1]),(6,[])]),([(0,1,0),(2,3,6),(1,4,7),(2,4,6)],[7,9,0,1,2,8,5],[(3,[0,1])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q144 : ck144 [] d144 = true := by decide +kernel
private def d145 : List NodeSpec := [([(0,1,0),(2,3,6),(1,4,7),(2,8,6)],[7,9,0,1,2,4,5],[(5,[0,1])]),([(0,1,0),(2,3,6),(1,4,7),(2,5,6)],[7,9,0,1,2,4,8],[(7,[0,3])]),([(0,1,0),(2,3,6),(2,4,7),(2,5,6)],[7,9,8,0,1,2,4],[]),([(0,1,0),(2,3,6),(2,4,6),(1,8,7)],[7,8,9,0,1,2,5],[(5,[0,1])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q145 : ck144 [] d145 = true := by decide +kernel
private def d146 : List NodeSpec := [([(0,1,0),(2,3,6),(2,4,6),(1,8,7)],[8,9,0,1,2,3,5],[(0,[0,1,2]),(5,[0,1])]),([(0,1,0),(2,3,6),(2,4,6),(1,3,8)],[7,8,0,1,2,9,5],[(5,[])]),([(0,1,0),(2,3,6),(2,4,6),(1,4,3)],[7,8,0,1,2,9,5],[(3,[0,1])]),([(0,1,0),(2,3,6),(1,4,3),(2,5,6)],[7,9,0,1,2,4,8],[(5,[0,3])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q146 : ck144 [] d146 = true := by decide +kernel
private def lv_0_0_6_4 : List NodeSpec := (d144 ++ (d145 ++ d146))

private theorem ok_0_0_6_4 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6_4 := by
  have go {ids ds} (h : ck144 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 6 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_5) h
  exact (levelOK_append (go q144) (levelOK_append (go q145) (go q146)))
private def ck147 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_5) 6
private def d147 : List NodeSpec := [([(0,1,0),(2,3,6),(2,4,3),(2,5,6)],[8,7,9,0,1,2,4],[]),([(0,1,0),(1,4,6),(2,7,6),(0,7,3)],[8,0,1,2,9,3,5],[(6,[0,1])]),([(0,1,0),(1,4,6),(0,7,3),(2,5,6)],[9,0,1,2,8,3,7],[(3,[0,3])]),([(0,1,0),(1,4,6),(2,7,3),(2,5,6)],[8,9,0,1,2,3,7],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q147 : ck147 [] d147 = true := by decide +kernel
private def d148 : List NodeSpec := [([(0,1,0),(1,4,6),(0,4,3),(2,5,6)],[9,0,1,2,8,3,7],[(3,[0,3])]),([(0,1,0),(1,4,6),(2,4,3),(2,5,6)],[8,9,0,1,2,3,7],[]),([(0,1,0),(2,4,6),(1,3,7),(1,6,7)],[0,1,2,3,8,9,5],[(3,[]),(7,[0,1])]),([(0,1,0),(2,4,6),(1,3,7),(2,5,6)],[7,9,0,1,2,3,8],[(5,[0,3])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q148 : ck147 [] d148 = true := by decide +kernel
private def d149 : List NodeSpec := [([(0,1,0),(2,4,6),(2,3,7),(2,5,6)],[7,9,8,0,1,2,3],[]),([(0,1,0),(2,4,6),(1,4,3),(2,5,6)],[7,9,0,1,2,3,8],[(5,[0,3])]),([(0,1,0),(2,4,6),(3,4,3),(2,5,6)],[8,7,9,0,1,2,3],[]),([(0,1,0),(0,4,3),(1,7,6),(1,4,3)],[0,1,2,8,9,5],[(3,[0,2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q149 : ck147 [0,3,7] d149 = true := by decide +kernel
private def lv_0_0_6_5 : List NodeSpec := (d147 ++ (d148 ++ d149))

private theorem ok_0_0_6_5 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6_5 := by
  have go {ids ds} (h : ck147 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 6 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_5) h
  exact (levelOK_append (go q147) (levelOK_append (go q148) (go q149)))
private def ck150 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_5) 6
private def d150 : List NodeSpec := [([(0,1,0),(0,4,3),(1,7,6),(1,4,3)],[6,0,1,2,8,9,5],[(0,[0,1,2,3]),(1,[0,1,2,3]),(3,[0,2]),(5,[])]),([(0,1,0),(0,4,3),(1,7,6),(2,5,6)],[9,0,1,2,3,8,4],[(3,[0,3]),(6,[0,3])]),([(0,1,0),(0,4,3),(1,4,3),(2,8,6)],[9,0,1,2,7,5],[(5,[0,3])]),([(0,1,0),(0,4,3),(1,4,3),(2,8,6)],[9,6,0,1,2,7,5],[(0,[0,1,2,3]),(1,[0,1,2,3]),(3,[]),(5,[0,3])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q150 : ck150 [0,5,6,8,9,10,11] d150 = true := by decide +kernel
private def d151 : List NodeSpec := [([(0,1,0),(0,4,3),(1,4,3),(2,5,6)],[9,0,1,2,7,8],[(3,[0,3]),(5,[0,3])]),([(0,1,0),(0,4,3),(1,4,3),(2,5,6)],[9,6,0,1,2,7,8],[(0,[1,2]),(1,[0,1,2,3]),(3,[0,3]),(5,[0,3]),(9,[1,2])]),([(0,1,0),(1,4,3),(2,7,6),(2,5,6)],[8,9,0,1,2,3,4],[(5,[0,3]),(7,[0,3])]),([(0,1,0),(2,4,3),(1,6,7),(2,5,6)],[9,8,0,1,2,3,4],[(3,[0,3]),(7,[0,3])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q151 : ck150 [9,11] d151 = true := by decide +kernel
private def d152 : List NodeSpec := [([(0,1,0),(3,4,3),(1,6,7),(2,5,6)],[9,8,0,1,2,3,4],[(5,[0,3]),(6,[0,3])]),([(1,1,0),(2,1,0),(0,4,3),(1,4,3)],[7,1,6,2,8,9,5],[(0,[2,3])]),([(1,1,0),(3,1,0),(0,4,3),(1,4,3)],[7,0,6,2,8,9,5],[(0,[2,3])]),([(1,1,0),(3,1,0),(1,4,3),(0,8,6)],[7,0,9,2,3,4,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q152 : ck150 [12] d152 = true := by decide +kernel
private def lv_0_0_6_6 : List NodeSpec := (d150 ++ (d151 ++ d152))

private theorem ok_0_0_6_6 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6_6 := by
  have go {ids ds} (h : ck150 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 6 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_5) h
  exact (levelOK_append (go q150) (levelOK_append (go q151) (go q152)))
private def ck153 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_5) 6
private def d153 : List NodeSpec := [([(1,1,0),(3,2,6),(0,4,3),(1,4,3)],[7,0,1,8,9,5],[(3,[0,1]),(5,[0,1])]),([(1,1,0),(3,2,6),(0,3,6),(1,4,8)],[7,0,1,8,4,9,5],[(7,[0,1])]),([(1,1,0),(3,2,6),(0,3,6),(2,4,8)],[7,9,0,1,8,4,5],[]),([(1,1,0),(3,2,6),(0,3,6),(1,4,3)],[7,0,1,8,4,9,5],[(5,[0,1])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q153 : ck153 [] d153 = true := by decide +kernel
private def d154 : List NodeSpec := [([(1,1,0),(3,2,6),(0,3,6),(2,4,3)],[9,7,0,1,8,4,5],[]),([(1,1,0),(3,2,6),(3,3,6),(1,4,8)],[8,7,0,1,4,9,5],[]),([(1,1,0),(3,2,6),(3,3,6),(2,4,8)],[8,7,0,1,9,4,5],[(6,[0,1])]),([(1,1,0),(3,2,6),(3,3,6),(0,4,3)],[8,7,0,1,9,4,5],[(3,[0,1])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q154 : ck153 [] d154 = true := by decide +kernel
private def d155 : List NodeSpec := [([(1,1,0),(3,2,6),(3,3,6),(3,4,3)],[9,8,7,0,1,4,5],[]),([(1,1,0),(3,2,6),(0,4,6),(1,3,8)],[7,0,1,8,3,9,5],[(5,[0,1])]),([(1,1,0),(3,2,6),(0,4,6),(2,3,8)],[7,9,0,1,8,3,5],[]),([(1,1,0),(3,2,6),(0,4,6),(1,4,3)],[7,0,1,8,3,9,5],[(5,[0,1])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q155 : ck153 [] d155 = true := by decide +kernel
private def lv_0_0_6_7 : List NodeSpec := (d153 ++ (d154 ++ d155))

private theorem ok_0_0_6_7 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6_7 := by
  have go {ids ds} (h : ck153 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 6 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_5) h
  exact (levelOK_append (go q153) (levelOK_append (go q154) (go q155)))
private def ck156 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_5) 6
private def d156 : List NodeSpec := [([(1,1,0),(3,2,6),(0,4,6),(3,4,3)],[9,7,0,1,8,3,5],[]),([(1,1,0),(3,2,6),(3,4,6),(1,3,8)],[8,7,0,1,3,9,5],[]),([(1,1,0),(3,2,6),(3,4,6),(2,3,8)],[8,7,0,1,9,3,5],[(3,[0,1])]),([(1,1,0),(3,2,6),(3,4,6),(0,4,3)],[8,7,0,1,9,3,5],[(3,[0,1])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q156 : ck156 [] d156 = true := by decide +kernel
private def d157 : List NodeSpec := [([(1,1,0),(3,2,6),(3,4,6),(2,4,3)],[8,9,7,0,1,3,5],[]),([(1,1,0),(3,2,6),(0,4,3),(3,8,6)],[9,7,0,1,3,4,5],[(3,[0,1]),(6,[0,1])]),([(1,1,0),(3,2,6),(0,4,3),(1,4,3)],[7,0,1,6,8,9,5],[(0,[0,1,2,3]),(1,[2,3]),(3,[0,1]),(5,[0,1]),(9,[2,3])]),([(1,1,0),(3,2,6),(1,4,3),(0,8,6)],[7,0,1,9,3,4,5],[(5,[0,1]),(7,[0,1])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q157 : ck156 [13,14] d157 = true := by decide +kernel
private def d158 : List NodeSpec := [([(1,1,0),(3,2,6),(2,4,3),(2,6,8)],[7,0,1,9,3,4,5],[(3,[0,1]),(7,[0,1])]),([(1,1,0),(3,2,6),(3,4,3),(2,6,8)],[7,0,1,9,3,4,5],[(5,[0,1]),(6,[0,1])]),([(1,1,0),(0,3,6),(2,6,7),(1,4,7)],[8,0,1,2,4,9,5],[(5,[0,1])]),([(1,1,0),(0,3,6),(1,4,7),(0,4,6)],[0,1,7,9,2,8,5],[(3,[0,1])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q158 : ck156 [] d158 = true := by decide +kernel
private def lv_0_0_6_8 : List NodeSpec := (d156 ++ (d157 ++ d158))

private theorem ok_0_0_6_8 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6_8 := by
  have go {ids ds} (h : ck156 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 6 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_5) h
  exact (levelOK_append (go q156) (levelOK_append (go q157) (go q158)))
private def ck159 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_5) 6
private def d159 : List NodeSpec := [([(1,1,0),(0,3,6),(1,4,7),(0,8,6)],[0,1,7,9,2,4,5],[(5,[0,1])]),([(1,1,0),(0,3,6),(1,4,7),(0,5,6)],[0,1,7,9,2,4,8],[(7,[0,3])]),([(1,1,0),(0,3,6),(2,4,7),(0,5,6)],[8,0,1,7,9,2,4],[]),([(1,1,0),(0,3,6),(0,4,6),(1,8,7)],[0,1,7,8,9,2,5],[(5,[0,1])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q159 : ck159 [] d159 = true := by decide +kernel
private def d160 : List NodeSpec := [([(1,1,0),(0,3,6),(0,4,6),(1,8,7)],[0,1,8,9,2,3,5],[(0,[0,1,2]),(5,[0,1])]),([(1,1,0),(0,3,6),(0,4,6),(1,3,8)],[0,1,7,8,2,9,5],[(5,[])]),([(1,1,0),(0,3,6),(0,4,6),(1,4,3)],[0,1,7,8,2,9,5],[(3,[0,1])]),([(1,1,0),(0,3,6),(1,4,3),(0,5,6)],[0,1,7,9,2,4,8],[(5,[0,3])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q160 : ck159 [] d160 = true := by decide +kernel
private def d161 : List NodeSpec := [([(1,1,0),(0,3,6),(2,4,3),(0,5,6)],[8,0,1,7,9,2,4],[]),([(1,1,0),(3,3,6),(1,4,7),(0,5,6)],[7,0,1,9,2,4,8],[]),([(1,1,0),(3,3,6),(2,4,7),(2,6,7)],[0,1,9,2,8,4,5],[(3,[0,1]),(7,[])]),([(1,1,0),(3,3,6),(2,4,7),(3,8,6)],[7,9,0,1,2,4,5],[(3,[0,1])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q161 : ck159 [] d161 = true := by decide +kernel
private def lv_0_0_6_9 : List NodeSpec := (d159 ++ (d160 ++ d161))

private theorem ok_0_0_6_9 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6_9 := by
  have go {ids ds} (h : ck159 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 6 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_5) h
  exact (levelOK_append (go q159) (levelOK_append (go q160) (go q161)))
private def ck162 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_5) 6
private def d162 : List NodeSpec := [([(1,1,0),(3,3,6),(2,4,7),(3,4,6)],[9,7,0,1,2,8,5],[(3,[0,1])]),([(1,1,0),(3,3,6),(2,4,7),(0,5,6)],[7,0,1,9,2,8,4],[(6,[0,3])]),([(1,1,0),(3,3,6),(3,4,6),(1,7,8)],[8,7,9,0,1,2,5],[(3,[0,1])]),([(1,1,0),(3,3,6),(3,4,6),(1,7,8)],[8,9,0,1,2,3,5],[(0,[0,1,2]),(3,[0,1])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q162 : ck162 [] d162 = true := by decide +kernel
private def d163 : List NodeSpec := [([(1,1,0),(3,3,6),(3,4,6),(2,3,8)],[8,7,0,1,2,9,5],[(3,[])]),([(1,1,0),(3,3,6),(3,4,6),(0,4,3)],[8,7,0,1,2,9,5],[(3,[])]),([(1,1,0),(3,3,6),(0,4,3),(0,5,6)],[7,0,1,9,2,8,4],[(3,[0,3])]),([(1,1,0),(3,3,6),(3,4,3),(0,5,6)],[8,7,0,1,9,2,4],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q163 : ck162 [] d163 = true := by decide +kernel
private def d164 : List NodeSpec := [([(1,1,0),(0,4,6),(2,6,7),(1,3,7)],[8,0,1,2,3,9,5],[(7,[0,1])]),([(1,1,0),(0,4,6),(1,3,7),(0,5,6)],[0,1,7,9,2,3,8],[(5,[0,3])]),([(1,1,0),(0,4,6),(2,3,7),(0,5,6)],[8,0,1,7,9,2,3],[]),([(1,1,0),(0,4,6),(1,4,3),(0,5,6)],[0,1,7,9,2,3,8],[(5,[0,3])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q164 : ck162 [] d164 = true := by decide +kernel
private def lv_0_0_6_10 : List NodeSpec := (d162 ++ (d163 ++ d164))

private theorem ok_0_0_6_10 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6_10 := by
  have go {ids ds} (h : ck162 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 6 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_5) h
  exact (levelOK_append (go q162) (levelOK_append (go q163) (go q164)))
private def ck165 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_5) 6
private def d165 : List NodeSpec := [([(1,1,0),(0,4,6),(3,4,3),(0,5,6)],[8,0,1,7,9,2,3],[]),([(1,1,0),(3,4,6),(1,3,7),(0,5,6)],[7,0,1,9,2,3,8],[]),([(1,1,0),(3,4,6),(2,3,7),(2,6,7)],[0,1,9,2,8,3,5],[(5,[]),(6,[0,1])]),([(1,1,0),(3,4,6),(2,3,7),(0,5,6)],[7,0,1,9,2,8,3],[(3,[0,3])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q165 : ck165 [] d165 = true := by decide +kernel
private def d166 : List NodeSpec := [([(1,1,0),(3,4,6),(0,4,3),(0,5,6)],[7,0,1,9,2,8,3],[(3,[0,3])]),([(1,1,0),(3,4,6),(2,4,3),(0,5,6)],[7,8,0,1,9,2,3],[]),([(1,1,0),(0,4,3),(3,7,6),(1,4,3)],[8,0,1,2,9,5],[(3,[0,2])]),([(1,1,0),(0,4,3),(3,7,6),(1,4,3)],[8,0,1,6,2,9,5],[(0,[0,1,2,3]),(1,[0,1,2,3]),(3,[0,2]),(5,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q166 : ck165 [13,15,16,17] d166 = true := by decide +kernel
private def d167 : List NodeSpec := [([(1,1,0),(0,4,3),(3,7,6),(0,5,6)],[8,0,1,9,2,3,4],[(3,[0,3]),(6,[0,3])]),([(1,1,0),(0,4,3),(1,4,3),(0,8,6)],[0,1,9,2,7,5],[(5,[0,3])]),([(1,1,0),(0,4,3),(1,4,3),(0,8,6)],[0,1,9,6,2,7,5],[(0,[0,1,2,3]),(1,[0,1,2,3]),(3,[]),(5,[0,3])]),([(1,1,0),(0,4,3),(1,4,3),(0,5,6)],[0,1,9,2,7,8],[(3,[0,3]),(5,[0,3])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q167 : ck165 [4,12,14,16,17,18,19] d167 = true := by decide +kernel
private def lv_0_0_6_11 : List NodeSpec := (d165 ++ (d166 ++ d167))

private theorem ok_0_0_6_11 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6_11 := by
  have go {ids ds} (h : ck165 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 6 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_5) h
  exact (levelOK_append (go q165) (levelOK_append (go q166) (go q167)))
private def ck168 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_5) 6
private def d168 : List NodeSpec := [([(1,1,0),(0,4,3),(1,4,3),(0,5,6)],[0,1,9,6,2,7,8],[(0,[1,2]),(1,[0,1,2,3]),(3,[0,3]),(5,[0,3]),(9,[1,2])]),([(1,1,0),(1,4,3),(0,7,6),(0,5,6)],[0,1,8,9,2,3,4],[(5,[0,3]),(7,[0,3])]),([(1,1,0),(2,4,3),(2,6,7),(0,5,6)],[0,1,8,9,2,3,4],[(3,[0,3]),(7,[0,3])]),([(1,1,0),(3,4,3),(2,6,7),(0,5,6)],[0,1,8,9,2,3,4],[(5,[0,3]),(6,[0,3])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q168 : ck168 [17,19] d168 = true := by decide +kernel
private def d169 : List NodeSpec := [([(2,1,0),(1,0,6),(0,4,3),(3,8,7)],[9,0,1,2,3,4,5],[(3,[]),(6,[])]),([(2,1,0),(1,0,6),(0,4,3),(1,4,3)],[0,1,7,2,8,9,5],[(0,[2,3]),(1,[2,3]),(2,[2,3]),(3,[]),(4,[2,3]),(5,[])]),([(2,1,0),(1,0,6),(1,4,3),(0,8,7)],[0,1,9,2,3,4,5],[(5,[]),(7,[])]),([(2,1,0),(2,1,6),(0,4,3),(1,8,7)],[0,1,2,3,9,4,5],[(3,[]),(6,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q169 : ck168 [20,21,22] d169 = true := by decide +kernel
private def d170 : List NodeSpec := [([(2,1,0),(2,1,6),(0,4,3),(1,4,3)],[7,0,1,2,8,9,5],[(0,[2,3]),(1,[2,3]),(2,[2,3]),(3,[]),(4,[2,3]),(5,[])]),([(2,1,0),(2,1,6),(1,4,3),(2,8,7)],[9,0,1,2,3,4,5],[(5,[]),(7,[])]),([(2,1,0),(3,1,0),(0,4,3),(1,4,3)],[7,6,1,2,8,9,5],[]),([(2,1,0),(3,1,0),(0,4,3),(1,4,3)],[7,6,0,2,8,9,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q170 : ck168 [1,2,22,23] d170 = true := by decide +kernel
private def lv_0_0_6_12 : List NodeSpec := (d168 ++ (d169 ++ d170))

private theorem ok_0_0_6_12 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6_12 := by
  have go {ids ds} (h : ck168 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 6 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_5) h
  exact (levelOK_append (go q168) (levelOK_append (go q169) (go q170)))
private def ck171 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_5) 6
private def d171 : List NodeSpec := [([(0,3,0),(1,3,0),(2,7,6),(0,4,8)],[9,8,0,1,2,4,5],[]),([(0,3,0),(1,3,0),(2,7,6),(1,4,8)],[8,0,1,2,4,9,5],[(1,[0,1,2])]),([(0,3,0),(1,3,0),(2,7,6),(2,4,8)],[8,9,0,1,2,4,5],[(0,[0,1,2])]),([(0,3,0),(1,3,0),(2,7,6),(3,4,8)],[9,8,0,1,2,4,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q171 : ck171 [24,25,26] d171 = true := by decide +kernel
private def d172 : List NodeSpec := [([(0,3,0),(3,3,1),(1,6,7),(0,4,8)],[0,9,8,1,2,4,5],[(0,[0,1,2]),(7,[]),(11,[0])]),([(0,3,0),(3,3,1),(1,6,7),(1,4,8)],[0,8,1,2,4,9,5],[]),([(0,3,0),(3,3,1),(1,6,7),(2,4,8)],[9,0,8,1,2,4,5],[]),([(0,3,0),(3,3,1),(1,6,7),(3,4,8)],[9,0,8,1,2,4,5],[(1,[0,1,2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q172 : ck171 [27,28,29] d172 = true := by decide +kernel
private def d173 : List NodeSpec := [([(1,3,0),(2,3,1),(2,6,7),(0,4,8)],[0,9,8,1,2,4,5],[]),([(1,3,0),(2,3,1),(2,6,7),(1,4,8)],[0,8,1,2,4,9,5],[(1,[0,1,2]),(6,[]),(10,[0])]),([(1,3,0),(2,3,1),(2,6,7),(2,4,8)],[9,0,8,1,2,4,5],[(0,[0,1,2])]),([(1,3,0),(2,3,1),(2,6,7),(3,4,8)],[9,0,8,1,2,4,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q173 : ck171 [30,31,32] d173 = true := by decide +kernel
private def lv_0_0_6_13 : List NodeSpec := (d171 ++ (d172 ++ d173))

private theorem ok_0_0_6_13 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6_13 := by
  have go {ids ds} (h : ck171 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 6 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_5) h
  exact (levelOK_append (go q171) (levelOK_append (go q172) (go q173)))
private def ck174 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_5) 6
private def d174 : List NodeSpec := [([(0,3,1),(1,3,1),(2,7,6),(0,4,8)],[9,8,0,1,2,4,5],[(0,[0,1,2])]),([(0,3,1),(1,3,1),(2,7,6),(1,4,8)],[8,0,1,2,4,9,5],[]),([(0,3,1),(1,3,1),(2,7,6),(2,4,8)],[8,0,9,1,2,4,5],[]),([(0,3,1),(1,3,1),(2,7,6),(3,4,8)],[9,8,0,1,2,4,5],[(1,[0,1,2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q174 : ck174 [33,34,35] d174 = true := by decide +kernel
private def d175 : List NodeSpec := [([(0,4,0),(1,4,0),(2,7,6),(0,3,8)],[9,8,0,1,2,3,5],[]),([(0,4,0),(1,4,0),(2,7,6),(1,3,8)],[8,0,1,2,3,9,5],[(1,[0,1,2])]),([(0,4,0),(1,4,0),(2,7,6),(2,3,8)],[8,9,0,1,2,3,5],[(0,[0,1,2])]),([(0,4,0),(1,4,0),(2,7,6),(3,3,8)],[9,8,0,1,2,3,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q175 : ck174 [36,37,38] d175 = true := by decide +kernel
private def d176 : List NodeSpec := [([(0,4,0),(3,4,1),(1,6,7),(0,3,8)],[9,0,8,1,2,3,5],[(0,[0,1,2]),(5,[]),(11,[0])]),([(0,4,0),(3,4,1),(1,6,7),(1,3,8)],[0,8,1,2,3,9,5],[]),([(0,4,0),(3,4,1),(1,6,7),(2,3,8)],[9,0,8,1,2,3,5],[]),([(0,4,0),(3,4,1),(1,6,7),(3,3,8)],[9,0,8,1,2,3,5],[(1,[0,1,2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q176 : ck174 [39,40,41] d176 = true := by decide +kernel
private def lv_0_0_6_14 : List NodeSpec := (d174 ++ (d175 ++ d176))

private theorem ok_0_0_6_14 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6_14 := by
  have go {ids ds} (h : ck174 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 6 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_5) h
  exact (levelOK_append (go q174) (levelOK_append (go q175) (go q176)))
private def ck177 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_5) 6
private def d177 : List NodeSpec := [([(1,4,0),(2,4,1),(2,6,7),(0,3,8)],[0,9,8,1,2,3,5],[]),([(1,4,0),(2,4,1),(2,6,7),(1,3,8)],[0,8,1,2,3,9,5],[(1,[0,1,2]),(3,[]),(10,[0])]),([(1,4,0),(2,4,1),(2,6,7),(2,3,8)],[9,0,8,1,2,3,5],[(0,[0,1,2])]),([(1,4,0),(2,4,1),(2,6,7),(3,3,8)],[9,0,8,1,2,3,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q177 : ck177 [42,43,44] d177 = true := by decide +kernel
private def d178 : List NodeSpec := [([(0,4,1),(1,4,1),(2,7,6),(0,3,8)],[9,8,0,1,2,3,5],[(0,[0,1,2])]),([(0,4,1),(1,4,1),(2,7,6),(1,3,8)],[8,0,1,2,3,9,5],[]),([(0,4,1),(1,4,1),(2,7,6),(2,3,8)],[8,0,9,1,2,3,5],[]),([(0,4,1),(1,4,1),(2,7,6),(3,3,8)],[9,8,0,1,2,3,5],[(1,[0,1,2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q178 : ck177 [45,46,47] d178 = true := by decide +kernel
private def lv_0_0_6_15 : List NodeSpec := (d177 ++ d178)

private theorem ok_0_0_6_15 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6_15 := by
  have go {ids ds} (h : ck177 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 6 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_5) h
  exact (levelOK_append (go q177) (go q178))
private def lv_0_0_6 : List NodeSpec := ((((lv_0_0_6_0 ++ lv_0_0_6_1) ++ (lv_0_0_6_2 ++ lv_0_0_6_3)) ++ ((lv_0_0_6_4 ++ lv_0_0_6_5) ++ (lv_0_0_6_6 ++ lv_0_0_6_7))) ++ (((lv_0_0_6_8 ++ lv_0_0_6_9) ++ (lv_0_0_6_10 ++ lv_0_0_6_11)) ++ ((lv_0_0_6_12 ++ lv_0_0_6_13) ++ (lv_0_0_6_14 ++ lv_0_0_6_15))))
private theorem ok_0_0_6 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6 := (levelOK_append (levelOK_append (levelOK_append (levelOK_append ok_0_0_6_0 ok_0_0_6_1) (levelOK_append ok_0_0_6_2 ok_0_0_6_3)) (levelOK_append (levelOK_append ok_0_0_6_4 ok_0_0_6_5) (levelOK_append ok_0_0_6_6 ok_0_0_6_7))) (levelOK_append (levelOK_append (levelOK_append ok_0_0_6_8 ok_0_0_6_9) (levelOK_append ok_0_0_6_10 ok_0_0_6_11)) (levelOK_append (levelOK_append ok_0_0_6_12 ok_0_0_6_13) (levelOK_append ok_0_0_6_14 ok_0_0_6_15))))
private def ck179 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d179 : List NodeSpec := [([(0,1,0),(2,0,6),(0,4,3)],[7,0,1,2,8,3,4,5],[(5,[]),(10,[]),(15,[])]),([(0,1,0),(2,0,6),(1,4,3)],[7,0,1,2,3,4,8,5],[(3,[]),(10,[]),(11,[]),(15,[])]),([(0,1,0),(2,0,6),(2,4,3)],[8,7,0,1,2,3,4,5],[(5,[]),(10,[]),(15,[])]),([(0,1,0),(2,0,6),(3,4,3)],[8,7,0,1,2,3,4,5],[(3,[]),(10,[]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q179 : ck179 [0] d179 = true := by decide +kernel
private def d180 : List NodeSpec := [([(0,1,0),(2,0,6),(0,4,3)],[7,6,1,2,8,3,4,5],[(0,[2])]),([(0,1,0),(2,0,6),(1,4,3)],[7,6,1,2,3,4,8,5],[(0,[2]),(10,[]),(11,[])]),([(0,1,0),(2,0,6),(2,4,3)],[8,7,6,1,2,3,4,5],[(0,[2])]),([(0,1,0),(2,0,6),(3,4,3)],[8,7,6,1,2,3,4,5],[(0,[2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q180 : ck179 [1] d180 = true := by decide +kernel
private def d181 : List NodeSpec := [([(0,1,0),(2,1,6),(0,4,3)],[7,0,1,2,8,3,4,5],[(5,[]),(8,[]),(10,[]),(11,[]),(16,[])]),([(0,1,0),(2,1,6),(1,4,3)],[7,0,1,2,3,4,8,5],[(3,[]),(8,[]),(16,[])]),([(0,1,0),(2,1,6),(2,4,3)],[8,7,0,1,2,3,4,5],[(5,[]),(8,[]),(16,[])]),([(0,1,0),(2,1,6),(3,4,3)],[8,7,0,1,2,3,4,5],[(3,[]),(8,[]),(16,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q181 : ck179 [2] d181 = true := by decide +kernel
private def lv_0_0_7_0 : List NodeSpec := (d179 ++ (d180 ++ d181))

private theorem ok_0_0_7_0 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_0 := by
  have go {ids ds} (h : ck179 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q179) (levelOK_append (go q180) (go q181)))
private def ck182 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d182 : List NodeSpec := [([(0,1,0),(2,1,6),(0,4,3)],[7,6,0,2,8,3,4,5],[(0,[2]),(11,[])]),([(0,1,0),(2,1,6),(1,4,3)],[7,6,0,2,3,4,8,5],[(0,[2]),(8,[]),(16,[])]),([(0,1,0),(2,1,6),(2,4,3)],[8,7,6,0,2,3,4,5],[(0,[2])]),([(0,1,0),(2,1,6),(3,4,3)],[8,7,6,0,2,3,4,5],[(0,[2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q182 : ck182 [3,4] d182 = true := by decide +kernel
private def d183 : List NodeSpec := [([(0,1,0),(1,1,0),(2,7,6)],[8,1,2,3,4,5],[(0,[0,1,2]),(1,[0,1,2]),(8,[]),(10,[]),(15,[])]),([(0,1,0),(1,1,0),(0,4,3)],[6,1,7,2,8,3,4,5],[]),([(0,1,0),(1,1,0),(1,4,3)],[6,1,7,2,3,4,8,5],[(10,[]),(11,[])]),([(0,1,0),(1,1,0),(2,4,3)],[8,6,1,7,2,3,4,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q183 : ck182 [5,6,7,8,9] d183 = true := by decide +kernel
private def d184 : List NodeSpec := [([(0,1,0),(1,1,0),(3,4,3)],[8,6,1,7,2,3,4,5],[]),([(0,1,0),(1,1,0),(2,7,6)],[8,0,2,3,4,5],[(0,[0,1,2]),(1,[0,1,2]),(8,[]),(15,[])]),([(0,1,0),(1,1,0),(0,4,3)],[6,0,7,2,8,3,4,5],[(11,[])]),([(0,1,0),(1,1,0),(1,4,3)],[6,0,7,2,3,4,8,5],[(8,[]),(12,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q184 : ck182 [8,10,11,12,13,14,15,16] d184 = true := by decide +kernel
private def lv_0_0_7_1 : List NodeSpec := (d182 ++ (d183 ++ d184))

private theorem ok_0_0_7_1 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_1 := by
  have go {ids ds} (h : ck182 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q182) (levelOK_append (go q183) (go q184)))
private def ck185 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d185 : List NodeSpec := [([(0,1,0),(1,1,0),(2,4,3)],[8,6,0,7,2,3,4,5],[]),([(0,1,0),(1,1,0),(3,4,3)],[8,6,0,7,2,3,4,5],[]),([(0,1,0),(1,2,6),(0,4,3)],[0,1,7,8,3,4,5],[(0,[0,1]),(0,[0,1,2]),(3,[0,1]),(4,[]),(4,[2]),(5,[0,1]),(6,[0,1]),(8,[1]),(10,[1]),(11,[]),(12,[])]),([(0,1,0),(1,2,6),(1,4,3)],[0,1,7,3,4,8,5],[(0,[0,1]),(0,[0,1,2]),(3,[0,1]),(4,[]),(4,[2]),(5,[0,1]),(6,[0,1]),(8,[1]),(10,[1]),(11,[]),(12,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q185 : ck185 [12,13,17] d185 = true := by decide +kernel
private def d186 : List NodeSpec := [([(0,1,0),(1,2,6),(2,4,3)],[8,0,1,7,3,4,5],[(0,[0,1]),(0,[0,1,2]),(3,[0,1]),(4,[]),(4,[2]),(5,[0,1]),(6,[0,1]),(8,[1]),(10,[1]),(11,[]),(12,[])]),([(0,1,0),(1,2,6),(3,4,3)],[8,0,1,7,3,4,5],[(0,[0,1]),(0,[0,1,2]),(3,[0,1]),(4,[]),(4,[2]),(5,[0,1]),(6,[0,1]),(8,[1]),(10,[1]),(11,[]),(12,[])]),([(0,1,0),(1,2,6),(1,3,6)],[0,1,7,8,4,5],[(0,[0,1,2]),(1,[0,2]),(4,[0,2]),(6,[0,1]),(11,[]),(12,[]),(18,[])]),([(0,1,0),(1,2,6),(1,3,6)],[0,1,7,3,8,4,5],[(0,[0,1]),(0,[0,1,2]),(1,[0]),(1,[0,2]),(3,[0,1]),(4,[]),(4,[0,2]),(5,[0,1]),(6,[0,1]),(7,[0,1]),(11,[]),(12,[]),(18,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q186 : ck185 [18,19,20,21] d186 = true := by decide +kernel
private def d187 : List NodeSpec := [([(0,1,0),(1,2,6),(2,3,6)],[8,0,1,7,4,5],[(0,[0,1,2]),(1,[0,2]),(4,[0,2]),(7,[0,1]),(11,[]),(12,[]),(18,[])]),([(0,1,0),(1,2,6),(2,3,6)],[8,0,1,7,3,4,5],[(0,[0,1]),(0,[0,1,2]),(1,[0]),(1,[0,2]),(3,[0,1]),(4,[]),(4,[0,2]),(5,[0,1]),(6,[0,1]),(7,[0,1]),(11,[]),(12,[]),(18,[])]),([(0,1,0),(1,2,6),(1,4,6)],[0,1,7,3,8,5],[(0,[0,1,2]),(1,[0,2]),(3,[0,1]),(4,[0,2]),(11,[]),(12,[]),(18,[])]),([(0,1,0),(1,2,6),(1,4,6)],[0,1,7,3,4,8,5],[(0,[0,1]),(0,[0,1,2]),(1,[0]),(1,[0,2]),(3,[0,1]),(4,[]),(4,[0,2]),(5,[0,1]),(6,[0,1]),(7,[0,1]),(11,[]),(12,[]),(18,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q187 : ck185 [22,23,24,25,26,27,28,29] d187 = true := by decide +kernel
private def lv_0_0_7_2 : List NodeSpec := (d185 ++ (d186 ++ d187))

private theorem ok_0_0_7_2 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_2 := by
  have go {ids ds} (h : ck185 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q185) (levelOK_append (go q186) (go q187)))
private def ck188 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d188 : List NodeSpec := [([(0,1,0),(1,2,6),(2,4,6)],[8,0,1,7,3,5],[(0,[0,1,2]),(1,[0,2]),(4,[0,2]),(5,[0,1]),(11,[]),(12,[]),(18,[])]),([(0,1,0),(1,2,6),(2,4,6)],[8,0,1,7,3,4,5],[(0,[0,1]),(0,[0,1,2]),(1,[0]),(1,[0,2]),(3,[0,1]),(4,[0,2]),(5,[0,1]),(6,[0,1]),(7,[0,1]),(11,[]),(12,[]),(18,[])]),([(0,1,0),(1,2,6),(0,4,3)],[6,0,1,7,8,3,4,5],[(0,[0,1,2]),(1,[2]),(5,[0,1]),(7,[0,1]),(9,[2]),(11,[])]),([(0,1,0),(1,2,6),(1,4,3)],[6,0,1,7,3,4,8,5],[(0,[0,1,2]),(1,[2]),(3,[0,1]),(6,[0,1]),(9,[2]),(11,[]),(16,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q188 : ck188 [20,24,28,30,31,32,33,34,35,36] d188 = true := by decide +kernel
private def d189 : List NodeSpec := [([(0,1,0),(1,2,6),(2,4,3)],[8,6,0,1,7,3,4,5],[(0,[0,1,2]),(1,[2]),(5,[0,1]),(6,[0,1]),(9,[2]),(11,[])]),([(0,1,0),(1,2,6),(3,4,3)],[8,6,0,1,7,3,4,5],[(0,[0,1,2]),(1,[2]),(3,[0,1]),(7,[0,1]),(9,[2]),(11,[])]),([(0,1,0),(1,3,6),(2,7,6)],[8,0,1,2,7,4,5],[(0,[0,1]),(0,[0,1,2]),(1,[0,1]),(1,[0,1,2]),(3,[0,1]),(5,[0,1]),(6,[]),(6,[0]),(7,[]),(7,[0]),(11,[]),(12,[]),(19,[])]),([(0,1,0),(1,3,6),(1,4,6)],[0,1,2,7,8,5],[(0,[0,1,2]),(1,[0,1,2]),(3,[0,1]),(6,[0,2]),(11,[]),(12,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q189 : ck188 [21,25,29,33,37,38,39,40] d189 = true := by decide +kernel
private def d190 : List NodeSpec := [([(0,1,0),(1,3,6),(1,4,6)],[0,1,2,7,4,8,5],[(0,[0,1]),(0,[0,1,2]),(1,[0,1]),(1,[0,1,2]),(3,[0,1]),(5,[0,1]),(6,[0,2]),(11,[]),(12,[])]),([(0,1,0),(1,3,6),(2,4,6)],[8,0,1,2,7,5],[(0,[0,1,2]),(1,[0,1,2]),(5,[0,1]),(6,[0,2]),(11,[]),(12,[]),(20,[])]),([(0,1,0),(1,3,6),(2,4,6)],[8,0,1,2,7,4,5],[(0,[0,1]),(0,[0,1,2]),(1,[0,1]),(1,[0,1,2]),(3,[0,1]),(5,[0,1]),(6,[0,2]),(11,[]),(12,[]),(20,[])]),([(0,1,0),(1,3,6),(0,4,7)],[6,0,1,2,8,7,4,5],[(0,[0,1,2]),(1,[0,1,2]),(3,[0,1]),(5,[0,1]),(6,[0])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q190 : ck188 [18,39,41,42,43] d190 = true := by decide +kernel
private def lv_0_0_7_3 : List NodeSpec := (d188 ++ (d189 ++ d190))

private theorem ok_0_0_7_3 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_3 := by
  have go {ids ds} (h : ck188 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q188) (levelOK_append (go q189) (go q190)))
private def ck191 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d191 : List NodeSpec := [([(0,1,0),(1,3,6),(3,4,7)],[8,6,0,1,2,7,4,5],[(0,[0,1,2]),(1,[0,1,2]),(3,[0,1]),(5,[0,1]),(19,[]),(20,[])]),([(0,1,0),(1,3,6),(2,5,6)],[8,0,1,2,7,4],[(0,[0,1]),(1,[0,1,2]),(2,[0,1]),(6,[0,2]),(11,[]),(12,[]),(17,[])]),([(0,1,0),(1,3,6),(1,4,6)],[0,1,2,3,7,8,5],[(0,[0,2]),(0,[0,1,2]),(1,[0,2]),(1,[0,1,2]),(3,[]),(3,[0,1]),(5,[0]),(6,[0,2]),(7,[0,2]),(11,[]),(12,[])]),([(0,1,0),(1,3,6),(1,4,6)],[0,1,2,3,7,4,8,5],[(3,[]),(3,[0,1]),(5,[]),(5,[0]),(6,[]),(6,[0,2]),(7,[0])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q191 : ck191 [19,43,44,45,46,47] d191 = true := by decide +kernel
private def d192 : List NodeSpec := [([(0,1,0),(1,3,6),(2,4,6)],[8,0,1,2,3,7,5],[(0,[0,2]),(0,[0,1,2]),(1,[0,2]),(1,[0,1,2]),(3,[0]),(5,[]),(5,[0,1]),(6,[0,2]),(7,[0,2]),(11,[]),(12,[]),(20,[])]),([(0,1,0),(1,3,6),(0,4,3)],[6,0,1,2,8,7,4,5],[(0,[0,1,2]),(1,[0,1,2]),(3,[0]),(5,[0,1]),(7,[]),(11,[])]),([(0,1,0),(1,3,6),(3,4,3)],[8,6,0,1,2,7,4,5],[(0,[0,1,2]),(1,[0,1,2]),(3,[0,1]),(7,[]),(11,[]),(20,[])]),([(0,1,0),(1,3,6),(2,5,6)],[8,0,1,2,3,7,4],[(0,[0]),(0,[0,1]),(1,[0,2]),(1,[0,1,2]),(2,[]),(2,[0,1]),(3,[0,2]),(5,[0,2]),(6,[0,2]),(7,[0,2]),(11,[]),(12,[]),(17,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q192 : ck191 [20,21,42,47,48,49] d192 = true := by decide +kernel
private def d193 : List NodeSpec := [([(0,1,0),(2,3,6),(1,4,7)],[7,6,0,1,2,4,8,5],[(0,[0,1,2]),(1,[0,1,2]),(3,[0,1]),(5,[0,1]),(7,[0]),(11,[]),(16,[])]),([(0,1,0),(2,3,6),(2,4,7)],[7,6,8,0,1,2,4,5],[(0,[0,1,2]),(1,[0,1,2]),(3,[0,1]),(5,[0,1]),(19,[]),(20,[])]),([(0,1,0),(2,3,6),(1,4,6)],[7,0,1,2,8,5],[(0,[0,1,2]),(1,[0,1,2]),(3,[0,1]),(7,[0,2]),(11,[]),(12,[]),(19,[])]),([(0,1,0),(2,3,6),(1,4,6)],[7,0,1,2,4,8,5],[(0,[0,1]),(0,[0,1,2]),(1,[0,1]),(1,[0,1,2]),(3,[0,1]),(5,[0,1]),(7,[0,2]),(11,[]),(12,[]),(19,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q193 : ck191 [22,23,50,51,52,53,54] d193 = true := by decide +kernel
private def lv_0_0_7_4 : List NodeSpec := (d191 ++ (d192 ++ d193))

private theorem ok_0_0_7_4 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_4 := by
  have go {ids ds} (h : ck191 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q191) (levelOK_append (go q192) (go q193)))
private def ck194 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d194 : List NodeSpec := [([(0,1,0),(2,3,6),(2,4,6)],[7,8,0,1,2,5],[(0,[0,1,2]),(1,[0,1,2]),(5,[0,1]),(7,[0,2]),(11,[]),(12,[])]),([(0,1,0),(2,3,6),(2,4,6)],[7,8,0,1,2,4,5],[(0,[0,1]),(0,[0,1,2]),(1,[0,1]),(1,[0,1,2]),(3,[0,1]),(5,[0,1]),(7,[0,2]),(11,[]),(12,[])]),([(0,1,0),(2,3,6),(2,5,6)],[7,8,0,1,2,4],[(0,[0,1]),(1,[0,1,2]),(2,[0,1]),(7,[0,2]),(11,[]),(12,[]),(17,[])]),([(0,1,0),(2,3,6),(1,4,6)],[7,0,1,2,3,8,5],[(0,[0,2]),(0,[0,1,2]),(1,[0,2]),(1,[0,1,2]),(3,[]),(3,[0,1]),(5,[0]),(6,[0,2]),(7,[0,2]),(11,[]),(12,[]),(19,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q194 : ck194 [51,52,53,54,55] d194 = true := by decide +kernel
private def d195 : List NodeSpec := [([(0,1,0),(2,3,6),(2,4,6)],[7,8,0,1,2,3,5],[(0,[0,2]),(0,[0,1,2]),(1,[0,2]),(1,[0,1,2]),(3,[0]),(5,[]),(5,[0,1]),(6,[0,2]),(7,[0,2]),(11,[]),(12,[])]),([(0,1,0),(2,3,6),(2,4,6)],[7,8,0,1,2,3,4,5],[(3,[]),(3,[0]),(5,[]),(5,[0,1]),(6,[0]),(7,[]),(7,[0,2])]),([(0,1,0),(2,3,6),(1,4,3)],[7,6,0,1,2,4,8,5],[(0,[0,1,2]),(1,[0,1,2]),(3,[0,1]),(5,[0]),(6,[]),(11,[]),(16,[])]),([(0,1,0),(2,3,6),(2,4,3)],[8,7,6,0,1,2,4,5],[(0,[0,1,2]),(1,[0,1,2]),(5,[0,1]),(6,[]),(11,[]),(19,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q195 : ck194 [24,25,52,56,57,58,59,60] d195 = true := by decide +kernel
private def d196 : List NodeSpec := [([(0,1,0),(2,3,6),(2,5,6)],[7,8,0,1,2,3,4],[(0,[0]),(0,[0,1]),(1,[0,2]),(1,[0,1,2]),(2,[]),(2,[0,1]),(3,[0,2]),(5,[0,2]),(6,[0,2]),(7,[0,2]),(11,[]),(12,[]),(17,[])]),([(0,1,0),(1,4,6),(2,7,6)],[8,0,1,2,3,7,5],[(0,[0,1]),(0,[0,1,2]),(1,[0,1]),(1,[0,1,2]),(3,[]),(3,[0]),(5,[]),(5,[0]),(6,[0,1]),(7,[0,1]),(11,[]),(12,[]),(20,[])]),([(0,1,0),(1,4,6),(0,7,3)],[6,0,1,2,8,3,7,5],[(0,[0,1,2]),(1,[0,1,2]),(3,[0]),(5,[0]),(6,[0,1]),(7,[0,1])]),([(0,1,0),(1,4,6),(2,7,3)],[8,6,0,1,2,3,7,5],[(0,[0,1,2]),(1,[0,1,2]),(5,[0]),(6,[0,1]),(7,[0,1]),(19,[]),(20,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q196 : ck194 [26,27,45,46,59,60,61,62,63] d196 = true := by decide +kernel
private def lv_0_0_7_5 : List NodeSpec := (d194 ++ (d195 ++ d196))

private theorem ok_0_0_7_5 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_5 := by
  have go {ids ds} (h : ck194 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q194) (levelOK_append (go q195) (go q196)))
private def ck197 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d197 : List NodeSpec := [([(0,1,0),(1,4,6),(2,5,6)],[8,0,1,2,3,7],[(0,[0,1]),(1,[0,1,2]),(2,[0,1]),(3,[0,2]),(11,[]),(12,[]),(17,[])]),([(0,1,0),(1,4,6),(0,4,3)],[6,0,1,2,8,3,7,5],[(0,[0,1,2]),(1,[0,1,2]),(3,[0]),(5,[]),(5,[0]),(7,[0,1]),(11,[])]),([(0,1,0),(1,4,6),(2,4,3)],[8,6,0,1,2,3,7,5],[(0,[0,1,2]),(1,[0,1,2]),(5,[]),(5,[0]),(6,[0,1]),(11,[]),(19,[])]),([(0,1,0),(1,4,6),(2,5,6)],[8,0,1,2,3,4,7],[(0,[0]),(0,[0,1]),(1,[0,2]),(1,[0,1,2]),(2,[]),(2,[0,1]),(3,[0,2]),(5,[0,2]),(6,[0,2]),(7,[0,2]),(11,[]),(12,[]),(17,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q197 : ck197 [28,29,46,47,62,63,64,65] d197 = true := by decide +kernel
private def d198 : List NodeSpec := [([(0,1,0),(2,4,6),(1,3,7)],[7,6,0,1,2,3,8,5],[(0,[0,1,2]),(1,[0,1,2]),(3,[0]),(5,[0]),(6,[0,1]),(7,[0,1]),(11,[]),(16,[])]),([(0,1,0),(2,4,6),(2,3,7)],[7,8,6,0,1,2,3,5],[(0,[0,1,2]),(1,[0,1,2]),(3,[0]),(6,[0,1]),(7,[0,1]),(19,[]),(20,[])]),([(0,1,0),(2,4,6),(2,5,6)],[7,8,0,1,2,3],[(0,[0,1]),(1,[0,1,2]),(2,[0,1]),(5,[0,2]),(11,[]),(12,[]),(17,[])]),([(0,1,0),(2,4,6),(1,4,3)],[7,6,0,1,2,3,8,5],[(0,[0,1,2]),(1,[0,1,2]),(3,[]),(3,[0]),(5,[0]),(6,[0,1]),(11,[]),(16,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q198 : ck197 [30,31,32,56,57,58,66,67,68,69] d198 = true := by decide +kernel
private def d199 : List NodeSpec := [([(0,1,0),(2,4,6),(3,4,3)],[8,7,6,0,1,2,3,5],[(0,[0,1,2]),(1,[0,1,2]),(3,[]),(3,[0]),(7,[0,1]),(11,[]),(20,[])]),([(0,1,0),(2,4,6),(2,5,6)],[7,8,0,1,2,3,4],[(0,[0]),(0,[0,1]),(1,[0,2]),(1,[0,1,2]),(2,[]),(2,[0,1]),(3,[0,2]),(5,[0,2]),(6,[0,2]),(7,[0,2]),(11,[]),(12,[]),(17,[])]),([(0,1,0),(0,4,3),(1,7,6)],[0,1,2,3,8,4,5],[(0,[]),(0,[0,1,2]),(1,[]),(1,[0,1,2]),(3,[]),(3,[0,2]),(5,[]),(5,[0]),(6,[]),(6,[0,2]),(8,[]),(10,[])]),([(0,1,0),(0,4,3),(1,7,6)],[6,0,1,2,3,8,4,5],[(0,[0,1,2]),(1,[0,1,2]),(3,[0]),(5,[]),(5,[0]),(6,[0]),(7,[0])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q199 : ck197 [3,14,33,34,42,46,69,70,71,72,73] d199 = true := by decide +kernel
private def lv_0_0_7_6 : List NodeSpec := (d197 ++ (d198 ++ d199))

private theorem ok_0_0_7_6 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_6 := by
  have go {ids ds} (h : ck197 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q197) (levelOK_append (go q198) (go q199)))
private def ck200 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d200 : List NodeSpec := [([(0,1,0),(0,4,3),(1,4,3)],[6,0,1,2,7,8,5],[(0,[1,2]),(0,[0,1,2]),(1,[1,2]),(1,[0,1,2]),(3,[]),(3,[0]),(5,[]),(5,[0])]),([(0,1,0),(0,4,3),(2,5,6)],[8,0,1,2,7,3,4],[(1,[0,2]),(1,[0,1,2]),(2,[]),(2,[1]),(3,[0,2]),(5,[0,2]),(6,[0,2]),(8,[2]),(10,[2]),(11,[]),(12,[])]),([(0,1,0),(0,4,3),(2,5,6)],[8,6,0,1,2,7,3,4],[(0,[1]),(1,[0,1,2]),(5,[0,2]),(7,[0,2]),(9,[1]),(11,[])]),([(0,1,0),(1,4,3),(2,7,6)],[8,0,1,2,3,4,5],[(0,[]),(0,[0,1,2]),(1,[]),(1,[0,1,2]),(3,[]),(3,[0]),(5,[]),(5,[0,2]),(6,[0]),(7,[]),(8,[]),(10,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q200 : ck200 [0,1,2,4,9,15,17,35,48,52,56,64,71,72,73,74,75,76,77] d200 = true := by decide +kernel
private def d201 : List NodeSpec := [([(0,1,0),(1,4,3),(2,7,6)],[8,6,0,1,2,3,4,5],[(0,[0,1,2]),(1,[0,1,2]),(3,[]),(3,[0]),(5,[0]),(6,[0]),(7,[0]),(8,[])]),([(0,1,0),(1,4,3),(2,5,6)],[8,0,1,2,3,4,7],[(1,[0,2]),(1,[0,1,2]),(2,[]),(2,[1]),(3,[0,2]),(5,[0,2]),(6,[0,2]),(8,[2]),(10,[2]),(11,[]),(12,[])]),([(0,1,0),(1,4,3),(2,5,6)],[8,6,0,1,2,3,4,7],[(0,[1]),(1,[0,1,2]),(3,[0,2]),(6,[0,2]),(9,[1]),(11,[]),(16,[])]),([(0,1,0),(2,4,3),(1,6,7)],[8,0,1,2,3,4,5],[(0,[]),(0,[0,1,2]),(1,[]),(1,[0,1,2]),(3,[]),(3,[0,2]),(5,[]),(5,[0]),(6,[0]),(7,[]),(8,[]),(10,[]),(19,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q201 : ck200 [36,52,56,59,69,75,76,77,78] d201 = true := by decide +kernel
private def d202 : List NodeSpec := [([(0,1,0),(2,4,3),(1,6,7)],[6,8,0,1,2,3,4,5],[(0,[0,1,2]),(1,[0,1,2]),(3,[0]),(5,[]),(5,[0]),(6,[0]),(7,[0]),(19,[])]),([(0,1,0),(2,4,3),(2,5,6)],[7,8,0,1,2,3,4],[(1,[0,2]),(1,[0,1,2]),(2,[]),(2,[1]),(3,[0,2]),(5,[0,2]),(6,[0,2]),(8,[2]),(10,[2]),(11,[]),(12,[])]),([(0,1,0),(2,4,3),(2,5,6)],[7,8,6,0,1,2,3,4],[(0,[1]),(1,[0,1,2]),(5,[0,2]),(6,[0,2]),(9,[1]),(11,[])]),([(0,1,0),(3,4,3),(1,6,7)],[8,0,1,2,3,4,5],[(0,[]),(0,[0,1,2]),(1,[]),(1,[0,1,2]),(3,[]),(3,[0]),(5,[]),(5,[0,2]),(6,[]),(6,[0,2]),(8,[]),(10,[]),(20,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q202 : ck200 [37,60,65,79] d202 = true := by decide +kernel
private def lv_0_0_7_7 : List NodeSpec := (d200 ++ (d201 ++ d202))

private theorem ok_0_0_7_7 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_7 := by
  have go {ids ds} (h : ck200 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q200) (levelOK_append (go q201) (go q202)))
private def ck203 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d203 : List NodeSpec := [([(0,1,0),(3,4,3),(1,6,7)],[6,8,0,1,2,3,4,5],[(0,[0,1,2]),(1,[0,1,2]),(3,[]),(3,[0]),(5,[0]),(6,[0]),(7,[0]),(20,[])]),([(0,1,0),(3,4,3),(2,5,6)],[7,8,0,1,2,3,4],[(1,[0,2]),(1,[0,1,2]),(2,[]),(2,[1]),(3,[0,2]),(5,[0,2]),(6,[0,2]),(8,[2]),(10,[2]),(11,[]),(12,[])]),([(0,1,0),(3,4,3),(2,5,6)],[7,8,6,0,1,2,3,4],[(0,[1]),(1,[0,1,2]),(3,[0,2]),(7,[0,2]),(9,[1]),(11,[])]),([(1,1,0),(2,1,0),(0,4,3)],[7,1,6,2,8,3,4,5],[(0,[2]),(10,[]),(11,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q203 : ck203 [38,49,70,80,81] d203 = true := by decide +kernel
private def d204 : List NodeSpec := [([(1,1,0),(2,1,0),(1,4,3)],[7,1,6,2,3,4,8,5],[(0,[2])]),([(1,1,0),(2,1,0),(2,4,3)],[8,7,1,6,2,3,4,5],[(0,[2])]),([(1,1,0),(2,1,0),(3,4,3)],[8,7,1,6,2,3,4,5],[(0,[2])]),([(1,1,0),(3,1,0),(0,4,3)],[7,0,6,2,8,3,4,5],[(0,[2]),(10,[]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q204 : ck203 [81,82] d204 = true := by decide +kernel
private def d205 : List NodeSpec := [([(1,1,0),(3,1,0),(1,4,3)],[7,0,6,2,3,4,8,5],[(0,[2]),(8,[])]),([(1,1,0),(3,1,0),(2,4,3)],[8,7,0,6,2,3,4,5],[(0,[2])]),([(1,1,0),(3,1,0),(3,4,3)],[8,7,0,6,2,3,4,5],[(0,[2])]),([(1,1,0),(3,2,6),(0,4,3)],[7,0,1,8,3,4,5],[(0,[0,1]),(0,[0,1,2]),(3,[0,1]),(4,[]),(4,[2]),(5,[0,1]),(6,[0,1]),(8,[]),(10,[]),(11,[1]),(12,[1])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q205 : ck203 [82,83,84] d205 = true := by decide +kernel
private def lv_0_0_7_8 : List NodeSpec := (d203 ++ (d204 ++ d205))

private theorem ok_0_0_7_8 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_8 := by
  have go {ids ds} (h : ck203 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q203) (levelOK_append (go q204) (go q205)))
private def ck206 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d206 : List NodeSpec := [([(1,1,0),(3,2,6),(1,4,3)],[7,0,1,3,4,8,5],[(0,[0,1]),(0,[0,1,2]),(3,[0,1]),(4,[]),(4,[2]),(5,[0,1]),(6,[0,1]),(8,[]),(10,[]),(11,[1]),(12,[1])]),([(1,1,0),(3,2,6),(2,4,3)],[8,7,0,1,3,4,5],[(0,[0,1]),(0,[0,1,2]),(3,[0,1]),(4,[]),(4,[2]),(5,[0,1]),(6,[0,1]),(8,[]),(10,[]),(11,[1]),(12,[1])]),([(1,1,0),(3,2,6),(3,4,3)],[8,7,0,1,3,4,5],[(0,[0,1]),(0,[0,1,2]),(3,[0,1]),(4,[]),(4,[2]),(5,[0,1]),(6,[0,1]),(8,[]),(10,[]),(11,[1]),(12,[1])]),([(1,1,0),(3,2,6),(0,3,6)],[7,0,1,8,4,5],[(0,[0,1,2]),(1,[0,2]),(4,[0,2]),(7,[0,1]),(8,[]),(10,[]),(13,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q206 : ck206 [84,85,86] d206 = true := by decide +kernel
private def d207 : List NodeSpec := [([(1,1,0),(3,2,6),(0,3,6)],[7,0,1,8,3,4,5],[(0,[0,1]),(0,[0,1,2]),(1,[0]),(1,[0,2]),(3,[0,1]),(4,[]),(4,[0,2]),(5,[0,1]),(6,[0,1]),(7,[0,1]),(8,[]),(10,[]),(13,[])]),([(1,1,0),(3,2,6),(3,3,6)],[8,7,0,1,4,5],[(0,[0,1,2]),(1,[0,2]),(4,[0,2]),(6,[0,1]),(8,[]),(10,[]),(13,[])]),([(1,1,0),(3,2,6),(3,3,6)],[8,7,0,1,3,4,5],[(0,[0,1]),(0,[0,1,2]),(1,[0]),(1,[0,2]),(3,[0,1]),(4,[]),(4,[0,2]),(5,[0,1]),(6,[0,1]),(7,[0,1]),(8,[]),(10,[]),(13,[])]),([(1,1,0),(3,2,6),(0,4,6)],[7,0,1,8,3,5],[(0,[0,1,2]),(1,[0,2]),(4,[0,2]),(5,[0,1]),(8,[]),(10,[]),(13,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q207 : ck206 [87,88,89,90,91,92,93,94] d207 = true := by decide +kernel
private def d208 : List NodeSpec := [([(1,1,0),(3,2,6),(0,4,6)],[7,0,1,8,3,4,5],[(0,[0,1]),(0,[0,1,2]),(1,[0]),(1,[0,2]),(3,[0,1]),(4,[0,2]),(5,[0,1]),(6,[0,1]),(7,[0,1]),(8,[]),(10,[]),(13,[])]),([(1,1,0),(3,2,6),(3,4,6)],[8,7,0,1,3,5],[(0,[0,1,2]),(1,[0,2]),(3,[0,1]),(4,[0,2]),(8,[]),(10,[]),(13,[])]),([(1,1,0),(3,2,6),(3,4,6)],[8,7,0,1,3,4,5],[(0,[0,1]),(0,[0,1,2]),(1,[0]),(1,[0,2]),(3,[0,1]),(4,[]),(4,[0,2]),(5,[0,1]),(6,[0,1]),(7,[0,1]),(8,[]),(10,[]),(13,[])]),([(1,1,0),(3,2,6),(0,4,3)],[7,0,1,6,8,3,4,5],[(0,[0,1,2]),(1,[2]),(5,[0,1]),(7,[0,1]),(8,[]),(9,[2]),(10,[]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q208 : ck206 [91,95,96,97,98,99,100,101,102] d208 = true := by decide +kernel
private def lv_0_0_7_9 : List NodeSpec := (d206 ++ (d207 ++ d208))

private theorem ok_0_0_7_9 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_9 := by
  have go {ids ds} (h : ck206 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q206) (levelOK_append (go q207) (go q208)))
private def ck209 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d209 : List NodeSpec := [([(1,1,0),(3,2,6),(1,4,3)],[7,0,1,6,3,4,8,5],[(0,[0,1,2]),(1,[2]),(3,[0,1]),(6,[0,1]),(8,[]),(9,[2])]),([(1,1,0),(3,2,6),(2,4,3)],[8,7,0,1,6,3,4,5],[(0,[0,1,2]),(1,[2]),(5,[0,1]),(6,[0,1]),(8,[]),(9,[2])]),([(1,1,0),(3,2,6),(3,4,3)],[8,7,0,1,6,3,4,5],[(0,[0,1,2]),(1,[2]),(3,[0,1]),(7,[0,1]),(8,[]),(9,[2])]),([(1,1,0),(0,3,6),(2,6,7)],[8,0,1,7,2,4,5],[(0,[0,1]),(0,[0,1,2]),(1,[0,1]),(1,[0,1,2]),(3,[0,1]),(5,[0,1]),(6,[]),(6,[0]),(7,[]),(7,[0]),(8,[]),(10,[]),(20,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q209 : ck209 [87,88,92,95,96,100,102,103,104,105,106] d209 = true := by decide +kernel
private def d210 : List NodeSpec := [([(1,1,0),(0,3,6),(1,4,7)],[0,1,7,6,2,4,8,5],[(0,[0,1,2]),(1,[0,1,2]),(3,[0,1]),(5,[0,1]),(7,[0])]),([(1,1,0),(0,3,6),(2,4,7)],[8,0,1,7,6,2,4,5],[(0,[0,1,2]),(1,[0,1,2]),(3,[0,1]),(5,[0,1]),(19,[]),(20,[])]),([(1,1,0),(0,3,6),(0,4,6)],[0,1,7,8,2,5],[(0,[0,1,2]),(1,[0,1,2]),(5,[0,1]),(7,[0,2]),(8,[]),(10,[])]),([(1,1,0),(0,3,6),(0,4,6)],[0,1,7,8,2,4,5],[(0,[0,1]),(0,[0,1,2]),(1,[0,1]),(1,[0,1,2]),(3,[0,1]),(5,[0,1]),(7,[0,2]),(8,[]),(10,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q210 : ck209 [85,86,106,107,108,109,110,111] d210 = true := by decide +kernel
private def d211 : List NodeSpec := [([(1,1,0),(0,3,6),(3,4,6)],[8,0,1,7,2,5],[(0,[0,1,2]),(1,[0,1,2]),(3,[0,1]),(7,[0,2]),(8,[]),(10,[]),(19,[])]),([(1,1,0),(0,3,6),(3,4,6)],[8,0,1,7,2,4,5],[(0,[0,1]),(0,[0,1,2]),(1,[0,1]),(1,[0,1,2]),(3,[0,1]),(5,[0,1]),(7,[0,2]),(8,[]),(10,[]),(19,[])]),([(1,1,0),(0,3,6),(0,5,6)],[0,1,7,8,2,4],[(0,[0,1]),(1,[0,1,2]),(2,[0,1]),(7,[0,2]),(8,[]),(10,[]),(14,[])]),([(1,1,0),(0,3,6),(0,4,6)],[0,1,7,8,2,3,5],[(0,[0,2]),(0,[0,1,2]),(1,[0,2]),(1,[0,1,2]),(3,[0]),(5,[]),(5,[0,1]),(6,[0,2]),(7,[0,2]),(8,[]),(10,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q211 : ck209 [109,110,112,113] d211 = true := by decide +kernel
private def lv_0_0_7_10 : List NodeSpec := (d209 ++ (d210 ++ d211))

private theorem ok_0_0_7_10 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_10 := by
  have go {ids ds} (h : ck209 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q209) (levelOK_append (go q210) (go q211)))
private def ck212 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d212 : List NodeSpec := [([(1,1,0),(0,3,6),(0,4,6)],[0,1,7,8,2,3,4,5],[(3,[]),(3,[0]),(5,[]),(5,[0,1]),(6,[0]),(7,[]),(7,[0,2])]),([(1,1,0),(0,3,6),(3,4,6)],[8,0,1,7,2,3,5],[(0,[0,2]),(0,[0,1,2]),(1,[0,2]),(1,[0,1,2]),(3,[]),(3,[0,1]),(5,[0]),(6,[0,2]),(7,[0,2]),(8,[]),(10,[]),(19,[])]),([(1,1,0),(0,3,6),(1,4,3)],[0,1,7,6,2,4,8,5],[(0,[0,1,2]),(1,[0,1,2]),(3,[0,1]),(5,[0]),(6,[]),(8,[])]),([(1,1,0),(0,3,6),(2,4,3)],[8,0,1,7,6,2,4,5],[(0,[0,1,2]),(1,[0,1,2]),(5,[0,1]),(6,[]),(8,[]),(19,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q212 : ck212 [87,88,108,114,115,116] d212 = true := by decide +kernel
private def d213 : List NodeSpec := [([(1,1,0),(0,3,6),(0,5,6)],[0,1,7,8,2,3,4],[(0,[0]),(0,[0,1]),(1,[0,2]),(1,[0,1,2]),(2,[]),(2,[0,1]),(3,[0,2]),(5,[0,2]),(6,[0,2]),(7,[0,2]),(8,[]),(10,[]),(14,[])]),([(1,1,0),(3,3,6),(1,4,7)],[7,0,1,6,2,4,8,5],[(0,[0,1,2]),(1,[0,1,2]),(3,[0,1]),(5,[0,1]),(19,[]),(20,[])]),([(1,1,0),(3,3,6),(2,4,7)],[7,0,1,6,2,8,4,5],[(0,[0,1,2]),(1,[0,1,2]),(3,[0,1]),(5,[0,1]),(6,[0]),(10,[]),(15,[])]),([(1,1,0),(3,3,6),(0,4,6)],[7,0,1,8,2,5],[(0,[0,1,2]),(1,[0,1,2]),(5,[0,1]),(6,[0,2]),(8,[]),(10,[]),(20,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q213 : ck212 [89,90,115,116,117,118,119,120,121] d213 = true := by decide +kernel
private def d214 : List NodeSpec := [([(1,1,0),(3,3,6),(0,4,6)],[7,0,1,8,2,4,5],[(0,[0,1]),(0,[0,1,2]),(1,[0,1]),(1,[0,1,2]),(3,[0,1]),(5,[0,1]),(6,[0,2]),(8,[]),(10,[]),(20,[])]),([(1,1,0),(3,3,6),(3,4,6)],[8,7,0,1,2,5],[(0,[0,1,2]),(1,[0,1,2]),(3,[0,1]),(6,[0,2]),(8,[]),(10,[])]),([(1,1,0),(3,3,6),(3,4,6)],[8,7,0,1,2,4,5],[(0,[0,1]),(0,[0,1,2]),(1,[0,1]),(1,[0,1,2]),(3,[0,1]),(5,[0,1]),(6,[0,2]),(8,[]),(10,[])]),([(1,1,0),(3,3,6),(0,5,6)],[7,0,1,8,2,4],[(0,[0,1]),(1,[0,1,2]),(2,[0,1]),(6,[0,2]),(8,[]),(10,[]),(14,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q214 : ck212 [117,119,120,121,122] d214 = true := by decide +kernel
private def lv_0_0_7_11 : List NodeSpec := (d212 ++ (d213 ++ d214))

private theorem ok_0_0_7_11 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_11 := by
  have go {ids ds} (h : ck212 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q212) (levelOK_append (go q213) (go q214)))
private def ck215 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d215 : List NodeSpec := [([(1,1,0),(3,3,6),(0,4,6)],[7,0,1,8,2,3,5],[(0,[0,2]),(0,[0,1,2]),(1,[0,2]),(1,[0,1,2]),(3,[0]),(5,[]),(5,[0,1]),(6,[0,2]),(7,[0,2]),(8,[]),(10,[]),(20,[])]),([(1,1,0),(3,3,6),(3,4,6)],[8,7,0,1,2,3,5],[(0,[0,2]),(0,[0,1,2]),(1,[0,2]),(1,[0,1,2]),(3,[]),(3,[0,1]),(5,[0]),(6,[0,2]),(7,[0,2]),(8,[]),(10,[])]),([(1,1,0),(3,3,6),(3,4,6)],[8,7,0,1,2,3,4,5],[(3,[]),(3,[0,1]),(5,[]),(5,[0]),(6,[]),(6,[0,2]),(7,[0])]),([(1,1,0),(3,3,6),(0,4,3)],[7,0,1,6,2,8,4,5],[(0,[0,1,2]),(1,[0,1,2]),(3,[0]),(5,[0,1]),(7,[]),(8,[]),(10,[]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q215 : ck215 [91,119,123,124,125,126] d215 = true := by decide +kernel
private def d216 : List NodeSpec := [([(1,1,0),(3,3,6),(3,4,3)],[8,7,0,1,6,2,4,5],[(0,[0,1,2]),(1,[0,1,2]),(3,[0,1]),(7,[]),(8,[]),(20,[])]),([(1,1,0),(3,3,6),(0,5,6)],[7,0,1,8,2,3,4],[(0,[0]),(0,[0,1]),(1,[0,2]),(1,[0,1,2]),(2,[]),(2,[0,1]),(3,[0,2]),(5,[0,2]),(6,[0,2]),(7,[0,2]),(8,[]),(10,[]),(14,[])]),([(1,1,0),(0,4,6),(2,6,7)],[8,0,1,7,2,3,5],[(0,[0,1]),(0,[0,1,2]),(1,[0,1]),(1,[0,1,2]),(3,[]),(3,[0]),(5,[]),(5,[0]),(6,[0,1]),(7,[0,1]),(8,[]),(10,[]),(19,[])]),([(1,1,0),(0,4,6),(1,3,7)],[0,1,7,6,2,3,8,5],[(0,[0,1,2]),(1,[0,1,2]),(3,[0]),(5,[0]),(6,[0,1]),(7,[0,1])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q216 : ck215 [92,93,112,113,126,127,128,129] d216 = true := by decide +kernel
private def d217 : List NodeSpec := [([(1,1,0),(0,4,6),(2,3,7)],[8,0,1,7,6,2,3,5],[(0,[0,1,2]),(1,[0,1,2]),(3,[0]),(6,[0,1]),(7,[0,1]),(19,[]),(20,[])]),([(1,1,0),(0,4,6),(0,5,6)],[0,1,7,8,2,3],[(0,[0,1]),(1,[0,1,2]),(2,[0,1]),(5,[0,2]),(8,[]),(10,[]),(14,[])]),([(1,1,0),(0,4,6),(1,4,3)],[0,1,7,6,2,3,8,5],[(0,[0,1,2]),(1,[0,1,2]),(3,[]),(3,[0]),(5,[0]),(6,[0,1]),(8,[])]),([(1,1,0),(0,4,6),(3,4,3)],[8,0,1,7,6,2,3,5],[(0,[0,1,2]),(1,[0,1,2]),(3,[]),(3,[0]),(7,[0,1]),(8,[]),(20,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q217 : ck215 [94,95,96,112,114,129,130,131,132] d217 = true := by decide +kernel
private def lv_0_0_7_12 : List NodeSpec := (d215 ++ (d216 ++ d217))

private theorem ok_0_0_7_12 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_12 := by
  have go {ids ds} (h : ck215 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q215) (levelOK_append (go q216) (go q217)))
private def ck218 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d218 : List NodeSpec := [([(1,1,0),(0,4,6),(0,5,6)],[0,1,7,8,2,3,4],[(0,[0]),(0,[0,1]),(1,[0,2]),(1,[0,1,2]),(2,[]),(2,[0,1]),(3,[0,2]),(5,[0,2]),(6,[0,2]),(7,[0,2]),(8,[]),(10,[]),(14,[])]),([(1,1,0),(3,4,6),(1,3,7)],[7,0,1,6,2,3,8,5],[(0,[0,1,2]),(1,[0,1,2]),(5,[0]),(6,[0,1]),(7,[0,1]),(19,[]),(20,[])]),([(1,1,0),(3,4,6),(2,3,7)],[7,0,1,6,2,8,3,5],[(0,[0,1,2]),(1,[0,1,2]),(3,[0]),(5,[0]),(6,[0,1]),(7,[0,1]),(10,[]),(15,[])]),([(1,1,0),(3,4,6),(0,5,6)],[7,0,1,8,2,3],[(0,[0,1]),(1,[0,1,2]),(2,[0,1]),(3,[0,2]),(8,[]),(10,[]),(14,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q218 : ck218 [97,98,123,124,131,132,133,134,135] d218 = true := by decide +kernel
private def d219 : List NodeSpec := [([(1,1,0),(3,4,6),(0,4,3)],[7,0,1,6,2,8,3,5],[(0,[0,1,2]),(1,[0,1,2]),(3,[0]),(5,[]),(5,[0]),(7,[0,1]),(8,[]),(10,[]),(15,[])]),([(1,1,0),(3,4,6),(2,4,3)],[7,8,0,1,6,2,3,5],[(0,[0,1,2]),(1,[0,1,2]),(5,[]),(5,[0]),(6,[0,1]),(8,[]),(19,[])]),([(1,1,0),(3,4,6),(0,5,6)],[7,0,1,8,2,3,4],[(0,[0]),(0,[0,1]),(1,[0,2]),(1,[0,1,2]),(2,[]),(2,[0,1]),(3,[0,2]),(5,[0,2]),(6,[0,2]),(7,[0,2]),(8,[]),(10,[]),(14,[])]),([(1,1,0),(0,4,3),(3,7,6)],[8,0,1,2,3,4,5],[(0,[]),(0,[0,1,2]),(1,[]),(1,[0,1,2]),(3,[]),(3,[0,2]),(5,[]),(5,[0]),(6,[]),(6,[0,2]),(8,[]),(10,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q219 : ck218 [99,100,119,123,125,136,137,138] d219 = true := by decide +kernel
private def d220 : List NodeSpec := [([(1,1,0),(0,4,3),(3,7,6)],[8,0,1,6,2,3,4,5],[(0,[0,1,2]),(1,[0,1,2]),(3,[0]),(5,[]),(5,[0]),(6,[0]),(7,[0]),(10,[])]),([(1,1,0),(0,4,3),(1,4,3)],[0,1,6,2,7,8,5],[(0,[1,2]),(0,[0,1,2]),(1,[1,2]),(1,[0,1,2]),(3,[]),(3,[0]),(5,[]),(5,[0])]),([(1,1,0),(0,4,3),(0,5,6)],[0,1,8,2,7,3,4],[(1,[0,2]),(1,[0,1,2]),(2,[]),(2,[1]),(3,[0,2]),(5,[0,2]),(6,[0,2]),(8,[]),(10,[]),(11,[2]),(12,[2])]),([(1,1,0),(0,4,3),(0,5,6)],[0,1,8,6,2,7,3,4],[(0,[1]),(1,[0,1,2]),(5,[0,2]),(7,[0,2]),(8,[]),(9,[1]),(10,[]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q220 : ck218 [0,2,9,15,81,82,84,101,102,119,123,126,136,138,139,140,141,142,143,144] d220 = true := by decide +kernel
private def lv_0_0_7_13 : List NodeSpec := (d218 ++ (d219 ++ d220))

private theorem ok_0_0_7_13 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_13 := by
  have go {ids ds} (h : ck218 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q218) (levelOK_append (go q219) (go q220)))
private def ck221 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d221 : List NodeSpec := [([(1,1,0),(1,4,3),(0,7,6)],[0,1,8,2,3,4,5],[(0,[]),(0,[0,1,2]),(1,[]),(1,[0,1,2]),(3,[]),(3,[0]),(5,[]),(5,[0,2]),(6,[0]),(7,[]),(8,[]),(10,[])]),([(1,1,0),(1,4,3),(0,7,6)],[0,1,8,6,2,3,4,5],[(0,[0,1,2]),(1,[0,1,2]),(3,[]),(3,[0]),(5,[0]),(6,[0]),(7,[0])]),([(1,1,0),(1,4,3),(0,5,6)],[0,1,8,2,3,4,7],[(1,[0,2]),(1,[0,1,2]),(2,[]),(2,[1]),(3,[0,2]),(5,[0,2]),(6,[0,2]),(8,[]),(10,[]),(11,[2]),(12,[2])]),([(1,1,0),(1,4,3),(0,5,6)],[0,1,8,6,2,3,4,7],[(0,[1]),(1,[0,1,2]),(3,[0,2]),(6,[0,2]),(8,[]),(9,[1])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q221 : ck221 [16,83,103,108,112,115,131,141,142,143,144,145] d221 = true := by decide +kernel
private def d222 : List NodeSpec := [([(1,1,0),(2,4,3),(2,6,7)],[0,1,8,2,3,4,5],[(0,[]),(0,[0,1,2]),(1,[]),(1,[0,1,2]),(3,[]),(3,[0,2]),(5,[]),(5,[0]),(6,[0]),(7,[]),(8,[]),(10,[]),(19,[])]),([(1,1,0),(2,4,3),(2,6,7)],[0,1,8,6,2,3,4,5],[(0,[0,1,2]),(1,[0,1,2]),(3,[0]),(5,[]),(5,[0]),(6,[0]),(7,[0]),(19,[])]),([(1,1,0),(2,4,3),(0,5,6)],[7,0,1,8,2,3,4],[(1,[0,2]),(1,[0,1,2]),(2,[]),(2,[1]),(3,[0,2]),(5,[0,2]),(6,[0,2]),(8,[]),(10,[]),(11,[2]),(12,[2])]),([(1,1,0),(2,4,3),(0,5,6)],[7,0,1,8,6,2,3,4],[(0,[1]),(1,[0,1,2]),(5,[0,2]),(6,[0,2]),(8,[]),(9,[1])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q222 : ck221 [104,116,137,146] d222 = true := by decide +kernel
private def d223 : List NodeSpec := [([(1,1,0),(3,4,3),(2,6,7)],[0,1,8,2,3,4,5],[(0,[]),(0,[0,1,2]),(1,[]),(1,[0,1,2]),(3,[]),(3,[0]),(5,[]),(5,[0,2]),(6,[]),(6,[0,2]),(8,[]),(10,[]),(20,[])]),([(1,1,0),(3,4,3),(2,6,7)],[0,1,8,6,2,3,4,5],[(0,[0,1,2]),(1,[0,1,2]),(3,[]),(3,[0]),(5,[0]),(6,[0]),(7,[0]),(20,[])]),([(1,1,0),(3,4,3),(0,5,6)],[7,0,1,8,2,3,4],[(1,[0,2]),(1,[0,1,2]),(2,[]),(2,[1]),(3,[0,2]),(5,[0,2]),(6,[0,2]),(8,[]),(10,[]),(11,[2]),(12,[2])]),([(1,1,0),(3,4,3),(0,5,6)],[7,0,1,8,6,2,3,4],[(0,[1]),(1,[0,1,2]),(3,[0,2]),(7,[0,2]),(8,[]),(9,[1])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q223 : ck221 [105,127,132,147] d223 = true := by decide +kernel
private def lv_0_0_7_14 : List NodeSpec := (d221 ++ (d222 ++ d223))

private theorem ok_0_0_7_14 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_14 := by
  have go {ids ds} (h : ck221 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q221) (levelOK_append (go q222) (go q223)))
private def ck224 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d224 : List NodeSpec := [([(2,1,0),(1,0,6),(0,4,3)],[0,1,7,2,8,3,4,5],[(0,[2]),(1,[2]),(2,[2]),(3,[]),(4,[2]),(5,[]),(6,[]),(7,[]),(8,[]),(10,[]),(11,[])]),([(2,1,0),(1,0,6),(1,4,3)],[0,1,7,2,3,4,8,5],[(0,[2]),(1,[2]),(2,[2]),(3,[]),(4,[2]),(5,[]),(6,[]),(7,[]),(8,[])]),([(2,1,0),(1,0,6),(2,4,3)],[8,0,1,7,2,3,4,5],[(0,[2]),(1,[2]),(2,[2]),(3,[]),(4,[2]),(5,[]),(6,[]),(7,[]),(8,[]),(19,[])]),([(2,1,0),(1,0,6),(3,4,3)],[8,0,1,7,2,3,4,5],[(0,[2]),(1,[2]),(2,[2]),(3,[]),(4,[2]),(5,[]),(6,[]),(7,[]),(8,[]),(20,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q224 : ck224 [148,149,150] d224 = true := by decide +kernel
private def d225 : List NodeSpec := [([(2,1,0),(2,1,6),(0,4,3)],[7,0,1,2,8,3,4,5],[(0,[2]),(1,[2]),(2,[2]),(3,[]),(4,[2]),(5,[]),(6,[]),(7,[]),(11,[])]),([(2,1,0),(2,1,6),(1,4,3)],[7,0,1,2,3,4,8,5],[(0,[2]),(1,[2]),(2,[2]),(3,[]),(4,[2]),(5,[]),(6,[]),(7,[]),(10,[]),(11,[])]),([(2,1,0),(2,1,6),(2,4,3)],[8,7,0,1,2,3,4,5],[(0,[2]),(1,[2]),(2,[2]),(3,[]),(4,[2]),(5,[]),(6,[]),(7,[]),(11,[]),(19,[])]),([(2,1,0),(2,1,6),(3,4,3)],[8,7,0,1,2,3,4,5],[(0,[2]),(1,[2]),(2,[2]),(3,[]),(4,[2]),(5,[]),(6,[]),(7,[]),(11,[]),(20,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q225 : ck224 [151,152,153] d225 = true := by decide +kernel
private def d226 : List NodeSpec := [([(2,1,0),(3,1,0),(0,4,3)],[7,6,1,2,8,3,4,5],[]),([(2,1,0),(3,1,0),(1,4,3)],[7,6,1,2,3,4,8,5],[]),([(2,1,0),(3,1,0),(2,4,3)],[8,7,6,1,2,3,4,5],[]),([(2,1,0),(3,1,0),(3,4,3)],[8,7,6,1,2,3,4,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q226 : ck224 [5,6,7,8,154] d226 = true := by decide +kernel
private def lv_0_0_7_15 : List NodeSpec := (d224 ++ (d225 ++ d226))

private theorem ok_0_0_7_15 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_15 := by
  have go {ids ds} (h : ck224 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q224) (levelOK_append (go q225) (go q226)))
private def ck227 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d227 : List NodeSpec := [([(2,1,0),(3,1,0),(0,4,3)],[7,6,0,2,8,3,4,5],[(10,[]),(15,[])]),([(2,1,0),(3,1,0),(1,4,3)],[7,6,0,2,3,4,8,5],[(8,[]),(16,[])]),([(2,1,0),(3,1,0),(2,4,3)],[8,7,6,0,2,3,4,5],[]),([(2,1,0),(3,1,0),(3,4,3)],[8,7,6,0,2,3,4,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q227 : ck227 [10,11,12,13,155] d227 = true := by decide +kernel
private def d228 : List NodeSpec := [([(2,1,0),(0,4,3),(1,4,3)],[6,0,1,2,7,8,5],[(0,[1,2]),(0,[0,1,2]),(1,[1,2]),(1,[0,1,2]),(3,[]),(3,[0]),(5,[]),(5,[0])]),([(3,1,0),(0,4,3),(1,4,3)],[6,0,1,2,7,8,5],[(0,[1,2]),(0,[0,1,2]),(1,[1,2]),(1,[0,1,2]),(3,[]),(3,[0]),(5,[]),(5,[0])]),([(0,3,0),(1,1,6),(3,4,1)],[8,0,7,2,3,4,5],[(0,[0,1]),(0,[0,1,2]),(3,[0,1]),(7,[]),(7,[2]),(10,[]),(12,[]),(12,[2]),(15,[])]),([(0,3,0),(1,2,6),(1,4,0)],[0,1,7,3,4,8,5],[(0,[0,1]),(0,[0,1,2]),(1,[0]),(1,[0,2]),(3,[0,1]),(4,[]),(5,[0,1]),(6,[1]),(7,[]),(8,[1]),(9,[]),(15,[1])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q228 : ck227 [1,4,81,82,149,152,154,155] d228 = true := by decide +kernel
private def d229 : List NodeSpec := [([(0,3,0),(1,2,6),(2,4,0)],[8,0,1,7,3,4,5],[(0,[0,1]),(0,[0,1,2]),(1,[0]),(1,[0,2]),(3,[0,1]),(4,[]),(5,[0,1]),(6,[1]),(7,[]),(8,[1]),(15,[1])]),([(0,3,0),(1,2,6),(0,4,1)],[0,8,1,7,3,4,5],[(0,[0,1]),(0,[0,1,2]),(3,[0,1]),(4,[]),(4,[2]),(5,[0,1]),(6,[1]),(7,[]),(8,[1]),(12,[]),(12,[2]),(15,[1])]),([(0,3,0),(1,2,6),(3,4,1)],[8,0,1,7,3,4,5],[(0,[0,1]),(0,[0,1,2]),(3,[0,1]),(4,[]),(4,[2]),(5,[0,1]),(6,[1]),(7,[]),(8,[1]),(9,[]),(12,[]),(12,[2]),(15,[1])]),([(0,3,0),(1,3,0),(2,7,6)],[8,0,1,2,4,5],[(0,[0,1,2]),(1,[0,1,2]),(6,[]),(8,[]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q229 : ck227 [156,157,158,159] d229 = true := by decide +kernel
private def lv_0_0_7_16 : List NodeSpec := (d227 ++ (d228 ++ d229))

private theorem ok_0_0_7_16 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_16 := by
  have go {ids ds} (h : ck227 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q227) (levelOK_append (go q228) (go q229)))
private def ck230 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d230 : List NodeSpec := [([(0,3,0),(3,3,1),(1,6,7)],[0,8,1,2,4,5],[(0,[0,1,2]),(1,[0,1,2]),(6,[]),(7,[]),(11,[0]),(12,[1]),(15,[])]),([(0,3,0),(1,4,0),(2,7,6)],[8,0,1,2,3,4,5],[(0,[]),(0,[0]),(0,[1]),(0,[0,1,2]),(1,[]),(1,[0,1,2]),(3,[]),(3,[0]),(5,[]),(6,[]),(7,[1]),(8,[]),(10,[]),(11,[]),(15,[])]),([(0,3,0),(1,4,0),(0,5,7)],[6,0,1,2,3,4,8],[(0,[1]),(0,[0,1]),(1,[1,2]),(1,[0,1,2]),(2,[]),(3,[]),(3,[0]),(6,[1,2]),(7,[1,2]),(8,[]),(9,[]),(15,[])]),([(0,3,0),(2,4,0),(1,6,7)],[0,1,2,3,8,4,5],[(0,[]),(0,[0]),(0,[1]),(0,[0,1,2]),(1,[]),(1,[0,1,2]),(3,[]),(5,[]),(5,[0]),(6,[]),(7,[1]),(8,[]),(10,[]),(11,[]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q230 : ck230 [160,161,162,163] d230 = true := by decide +kernel
private def d231 : List NodeSpec := [([(0,3,0),(0,4,1),(1,7,6)],[0,1,8,2,3,4,5],[(0,[]),(0,[0,1,2]),(1,[]),(1,[0,1,2]),(3,[]),(3,[0,2]),(5,[]),(5,[0]),(6,[]),(7,[]),(7,[1]),(11,[0]),(12,[1]),(15,[])]),([(0,3,0),(3,4,1),(1,6,7)],[8,0,1,2,3,4,5],[(0,[]),(0,[0,1,2]),(1,[]),(1,[0,1,2]),(3,[]),(3,[0]),(5,[]),(6,[]),(7,[]),(7,[1]),(11,[0]),(12,[1]),(15,[])]),([(0,3,0),(3,4,1),(2,5,7)],[6,0,1,2,3,4,8],[(1,[1,2]),(1,[0,1,2]),(2,[]),(2,[0]),(3,[]),(3,[0]),(6,[1,2]),(7,[1,2]),(9,[]),(10,[2]),(11,[]),(11,[0]),(15,[])]),([(1,3,0),(2,3,1),(2,6,7)],[0,8,1,2,4,5],[(0,[0,1,2]),(1,[0,1,2]),(6,[]),(7,[]),(8,[1]),(10,[0]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q231 : ck230 [164,165,166,167] d231 = true := by decide +kernel
private def d232 : List NodeSpec := [([(1,3,0),(0,6,1),(2,4,1)],[8,0,7,2,3,4,5],[(1,[0,1]),(1,[0,1,2]),(3,[]),(5,[0,1]),(6,[]),(6,[2]),(8,[]),(8,[2]),(10,[0]),(11,[]),(15,[])]),([(1,3,0),(0,4,0),(1,2,7)],[0,1,8,3,6,4,5],[(0,[1,2]),(0,[0,1,2]),(1,[1]),(1,[0,1]),(3,[2]),(4,[]),(5,[]),(6,[1,2]),(7,[1,2]),(8,[2]),(9,[]),(15,[2])]),([(1,3,0),(0,4,0),(2,6,7)],[8,0,1,2,3,4,5],[(0,[]),(0,[0]),(0,[1]),(0,[0,1,2]),(1,[]),(1,[0,1,2]),(3,[]),(5,[]),(5,[0]),(6,[]),(6,[1]),(8,[]),(10,[]),(11,[]),(15,[])]),([(1,3,0),(0,4,0),(0,5,6)],[7,0,1,2,3,8,4],[(0,[0]),(0,[0,1]),(1,[0,2]),(1,[0,1,2]),(2,[]),(3,[0,2]),(5,[0,2]),(6,[]),(6,[1]),(8,[]),(9,[]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q232 : ck230 [] d232 = true := by decide +kernel
private def lv_0_0_7_17 : List NodeSpec := (d230 ++ (d231 ++ d232))

private theorem ok_0_0_7_17 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_17 := by
  have go {ids ds} (h : ck230 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q230) (levelOK_append (go q231) (go q232)))
private def ck233 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d233 : List NodeSpec := [([(1,3,0),(3,4,0),(2,6,7)],[0,1,2,3,8,4,5],[(0,[]),(0,[0]),(0,[1]),(0,[0,1,2]),(1,[]),(1,[0,1,2]),(3,[]),(3,[0]),(5,[]),(6,[]),(6,[1]),(8,[]),(10,[]),(11,[]),(15,[])]),([(1,3,0),(3,4,0),(0,5,6)],[7,0,1,2,3,8,4],[(0,[0]),(0,[0,1]),(1,[0,2]),(1,[0,1,2]),(2,[]),(3,[0,2]),(5,[0,2]),(6,[]),(6,[1]),(8,[]),(15,[])]),([(1,3,0),(1,4,1),(0,7,6)],[0,1,2,3,8,4,5],[(0,[]),(0,[0,1,2]),(1,[]),(1,[0,1,2]),(3,[]),(3,[0]),(5,[]),(6,[]),(6,[1]),(7,[]),(8,[1]),(10,[0]),(15,[])]),([(1,3,0),(1,4,1),(0,5,6)],[0,1,2,3,8,4,7],[(1,[0,2]),(1,[0,1,2]),(2,[]),(2,[1]),(3,[0,2]),(5,[0,2]),(6,[]),(6,[1]),(8,[]),(8,[1]),(12,[2]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q233 : ck233 [] d233 = true := by decide +kernel
private def d234 : List NodeSpec := [([(1,3,0),(2,4,1),(1,2,7)],[0,1,8,3,6,4,5],[(0,[1,2]),(0,[0,1,2]),(3,[2]),(4,[]),(4,[0]),(5,[]),(6,[1,2]),(7,[1,2]),(9,[]),(10,[]),(10,[0]),(11,[2]),(15,[2])]),([(1,3,0),(2,4,1),(2,6,7)],[0,8,1,2,3,4,5],[(0,[]),(0,[0,1,2]),(1,[]),(1,[0,1,2]),(3,[]),(5,[]),(5,[0]),(6,[]),(6,[1]),(7,[]),(8,[1]),(10,[0]),(15,[])]),([(1,3,0),(2,4,1),(0,5,6)],[7,0,1,2,3,8,4],[(1,[0,2]),(1,[0,1,2]),(2,[]),(2,[1]),(3,[0,2]),(5,[0,2]),(6,[]),(6,[1]),(8,[]),(8,[1]),(9,[]),(12,[2]),(15,[])]),([(2,3,0),(0,4,0),(1,2,7)],[6,0,1,8,3,4,5],[(0,[1,2]),(0,[0,1,2]),(1,[1]),(1,[0,1]),(3,[2]),(4,[]),(5,[]),(6,[1,2]),(7,[1,2]),(8,[2]),(15,[2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q234 : ck233 [] d234 = true := by decide +kernel
private def d235 : List NodeSpec := [([(2,3,0),(1,4,1),(2,7,6)],[0,8,1,2,3,4,5],[(0,[]),(0,[0,1,2]),(1,[]),(1,[0,1,2]),(3,[]),(3,[0]),(5,[]),(6,[]),(7,[]),(7,[1]),(8,[1]),(10,[0]),(15,[])]),([(2,3,0),(2,4,1),(1,6,7)],[8,0,1,2,3,4,5],[(0,[]),(0,[0,1,2]),(1,[]),(1,[0,1,2]),(3,[]),(5,[]),(5,[0]),(6,[]),(7,[]),(7,[1]),(8,[1]),(10,[0]),(15,[])]),([(2,3,0),(2,4,1),(1,2,7)],[6,0,1,8,3,4,5],[(0,[1,2]),(0,[0,1,2]),(3,[2]),(4,[]),(4,[0]),(5,[]),(6,[1,2]),(7,[1,2]),(10,[]),(10,[0]),(11,[2]),(15,[2])]),([(3,3,0),(1,4,0),(0,5,7)],[6,0,1,2,3,4,8],[(0,[1]),(0,[0,1]),(1,[1,2]),(1,[0,1,2]),(2,[]),(3,[]),(3,[0]),(6,[1,2]),(7,[1,2]),(8,[]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q235 : ck233 [] d235 = true := by decide +kernel
private def lv_0_0_7_18 : List NodeSpec := (d233 ++ (d234 ++ d235))

private theorem ok_0_0_7_18 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_18 := by
  have go {ids ds} (h : ck233 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q233) (levelOK_append (go q234) (go q235)))
private def ck236 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d236 : List NodeSpec := [([(3,3,0),(0,4,1),(1,7,6)],[0,1,8,2,3,4,5],[(0,[]),(0,[0,1,2]),(1,[]),(1,[0,1,2]),(3,[]),(5,[]),(5,[0]),(6,[]),(6,[1]),(7,[]),(11,[0]),(12,[1]),(15,[])]),([(3,3,0),(3,4,1),(1,6,7)],[8,0,1,2,3,4,5],[(0,[]),(0,[0,1,2]),(1,[]),(1,[0,1,2]),(3,[]),(3,[0]),(5,[]),(6,[]),(6,[1]),(7,[]),(11,[0]),(12,[1]),(15,[])]),([(3,3,0),(3,4,1),(2,5,7)],[6,0,1,2,3,4,8],[(1,[1,2]),(1,[0,1,2]),(2,[]),(2,[0]),(3,[]),(3,[0]),(6,[1,2]),(7,[1,2]),(10,[2]),(11,[]),(11,[0]),(15,[])]),([(0,3,1),(1,3,1),(2,7,6)],[8,0,1,2,4,5],[(0,[0,1,2]),(1,[0,1,2]),(6,[]),(10,[]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q236 : ck236 [168,169,170,171] d236 = true := by decide +kernel
private def d237 : List NodeSpec := [([(0,3,1),(0,4,0),(1,6,7)],[0,1,8,2,3,4,5],[(0,[]),(0,[0,1,2]),(1,[]),(1,[0,1,2]),(3,[]),(5,[]),(5,[0]),(6,[]),(6,[1,2]),(7,[]),(7,[1]),(11,[1]),(12,[0]),(15,[])]),([(0,3,1),(0,4,0),(1,2,7)],[0,6,1,8,3,4,5],[(0,[1,2]),(0,[0,1,2]),(3,[2]),(4,[]),(4,[0]),(5,[]),(6,[1,2]),(7,[1,2]),(8,[2]),(12,[]),(12,[0]),(15,[2])]),([(0,3,1),(3,4,0),(1,6,7)],[0,8,1,2,3,4,5],[(0,[]),(0,[0,1,2]),(1,[]),(1,[0,1,2]),(3,[]),(3,[0]),(5,[]),(6,[]),(7,[]),(7,[1]),(11,[1]),(12,[0]),(15,[])]),([(0,3,1),(1,4,1),(2,7,6)],[8,0,1,2,3,4,5],[(0,[]),(0,[0]),(0,[1]),(0,[0,1,2]),(1,[]),(1,[0,1,2]),(3,[]),(3,[0]),(5,[]),(6,[]),(7,[1]),(8,[]),(10,[]),(12,[]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q237 : ck236 [] d237 = true := by decide +kernel
private def d238 : List NodeSpec := [([(0,3,1),(2,4,1),(1,6,7)],[0,1,2,3,8,4,5],[(0,[]),(0,[0]),(0,[1]),(0,[0,1,2]),(1,[]),(1,[0,1,2]),(3,[]),(5,[]),(5,[0]),(6,[]),(7,[1]),(8,[]),(10,[]),(12,[]),(15,[])]),([(0,3,1),(2,4,1),(1,2,7)],[0,6,1,8,3,4,5],[(0,[1,2]),(0,[0,1,2]),(1,[1]),(1,[0,1]),(3,[2]),(4,[]),(5,[]),(6,[1,2]),(7,[1,2]),(10,[]),(15,[2])]),([(1,3,1),(1,4,0),(0,7,6)],[0,1,2,3,8,4,5],[(0,[]),(0,[0,1,2]),(1,[]),(1,[0,1,2]),(3,[]),(3,[0]),(5,[]),(6,[]),(6,[1]),(7,[]),(8,[0]),(10,[1]),(15,[])]),([(1,3,1),(1,4,0),(0,5,7)],[0,1,2,3,6,4,8],[(1,[1,2]),(1,[0,1,2]),(2,[]),(2,[0]),(3,[]),(3,[0]),(6,[1,2]),(7,[1,2]),(8,[]),(8,[0]),(12,[2]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q238 : ck236 [] d238 = true := by decide +kernel
private def lv_0_0_7_19 : List NodeSpec := (d236 ++ (d237 ++ d238))

private theorem ok_0_0_7_19 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_19 := by
  have go {ids ds} (h : ck236 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q236) (levelOK_append (go q237) (go q238)))
private def ck239 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d239 : List NodeSpec := [([(1,3,1),(2,4,0),(2,6,7)],[8,0,1,2,3,4,5],[(0,[]),(0,[0,1,2]),(1,[]),(1,[0,1,2]),(3,[]),(5,[]),(5,[0]),(6,[]),(6,[1]),(7,[]),(8,[0]),(10,[1]),(15,[])]),([(1,3,1),(0,4,1),(2,6,7)],[8,0,1,2,3,4,5],[(0,[]),(0,[0]),(0,[1]),(0,[0,1,2]),(1,[]),(1,[0,1,2]),(3,[]),(5,[]),(5,[0]),(6,[]),(6,[1]),(8,[]),(10,[]),(12,[]),(15,[])]),([(1,3,1),(3,4,1),(2,6,7)],[0,1,2,3,8,4,5],[(0,[]),(0,[0]),(0,[1]),(0,[0,1,2]),(1,[]),(1,[0,1,2]),(3,[]),(3,[0]),(5,[]),(6,[]),(6,[1]),(8,[]),(10,[]),(12,[]),(15,[])]),([(1,3,1),(3,4,1),(2,5,7)],[0,1,2,3,6,4,8],[(0,[1]),(0,[0,1]),(1,[1,2]),(1,[0,1,2]),(2,[]),(3,[]),(3,[0]),(6,[1,2]),(7,[1,2]),(10,[2]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q239 : ck239 [] d239 = true := by decide +kernel
private def d240 : List NodeSpec := [([(2,3,1),(1,2,6),(1,4,0)],[0,1,7,3,4,8,5],[(0,[0,1]),(0,[0,1,2]),(3,[0,1]),(4,[]),(4,[2]),(5,[0,1]),(6,[1]),(7,[]),(9,[]),(10,[]),(10,[2]),(11,[1]),(15,[1])]),([(2,3,1),(1,2,6),(2,4,0)],[8,0,1,7,3,4,5],[(0,[0,1]),(0,[0,1,2]),(3,[0,1]),(4,[]),(4,[2]),(5,[0,1]),(6,[1]),(7,[]),(10,[]),(10,[2]),(11,[1]),(15,[1])]),([(2,3,1),(1,2,6),(0,4,1)],[0,8,1,7,3,4,5],[(0,[0,1]),(0,[0,1,2]),(1,[0]),(1,[0,2]),(3,[0,1]),(4,[]),(5,[0,1]),(6,[1]),(7,[]),(10,[]),(15,[1])]),([(2,3,1),(1,2,6),(3,4,1)],[8,0,1,7,3,4,5],[(0,[0,1]),(0,[0,1,2]),(1,[0]),(1,[0,2]),(3,[0,1]),(4,[]),(5,[0,1]),(6,[1]),(7,[]),(9,[]),(10,[]),(15,[1])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q240 : ck239 [] d240 = true := by decide +kernel
private def d241 : List NodeSpec := [([(2,3,1),(1,4,0),(2,7,6)],[0,1,8,2,3,4,5],[(0,[]),(0,[0,1,2]),(1,[]),(1,[0,1,2]),(3,[]),(3,[0]),(5,[]),(6,[]),(7,[]),(7,[1]),(8,[0]),(10,[1]),(15,[])]),([(2,3,1),(1,4,0),(0,7,1)],[6,0,8,2,3,4,5],[(1,[1,2]),(1,[0,1,2]),(3,[]),(3,[0]),(6,[]),(7,[1,2]),(8,[]),(8,[0]),(10,[1]),(11,[]),(15,[])]),([(2,3,1),(1,4,0),(0,5,7)],[6,0,1,2,3,4,8],[(1,[1,2]),(1,[0,1,2]),(2,[]),(2,[0]),(3,[]),(3,[0]),(6,[1,2]),(7,[1,2]),(8,[]),(8,[0]),(9,[]),(12,[2]),(15,[])]),([(2,3,1),(2,4,0),(1,7,6)],[8,0,1,2,3,4,5],[(0,[]),(0,[0,1,2]),(1,[]),(1,[0,1,2]),(3,[]),(5,[]),(5,[0]),(6,[]),(7,[]),(7,[1]),(8,[0]),(10,[1]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q241 : ck239 [] d241 = true := by decide +kernel
private def lv_0_0_7_20 : List NodeSpec := (d239 ++ (d240 ++ d241))

private theorem ok_0_0_7_20 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_20 := by
  have go {ids ds} (h : ck239 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q239) (levelOK_append (go q240) (go q241)))
private def ck242 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d242 : List NodeSpec := [([(2,3,1),(3,4,1),(2,5,7)],[6,0,1,2,3,4,8],[(0,[1]),(0,[0,1]),(1,[1,2]),(1,[0,1,2]),(2,[]),(3,[]),(3,[0]),(6,[1,2]),(7,[1,2]),(9,[]),(10,[2]),(15,[])]),([(3,3,1),(0,4,0),(1,7,6)],[0,8,1,2,3,4,5],[(0,[]),(0,[0,1,2]),(1,[]),(1,[0,1,2]),(3,[]),(5,[]),(5,[0]),(6,[]),(6,[1]),(7,[]),(11,[1]),(12,[0]),(15,[])]),([(3,3,1),(0,4,0),(1,1,7)],[6,0,8,2,3,4,5],[(0,[1,2]),(0,[0,1,2]),(5,[]),(5,[0]),(6,[1,2]),(10,[]),(12,[]),(12,[0]),(15,[])]),([(3,3,1),(0,4,0),(1,2,7)],[6,0,1,8,3,4,5],[(0,[1,2]),(0,[0,1,2]),(3,[2]),(4,[]),(4,[0]),(5,[]),(6,[1,2]),(7,[1,2]),(8,[2]),(9,[]),(12,[]),(12,[0]),(15,[2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q242 : ck242 [] d242 = true := by decide +kernel
private def d243 : List NodeSpec := [([(3,3,1),(0,4,0),(2,5,6)],[7,0,1,2,3,8,4],[(1,[0,2]),(1,[0,1,2]),(2,[]),(2,[1]),(3,[0,2]),(5,[0,2]),(6,[]),(6,[1]),(9,[]),(10,[2]),(11,[]),(11,[1]),(15,[])]),([(3,3,1),(3,4,0),(1,6,7)],[8,0,1,2,3,4,5],[(0,[]),(0,[0,1,2]),(1,[]),(1,[0,1,2]),(3,[]),(3,[0]),(5,[]),(6,[]),(6,[1]),(7,[]),(11,[1]),(12,[0]),(15,[])]),([(3,3,1),(3,4,0),(2,5,6)],[7,0,1,2,3,8,4],[(1,[0,2]),(1,[0,1,2]),(2,[]),(2,[1]),(3,[0,2]),(5,[0,2]),(6,[]),(6,[1]),(10,[2]),(11,[]),(11,[1]),(15,[])]),([(3,3,1),(1,4,1),(2,5,6)],[0,1,2,3,8,4,7],[(0,[0]),(0,[0,1]),(1,[0,2]),(1,[0,1,2]),(2,[]),(3,[0,2]),(5,[0,2]),(6,[]),(6,[1]),(10,[2]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q243 : ck242 [] d243 = true := by decide +kernel
private def d244 : List NodeSpec := [([(3,3,1),(2,4,1),(1,2,7)],[6,0,1,8,3,4,5],[(0,[1,2]),(0,[0,1,2]),(1,[1]),(1,[0,1]),(3,[2]),(4,[]),(5,[]),(6,[1,2]),(7,[1,2]),(9,[]),(10,[]),(15,[2])]),([(3,3,1),(2,4,1),(2,5,6)],[7,0,1,2,3,8,4],[(0,[0]),(0,[0,1]),(1,[0,2]),(1,[0,1,2]),(2,[]),(3,[0,2]),(5,[0,2]),(6,[]),(6,[1]),(9,[]),(10,[2]),(15,[])]),([(0,4,0),(1,4,0),(2,7,6)],[8,0,1,2,3,5],[(0,[0,1,2]),(1,[0,1,2]),(3,[]),(8,[]),(15,[])]),([(0,4,0),(3,4,1),(1,6,7)],[0,8,1,2,3,5],[(0,[0,1,2]),(1,[0,1,2]),(3,[]),(5,[]),(11,[0]),(12,[1]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q244 : ck242 [172,173,174,175,176,177,178,179] d244 = true := by decide +kernel
private def lv_0_0_7_21 : List NodeSpec := (d242 ++ (d243 ++ d244))

private theorem ok_0_0_7_21 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_21 := by
  have go {ids ds} (h : ck242 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q242) (levelOK_append (go q243) (go q244)))
private def lv_0_0_7_22 : List NodeSpec := [([(1, 4, 0), (2, 4, 1), (2, 6, 7)], [0, 8, 1, 2, 3, 5], [(0, [0, 1, 2]), (1, [0, 1, 2]), (3, []), (5, []), (8, [1]), (10, [0]), (15, [])]), ([(0, 4, 1), (1, 4, 1), (2, 7, 6)], [8, 0, 1, 2, 3, 5], [(0, [0, 1, 2]), (1, [0, 1, 2]), (3, []), (10, []), (15, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_0_0_7_22 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_22 :=
  levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK [180,181,182,183,184,185,186,187] ok_0_0_6)
    (by decide +kernel : levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev [180,181,182,183,184,185,186,187] lv_0_0_6) 7 lv_0_0_7_22 = true)
private def lv_0_0_7 : List NodeSpec := ((((lv_0_0_7_0 ++ lv_0_0_7_1) ++ (lv_0_0_7_2 ++ (lv_0_0_7_3 ++ lv_0_0_7_4))) ++ ((lv_0_0_7_5 ++ (lv_0_0_7_6 ++ lv_0_0_7_7)) ++ (lv_0_0_7_8 ++ (lv_0_0_7_9 ++ lv_0_0_7_10)))) ++ (((lv_0_0_7_11 ++ (lv_0_0_7_12 ++ lv_0_0_7_13)) ++ (lv_0_0_7_14 ++ (lv_0_0_7_15 ++ lv_0_0_7_16))) ++ ((lv_0_0_7_17 ++ (lv_0_0_7_18 ++ lv_0_0_7_19)) ++ (lv_0_0_7_20 ++ (lv_0_0_7_21 ++ lv_0_0_7_22)))))
private theorem ok_0_0_7 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7 := (levelOK_append (levelOK_append (levelOK_append (levelOK_append ok_0_0_7_0 ok_0_0_7_1) (levelOK_append ok_0_0_7_2 (levelOK_append ok_0_0_7_3 ok_0_0_7_4))) (levelOK_append (levelOK_append ok_0_0_7_5 (levelOK_append ok_0_0_7_6 ok_0_0_7_7)) (levelOK_append ok_0_0_7_8 (levelOK_append ok_0_0_7_9 ok_0_0_7_10)))) (levelOK_append (levelOK_append (levelOK_append ok_0_0_7_11 (levelOK_append ok_0_0_7_12 ok_0_0_7_13)) (levelOK_append ok_0_0_7_14 (levelOK_append ok_0_0_7_15 ok_0_0_7_16))) (levelOK_append (levelOK_append ok_0_0_7_17 (levelOK_append ok_0_0_7_18 ok_0_0_7_19)) (levelOK_append ok_0_0_7_20 (levelOK_append ok_0_0_7_21 ok_0_0_7_22)))))
private def ck245 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_7) 8
private def d245 : List NodeSpec := [([(0,1,0),(2,0,6)],[7,0,1,2,3,4,5],[(0,[]),(0,[0]),(0,[0,1]),(1,[]),(1,[0,1]),(3,[]),(5,[]),(6,[]),(7,[]),(8,[]),(10,[]),(12,[])]),([(0,1,0),(2,0,6)],[7,6,1,2,3,4,5],[(0,[]),(0,[0]),(0,[0,1]),(1,[0,1]),(10,[]),(11,[])]),([(0,1,0),(2,1,6)],[7,0,1,2,3,4,5],[(0,[]),(0,[0]),(0,[0,1]),(1,[]),(1,[0,1]),(3,[]),(5,[]),(6,[]),(7,[]),(8,[]),(10,[]),(11,[])]),([(0,1,0),(2,1,6)],[7,6,0,2,3,4,5],[(0,[]),(0,[0]),(0,[0,1]),(1,[0,1]),(8,[]),(11,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q245 : ck245 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] d245 = true := by decide +kernel
private def d246 : List NodeSpec := [([(0,1,0),(1,1,0)],[6,1,7,2,3,4,5],[(0,[0,1]),(1,[0,1]),(8,[]),(10,[]),(11,[])]),([(0,1,0),(1,1,0)],[6,0,7,2,3,4,5],[(0,[0,1]),(1,[0,1]),(8,[]),(10,[]),(11,[]),(12,[])]),([(0,1,0),(1,2,6)],[0,1,7,3,4,5],[(0,[0,1]),(1,[0]),(4,[]),(11,[]),(12,[]),(15,[]),(16,[])]),([(0,1,0),(1,2,6)],[6,0,1,7,3,4,5],[(0,[0,1]),(1,[]),(1,[0]),(4,[0]),(9,[]),(11,[]),(12,[]),(18,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q246 : ck245 [16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41] d246 = true := by decide +kernel
private def d247 : List NodeSpec := [([(0,1,0),(1,3,6)],[0,1,2,7,4,5],[(0,[0,1]),(1,[0,1]),(6,[]),(11,[]),(12,[]),(15,[]),(16,[])]),([(0,1,0),(1,3,6)],[6,0,1,2,7,4,5],[(0,[0,1]),(1,[0,1]),(6,[0]),(7,[]),(11,[]),(12,[])]),([(0,1,0),(1,3,6)],[6,0,1,2,3,7,4,5],[(0,[0]),(0,[0,1]),(1,[0]),(1,[0,1]),(3,[0]),(5,[0]),(6,[]),(6,[0]),(7,[]),(7,[0]),(11,[]),(12,[]),(20,[])]),([(0,1,0),(2,3,6)],[7,0,1,2,4,5],[(0,[0,1]),(1,[0,1]),(7,[]),(11,[]),(12,[]),(15,[]),(16,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q247 : ck245 [30,31,42,43,44,45,46,47,48,49,50,51,52,53,54,55] d247 = true := by decide +kernel
private def lv_0_0_8_0 : List NodeSpec := (d245 ++ (d246 ++ d247))

private theorem ok_0_0_8_0 : LevelOK rd_0_0 (subGoal 0 0) 8 lv_0_0_8_0 := by
  have go {ids ds} (h : ck245 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 8 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_7) h
  exact (levelOK_append (go q245) (levelOK_append (go q246) (go q247)))
private def ck248 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_7) 8
private def d248 : List NodeSpec := [([(0,1,0),(2,3,6)],[7,6,0,1,2,4,5],[(0,[0,1]),(1,[0,1]),(6,[]),(7,[0]),(11,[]),(12,[])]),([(0,1,0),(2,3,6)],[7,6,0,1,2,3,4,5],[(0,[0]),(0,[0,1]),(1,[0]),(1,[0,1]),(3,[0]),(5,[0]),(6,[]),(6,[0]),(7,[]),(7,[0]),(11,[]),(12,[]),(19,[])]),([(0,1,0),(1,4,6)],[0,1,2,3,7,5],[(0,[0,1]),(1,[0,1]),(3,[]),(11,[]),(12,[]),(15,[]),(16,[])]),([(0,1,0),(1,4,6)],[6,0,1,2,3,7,5],[(0,[0,1]),(1,[0,1]),(3,[0]),(5,[]),(11,[]),(12,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q248 : ck248 [32,33,34,42,43,50,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72] d248 = true := by decide +kernel
private def d249 : List NodeSpec := [([(0,1,0),(1,4,6)],[6,0,1,2,3,4,7,5],[(0,[0]),(0,[0,1]),(1,[0]),(1,[0,1]),(3,[]),(3,[0]),(5,[]),(5,[0]),(6,[0]),(7,[0]),(11,[]),(12,[]),(19,[])]),([(0,1,0),(2,4,6)],[7,0,1,2,3,5],[(0,[0,1]),(1,[0,1]),(5,[]),(11,[]),(12,[]),(15,[]),(16,[])]),([(0,1,0),(2,4,6)],[7,6,0,1,2,3,5],[(0,[0,1]),(1,[0,1]),(3,[]),(5,[0]),(11,[]),(12,[])]),([(0,1,0),(2,4,6)],[7,6,0,1,2,3,4,5],[(0,[0]),(0,[0,1]),(1,[0]),(1,[0,1]),(3,[]),(3,[0]),(5,[]),(5,[0]),(6,[0]),(7,[0]),(11,[]),(12,[]),(20,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q249 : ck248 [35,36,37,44,45,46,51,52,59,60,61,64,65,69,73,74,75,76,77,78,79,80,81] d249 = true := by decide +kernel
private def d250 : List NodeSpec := [([(0,1,0),(0,4,3)],[6,0,1,2,7,3,4,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(5,[]),(5,[0]),(6,[]),(6,[0]),(7,[]),(7,[0]),(8,[]),(10,[]),(11,[]),(12,[])]),([(0,1,0),(1,4,3)],[6,0,1,2,3,4,7,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(5,[]),(5,[0]),(6,[]),(6,[0]),(7,[]),(8,[]),(10,[]),(11,[]),(12,[]),(16,[])]),([(0,1,0),(2,4,3)],[7,6,0,1,2,3,4,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(5,[]),(5,[0]),(6,[]),(6,[0]),(7,[]),(8,[]),(10,[]),(11,[]),(12,[])]),([(0,1,0),(3,4,3)],[7,6,0,1,2,3,4,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(5,[]),(5,[0]),(6,[]),(6,[0]),(7,[]),(7,[0]),(8,[]),(10,[]),(11,[]),(12,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q250 : ck248 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,17,18,19,20,22,23,24,25,26,27,28,29,38,39,40,41,53,54,66,67,73,74,79,80,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98] d250 = true := by decide +kernel
private def lv_0_0_8_1 : List NodeSpec := (d248 ++ (d249 ++ d250))

private theorem ok_0_0_8_1 : LevelOK rd_0_0 (subGoal 0 0) 8 lv_0_0_8_1 := by
  have go {ids ds} (h : ck248 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 8 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_7) h
  exact (levelOK_append (go q248) (levelOK_append (go q249) (go q250)))
private def ck251 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_7) 8
private def d251 : List NodeSpec := [([(0,1,0),(2,5,6)],[7,0,1,2,3,4],[(0,[0]),(1,[0,1]),(2,[]),(11,[]),(12,[]),(15,[]),(16,[])]),([(0,1,0),(2,5,6)],[7,6,0,1,2,3,4],[(0,[]),(0,[0]),(1,[0,1]),(2,[0]),(9,[]),(11,[]),(12,[]),(17,[])]),([(1,1,0),(2,1,0)],[7,1,6,2,3,4,5],[(0,[]),(0,[0]),(0,[1]),(0,[0,1]),(1,[0,1]),(8,[]),(10,[])]),([(1,1,0),(3,1,0)],[7,0,6,2,3,4,5],[(0,[]),(0,[0]),(0,[1]),(0,[0,1]),(1,[0,1]),(8,[]),(10,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q251 : ck251 [49,55,62,68,72,75,78,81,85,86,89,90,93,94,97,98,99,100,101,102,103,104,105,106] d251 = true := by decide +kernel
private def d252 : List NodeSpec := [([(1,1,0),(3,2,6)],[7,0,1,3,4,5],[(0,[0,1]),(1,[0]),(4,[]),(8,[]),(10,[]),(15,[]),(16,[])]),([(1,1,0),(3,2,6)],[7,0,1,6,3,4,5],[(0,[0,1]),(1,[]),(1,[0]),(4,[0]),(8,[]),(9,[]),(10,[]),(13,[])]),([(1,1,0),(0,3,6)],[0,1,7,2,4,5],[(0,[0,1]),(1,[0,1]),(7,[]),(8,[]),(10,[]),(15,[]),(16,[])]),([(1,1,0),(0,3,6)],[0,1,7,6,2,4,5],[(0,[0,1]),(1,[0,1]),(6,[]),(7,[0]),(8,[]),(10,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q252 : ck251 [107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130] d252 = true := by decide +kernel
private def d253 : List NodeSpec := [([(1,1,0),(0,3,6)],[0,1,7,6,2,3,4,5],[(0,[0]),(0,[0,1]),(1,[0]),(1,[0,1]),(3,[0]),(5,[0]),(6,[]),(6,[0]),(7,[]),(7,[0]),(8,[]),(10,[]),(19,[])]),([(1,1,0),(3,3,6)],[7,0,1,2,4,5],[(0,[0,1]),(1,[0,1]),(6,[]),(8,[]),(10,[]),(15,[]),(16,[])]),([(1,1,0),(3,3,6)],[7,0,1,6,2,4,5],[(0,[0,1]),(1,[0,1]),(6,[0]),(7,[]),(8,[]),(10,[])]),([(1,1,0),(3,3,6)],[7,0,1,6,2,3,4,5],[(0,[0]),(0,[0,1]),(1,[0]),(1,[0,1]),(3,[0]),(5,[0]),(6,[]),(6,[0]),(7,[]),(7,[0]),(8,[]),(10,[]),(20,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q253 : ck251 [112,113,114,123,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149] d253 = true := by decide +kernel
private def lv_0_0_8_2 : List NodeSpec := (d251 ++ (d252 ++ d253))

private theorem ok_0_0_8_2 : LevelOK rd_0_0 (subGoal 0 0) 8 lv_0_0_8_2 := by
  have go {ids ds} (h : ck251 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 8 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_7) h
  exact (levelOK_append (go q251) (levelOK_append (go q252) (go q253)))
private def ck254 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_7) 8
private def d254 : List NodeSpec := [([(1,1,0),(0,4,6)],[0,1,7,2,3,5],[(0,[0,1]),(1,[0,1]),(5,[]),(8,[]),(10,[]),(15,[]),(16,[])]),([(1,1,0),(0,4,6)],[0,1,7,6,2,3,5],[(0,[0,1]),(1,[0,1]),(3,[]),(5,[0]),(8,[]),(10,[])]),([(1,1,0),(0,4,6)],[0,1,7,6,2,3,4,5],[(0,[0]),(0,[0,1]),(1,[0]),(1,[0,1]),(3,[]),(3,[0]),(5,[]),(5,[0]),(6,[0]),(7,[0]),(8,[]),(10,[]),(20,[])]),([(1,1,0),(3,4,6)],[7,0,1,2,3,5],[(0,[0,1]),(1,[0,1]),(3,[]),(8,[]),(10,[]),(15,[]),(16,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q254 : ck254 [115,116,126,127,131,132,139,140,144,150,151,152,153,154,155,156] d254 = true := by decide +kernel
private def d255 : List NodeSpec := [([(1,1,0),(3,4,6)],[7,0,1,6,2,3,5],[(0,[0,1]),(1,[0,1]),(3,[0]),(5,[]),(8,[]),(10,[])]),([(1,1,0),(3,4,6)],[7,0,1,6,2,3,4,5],[(0,[0]),(0,[0,1]),(1,[0]),(1,[0,1]),(3,[]),(3,[0]),(5,[]),(5,[0]),(6,[0]),(7,[0]),(8,[]),(10,[]),(19,[])]),([(1,1,0),(0,4,3)],[0,1,6,2,7,3,4,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(5,[]),(5,[0]),(6,[]),(6,[0]),(7,[]),(7,[0]),(8,[]),(10,[]),(11,[]),(12,[]),(15,[])]),([(1,1,0),(1,4,3)],[0,1,6,2,3,4,7,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(5,[]),(5,[0]),(6,[]),(6,[0]),(7,[]),(8,[]),(10,[]),(11,[]),(12,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q255 : ck254 [0,1,8,9,17,18,22,23,99,100,103,104,107,108,117,118,119,120,128,129,133,134,141,142,145,146,147,150,154,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171] d255 = true := by decide +kernel
private def d256 : List NodeSpec := [([(1,1,0),(2,4,3)],[7,0,1,6,2,3,4,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(5,[]),(5,[0]),(6,[]),(6,[0]),(7,[]),(8,[]),(10,[]),(11,[]),(12,[])]),([(1,1,0),(3,4,3)],[7,0,1,6,2,3,4,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(5,[]),(5,[0]),(6,[]),(6,[0]),(7,[]),(7,[0]),(8,[]),(10,[]),(11,[]),(12,[])]),([(1,1,0),(0,5,6)],[0,1,7,2,3,4],[(0,[0]),(1,[0,1]),(2,[]),(8,[]),(10,[]),(15,[]),(16,[])]),([(1,1,0),(0,5,6)],[0,1,7,6,2,3,4],[(0,[]),(0,[0]),(1,[0,1]),(2,[0]),(8,[]),(9,[]),(10,[]),(14,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q256 : ck254 [2,3,10,11,19,20,24,25,101,102,105,106,109,110,121,122,130,135,136,143,148,149,153,155,156,159,161,162,166,167,170,171,172,173,174,175,176,177,178,179] d256 = true := by decide +kernel
private def lv_0_0_8_3 : List NodeSpec := (d254 ++ (d255 ++ d256))

private theorem ok_0_0_8_3 : LevelOK rd_0_0 (subGoal 0 0) 8 lv_0_0_8_3 := by
  have go {ids ds} (h : ck254 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 8 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_7) h
  exact (levelOK_append (go q254) (levelOK_append (go q255) (go q256)))
private def ck257 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_7) 8
private def d257 : List NodeSpec := [([(2,1,0),(1,0,6)],[0,1,7,2,3,4,5],[(0,[]),(0,[0]),(0,[0,1]),(1,[]),(1,[0,1]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[]),(10,[])]),([(2,1,0),(2,1,6)],[7,0,1,2,3,4,5],[(0,[]),(0,[0]),(0,[0,1]),(1,[]),(1,[0,1]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[]),(10,[]),(11,[]),(12,[])]),([(2,1,0),(3,1,0)],[7,6,1,2,3,4,5],[(0,[0,1]),(1,[0,1]),(8,[]),(10,[]),(11,[])]),([(2,1,0),(3,1,0)],[7,6,0,2,3,4,5],[(0,[0,1]),(1,[0,1]),(8,[]),(10,[]),(11,[]),(12,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q257 : ck257 [16,21,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195] d257 = true := by decide +kernel
private def d258 : List NodeSpec := [([(2,1,0),(0,4,3)],[6,0,1,2,7,3,4,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(5,[]),(5,[0]),(6,[]),(6,[0]),(7,[]),(8,[]),(10,[]),(11,[]),(12,[]),(16,[])]),([(2,1,0),(1,4,3)],[6,0,1,2,3,4,7,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(6,[]),(6,[0]),(8,[]),(10,[]),(11,[]),(12,[]),(16,[])]),([(2,1,0),(2,4,3)],[7,6,0,1,2,3,4,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(5,[]),(5,[0]),(6,[]),(6,[0]),(8,[]),(10,[]),(11,[]),(12,[]),(16,[])]),([(2,1,0),(3,4,3)],[7,6,0,1,2,3,4,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(6,[]),(6,[0]),(7,[]),(8,[]),(10,[]),(11,[]),(12,[]),(16,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q258 : ck257 [8,12,13,14,15,99,100,101,102,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196] d258 = true := by decide +kernel
private def d259 : List NodeSpec := [([(3,1,0),(0,4,3)],[6,0,1,2,7,3,4,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(5,[]),(5,[0]),(6,[]),(6,[0]),(7,[]),(8,[]),(10,[]),(11,[]),(12,[]),(15,[])]),([(3,1,0),(1,4,3)],[6,0,1,2,3,4,7,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(6,[]),(6,[0]),(8,[]),(10,[]),(11,[]),(12,[]),(15,[])]),([(3,1,0),(2,4,3)],[7,6,0,1,2,3,4,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(5,[]),(5,[0]),(6,[]),(6,[0]),(8,[]),(10,[]),(11,[]),(12,[]),(15,[])]),([(3,1,0),(3,4,3)],[7,6,0,1,2,3,4,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(6,[]),(6,[0]),(7,[]),(8,[]),(10,[]),(11,[]),(12,[]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q259 : ck257 [0,4,5,6,7,103,104,105,106,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,197] d259 = true := by decide +kernel
private def lv_0_0_8_4 : List NodeSpec := (d257 ++ (d258 ++ d259))

private theorem ok_0_0_8_4 : LevelOK rd_0_0 (subGoal 0 0) 8 lv_0_0_8_4 := by
  have go {ids ds} (h : ck257 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 8 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_7) h
  exact (levelOK_append (go q257) (levelOK_append (go q258) (go q259)))
private def ck260 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_7) 8
private def d260 : List NodeSpec := [([(0,3,0),(1,1,6)],[0,1,7,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(3,[]),(5,[]),(6,[]),(6,[1]),(7,[]),(8,[]),(10,[]),(12,[]),(15,[])]),([(0,3,0),(2,1,6)],[7,0,1,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(3,[]),(5,[]),(6,[]),(6,[1]),(7,[]),(8,[]),(11,[]),(12,[]),(15,[]),(16,[])]),([(0,3,0),(1,2,6)],[0,1,7,3,4,5],[(0,[0,1]),(1,[0]),(4,[]),(6,[1]),(7,[]),(12,[]),(16,[])]),([(0,3,0),(1,3,0)],[6,0,1,2,7,4,5],[(0,[0,1]),(1,[0,1]),(6,[]),(7,[]),(8,[]),(12,[]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q260 : ck260 [198,199,200,201,202,203] d260 = true := by decide +kernel
private def d261 : List NodeSpec := [([(0,3,0),(3,3,1)],[7,6,0,1,2,4,5],[(0,[0,1]),(1,[0,1]),(6,[]),(7,[]),(8,[]),(10,[]),(11,[0]),(12,[1]),(15,[])]),([(0,3,0),(1,4,0)],[6,0,1,2,3,4,7,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(5,[0]),(6,[]),(6,[1]),(7,[]),(7,[1]),(8,[]),(15,[])]),([(0,3,0),(2,4,0)],[7,6,0,1,2,3,4,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(5,[]),(5,[0]),(6,[]),(6,[1]),(7,[]),(7,[1]),(8,[]),(15,[])]),([(0,3,0),(0,4,1)],[6,0,7,1,2,3,4,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(5,[]),(5,[0]),(6,[]),(6,[1]),(7,[]),(7,[1]),(8,[]),(10,[]),(11,[]),(11,[0]),(12,[]),(12,[1]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q261 : ck260 [199,200,201,204,205,206,207,208] d261 = true := by decide +kernel
private def d262 : List NodeSpec := [([(0,3,0),(3,4,1)],[7,6,0,1,2,3,4,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(5,[0]),(6,[]),(6,[1]),(7,[]),(7,[1]),(8,[]),(10,[]),(11,[]),(11,[0]),(12,[]),(12,[1]),(15,[])]),([(1,3,0),(2,3,1)],[7,0,1,2,6,4,5],[(0,[0,1]),(1,[0,1]),(6,[]),(7,[]),(8,[1]),(10,[0]),(11,[]),(12,[]),(15,[])]),([(1,3,0),(0,6,1)],[0,7,1,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(3,[]),(5,[]),(6,[]),(7,[]),(7,[1]),(8,[]),(10,[]),(11,[]),(15,[])]),([(1,3,0),(2,6,1)],[7,0,1,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(3,[]),(5,[]),(6,[]),(7,[]),(7,[1]),(8,[]),(10,[]),(11,[]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q262 : ck260 [198,202,209,210,211,212] d262 = true := by decide +kernel
private def lv_0_0_8_5 : List NodeSpec := (d260 ++ (d261 ++ d262))

private theorem ok_0_0_8_5 : LevelOK rd_0_0 (subGoal 0 0) 8 lv_0_0_8_5 := by
  have go {ids ds} (h : ck260 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 8 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_7) h
  exact (levelOK_append (go q260) (levelOK_append (go q261) (go q262)))
private def ck263 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_7) 8
private def d263 : List NodeSpec := [([(1,3,0),(0,4,0)],[7,0,1,2,3,6,4,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(5,[]),(5,[0]),(6,[]),(6,[1]),(7,[1]),(8,[]),(15,[])]),([(1,3,0),(3,4,0)],[7,0,1,2,3,6,4,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(5,[0]),(6,[]),(6,[1]),(7,[1]),(8,[]),(15,[])]),([(1,3,0),(1,4,1)],[0,1,2,3,6,4,7,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(5,[0]),(6,[]),(6,[1]),(7,[1]),(8,[]),(8,[1]),(10,[]),(10,[0]),(11,[]),(12,[]),(15,[])]),([(1,3,0),(2,4,1)],[7,0,1,2,3,6,4,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(5,[]),(5,[0]),(6,[]),(6,[1]),(7,[1]),(8,[]),(8,[1]),(10,[]),(10,[0]),(11,[]),(12,[]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q263 : ck263 [212,213,214,215,216,217,218,219,220,221,222] d263 = true := by decide +kernel
private def d264 : List NodeSpec := [([(1,3,0),(0,5,6)],[0,1,2,3,7,4],[(0,[0]),(1,[0,1]),(2,[]),(6,[]),(8,[]),(15,[])]),([(2,3,0),(1,1,6)],[0,1,7,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(3,[]),(5,[]),(6,[]),(6,[1]),(7,[]),(8,[]),(10,[]),(11,[]),(15,[])]),([(2,3,0),(2,1,6)],[7,0,1,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(2,[]),(3,[]),(5,[]),(6,[]),(6,[1]),(7,[]),(8,[]),(10,[]),(11,[]),(15,[])]),([(2,3,0),(3,3,0)],[7,6,0,1,2,4,5],[(0,[0,1]),(1,[0,1]),(6,[]),(7,[]),(8,[]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q264 : ck263 [203,215,217,219,222] d264 = true := by decide +kernel
private def d265 : List NodeSpec := [([(2,3,0),(1,3,1)],[6,0,1,2,7,4,5],[(0,[0,1]),(1,[0,1]),(6,[]),(7,[]),(8,[1]),(10,[0]),(11,[]),(12,[]),(15,[])]),([(2,3,0),(0,4,0)],[6,7,0,1,2,3,4,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(5,[]),(5,[0]),(6,[]),(6,[1]),(7,[]),(7,[1]),(8,[]),(15,[])]),([(2,3,0),(3,4,0)],[7,6,0,1,2,3,4,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(5,[0]),(6,[]),(6,[1]),(7,[]),(7,[1]),(8,[]),(15,[])]),([(2,3,0),(1,4,1)],[6,0,1,2,3,4,7,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(5,[0]),(6,[]),(6,[1]),(7,[]),(7,[1]),(8,[]),(8,[1]),(10,[]),(10,[0]),(11,[]),(12,[]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q265 : ck263 [204,214,216,223,224] d265 = true := by decide +kernel
private def lv_0_0_8_6 : List NodeSpec := (d263 ++ (d264 ++ d265))

private theorem ok_0_0_8_6 : LevelOK rd_0_0 (subGoal 0 0) 8 lv_0_0_8_6 := by
  have go {ids ds} (h : ck263 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 8 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_7) h
  exact (levelOK_append (go q263) (levelOK_append (go q264) (go q265)))
private def ck266 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_7) 8
private def d266 : List NodeSpec := [([(2,3,0),(2,4,1)],[7,6,0,1,2,3,4,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(5,[]),(5,[0]),(6,[]),(6,[1]),(7,[]),(7,[1]),(8,[]),(8,[1]),(10,[]),(10,[0]),(11,[]),(12,[]),(15,[])]),([(3,3,0),(1,1,6)],[0,1,7,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(7,[1]),(8,[]),(10,[]),(12,[]),(15,[])]),([(3,3,0),(2,1,6)],[0,7,1,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(3,[]),(5,[]),(6,[]),(7,[]),(7,[1]),(8,[]),(11,[]),(12,[]),(15,[])]),([(3,3,0),(0,3,1)],[6,0,7,1,2,4,5],[(0,[0,1]),(1,[0,1]),(6,[]),(7,[]),(8,[]),(10,[]),(11,[0]),(12,[1]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q266 : ck266 [211,225,226] d266 = true := by decide +kernel
private def d267 : List NodeSpec := [([(3,3,0),(1,4,0)],[6,0,1,2,3,4,7,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(5,[0]),(6,[]),(6,[1]),(7,[1]),(8,[]),(15,[])]),([(3,3,0),(2,4,0)],[6,7,0,1,2,3,4,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(5,[]),(5,[0]),(6,[]),(6,[1]),(7,[1]),(8,[]),(15,[])]),([(3,3,0),(0,4,1)],[6,0,7,1,2,3,4,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(5,[]),(5,[0]),(6,[]),(6,[1]),(7,[1]),(8,[]),(10,[]),(11,[]),(11,[0]),(12,[]),(12,[1]),(15,[])]),([(3,3,0),(3,4,1)],[7,6,0,1,2,3,4,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(5,[0]),(6,[]),(6,[1]),(7,[1]),(8,[]),(10,[]),(11,[]),(11,[0]),(12,[]),(12,[1]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q267 : ck266 [205,207,227,228,229,230] d267 = true := by decide +kernel
private def d268 : List NodeSpec := [([(0,3,1),(1,6,0)],[0,1,7,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(2,[]),(3,[]),(5,[]),(6,[]),(6,[1]),(7,[]),(8,[]),(10,[]),(11,[]),(15,[])]),([(0,3,1),(3,6,0)],[7,0,1,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(3,[]),(5,[]),(6,[]),(6,[1]),(7,[]),(8,[]),(10,[]),(11,[]),(12,[]),(15,[])]),([(0,3,1),(1,3,1)],[0,6,1,2,7,4,5],[(0,[0,1]),(1,[0,1]),(6,[]),(7,[]),(10,[]),(15,[])]),([(0,3,1),(0,4,0)],[7,0,6,1,2,3,4,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(5,[]),(5,[0]),(6,[]),(6,[1]),(7,[]),(7,[1]),(8,[]),(10,[]),(11,[]),(11,[1]),(12,[]),(12,[0]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q268 : ck266 [231,232,233] d268 = true := by decide +kernel
private def lv_0_0_8_7 : List NodeSpec := (d266 ++ (d267 ++ d268))

private theorem ok_0_0_8_7 : LevelOK rd_0_0 (subGoal 0 0) 8 lv_0_0_8_7 := by
  have go {ids ds} (h : ck266 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 8 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_7) h
  exact (levelOK_append (go q266) (levelOK_append (go q267) (go q268)))
private def ck269 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_7) 8
private def d269 : List NodeSpec := [([(0,3,1),(3,4,0)],[7,0,6,1,2,3,4,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(5,[0]),(6,[]),(6,[1]),(7,[]),(7,[1]),(8,[]),(10,[]),(11,[]),(11,[1]),(12,[]),(12,[0]),(15,[])]),([(0,3,1),(1,4,1)],[0,6,1,2,3,4,7,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(5,[0]),(6,[]),(6,[1]),(7,[]),(7,[1]),(10,[]),(15,[])]),([(0,3,1),(2,4,1)],[7,0,6,1,2,3,4,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(5,[]),(5,[0]),(6,[]),(6,[1]),(7,[]),(7,[1]),(10,[]),(11,[]),(15,[])]),([(1,3,1),(0,6,0)],[7,0,1,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(7,[1]),(8,[]),(10,[]),(11,[]),(12,[]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q269 : ck269 [234,235,236,237] d269 = true := by decide +kernel
private def d270 : List NodeSpec := [([(1,3,1),(2,6,0)],[7,0,1,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(3,[]),(5,[]),(6,[]),(7,[]),(7,[1]),(8,[]),(10,[]),(11,[]),(15,[])]),([(1,3,1),(1,4,0)],[0,1,2,3,6,4,7,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(5,[0]),(6,[]),(6,[1]),(7,[1]),(8,[]),(8,[0]),(10,[]),(10,[1]),(11,[]),(12,[]),(15,[])]),([(1,3,1),(2,4,0)],[7,0,1,2,3,6,4,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(5,[]),(5,[0]),(6,[]),(6,[1]),(7,[1]),(8,[]),(8,[0]),(10,[]),(10,[1]),(11,[]),(12,[]),(15,[])]),([(1,3,1),(0,4,1)],[0,7,1,2,3,6,4,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(5,[]),(5,[0]),(6,[]),(6,[1]),(7,[1]),(10,[]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q270 : ck269 [238,239,240,241] d270 = true := by decide +kernel
private def d271 : List NodeSpec := [([(1,3,1),(3,4,1)],[7,0,1,2,3,6,4,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(5,[0]),(6,[]),(6,[1]),(7,[1]),(10,[]),(11,[]),(15,[])]),([(2,3,1),(1,0,6)],[0,7,1,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(3,[]),(5,[]),(6,[]),(6,[1]),(7,[]),(8,[]),(10,[]),(11,[]),(15,[])]),([(2,3,1),(2,0,6)],[7,0,1,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(3,[]),(5,[]),(6,[]),(6,[1]),(7,[]),(8,[]),(10,[]),(11,[]),(12,[]),(15,[])]),([(2,3,1),(1,2,6)],[0,1,7,3,4,5],[(0,[0,1]),(1,[0]),(4,[]),(6,[1]),(7,[]),(10,[]),(16,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q271 : ck269 [242,243,244,245,246,247] d271 = true := by decide +kernel
private def lv_0_0_8_8 : List NodeSpec := (d269 ++ (d270 ++ d271))

private theorem ok_0_0_8_8 : LevelOK rd_0_0 (subGoal 0 0) 8 lv_0_0_8_8 := by
  have go {ids ds} (h : ck269 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 8 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_7) h
  exact (levelOK_append (go q269) (levelOK_append (go q270) (go q271)))
private def ck272 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_7) 8
private def d272 : List NodeSpec := [([(2,3,1),(3,3,1)],[7,6,0,1,2,4,5],[(0,[0,1]),(1,[0,1]),(6,[]),(7,[]),(10,[]),(15,[])]),([(2,3,1),(1,4,0)],[6,0,1,2,3,4,7,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(5,[0]),(6,[]),(6,[1]),(7,[]),(7,[1]),(8,[]),(8,[0]),(10,[]),(10,[1]),(11,[]),(12,[]),(15,[])]),([(2,3,1),(2,4,0)],[6,7,0,1,2,3,4,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(5,[]),(5,[0]),(6,[]),(6,[1]),(7,[]),(7,[1]),(8,[]),(8,[0]),(10,[]),(10,[1]),(11,[]),(12,[]),(15,[])]),([(2,3,1),(0,4,1)],[6,0,7,1,2,3,4,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(5,[]),(5,[0]),(6,[]),(6,[1]),(7,[]),(7,[1]),(10,[]),(11,[]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q272 : ck272 [231,242,244,245,246,248,249,250,251] d272 = true := by decide +kernel
private def d273 : List NodeSpec := [([(2,3,1),(3,4,1)],[7,6,0,1,2,3,4,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(5,[0]),(6,[]),(6,[1]),(7,[]),(7,[1]),(10,[]),(15,[])]),([(3,3,1),(1,0,6)],[0,7,1,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(3,[]),(5,[]),(6,[]),(7,[]),(7,[1]),(8,[]),(10,[]),(11,[]),(15,[])]),([(3,3,1),(2,0,6)],[7,0,1,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(3,[]),(5,[]),(6,[]),(7,[]),(7,[1]),(8,[]),(10,[]),(11,[]),(12,[]),(15,[])]),([(3,3,1),(0,4,0)],[6,7,0,1,2,3,4,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(5,[]),(5,[0]),(6,[]),(6,[1]),(7,[1]),(8,[]),(10,[]),(11,[]),(11,[1]),(12,[]),(12,[0]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q273 : ck272 [241,247,252,253,254,255,256] d273 = true := by decide +kernel
private def d274 : List NodeSpec := [([(3,3,1),(3,4,0)],[7,6,0,1,2,3,4,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(5,[0]),(6,[]),(6,[1]),(7,[1]),(8,[]),(10,[]),(11,[]),(11,[1]),(12,[]),(12,[0]),(15,[])]),([(3,3,1),(1,4,1)],[6,0,1,2,3,4,7,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(5,[0]),(6,[]),(6,[1]),(7,[1]),(10,[]),(11,[]),(15,[])]),([(3,3,1),(2,4,1)],[6,7,0,1,2,3,4,5],[(0,[0]),(0,[1]),(0,[0,1]),(1,[0]),(1,[1]),(1,[0,1]),(3,[]),(3,[0]),(5,[]),(5,[0]),(6,[]),(6,[1]),(7,[1]),(10,[]),(15,[])]),([(3,3,1),(2,5,6)],[0,1,2,3,7,4],[(0,[0]),(1,[0,1]),(2,[]),(6,[]),(11,[]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q274 : ck272 [235,236,256,257,258,259,260,261] d274 = true := by decide +kernel
private def lv_0_0_8_9 : List NodeSpec := (d272 ++ (d273 ++ d274))

private theorem ok_0_0_8_9 : LevelOK rd_0_0 (subGoal 0 0) 8 lv_0_0_8_9 := by
  have go {ids ds} (h : ck272 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 8 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_7) h
  exact (levelOK_append (go q272) (levelOK_append (go q273) (go q274)))
private def ck275 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_7) 8
private def d275 : List NodeSpec := [([(0,4,0),(1,1,6)],[0,1,7,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(3,[]),(3,[1]),(5,[]),(6,[]),(7,[]),(8,[]),(10,[]),(12,[]),(15,[])]),([(0,4,0),(2,1,6)],[7,0,1,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(3,[]),(3,[1]),(5,[]),(6,[]),(7,[]),(8,[]),(11,[]),(12,[]),(15,[]),(16,[])]),([(0,4,0),(1,2,6)],[0,1,7,3,4,5],[(0,[0,1]),(1,[0]),(3,[1]),(4,[]),(5,[]),(12,[]),(16,[])]),([(0,4,0),(1,4,0)],[6,0,1,2,3,7,5],[(0,[0,1]),(1,[0,1]),(3,[]),(5,[]),(8,[]),(12,[]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q275 : ck275 [213,223,233,254,255,262] d275 = true := by decide +kernel
private def d276 : List NodeSpec := [([(0,4,0),(3,4,1)],[7,6,0,1,2,3,5],[(0,[0,1]),(1,[0,1]),(3,[]),(5,[]),(8,[]),(10,[]),(11,[0]),(12,[1]),(15,[])]),([(1,4,0),(2,4,1)],[7,0,1,2,3,6,5],[(0,[0,1]),(1,[0,1]),(3,[]),(5,[]),(8,[1]),(10,[0]),(11,[]),(12,[]),(15,[])]),([(1,4,0),(0,6,1)],[0,7,1,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(3,[]),(5,[]),(5,[1]),(6,[]),(7,[]),(8,[]),(10,[]),(11,[]),(15,[])]),([(1,4,0),(2,6,1)],[7,0,1,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(3,[]),(5,[]),(5,[1]),(6,[]),(7,[]),(8,[]),(10,[]),(11,[]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q276 : ck275 [249,263,264] d276 = true := by decide +kernel
private def d277 : List NodeSpec := [([(1,4,0),(0,5,6)],[0,1,2,3,4,7],[(0,[0]),(1,[0,1]),(2,[]),(3,[]),(8,[]),(15,[])]),([(2,4,0),(1,1,6)],[0,1,7,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(3,[]),(3,[1]),(5,[]),(6,[]),(7,[]),(8,[]),(10,[]),(11,[]),(15,[])]),([(2,4,0),(2,1,6)],[7,0,1,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(2,[]),(3,[]),(3,[1]),(5,[]),(6,[]),(7,[]),(8,[]),(10,[]),(11,[]),(15,[])]),([(2,4,0),(3,4,0)],[7,6,0,1,2,3,5],[(0,[0,1]),(1,[0,1]),(3,[]),(5,[]),(8,[]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q277 : ck275 [206,227,239,250,262] d277 = true := by decide +kernel
private def lv_0_0_8_10 : List NodeSpec := (d275 ++ (d276 ++ d277))

private theorem ok_0_0_8_10 : LevelOK rd_0_0 (subGoal 0 0) 8 lv_0_0_8_10 := by
  have go {ids ds} (h : ck275 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 8 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_7) h
  exact (levelOK_append (go q275) (levelOK_append (go q276) (go q277)))
private def ck278 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_7) 8
private def d278 : List NodeSpec := [([(2,4,0),(1,4,1)],[6,0,1,2,3,7,5],[(0,[0,1]),(1,[0,1]),(3,[]),(5,[]),(8,[1]),(10,[0]),(11,[]),(12,[]),(15,[])]),([(3,4,0),(1,1,6)],[0,1,7,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(3,[]),(4,[]),(5,[]),(5,[1]),(6,[]),(7,[]),(8,[]),(10,[]),(12,[]),(15,[])]),([(3,4,0),(2,1,6)],[0,7,1,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(3,[]),(5,[]),(5,[1]),(6,[]),(7,[]),(8,[]),(11,[]),(12,[]),(15,[])]),([(3,4,0),(0,4,1)],[6,0,7,1,2,3,5],[(0,[0,1]),(1,[0,1]),(3,[]),(5,[]),(8,[]),(10,[]),(11,[0]),(12,[1]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q278 : ck278 [263,264] d278 = true := by decide +kernel
private def d279 : List NodeSpec := [([(0,4,1),(1,6,0)],[0,1,7,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(2,[]),(3,[]),(3,[1]),(5,[]),(6,[]),(7,[]),(8,[]),(10,[]),(11,[]),(15,[])]),([(0,4,1),(3,6,0)],[7,0,1,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(3,[]),(3,[1]),(5,[]),(6,[]),(7,[]),(8,[]),(10,[]),(11,[]),(12,[]),(15,[])]),([(0,4,1),(1,4,1)],[0,6,1,2,3,7,5],[(0,[0,1]),(1,[0,1]),(3,[]),(5,[]),(10,[]),(15,[])]),([(1,4,1),(0,6,0)],[7,0,1,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(3,[]),(4,[]),(5,[]),(5,[1]),(6,[]),(7,[]),(8,[]),(10,[]),(11,[]),(12,[]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q279 : ck278 [265] d279 = true := by decide +kernel
private def d280 : List NodeSpec := [([(1,4,1),(2,6,0)],[7,0,1,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(3,[]),(5,[]),(5,[1]),(6,[]),(7,[]),(8,[]),(10,[]),(11,[]),(15,[])]),([(2,4,1),(1,0,6)],[0,7,1,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(3,[]),(3,[1]),(5,[]),(6,[]),(7,[]),(8,[]),(10,[]),(11,[]),(15,[])]),([(2,4,1),(2,0,6)],[7,0,1,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(3,[]),(3,[1]),(5,[]),(6,[]),(7,[]),(8,[]),(10,[]),(11,[]),(12,[]),(15,[])]),([(2,4,1),(1,2,6)],[0,1,7,3,4,5],[(0,[0,1]),(1,[0]),(3,[1]),(4,[]),(5,[]),(10,[]),(16,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q280 : ck278 [220,226,237,260] d280 = true := by decide +kernel
private def lv_0_0_8_11 : List NodeSpec := (d278 ++ (d279 ++ d280))

private theorem ok_0_0_8_11 : LevelOK rd_0_0 (subGoal 0 0) 8 lv_0_0_8_11 := by
  have go {ids ds} (h : ck278 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 8 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_7) h
  exact (levelOK_append (go q278) (levelOK_append (go q279) (go q280)))
private def ck281 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_7) 8
private def d281 : List NodeSpec := [([(2,4,1),(3,4,1)],[7,6,0,1,2,3,5],[(0,[0,1]),(1,[0,1]),(3,[]),(5,[]),(10,[]),(15,[])]),([(3,4,1),(1,0,6)],[0,7,1,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(3,[]),(5,[]),(5,[1]),(6,[]),(7,[]),(8,[]),(10,[]),(11,[]),(15,[])]),([(3,4,1),(2,0,6)],[7,0,1,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(3,[]),(5,[]),(5,[1]),(6,[]),(7,[]),(8,[]),(10,[]),(11,[]),(12,[]),(15,[])]),([(3,4,1),(2,5,6)],[0,1,2,3,4,7],[(0,[0]),(1,[0,1]),(2,[]),(3,[]),(11,[]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q281 : ck281 [210,230,243,252,265] d281 = true := by decide +kernel
private def d282 : List NodeSpec := [([(0,4,3),(1,6,0)],[0,1,2,3,7,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(2,[]),(3,[]),(3,[1]),(5,[]),(6,[]),(6,[1]),(7,[]),(8,[]),(10,[]),(11,[])]),([(0,4,3),(3,6,0)],[7,0,1,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(3,[]),(3,[1]),(5,[]),(6,[]),(6,[1]),(7,[]),(10,[]),(11,[]),(12,[])]),([(0,4,3),(1,6,1)],[0,1,2,3,7,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(3,[]),(3,[1]),(5,[]),(6,[]),(6,[1]),(7,[]),(8,[]),(10,[]),(12,[]),(16,[])]),([(0,4,3),(3,6,1)],[7,0,1,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(2,[]),(3,[]),(3,[1]),(5,[]),(6,[]),(6,[1]),(7,[]),(8,[]),(11,[]),(12,[]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q282 : ck281 [] d282 = true := by decide +kernel
private def d283 : List NodeSpec := [([(0,4,3),(1,4,3)],[0,1,2,6,7,5],[(0,[0,1]),(1,[0,1]),(3,[]),(5,[])]),([(1,4,3),(0,6,0)],[7,0,1,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(3,[]),(4,[]),(5,[]),(5,[1]),(6,[]),(10,[]),(11,[]),(12,[])]),([(1,4,3),(2,6,0)],[7,0,1,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(3,[]),(5,[]),(5,[1]),(6,[]),(8,[]),(10,[]),(11,[])]),([(1,4,3),(0,6,1)],[0,7,1,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(3,[]),(5,[]),(5,[1]),(6,[]),(8,[]),(11,[]),(12,[]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q283 : ck281 [84,165,196,197] d283 = true := by decide +kernel
private def lv_0_0_8_12 : List NodeSpec := (d281 ++ (d282 ++ d283))

private theorem ok_0_0_8_12 : LevelOK rd_0_0 (subGoal 0 0) 8 lv_0_0_8_12 := by
  have go {ids ds} (h : ck281 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 8 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_7) h
  exact (levelOK_append (go q281) (levelOK_append (go q282) (go q283)))
private def ck284 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_7) 8
private def d284 : List NodeSpec := [([(1,4,3),(2,6,1)],[7,0,1,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(3,[]),(4,[]),(5,[]),(5,[1]),(6,[]),(8,[]),(10,[]),(12,[]),(16,[])]),([(2,4,3),(1,0,6)],[0,7,1,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(3,[]),(3,[1]),(5,[]),(6,[]),(8,[]),(10,[]),(11,[])]),([(2,4,3),(2,0,6)],[7,0,1,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(3,[]),(3,[1]),(5,[]),(6,[]),(10,[]),(11,[]),(12,[])]),([(2,4,3),(1,1,6)],[0,1,7,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(3,[]),(3,[1]),(5,[]),(6,[]),(8,[]),(10,[]),(12,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q284 : ck284 [] d284 = true := by decide +kernel
private def d285 : List NodeSpec := [([(2,4,3),(2,1,6)],[0,7,1,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(3,[]),(3,[1]),(5,[]),(6,[]),(8,[]),(11,[]),(12,[])]),([(3,4,3),(1,0,6)],[0,7,1,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(3,[]),(5,[]),(5,[1]),(6,[]),(6,[1]),(7,[]),(8,[]),(10,[]),(11,[])]),([(3,4,3),(2,0,6)],[7,0,1,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(3,[]),(5,[]),(5,[1]),(6,[]),(6,[1]),(7,[]),(10,[]),(11,[]),(12,[])]),([(3,4,3),(1,1,6)],[0,1,7,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(3,[]),(5,[]),(5,[1]),(6,[]),(6,[1]),(7,[]),(8,[]),(10,[]),(12,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q285 : ck284 [] d285 = true := by decide +kernel
private def d286 : List NodeSpec := [([(3,4,3),(2,1,6)],[0,7,1,2,3,4,5],[(0,[]),(0,[0,1]),(1,[]),(1,[0,1]),(3,[]),(5,[]),(5,[1]),(6,[]),(6,[1]),(7,[]),(8,[]),(11,[]),(12,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q286 : ck284 [] d286 = true := by decide +kernel
private def lv_0_0_8_13 : List NodeSpec := (d284 ++ (d285 ++ d286))

private theorem ok_0_0_8_13 : LevelOK rd_0_0 (subGoal 0 0) 8 lv_0_0_8_13 := by
  have go {ids ds} (h : ck284 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 8 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_7) h
  exact (levelOK_append (go q284) (levelOK_append (go q285) (go q286)))
private def lv_0_0_8 : List NodeSpec := (((lv_0_0_8_0 ++ (lv_0_0_8_1 ++ lv_0_0_8_2)) ++ ((lv_0_0_8_3 ++ lv_0_0_8_4) ++ (lv_0_0_8_5 ++ lv_0_0_8_6))) ++ ((lv_0_0_8_7 ++ (lv_0_0_8_8 ++ lv_0_0_8_9)) ++ ((lv_0_0_8_10 ++ lv_0_0_8_11) ++ (lv_0_0_8_12 ++ lv_0_0_8_13))))
private theorem ok_0_0_8 : LevelOK rd_0_0 (subGoal 0 0) 8 lv_0_0_8 := (levelOK_append (levelOK_append (levelOK_append ok_0_0_8_0 (levelOK_append ok_0_0_8_1 ok_0_0_8_2)) (levelOK_append (levelOK_append ok_0_0_8_3 ok_0_0_8_4) (levelOK_append ok_0_0_8_5 ok_0_0_8_6))) (levelOK_append (levelOK_append ok_0_0_8_7 (levelOK_append ok_0_0_8_8 ok_0_0_8_9)) (levelOK_append (levelOK_append ok_0_0_8_10 ok_0_0_8_11) (levelOK_append ok_0_0_8_12 ok_0_0_8_13))))
private def ck287 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_8) 9
private def d287 : List NodeSpec := [([(0,1,0)],[6,0,1,2,3,4,5],[(0,[]),(0,[0]),(1,[]),(1,[0]),(3,[]),(5,[]),(6,[]),(7,[]),(11,[]),(12,[]),(15,[]),(16,[])]),([(1,1,0)],[0,1,6,2,3,4,5],[(0,[]),(0,[0]),(1,[]),(1,[0]),(3,[]),(5,[]),(6,[]),(7,[]),(8,[]),(10,[]),(15,[]),(16,[])]),([(2,1,0)],[6,0,1,2,3,4,5],[(0,[]),(0,[0]),(1,[]),(1,[0]),(3,[]),(5,[]),(6,[]),(7,[]),(8,[]),(11,[]),(15,[]),(16,[])]),([(3,1,0)],[6,0,1,2,3,4,5],[(0,[]),(0,[0]),(1,[]),(1,[0]),(3,[]),(5,[]),(6,[]),(7,[]),(10,[]),(12,[]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q287 : ck287 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59] d287 = true := by decide +kernel
private def d288 : List NodeSpec := [([(0,3,0)],[6,0,1,2,3,4,5],[(0,[]),(0,[0]),(1,[]),(1,[0]),(3,[]),(5,[]),(6,[]),(7,[]),(12,[]),(16,[])]),([(1,3,0)],[0,1,2,3,6,4,5],[(0,[]),(0,[0]),(1,[]),(1,[0]),(3,[]),(5,[]),(6,[]),(7,[]),(8,[]),(15,[])]),([(2,3,0)],[6,0,1,2,3,4,5],[(0,[]),(0,[0]),(1,[]),(1,[0]),(3,[]),(5,[]),(6,[]),(7,[]),(8,[]),(15,[])]),([(3,3,0)],[6,0,1,2,3,4,5],[(0,[]),(0,[0]),(1,[]),(1,[0]),(3,[]),(5,[]),(6,[]),(7,[]),(12,[]),(16,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q288 : ck287 [60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91] d288 = true := by decide +kernel
private def d289 : List NodeSpec := [([(0,3,1)],[0,6,1,2,3,4,5],[(0,[]),(0,[0]),(1,[]),(1,[0]),(3,[]),(5,[]),(6,[]),(7,[]),(11,[]),(15,[])]),([(1,3,1)],[0,1,2,3,6,4,5],[(0,[]),(0,[0]),(1,[]),(1,[0]),(3,[]),(5,[]),(6,[]),(7,[]),(10,[]),(16,[])]),([(2,3,1)],[6,0,1,2,3,4,5],[(0,[]),(0,[0]),(1,[]),(1,[0]),(3,[]),(5,[]),(6,[]),(7,[]),(10,[]),(16,[])]),([(3,3,1)],[6,0,1,2,3,4,5],[(0,[]),(0,[0]),(1,[]),(1,[0]),(3,[]),(5,[]),(6,[]),(7,[]),(11,[]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q289 : ck287 [64,69,80,87,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119] d289 = true := by decide +kernel
private def lv_0_0_9_0 : List NodeSpec := (d287 ++ (d288 ++ d289))

private theorem ok_0_0_9_0 : LevelOK rd_0_0 (subGoal 0 0) 9 lv_0_0_9_0 := by
  have go {ids ds} (h : ck287 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 9 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_8) h
  exact (levelOK_append (go q287) (levelOK_append (go q288) (go q289)))
private def ck290 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_8) 9
private def d290 : List NodeSpec := [([(0,4,0)],[6,0,1,2,3,4,5],[(0,[]),(0,[0]),(1,[]),(1,[0]),(3,[]),(5,[]),(6,[]),(7,[]),(12,[]),(16,[])]),([(1,4,0)],[0,1,2,3,4,6,5],[(0,[]),(0,[0]),(1,[]),(1,[0]),(3,[]),(5,[]),(6,[]),(7,[]),(8,[]),(15,[])]),([(2,4,0)],[6,0,1,2,3,4,5],[(0,[]),(0,[0]),(1,[]),(1,[0]),(3,[]),(5,[]),(6,[]),(7,[]),(8,[]),(15,[])]),([(3,4,0)],[6,0,1,2,3,4,5],[(0,[]),(0,[0]),(1,[]),(1,[0]),(3,[]),(5,[]),(6,[]),(7,[]),(12,[]),(16,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q290 : ck290 [65,66,72,73,81,82,88,89,95,96,101,102,109,110,115,116,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135] d290 = true := by decide +kernel
private def d291 : List NodeSpec := [([(0,4,1)],[0,6,1,2,3,4,5],[(0,[]),(0,[0]),(1,[]),(1,[0]),(3,[]),(5,[]),(6,[]),(7,[]),(11,[]),(15,[])]),([(1,4,1)],[0,1,2,3,4,6,5],[(0,[]),(0,[0]),(1,[]),(1,[0]),(3,[]),(5,[]),(6,[]),(7,[]),(10,[]),(16,[])]),([(2,4,1)],[6,0,1,2,3,4,5],[(0,[]),(0,[0]),(1,[]),(1,[0]),(3,[]),(5,[]),(6,[]),(7,[]),(10,[]),(16,[])]),([(3,4,1)],[6,0,1,2,3,4,5],[(0,[]),(0,[0]),(1,[]),(1,[0]),(3,[]),(5,[]),(6,[]),(7,[]),(11,[]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q291 : ck290 [67,68,74,75,83,84,90,91,97,98,103,104,111,112,117,118,124,125,132,135,136,137,138,139,140,141,142,143,144,145,146,147] d291 = true := by decide +kernel
private def d292 : List NodeSpec := [([(0,4,3)],[0,1,2,6,3,4,5],[(0,[]),(0,[0]),(1,[]),(1,[0]),(3,[]),(5,[]),(6,[]),(7,[])]),([(1,4,3)],[0,1,2,3,4,6,5],[(0,[]),(0,[0]),(1,[]),(1,[0]),(3,[]),(5,[]),(6,[])]),([(2,4,3)],[6,0,1,2,3,4,5],[(0,[]),(0,[0]),(1,[]),(1,[0]),(3,[]),(5,[]),(6,[])]),([(3,4,3)],[6,0,1,2,3,4,5],[(0,[]),(0,[0]),(1,[]),(1,[0]),(3,[]),(5,[]),(6,[]),(7,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q292 : ck290 [20,21,22,23,42,43,44,45,52,53,54,55,56,57,58,59,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164] d292 = true := by decide +kernel
private def lv_0_0_9_1 : List NodeSpec := (d290 ++ (d291 ++ d292))

private theorem ok_0_0_9_1 : LevelOK rd_0_0 (subGoal 0 0) 9 lv_0_0_9_1 := by
  have go {ids ds} (h : ck290 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 9 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_8) h
  exact (levelOK_append (go q290) (levelOK_append (go q291) (go q292)))
private def lv_0_0_9 : List NodeSpec := (lv_0_0_9_0 ++ lv_0_0_9_1)
private theorem ok_0_0_9 : LevelOK rd_0_0 (subGoal 0 0) 9 lv_0_0_9 := (levelOK_append ok_0_0_9_0 ok_0_0_9_1)
private def lv_0_0_10_0 : List NodeSpec := [([], [0, 1, 2, 3, 4, 5], [(0, []), (1, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_0_0_10_0 : LevelOK rd_0_0 (subGoal 0 0) 10 lv_0_0_10_0 :=
  levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] ok_0_0_9)
    (by decide +kernel : levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] lv_0_0_9) 10 lv_0_0_10_0 = true)
private def lv_0_0_10 : List NodeSpec := lv_0_0_10_0
private theorem ok_0_0_10 : LevelOK rd_0_0 (subGoal 0 0) 10 lv_0_0_10 := ok_0_0_10_0
private theorem lower_0_0 : Lower (freeVars 0 0) (subGoal 0 0) 11 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 10, 14), (inputs.getD 3 zero, 6, 14), (inputs.getD 4 zero, 6, 22), (inputs.getD 5 zero, 5, 37)]) ok_0_0_10 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube0_0

private theorem rootCertificate : Impossible target 10 inputs.toFinset := by
  have ht : subGoal 0 0 = target := by decide +kernel
  have hraw : (freeVars 0 0).toFinset = inputs.toFinset := by decide +kernel
  have hc : Impossible (subGoal 0 0) 10 (freeVars 0 0).toFinset :=
    impossible_of_top ok_0_0_10 List.mem_cons_self (by decide +kernel)
  simpa only [ht, hraw] using hc

theorem compactMain :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 targetFun s →
      ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧
        ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = targetFun x :=
  main_from_root rootCertificate

end PEqualNP.Outside.L_meta_39687_aux.Frontier

theorem PEqualNP.Outside.L_meta_39687 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372904 * 2 ^ 32 + 3939027080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372904 * 2 ^ 32 + 3939027080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  exact PEqualNP.Outside.L_meta_39687_aux.Frontier.compactMain
