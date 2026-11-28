import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_37945_aux.Upper

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open scoped BigOperators

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4277075680 * 2 ^ 32 + 4276812000)
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def witness : Circuit :=
  ⟨[⟨.or, [1, 0]⟩,
    ⟨.and, [1, 0]⟩,
    ⟨.or, [2, 7]⟩,
    ⟨.or, [3, 0]⟩,
    ⟨.and, [3, 8]⟩,
    ⟨.or, [4, 3]⟩,
    ⟨.and, [4, 9]⟩,
    ⟨.or, [12, 2]⟩,
    ⟨.and, [5, 11]⟩,
    ⟨.or, [14, 13]⟩,
    ⟨.and, [15, 6]⟩,
    ⟨.or, [16, 10]⟩], 17⟩

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

end PEqualNP.Outside.L_meta_37945_aux.Upper

namespace PEqualNP.Outside.L_meta_37945_aux.Frontier
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
def target : Sig := 0xfeeefee0feeaf8e0
def targetFun (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4277075680 * 2 ^ 32 + 4276812000) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
      Nat.testBit (4277075680 * 2 ^ 32 + 4276812000)
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
  [(inputs.getD 0 zero, 4, 5), (inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 1, 5), (inputs.getD 3 zero, 3, 11), (inputs.getD 4 zero, 1, 17), (inputs.getD 5 zero, 9, 41)]

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
  · exact PEqualNP.Outside.L_meta_37945_aux.Upper.bounded_replacement hs
  · by_cases hno : ∀ g ∈ C.gates, isNot g = false
    · exact ⟨C, no_not_monotone C hfan hno, hsz, heval⟩
    · exact False.elim (circuit_with_not_impossible root_imp root_ess C hfan (by omega) heval hno)

end PEqualNP.Outside.L_meta_37945_aux.Frontier

namespace PEqualNP.Outside.L_meta_37945_aux.Frontier
section Cube48_0

private def p_48_0 : Nat → Bits
  | 0 => mk128 0xadf1cf3e38fc74f3 0xadf1cf3e38fc74f3
  | 1 => mk128 0xcefe0fcfc0ff88fc 0xcefe0fcfc0ff88fc
  | 2 => mk128 0xf7fff7ffff1fff1f 0xf7fff7ffff1fff1f
  | 3 => mk128 0xf8fff80fffe00fe0 0xf8fff80fffe00fe0
  | 4 => mk128 0x0 0x0
  | 5 => mk128 0x0 0x0
  | _ => 0
private def q_48_0 : Nat → Bits
  | 0 => mk128 0x521c92460a256471 0x521c92460a256471
  | 1 => mk128 0x3125a41a444b28b4 0x3125a41a444b28b4
  | 2 => mk128 0x84000009010010a 0x84000009010010a
  | 3 => mk128 0x78906ad26824ec0 0x78906ad26824ec0
  | 4 => mk128 0x0 0x0
  | 5 => mk128 0x0 0x0
  | _ => 0
private theorem pp_48_0 : properPairs (subGoal 48 0) (asRow p_48_0) (asRow q_48_0) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_48_0 : List Decor := rawDecor (freeMask 48 0) p_48_0 q_48_0
private def sl_48_0 : List (Sig × Nat) := []
private theorem sl_48_0_ok : ∀ s ∈ sl_48_0, Slice (freeVars 48 0) (subGoal 48 0) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private def autos_48_0 : List (List Move) := [[], [swapRows 49], [swapRows 16], [swapRows 16, swapRows 49], [swapRows 48, swapRows 49], [swapRows 48]]
private theorem autos_48_0_ok : ∀ m ∈ autos_48_0, autoOK (subGoal 48 0) m = true := by
  intro m hm
  simp only [autos_48_0, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
private def ck0 := levelCheck (freeVars 48 0) rd_48_0 (subGoal 48 0) sl_48_0 autos_48_0 [] 3
private def d0 : List NodeSpec := [([(0,1,0),(1,1,0)],[4,5,2,3],[]),([(2,1,0),(1,3,4)],[0,1,2,5],[]),([(2,1,0),(2,3,4)],[0,5,1,2],[]),([(0,2,0),(1,1,4)],[0,5,2,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q0 : ck0 d0 = true := by decide +kernel
private def d1 : List NodeSpec := [([(0,2,0),(2,1,4)],[5,0,2,3],[]),([(1,2,0),(0,4,1)],[0,5,2,3],[]),([(1,2,0),(2,4,1)],[5,0,2,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q1 : ck0 d1 = true := by decide +kernel
private def lv_48_0_3_0 : List NodeSpec := (d0 ++ d1)

private theorem ok_48_0_3_0 : LevelOK rd_48_0 (subGoal 48 0) 3 lv_48_0_3_0 :=
  levelCheck_sound pp_48_0 (raw_faithful _ _ _) sl_48_0_ok autos_48_0_ok (emptyLevelOK rd_48_0 (subGoal 48 0) 2)
    (levelCheck_join q0 q1)
private def lv_48_0_3 : List NodeSpec := lv_48_0_3_0
private theorem ok_48_0_3 : LevelOK rd_48_0 (subGoal 48 0) 3 lv_48_0_3 := ok_48_0_3_0
private def ck2 (ids : List Nat) := levelCheck (freeVars 48 0) rd_48_0 (subGoal 48 0) sl_48_0 autos_48_0 (selectPrev ids lv_48_0_3) 4
private def d2 : List NodeSpec := [([(0,1,0)],[4,0,1,2,3],[]),([(1,1,0)],[0,1,4,2,3],[]),([(2,1,0)],[4,0,1,2,3],[]),([(0,2,0)],[4,0,1,2,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q2 : ck2 [0,1,2,3,4] d2 = true := by decide +kernel
private def d3 : List NodeSpec := [([(1,2,0)],[0,1,2,4,3],[]),([(2,2,0)],[4,0,1,2,3],[]),([(3,2,0)],[4,0,1,2,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q3 : ck2 [5,6] d3 = true := by decide +kernel
private def lv_48_0_4_0 : List NodeSpec := (d2 ++ d3)

private theorem ok_48_0_4_0 : LevelOK rd_48_0 (subGoal 48 0) 4 lv_48_0_4_0 := by
  have go {ids ds} (h : ck2 ids ds = true) : LevelOK rd_48_0 (subGoal 48 0) 4 ds :=
    levelCheck_sound pp_48_0 (raw_faithful _ _ _) sl_48_0_ok autos_48_0_ok (selectPrevOK ids ok_48_0_3) h
  exact (levelOK_append (go q2) (go q3))
private def lv_48_0_4 : List NodeSpec := lv_48_0_4_0
private theorem ok_48_0_4 : LevelOK rd_48_0 (subGoal 48 0) 4 lv_48_0_4 := ok_48_0_4_0
private def lv_48_0_5_0 : List NodeSpec := [([], [0, 1, 2, 3], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_48_0_5_0 : LevelOK rd_48_0 (subGoal 48 0) 5 lv_48_0_5_0 :=
  levelCheck_sound pp_48_0 (raw_faithful _ _ _) sl_48_0_ok autos_48_0_ok (selectPrevOK [0,1,2,3,4,5,6] ok_48_0_4)
    (by decide +kernel : levelCheck (freeVars 48 0) rd_48_0 (subGoal 48 0) sl_48_0 autos_48_0 (selectPrev [0,1,2,3,4,5,6] lv_48_0_4) 5 lv_48_0_5_0 = true)
private def lv_48_0_5 : List NodeSpec := lv_48_0_5_0
private theorem ok_48_0_5 : LevelOK rd_48_0 (subGoal 48 0) 5 lv_48_0_5 := ok_48_0_5_0
private theorem lower_48_0 : Lower (freeVars 48 0) (subGoal 48 0) 6 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 4, 5), (inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 1, 5), (inputs.getD 3 zero, 3, 11)]) ok_48_0_5 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube48_0

section Cube33_16

private def p_33_16 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0xbecfbecfbecfbecf 0xbecfbecfbecfbecf
  | 2 => mk128 0xdf73df73df73df73 0xdf73df73df73df73
  | 3 => mk128 0xefbcefbcefbcefbc 0xefbcefbcefbcefbc
  | 4 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 5 => mk128 0x0 0x0
  | _ => 0
private def q_33_16 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0x4205420542054205 0x4205420542054205
  | 2 => mk128 0x2412241224122412 0x2412241224122412
  | 3 => mk128 0x1828182818281828 0x1828182818281828
  | 4 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 5 => mk128 0x0 0x0
  | _ => 0
private theorem pp_33_16 : properPairs (subGoal 33 16) (asRow p_33_16) (asRow q_33_16) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_33_16 : List Decor := rawDecor (freeMask 33 16) p_33_16 q_33_16
private def sl_33_16 : List (Sig × Nat) := []
private theorem sl_33_16_ok : ∀ s ∈ sl_33_16, Slice (freeVars 33 16) (subGoal 33 16) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private def autos_33_16 : List (List Move) := [[], [swapRows 50], [swapRows 33], [swapRows 33, swapRows 50], [swapRows 49, swapRows 50], [swapRows 49]]
private theorem autos_33_16_ok : ∀ m ∈ autos_33_16, autoOK (subGoal 33 16) m = true := by
  intro m hm
  simp only [autos_33_16, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
private def lv_33_16_3_0 : List NodeSpec := [([], [0, 1, 2], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_33_16_3_0 : LevelOK rd_33_16 (subGoal 33 16) 3 lv_33_16_3_0 :=
  levelCheck_sound pp_33_16 (raw_faithful _ _ _) sl_33_16_ok autos_33_16_ok (emptyLevelOK rd_33_16 (subGoal 33 16) 2)
    (by decide +kernel : levelCheck (freeVars 33 16) rd_33_16 (subGoal 33 16) sl_33_16 autos_33_16 [] 3 lv_33_16_3_0 = true)
private def lv_33_16_3 : List NodeSpec := lv_33_16_3_0
private theorem ok_33_16_3 : LevelOK rd_33_16 (subGoal 33 16) 3 lv_33_16_3 := ok_33_16_3_0
private theorem lower_33_16 : Lower (freeVars 33 16) (subGoal 33 16) 4 :=
  lower_of_search (xs := [(inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 3 zero, 2, 10)]) ok_33_16_3 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube33_16

section Cube33_0

private def p_33_0 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0xeef8ff9f8ff879f9 0xddf1ff3f1ff0f3f3
  | 2 => mk128 0xf7ff3ffff1fffe3f 0xeffe7fffe3fffc7f
  | 3 => mk128 0x3b7fc7e7fe3f87ce 0x76ff8fcffc7f0f9c
  | 4 => mk128 0x3c7ff807ffc007f0 0x78fff00fff800fe0
  | 5 => mk128 0x0 0x0
  | _ => 0
private def q_33_0 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0x510e1121824930d8 0xa21c2243049261b1
  | 2 => mk128 0x8810820210924223 0x1021040421248446
  | 3 => mk128 0x4a2340ca425154c 0x9446819484a2a98
  | 4 => mk128 0x3c4a757490667b0 0x7894eae920ccf60
  | 5 => mk128 0x0 0x0
  | _ => 0
private theorem pp_33_0 : properPairs (subGoal 33 0) (asRow p_33_0) (asRow q_33_0) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_33_0 : List Decor := rawDecor (freeMask 33 0) p_33_0 q_33_0
private def sl_33_0 : List (Sig × Nat) := [(subcube 33 16, 4)]
private theorem sl_33_0_ok : ∀ s ∈ sl_33_0, Slice (freeVars 33 0) (subGoal 33 0) s.1 s.2 := by
  intro s hs
  simp only [sl_33_0, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 33 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_33_16
private def autos_33_0 : List (List Move) := [[], [swapRows 49]]
private theorem autos_33_0_ok : ∀ m ∈ autos_33_0, autoOK (subGoal 33 0) m = true := by
  intro m hm
  simp only [autos_33_0, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl <;> decide +kernel
private def lv_33_0_4_0 : List NodeSpec := [([], [0, 1, 2, 3], [(0, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_33_0_4_0 : LevelOK rd_33_0 (subGoal 33 0) 4 lv_33_0_4_0 :=
  levelCheck_sound pp_33_0 (raw_faithful _ _ _) sl_33_0_ok autos_33_0_ok (emptyLevelOK rd_33_0 (subGoal 33 0) 3)
    (by decide +kernel : levelCheck (freeVars 33 0) rd_33_0 (subGoal 33 0) sl_33_0 autos_33_0 [] 4 lv_33_0_4_0 = true)
private def lv_33_0_4 : List NodeSpec := lv_33_0_4_0
private theorem ok_33_0_4 : LevelOK rd_33_0 (subGoal 33 0) 4 lv_33_0_4 := ok_33_0_4_0
private theorem lower_33_0 : Lower (freeVars 33 0) (subGoal 33 0) 5 :=
  lower_of_search (xs := [(inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 3 zero, 4, 12), (inputs.getD 4 zero, 10, 26)]) ok_33_0_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube33_0

section Cube36_2

private def p_36_2 : Nat → Bits
  | 0 => mk128 0xbecfbecfbecfbecf 0xbecfbecfbecfbecf
  | 1 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 2 => mk128 0x0 0x0
  | 3 => mk128 0xdf73df73df73df73 0xdf73df73df73df73
  | 4 => mk128 0xefbcefbcefbcefbc 0xefbcefbcefbcefbc
  | 5 => mk128 0x0 0x0
  | _ => 0
private def q_36_2 : Nat → Bits
  | 0 => mk128 0x4205420542054205 0x4205420542054205
  | 1 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 2 => mk128 0x0 0x0
  | 3 => mk128 0x2412241224122412 0x2412241224122412
  | 4 => mk128 0x1828182818281828 0x1828182818281828
  | 5 => mk128 0x0 0x0
  | _ => 0
private theorem pp_36_2 : properPairs (subGoal 36 2) (asRow p_36_2) (asRow q_36_2) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_36_2 : List Decor := rawDecor (freeMask 36 2) p_36_2 q_36_2
private def sl_36_2 : List (Sig × Nat) := []
private theorem sl_36_2_ok : ∀ s ∈ sl_36_2, Slice (freeVars 36 2) (subGoal 36 2) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private def autos_36_2 : List (List Move) := [[], [swapRows 67], [swapRows 48], [swapRows 48, swapRows 67], [swapRows 64, swapRows 67], [swapRows 64]]
private theorem autos_36_2_ok : ∀ m ∈ autos_36_2, autoOK (subGoal 36 2) m = true := by
  intro m hm
  simp only [autos_36_2, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
private def lv_36_2_3_0 : List NodeSpec := [([], [0, 1, 2], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_36_2_3_0 : LevelOK rd_36_2 (subGoal 36 2) 3 lv_36_2_3_0 :=
  levelCheck_sound pp_36_2 (raw_faithful _ _ _) sl_36_2_ok autos_36_2_ok (emptyLevelOK rd_36_2 (subGoal 36 2) 2)
    (by decide +kernel : levelCheck (freeVars 36 2) rd_36_2 (subGoal 36 2) sl_36_2 autos_36_2 [] 3 lv_36_2_3_0 = true)
private def lv_36_2_3 : List NodeSpec := lv_36_2_3_0
private theorem ok_36_2_3 : LevelOK rd_36_2 (subGoal 36 2) 3 lv_36_2_3 := ok_36_2_3_0
private theorem lower_36_2 : Lower (freeVars 36 2) (subGoal 36 2) 4 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 8, 9), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 1, 17)]) ok_36_2_3 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube36_2

section Cube32_2

private def p_32_2 : Nat → Bits
  | 0 => mk128 0x73b7606ebea673b7 0x606ebea673b7606e
  | 1 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 2 => mk128 0xbc3bbc93ff3bbc3b 0xbc93ff3bbc3bbc93
  | 3 => mk128 0xcfc3c31cdfc3cfc3 0xc31cdfc3cfc3c31c
  | 4 => mk128 0xffc03e0effc0ffc 0x3e0effc0ffc03e0
  | 5 => mk128 0x0 0x0
  | _ => 0
private def q_32_2 : Nat → Bits
  | 0 => mk128 0x8091042642488091 0x426424880910426
  | 1 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 2 => mk128 0x0 0x0
  | 3 => mk128 0x1502091824141502 0x918241415020918
  | 4 => mk128 0x6a2012c018016a20 0x12c018016a2012c0
  | 5 => mk128 0x0 0x0
  | _ => 0
private theorem pp_32_2 : properPairs (subGoal 32 2) (asRow p_32_2) (asRow q_32_2) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_32_2 : List Decor := rawDecor (freeMask 32 2) p_32_2 q_32_2
private def sl_32_2 : List (Sig × Nat) := [(subcube 36 2, 4)]
private theorem sl_32_2_ok : ∀ s ∈ sl_32_2, Slice (freeVars 32 2) (subGoal 32 2) s.1 s.2 := by
  intro s hs
  simp only [sl_32_2, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 36 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_36_2
private def autos_32_2 : List (List Move) := [[], [swapRows 67], [swapRows 48], [swapRows 48, swapRows 67], [swapRows 64, swapRows 67], [swapRows 64]]
private theorem autos_32_2_ok : ∀ m ∈ autos_32_2, autoOK (subGoal 32 2) m = true := by
  intro m hm
  simp only [autos_32_2, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
private def lv_32_2_4_0 : List NodeSpec := [([], [0, 1, 2, 3], [(0, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_32_2_4_0 : LevelOK rd_32_2 (subGoal 32 2) 4 lv_32_2_4_0 :=
  levelCheck_sound pp_32_2 (raw_faithful _ _ _) sl_32_2_ok autos_32_2_ok (emptyLevelOK rd_32_2 (subGoal 32 2) 3)
    (by decide +kernel : levelCheck (freeVars 32 2) rd_32_2 (subGoal 32 2) sl_32_2 autos_32_2 [] 4 lv_32_2_4_0 = true)
private def lv_32_2_4 : List NodeSpec := lv_32_2_4_0
private theorem ok_32_2_4 : LevelOK rd_32_2 (subGoal 32 2) 4 lv_32_2_4 := ok_32_2_4_0
private theorem lower_32_2 : Lower (freeVars 32 2) (subGoal 32 2) 5 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 8, 9), (inputs.getD 2 zero, 0, 4), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 1, 17)]) ok_32_2_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube32_2

section Cube36_0

private def p_36_0 : Nat → Bits
  | 0 => mk128 0xffbfc7fffe3fff1f 0xfbfc7fffe3fff1ff
  | 1 => mk128 0x67d7f879ffc707e6 0x7d7f879ffc707e67
  | 2 => mk128 0x0 0x0
  | 3 => mk128 0x87e7ff81fff807f8 0x7e7ff81fff807f87
  | 4 => mk128 0xf8fbfffe3ffff8ff 0x8fbfffe3ffff8ff8
  | 5 => mk128 0x0 0x0
  | _ => 0
private def q_36_0 : Nat → Bits
  | 0 => mk128 0xab4071100609310a 0xb4071100609310ab
  | 1 => mk128 0x652897229a425266 0x52897229a4252665
  | 2 => mk128 0x0 0x0
  | 3 => mk128 0x861922752c90a4b8 0x61922752c90a4b86
  | 4 => mk128 0x50060441b124c0d5 0x60441b124c0d50
  | 5 => mk128 0x0 0x0
  | _ => 0
private theorem pp_36_0 : properPairs (subGoal 36 0) (asRow p_36_0) (asRow q_36_0) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_36_0 : List Decor := rawDecor (freeMask 36 0) p_36_0 q_36_0
private def sl_36_0 : List (Sig × Nat) := [(subcube 36 2, 4)]
private theorem sl_36_0_ok : ∀ s ∈ sl_36_0, Slice (freeVars 36 0) (subGoal 36 0) s.1 s.2 := by
  intro s hs
  simp only [sl_36_0, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 36 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_36_2
private def autos_36_0 : List (List Move) := [[], [swapRows 49], [swapRows 64], [swapRows 64, swapRows 49]]
private theorem autos_36_0_ok : ∀ m ∈ autos_36_0, autoOK (subGoal 36 0) m = true := by
  intro m hm
  simp only [autos_36_0, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl <;> decide +kernel
private def lv_36_0_4_0 : List NodeSpec := [([], [0, 1, 2, 3], [(0, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_36_0_4_0 : LevelOK rd_36_0 (subGoal 36 0) 4 lv_36_0_4_0 :=
  levelCheck_sound pp_36_0 (raw_faithful _ _ _) sl_36_0_ok autos_36_0_ok (emptyLevelOK rd_36_0 (subGoal 36 0) 3)
    (by decide +kernel : levelCheck (freeVars 36 0) rd_36_0 (subGoal 36 0) sl_36_0 autos_36_0 [] 4 lv_36_0_4_0 = true)
private def lv_36_0_4 : List NodeSpec := lv_36_0_4_0
private theorem ok_36_0_4 : LevelOK rd_36_0 (subGoal 36 0) 4 lv_36_0_4 := ok_36_0_4_0
private theorem lower_36_0 : Lower (freeVars 36 0) (subGoal 36 0) 5 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 10, 11), (inputs.getD 1 zero, 9, 11), (inputs.getD 3 zero, 3, 11), (inputs.getD 4 zero, 1, 17)]) ok_36_0_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube36_0

section Cube36_8

private def p_36_8 : Nat → Bits
  | 0 => mk128 0xbecfbecfbecfbecf 0xbecfbecfbecfbecf
  | 1 => mk128 0xdf73df73df73df73 0xdf73df73df73df73
  | 2 => mk128 0x0 0x0
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0xefbcefbcefbcefbc 0xefbcefbcefbcefbc
  | 5 => mk128 0x0 0x0
  | _ => 0
private def q_36_8 : Nat → Bits
  | 0 => mk128 0x4205420542054205 0x4205420542054205
  | 1 => mk128 0x2412241224122412 0x2412241224122412
  | 2 => mk128 0x0 0x0
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0x1828182818281828 0x1828182818281828
  | 5 => mk128 0x0 0x0
  | _ => 0
private theorem pp_36_8 : properPairs (subGoal 36 8) (asRow p_36_8) (asRow q_36_8) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_36_8 : List Decor := rawDecor (freeMask 36 8) p_36_8 q_36_8
private def sl_36_8 : List (Sig × Nat) := []
private theorem sl_36_8_ok : ∀ s ∈ sl_36_8, Slice (freeVars 36 8) (subGoal 36 8) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private def autos_36_8 : List (List Move) := [[], [swapRows 65], [swapRows 16], [swapRows 16, swapRows 65], [swapRows 64, swapRows 65], [swapRows 64]]
private theorem autos_36_8_ok : ∀ m ∈ autos_36_8, autoOK (subGoal 36 8) m = true := by
  intro m hm
  simp only [autos_36_8, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
private def lv_36_8_3_0 : List NodeSpec := [([], [0, 1, 2], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_36_8_3_0 : LevelOK rd_36_8 (subGoal 36 8) 3 lv_36_8_3_0 :=
  levelCheck_sound pp_36_8 (raw_faithful _ _ _) sl_36_8_ok autos_36_8_ok (emptyLevelOK rd_36_8 (subGoal 36 8) 2)
    (by decide +kernel : levelCheck (freeVars 36 8) rd_36_8 (subGoal 36 8) sl_36_8 autos_36_8 [] 3 lv_36_8_3_0 = true)
private def lv_36_8_3 : List NodeSpec := lv_36_8_3_0
private theorem ok_36_8_3 : LevelOK rd_36_8 (subGoal 36 8) 3 lv_36_8_3 := ok_36_8_3_0
private theorem lower_36_8 : Lower (freeVars 36 8) (subGoal 36 8) 4 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 4 zero, 1, 17)]) ok_36_8_3 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube36_8

section Cube32_8

private def p_32_8 : Nat → Bits
  | 0 => mk128 0x7377446bbe967377 0x446bbe967377446b
  | 1 => mk128 0x9c7b8593df1b9c7b 0x8593df1b9c7b8593
  | 2 => mk128 0xef83fa1cffe3ef83 0xfa1cffe3ef83fa1c
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0xffc03e0effc0ffc 0x3e0effc0ffc03e0
  | 5 => mk128 0x0 0x0
  | _ => 0
private def q_32_8 : Nat → Bits
  | 0 => mk128 0x8111082942288111 0x829422881110829
  | 1 => mk128 0x2422109224442422 0x1092244424221092
  | 2 => mk128 0x0 0x0
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0x5a40234018015a40 0x234018015a402340
  | 5 => mk128 0x0 0x0
  | _ => 0
private theorem pp_32_8 : properPairs (subGoal 32 8) (asRow p_32_8) (asRow q_32_8) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_32_8 : List Decor := rawDecor (freeMask 32 8) p_32_8 q_32_8
private def sl_32_8 : List (Sig × Nat) := [(subcube 36 8, 4)]
private theorem sl_32_8_ok : ∀ s ∈ sl_32_8, Slice (freeVars 32 8) (subGoal 32 8) s.1 s.2 := by
  intro s hs
  simp only [sl_32_8, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 36 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_36_8
private def autos_32_8 : List (List Move) := [[], [swapRows 65], [swapRows 16], [swapRows 16, swapRows 65], [swapRows 64, swapRows 65], [swapRows 64]]
private theorem autos_32_8_ok : ∀ m ∈ autos_32_8, autoOK (subGoal 32 8) m = true := by
  intro m hm
  simp only [autos_32_8, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
private def lv_32_8_4_0 : List NodeSpec := [([], [0, 1, 2, 3], [(0, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_32_8_4_0 : LevelOK rd_32_8 (subGoal 32 8) 4 lv_32_8_4_0 :=
  levelCheck_sound pp_32_8 (raw_faithful _ _ _) sl_32_8_ok autos_32_8_ok (emptyLevelOK rd_32_8 (subGoal 32 8) 3)
    (by decide +kernel : levelCheck (freeVars 32 8) rd_32_8 (subGoal 32 8) sl_32_8 autos_32_8 [] 4 lv_32_8_4_0 = true)
private def lv_32_8_4 : List NodeSpec := lv_32_8_4_0
private theorem ok_32_8_4 : LevelOK rd_32_8 (subGoal 32 8) 4 lv_32_8_4 := ok_32_8_4_0
private theorem lower_32_8 : Lower (freeVars 32 8) (subGoal 32 8) 5 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 0, 4), (inputs.getD 4 zero, 1, 17)]) ok_32_8_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube32_8

section Cube32_16

private def p_32_16 : Nat → Bits
  | 0 => mk128 0xf1b77c27feaef1b7 0x7c27feaef1b77c27
  | 1 => mk128 0x3e3ba0dabf333e3b 0xa0dabf333e3ba0da
  | 2 => mk128 0xcfc3c31cdfc3cfc3 0xc31cdfc3cfc3c31c
  | 3 => mk128 0xffc03e0effc0ffc 0x3e0effc0ffc03e0
  | 4 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 5 => mk128 0x0 0x0
  | _ => 0
private def q_32_16 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0x4211044a42444211 0x44a42444211044a
  | 2 => mk128 0x1482091424181482 0x914241814820914
  | 3 => mk128 0xa92012a01801a920 0x12a01801a92012a0
  | 4 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 5 => mk128 0x0 0x0
  | _ => 0
private theorem pp_32_16 : properPairs (subGoal 32 16) (asRow p_32_16) (asRow q_32_16) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_32_16 : List Decor := rawDecor (freeMask 32 16) p_32_16 q_32_16
private def sl_32_16 : List (Sig × Nat) := [(subcube 33 16, 4)]
private theorem sl_32_16_ok : ∀ s ∈ sl_32_16, Slice (freeVars 32 16) (subGoal 32 16) s.1 s.2 := by
  intro s hs
  simp only [sl_32_16, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 33 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_33_16
private def autos_32_16 : List (List Move) := [[], [swapRows 50], [swapRows 33], [swapRows 33, swapRows 50], [swapRows 49, swapRows 50], [swapRows 49]]
private theorem autos_32_16_ok : ∀ m ∈ autos_32_16, autoOK (subGoal 32 16) m = true := by
  intro m hm
  simp only [autos_32_16, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
private def lv_32_16_4_0 : List NodeSpec := [([], [0, 1, 2, 3], [(0, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_32_16_4_0 : LevelOK rd_32_16 (subGoal 32 16) 4 lv_32_16_4_0 :=
  levelCheck_sound pp_32_16 (raw_faithful _ _ _) sl_32_16_ok autos_32_16_ok (emptyLevelOK rd_32_16 (subGoal 32 16) 3)
    (by decide +kernel : levelCheck (freeVars 32 16) rd_32_16 (subGoal 32 16) sl_32_16 autos_32_16 [] 4 lv_32_16_4_0 = true)
private def lv_32_16_4 : List NodeSpec := lv_32_16_4_0
private theorem ok_32_16_4 : LevelOK rd_32_16 (subGoal 32 16) 4 lv_32_16_4 := ok_32_16_4_0
private theorem lower_32_16 : Lower (freeVars 32 16) (subGoal 32 16) 5 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 0, 1), (inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 3 zero, 2, 10)]) ok_32_16_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube32_16

section Cube34_0

private def p_34_0 : Nat → Bits
  | 0 => mk128 0xbfcffcf8fff873f3 0xbfcffcf8fff873f3
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0xdff39fff1c3ffc9f 0xdff39fff1c3ffc9f
  | 3 => mk128 0xebfc1f3fe03f8f1c 0xebfc1f3fe03f8f1c
  | 4 => mk128 0xf3ffe03fffc00fe0 0xf3ffe03fffc00fe0
  | 5 => mk128 0x0 0x0
  | _ => 0
private def q_34_0 : Nat → Bits
  | 0 => mk128 0x4061010824892131 0x4061010824892131
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0x2088281109124486 0x2088281109124486
  | 3 => mk128 0x1523506a42a52b18 0x1523506a42a52b18
  | 4 => mk128 0xe0a1ab493064ec0 0xe0a1ab493064ec0
  | 5 => mk128 0x0 0x0
  | _ => 0
private theorem pp_34_0 : properPairs (subGoal 34 0) (asRow p_34_0) (asRow q_34_0) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_34_0 : List Decor := rawDecor (freeMask 34 0) p_34_0 q_34_0
private def sl_34_0 : List (Sig × Nat) := []
private theorem sl_34_0_ok : ∀ s ∈ sl_34_0, Slice (freeVars 34 0) (subGoal 34 0) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private def autos_34_0 : List (List Move) := [[], [swapRows 32, swapRows 67]]
private theorem autos_34_0_ok : ∀ m ∈ autos_34_0, autoOK (subGoal 34 0) m = true := by
  intro m hm
  simp only [autos_34_0, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl <;> decide +kernel
private def lv_34_0_3_0 : List NodeSpec := [([], [0, 1, 2, 3], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_34_0_3_0 : LevelOK rd_34_0 (subGoal 34 0) 3 lv_34_0_3_0 :=
  levelCheck_sound pp_34_0 (raw_faithful _ _ _) sl_34_0_ok autos_34_0_ok (emptyLevelOK rd_34_0 (subGoal 34 0) 2)
    (by decide +kernel : levelCheck (freeVars 34 0) rd_34_0 (subGoal 34 0) sl_34_0 autos_34_0 [] 3 lv_34_0_3_0 = true)
private def lv_34_0_3 : List NodeSpec := lv_34_0_3_0
private theorem ok_34_0_3 : LevelOK rd_34_0 (subGoal 34 0) 3 lv_34_0_3 := ok_34_0_3_0
private theorem lower_34_0 : Lower (freeVars 34 0) (subGoal 34 0) 4 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 4, 5), (inputs.getD 2 zero, 1, 5), (inputs.getD 3 zero, 4, 12), (inputs.getD 4 zero, 1, 17)]) ok_34_0_3 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube34_0

section Cube40_0

private def p_40_0 : Nat → Bits
  | 0 => mk128 0xbfcffcf8fff873f3 0xbfcffcf8fff873f3
  | 1 => mk128 0xdbf19f3f1c3f8d9c 0xdbf19f3f1c3f8d9c
  | 2 => mk128 0xeffe1fffe03ffe1f 0xeffe1fffe03ffe1f
  | 3 => mk128 0x0 0x0
  | 4 => mk128 0xf3ffe03fffc00fe0 0xf3ffe03fffc00fe0
  | 5 => mk128 0x0 0x0
  | _ => 0
private def q_40_0 : Nat → Bits
  | 0 => mk128 0x40640108248920b1 0x40640108248920b1
  | 1 => mk128 0x24ac285909932594 0x24ac285909932594
  | 2 => mk128 0x1101502242244a0a 0x1101502242244a0a
  | 3 => mk128 0x0 0x0
  | 4 => mk128 0xe091ab493064f40 0xe091ab493064f40
  | 5 => mk128 0x0 0x0
  | _ => 0
private theorem pp_40_0 : properPairs (subGoal 40 0) (asRow p_40_0) (asRow q_40_0) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_40_0 : List Decor := rawDecor (freeMask 40 0) p_40_0 q_40_0
private def sl_40_0 : List (Sig × Nat) := []
private theorem sl_40_0_ok : ∀ s ∈ sl_40_0, Slice (freeVars 40 0) (subGoal 40 0) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private def autos_40_0 : List (List Move) := [[], [swapRows 32, swapRows 65]]
private theorem autos_40_0_ok : ∀ m ∈ autos_40_0, autoOK (subGoal 40 0) m = true := by
  intro m hm
  simp only [autos_40_0, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl <;> decide +kernel
private def lv_40_0_3_0 : List NodeSpec := [([], [0, 1, 2, 3], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_40_0_3_0 : LevelOK rd_40_0 (subGoal 40 0) 3 lv_40_0_3_0 :=
  levelCheck_sound pp_40_0 (raw_faithful _ _ _) sl_40_0_ok autos_40_0_ok (emptyLevelOK rd_40_0 (subGoal 40 0) 2)
    (by decide +kernel : levelCheck (freeVars 40 0) rd_40_0 (subGoal 40 0) sl_40_0 autos_40_0 [] 3 lv_40_0_3_0 = true)
private def lv_40_0_3 : List NodeSpec := lv_40_0_3_0
private theorem ok_40_0_3 : LevelOK rd_40_0 (subGoal 40 0) 3 lv_40_0_3 := ok_40_0_3_0
private theorem lower_40_0 : Lower (freeVars 40 0) (subGoal 40 0) 4 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 4, 5), (inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 1, 5), (inputs.getD 4 zero, 1, 17)]) ok_40_0_3 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube40_0

section Cube32_0

private def p_32_0 : Nat → Bits
  | 0 => mk128 0xfc0f8ff1c38f8fc7 0xfff1c1f83c19f4f3
  | 1 => mk128 0x3ff00ffe3c0ff1f8 0xe07e01ffc0e6c8fc
  | 2 => mk128 0x3ffff1fffff001ff 0x7ffe3fff070f1f
  | 3 => mk128 0x3ffffe003ffffe00 0x7fffc003f80fe0
  | 4 => mk128 0xc00000003fffffff 0xff80000003fff000
  | 5 => mk128 0x0 0x0
  | _ => 0
private def q_32_0 : Nat → Bits
  | 0 => mk128 0x461102200818241 0x2330444898085471
  | 1 => mk128 0x48a324c04c0690c8 0x455208938862c8b4
  | 2 => mk128 0x9104010011100112 0x80490242105010a
  | 3 => mk128 0x224a0864a6ab2400 0x12692d0112b80ec0
  | 4 => mk128 0x38c4d893b4c49a4 0x9c00300623d7a000
  | 5 => mk128 0x0 0x0
  | _ => 0
private theorem pp_32_0 : properPairs (subGoal 32 0) (asRow p_32_0) (asRow q_32_0) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_32_0 : List Decor := rawDecor (freeMask 32 0) p_32_0 q_32_0
private def sl_32_0 : List (Sig × Nat) := [(subcube 48 0, 6), (subcube 33 0, 5), (subcube 32 2, 5), (subcube 36 0, 5), (subcube 32 8, 5), (subcube 32 16, 5), (subcube 34 0, 4), (subcube 36 2, 4), (subcube 40 0, 4), (subcube 36 8, 4), (subcube 33 16, 4)]
private theorem sl_32_0_ok : ∀ s ∈ sl_32_0, Slice (freeVars 32 0) (subGoal 32 0) s.1 s.2 := by
  intro s hs
  simp only [sl_32_0, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact slice_correct (ms := fixRows 48 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_48_0
  · exact slice_correct (ms := fixRows 33 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_33_0
  · exact slice_correct (ms := fixRows 32 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_32_2
  · exact slice_correct (ms := fixRows 36 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_36_0
  · exact slice_correct (ms := fixRows 32 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_32_8
  · exact slice_correct (ms := fixRows 32 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_32_16
  · exact slice_correct (ms := fixRows 34 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_34_0
  · exact slice_correct (ms := fixRows 36 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_36_2
  · exact slice_correct (ms := fixRows 40 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_40_0
  · exact slice_correct (ms := fixRows 36 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_36_8
  · exact slice_correct (ms := fixRows 33 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_33_16
private def autos_32_0 : List (List Move) := [[], [swapRows 49]]
private theorem autos_32_0_ok : ∀ m ∈ autos_32_0, autoOK (subGoal 32 0) m = true := by
  intro m hm
  simp only [autos_32_0, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl <;> decide +kernel
private def ck4 := levelCheck (freeVars 32 0) rd_32_0 (subGoal 32 0) sl_32_0 autos_32_0 [] 4
private def d4 : List NodeSpec := [([(2,1,0),(1,2,1),(0,3,6),(1,7,0)],[5,2,7,8,4],[]),([(2,1,0),(1,2,1),(0,3,6),(3,7,0)],[8,5,2,7,4],[]),([(2,1,0),(0,3,5),(1,2,6),(1,4,2)],[0,1,7,3,8],[]),([(2,1,0),(0,3,1),(1,2,6),(1,4,2)],[5,0,7,3,8],[(4,[2,3])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q4 : ck4 d4 = true := by decide +kernel
private def d5 : List NodeSpec := [([(1,2,0),(0,3,1),(1,6,0),(1,4,2)],[1,7,5,3,8],[]),([(1,2,0),(0,3,1),(1,5,6),(1,4,2)],[0,1,7,3,8],[(0,[])]),([(1,2,0),(0,3,1),(2,5,6),(1,4,2)],[7,0,1,3,8],[]),([(1,2,1),(0,3,5),(1,6,0),(3,4,7)],[8,0,1,2,6],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q5 : ck4 d5 = true := by decide +kernel
private def d6 : List NodeSpec := [([(1,2,1),(0,3,5),(3,4,0),(2,1,7)],[0,8,2,6,4],[]),([(0,3,1),(1,5,0),(0,4,6),(1,2,7)],[0,1,6,8,3],[]),([(0,3,1),(1,5,0),(1,4,2),(0,7,6)],[0,1,8,2,3],[(0,[])]),([(0,3,1),(1,5,0),(2,4,2),(2,6,7)],[0,1,8,2,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q6 : ck4 d6 = true := by decide +kernel
private def lv_32_0_4_0 : List NodeSpec := (d4 ++ (d5 ++ d6))

private theorem ok_32_0_4_0 : LevelOK rd_32_0 (subGoal 32 0) 4 lv_32_0_4_0 :=
  levelCheck_sound pp_32_0 (raw_faithful _ _ _) sl_32_0_ok autos_32_0_ok (emptyLevelOK rd_32_0 (subGoal 32 0) 3)
    (levelCheck_join q4 (levelCheck_join q5 q6))
private def ck7 := levelCheck (freeVars 32 0) rd_32_0 (subGoal 32 0) sl_32_0 autos_32_0 [] 4
private def d7 : List NodeSpec := [([(0,3,1),(1,5,0),(1,3,1),(2,7,0)],[8,5,6,2,4],[]),([(0,3,1),(1,5,0),(1,3,1),(2,7,6)],[8,0,5,2,4],[]),([(0,3,1),(1,5,0),(1,3,1),(3,4,6)],[8,0,5,2,7],[]),([(0,3,1),(3,5,0),(1,3,1),(2,7,6)],[0,5,8,2,4],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q7 : ck7 d7 = true := by decide +kernel
private def d8 : List NodeSpec := [([(0,3,1),(3,5,0),(1,3,1),(2,7,0)],[6,8,5,2,4],[]),([(0,3,1),(1,2,5),(2,6,0),(1,4,2)],[7,0,1,3,8],[]),([(0,3,1),(1,2,5),(1,4,2),(0,7,1)],[0,8,6,3,7],[(4,[1,2])]),([(0,3,1),(1,3,1),(2,6,5),(1,0,7)],[0,8,5,2,4],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q8 : ck7 d8 = true := by decide +kernel
private def d9 : List NodeSpec := [([(0,3,1),(1,3,1),(1,4,0),(2,7,5)],[8,0,2,6,4],[]),([(0,3,1),(1,3,1),(3,4,0),(2,6,7)],[0,5,2,8,4],[]),([(0,3,1),(1,4,2),(0,6,5),(1,7,0)],[1,8,2,3,6],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q9 : ck7 d9 = true := by decide +kernel
private def lv_32_0_4_1 : List NodeSpec := (d7 ++ (d8 ++ d9))

private theorem ok_32_0_4_1 : LevelOK rd_32_0 (subGoal 32 0) 4 lv_32_0_4_1 :=
  levelCheck_sound pp_32_0 (raw_faithful _ _ _) sl_32_0_ok autos_32_0_ok (emptyLevelOK rd_32_0 (subGoal 32 0) 3)
    (levelCheck_join q7 (levelCheck_join q8 q9))
private def lv_32_0_4 : List NodeSpec := (lv_32_0_4_0 ++ lv_32_0_4_1)
private theorem ok_32_0_4 : LevelOK rd_32_0 (subGoal 32 0) 4 lv_32_0_4 := (levelOK_append ok_32_0_4_0 ok_32_0_4_1)
private def ck10 (ids : List Nat) := levelCheck (freeVars 32 0) rd_32_0 (subGoal 32 0) sl_32_0 autos_32_0 (selectPrev ids lv_32_0_4) 5
private def d10 : List NodeSpec := [([(0,1,0),(1,2,5),(1,3,2)],[0,1,6,3,7,4],[(1,[])]),([(0,1,0),(2,3,5),(1,2,6)],[0,1,2,7,3,4],[(2,[])]),([(0,1,0),(2,3,5),(1,3,2)],[6,0,1,2,7,4],[(6,[])]),([(0,1,0),(2,3,5),(2,4,2)],[7,6,0,1,2,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q10 : ck10 [] d10 = true := by decide +kernel
private def d11 : List NodeSpec := [([(0,1,0),(1,3,2),(2,6,5)],[7,0,1,2,3,4],[(2,[])]),([(1,1,0),(1,3,0),(0,3,1)],[0,7,5,2,6,4],[(1,[]),(2,[])]),([(1,1,0),(1,3,0),(0,3,5)],[0,1,7,2,6,4],[]),([(1,1,0),(1,3,0),(0,6,5)],[0,1,7,2,3,4],[(0,[]),(5,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q11 : ck10 [] d11 = true := by decide +kernel
private def d12 : List NodeSpec := [([(1,1,0),(2,3,0),(2,1,6)],[7,0,5,2,3,4],[(0,[1,2])]),([(1,1,0),(2,3,0),(0,3,1)],[6,0,7,5,2,4],[(1,[]),(2,[])]),([(1,1,0),(0,3,1),(2,5,6)],[7,0,6,2,3,4],[(2,[])]),([(2,1,0),(1,2,5),(1,2,0)],[0,1,6,7,3,4],[(0,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q12 : ck10 [] d12 = true := by decide +kernel
private def lv_32_0_5_0 : List NodeSpec := (d10 ++ (d11 ++ d12))

private theorem ok_32_0_5_0 : LevelOK rd_32_0 (subGoal 32 0) 5 lv_32_0_5_0 := by
  have go {ids ds} (h : ck10 ids ds = true) : LevelOK rd_32_0 (subGoal 32 0) 5 ds :=
    levelCheck_sound pp_32_0 (raw_faithful _ _ _) sl_32_0_ok autos_32_0_ok (selectPrevOK ids ok_32_0_4) h
  exact (levelOK_append (go q10) (levelOK_append (go q11) (go q12)))
private def ck13 (ids : List Nat) := levelCheck (freeVars 32 0) rd_32_0 (subGoal 32 0) sl_32_0 autos_32_0 (selectPrev ids lv_32_0_4) 5
private def d13 : List NodeSpec := [([(2,1,0),(1,2,1),(2,6,5)],[5,0,7,2,3,4],[]),([(2,1,0),(1,2,1),(0,3,6)],[5,0,2,7,4],[(2,[]),(3,[2]),(4,[1]),(7,[]),(9,[])]),([(2,1,0),(1,2,1),(0,3,6)],[5,0,2,7,3,4],[(4,[1])]),([(2,1,0),(0,3,5),(1,2,6)],[0,1,2,7,3,4],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q13 : ck13 [0,1,2] d13 = true := by decide +kernel
private def d14 : List NodeSpec := [([(2,1,0),(0,3,5),(1,4,2)],[6,0,1,2,3,7],[(3,[])]),([(2,1,0),(0,3,5),(2,4,2)],[7,6,0,1,2,3],[]),([(2,1,0),(2,3,5),(1,2,6)],[0,1,2,7,3,4],[(2,[])]),([(2,1,0),(2,3,5),(1,3,2)],[0,6,1,2,7,4],[(6,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q14 : ck13 [2] d14 = true := by decide +kernel
private def d15 : List NodeSpec := [([(2,1,0),(2,3,5),(1,4,2)],[0,6,1,2,3,7],[]),([(2,1,0),(2,3,5),(2,4,2)],[7,0,6,1,2,3],[]),([(2,1,0),(2,3,0),(0,3,1)],[5,6,0,7,2,4],[(1,[]),(2,[])]),([(2,1,0),(0,3,1),(1,2,6)],[5,0,2,7,3,4],[(2,[]),(4,[2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q15 : ck13 [3] d15 = true := by decide +kernel
private def lv_32_0_5_1 : List NodeSpec := (d13 ++ (d14 ++ d15))

private theorem ok_32_0_5_1 : LevelOK rd_32_0 (subGoal 32 0) 5 lv_32_0_5_1 := by
  have go {ids ds} (h : ck13 ids ds = true) : LevelOK rd_32_0 (subGoal 32 0) 5 ds :=
    levelCheck_sound pp_32_0 (raw_faithful _ _ _) sl_32_0_ok autos_32_0_ok (selectPrevOK ids ok_32_0_4) h
  exact (levelOK_append (go q13) (levelOK_append (go q14) (go q15)))
private def ck16 (ids : List Nat) := levelCheck (freeVars 32 0) rd_32_0 (subGoal 32 0) sl_32_0 autos_32_0 (selectPrev ids lv_32_0_4) 5
private def d16 : List NodeSpec := [([(2,1,0),(0,3,1),(1,4,2)],[5,0,6,2,3,7],[(1,[2]),(4,[2])]),([(2,1,0),(0,3,1),(2,4,2)],[7,5,0,6,2,3],[(1,[2]),(4,[2])]),([(2,1,0),(2,3,1),(1,5,6)],[5,7,0,2,3,4],[(2,[])]),([(2,1,0),(1,3,2),(2,6,5)],[0,7,1,2,3,4],[(2,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q16 : ck16 [3] d16 = true := by decide +kernel
private def d17 : List NodeSpec := [([(1,2,0),(0,5,1),(1,4,2)],[0,6,1,5,3,7],[(1,[2]),(3,[]),(7,[])]),([(1,2,0),(3,5,1),(1,4,2)],[6,0,1,5,3,7],[(7,[])]),([(1,2,0),(0,3,1),(1,6,0)],[1,7,2,5,3,4],[(3,[]),(6,[]),(8,[])]),([(1,2,0),(0,3,1),(1,2,6)],[0,1,5,7,3,4],[(1,[]),(7,[]),(9,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q17 : ck16 [4] d17 = true := by decide +kernel
private def d18 : List NodeSpec := [([(1,2,0),(0,3,1),(1,5,6)],[0,1,2,7,3,4],[(0,[]),(2,[]),(4,[]),(5,[])]),([(1,2,0),(0,3,1),(2,5,6)],[7,0,1,2,3,4],[]),([(1,2,0),(0,3,1),(1,4,2)],[0,6,1,5,3,7],[(1,[2]),(7,[]),(9,[])]),([(3,2,0),(0,3,1),(1,6,5)],[0,1,7,2,3,4],[(0,[]),(5,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q18 : ck16 [4,5,6] d18 = true := by decide +kernel
private def lv_32_0_5_2 : List NodeSpec := (d16 ++ (d17 ++ d18))

private theorem ok_32_0_5_2 : LevelOK rd_32_0 (subGoal 32 0) 5 lv_32_0_5_2 := by
  have go {ids ds} (h : ck16 ids ds = true) : LevelOK rd_32_0 (subGoal 32 0) 5 ds :=
    levelCheck_sound pp_32_0 (raw_faithful _ _ _) sl_32_0_ok autos_32_0_ok (selectPrevOK ids ok_32_0_4) h
  exact (levelOK_append (go q16) (levelOK_append (go q17) (go q18)))
private def ck19 (ids : List Nat) := levelCheck (freeVars 32 0) rd_32_0 (subGoal 32 0) sl_32_0 autos_32_0 (selectPrev ids lv_32_0_4) 5
private def d19 : List NodeSpec := [([(3,2,0),(0,3,1),(1,6,0)],[5,1,7,2,3,4],[]),([(0,2,1),(1,5,0),(1,4,6)],[1,6,2,3,4,7],[(2,[1]),(6,[])]),([(0,2,1),(1,5,0),(3,4,6)],[7,1,6,2,3,4],[]),([(0,2,1),(1,5,0),(1,4,0)],[1,6,2,3,4,7],[(0,[]),(2,[1]),(6,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q19 : ck19 [] d19 = true := by decide +kernel
private def d20 : List NodeSpec := [([(0,2,1),(1,5,0),(3,4,0)],[7,1,6,2,3,4],[]),([(0,2,1),(1,3,5),(1,4,0)],[0,1,2,6,4,7],[(2,[1]),(6,[])]),([(0,2,1),(1,3,5),(3,4,0)],[7,0,1,2,6,4],[]),([(0,2,1),(2,3,5),(1,4,0)],[6,0,1,2,4,7],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q20 : ck19 [] d20 = true := by decide +kernel
private def d21 : List NodeSpec := [([(0,2,1),(2,3,5),(3,4,0)],[7,6,0,1,2,4],[]),([(0,2,1),(1,4,0),(2,6,5)],[7,0,1,2,3,4],[(0,[]),(0,[0,2])]),([(0,2,1),(3,4,0),(1,5,6)],[0,7,1,2,3,4],[(0,[]),(0,[0,2])]),([(1,2,1),(0,3,5),(1,6,0)],[0,1,2,6,7,4],[(0,[0,1]),(2,[]),(4,[0]),(8,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q21 : ck19 [0,7] d21 = true := by decide +kernel
private def lv_32_0_5_3 : List NodeSpec := (d19 ++ (d20 ++ d21))

private theorem ok_32_0_5_3 : LevelOK rd_32_0 (subGoal 32 0) 5 lv_32_0_5_3 := by
  have go {ids ds} (h : ck19 ids ds = true) : LevelOK rd_32_0 (subGoal 32 0) 5 ds :=
    levelCheck_sound pp_32_0 (raw_faithful _ _ _) sl_32_0_ok autos_32_0_ok (selectPrevOK ids ok_32_0_4) h
  exact (levelOK_append (go q19) (levelOK_append (go q20) (go q21)))
private def ck22 (ids : List Nat) := levelCheck (freeVars 32 0) rd_32_0 (subGoal 32 0) sl_32_0 autos_32_0 (selectPrev ids lv_32_0_4) 5
private def d22 : List NodeSpec := [([(1,2,1),(0,3,5),(3,6,0)],[7,0,1,2,6,4],[(2,[]),(9,[])]),([(1,2,1),(0,3,5),(1,4,0)],[0,1,2,6,4,7],[]),([(1,2,1),(0,3,5),(3,4,0)],[7,0,1,2,6,4],[(2,[])]),([(1,2,1),(0,3,5),(1,4,6)],[0,1,2,6,4,7],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q22 : ck22 [1,8] d22 = true := by decide +kernel
private def d23 : List NodeSpec := [([(1,2,1),(0,3,5),(1,6,0)],[0,1,2,7,3,4],[(0,[]),(2,[]),(5,[]),(8,[])]),([(1,2,1),(3,3,5),(1,4,0)],[6,0,1,2,4,7],[]),([(1,2,1),(3,3,5),(3,4,0)],[7,6,0,1,2,4],[]),([(1,2,1),(1,4,0),(0,6,5)],[0,1,2,7,3,4],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q23 : ck22 [] d23 = true := by decide +kernel
private def d24 : List NodeSpec := [([(1,2,1),(3,4,0),(2,1,6)],[0,7,2,5,3,4],[]),([(1,2,1),(3,4,0),(2,5,6)],[0,1,2,7,3,4],[]),([(1,2,1),(3,4,3),(2,1,6)],[0,7,2,5,3,4],[(8,[])]),([(1,2,1),(3,4,3),(2,5,6)],[0,1,2,7,3,4],[(0,[0,2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q24 : ck22 [8] d24 = true := by decide +kernel
private def lv_32_0_5_4 : List NodeSpec := (d22 ++ (d23 ++ d24))

private theorem ok_32_0_5_4 : LevelOK rd_32_0 (subGoal 32 0) 5 lv_32_0_5_4 := by
  have go {ids ds} (h : ck22 ids ds = true) : LevelOK rd_32_0 (subGoal 32 0) 5 ds :=
    levelCheck_sound pp_32_0 (raw_faithful _ _ _) sl_32_0_ok autos_32_0_ok (selectPrevOK ids ok_32_0_4) h
  exact (levelOK_append (go q22) (levelOK_append (go q23) (go q24)))
private def ck25 (ids : List Nat) := levelCheck (freeVars 32 0) rd_32_0 (subGoal 32 0) sl_32_0 autos_32_0 (selectPrev ids lv_32_0_4) 5
private def d25 : List NodeSpec := [([(2,2,1),(1,4,0),(2,6,5)],[0,1,7,2,3,4],[(0,[])]),([(2,2,1),(1,4,0),(0,6,1)],[5,0,7,2,3,4],[(5,[])]),([(2,2,1),(3,4,0),(1,5,6)],[7,0,1,2,3,4],[(0,[])]),([(3,2,1),(0,3,5),(1,0,6)],[0,7,1,2,3,4],[(0,[]),(5,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q25 : ck25 [] d25 = true := by decide +kernel
private def d26 : List NodeSpec := [([(0,3,1),(1,5,0),(3,2,6)],[7,0,1,2,3,4],[(0,[]),(5,[])]),([(0,3,1),(1,5,0),(1,4,0)],[1,6,2,3,4,7],[(0,[])]),([(0,3,1),(1,5,0),(3,4,0)],[7,1,6,2,3,4],[(0,[])]),([(0,3,1),(1,5,0),(0,4,6)],[0,1,7,6,2,3],[(5,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q26 : ck25 [9] d26 = true := by decide +kernel
private def d27 : List NodeSpec := [([(0,3,1),(1,5,0),(3,4,6)],[7,0,1,6,2,3],[(0,[])]),([(0,3,1),(1,5,0),(1,4,2)],[0,1,6,2,3,7],[(3,[]),(5,[])]),([(0,3,1),(1,5,0),(2,4,2)],[7,0,1,6,2,3],[(0,[])]),([(0,3,1),(1,5,0),(1,3,1)],[0,5,6,2,7,4],[(0,[0,2]),(2,[]),(6,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q27 : ck25 [4,5,10,11,12,13,14] d27 = true := by decide +kernel
private def lv_32_0_5_5 : List NodeSpec := (d25 ++ (d26 ++ d27))

private theorem ok_32_0_5_5 : LevelOK rd_32_0 (subGoal 32 0) 5 lv_32_0_5_5 := by
  have go {ids ds} (h : ck25 ids ds = true) : LevelOK rd_32_0 (subGoal 32 0) 5 ds :=
    levelCheck_sound pp_32_0 (raw_faithful _ _ _) sl_32_0_ok autos_32_0_ok (selectPrevOK ids ok_32_0_4) h
  exact (levelOK_append (go q25) (levelOK_append (go q26) (go q27)))
private def ck28 (ids : List Nat) := levelCheck (freeVars 32 0) rd_32_0 (subGoal 32 0) sl_32_0 autos_32_0 (selectPrev ids lv_32_0_4) 5
private def d28 : List NodeSpec := [([(0,3,1),(1,5,0),(3,4,6)],[7,0,5,1,2,3],[]),([(0,3,1),(3,5,0),(1,3,1)],[6,0,5,2,7,4],[(2,[])]),([(0,3,1),(1,2,5),(2,6,0)],[7,0,1,2,3,4],[]),([(0,3,1),(1,2,5),(1,4,2)],[0,1,6,3,7],[(0,[]),(2,[1,2]),(3,[0]),(4,[1,2]),(7,[]),(9,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q28 : ck28 [3,5,14,15,16,17,18] d28 = true := by decide +kernel
private def d29 : List NodeSpec := [([(0,3,1),(1,2,5),(1,4,2)],[0,1,6,3,4,7],[(0,[]),(7,[])]),([(0,3,1),(1,2,5),(1,4,2)],[0,5,1,6,3,7],[(2,[1,2]),(3,[]),(4,[1,2]),(7,[])]),([(0,3,1),(1,3,1),(2,6,0)],[7,0,5,2,4],[(2,[]),(3,[0]),(7,[])]),([(0,3,1),(1,3,1),(2,6,5)],[7,0,5,2,4],[(0,[0,1]),(2,[]),(3,[0]),(7,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q29 : ck28 [12,13,15,16,19] d29 = true := by decide +kernel
private def d30 : List NodeSpec := [([(0,3,1),(1,3,1),(1,4,0)],[0,5,2,6,4,7],[(6,[])]),([(0,3,1),(1,3,1),(3,4,0)],[7,0,5,2,6,4],[(2,[])]),([(0,3,1),(1,3,1),(1,4,5)],[0,5,2,6,4,7],[(0,[0,1])]),([(0,3,1),(1,4,0),(2,6,5)],[7,0,1,2,3,4],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q30 : ck28 [20,21] d30 = true := by decide +kernel
private def lv_32_0_5_6 : List NodeSpec := (d28 ++ (d29 ++ d30))

private theorem ok_32_0_5_6 : LevelOK rd_32_0 (subGoal 32 0) 5 lv_32_0_5_6 := by
  have go {ids ds} (h : ck28 ids ds = true) : LevelOK rd_32_0 (subGoal 32 0) 5 ds :=
    levelCheck_sound pp_32_0 (raw_faithful _ _ _) sl_32_0_ok autos_32_0_ok (selectPrevOK ids ok_32_0_4) h
  exact (levelOK_append (go q28) (levelOK_append (go q29) (go q30)))
private def ck31 (ids : List Nat) := levelCheck (freeVars 32 0) rd_32_0 (subGoal 32 0) sl_32_0 autos_32_0 (selectPrev ids lv_32_0_4) 5
private def d31 : List NodeSpec := [([(0,3,1),(3,4,0),(1,5,6)],[0,7,1,2,3,4],[(5,[])]),([(0,3,1),(1,4,2),(0,6,5)],[0,7,1,2,3,6],[(0,[]),(1,[1]),(3,[])]),([(0,3,1),(1,4,2),(2,6,5)],[7,0,1,2,3,6],[(0,[]),(3,[])]),([(0,3,1),(1,4,2),(0,6,1)],[0,5,7,2,3,6],[(4,[1]),(5,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q31 : ck31 [18,22] d31 = true := by decide +kernel
private def d32 : List NodeSpec := [([(0,3,1),(1,4,2),(2,6,5)],[7,0,1,2,3,4],[(3,[])]),([(1,3,1),(1,4,0),(0,6,1)],[0,7,2,3,5,4],[(6,[])]),([(1,3,1),(1,4,0),(0,6,5)],[0,1,2,3,7,4],[]),([(1,3,1),(3,4,0),(2,5,6)],[0,1,2,3,7,4],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q32 : ck31 [21] d32 = true := by decide +kernel
private def d33 : List NodeSpec := [([(2,3,1),(1,4,0),(2,6,5)],[0,1,7,2,3,4],[]),([(2,3,1),(3,4,0),(1,5,6)],[7,0,1,2,3,4],[]),([(2,3,1),(3,4,0),(2,1,6)],[5,0,7,2,3,4],[]),([(1,4,0),(0,5,1),(1,2,6)],[0,1,2,7,3,4],[(4,[]),(5,[]),(8,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q33 : ck31 [] d33 = true := by decide +kernel
private def lv_32_0_5_7 : List NodeSpec := (d31 ++ (d32 ++ d33))

private theorem ok_32_0_5_7 : LevelOK rd_32_0 (subGoal 32 0) 5 lv_32_0_5_7 := by
  have go {ids ds} (h : ck31 ids ds = true) : LevelOK rd_32_0 (subGoal 32 0) 5 ds :=
    levelCheck_sound pp_32_0 (raw_faithful _ _ _) sl_32_0_ok autos_32_0_ok (selectPrevOK ids ok_32_0_4) h
  exact (levelOK_append (go q31) (levelOK_append (go q32) (go q33)))
private def lv_32_0_5_8 : List NodeSpec := [([(3, 4, 0), (2, 1, 5), (1, 2, 6)], [0, 1, 2, 7, 3, 4], []), ([(3, 4, 1), (2, 3, 5), (1, 6, 2)], [0, 1, 2, 3, 7, 4], [(2, [])]), ([(1, 4, 2), (0, 5, 1), (2, 3, 6)], [7, 0, 1, 2, 3, 5], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_32_0_5_8 : LevelOK rd_32_0 (subGoal 32 0) 5 lv_32_0_5_8 :=
  levelCheck_sound pp_32_0 (raw_faithful _ _ _) sl_32_0_ok autos_32_0_ok (selectPrevOK [] ok_32_0_4)
    (by decide +kernel : levelCheck (freeVars 32 0) rd_32_0 (subGoal 32 0) sl_32_0 autos_32_0 (selectPrev [] lv_32_0_4) 5 lv_32_0_5_8 = true)
private def lv_32_0_5 : List NodeSpec := (((lv_32_0_5_0 ++ lv_32_0_5_1) ++ (lv_32_0_5_2 ++ lv_32_0_5_3)) ++ ((lv_32_0_5_4 ++ lv_32_0_5_5) ++ (lv_32_0_5_6 ++ (lv_32_0_5_7 ++ lv_32_0_5_8))))
private theorem ok_32_0_5 : LevelOK rd_32_0 (subGoal 32 0) 5 lv_32_0_5 := (levelOK_append (levelOK_append (levelOK_append ok_32_0_5_0 ok_32_0_5_1) (levelOK_append ok_32_0_5_2 ok_32_0_5_3)) (levelOK_append (levelOK_append ok_32_0_5_4 ok_32_0_5_5) (levelOK_append ok_32_0_5_6 (levelOK_append ok_32_0_5_7 ok_32_0_5_8))))
private def ck34 (ids : List Nat) := levelCheck (freeVars 32 0) rd_32_0 (subGoal 32 0) sl_32_0 autos_32_0 (selectPrev ids lv_32_0_5) 6
private def d34 : List NodeSpec := [([(0,1,0),(2,1,5)],[6,0,1,2,3,4],[(0,[]),(0,[0]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[])]),([(0,1,0),(1,2,5)],[0,1,2,6,3,4],[(0,[]),(1,[]),(2,[]),(2,[1]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[]),(10,[])]),([(0,1,0),(2,3,5)],[6,0,1,2,3,4],[(0,[]),(1,[]),(2,[]),(3,[]),(5,[]),(6,[]),(8,[]),(10,[])]),([(0,1,0),(1,3,2)],[5,0,1,2,3,6,4],[(1,[]),(2,[]),(3,[]),(4,[]),(6,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q34 : ck34 [0,1,2,3,4] d34 = true := by decide +kernel
private def d35 : List NodeSpec := [([(0,1,0),(2,3,2)],[6,5,0,1,2,3,4],[(1,[]),(4,[]),(8,[]),(9,[])]),([(0,1,0),(2,4,2)],[6,5,0,1,2,3],[(0,[]),(0,[0]),(1,[1]),(2,[1]),(3,[]),(4,[1]),(7,[])]),([(1,1,0),(1,3,0)],[0,1,5,2,3,6,4],[(0,[0]),(0,[1]),(1,[]),(2,[]),(4,[]),(10,[])]),([(1,1,0),(2,3,0)],[6,0,1,5,2,3,4],[(0,[1]),(2,[]),(4,[]),(6,[]),(8,[]),(10,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q35 : ck34 [3,5,6,7,8,9] d35 = true := by decide +kernel
private def d36 : List NodeSpec := [([(1,1,0),(0,3,1)],[0,6,5,2,3,4],[(1,[]),(2,[]),(3,[1]),(4,[]),(5,[0]),(6,[]),(7,[])]),([(1,1,0),(0,3,5)],[0,1,6,2,3,4],[(0,[]),(1,[]),(2,[]),(3,[]),(5,[]),(6,[]),(7,[]),(8,[])]),([(1,1,0),(3,4,5)],[6,0,1,2,3],[(0,[0]),(1,[1]),(2,[]),(5,[]),(7,[]),(10,[])]),([(2,1,0),(1,2,5)],[0,1,2,6,3,4],[(0,[]),(1,[]),(2,[]),(2,[1]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q36 : ck34 [5,6,7,9,10,11] d36 = true := by decide +kernel
private def lv_32_0_6_0 : List NodeSpec := (d34 ++ (d35 ++ d36))

private theorem ok_32_0_6_0 : LevelOK rd_32_0 (subGoal 32 0) 6 lv_32_0_6_0 := by
  have go {ids ds} (h : ck34 ids ds = true) : LevelOK rd_32_0 (subGoal 32 0) 6 ds :=
    levelCheck_sound pp_32_0 (raw_faithful _ _ _) sl_32_0_ok autos_32_0_ok (selectPrevOK ids ok_32_0_5) h
  exact (levelOK_append (go q34) (levelOK_append (go q35) (go q36)))
private def ck37 (ids : List Nat) := levelCheck (freeVars 32 0) rd_32_0 (subGoal 32 0) sl_32_0 autos_32_0 (selectPrev ids lv_32_0_5) 6
private def d37 : List NodeSpec := [([(2,1,0),(1,2,5)],[5,0,1,2,6,3,4],[(1,[]),(2,[]),(2,[1]),(3,[]),(6,[])]),([(2,1,0),(3,2,5)],[6,0,1,2,3,4],[(0,[]),(2,[1]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[])]),([(2,1,0),(1,2,0)],[5,0,1,2,6,3,4],[(2,[]),(2,[1]),(3,[]),(6,[]),(10,[])]),([(2,1,0),(1,2,1)],[5,0,2,6,3,4],[(1,[]),(2,[]),(3,[]),(4,[1]),(5,[0]),(6,[]),(7,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q37 : ck37 [11,12,13,14] d37 = true := by decide +kernel
private def d38 : List NodeSpec := [([(2,1,0),(3,2,1)],[6,5,0,2,3,4],[(1,[]),(2,[]),(3,[]),(4,[1]),(5,[0]),(6,[]),(7,[])]),([(2,1,0),(0,3,5)],[6,0,1,2,3,4],[(0,[]),(3,[]),(5,[]),(6,[]),(8,[])]),([(2,1,0),(1,3,5)],[5,0,1,2,3,6,4],[(1,[]),(2,[]),(4,[]),(6,[]),(8,[])]),([(2,1,0),(2,3,5)],[0,6,1,2,3,4],[(0,[]),(0,[0,1]),(1,[]),(2,[]),(3,[]),(5,[]),(6,[]),(8,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q38 : ck37 [7,8,15,16,17,18,19,20,21] d38 = true := by decide +kernel
private def d39 : List NodeSpec := [([(2,1,0),(2,3,5)],[5,0,6,1,2,3,4],[(1,[]),(2,[]),(4,[]),(6,[])]),([(2,1,0),(2,3,0)],[5,6,0,1,2,3,4],[(2,[]),(4,[]),(6,[]),(8,[])]),([(2,1,0),(0,3,1)],[5,0,6,2,3,4],[(1,[]),(2,[]),(3,[1]),(4,[]),(5,[0]),(6,[]),(7,[])]),([(2,1,0),(2,3,1)],[6,5,0,2,3,4],[(1,[]),(2,[]),(3,[1]),(4,[]),(5,[0]),(6,[]),(7,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q39 : ck37 [9,22,23,24,25,26] d39 = true := by decide +kernel
private def lv_32_0_6_1 : List NodeSpec := (d37 ++ (d38 ++ d39))

private theorem ok_32_0_6_1 : LevelOK rd_32_0 (subGoal 32 0) 6 lv_32_0_6_1 := by
  have go {ids ds} (h : ck37 ids ds = true) : LevelOK rd_32_0 (subGoal 32 0) 6 ds :=
    levelCheck_sound pp_32_0 (raw_faithful _ _ _) sl_32_0_ok autos_32_0_ok (selectPrevOK ids ok_32_0_5) h
  exact (levelOK_append (go q37) (levelOK_append (go q38) (go q39)))
private def ck40 (ids : List Nat) := levelCheck (freeVars 32 0) rd_32_0 (subGoal 32 0) sl_32_0 autos_32_0 (selectPrev ids lv_32_0_5) 6
private def d40 : List NodeSpec := [([(2,1,0),(1,3,2)],[5,0,1,2,3,6,4],[(2,[]),(4,[]),(6,[]),(7,[])]),([(2,1,0),(2,3,2)],[6,5,0,1,2,3,4],[(2,[]),(4,[]),(6,[]),(7,[]),(8,[]),(9,[])]),([(2,1,0),(1,4,2)],[5,0,1,2,3,6],[(0,[0]),(1,[1]),(2,[1]),(3,[]),(4,[1]),(5,[]),(5,[0]),(7,[]),(10,[])]),([(2,1,0),(2,4,2)],[6,5,0,1,2,3],[(0,[]),(0,[0]),(1,[1]),(2,[1]),(3,[]),(4,[1]),(7,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q40 : ck40 [16,17,19,20,21,24,25,27] d40 = true := by decide +kernel
private def d41 : List NodeSpec := [([(3,1,0),(1,3,5)],[0,1,2,6,4],[(0,[0,1]),(1,[]),(2,[]),(4,[]),(7,[])]),([(3,1,0),(2,3,5)],[0,1,6,2,4],[(0,[0,1]),(1,[]),(2,[]),(7,[]),(8,[]),(10,[])]),([(3,1,0),(2,3,5)],[0,1,6,2,3,4],[(0,[]),(0,[0,1]),(1,[]),(2,[]),(3,[]),(5,[]),(7,[]),(8,[]),(10,[])]),([(0,2,0),(1,1,5)],[0,6,2,3,4],[(0,[0,1]),(1,[]),(2,[]),(3,[]),(9,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q41 : ck40 [] d41 = true := by decide +kernel
private def d42 : List NodeSpec := [([(0,2,0),(2,1,5)],[6,0,2,3,4],[(0,[0,1]),(1,[]),(3,[]),(6,[]),(7,[]),(9,[])]),([(0,2,0),(1,4,5)],[0,1,2,3,6],[(0,[]),(0,[0]),(1,[]),(3,[]),(5,[]),(7,[])]),([(1,2,0),(0,5,1)],[0,6,1,2,3,4],[(0,[]),(0,[0,1]),(1,[]),(2,[]),(2,[0]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[])]),([(1,2,0),(0,5,1)],[0,6,1,2,5,3,4],[(1,[]),(2,[]),(3,[]),(6,[]),(7,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q42 : ck40 [28] d42 = true := by decide +kernel
private def lv_32_0_6_2 : List NodeSpec := (d40 ++ (d41 ++ d42))

private theorem ok_32_0_6_2 : LevelOK rd_32_0 (subGoal 32 0) 6 lv_32_0_6_2 := by
  have go {ids ds} (h : ck40 ids ds = true) : LevelOK rd_32_0 (subGoal 32 0) 6 ds :=
    levelCheck_sound pp_32_0 (raw_faithful _ _ _) sl_32_0_ok autos_32_0_ok (selectPrevOK ids ok_32_0_5) h
  exact (levelOK_append (go q40) (levelOK_append (go q41) (go q42)))
private def ck43 (ids : List Nat) := levelCheck (freeVars 32 0) rd_32_0 (subGoal 32 0) sl_32_0 autos_32_0 (selectPrev ids lv_32_0_5) 6
private def d43 : List NodeSpec := [([(1,2,0),(3,5,1)],[6,0,1,2,5,3,4],[(2,[]),(6,[]),(7,[])]),([(1,2,0),(0,3,1)],[0,6,1,2,5,3,4],[(1,[]),(2,[]),(3,[]),(4,[]),(6,[]),(7,[]),(8,[]),(9,[])]),([(1,2,0),(1,4,2)],[0,1,5,3,6],[(0,[]),(0,[0]),(1,[1]),(3,[]),(5,[0]),(7,[]),(9,[]),(10,[])]),([(1,2,0),(1,4,2)],[0,1,2,5,3,6],[(0,[]),(0,[0]),(1,[1]),(2,[1]),(3,[]),(4,[1]),(5,[]),(7,[]),(9,[]),(10,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q43 : ck43 [11,28,29,30,31,32,33,34] d43 = true := by decide +kernel
private def d44 : List NodeSpec := [([(1,2,0),(2,4,2)],[6,0,1,2,5,3],[(0,[]),(0,[0]),(1,[1]),(2,[1]),(3,[]),(4,[1]),(7,[]),(9,[]),(10,[])]),([(2,2,0),(1,0,5)],[0,1,2,6,3,4],[(0,[]),(0,[0]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[]),(9,[]),(10,[])]),([(2,2,0),(1,4,5)],[0,1,2,3,6],[(0,[]),(0,[0]),(1,[1]),(3,[]),(5,[]),(7,[]),(9,[])]),([(2,2,0),(1,4,2)],[5,0,1,3,6],[(1,[1]),(3,[]),(5,[0]),(7,[]),(9,[]),(10,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q44 : ck43 [] d44 = true := by decide +kernel
private def d45 : List NodeSpec := [([(3,2,0),(2,1,5)],[0,6,1,2,3,4],[(0,[]),(1,[]),(2,[]),(2,[0]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[])]),([(3,2,0),(0,3,1)],[5,0,6,1,2,3,4],[(1,[]),(2,[]),(4,[]),(6,[]),(7,[]),(8,[]),(9,[])]),([(3,2,0),(2,4,2)],[5,6,0,1,2,3],[(0,[]),(0,[0]),(1,[1]),(2,[1]),(3,[]),(4,[1]),(7,[]),(9,[])]),([(0,2,1),(1,5,0)],[1,6,2,3,4],[(0,[0,1]),(2,[1]),(3,[]),(6,[]),(7,[]),(9,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q45 : ck43 [35,36,37,38] d45 = true := by decide +kernel
private def lv_32_0_6_3 : List NodeSpec := (d43 ++ (d44 ++ d45))

private theorem ok_32_0_6_3 : LevelOK rd_32_0 (subGoal 32 0) 6 lv_32_0_6_3 := by
  have go {ids ds} (h : ck43 ids ds = true) : LevelOK rd_32_0 (subGoal 32 0) 6 ds :=
    levelCheck_sound pp_32_0 (raw_faithful _ _ _) sl_32_0_ok autos_32_0_ok (selectPrevOK ids ok_32_0_5) h
  exact (levelOK_append (go q43) (levelOK_append (go q44) (go q45)))
private def ck46 (ids : List Nat) := levelCheck (freeVars 32 0) rd_32_0 (subGoal 32 0) sl_32_0 autos_32_0 (selectPrev ids lv_32_0_5) 6
private def d46 : List NodeSpec := [([(0,2,1),(1,5,0)],[0,1,6,2,3,4],[(0,[]),(0,[0,1]),(1,[]),(2,[]),(2,[1]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[]),(9,[])]),([(0,2,1),(3,5,0)],[6,1,2,3,4],[(0,[0,1]),(1,[]),(2,[1]),(3,[]),(6,[]),(9,[])]),([(0,2,1),(1,3,5)],[0,1,2,6,4],[(0,[0,1]),(2,[1]),(3,[]),(4,[]),(6,[])]),([(0,2,1),(2,3,5)],[6,0,1,2,4],[(0,[0,1]),(2,[1]),(3,[]),(6,[]),(8,[]),(9,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q46 : ck46 [39,40,41,42,43,44] d46 = true := by decide +kernel
private def d47 : List NodeSpec := [([(0,2,1),(1,4,0)],[0,5,1,2,3,4,6],[(0,[]),(1,[]),(2,[]),(3,[]),(5,[]),(6,[])]),([(0,2,1),(3,4,0)],[6,0,5,1,2,3,4],[(0,[]),(1,[]),(3,[]),(5,[])]),([(0,2,1),(1,4,5)],[0,1,2,3,6],[(0,[]),(0,[0]),(2,[1]),(3,[]),(5,[]),(6,[]),(9,[])]),([(1,2,1),(2,5,0)],[6,0,1,2,3,4],[(0,[]),(0,[0,1]),(1,[]),(2,[]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q47 : ck46 [39,40,41,42,43,44,45,46] d47 = true := by decide +kernel
private def d48 : List NodeSpec := [([(1,2,1),(0,3,5)],[0,1,2,6,4],[(0,[0,1]),(2,[]),(3,[1]),(7,[]),(8,[]),(9,[])]),([(1,2,1),(0,3,5)],[0,1,2,6,3,4],[(0,[]),(0,[0,1]),(1,[]),(2,[]),(3,[]),(3,[1]),(4,[0]),(5,[]),(6,[]),(7,[]),(8,[]),(9,[])]),([(1,2,1),(3,3,5)],[6,0,1,2,4],[(0,[0,1]),(2,[]),(3,[1]),(4,[]),(7,[])]),([(1,2,1),(1,4,0)],[0,1,2,5,3,4,6],[(2,[]),(5,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q48 : ck46 [13,14,47,48,49,50,51,52,53,54,55] d48 = true := by decide +kernel
private def lv_32_0_6_4 : List NodeSpec := (d46 ++ (d47 ++ d48))

private theorem ok_32_0_6_4 : LevelOK rd_32_0 (subGoal 32 0) 6 lv_32_0_6_4 := by
  have go {ids ds} (h : ck46 ids ds = true) : LevelOK rd_32_0 (subGoal 32 0) 6 ds :=
    levelCheck_sound pp_32_0 (raw_faithful _ _ _) sl_32_0_ok autos_32_0_ok (selectPrevOK ids ok_32_0_5) h
  exact (levelOK_append (go q46) (levelOK_append (go q47) (go q48)))
private def ck49 (ids : List Nat) := levelCheck (freeVars 32 0) rd_32_0 (subGoal 32 0) sl_32_0 autos_32_0 (selectPrev ids lv_32_0_5) 6
private def d49 : List NodeSpec := [([(1,2,1),(3,4,0)],[6,0,1,2,5,3,4],[(0,[]),(1,[]),(2,[]),(5,[])]),([(1,2,1),(3,4,3)],[6,0,1,2,5,3,4],[(2,[]),(4,[]),(5,[]),(8,[])]),([(2,2,1),(1,0,5)],[0,6,1,2,3,4],[(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(8,[]),(9,[])]),([(2,2,1),(1,4,5)],[0,1,2,3,6],[(0,[]),(0,[0]),(2,[]),(3,[]),(5,[]),(9,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q49 : ck49 [50,54,56,57,58,59] d49 = true := by decide +kernel
private def d50 : List NodeSpec := [([(2,2,1),(1,4,0)],[5,0,1,2,3,4,6],[(0,[]),(2,[]),(5,[])]),([(2,2,1),(3,4,0)],[6,5,0,1,2,3,4],[(0,[]),(1,[]),(2,[]),(5,[])]),([(3,2,1),(0,3,5)],[6,0,1,2,3,4],[(0,[]),(1,[]),(2,[1]),(3,[1]),(4,[0]),(5,[]),(6,[]),(7,[]),(8,[]),(9,[])]),([(3,2,1),(1,4,0)],[5,0,1,2,3,4,6],[(5,[]),(6,[]),(7,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q50 : ck49 [60,61,62,63] d50 = true := by decide +kernel
private def d51 : List NodeSpec := [([(3,2,1),(3,4,0)],[6,5,0,1,2,3,4],[(0,[]),(1,[]),(2,[]),(5,[]),(6,[]),(7,[])]),([(3,2,1),(3,4,3)],[6,5,0,1,2,3,4],[(2,[]),(5,[]),(6,[]),(7,[])]),([(0,3,1),(1,5,0)],[0,1,6,2,3,4],[(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(8,[])]),([(0,3,1),(1,5,0)],[0,5,1,6,2,3,4],[(0,[0]),(1,[]),(2,[]),(4,[]),(6,[]),(8,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q51 : ck49 [30,32,36,64,65,66,67,68,69,70,71,72] d51 = true := by decide +kernel
private def lv_32_0_6_5 : List NodeSpec := (d49 ++ (d50 ++ d51))

private theorem ok_32_0_6_5 : LevelOK rd_32_0 (subGoal 32 0) 6 lv_32_0_6_5 := by
  have go {ids ds} (h : ck49 ids ds = true) : LevelOK rd_32_0 (subGoal 32 0) 6 ds :=
    levelCheck_sound pp_32_0 (raw_faithful _ _ _) sl_32_0_ok autos_32_0_ok (selectPrevOK ids ok_32_0_5) h
  exact (levelOK_append (go q49) (levelOK_append (go q50) (go q51)))
private def ck52 (ids : List Nat) := levelCheck (freeVars 32 0) rd_32_0 (subGoal 32 0) sl_32_0 autos_32_0 (selectPrev ids lv_32_0_5) 6
private def d52 : List NodeSpec := [([(0,3,1),(3,5,0)],[6,0,5,1,2,3,4],[(1,[]),(2,[]),(4,[]),(6,[]),(8,[])]),([(0,3,1),(1,2,5)],[0,1,2,6,3,4],[(0,[]),(1,[]),(2,[]),(2,[1]),(3,[]),(3,[0]),(4,[]),(4,[1]),(5,[]),(6,[]),(7,[]),(8,[]),(9,[])]),([(0,3,1),(1,2,5)],[0,5,1,2,6,3,4],[(2,[]),(2,[1]),(3,[]),(3,[0]),(4,[]),(4,[1]),(6,[]),(7,[])]),([(0,3,1),(1,3,1)],[0,5,2,6,4],[(0,[0,1]),(2,[]),(3,[0]),(6,[]),(7,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q52 : ck52 [7,23,31,32,71,73,74,75,76,77,78,79,80,81,82] d52 = true := by decide +kernel
private def d53 : List NodeSpec := [([(0,3,1),(1,4,0)],[0,5,1,2,3,4,6],[(0,[]),(1,[]),(5,[]),(6,[])]),([(0,3,1),(3,4,0)],[6,0,5,1,2,3,4],[(0,[]),(1,[]),(2,[]),(4,[]),(5,[]),(6,[]),(8,[])]),([(0,3,1),(1,4,5)],[0,5,1,2,3,4,6],[(0,[]),(0,[0]),(5,[])]),([(0,3,1),(1,4,2)],[0,5,1,2,3,6],[(0,[0]),(1,[1]),(2,[1]),(3,[]),(3,[0]),(4,[1]),(5,[]),(7,[]),(9,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q53 : ck52 [16,24,34,65,66,69,75,77,80,81,82,83,84,85,86,87] d53 = true := by decide +kernel
private def d54 : List NodeSpec := [([(0,3,1),(1,4,2)],[0,5,1,2,3,4,6],[(0,[]),(0,[0]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[])]),([(0,3,1),(2,4,2)],[6,0,5,1,2,3],[(0,[]),(0,[0]),(1,[1]),(2,[1]),(3,[]),(3,[0]),(4,[1]),(7,[]),(9,[])]),([(1,3,1),(2,5,0)],[6,0,1,2,3,4],[(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(7,[])]),([(1,3,1),(1,4,0)],[0,1,2,3,5,4,6],[(2,[]),(4,[]),(5,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q54 : ck52 [17,25,70,76,78,80,88,89,90] d54 = true := by decide +kernel
private def lv_32_0_6_6 : List NodeSpec := (d52 ++ (d53 ++ d54))

private theorem ok_32_0_6_6 : LevelOK rd_32_0 (subGoal 32 0) 6 lv_32_0_6_6 := by
  have go {ids ds} (h : ck52 ids ds = true) : LevelOK rd_32_0 (subGoal 32 0) 6 ds :=
    levelCheck_sound pp_32_0 (raw_faithful _ _ _) sl_32_0_ok autos_32_0_ok (selectPrevOK ids ok_32_0_5) h
  exact (levelOK_append (go q52) (levelOK_append (go q53) (go q54)))
private def ck55 (ids : List Nat) := levelCheck (freeVars 32 0) rd_32_0 (subGoal 32 0) sl_32_0 autos_32_0 (selectPrev ids lv_32_0_5) 6
private def d55 : List NodeSpec := [([(1,3,1),(3,4,0)],[6,0,1,2,3,5,4],[(0,[]),(1,[]),(2,[]),(5,[])]),([(2,3,1),(1,0,5)],[0,6,1,2,3,4],[(0,[]),(0,[0,1]),(1,[]),(2,[]),(3,[]),(5,[]),(6,[]),(7,[]),(8,[])]),([(2,3,1),(2,3,5)],[0,6,1,2,3,4],[(0,[]),(0,[0]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[])]),([(2,3,1),(1,4,0)],[5,0,1,2,3,4,6],[(2,[]),(4,[]),(5,[]),(8,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q55 : ck55 [7,81,91,92] d55 = true := by decide +kernel
private def d56 : List NodeSpec := [([(2,3,1),(3,4,0)],[6,5,0,1,2,3,4],[(0,[]),(1,[]),(2,[]),(5,[])]),([(1,4,0),(0,5,1)],[0,6,1,2,3,4],[(0,[]),(0,[1]),(1,[]),(1,[1]),(3,[]),(4,[]),(5,[]),(6,[]),(8,[]),(10,[])]),([(1,4,0),(2,5,2)],[6,0,1,2,3,4],[(0,[]),(0,[1]),(1,[]),(1,[1]),(2,[]),(4,[]),(5,[]),(6,[]),(8,[]),(10,[])]),([(3,4,0),(2,1,5)],[0,6,1,2,3,4],[(0,[]),(0,[1]),(1,[]),(3,[]),(4,[]),(5,[]),(6,[]),(8,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q56 : ck55 [56,61,89,93,94,95,96] d56 = true := by decide +kernel
private def d57 : List NodeSpec := [([(3,4,0),(1,2,5)],[0,1,2,6,3,4],[(0,[]),(0,[1]),(1,[]),(2,[]),(4,[]),(5,[]),(6,[]),(8,[])]),([(1,4,1),(0,5,3)],[0,1,2,6,3,4],[(0,[]),(0,[1]),(1,[]),(2,[]),(3,[]),(5,[]),(7,[]),(8,[]),(10,[])]),([(3,4,1),(1,2,5)],[0,1,2,6,3,4],[(0,[]),(0,[1]),(1,[]),(2,[]),(2,[1]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[]),(10,[])]),([(3,4,1),(2,3,5)],[0,1,2,6,3,4],[(0,[]),(0,[1]),(1,[]),(2,[]),(3,[]),(5,[]),(6,[]),(8,[]),(10,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q57 : ck55 [58,97] d57 = true := by decide +kernel
private def lv_32_0_6_7 : List NodeSpec := (d55 ++ (d56 ++ d57))

private theorem ok_32_0_6_7 : LevelOK rd_32_0 (subGoal 32 0) 6 lv_32_0_6_7 := by
  have go {ids ds} (h : ck55 ids ds = true) : LevelOK rd_32_0 (subGoal 32 0) 6 ds :=
    levelCheck_sound pp_32_0 (raw_faithful _ _ _) sl_32_0_ok autos_32_0_ok (selectPrevOK ids ok_32_0_5) h
  exact (levelOK_append (go q55) (levelOK_append (go q56) (go q57)))
private def lv_32_0_6_8 : List NodeSpec := [([(1, 4, 2), (0, 5, 1)], [0, 6, 1, 2, 3, 5], [(0, []), (0, [1]), (1, [0]), (2, [0]), (3, []), (4, [0]), (5, []), (7, []), (10, [])]), ([(1, 4, 2), (0, 5, 1)], [0, 6, 1, 2, 3, 4], [(0, []), (0, [1]), (1, []), (2, []), (2, [0]), (3, []), (4, []), (5, []), (6, []), (7, []), (8, []), (10, [])]), ([(2, 4, 2), (1, 2, 5)], [0, 1, 2, 3, 6], [(0, []), (3, []), (5, []), (7, []), (9, []), (10, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_32_0_6_8 : LevelOK rd_32_0 (subGoal 32 0) 6 lv_32_0_6_8 :=
  levelCheck_sound pp_32_0 (raw_faithful _ _ _) sl_32_0_ok autos_32_0_ok (selectPrevOK [85,87,98] ok_32_0_5)
    (by decide +kernel : levelCheck (freeVars 32 0) rd_32_0 (subGoal 32 0) sl_32_0 autos_32_0 (selectPrev [85,87,98] lv_32_0_5) 6 lv_32_0_6_8 = true)
private def lv_32_0_6 : List NodeSpec := (((lv_32_0_6_0 ++ lv_32_0_6_1) ++ (lv_32_0_6_2 ++ lv_32_0_6_3)) ++ ((lv_32_0_6_4 ++ lv_32_0_6_5) ++ (lv_32_0_6_6 ++ (lv_32_0_6_7 ++ lv_32_0_6_8))))
private theorem ok_32_0_6 : LevelOK rd_32_0 (subGoal 32 0) 6 lv_32_0_6 := (levelOK_append (levelOK_append (levelOK_append ok_32_0_6_0 ok_32_0_6_1) (levelOK_append ok_32_0_6_2 ok_32_0_6_3)) (levelOK_append (levelOK_append ok_32_0_6_4 ok_32_0_6_5) (levelOK_append ok_32_0_6_6 (levelOK_append ok_32_0_6_7 ok_32_0_6_8))))
private def ck58 (ids : List Nat) := levelCheck (freeVars 32 0) rd_32_0 (subGoal 32 0) sl_32_0 autos_32_0 (selectPrev ids lv_32_0_6) 7
private def d58 : List NodeSpec := [([(0,1,0)],[5,0,1,2,3,4],[(0,[]),(0,[0]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(10,[])]),([(1,1,0)],[0,1,5,2,3,4],[(0,[]),(0,[0]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(7,[]),(10,[])]),([(2,1,0)],[5,0,1,2,3,4],[(0,[]),(0,[0]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(10,[])]),([(3,1,0)],[5,0,1,2,3,4],[(0,[]),(0,[0]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(7,[]),(10,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q58 : ck58 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30] d58 = true := by decide +kernel
private def d59 : List NodeSpec := [([(0,2,0)],[5,0,1,2,3,4],[(0,[]),(0,[0]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(7,[]),(9,[])]),([(1,2,0)],[0,1,2,5,3,4],[(0,[]),(0,[0]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(7,[]),(9,[]),(10,[])]),([(2,2,0)],[5,0,1,2,3,4],[(0,[]),(0,[0]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(7,[]),(9,[]),(10,[])]),([(3,2,0)],[5,0,1,2,3,4],[(0,[]),(0,[0]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(7,[]),(9,[]),(10,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q59 : ck58 [13,14,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46] d59 = true := by decide +kernel
private def d60 : List NodeSpec := [([(0,2,1)],[0,5,1,2,3,4],[(0,[]),(0,[0]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(9,[])]),([(1,2,1)],[0,1,2,5,3,4],[(0,[]),(0,[0]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(7,[]),(9,[])]),([(2,2,1)],[5,0,1,2,3,4],[(0,[]),(0,[0]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(9,[])]),([(3,2,1)],[5,0,1,2,3,4],[(0,[]),(0,[0]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(9,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q60 : ck58 [3,4,13,15,16,24,25,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69] d60 = true := by decide +kernel
private def lv_32_0_7_0 : List NodeSpec := (d58 ++ (d59 ++ d60))

private theorem ok_32_0_7_0 : LevelOK rd_32_0 (subGoal 32 0) 7 lv_32_0_7_0 := by
  have go {ids ds} (h : ck58 ids ds = true) : LevelOK rd_32_0 (subGoal 32 0) 7 ds :=
    levelCheck_sound pp_32_0 (raw_faithful _ _ _) sl_32_0_ok autos_32_0_ok (selectPrevOK ids ok_32_0_6) h
  exact (levelOK_append (go q58) (levelOK_append (go q59) (go q60)))
private def ck61 (ids : List Nat) := levelCheck (freeVars 32 0) rd_32_0 (subGoal 32 0) sl_32_0 autos_32_0 (selectPrev ids lv_32_0_6) 7
private def d61 : List NodeSpec := [([(0,3,1)],[0,5,1,2,3,4],[(0,[]),(0,[0]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[]),(9,[])]),([(1,3,1)],[0,1,2,3,5,4],[(0,[]),(0,[0]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(7,[])]),([(2,3,1)],[5,0,1,2,3,4],[(0,[]),(0,[0]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(7,[]),(8,[])]),([(1,4,0)],[0,1,2,3,4,5],[(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(10,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q61 : ck61 [8,17,22,23,37,45,52,59,64,66,67,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90] d61 = true := by decide +kernel
private def d62 : List NodeSpec := [([(3,4,0)],[5,0,1,2,3,4],[(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[])]),([(1,4,1)],[0,1,2,3,4,5],[(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(7,[]),(10,[])]),([(3,4,1)],[5,0,1,2,3,4],[(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(10,[])]),([(1,4,2)],[0,1,2,3,5],[(0,[]),(3,[]),(5,[]),(7,[]),(9,[]),(10,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q62 : ck61 [26,38,39,43,53,60,61,65,68,69,77,79,84,88,91,92,93,94,95,96] d62 = true := by decide +kernel
private def d63 : List NodeSpec := [([(1,4,2)],[0,1,2,3,4,5],[(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(7,[]),(9,[]),(10,[])]),([(2,4,2)],[5,0,1,2,3],[(0,[]),(3,[]),(7,[]),(9,[])]),([(3,4,2)],[5,0,1,2,3,4],[(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(7,[]),(9,[]),(10,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q63 : ck61 [5,27,40,46,80,81,97,98] d63 = true := by decide +kernel
private def lv_32_0_7_1 : List NodeSpec := (d61 ++ (d62 ++ d63))

private theorem ok_32_0_7_1 : LevelOK rd_32_0 (subGoal 32 0) 7 lv_32_0_7_1 := by
  have go {ids ds} (h : ck61 ids ds = true) : LevelOK rd_32_0 (subGoal 32 0) 7 ds :=
    levelCheck_sound pp_32_0 (raw_faithful _ _ _) sl_32_0_ok autos_32_0_ok (selectPrevOK ids ok_32_0_6) h
  exact (levelOK_append (go q61) (levelOK_append (go q62) (go q63)))
private def lv_32_0_7 : List NodeSpec := (lv_32_0_7_0 ++ lv_32_0_7_1)
private theorem ok_32_0_7 : LevelOK rd_32_0 (subGoal 32 0) 7 lv_32_0_7 := (levelOK_append ok_32_0_7_0 ok_32_0_7_1)
private def lv_32_0_8_0 : List NodeSpec := [([], [0, 1, 2, 3, 4], [(0, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_32_0_8_0 : LevelOK rd_32_0 (subGoal 32 0) 8 lv_32_0_8_0 :=
  levelCheck_sound pp_32_0 (raw_faithful _ _ _) sl_32_0_ok autos_32_0_ok (selectPrevOK [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22] ok_32_0_7)
    (by decide +kernel : levelCheck (freeVars 32 0) rd_32_0 (subGoal 32 0) sl_32_0 autos_32_0 (selectPrev [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22] lv_32_0_7) 8 lv_32_0_8_0 = true)
private def lv_32_0_8 : List NodeSpec := lv_32_0_8_0
private theorem ok_32_0_8 : LevelOK rd_32_0 (subGoal 32 0) 8 lv_32_0_8 := ok_32_0_8_0
private theorem lower_32_0 : Lower (freeVars 32 0) (subGoal 32 0) 9 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 4, 5), (inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 1, 5), (inputs.getD 3 zero, 3, 11), (inputs.getD 4 zero, 1, 17)]) ok_32_0_8 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube32_0

section Cube5_2

private def p_5_2 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 2 => mk128 0x0 0x0
  | 3 => mk128 0xbecfbecfbecfbecf 0xbecfbecfbecfbecf
  | 4 => mk128 0xdf73df73df73df73 0xdf73df73df73df73
  | 5 => mk128 0xefbcefbcefbcefbc 0xefbcefbcefbcefbc
  | _ => 0
private def q_5_2 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 2 => mk128 0x0 0x0
  | 3 => mk128 0x4205420542054205 0x4205420542054205
  | 4 => mk128 0x2412241224122412 0x2412241224122412
  | 5 => mk128 0x1828182818281828 0x1828182818281828
  | _ => 0
private theorem pp_5_2 : properPairs (subGoal 5 2) (asRow p_5_2) (asRow q_5_2) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_5_2 : List Decor := rawDecor (freeMask 5 2) p_5_2 q_5_2
private def sl_5_2 : List (Sig × Nat) := []
private theorem sl_5_2_ok : ∀ s ∈ sl_5_2, Slice (freeVars 5 2) (subGoal 5 2) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private def autos_5_2 : List (List Move) := [[], [swapRows 84], [swapRows 67], [swapRows 67, swapRows 84], [swapRows 83, swapRows 84], [swapRows 83]]
private theorem autos_5_2_ok : ∀ m ∈ autos_5_2, autoOK (subGoal 5 2) m = true := by
  intro m hm
  simp only [autos_5_2, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
private def lv_5_2_3_0 : List NodeSpec := [([], [0, 1, 2], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_5_2_3_0 : LevelOK rd_5_2 (subGoal 5 2) 3 lv_5_2_3_0 :=
  levelCheck_sound pp_5_2 (raw_faithful _ _ _) sl_5_2_ok autos_5_2_ok (emptyLevelOK rd_5_2 (subGoal 5 2) 2)
    (by decide +kernel : levelCheck (freeVars 5 2) rd_5_2 (subGoal 5 2) sl_5_2 autos_5_2 [] 3 lv_5_2_3_0 = true)
private def lv_5_2_3 : List NodeSpec := lv_5_2_3_0
private theorem ok_5_2_3 : LevelOK rd_5_2 (subGoal 5 2) 3 lv_5_2_3 := ok_5_2_3_0
private theorem lower_5_2 : Lower (freeVars 5 2) (subGoal 5 2) 4 :=
  lower_of_search (xs := [(inputs.getD 3 zero, 16, 24), (inputs.getD 4 zero, 8, 24), (inputs.getD 5 zero, 8, 40)]) ok_5_2_3 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube5_2

section Cube1_2

private def p_1_2 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 2 => mk128 0xf1b77c27feaef1b7 0x7c27feaef1b77c27
  | 3 => mk128 0x3e3ba0dabf333e3b 0xa0dabf333e3ba0da
  | 4 => mk128 0xcfc3c31cdfc3cfc3 0xc31cdfc3cfc3c31c
  | 5 => mk128 0xffc03e0effc0ffc 0x3e0effc0ffc03e0
  | _ => 0
private def q_1_2 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 2 => mk128 0x0 0x0
  | 3 => mk128 0x4211044a42444211 0x44a42444211044a
  | 4 => mk128 0x1482091424181482 0x914241814820914
  | 5 => mk128 0xa92012a01801a920 0x12a01801a92012a0
  | _ => 0
private theorem pp_1_2 : properPairs (subGoal 1 2) (asRow p_1_2) (asRow q_1_2) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_1_2 : List Decor := rawDecor (freeMask 1 2) p_1_2 q_1_2
private def sl_1_2 : List (Sig × Nat) := [(subcube 5 2, 4)]
private theorem sl_1_2_ok : ∀ s ∈ sl_1_2, Slice (freeVars 1 2) (subGoal 1 2) s.1 s.2 := by
  intro s hs
  simp only [sl_1_2, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 5 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_5_2
private def autos_1_2 : List (List Move) := [[], [swapRows 84], [swapRows 67], [swapRows 67, swapRows 84], [swapRows 83, swapRows 84], [swapRows 83]]
private theorem autos_1_2_ok : ∀ m ∈ autos_1_2, autoOK (subGoal 1 2) m = true := by
  intro m hm
  simp only [autos_1_2, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
private def lv_1_2_4_0 : List NodeSpec := [([], [0, 1, 2, 3], [(0, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_1_2_4_0 : LevelOK rd_1_2 (subGoal 1 2) 4 lv_1_2_4_0 :=
  levelCheck_sound pp_1_2 (raw_faithful _ _ _) sl_1_2_ok autos_1_2_ok (emptyLevelOK rd_1_2 (subGoal 1 2) 3)
    (by decide +kernel : levelCheck (freeVars 1 2) rd_1_2 (subGoal 1 2) sl_1_2 autos_1_2 [] 4 lv_1_2_4_0 = true)
private def lv_1_2_4 : List NodeSpec := lv_1_2_4_0
private theorem ok_1_2_4 : LevelOK rd_1_2 (subGoal 1 2) 4 lv_1_2_4 := ok_1_2_4_0
private theorem lower_1_2 : Lower (freeVars 1 2) (subGoal 1 2) 5 :=
  lower_of_search (xs := [(inputs.getD 2 zero, 0, 4), (inputs.getD 3 zero, 16, 24), (inputs.getD 4 zero, 8, 24), (inputs.getD 5 zero, 8, 40)]) ok_1_2_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube1_2

section Cube5_0

private def p_5_0 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 2 => mk128 0x0 0x0
  | 3 => mk128 0xffc3fe3fbf0fffc3 0xfe3fbf0fffc3fe3f
  | 4 => mk128 0xfffc3fc7dff0fffc 0x3fc7dff0fffc3fc7
  | 5 => mk128 0xfffc3f8efff0fff 0xc3f8efff0fffc3f8
  | _ => 0
private def q_5_0 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0x22c444db012222c4 0x44db012222c444db
  | 2 => mk128 0x0 0x0
  | 3 => mk128 0x4562aa2d42e44562 0xaa2d42e44562aa2d
  | 4 => mk128 0x89aa3346244e89aa 0x3346244e89aa3346
  | 5 => mk128 0xee3323b01888ee33 0x23b01888ee3323b0
  | _ => 0
private theorem pp_5_0 : properPairs (subGoal 5 0) (asRow p_5_0) (asRow q_5_0) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_5_0 : List Decor := rawDecor (freeMask 5 0) p_5_0 q_5_0
private def sl_5_0 : List (Sig × Nat) := [(subcube 5 2, 4)]
private theorem sl_5_0_ok : ∀ s ∈ sl_5_0, Slice (freeVars 5 0) (subGoal 5 0) s.1 s.2 := by
  intro s hs
  simp only [sl_5_0, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 5 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_5_2
private def autos_5_0 : List (List Move) := [[], [swapRows 84], [swapRows 67], [swapRows 67, swapRows 84], [swapRows 83, swapRows 84], [swapRows 83]]
private theorem autos_5_0_ok : ∀ m ∈ autos_5_0, autoOK (subGoal 5 0) m = true := by
  intro m hm
  simp only [autos_5_0, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
private def lv_5_0_4_0 : List NodeSpec := [([], [0, 1, 2, 3], [(0, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_5_0_4_0 : LevelOK rd_5_0 (subGoal 5 0) 4 lv_5_0_4_0 :=
  levelCheck_sound pp_5_0 (raw_faithful _ _ _) sl_5_0_ok autos_5_0_ok (emptyLevelOK rd_5_0 (subGoal 5 0) 3)
    (by decide +kernel : levelCheck (freeVars 5 0) rd_5_0 (subGoal 5 0) sl_5_0 autos_5_0 [] 4 lv_5_0_4_0 = true)
private def lv_5_0_4 : List NodeSpec := lv_5_0_4_0
private theorem ok_5_0_4 : LevelOK rd_5_0 (subGoal 5 0) 4 lv_5_0_4 := ok_5_0_4_0
private theorem lower_5_0 : Lower (freeVars 5 0) (subGoal 5 0) 5 :=
  lower_of_search (xs := [(inputs.getD 1 zero, 24, 26), (inputs.getD 3 zero, 18, 26), (inputs.getD 4 zero, 10, 26), (inputs.getD 5 zero, 10, 42)]) ok_5_0_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube5_0

section Cube17_32

private def p_17_32 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0xbecfbecfbecfbecf 0xbecfbecfbecfbecf
  | 2 => mk128 0xdf73df73df73df73 0xdf73df73df73df73
  | 3 => mk128 0xefbcefbcefbcefbc 0xefbcefbcefbcefbc
  | 4 => mk128 0x0 0x0
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private def q_17_32 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0x4205420542054205 0x4205420542054205
  | 2 => mk128 0x2412241224122412 0x2412241224122412
  | 3 => mk128 0x1828182818281828 0x1828182818281828
  | 4 => mk128 0x0 0x0
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private theorem pp_17_32 : properPairs (subGoal 17 32) (asRow p_17_32) (asRow q_17_32) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_17_32 : List Decor := rawDecor (freeMask 17 32) p_17_32 q_17_32
private def sl_17_32 : List (Sig × Nat) := []
private theorem sl_17_32_ok : ∀ s ∈ sl_17_32, Slice (freeVars 17 32) (subGoal 17 32) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private def autos_17_32 : List (List Move) := [[], [swapRows 50], [swapRows 33], [swapRows 33, swapRows 50], [swapRows 49, swapRows 50], [swapRows 49]]
private theorem autos_17_32_ok : ∀ m ∈ autos_17_32, autoOK (subGoal 17 32) m = true := by
  intro m hm
  simp only [autos_17_32, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
private def lv_17_32_3_0 : List NodeSpec := [([], [0, 1, 2], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_17_32_3_0 : LevelOK rd_17_32 (subGoal 17 32) 3 lv_17_32_3_0 :=
  levelCheck_sound pp_17_32 (raw_faithful _ _ _) sl_17_32_ok autos_17_32_ok (emptyLevelOK rd_17_32 (subGoal 17 32) 2)
    (by decide +kernel : levelCheck (freeVars 17 32) rd_17_32 (subGoal 17 32) sl_17_32 autos_17_32 [] 3 lv_17_32_3_0 = true)
private def lv_17_32_3 : List NodeSpec := lv_17_32_3_0
private theorem ok_17_32_3 : LevelOK rd_17_32 (subGoal 17 32) 3 lv_17_32_3 := ok_17_32_3_0
private theorem lower_17_32 : Lower (freeVars 17 32) (subGoal 17 32) 4 :=
  lower_of_search (xs := [(inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 3 zero, 2, 10)]) ok_17_32_3 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube17_32

section Cube17_0

private def p_17_0 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0xeef8ff9f8ff879f9 0xddf1ff3f1ff0f3f3
  | 2 => mk128 0xf7ff3ffff1fffe3f 0xeffe7fffe3fffc7f
  | 3 => mk128 0x3b7fc7e7fe3f87ce 0x76ff8fcffc7f0f9c
  | 4 => mk128 0x0 0x0
  | 5 => mk128 0x3c7ff807ffc007f0 0x78fff00fff800fe0
  | _ => 0
private def q_17_0 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0x510e1121824930d8 0xa21c2243049261b1
  | 2 => mk128 0x8810820210924223 0x1021040421248446
  | 3 => mk128 0x4a2340ca425154c 0x9446819484a2a98
  | 4 => mk128 0x0 0x0
  | 5 => mk128 0x3c4a757490667b0 0x7894eae920ccf60
  | _ => 0
private theorem pp_17_0 : properPairs (subGoal 17 0) (asRow p_17_0) (asRow q_17_0) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_17_0 : List Decor := rawDecor (freeMask 17 0) p_17_0 q_17_0
private def sl_17_0 : List (Sig × Nat) := [(subcube 17 32, 4)]
private theorem sl_17_0_ok : ∀ s ∈ sl_17_0, Slice (freeVars 17 0) (subGoal 17 0) s.1 s.2 := by
  intro s hs
  simp only [sl_17_0, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 17 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_17_32
private def autos_17_0 : List (List Move) := [[], [swapRows 49]]
private theorem autos_17_0_ok : ∀ m ∈ autos_17_0, autoOK (subGoal 17 0) m = true := by
  intro m hm
  simp only [autos_17_0, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl <;> decide +kernel
private def lv_17_0_4_0 : List NodeSpec := [([], [0, 1, 2, 3], [(0, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_17_0_4_0 : LevelOK rd_17_0 (subGoal 17 0) 4 lv_17_0_4_0 :=
  levelCheck_sound pp_17_0 (raw_faithful _ _ _) sl_17_0_ok autos_17_0_ok (emptyLevelOK rd_17_0 (subGoal 17 0) 3)
    (by decide +kernel : levelCheck (freeVars 17 0) rd_17_0 (subGoal 17 0) sl_17_0 autos_17_0 [] 4 lv_17_0_4_0 = true)
private def lv_17_0_4 : List NodeSpec := lv_17_0_4_0
private theorem ok_17_0_4 : LevelOK rd_17_0 (subGoal 17 0) 4 lv_17_0_4 := ok_17_0_4_0
private theorem lower_17_0 : Lower (freeVars 17 0) (subGoal 17 0) 5 :=
  lower_of_search (xs := [(inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 3 zero, 4, 12), (inputs.getD 5 zero, 10, 42)]) ok_17_0_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube17_0

section Cube1_16

private def p_1_16 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0xeffbfe7e3ffc79e7 0xdff7fcfc7ff8f3cf
  | 2 => mk128 0xf6fccf9fc71f9e99 0xedf99f3f8e3f3d33
  | 3 => mk128 0x3b7f0fe7f81fe71e 0x76fe1fcff03fce3c
  | 4 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 5 => mk128 0x3c7ff007ffe007e0 0x78ffe00fffc00fc0
  | _ => 0
private def q_1_16 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0x5008008009040022 0xa010010012080045
  | 2 => mk128 0x8912142242491289 0x1224284484922512
  | 3 => mk128 0x4a0a80c90924514 0x941501921248a28
  | 4 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 5 => mk128 0x3c28d5724c357c0 0x7851aae4986af80
  | _ => 0
private theorem pp_1_16 : properPairs (subGoal 1 16) (asRow p_1_16) (asRow q_1_16) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_1_16 : List Decor := rawDecor (freeMask 1 16) p_1_16 q_1_16
private def sl_1_16 : List (Sig × Nat) := [(subcube 33 16, 4)]
private theorem sl_1_16_ok : ∀ s ∈ sl_1_16, Slice (freeVars 1 16) (subGoal 1 16) s.1 s.2 := by
  intro s hs
  simp only [sl_1_16, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 33 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_33_16
private def autos_1_16 : List (List Move) := [[], [swapRows 50]]
private theorem autos_1_16_ok : ∀ m ∈ autos_1_16, autoOK (subGoal 1 16) m = true := by
  intro m hm
  simp only [autos_1_16, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl <;> decide +kernel
private def lv_1_16_4_0 : List NodeSpec := [([], [0, 1, 2, 3], [(0, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_1_16_4_0 : LevelOK rd_1_16 (subGoal 1 16) 4 lv_1_16_4_0 :=
  levelCheck_sound pp_1_16 (raw_faithful _ _ _) sl_1_16_ok autos_1_16_ok (emptyLevelOK rd_1_16 (subGoal 1 16) 3)
    (by decide +kernel : levelCheck (freeVars 1 16) rd_1_16 (subGoal 1 16) sl_1_16 autos_1_16 [] 4 lv_1_16_4_0 = true)
private def lv_1_16_4 : List NodeSpec := lv_1_16_4_0
private theorem ok_1_16_4 : LevelOK rd_1_16 (subGoal 1 16) 4 lv_1_16_4 := ok_1_16_4_0
private theorem lower_1_16 : Lower (freeVars 1 16) (subGoal 1 16) 5 :=
  lower_of_search (xs := [(inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 3 zero, 2, 10), (inputs.getD 5 zero, 2, 34)]) ok_1_16_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube1_16

section Cube1_32

private def p_1_32 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0xeffbfe7e3ffc79e7 0xdff7fcfc7ff8f3cf
  | 2 => mk128 0xf6fccf9fc71f9e99 0xedf99f3f8e3f3d33
  | 3 => mk128 0x3b7f0fe7f81fe71e 0x76fe1fcff03fce3c
  | 4 => mk128 0x3c7ff007ffe007e0 0x78ffe00fffc00fc0
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private def q_1_32 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0x5008008009040022 0xa010010012080045
  | 2 => mk128 0x8912142242491289 0x1224284484922512
  | 3 => mk128 0x4a0a80c90924514 0x941501921248a28
  | 4 => mk128 0x3c28d5724c357c0 0x7851aae4986af80
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private theorem pp_1_32 : properPairs (subGoal 1 32) (asRow p_1_32) (asRow q_1_32) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_1_32 : List Decor := rawDecor (freeMask 1 32) p_1_32 q_1_32
private def sl_1_32 : List (Sig × Nat) := [(subcube 17 32, 4)]
private theorem sl_1_32_ok : ∀ s ∈ sl_1_32, Slice (freeVars 1 32) (subGoal 1 32) s.1 s.2 := by
  intro s hs
  simp only [sl_1_32, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 17 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_17_32
private def autos_1_32 : List (List Move) := [[], [swapRows 50]]
private theorem autos_1_32_ok : ∀ m ∈ autos_1_32, autoOK (subGoal 1 32) m = true := by
  intro m hm
  simp only [autos_1_32, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl <;> decide +kernel
private def lv_1_32_4_0 : List NodeSpec := [([], [0, 1, 2, 3], [(0, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_1_32_4_0 : LevelOK rd_1_32 (subGoal 1 32) 4 lv_1_32_4_0 :=
  levelCheck_sound pp_1_32 (raw_faithful _ _ _) sl_1_32_ok autos_1_32_ok (emptyLevelOK rd_1_32 (subGoal 1 32) 3)
    (by decide +kernel : levelCheck (freeVars 1 32) rd_1_32 (subGoal 1 32) sl_1_32 autos_1_32 [] 4 lv_1_32_4_0 = true)
private def lv_1_32_4 : List NodeSpec := lv_1_32_4_0
private theorem ok_1_32_4 : LevelOK rd_1_32 (subGoal 1 32) 4 lv_1_32_4 := ok_1_32_4_0
private theorem lower_1_32 : Lower (freeVars 1 32) (subGoal 1 32) 5 :=
  lower_of_search (xs := [(inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 3 zero, 2, 10), (inputs.getD 4 zero, 2, 18)]) ok_1_32_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube1_32

section Cube1_0

private def p_1_0 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0x1ffff83f07ffff83 0xffc1ffc0fcf9f3f3
  | 2 => mk128 0xe0fffffff81f07fc 0x3ffe1fffff463c7f
  | 3 => mk128 0xff03ffc3ffe007ff 0xc3ffe1ff0387cf9c
  | 4 => mk128 0xfffc0003fffff800 0x3fffe0003f80fe0
  | 5 => mk128 0x3ffffffff 0xfc00000003fff000
  | _ => 0
private def q_1_0 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0xc428904001650980 0x44c022425818d1b1
  | 2 => mk128 0x2412221280a4224 0x29121494a1422446
  | 3 => mk128 0x481a440652a084ca 0x8265412a0a854a98
  | 4 => mk128 0x929076ab9cd3d062 0x23b9980c33e80f60
  | 5 => mk128 0x1ce38733e71ce773 0x30311030c3f7b000
  | _ => 0
private theorem pp_1_0 : properPairs (subGoal 1 0) (asRow p_1_0) (asRow q_1_0) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_1_0 : List Decor := rawDecor (freeMask 1 0) p_1_0 q_1_0
private def sl_1_0 : List (Sig × Nat) := [(subcube 1 2, 5), (subcube 5 0, 5), (subcube 17 0, 5), (subcube 1 16, 5), (subcube 33 0, 5), (subcube 1 32, 5), (subcube 5 2, 4)]
private theorem sl_1_0_ok : ∀ s ∈ sl_1_0, Slice (freeVars 1 0) (subGoal 1 0) s.1 s.2 := by
  intro s hs
  simp only [sl_1_0, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact slice_correct (ms := fixRows 1 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_1_2
  · exact slice_correct (ms := fixRows 5 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_5_0
  · exact slice_correct (ms := fixRows 17 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_17_0
  · exact slice_correct (ms := fixRows 1 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_1_16
  · exact slice_correct (ms := fixRows 33 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_33_0
  · exact slice_correct (ms := fixRows 1 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_1_32
  · exact slice_correct (ms := fixRows 5 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_5_2
private def autos_1_0 : List (List Move) := [[], [swapRows 84]]
private theorem autos_1_0_ok : ∀ m ∈ autos_1_0, autoOK (subGoal 1 0) m = true := by
  intro m hm
  simp only [autos_1_0, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl <;> decide +kernel
private def lv_1_0_5_0 : List NodeSpec := [([(0, 2, 0), (2, 0, 5)], [6, 5, 1, 2, 3, 4], [(0, [])]), ([(1, 2, 1), (2, 2, 1)], [6, 0, 2, 5, 3, 4], [(0, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_1_0_5_0 : LevelOK rd_1_0 (subGoal 1 0) 5 lv_1_0_5_0 :=
  levelCheck_sound pp_1_0 (raw_faithful _ _ _) sl_1_0_ok autos_1_0_ok (emptyLevelOK rd_1_0 (subGoal 1 0) 4)
    (by decide +kernel : levelCheck (freeVars 1 0) rd_1_0 (subGoal 1 0) sl_1_0 autos_1_0 [] 5 lv_1_0_5_0 = true)
private def lv_1_0_5 : List NodeSpec := lv_1_0_5_0
private theorem ok_1_0_5 : LevelOK rd_1_0 (subGoal 1 0) 5 lv_1_0_5 := ok_1_0_5_0
private def ck64 (ids : List Nat) := levelCheck (freeVars 1 0) rd_1_0 (subGoal 1 0) sl_1_0 autos_1_0 (selectPrev ids lv_1_0_5) 6
private def d64 : List NodeSpec := [([(0,2,0)],[5,0,1,2,3,4],[(0,[]),(1,[]),(1,[0]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[])]),([(3,2,0)],[5,0,1,2,3,4],[(0,[]),(1,[]),(1,[0]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[])]),([(1,2,1)],[0,1,2,5,3,4],[(0,[]),(0,[0]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[])]),([(2,2,1)],[5,0,1,2,3,4],[(0,[]),(0,[0]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q64 : ck64 [0,1] d64 = true := by decide +kernel
private def d65 : List NodeSpec := [([(0,3,0)],[5,0,1,2,4],[(0,[]),(1,[0]),(2,[]),(4,[0]),(5,[0]),(6,[])]),([(3,3,0)],[5,0,1,2,4],[(0,[]),(1,[0]),(2,[]),(3,[]),(4,[0]),(5,[0]),(6,[])]),([(1,3,1)],[0,1,2,5,4],[(0,[0]),(1,[]),(2,[]),(3,[]),(4,[0]),(5,[0]),(6,[])]),([(2,3,1)],[5,0,1,2,4],[(0,[0]),(1,[]),(2,[]),(4,[0]),(5,[0]),(6,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q65 : ck64 [] d65 = true := by decide +kernel
private def lv_1_0_6_0 : List NodeSpec := (d64 ++ d65)

private theorem ok_1_0_6_0 : LevelOK rd_1_0 (subGoal 1 0) 6 lv_1_0_6_0 := by
  have go {ids ds} (h : ck64 ids ds = true) : LevelOK rd_1_0 (subGoal 1 0) 6 ds :=
    levelCheck_sound pp_1_0 (raw_faithful _ _ _) sl_1_0_ok autos_1_0_ok (selectPrevOK ids ok_1_0_5) h
  exact (levelOK_append (go q64) (go q65))
private def lv_1_0_6 : List NodeSpec := lv_1_0_6_0
private theorem ok_1_0_6 : LevelOK rd_1_0 (subGoal 1 0) 6 lv_1_0_6 := ok_1_0_6_0
private def lv_1_0_7_0 : List NodeSpec := [([], [0, 1, 2, 3, 4], [(0, []), (1, []), (2, []), (3, []), (4, []), (5, []), (6, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_1_0_7_0 : LevelOK rd_1_0 (subGoal 1 0) 7 lv_1_0_7_0 :=
  levelCheck_sound pp_1_0 (raw_faithful _ _ _) sl_1_0_ok autos_1_0_ok (selectPrevOK [0,1,2,3,4,5,6,7] ok_1_0_6)
    (by decide +kernel : levelCheck (freeVars 1 0) rd_1_0 (subGoal 1 0) sl_1_0 autos_1_0 (selectPrev [0,1,2,3,4,5,6,7] lv_1_0_6) 7 lv_1_0_7_0 = true)
private def lv_1_0_7 : List NodeSpec := lv_1_0_7_0
private theorem ok_1_0_7 : LevelOK rd_1_0 (subGoal 1 0) 7 lv_1_0_7 := ok_1_0_7_0
private theorem lower_1_0 : Lower (freeVars 1 0) (subGoal 1 0) 8 :=
  lower_of_search (xs := [(inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 3 zero, 4, 12), (inputs.getD 4 zero, 10, 26), (inputs.getD 5 zero, 10, 42)]) ok_1_0_7 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube1_0

section Cube18_32

private def p_18_32 : Nat → Bits
  | 0 => mk128 0xbecfbecfbecfbecf 0xbecfbecfbecfbecf
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0xdf73df73df73df73 0xdf73df73df73df73
  | 3 => mk128 0xefbcefbcefbcefbc 0xefbcefbcefbcefbc
  | 4 => mk128 0x0 0x0
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private def q_18_32 : Nat → Bits
  | 0 => mk128 0x4205420542054205 0x4205420542054205
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0x2412241224122412 0x2412241224122412
  | 3 => mk128 0x1828182818281828 0x1828182818281828
  | 4 => mk128 0x0 0x0
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private theorem pp_18_32 : properPairs (subGoal 18 32) (asRow p_18_32) (asRow q_18_32) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_18_32 : List Decor := rawDecor (freeMask 18 32) p_18_32 q_18_32
private def sl_18_32 : List (Sig × Nat) := []
private theorem sl_18_32_ok : ∀ s ∈ sl_18_32, Slice (freeVars 18 32) (subGoal 18 32) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private def autos_18_32 : List (List Move) := [[], [swapRows 50], [swapRows 32], [swapRows 32, swapRows 50], [swapRows 48, swapRows 50], [swapRows 48]]
private theorem autos_18_32_ok : ∀ m ∈ autos_18_32, autoOK (subGoal 18 32) m = true := by
  intro m hm
  simp only [autos_18_32, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
private def lv_18_32_3_0 : List NodeSpec := [([], [0, 1, 2], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_18_32_3_0 : LevelOK rd_18_32 (subGoal 18 32) 3 lv_18_32_3_0 :=
  levelCheck_sound pp_18_32 (raw_faithful _ _ _) sl_18_32_ok autos_18_32_ok (emptyLevelOK rd_18_32 (subGoal 18 32) 2)
    (by decide +kernel : levelCheck (freeVars 18 32) rd_18_32 (subGoal 18 32) sl_18_32 autos_18_32 [] 3 lv_18_32_3_0 = true)
private def lv_18_32_3 : List NodeSpec := lv_18_32_3_0
private theorem ok_18_32_3 : LevelOK rd_18_32 (subGoal 18 32) 3 lv_18_32_3 := ok_18_32_3_0
private theorem lower_18_32 : Lower (freeVars 18 32) (subGoal 18 32) 4 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 4, 5), (inputs.getD 2 zero, 1, 5), (inputs.getD 3 zero, 1, 9)]) ok_18_32_3 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube18_32

section Cube18_0

private def p_18_0 : Nat → Bits
  | 0 => mk128 0xeef8ff9f8ff879f9 0xddf1ff3f1ff0f3f3
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0xf7ff3ffff1fffe3f 0xeffe7fffe3fffc7f
  | 3 => mk128 0x3b7fc7e7fe3f87ce 0x76ff8fcffc7f0f9c
  | 4 => mk128 0x0 0x0
  | 5 => mk128 0x3c7ff807ffc007f0 0x78fff00fff800fe0
  | _ => 0
private def q_18_0 : Nat → Bits
  | 0 => mk128 0x510e1121824930d8 0xa21c2243049261b1
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0x8810820210924223 0x1021040421248446
  | 3 => mk128 0x4a2340ca425154c 0x9446819484a2a98
  | 4 => mk128 0x0 0x0
  | 5 => mk128 0x3c4a757490667b0 0x7894eae920ccf60
  | _ => 0
private theorem pp_18_0 : properPairs (subGoal 18 0) (asRow p_18_0) (asRow q_18_0) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_18_0 : List Decor := rawDecor (freeMask 18 0) p_18_0 q_18_0
private def sl_18_0 : List (Sig × Nat) := [(subcube 18 32, 4)]
private theorem sl_18_0_ok : ∀ s ∈ sl_18_0, Slice (freeVars 18 0) (subGoal 18 0) s.1 s.2 := by
  intro s hs
  simp only [sl_18_0, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 18 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_18_32
private def autos_18_0 : List (List Move) := [[], [swapRows 48]]
private theorem autos_18_0_ok : ∀ m ∈ autos_18_0, autoOK (subGoal 18 0) m = true := by
  intro m hm
  simp only [autos_18_0, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl <;> decide +kernel
private def lv_18_0_4_0 : List NodeSpec := [([], [0, 1, 2, 3], [(0, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_18_0_4_0 : LevelOK rd_18_0 (subGoal 18 0) 4 lv_18_0_4_0 :=
  levelCheck_sound pp_18_0 (raw_faithful _ _ _) sl_18_0_ok autos_18_0_ok (emptyLevelOK rd_18_0 (subGoal 18 0) 3)
    (by decide +kernel : levelCheck (freeVars 18 0) rd_18_0 (subGoal 18 0) sl_18_0 autos_18_0 [] 4 lv_18_0_4_0 = true)
private def lv_18_0_4 : List NodeSpec := lv_18_0_4_0
private theorem ok_18_0_4 : LevelOK rd_18_0 (subGoal 18 0) 4 lv_18_0_4 := ok_18_0_4_0
private theorem lower_18_0 : Lower (freeVars 18 0) (subGoal 18 0) 5 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 4, 5), (inputs.getD 2 zero, 1, 5), (inputs.getD 3 zero, 4, 12), (inputs.getD 5 zero, 9, 41)]) ok_18_0_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube18_0

section Cube20_8

private def p_20_8 : Nat → Bits
  | 0 => mk128 0xbecfbecfbecfbecf 0xbecfbecfbecfbecf
  | 1 => mk128 0xdf73df73df73df73 0xdf73df73df73df73
  | 2 => mk128 0x0 0x0
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0x0 0x0
  | 5 => mk128 0xefbcefbcefbcefbc 0xefbcefbcefbcefbc
  | _ => 0
private def q_20_8 : Nat → Bits
  | 0 => mk128 0x4205420542054205 0x4205420542054205
  | 1 => mk128 0x2412241224122412 0x2412241224122412
  | 2 => mk128 0x0 0x0
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0x0 0x0
  | 5 => mk128 0x1828182818281828 0x1828182818281828
  | _ => 0
private theorem pp_20_8 : properPairs (subGoal 20 8) (asRow p_20_8) (asRow q_20_8) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_20_8 : List Decor := rawDecor (freeMask 20 8) p_20_8 q_20_8
private def sl_20_8 : List (Sig × Nat) := []
private theorem sl_20_8_ok : ∀ s ∈ sl_20_8, Slice (freeVars 20 8) (subGoal 20 8) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private def autos_20_8 : List (List Move) := [[], [swapRows 81], [swapRows 16], [swapRows 16, swapRows 81], [swapRows 80, swapRows 81], [swapRows 80]]
private theorem autos_20_8_ok : ∀ m ∈ autos_20_8, autoOK (subGoal 20 8) m = true := by
  intro m hm
  simp only [autos_20_8, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
private def lv_20_8_3_0 : List NodeSpec := [([], [0, 1, 2], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_20_8_3_0 : LevelOK rd_20_8 (subGoal 20 8) 3 lv_20_8_3_0 :=
  levelCheck_sound pp_20_8 (raw_faithful _ _ _) sl_20_8_ok autos_20_8_ok (emptyLevelOK rd_20_8 (subGoal 20 8) 2)
    (by decide +kernel : levelCheck (freeVars 20 8) rd_20_8 (subGoal 20 8) sl_20_8 autos_20_8 [] 3 lv_20_8_3_0 = true)
private def lv_20_8_3 : List NodeSpec := lv_20_8_3_0
private theorem ok_20_8_3 : LevelOK rd_20_8 (subGoal 20 8) 3 lv_20_8_3 := ok_20_8_3_0
private theorem lower_20_8 : Lower (freeVars 20 8) (subGoal 20 8) 4 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 5 zero, 1, 33)]) ok_20_8_3 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube20_8

section Cube20_0

private def p_20_0 : Nat → Bits
  | 0 => mk128 0xffc3fe3fbf0fffc3 0xfe3fbf0fffc3fe3f
  | 1 => mk128 0xfffc3fc7dff0fffc 0x3fc7dff0fffc3fc7
  | 2 => mk128 0x0 0x0
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0x0 0x0
  | 5 => mk128 0xfffc3f8efff0fff 0xc3f8efff0fffc3f8
  | _ => 0
private def q_20_0 : Nat → Bits
  | 0 => mk128 0x22e2661b41e222e2 0x661b41e222e2661b
  | 1 => mk128 0x45662ac5222e4566 0x2ac5222e45662ac5
  | 2 => mk128 0x0 0x0
  | 3 => mk128 0x8988916e04448988 0x916e04448988916e
  | 4 => mk128 0x0 0x0
  | 5 => mk128 0xee3323b01888ee33 0x23b01888ee3323b0
  | _ => 0
private theorem pp_20_0 : properPairs (subGoal 20 0) (asRow p_20_0) (asRow q_20_0) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_20_0 : List Decor := rawDecor (freeMask 20 0) p_20_0 q_20_0
private def sl_20_0 : List (Sig × Nat) := [(subcube 20 8, 4)]
private theorem sl_20_0_ok : ∀ s ∈ sl_20_0, Slice (freeVars 20 0) (subGoal 20 0) s.1 s.2 := by
  intro s hs
  simp only [sl_20_0, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 20 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_20_8
private def autos_20_0 : List (List Move) := [[], [swapRows 81], [swapRows 16], [swapRows 16, swapRows 81], [swapRows 80, swapRows 81], [swapRows 80]]
private theorem autos_20_0_ok : ∀ m ∈ autos_20_0, autoOK (subGoal 20 0) m = true := by
  intro m hm
  simp only [autos_20_0, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
private def lv_20_0_4_0 : List NodeSpec := [([], [0, 1, 2, 3], [(0, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_20_0_4_0 : LevelOK rd_20_0 (subGoal 20 0) 4 lv_20_0_4_0 :=
  levelCheck_sound pp_20_0 (raw_faithful _ _ _) sl_20_0_ok autos_20_0_ok (emptyLevelOK rd_20_0 (subGoal 20 0) 3)
    (by decide +kernel : levelCheck (freeVars 20 0) rd_20_0 (subGoal 20 0) sl_20_0 autos_20_0 [] 4 lv_20_0_4_0 = true)
private def lv_20_0_4 : List NodeSpec := lv_20_0_4_0
private theorem ok_20_0_4 : LevelOK rd_20_0 (subGoal 20 0) 4 lv_20_0_4 := ok_20_0_4_0
private theorem lower_20_0 : Lower (freeVars 20 0) (subGoal 20 0) 5 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 10, 11), (inputs.getD 1 zero, 9, 11), (inputs.getD 3 zero, 3, 11), (inputs.getD 5 zero, 9, 41)]) ok_20_0_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube20_0

section Cube16_8

private def p_16_8 : Nat → Bits
  | 0 => mk128 0x7377446bbe967377 0x446bbe967377446b
  | 1 => mk128 0x9c7b8593df1b9c7b 0x8593df1b9c7b8593
  | 2 => mk128 0xef83fa1cffe3ef83 0xfa1cffe3ef83fa1c
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0x0 0x0
  | 5 => mk128 0xffc03e0effc0ffc 0x3e0effc0ffc03e0
  | _ => 0
private def q_16_8 : Nat → Bits
  | 0 => mk128 0x8111082942288111 0x829422881110829
  | 1 => mk128 0x2422109224442422 0x1092244424221092
  | 2 => mk128 0x0 0x0
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0x0 0x0
  | 5 => mk128 0x5a40234018015a40 0x234018015a402340
  | _ => 0
private theorem pp_16_8 : properPairs (subGoal 16 8) (asRow p_16_8) (asRow q_16_8) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_16_8 : List Decor := rawDecor (freeMask 16 8) p_16_8 q_16_8
private def sl_16_8 : List (Sig × Nat) := [(subcube 20 8, 4)]
private theorem sl_16_8_ok : ∀ s ∈ sl_16_8, Slice (freeVars 16 8) (subGoal 16 8) s.1 s.2 := by
  intro s hs
  simp only [sl_16_8, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 20 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_20_8
private def autos_16_8 : List (List Move) := [[], [swapRows 81], [swapRows 16], [swapRows 16, swapRows 81], [swapRows 80, swapRows 81], [swapRows 80]]
private theorem autos_16_8_ok : ∀ m ∈ autos_16_8, autoOK (subGoal 16 8) m = true := by
  intro m hm
  simp only [autos_16_8, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
private def lv_16_8_4_0 : List NodeSpec := [([], [0, 1, 2, 3], [(0, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_16_8_4_0 : LevelOK rd_16_8 (subGoal 16 8) 4 lv_16_8_4_0 :=
  levelCheck_sound pp_16_8 (raw_faithful _ _ _) sl_16_8_ok autos_16_8_ok (emptyLevelOK rd_16_8 (subGoal 16 8) 3)
    (by decide +kernel : levelCheck (freeVars 16 8) rd_16_8 (subGoal 16 8) sl_16_8 autos_16_8 [] 4 lv_16_8_4_0 = true)
private def lv_16_8_4 : List NodeSpec := lv_16_8_4_0
private theorem ok_16_8_4 : LevelOK rd_16_8 (subGoal 16 8) 4 lv_16_8_4 := ok_16_8_4_0
private theorem lower_16_8 : Lower (freeVars 16 8) (subGoal 16 8) 5 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 0, 4), (inputs.getD 5 zero, 1, 33)]) ok_16_8_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube16_8

section Cube16_32

private def p_16_32 : Nat → Bits
  | 0 => mk128 0x73afcc9ce3b9f327 0x3afcc9ce3b9f3273
  | 1 => mk128 0x9ccff0e73c3e7c39 0xccff0e73c3e7c39c
  | 2 => mk128 0x1ff7ff07ffc07fc1 0xff7ff07ffc07fc1f
  | 3 => mk128 0xe0fbfff83fff80fe 0xfbfff83fff80fe0
  | 4 => mk128 0x0 0x0
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private def q_16_32 : Nat → Bits
  | 0 => mk128 0x31506921208d1a23 0x1506921208d1a231
  | 1 => mk128 0x9430aa0864152a29 0x430aa0864152a294
  | 2 => mk128 0xa09005009004040 0xa09005009004040a
  | 3 => mk128 0x4006000292200094 0x60002922000940
  | 4 => mk128 0x0 0x0
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private theorem pp_16_32 : properPairs (subGoal 16 32) (asRow p_16_32) (asRow q_16_32) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_16_32 : List Decor := rawDecor (freeMask 16 32) p_16_32 q_16_32
private def sl_16_32 : List (Sig × Nat) := [(subcube 17 32, 4)]
private theorem sl_16_32_ok : ∀ s ∈ sl_16_32, Slice (freeVars 16 32) (subGoal 16 32) s.1 s.2 := by
  intro s hs
  simp only [sl_16_32, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 17 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_17_32
private def autos_16_32 : List (List Move) := [[], [swapRows 50], [swapRows 16], [swapRows 16, swapRows 50]]
private theorem autos_16_32_ok : ∀ m ∈ autos_16_32, autoOK (subGoal 16 32) m = true := by
  intro m hm
  simp only [autos_16_32, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl <;> decide +kernel
private def lv_16_32_4_0 : List NodeSpec := [([], [0, 1, 2, 3], [(0, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_16_32_4_0 : LevelOK rd_16_32 (subGoal 16 32) 4 lv_16_32_4_0 :=
  levelCheck_sound pp_16_32 (raw_faithful _ _ _) sl_16_32_ok autos_16_32_ok (emptyLevelOK rd_16_32 (subGoal 16 32) 3)
    (by decide +kernel : levelCheck (freeVars 16 32) rd_16_32 (subGoal 16 32) sl_16_32 autos_16_32 [] 4 lv_16_32_4_0 = true)
private def lv_16_32_4 : List NodeSpec := lv_16_32_4_0
private theorem ok_16_32_4 : LevelOK rd_16_32 (subGoal 16 32) 4 lv_16_32_4 := ok_16_32_4_0
private theorem lower_16_32 : Lower (freeVars 16 32) (subGoal 16 32) 5 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 4, 5), (inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 1, 5), (inputs.getD 3 zero, 1, 9)]) ok_16_32_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube16_32

section Cube16_0

private def p_16_0 : Nat → Bits
  | 0 => mk128 0x7e3ff0f878fc3fc 0x3f8e0ff07c8f34f3
  | 1 => mk128 0xf803fff0f80ffc3f 0xc3f00fff80f1c8fc
  | 2 => mk128 0xfffc3ffffff0003f 0xfffff0ffff01ff1f
  | 3 => mk128 0xffffc000ffffffc0 0x3ffff0003fe0fe0
  | 4 => mk128 0x0 0x0
  | 5 => mk128 0xffffffff 0xfc00000003fff000
  | _ => 0
private def q_16_0 : Nat → Bits
  | 0 => mk128 0x31448a988182e24e 0x2582299138871471
  | 1 => mk128 0x50c9148998056616 0x62904aa708b148b4
  | 2 => mk128 0x8200200022100020 0x882480484100a10a
  | 3 => mk128 0x248206224ca98880 0x3496402125a0ec0
  | 4 => mk128 0x0 0x0
  | 5 => mk128 0xc713b8ccf74e333b 0x3001888c63edf000
  | _ => 0
private theorem pp_16_0 : properPairs (subGoal 16 0) (asRow p_16_0) (asRow q_16_0) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_16_0 : List Decor := rawDecor (freeMask 16 0) p_16_0 q_16_0
private def sl_16_0 : List (Sig × Nat) := [(subcube 48 0, 6), (subcube 17 0, 5), (subcube 18 0, 5), (subcube 20 0, 5), (subcube 16 8, 5), (subcube 16 32, 5), (subcube 20 8, 4), (subcube 17 32, 4)]
private theorem sl_16_0_ok : ∀ s ∈ sl_16_0, Slice (freeVars 16 0) (subGoal 16 0) s.1 s.2 := by
  intro s hs
  simp only [sl_16_0, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact slice_correct (ms := fixRows 48 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_48_0
  · exact slice_correct (ms := fixRows 17 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_17_0
  · exact slice_correct (ms := fixRows 18 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_18_0
  · exact slice_correct (ms := fixRows 20 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_20_0
  · exact slice_correct (ms := fixRows 16 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_16_8
  · exact slice_correct (ms := fixRows 16 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_16_32
  · exact slice_correct (ms := fixRows 20 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_20_8
  · exact slice_correct (ms := fixRows 17 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_17_32
private def autos_16_0 : List (List Move) := [[], [swapRows 16]]
private theorem autos_16_0_ok : ∀ m ∈ autos_16_0, autoOK (subGoal 16 0) m = true := by
  intro m hm
  simp only [autos_16_0, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl <;> decide +kernel
private def lv_16_0_4_0 : List NodeSpec := [([(1, 1, 0), (1, 2, 5), (0, 3, 6)], [0, 1, 2, 7, 4], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_16_0_4_0 : LevelOK rd_16_0 (subGoal 16 0) 4 lv_16_0_4_0 :=
  levelCheck_sound pp_16_0 (raw_faithful _ _ _) sl_16_0_ok autos_16_0_ok (emptyLevelOK rd_16_0 (subGoal 16 0) 3)
    (by decide +kernel : levelCheck (freeVars 16 0) rd_16_0 (subGoal 16 0) sl_16_0 autos_16_0 [] 4 lv_16_0_4_0 = true)
private def lv_16_0_4 : List NodeSpec := lv_16_0_4_0
private theorem ok_16_0_4 : LevelOK rd_16_0 (subGoal 16 0) 4 lv_16_0_4 := ok_16_0_4_0
private def ck66 (ids : List Nat) := levelCheck (freeVars 16 0) rd_16_0 (subGoal 16 0) sl_16_0 autos_16_0 (selectPrev ids lv_16_0_4) 5
private def d66 : List NodeSpec := [([(1,1,0),(1,2,0)],[1,5,2,6,3,4],[(2,[])]),([(1,1,0),(1,2,5)],[0,1,2,6,3,4],[(0,[]),(4,[]),(5,[])]),([(1,1,0),(3,2,5)],[6,0,1,2,3,4],[(0,[]),(5,[])]),([(1,1,0),(2,3,0)],[6,1,5,2,3,4],[(2,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q66 : ck66 [0] d66 = true := by decide +kernel
private def d67 : List NodeSpec := [([(1,1,0),(0,3,5)],[0,1,6,2,3,4],[(0,[]),(5,[])]),([(1,1,0),(2,3,5)],[6,0,1,2,3,4],[(0,[]),(5,[])]),([(1,2,0),(2,5,1)],[6,0,1,2,3,4],[]),([(2,3,0),(1,1,5)],[0,1,6,2,3,4],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q67 : ck66 [] d67 = true := by decide +kernel
private def lv_16_0_5_0 : List NodeSpec := (d66 ++ d67)

private theorem ok_16_0_5_0 : LevelOK rd_16_0 (subGoal 16 0) 5 lv_16_0_5_0 := by
  have go {ids ds} (h : ck66 ids ds = true) : LevelOK rd_16_0 (subGoal 16 0) 5 ds :=
    levelCheck_sound pp_16_0 (raw_faithful _ _ _) sl_16_0_ok autos_16_0_ok (selectPrevOK ids ok_16_0_4) h
  exact (levelOK_append (go q66) (go q67))
private def lv_16_0_5 : List NodeSpec := lv_16_0_5_0
private theorem ok_16_0_5 : LevelOK rd_16_0 (subGoal 16 0) 5 lv_16_0_5 := ok_16_0_5_0
private def ck68 (ids : List Nat) := levelCheck (freeVars 16 0) rd_16_0 (subGoal 16 0) sl_16_0 autos_16_0 (selectPrev ids lv_16_0_5) 6
private def d68 : List NodeSpec := [([(1,1,0)],[0,1,5,2,3,4],[(0,[]),(0,[0]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(7,[])]),([(1,2,0)],[0,1,2,5,3,4],[(0,[]),(0,[0]),(1,[]),(2,[]),(3,[]),(4,[]),(4,[0]),(6,[])]),([(2,3,0)],[5,0,1,2,3,4],[(0,[]),(0,[0]),(1,[]),(2,[]),(3,[]),(3,[0]),(4,[]),(6,[])]),([(1,4,2)],[0,1,2,3,5],[(0,[]),(1,[0]),(2,[0]),(3,[]),(4,[0]),(5,[]),(6,[]),(7,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q68 : ck68 [0,1,2,3,4,5,6,7] d68 = true := by decide +kernel
private def d69 : List NodeSpec := [([(3,4,3)],[5,0,1,2,3],[(0,[]),(1,[0]),(2,[0]),(3,[0]),(4,[]),(5,[]),(6,[]),(7,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q69 : ck68 [] d69 = true := by decide +kernel
private def lv_16_0_6_0 : List NodeSpec := (d68 ++ d69)

private theorem ok_16_0_6_0 : LevelOK rd_16_0 (subGoal 16 0) 6 lv_16_0_6_0 := by
  have go {ids ds} (h : ck68 ids ds = true) : LevelOK rd_16_0 (subGoal 16 0) 6 ds :=
    levelCheck_sound pp_16_0 (raw_faithful _ _ _) sl_16_0_ok autos_16_0_ok (selectPrevOK ids ok_16_0_5) h
  exact (levelOK_append (go q68) (go q69))
private def lv_16_0_6 : List NodeSpec := lv_16_0_6_0
private theorem ok_16_0_6 : LevelOK rd_16_0 (subGoal 16 0) 6 lv_16_0_6 := ok_16_0_6_0
private def lv_16_0_7_0 : List NodeSpec := [([], [0, 1, 2, 3, 4], [(0, []), (1, []), (2, []), (3, []), (4, []), (6, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_16_0_7_0 : LevelOK rd_16_0 (subGoal 16 0) 7 lv_16_0_7_0 :=
  levelCheck_sound pp_16_0 (raw_faithful _ _ _) sl_16_0_ok autos_16_0_ok (selectPrevOK [0,1,2,3,4] ok_16_0_6)
    (by decide +kernel : levelCheck (freeVars 16 0) rd_16_0 (subGoal 16 0) sl_16_0 autos_16_0 (selectPrev [0,1,2,3,4] lv_16_0_6) 7 lv_16_0_7_0 = true)
private def lv_16_0_7 : List NodeSpec := lv_16_0_7_0
private theorem ok_16_0_7 : LevelOK rd_16_0 (subGoal 16 0) 7 lv_16_0_7 := ok_16_0_7_0
private theorem lower_16_0 : Lower (freeVars 16 0) (subGoal 16 0) 8 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 4, 5), (inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 1, 5), (inputs.getD 3 zero, 3, 11), (inputs.getD 5 zero, 9, 41)]) ok_16_0_7 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube16_0

section Cube4_2

private def p_4_2 : Nat → Bits
  | 0 => mk128 0xfbbc933e39cef90 0xfbbc933e39cef90f
  | 1 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 2 => mk128 0x0 0x0
  | 3 => mk128 0xf3dff1fcfc1ff31f 0x3dff1fcfc1ff31f3
  | 4 => mk128 0x3ceffe3f3fe0fce3 0xceffe3f3fe0fce3c
  | 5 => mk128 0xc0f3ffc03fff00fc 0xf3ffc03fff00fc0
  | _ => 0
private def q_4_2 : Nat → Bits
  | 0 => mk128 0x544626420c62a90 0x544626420c62a905
  | 1 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 2 => mk128 0x0 0x0
  | 3 => mk128 0x5220840104084005 0x2208401040840052
  | 4 => mk128 0x2811008049008022 0x8110080490080228
  | 5 => mk128 0x800e202ab2520ad8 0xe202ab2520ad80
  | _ => 0
private theorem pp_4_2 : properPairs (subGoal 4 2) (asRow p_4_2) (asRow q_4_2) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_4_2 : List Decor := rawDecor (freeMask 4 2) p_4_2 q_4_2
private def sl_4_2 : List (Sig × Nat) := [(subcube 5 2, 4)]
private theorem sl_4_2_ok : ∀ s ∈ sl_4_2, Slice (freeVars 4 2) (subGoal 4 2) s.1 s.2 := by
  intro s hs
  simp only [sl_4_2, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 5 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_5_2
private def autos_4_2 : List (List Move) := [[], [swapRows 67], [swapRows 80], [swapRows 80, swapRows 67]]
private theorem autos_4_2_ok : ∀ m ∈ autos_4_2, autoOK (subGoal 4 2) m = true := by
  intro m hm
  simp only [autos_4_2, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl <;> decide +kernel
private def lv_4_2_4_0 : List NodeSpec := [([], [0, 1, 2, 3], [(0, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_4_2_4_0 : LevelOK rd_4_2 (subGoal 4 2) 4 lv_4_2_4_0 :=
  levelCheck_sound pp_4_2 (raw_faithful _ _ _) sl_4_2_ok autos_4_2_ok (emptyLevelOK rd_4_2 (subGoal 4 2) 3)
    (by decide +kernel : levelCheck (freeVars 4 2) rd_4_2 (subGoal 4 2) sl_4_2 autos_4_2 [] 4 lv_4_2_4_0 = true)
private def lv_4_2_4 : List NodeSpec := lv_4_2_4_0
private theorem ok_4_2_4 : LevelOK rd_4_2 (subGoal 4 2) 4 lv_4_2_4 := ok_4_2_4_0
private theorem lower_4_2 : Lower (freeVars 4 2) (subGoal 4 2) 5 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 8, 9), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 1, 17), (inputs.getD 5 zero, 8, 40)]) ok_4_2_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube4_2

section Cube4_8

private def p_4_8 : Nat → Bits
  | 0 => mk128 0xcfbfdcf3e3f3e74c 0xfbfdcf3e3f3e74cf
  | 1 => mk128 0x33dfef3cfc7cf9b3 0x3dfef3cfc7cf9b33
  | 2 => mk128 0x0 0x0
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0x3cebf03f3f80fec3 0xcebf03f3f80fec3c
  | 5 => mk128 0xc0f3ffc03fff00fc 0xf3ffc03fff00fc0
  | _ => 0
private def q_4_8 : Nat → Bits
  | 0 => mk128 0x4540410400902004 0x5404104009020045
  | 1 => mk128 0x1220804104204011 0x2208041042040112
  | 2 => mk128 0x0 0x0
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0x28150aa0690a94c2 0x8150aa0690a94c28
  | 5 => mk128 0x800e082ab24a14e8 0xe082ab24a14e80
  | _ => 0
private theorem pp_4_8 : properPairs (subGoal 4 8) (asRow p_4_8) (asRow q_4_8) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_4_8 : List Decor := rawDecor (freeMask 4 8) p_4_8 q_4_8
private def sl_4_8 : List (Sig × Nat) := [(subcube 20 8, 4)]
private theorem sl_4_8_ok : ∀ s ∈ sl_4_8, Slice (freeVars 4 8) (subGoal 4 8) s.1 s.2 := by
  intro s hs
  simp only [sl_4_8, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 20 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_20_8
private def autos_4_8 : List (List Move) := [[], [swapRows 84], [swapRows 16], [swapRows 16, swapRows 84]]
private theorem autos_4_8_ok : ∀ m ∈ autos_4_8, autoOK (subGoal 4 8) m = true := by
  intro m hm
  simp only [autos_4_8, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl <;> decide +kernel
private def lv_4_8_4_0 : List NodeSpec := [([], [0, 1, 2, 3], [(0, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_4_8_4_0 : LevelOK rd_4_8 (subGoal 4 8) 4 lv_4_8_4_0 :=
  levelCheck_sound pp_4_8 (raw_faithful _ _ _) sl_4_8_ok autos_4_8_ok (emptyLevelOK rd_4_8 (subGoal 4 8) 3)
    (by decide +kernel : levelCheck (freeVars 4 8) rd_4_8 (subGoal 4 8) sl_4_8 autos_4_8 [] 4 lv_4_8_4_0 = true)
private def lv_4_8_4 : List NodeSpec := lv_4_8_4_0
private theorem ok_4_8_4 : LevelOK rd_4_8 (subGoal 4 8) 4 lv_4_8_4 := ok_4_8_4_0
private theorem lower_4_8 : Lower (freeVars 4 8) (subGoal 4 8) 5 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 4 zero, 1, 17), (inputs.getD 5 zero, 1, 33)]) ok_4_8_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube4_8

section Cube4_0

private def p_4_0 : Nat → Bits
  | 0 => mk128 0xffffffe07fe0ffe 0xffc3ffffb1c71ff
  | 1 => mk128 0xf01fc1fff83ff07f 0xf07fc3c07de78e67
  | 2 => mk128 0x0 0x0
  | 3 => mk128 0xffe001ffffc0007f 0xfffffc007e07ff87
  | 4 => mk128 0xfffffe07ffffff80 0x7fffff87f80ff8
  | 5 => mk128 0x7ffffffff 0xff80000007fff000
  | _ => 0
private def q_4_0 : Nat → Bits
  | 0 => mk128 0x62449042014a8496 0x848c0653490c30ab
  | 1 => mk128 0xa1c912925816942a 0x9434428551658665
  | 2 => mk128 0x0 0x0
  | 3 => mk128 0x4483a524aac1084d 0x295aa80a2602db86
  | 4 => mk128 0x912203534a52901 0x863312c06b00d50
  | 5 => mk128 0x8e1c39c7c739ce71 0xce02223047df6000
  | _ => 0
private theorem pp_4_0 : properPairs (subGoal 4 0) (asRow p_4_0) (asRow q_4_0) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_4_0 : List Decor := rawDecor (freeMask 4 0) p_4_0 q_4_0
private def sl_4_0 : List (Sig × Nat) := [(subcube 5 0, 5), (subcube 4 2, 5), (subcube 4 8, 5), (subcube 20 0, 5), (subcube 36 0, 5), (subcube 5 2, 4), (subcube 20 8, 4), (subcube 36 2, 4), (subcube 36 8, 4)]
private theorem sl_4_0_ok : ∀ s ∈ sl_4_0, Slice (freeVars 4 0) (subGoal 4 0) s.1 s.2 := by
  intro s hs
  simp only [sl_4_0, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact slice_correct (ms := fixRows 5 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_5_0
  · exact slice_correct (ms := fixRows 4 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_4_2
  · exact slice_correct (ms := fixRows 4 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_4_8
  · exact slice_correct (ms := fixRows 20 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_20_0
  · exact slice_correct (ms := fixRows 36 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_36_0
  · exact slice_correct (ms := fixRows 5 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_5_2
  · exact slice_correct (ms := fixRows 20 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_20_8
  · exact slice_correct (ms := fixRows 36 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_36_2
  · exact slice_correct (ms := fixRows 36 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_36_8
private def autos_4_0 : List (List Move) := [[], [swapRows 64, swapRows 49]]
private theorem autos_4_0_ok : ∀ m ∈ autos_4_0, autoOK (subGoal 4 0) m = true := by
  intro m hm
  simp only [autos_4_0, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl <;> decide +kernel
private def lv_4_0_4_0 : List NodeSpec := [([(1, 3, 0), (1, 4, 5), (0, 6, 1)], [0, 7, 2, 3, 4], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_4_0_4_0 : LevelOK rd_4_0 (subGoal 4 0) 4 lv_4_0_4_0 :=
  levelCheck_sound pp_4_0 (raw_faithful _ _ _) sl_4_0_ok autos_4_0_ok (emptyLevelOK rd_4_0 (subGoal 4 0) 3)
    (by decide +kernel : levelCheck (freeVars 4 0) rd_4_0 (subGoal 4 0) sl_4_0 autos_4_0 [] 4 lv_4_0_4_0 = true)
private def lv_4_0_4 : List NodeSpec := lv_4_0_4_0
private theorem ok_4_0_4 : LevelOK rd_4_0 (subGoal 4 0) 4 lv_4_0_4 := ok_4_0_4_0
private def lv_4_0_5_0 : List NodeSpec := [([(1, 3, 0), (1, 4, 5)], [0, 1, 2, 3, 4, 6], [(1, []), (2, [])]), ([(1, 3, 0), (3, 4, 5)], [6, 0, 1, 2, 3, 4], []), ([(1, 4, 0), (1, 4, 3)], [0, 1, 2, 3, 5, 6], [(0, []), (3, [])]), ([(1, 4, 0), (2, 5, 3)], [6, 0, 1, 2, 3, 4], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_4_0_5_0 : LevelOK rd_4_0 (subGoal 4 0) 5 lv_4_0_5_0 :=
  levelCheck_sound pp_4_0 (raw_faithful _ _ _) sl_4_0_ok autos_4_0_ok (selectPrevOK [0] ok_4_0_4)
    (by decide +kernel : levelCheck (freeVars 4 0) rd_4_0 (subGoal 4 0) sl_4_0 autos_4_0 (selectPrev [0] lv_4_0_4) 5 lv_4_0_5_0 = true)
private def lv_4_0_5 : List NodeSpec := lv_4_0_5_0
private theorem ok_4_0_5 : LevelOK rd_4_0 (subGoal 4 0) 5 lv_4_0_5 := ok_4_0_5_0
private def lv_4_0_6_0 : List NodeSpec := [([(2, 2, 0)], [5, 0, 1, 2, 3, 4], [(0, []), (1, []), (2, []), (3, []), (3, [0]), (4, []), (5, []), (6, []), (8, [])]), ([(0, 2, 1)], [0, 5, 1, 2, 3, 4], [(0, []), (0, [0]), (1, []), (2, []), (3, []), (3, [0]), (4, []), (4, [0]), (5, []), (6, []), (7, [])]), ([(1, 3, 0)], [0, 1, 2, 3, 5, 4], [(0, []), (1, []), (2, []), (3, []), (4, []), (5, []), (6, [])]), ([(1, 4, 0)], [0, 1, 2, 3, 4, 5], [(0, []), (1, []), (1, [0]), (2, []), (3, []), (4, []), (5, []), (8, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_4_0_6_0 : LevelOK rd_4_0 (subGoal 4 0) 6 lv_4_0_6_0 :=
  levelCheck_sound pp_4_0 (raw_faithful _ _ _) sl_4_0_ok autos_4_0_ok (selectPrevOK [0,1,2,3] ok_4_0_5)
    (by decide +kernel : levelCheck (freeVars 4 0) rd_4_0 (subGoal 4 0) sl_4_0 autos_4_0 (selectPrev [0,1,2,3] lv_4_0_5) 6 lv_4_0_6_0 = true)
private def lv_4_0_6 : List NodeSpec := lv_4_0_6_0
private theorem ok_4_0_6 : LevelOK rd_4_0 (subGoal 4 0) 6 lv_4_0_6 := ok_4_0_6_0
private def lv_4_0_7_0 : List NodeSpec := [([], [0, 1, 2, 3, 4], [(0, []), (1, []), (2, []), (3, []), (4, []), (5, []), (6, []), (7, []), (8, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_4_0_7_0 : LevelOK rd_4_0 (subGoal 4 0) 7 lv_4_0_7_0 :=
  levelCheck_sound pp_4_0 (raw_faithful _ _ _) sl_4_0_ok autos_4_0_ok (selectPrevOK [0,1,2,3] ok_4_0_6)
    (by decide +kernel : levelCheck (freeVars 4 0) rd_4_0 (subGoal 4 0) sl_4_0 autos_4_0 (selectPrev [0,1,2,3] lv_4_0_6) 7 lv_4_0_7_0 = true)
private def lv_4_0_7 : List NodeSpec := lv_4_0_7_0
private theorem ok_4_0_7 : LevelOK rd_4_0 (subGoal 4 0) 7 lv_4_0_7 := ok_4_0_7_0
private theorem lower_4_0 : Lower (freeVars 4 0) (subGoal 4 0) 8 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 10, 11), (inputs.getD 1 zero, 9, 11), (inputs.getD 3 zero, 3, 11), (inputs.getD 4 zero, 1, 17), (inputs.getD 5 zero, 9, 41)]) ok_4_0_7 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube4_0

section Cube2_0

private def p_2_0 : Nat → Bits
  | 0 => mk128 0xfffff07e0ffffc1f 0xfc1ffff03e79f3f3
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0x1f83fffff0783fe1 0xffe1e07fffa63c9f
  | 3 => mk128 0xe003ff87ff803ffe 0x1ffe007fc1c7cf1c
  | 4 => mk128 0xfffc0007ffffc000 0x1fffff8001f80fe0
  | 5 => mk128 0x7ffffffff 0xe000000001fff000
  | _ => 0
private def q_2_0 : Nat → Bits
  | 0 => mk128 0x8500808002904c02 0x240229109408d131
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0x48252442502a1121 0x4921422528a22486
  | 3 => mk128 0x34a480ca5842654 0x1654054a85454b18
  | 4 => mk128 0x52606d57394e8311 0x1b99960309f00ec0
  | 5 => mk128 0x9c738e67ce773b99 0x8311180c31ffb000
  | _ => 0
private theorem pp_2_0 : properPairs (subGoal 2 0) (asRow p_2_0) (asRow q_2_0) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_2_0 : List Decor := rawDecor (freeMask 2 0) p_2_0 q_2_0
private def sl_2_0 : List (Sig × Nat) := [(subcube 18 0, 5)]
private theorem sl_2_0_ok : ∀ s ∈ sl_2_0, Slice (freeVars 2 0) (subGoal 2 0) s.1 s.2 := by
  intro s hs
  simp only [sl_2_0, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 18 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_18_0
private def lv_2_0_5_0 : List NodeSpec := [([], [0, 1, 2, 3, 4], [(0, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_2_0_5_0 : LevelOK rd_2_0 (subGoal 2 0) 5 lv_2_0_5_0 :=
  levelCheck_sound pp_2_0 (raw_faithful _ _ _) sl_2_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_2_0 (subGoal 2 0) 4)
    (by decide +kernel : levelCheck (freeVars 2 0) rd_2_0 (subGoal 2 0) sl_2_0 [[]] [] 5 lv_2_0_5_0 = true)
private def lv_2_0_5 : List NodeSpec := lv_2_0_5_0
private theorem ok_2_0_5 : LevelOK rd_2_0 (subGoal 2 0) 5 lv_2_0_5 := ok_2_0_5_0
private theorem lower_2_0 : Lower (freeVars 2 0) (subGoal 2 0) 6 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 4, 5), (inputs.getD 2 zero, 1, 5), (inputs.getD 3 zero, 4, 12), (inputs.getD 4 zero, 1, 17), (inputs.getD 5 zero, 9, 41)]) ok_2_0_5 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube2_0

section Cube0_16

private def p_0_16 : Nat → Bits
  | 0 => mk128 0x773e7cfc733e7f98 0x8e3c718cf3f8a427
  | 1 => mk128 0x87cf9f1f83c78e60 0xf3cf8e0f3c8158da
  | 2 => mk128 0xf80fe01ffc07f07f 0x3f00ff03f06631c
  | 3 => mk128 0xfff0001ffff8007f 0xfc000fffc00783e0
  | 4 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 5 => mk128 0xffffffe00000007f 0xfffff0000007fc00
  | _ => 0
private def q_0_16 : Nat → Bits
  | 0 => mk128 0x0 0x0
  | 1 => mk128 0x8102002404081000 0x104402041008084a
  | 2 => mk128 0x10a40949205402a9 0x29124a02a126114
  | 3 => mk128 0x220152924200a552 0xa402494a802582a0
  | 4 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 5 => mk128 0x44a958036aa549fc 0xcb2b60628a47f400
  | _ => 0
private theorem pp_0_16 : properPairs (subGoal 0 16) (asRow p_0_16) (asRow q_0_16) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_0_16 : List Decor := rawDecor (freeMask 0 16) p_0_16 q_0_16
private def sl_0_16 : List (Sig × Nat) := [(subcube 1 16, 5)]
private theorem sl_0_16_ok : ∀ s ∈ sl_0_16, Slice (freeVars 0 16) (subGoal 0 16) s.1 s.2 := by
  intro s hs
  simp only [sl_0_16, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 1 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_1_16
private def autos_0_16 : List (List Move) := [[], [swapRows 50]]
private theorem autos_0_16_ok : ∀ m ∈ autos_0_16, autoOK (subGoal 0 16) m = true := by
  intro m hm
  simp only [autos_0_16, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl <;> decide +kernel
private def lv_0_16_5_0 : List NodeSpec := [([], [0, 1, 2, 3, 4], [(0, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_0_16_5_0 : LevelOK rd_0_16 (subGoal 0 16) 5 lv_0_16_5_0 :=
  levelCheck_sound pp_0_16 (raw_faithful _ _ _) sl_0_16_ok autos_0_16_ok (emptyLevelOK rd_0_16 (subGoal 0 16) 4)
    (by decide +kernel : levelCheck (freeVars 0 16) rd_0_16 (subGoal 0 16) sl_0_16 autos_0_16 [] 5 lv_0_16_5_0 = true)
private def lv_0_16_5 : List NodeSpec := lv_0_16_5_0
private theorem ok_0_16_5 : LevelOK rd_0_16 (subGoal 0 16) 5 lv_0_16_5 := ok_0_16_5_0
private theorem lower_0_16 : Lower (freeVars 0 16) (subGoal 0 16) 6 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 0, 1), (inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 3 zero, 2, 10), (inputs.getD 5 zero, 2, 34)]) ok_0_16_5 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube0_16

section Cube0_2

private def p_0_2 : Nat → Bits
  | 0 => mk128 0xb68f393923b31e3e 0x89c9cc3b7bc2486e
  | 1 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 2 => mk128 0x3ff03e3e3fc3e7cf 0xe0e0fc39cfc0c93
  | 3 => mk128 0xc7ffc03fc3fc07f0 0xf00ff0fc1f00731c
  | 4 => mk128 0xf8ffffc003fff800 0xfff000ffe00383e0
  | 5 => mk128 0xfffffffc000000 0xffffff000003fc00
  | _ => 0
private def q_0_2 : Nat → Bits
  | 0 => mk128 0x49818c4c44a62441 0x886866094a864826
  | 1 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 2 => mk128 0x0 0x0
  | 3 => mk128 0x1012009009004802 0x1002805010081118
  | 4 => mk128 0x224100092000094 0x228000a2001082c0
  | 5 => mk128 0xedc8a424002a9529 0xcd2d2a0042a36c00
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
private def autos_0_2 : List (List Move) := [[], [swapRows 67], [swapRows 80], [swapRows 80, swapRows 67]]
private theorem autos_0_2_ok : ∀ m ∈ autos_0_2, autoOK (subGoal 0 2) m = true := by
  intro m hm
  simp only [autos_0_2, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl <;> decide +kernel
private def lv_0_2_5_0 : List NodeSpec := [([], [0, 1, 2, 3, 4], [(0, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_0_2_5_0 : LevelOK rd_0_2 (subGoal 0 2) 5 lv_0_2_5_0 :=
  levelCheck_sound pp_0_2 (raw_faithful _ _ _) sl_0_2_ok autos_0_2_ok (emptyLevelOK rd_0_2 (subGoal 0 2) 4)
    (by decide +kernel : levelCheck (freeVars 0 2) rd_0_2 (subGoal 0 2) sl_0_2 autos_0_2 [] 5 lv_0_2_5_0 = true)
private def lv_0_2_5 : List NodeSpec := lv_0_2_5_0
private theorem ok_0_2_5 : LevelOK rd_0_2 (subGoal 0 2) 5 lv_0_2_5 := ok_0_2_5_0
private theorem lower_0_2 : Lower (freeVars 0 2) (subGoal 0 2) 6 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 8, 9), (inputs.getD 2 zero, 0, 4), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 1, 17), (inputs.getD 5 zero, 8, 40)]) ok_0_2_5 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube0_2

section Cube0_8

private def p_0_8 : Nat → Bits
  | 0 => mk128 0xfb8ef798cf98ce3b 0x48e673339e848c6b
  | 1 => mk128 0x3df0fbe0f3e0f3c3 0x8f187cc3e7053193
  | 2 => mk128 0xdeff03ff03ff03fc 0xf01f80fc07fa421c
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0xe0fffc0003fffc00 0xffe000fff80383e0
  | 5 => mk128 0xfffffffc000000 0xffffff000003fc00
  | _ => 0
private def q_0_8 : Nat → Bits
  | 0 => mk128 0x2108110811040 0x22101082080429
  | 1 => mk128 0x4010210205020408 0x108204104101092
  | 2 => mk128 0x0 0x0
  | 3 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | 4 => mk128 0xfa44054aa508095 0xda410aaa50238340
  | 5 => mk128 0xb7c882508054a926 0xec954a085043e800
  | _ => 0
private theorem pp_0_8 : properPairs (subGoal 0 8) (asRow p_0_8) (asRow q_0_8) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_0_8 : List Decor := rawDecor (freeMask 0 8) p_0_8 q_0_8
private def sl_0_8 : List (Sig × Nat) := [(subcube 4 8, 5)]
private theorem sl_0_8_ok : ∀ s ∈ sl_0_8, Slice (freeVars 0 8) (subGoal 0 8) s.1 s.2 := by
  intro s hs
  simp only [sl_0_8, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 4 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_4_8
private def autos_0_8 : List (List Move) := [[], [swapRows 84], [swapRows 16], [swapRows 16, swapRows 84]]
private theorem autos_0_8_ok : ∀ m ∈ autos_0_8, autoOK (subGoal 0 8) m = true := by
  intro m hm
  simp only [autos_0_8, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl <;> decide +kernel
private def lv_0_8_5_0 : List NodeSpec := [([], [0, 1, 2, 3, 4], [(0, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_0_8_5_0 : LevelOK rd_0_8 (subGoal 0 8) 5 lv_0_8_5_0 :=
  levelCheck_sound pp_0_8 (raw_faithful _ _ _) sl_0_8_ok autos_0_8_ok (emptyLevelOK rd_0_8 (subGoal 0 8) 4)
    (by decide +kernel : levelCheck (freeVars 0 8) rd_0_8 (subGoal 0 8) sl_0_8 autos_0_8 [] 5 lv_0_8_5_0 = true)
private def lv_0_8_5 : List NodeSpec := lv_0_8_5_0
private theorem ok_0_8_5 : LevelOK rd_0_8 (subGoal 0 8) 5 lv_0_8_5 := ok_0_8_5_0
private theorem lower_0_8 : Lower (freeVars 0 8) (subGoal 0 8) 6 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 0, 4), (inputs.getD 4 zero, 1, 17), (inputs.getD 5 zero, 1, 33)]) ok_0_8_5 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube0_8

section Cube0_32

private def p_0_32 : Nat → Bits
  | 0 => mk128 0xfc7f0f18f8e631f1 0xf87c71c7e38b3273
  | 1 => mk128 0x1f8ff01f1f183e3e 0x3f8781f8fc15c39c
  | 2 => mk128 0xe00fffe01fffc03f 0xc007fe00ffe60c1f
  | 3 => mk128 0xfffffe01fffc0 0x7ffff00780fe0
  | 4 => mk128 0xfff00000001fffff 0xfff80000007ff000
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private def q_0_32 : Nat → Bits
  | 0 => mk128 0x4081222101001050 0x4914105229011231
  | 1 => mk128 0x4012224020201212 0x1114809249014294
  | 2 => mk128 0x9244402500a4024 0x822124009226040a
  | 3 => mk128 0x924888100254a480 0x442492400580940
  | 4 => mk128 0x9800cc94949f2929 0x26600c24127ea000
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private theorem pp_0_32 : properPairs (subGoal 0 32) (asRow p_0_32) (asRow q_0_32) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_0_32 : List Decor := rawDecor (freeMask 0 32) p_0_32 q_0_32
private def sl_0_32 : List (Sig × Nat) := [(subcube 1 32, 5)]
private theorem sl_0_32_ok : ∀ s ∈ sl_0_32, Slice (freeVars 0 32) (subGoal 0 32) s.1 s.2 := by
  intro s hs
  simp only [sl_0_32, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 1 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_1_32
private def autos_0_32 : List (List Move) := [[], [swapRows 50], [swapRows 16], [swapRows 16, swapRows 50]]
private theorem autos_0_32_ok : ∀ m ∈ autos_0_32, autoOK (subGoal 0 32) m = true := by
  intro m hm
  simp only [autos_0_32, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl <;> decide +kernel
private def lv_0_32_5_0 : List NodeSpec := [([], [0, 1, 2, 3, 4], [(0, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_0_32_5_0 : LevelOK rd_0_32 (subGoal 0 32) 5 lv_0_32_5_0 :=
  levelCheck_sound pp_0_32 (raw_faithful _ _ _) sl_0_32_ok autos_0_32_ok (emptyLevelOK rd_0_32 (subGoal 0 32) 4)
    (by decide +kernel : levelCheck (freeVars 0 32) rd_0_32 (subGoal 0 32) sl_0_32 autos_0_32 [] 5 lv_0_32_5_0 = true)
private def lv_0_32_5 : List NodeSpec := lv_0_32_5_0
private theorem ok_0_32_5 : LevelOK rd_0_32 (subGoal 0 32) 5 lv_0_32_5 := ok_0_32_5_0
private theorem lower_0_32 : Lower (freeVars 0 32) (subGoal 0 32) 6 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 4, 5), (inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 1, 5), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 1, 17)]) ok_0_32_5 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube0_32

section Cube2_32

private def p_2_32 : Nat → Bits
  | 0 => mk128 0xeffbfe7e3ffc79e7 0xdff7fcfc7ff8f3cf
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0xf6fccf9fc71f9e99 0xedf99f3f8e3f3d33
  | 3 => mk128 0x3b7f0fe7f81fe71e 0x76fe1fcff03fce3c
  | 4 => mk128 0x3c7ff007ffe007e0 0x78ffe00fffc00fc0
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private def q_2_32 : Nat → Bits
  | 0 => mk128 0x5008008009040022 0xa010010012080045
  | 1 => mk128 0x0 0x0
  | 2 => mk128 0x8912142242491289 0x1224284484922512
  | 3 => mk128 0x4a0a80c90924514 0x941501921248a28
  | 4 => mk128 0x3c28d5724c357c0 0x7851aae4986af80
  | 5 => mk128 0xffffffffffffffff 0xffffffffffffffff
  | _ => 0
private theorem pp_2_32 : properPairs (subGoal 2 32) (asRow p_2_32) (asRow q_2_32) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_2_32 : List Decor := rawDecor (freeMask 2 32) p_2_32 q_2_32
private def sl_2_32 : List (Sig × Nat) := [(subcube 18 32, 4)]
private theorem sl_2_32_ok : ∀ s ∈ sl_2_32, Slice (freeVars 2 32) (subGoal 2 32) s.1 s.2 := by
  intro s hs
  simp only [sl_2_32, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  exact slice_correct (ms := fixRows 18 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_18_32
private def autos_2_32 : List (List Move) := [[], [swapRows 50]]
private theorem autos_2_32_ok : ∀ m ∈ autos_2_32, autoOK (subGoal 2 32) m = true := by
  intro m hm
  simp only [autos_2_32, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl <;> decide +kernel
private def lv_2_32_4_0 : List NodeSpec := [([], [0, 1, 2, 3], [(0, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_2_32_4_0 : LevelOK rd_2_32 (subGoal 2 32) 4 lv_2_32_4_0 :=
  levelCheck_sound pp_2_32 (raw_faithful _ _ _) sl_2_32_ok autos_2_32_ok (emptyLevelOK rd_2_32 (subGoal 2 32) 3)
    (by decide +kernel : levelCheck (freeVars 2 32) rd_2_32 (subGoal 2 32) sl_2_32 autos_2_32 [] 4 lv_2_32_4_0 = true)
private def lv_2_32_4 : List NodeSpec := lv_2_32_4_0
private theorem ok_2_32_4 : LevelOK rd_2_32 (subGoal 2 32) 4 lv_2_32_4 := ok_2_32_4_0
private theorem lower_2_32 : Lower (freeVars 2 32) (subGoal 2 32) 5 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 4, 5), (inputs.getD 2 zero, 1, 5), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 1, 17)]) ok_2_32_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube2_32

section Cube8_0

private def p_8_0 : Nat → Bits
  | 0 => mk128 0xffff83f83fe0ff83 0xfc3ffff03ec733f3
  | 1 => mk128 0x7c1ffc1fc3ff07fc 0x1fc3c0ffc179cd9c
  | 2 => mk128 0x801ffffffc0007ff 0xfffc00ffff81fe1f
  | 3 => mk128 0x0 0x0
  | 4 => mk128 0xffe0001ffffff800 0x1fffff0001fe0fe0
  | 5 => mk128 0x1fffffffff 0xe000000001fff000
  | _ => 0
private def q_8_0 : Nat → Bits
  | 0 => mk128 0x1104250808a849a1 0x24065290944310b1
  | 1 => mk128 0x21292129416942a5 0xc4286a584594594
  | 2 => mk128 0xa5242129410844a 0x52a8084a2980aa0a
  | 3 => mk128 0x0 0x0
  | 4 => mk128 0x4a034a54e6529042 0x1b312c0309ac0f40
  | 5 => mk128 0x739c739f3b9ce773 0x8222308c31f7f000
  | _ => 0
private theorem pp_8_0 : properPairs (subGoal 8 0) (asRow p_8_0) (asRow q_8_0) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_8_0 : List Decor := rawDecor (freeMask 8 0) p_8_0 q_8_0
private def sl_8_0 : List (Sig × Nat) := []
private theorem sl_8_0_ok : ∀ s ∈ sl_8_0, Slice (freeVars 8 0) (subGoal 8 0) s.1 s.2 := by
  intro s hs
  exact False.elim (List.not_mem_nil hs)
private def autos_8_0 : List (List Move) := [[], [swapRows 32, swapRows 65]]
private theorem autos_8_0_ok : ∀ m ∈ autos_8_0, autoOK (subGoal 8 0) m = true := by
  intro m hm
  simp only [autos_8_0, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl <;> decide +kernel
private def lv_8_0_4_0 : List NodeSpec := [([], [0, 1, 2, 3, 4], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_8_0_4_0 : LevelOK rd_8_0 (subGoal 8 0) 4 lv_8_0_4_0 :=
  levelCheck_sound pp_8_0 (raw_faithful _ _ _) sl_8_0_ok autos_8_0_ok (emptyLevelOK rd_8_0 (subGoal 8 0) 3)
    (by decide +kernel : levelCheck (freeVars 8 0) rd_8_0 (subGoal 8 0) sl_8_0 autos_8_0 [] 4 lv_8_0_4_0 = true)
private def lv_8_0_4 : List NodeSpec := lv_8_0_4_0
private theorem ok_8_0_4 : LevelOK rd_8_0 (subGoal 8 0) 4 lv_8_0_4 := ok_8_0_4_0
private theorem lower_8_0 : Lower (freeVars 8 0) (subGoal 8 0) 5 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 4, 5), (inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 1, 5), (inputs.getD 4 zero, 1, 17), (inputs.getD 5 zero, 18, 50)]) ok_8_0_4 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube8_0

section Cube0_0

private def p_0_0 : Nat → Bits
  | 0 => mk128 0x1f0fe1ffffc701fe 0x3f16323cc19f4f3
  | 1 => mk128 0x1ff0fe1e01f801ff 0xfc02bc3c70e6c8fc
  | 2 => mk128 0xe000ffe001fffe1f 0xfffcc0c07f070f1f
  | 3 => mk128 0xffff000001ffffe0 0xf00ff83f80fe0
  | 4 => mk128 0xfffffffffe000000 0xfff0003fff000
  | 5 => mk128 0x0 0xffffffc000000
  | _ => 0
private def q_0_0 : Nat → Bits
  | 0 => mk128 0x30120328cc10532 0x9602121c4085471
  | 1 => mk128 0xd10621415480954 0xb8202c2c5062c8b4
  | 2 => mk128 0x2000954020125009 0x4284c0402905010a
  | 3 => mk128 0x56aa000049a4ac80 0x104b009682b80ec0
  | 4 => mk128 0x98ccd98970003000 0x608fd60003d7a000
  | 5 => mk128 0x8811118000c111 0x830ffbfb7c000000
  | _ => 0
private theorem pp_0_0 : properPairs (subGoal 0 0) (asRow p_0_0) (asRow q_0_0) :=
  properPairs_of_ofRows (by decide +kernel)
private def rd_0_0 : List Decor := rawDecor (freeMask 0 0) p_0_0 q_0_0
private def sl_0_0 : List (Sig × Nat) := [(subcube 32 0, 9), (subcube 1 0, 8), (subcube 16 0, 8), (subcube 4 0, 8), (subcube 2 0, 6), (subcube 0 16, 6), (subcube 0 2, 6), (subcube 0 8, 6), (subcube 0 32, 6), (subcube 48 0, 6), (subcube 20 0, 5), (subcube 4 8, 5), (subcube 17 0, 5), (subcube 18 0, 5), (subcube 16 32, 5), (subcube 32 16, 5), (subcube 32 8, 5), (subcube 1 16, 5), (subcube 16 8, 5), (subcube 36 0, 5), (subcube 2 32, 5), (subcube 32 2, 5), (subcube 1 32, 5), (subcube 33 0, 5), (subcube 4 2, 5), (subcube 5 0, 5), (subcube 8 0, 5), (subcube 1 2, 5), (subcube 40 0, 4), (subcube 36 2, 4), (subcube 36 8, 4), (subcube 5 2, 4), (subcube 33 16, 4), (subcube 17 32, 4), (subcube 18 32, 4), (subcube 20 8, 4)]
private theorem sl_0_0_ok : ∀ s ∈ sl_0_0, Slice (freeVars 0 0) (subGoal 0 0) s.1 s.2 := by
  intro s hs
  simp only [sl_0_0, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact slice_correct (ms := fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_32_0
  · exact slice_correct (ms := fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_1_0
  · exact slice_correct (ms := fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_16_0
  · exact slice_correct (ms := fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_4_0
  · exact slice_correct (ms := fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_2_0
  · exact slice_correct (ms := fixRows 0 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_0_16
  · exact slice_correct (ms := fixRows 0 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_0_2
  · exact slice_correct (ms := fixRows 0 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_0_8
  · exact slice_correct (ms := fixRows 0 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_0_32
  · exact slice_correct (ms := fixRows 48 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_48_0
  · exact slice_correct (ms := fixRows 20 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_20_0
  · exact slice_correct (ms := fixRows 4 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_4_8
  · exact slice_correct (ms := fixRows 17 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_17_0
  · exact slice_correct (ms := fixRows 18 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_18_0
  · exact slice_correct (ms := fixRows 16 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_16_32
  · exact slice_correct (ms := fixRows 32 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_32_16
  · exact slice_correct (ms := fixRows 32 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_32_8
  · exact slice_correct (ms := fixRows 1 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_1_16
  · exact slice_correct (ms := fixRows 16 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_16_8
  · exact slice_correct (ms := fixRows 36 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_36_0
  · exact slice_correct (ms := fixRows 2 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_2_32
  · exact slice_correct (ms := fixRows 32 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_32_2
  · exact slice_correct (ms := fixRows 1 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_1_32
  · exact slice_correct (ms := fixRows 33 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_33_0
  · exact slice_correct (ms := fixRows 4 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_4_2
  · exact slice_correct (ms := fixRows 5 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_5_0
  · exact slice_correct (ms := fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_8_0
  · exact slice_correct (ms := fixRows 1 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_1_2
  · exact slice_correct (ms := fixRows 40 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_40_0
  · exact slice_correct (ms := fixRows 36 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_36_2
  · exact slice_correct (ms := fixRows 36 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_36_8
  · exact slice_correct (ms := fixRows 5 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_5_2
  · exact slice_correct (ms := fixRows 33 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_33_16
  · exact slice_correct (ms := fixRows 17 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_17_32
  · exact slice_correct (ms := fixRows 18 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_18_32
  · exact slice_correct (ms := fixRows 20 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) lower_20_8
private def ck70 := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] [] 5
private def d70 : List NodeSpec := [([(1,1,0),(1,2,0),(0,3,1),(2,6,8),(1,2,8)],[9,7,10,3,4,5],[]),([(1,1,0),(1,2,0),(0,3,1),(2,6,8),(1,4,2)],[9,8,7,3,10,5],[]),([(1,1,0),(1,2,0),(1,4,2),(0,8,3),(3,9,1)],[10,6,7,3,8,5],[]),([(1,1,0),(1,2,0),(1,4,2),(0,8,3),(3,9,6)],[10,1,7,3,8,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q70 : ck70 d70 = true := by decide +kernel
private def d71 : List NodeSpec := [([(1,1,0),(1,2,0),(1,4,2),(0,8,3),(1,5,9)],[1,6,7,3,8,10],[(10,[])]),([(1,1,0),(1,2,0),(1,4,2),(2,8,3),(2,1,9)],[10,6,7,3,8,5],[]),([(1,1,0),(1,2,0),(1,4,3),(0,8,1),(1,2,9)],[6,7,10,3,4,5],[]),([(1,1,0),(1,2,6),(0,3,7),(1,4,8),(3,5,9)],[10,0,1,2,8,4],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q71 : ck70 d71 = true := by decide +kernel
private def d72 : List NodeSpec := [([(1,1,0),(1,2,6),(0,3,7),(1,4,3),(3,5,9)],[10,0,1,2,8,4],[]),([(1,1,0),(0,3,1),(2,6,7),(1,2,7),(1,4,2)],[8,0,9,3,10,5],[]),([(1,1,0),(0,3,6),(1,2,7),(1,4,2),(0,9,3)],[0,1,8,10,9,5],[(6,[2,3])]),([(1,1,0),(0,3,6),(1,2,7),(1,4,2),(2,9,3)],[10,0,1,8,9,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q72 : ck70 d72 = true := by decide +kernel
private def lv_0_0_5_0 : List NodeSpec := (d70 ++ (d71 ++ d72))

private theorem ok_0_0_5_0 : LevelOK rd_0_0 (subGoal 0 0) 5 lv_0_0_5_0 :=
  levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_0_0 (subGoal 0 0) 4)
    (levelCheck_join q70 (levelCheck_join q71 q72))
private def ck73 := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] [] 5
private def d73 : List NodeSpec := [([(1,1,0),(3,4,6),(1,2,7),(1,3,8),(2,9,2)],[10,0,1,8,3,5],[]),([(1,1,0),(3,4,6),(1,2,7),(2,3,8),(1,2,9)],[0,1,8,3,10,5],[]),([(1,1,0),(3,4,6),(1,2,7),(2,3,8),(1,5,9)],[0,1,2,8,3,10],[]),([(1,1,0),(3,4,6),(1,2,7),(3,3,8),(1,5,9)],[0,1,2,8,3,10],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q73 : ck73 d73 = true := by decide +kernel
private def d74 : List NodeSpec := [([(1,1,0),(3,4,6),(1,2,7),(2,3,7),(1,5,9)],[0,1,2,8,3,10],[]),([(1,1,0),(3,4,6),(1,3,7),(2,3,7),(1,5,9)],[0,1,2,3,8,10],[]),([(1,1,0),(3,4,6),(1,3,7),(2,8,2),(1,5,2)],[7,9,0,1,3,10],[]),([(1,1,0),(3,4,6),(2,3,7),(1,5,8),(2,9,2)],[7,10,0,1,2,3],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q74 : ck73 d74 = true := by decide +kernel
private def d75 : List NodeSpec := [([(1,1,0),(1,4,2),(0,7,3),(1,5,8),(0,9,6)],[0,1,10,2,3,7],[(9,[])]),([(1,1,0),(1,4,2),(2,7,3),(2,1,8),(1,2,9)],[0,6,10,3,7,5],[]),([(1,1,0),(1,4,2),(2,7,3),(2,6,8),(1,2,9)],[0,1,10,3,7,5],[]),([(1,1,0),(2,4,2),(2,6,7),(1,3,8),(2,9,2)],[10,0,1,8,3,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q75 : ck73 d75 = true := by decide +kernel
private def lv_0_0_5_1 : List NodeSpec := (d73 ++ (d74 ++ d75))

private theorem ok_0_0_5_1 : LevelOK rd_0_0 (subGoal 0 0) 5 lv_0_0_5_1 :=
  levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_0_0 (subGoal 0 0) 4)
    (levelCheck_join q73 (levelCheck_join q74 q75))
private def ck76 := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] [] 5
private def d76 : List NodeSpec := [([(1,1,0),(1,4,3),(0,7,6),(1,2,8),(1,5,2)],[0,1,9,3,4,10],[(0,[])]),([(1,1,0),(1,4,3),(3,5,6),(1,2,8),(0,7,9)],[0,1,10,2,3,4],[]),([(1,2,0),(0,3,1),(1,6,7),(2,8,0),(1,4,2)],[9,1,8,3,10,5],[]),([(1,2,0),(1,4,2),(0,7,3),(3,8,1),(1,0,9)],[10,1,6,3,7,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q76 : ck76 d76 = true := by decide +kernel
private def d77 : List NodeSpec := [([(1,2,0),(1,4,2),(2,7,3),(2,1,8),(1,9,0)],[1,10,6,3,7,5],[]),([(1,2,0),(1,4,2),(2,7,3),(2,1,8),(1,6,9)],[0,1,10,3,7,5],[]),([(0,3,1),(1,6,0),(1,2,7),(2,8,0),(1,4,2)],[9,1,7,3,10,5],[]),([(0,3,1),(1,6,0),(1,4,0),(1,4,2),(2,8,2)],[10,1,7,3,9,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q77 : ck76 d77 = true := by decide +kernel
private def d78 : List NodeSpec := [([(0,3,1),(1,6,0),(1,4,2),(1,8,0),(0,9,3)],[1,7,2,10,8,5],[]),([(0,3,1),(1,2,6),(1,3,1),(1,5,2),(0,9,8)],[0,7,10,4],[(19,[0]),(31,[]),(34,[])]),([(0,3,1),(1,2,6),(1,4,2),(1,8,0),(0,9,3)],[0,1,7,10,8,5],[(6,[1,2])]),([(0,3,1),(1,3,1),(2,7,6),(3,2,8),(1,4,2)],[9,8,0,6,10,5],[(3,[0,1,2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q78 : ck76 d78 = true := by decide +kernel
private def lv_0_0_5_2 : List NodeSpec := (d76 ++ (d77 ++ d78))

private theorem ok_0_0_5_2 : LevelOK rd_0_0 (subGoal 0 0) 5 lv_0_0_5_2 :=
  levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_0_0 (subGoal 0 0) 4)
    (levelCheck_join q76 (levelCheck_join q77 q78))
private def lv_0_0_5_3 : List NodeSpec := [([(0, 3, 1), (1, 4, 0), (1, 4, 2), (2, 7, 2), (1, 6, 9)], [0, 1, 10, 3, 8, 5], []), ([(1, 4, 2), (2, 6, 3), (2, 1, 7), (1, 2, 8), (2, 9, 0)], [10, 0, 1, 3, 6, 5], [])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_0_0_5_3 : LevelOK rd_0_0 (subGoal 0 0) 5 lv_0_0_5_3 :=
  levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (emptyLevelOK rd_0_0 (subGoal 0 0) 4)
    (by decide +kernel : levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] [] 5 lv_0_0_5_3 = true)
private def lv_0_0_5 : List NodeSpec := ((lv_0_0_5_0 ++ lv_0_0_5_1) ++ (lv_0_0_5_2 ++ lv_0_0_5_3))
private theorem ok_0_0_5 : LevelOK rd_0_0 (subGoal 0 0) 5 lv_0_0_5 := (levelOK_append (levelOK_append ok_0_0_5_0 ok_0_0_5_1) (levelOK_append ok_0_0_5_2 ok_0_0_5_3))
private def ck79 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_5) 6
private def d79 : List NodeSpec := [([(1,1,0),(1,2,0),(0,3,1),(2,6,8)],[9,8,2,7,3,4,5],[]),([(1,1,0),(1,2,0),(0,3,1),(1,2,8)],[6,7,9,3,4,5],[(24,[]),(25,[2]),(0,[0,1,2,3]),(5,[0,1]),(7,[1,3])]),([(1,1,0),(1,2,0),(0,3,1),(1,2,8)],[8,6,7,9,3,4,5],[(6,[1,3])]),([(1,1,0),(1,2,0),(0,3,1),(1,4,2)],[8,6,7,3,9,5],[(24,[]),(25,[2]),(0,[0,1,2,3]),(5,[0,1]),(7,[1,3]),(10,[2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q79 : ck79 [0,1] d79 = true := by decide +kernel
private def d80 : List NodeSpec := [([(1,1,0),(1,2,0),(0,3,1),(1,4,2)],[8,6,7,3,4,9,5],[(5,[0,1])]),([(1,1,0),(1,2,0),(3,4,1),(2,3,8)],[6,2,7,9,3,4,5],[(17,[]),(25,[])]),([(1,1,0),(1,2,0),(1,4,2),(0,8,3)],[1,6,7,9,3,8,5],[(6,[1,2]),(0,[0,1,2]),(10,[]),(11,[])]),([(1,1,0),(1,2,0),(1,4,2),(2,8,3)],[9,1,6,7,3,8,5],[(7,[1,2]),(6,[1,2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q80 : ck79 [2,3,4,5] d80 = true := by decide +kernel
private def d81 : List NodeSpec := [([(1,1,0),(1,2,0),(1,4,3),(0,8,1)],[9,6,2,7,3,4,5],[(3,[2,3]),(17,[])]),([(1,1,0),(1,2,0),(1,4,3),(2,8,7)],[9,1,6,2,3,4,5],[(4,[]),(17,[])]),([(1,1,0),(1,2,0),(1,4,3),(3,5,8)],[9,1,6,2,7,3,4],[(3,[2,3]),(17,[])]),([(1,1,0),(1,2,1),(0,3,7),(3,8,6)],[9,0,2,8,3,4,5],[(1,[1,2,3])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q81 : ck79 [6] d81 = true := by decide +kernel
private def lv_0_0_6_0 : List NodeSpec := (d79 ++ (d80 ++ d81))

private theorem ok_0_0_6_0 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6_0 := by
  have go {ids ds} (h : ck79 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 6 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_5) h
  exact (levelOK_append (go q79) (levelOK_append (go q80) (go q81)))
private def ck82 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_5) 6
private def d82 : List NodeSpec := [([(1,1,0),(1,2,1),(0,3,7),(1,4,3)],[0,6,2,8,4,9,5],[(0,[0,1,2]),(1,[1,2])]),([(1,1,0),(1,2,1),(0,3,7),(3,4,3)],[9,0,6,2,8,4,5],[(18,[1])]),([(1,1,0),(1,2,1),(1,4,3),(2,8,0)],[9,6,2,7,3,4,5],[(1,[2])]),([(1,1,0),(1,2,1),(1,4,3),(0,8,7)],[0,6,2,9,3,4,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q82 : ck82 [] d82 = true := by decide +kernel
private def d83 : List NodeSpec := [([(1,1,0),(1,2,1),(1,4,3),(3,5,8)],[9,0,6,2,7,3,4],[(1,[2,3])]),([(1,1,0),(3,2,1),(1,4,3),(2,8,0)],[7,9,6,2,3,4,5],[]),([(1,1,0),(1,2,6),(0,3,7),(1,4,8)],[0,1,2,8,4,9,5],[(0,[0,1,2])]),([(1,1,0),(1,2,6),(0,3,7),(1,4,3)],[0,1,2,8,4,9,5],[(0,[0,1,2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q83 : ck82 [7,8] d83 = true := by decide +kernel
private def d84 : List NodeSpec := [([(1,1,0),(1,2,6),(1,4,3),(0,8,7)],[0,1,2,9,3,4,5],[(2,[0,1,3]),(0,[]),(8,[])]),([(1,1,0),(1,2,6),(1,4,3),(3,5,8)],[9,0,1,2,7,3,4],[(15,[]),(2,[3]),(7,[]),(8,[])]),([(1,1,0),(3,2,6),(1,4,3),(0,8,7)],[9,0,1,2,3,4,5],[(0,[]),(2,[]),(8,[])]),([(1,1,0),(3,2,6),(1,4,3),(2,8,2)],[7,9,0,1,3,4,5],[(5,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q84 : ck82 [8] d84 = true := by decide +kernel
private def lv_0_0_6_1 : List NodeSpec := (d82 ++ (d83 ++ d84))

private theorem ok_0_0_6_1 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6_1 := by
  have go {ids ds} (h : ck82 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 6 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_5) h
  exact (levelOK_append (go q82) (levelOK_append (go q83) (go q84)))
private def ck85 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_5) 6
private def d85 : List NodeSpec := [([(1,1,0),(3,2,6),(1,4,3),(3,5,8)],[9,7,0,1,2,3,4],[(15,[]),(2,[3]),(8,[])]),([(1,1,0),(0,3,1),(2,6,7),(1,2,7)],[8,0,2,9,3,4,5],[(20,[])]),([(1,1,0),(0,3,1),(2,6,7),(1,4,2)],[8,0,7,2,3,9,5],[]),([(1,1,0),(0,3,1),(2,6,7),(3,4,6)],[9,8,0,7,2,3,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q85 : ck85 [0,1,9] d85 = true := by decide +kernel
private def d86 : List NodeSpec := [([(1,1,0),(0,3,1),(1,2,7),(2,3,2)],[9,0,6,8,3,4,5],[(7,[2])]),([(1,1,0),(0,3,1),(1,2,7),(1,4,2)],[0,6,8,3,9,5],[(24,[]),(0,[0,1,2,3]),(1,[1,2,3]),(7,[2,3]),(10,[1])]),([(1,1,0),(0,3,1),(1,2,7),(1,4,2)],[0,6,8,3,4,9,5],[]),([(1,1,0),(0,3,1),(1,2,7),(1,5,2)],[0,6,8,3,4,9],[(20,[]),(24,[]),(7,[2,3])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q86 : ck85 [] d86 = true := by decide +kernel
private def d87 : List NodeSpec := [([(1,1,0),(0,3,1),(1,2,7),(1,4,2)],[0,7,6,8,3,9,5],[(6,[2,3]),(35,[])]),([(1,1,0),(0,3,1),(3,3,6),(3,4,6)],[9,8,0,7,2,3,5],[(1,[3])]),([(1,1,0),(0,3,1),(3,3,6),(3,5,6)],[9,8,0,7,2,3,4],[(6,[])]),([(1,1,0),(0,3,1),(1,4,3),(2,8,0)],[9,7,6,2,3,4,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q87 : ck85 [9] d87 = true := by decide +kernel
private def lv_0_0_6_2 : List NodeSpec := (d85 ++ (d86 ++ d87))

private theorem ok_0_0_6_2 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6_2 := by
  have go {ids ds} (h : ck85 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 6 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_5) h
  exact (levelOK_append (go q85) (levelOK_append (go q86) (go q87)))
private def ck88 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_5) 6
private def d88 : List NodeSpec := [([(1,1,0),(0,3,1),(1,4,3),(2,8,7)],[9,0,6,2,3,4,5],[]),([(1,1,0),(2,3,1),(1,4,3),(2,8,0)],[7,9,6,2,3,4,5],[(1,[2])]),([(1,1,0),(2,3,1),(1,4,3),(3,5,8)],[9,7,0,6,2,3,4],[(1,[2,3])]),([(1,1,0),(0,3,6),(1,2,7),(1,4,2)],[0,1,8,3,9,5],[(1,[1,2,3]),(2,[]),(3,[0,1]),(6,[2,3])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q88 : ck88 [10,11] d88 = true := by decide +kernel
private def d89 : List NodeSpec := [([(1,1,0),(0,3,6),(1,2,7),(1,4,2)],[0,1,8,3,4,9,5],[(2,[])]),([(1,1,0),(0,3,6),(1,2,7),(1,5,2)],[0,1,8,3,4,9],[(29,[]),(1,[1,2,3])]),([(1,1,0),(0,3,6),(1,2,7),(1,4,2)],[0,1,7,8,3,9,5],[(3,[]),(6,[2,3])]),([(1,1,0),(0,3,6),(1,2,7),(1,5,2)],[0,1,7,8,3,4,9],[(3,[]),(6,[2,3])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q89 : ck88 [] d89 = true := by decide +kernel
private def d90 : List NodeSpec := [([(1,1,0),(0,3,6),(3,4,1),(1,3,8)],[0,1,7,2,9,4,5],[]),([(1,1,0),(0,3,6),(1,4,7),(3,5,8)],[9,0,1,7,2,3,4],[]),([(1,1,0),(0,3,6),(1,4,2),(0,8,3)],[0,1,7,2,9,8,5],[(6,[2])]),([(1,1,0),(0,3,6),(1,4,2),(2,8,3)],[9,0,1,7,2,8,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q90 : ck88 [10,11] d90 = true := by decide +kernel
private def lv_0_0_6_3 : List NodeSpec := (d88 ++ (d89 ++ d90))

private theorem ok_0_0_6_3 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6_3 := by
  have go {ids ds} (h : ck88 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 6 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_5) h
  exact (levelOK_append (go q88) (levelOK_append (go q89) (go q90)))
private def ck91 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_5) 6
private def d91 : List NodeSpec := [([(1,1,0),(0,3,6),(1,4,2),(2,8,3)],[9,0,1,7,2,4,5],[]),([(1,1,0),(0,3,6),(1,4,3),(2,8,7)],[9,0,1,2,3,4,5],[(5,[])]),([(1,1,0),(0,3,6),(1,4,3),(3,5,8)],[9,0,1,7,2,3,4],[]),([(1,1,0),(0,3,6),(3,4,1),(2,3,8)],[0,7,6,2,9,4,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q91 : ck91 [] d91 = true := by decide +kernel
private def d92 : List NodeSpec := [([(1,1,0),(0,3,6),(3,4,6),(1,3,8)],[8,0,1,7,2,9,5],[]),([(1,1,0),(0,3,6),(3,4,6),(2,3,8)],[8,0,1,7,2,9,5],[(6,[])]),([(1,1,0),(0,3,6),(3,4,6),(1,3,8)],[0,1,7,2,9,4,5],[]),([(1,1,0),(2,3,6),(1,4,3),(2,8,7)],[0,1,9,2,3,4,5],[(0,[]),(2,[]),(8,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q92 : ck91 [] d92 = true := by decide +kernel
private def d93 : List NodeSpec := [([(1,1,0),(2,3,6),(1,4,3),(3,5,8)],[9,7,0,1,2,3,4],[(0,[2]),(2,[3]),(5,[]),(8,[])]),([(1,1,0),(3,3,6),(3,4,1),(2,3,8)],[7,0,6,2,9,4,5],[]),([(1,1,0),(3,3,6),(3,4,6),(1,3,8)],[8,7,0,1,2,9,5],[(0,[0,2])]),([(1,1,0),(3,3,6),(3,4,6),(2,3,8)],[8,7,0,1,2,9,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q93 : ck91 [] d93 = true := by decide +kernel
private def lv_0_0_6_4 : List NodeSpec := (d91 ++ (d92 ++ d93))

private theorem ok_0_0_6_4 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6_4 := by
  have go {ids ds} (h : ck91 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 6 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_5) h
  exact (levelOK_append (go q91) (levelOK_append (go q92) (go q93)))
private def ck94 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_5) 6
private def d94 : List NodeSpec := [([(1,1,0),(3,3,6),(3,4,6),(2,3,8)],[7,0,1,2,9,4,5],[]),([(1,1,0),(1,3,2),(2,3,2),(0,7,6)],[8,0,1,9,3,4,5],[(3,[])]),([(1,1,0),(1,3,2),(2,3,2),(3,4,6)],[9,8,0,1,3,7,5],[(0,[0,3])]),([(1,1,0),(1,3,2),(2,3,2),(3,5,6)],[9,8,0,1,3,7,4],[(0,[0])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q94 : ck94 [] d94 = true := by decide +kernel
private def d95 : List NodeSpec := [([(1,1,0),(1,3,2),(3,4,1),(2,3,8)],[0,6,2,9,7,4,5],[]),([(1,1,0),(1,3,2),(3,4,1),(2,7,8)],[0,6,2,3,9,4,5],[(1,[]),(2,[1,3])]),([(1,1,0),(1,3,2),(3,4,6),(1,3,8)],[8,0,1,2,9,7,5],[(3,[0,2])]),([(1,1,0),(1,3,2),(3,4,6),(2,3,8)],[8,0,1,2,9,7,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q95 : ck94 [] d95 = true := by decide +kernel
private def d96 : List NodeSpec := [([(1,1,0),(1,3,2),(3,4,6),(1,7,8)],[8,0,1,2,3,9,5],[]),([(1,1,0),(1,3,2),(3,4,6),(2,7,8)],[8,0,1,2,3,9,5],[(0,[0,2]),(20,[2])]),([(1,1,0),(1,3,2),(3,4,6),(2,3,8)],[0,1,2,9,7,4,5],[]),([(1,1,0),(1,3,2),(3,4,6),(2,7,8)],[0,1,2,3,9,4,5],[(0,[]),(5,[]),(8,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q96 : ck94 [] d96 = true := by decide +kernel
private def lv_0_0_6_5 : List NodeSpec := (d94 ++ (d95 ++ d96))

private theorem ok_0_0_6_5 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6_5 := by
  have go {ids ds} (h : ck94 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 6 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_5) h
  exact (levelOK_append (go q94) (levelOK_append (go q95) (go q96)))
private def ck97 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_5) 6
private def d97 : List NodeSpec := [([(1,1,0),(2,3,2),(3,4,1),(2,7,8)],[9,0,6,2,3,4,5],[(1,[])]),([(1,1,0),(2,3,2),(3,4,1),(2,3,8)],[7,0,6,2,9,4,5],[]),([(1,1,0),(2,3,2),(3,4,6),(1,7,8)],[8,9,0,1,2,3,5],[]),([(1,1,0),(2,3,2),(3,4,6),(2,7,8)],[8,9,0,1,2,3,5],[(0,[0,2]),(20,[2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q97 : ck97 [] d97 = true := by decide +kernel
private def d98 : List NodeSpec := [([(1,1,0),(2,3,2),(3,4,6),(1,3,8)],[8,7,0,1,2,9,5],[]),([(1,1,0),(2,3,2),(3,4,6),(2,3,8)],[8,7,0,1,2,9,5],[(3,[0,2])]),([(1,1,0),(3,4,1),(1,2,7),(0,3,8)],[0,6,9,2,3,4,5],[]),([(1,1,0),(3,4,1),(2,3,7),(1,8,0)],[6,2,8,3,9,4,5],[(1,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q98 : ck97 [] d98 = true := by decide +kernel
private def d99 : List NodeSpec := [([(1,1,0),(3,4,1),(2,3,7),(1,8,2)],[0,6,2,3,9,4,5],[(1,[])]),([(1,1,0),(3,4,1),(2,3,7),(3,5,6)],[9,0,6,2,8,3,4],[(1,[3])]),([(1,1,0),(3,4,1),(2,3,7),(1,5,2)],[0,6,2,8,3,4,9],[(1,[3])]),([(1,1,0),(3,4,1),(2,3,7),(1,8,0)],[1,6,2,3,9,4,5],[(2,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q99 : ck97 [] d99 = true := by decide +kernel
private def lv_0_0_6_6 : List NodeSpec := (d97 ++ (d98 ++ d99))

private theorem ok_0_0_6_6 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6_6 := by
  have go {ids ds} (h : ck97 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 6 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_5) h
  exact (levelOK_append (go q97) (levelOK_append (go q98) (go q99)))
private def ck100 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_5) 6
private def d100 : List NodeSpec := [([(1,1,0),(3,4,6),(1,2,7),(0,3,8)],[0,1,9,2,8,3,5],[]),([(1,1,0),(3,4,6),(1,2,7),(1,3,8)],[0,1,2,8,3,9,5],[]),([(1,1,0),(3,4,6),(1,2,7),(2,3,8)],[9,0,1,2,8,3,5],[(0,[0,1,2])]),([(1,1,0),(3,4,6),(1,2,7),(3,3,8)],[9,0,1,2,8,3,5],[(0,[0,1,2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q100 : ck100 [12,13,14,15] d100 = true := by decide +kernel
private def d101 : List NodeSpec := [([(1,1,0),(3,4,6),(1,2,7),(1,3,7)],[0,1,2,8,3,9,5],[(3,[0,1])]),([(1,1,0),(3,4,6),(1,2,7),(2,3,7)],[0,1,2,8,9,3,5],[(3,[0,1]),(0,[0,1,2])]),([(1,1,0),(3,4,6),(1,2,7),(0,3,8)],[7,0,1,9,2,3,5],[(3,[0,1])]),([(1,1,0),(3,4,6),(1,2,7),(3,3,8)],[7,9,0,1,2,3,5],[(0,[0,1]),(3,[0,1]),(20,[1])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q101 : ck100 [12,13,16] d101 = true := by decide +kernel
private def d102 : List NodeSpec := [([(1,1,0),(3,4,6),(1,3,7),(2,3,7)],[0,1,2,9,3,8,5],[(0,[0,1])]),([(1,1,0),(3,4,6),(1,3,7),(2,8,2)],[7,9,0,1,2,3,5],[(3,[0,1])]),([(1,1,0),(3,4,6),(1,3,7),(1,5,2)],[7,0,1,2,3,8,9],[(3,[0,1])]),([(1,1,0),(3,4,6),(2,3,7),(1,8,2)],[7,0,1,2,3,9,5],[(0,[0,1]),(3,[0,1]),(20,[1])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q102 : ck100 [12,13,17,18] d102 = true := by decide +kernel
private def lv_0_0_6_7 : List NodeSpec := (d100 ++ (d101 ++ d102))

private theorem ok_0_0_6_7 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6_7 := by
  have go {ids ds} (h : ck100 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 6 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_5) h
  exact (levelOK_append (go q100) (levelOK_append (go q101) (go q102)))
private def ck103 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_5) 6
private def d103 : List NodeSpec := [([(1,1,0),(3,4,6),(2,3,7),(1,5,2)],[7,0,1,2,8,3,9],[(20,[1]),(29,[])]),([(1,1,0),(3,4,6),(2,3,7),(1,5,8)],[7,0,1,2,3,9],[(5,[3]),(20,[1])]),([(1,1,0),(3,4,6),(2,3,7),(1,5,8)],[7,0,1,2,8,3,9],[(0,[0,1])]),([(1,1,0),(3,4,6),(2,3,7),(1,8,2)],[0,1,2,3,9,4,5],[(0,[]),(5,[]),(8,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q103 : ck103 [16,17,19] d103 = true := by decide +kernel
private def d104 : List NodeSpec := [([(1,1,0),(3,4,6),(2,3,7),(1,5,2)],[0,1,2,8,3,4,9],[(5,[3]),(8,[]),(19,[])]),([(1,1,0),(3,4,6),(1,3,7),(3,5,6)],[9,7,0,1,2,3,8],[]),([(1,1,0),(3,4,6),(2,3,7),(1,8,0)],[7,1,6,2,3,9,5],[(2,[0])]),([(1,1,0),(3,4,6),(2,3,7),(3,5,6)],[9,7,0,1,2,8,3],[(2,[0,3]),(21,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q104 : ck103 [] d104 = true := by decide +kernel
private def d105 : List NodeSpec := [([(1,1,0),(3,4,6),(2,3,7),(1,5,8)],[7,0,1,6,2,3,9],[(2,[0,2,3]),(9,[0]),(20,[1])]),([(1,1,0),(3,4,6),(1,3,7),(3,5,6)],[9,0,1,2,3,8,4],[(6,[])]),([(1,1,0),(3,4,6),(2,3,7),(3,5,6)],[9,0,1,2,8,3,4],[(2,[0,3]),(6,[]),(16,[])]),([(1,1,0),(1,4,2),(0,7,3),(1,8,0)],[1,6,2,3,9,7,5],[(10,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q105 : ck103 [] d105 = true := by decide +kernel
private def lv_0_0_6_8 : List NodeSpec := (d103 ++ (d104 ++ d105))

private theorem ok_0_0_6_8 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6_8 := by
  have go {ids ds} (h : ck103 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 6 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_5) h
  exact (levelOK_append (go q103) (levelOK_append (go q104) (go q105)))
private def ck106 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_5) 6
private def d106 : List NodeSpec := [([(1,1,0),(1,4,2),(0,7,3),(3,8,1)],[9,0,6,2,3,7,5],[(10,[])]),([(1,1,0),(1,4,2),(0,7,3),(3,8,6)],[9,0,1,2,3,7,5],[(0,[1]),(5,[]),(8,[1])]),([(1,1,0),(1,4,2),(0,7,3),(3,5,6)],[9,0,1,2,8,3,7],[(8,[1]),(21,[1])]),([(1,1,0),(1,4,2),(0,7,3),(1,5,8)],[0,1,6,2,3,7,9],[(5,[3]),(8,[1]),(10,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q106 : ck106 [2,3,4,20] d106 = true := by decide +kernel
private def d107 : List NodeSpec := [([(1,1,0),(1,4,2),(2,7,3),(2,1,8)],[0,9,6,2,3,7,5],[(10,[])]),([(1,1,0),(1,4,2),(2,7,3),(2,6,8)],[0,1,9,2,3,7,5],[(3,[]),(5,[])]),([(1,1,0),(1,4,2),(2,7,3),(3,5,6)],[9,8,0,1,2,3,7],[]),([(1,1,0),(1,4,2),(0,7,3),(1,8,0)],[1,6,2,3,9,4,5],[(2,[2,3]),(4,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q107 : ck106 [5,21,22] d107 = true := by decide +kernel
private def d108 : List NodeSpec := [([(1,1,0),(1,4,2),(0,7,3),(3,8,6)],[9,0,1,2,3,4,5],[(0,[]),(5,[]),(8,[])]),([(1,1,0),(1,4,2),(0,7,3),(3,5,6)],[9,0,1,2,8,3,4],[(3,[0,3]),(8,[]),(21,[])]),([(1,1,0),(1,4,2),(2,7,3),(2,6,8)],[0,1,9,2,3,4,5],[(5,[])]),([(1,1,0),(1,4,2),(2,7,3),(3,5,6)],[9,8,0,1,2,3,4],[(3,[0,3])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q108 : ck106 [] d108 = true := by decide +kernel
private def lv_0_0_6_9 : List NodeSpec := (d106 ++ (d107 ++ d108))

private theorem ok_0_0_6_9 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6_9 := by
  have go {ids ds} (h : ck106 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 6 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_5) h
  exact (levelOK_append (go q106) (levelOK_append (go q107) (go q108)))
private def ck109 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_5) 6
private def d109 : List NodeSpec := [([(1,1,0),(2,4,2),(2,6,7),(0,3,8)],[0,1,9,8,2,3,5],[]),([(1,1,0),(2,4,2),(2,6,7),(1,3,8)],[0,1,8,2,3,9,5],[(3,[0,2])]),([(1,1,0),(2,4,2),(2,6,7),(2,3,8)],[9,0,1,8,2,3,5],[(0,[0,1,2]),(33,[])]),([(1,1,0),(2,4,2),(2,6,7),(3,3,8)],[9,0,1,8,2,3,5],[(33,[]),(13,[]),(0,[0,1,2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q109 : ck109 [23] d109 = true := by decide +kernel
private def d110 : List NodeSpec := [([(1,1,0),(1,4,3),(2,7,0),(3,5,6)],[9,8,1,6,2,3,4],[(17,[3])]),([(1,1,0),(1,4,3),(2,7,0),(1,5,2)],[8,1,6,2,3,4,9],[(30,[])]),([(1,1,0),(1,4,3),(0,7,1),(1,2,8)],[0,6,2,9,3,4,5],[(3,[1,2]),(20,[])]),([(1,1,0),(1,4,3),(0,7,6),(1,2,8)],[0,1,2,9,3,4,5],[(6,[]),(0,[]),(1,[]),(4,[]),(8,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q110 : ck109 [6,24] d110 = true := by decide +kernel
private def d111 : List NodeSpec := [([(1,1,0),(1,4,3),(0,7,6),(3,5,8)],[9,0,1,8,2,3,4],[(0,[]),(2,[0,2,3])]),([(1,1,0),(1,4,3),(0,7,6),(1,5,2)],[0,1,8,2,3,4,9],[(19,[]),(2,[3]),(8,[])]),([(1,1,0),(1,4,3),(0,7,6),(3,5,6)],[9,0,1,8,2,3,4],[(0,[0,1,2]),(2,[0,3])]),([(1,1,0),(1,4,3),(2,7,2),(3,5,6)],[9,8,0,1,2,3,4],[(2,[0,3]),(8,[]),(17,[3]),(21,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q111 : ck109 [24] d111 = true := by decide +kernel
private def lv_0_0_6_10 : List NodeSpec := (d109 ++ (d110 ++ d111))

private theorem ok_0_0_6_10 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6_10 := by
  have go {ids ds} (h : ck109 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 6 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_5) h
  exact (levelOK_append (go q109) (levelOK_append (go q110) (go q111)))
private def ck112 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_5) 6
private def d112 : List NodeSpec := [([(1,1,0),(1,4,3),(3,5,6),(1,2,8)],[0,1,2,9,3,4,7],[(21,[])]),([(1,1,0),(3,4,3),(2,6,7),(3,5,6)],[9,0,1,8,2,3,4],[(1,[3]),(2,[0,3])]),([(1,1,0),(3,4,3),(1,2,7),(0,8,6)],[0,1,9,2,3,4,5],[(3,[])]),([(1,1,0),(3,4,3),(1,2,7),(3,5,6)],[9,0,1,2,8,3,4],[(2,[0,3]),(17,[3])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q112 : ck112 [25] d112 = true := by decide +kernel
private def d113 : List NodeSpec := [([(1,1,0),(3,4,3),(3,5,6),(1,2,8)],[7,0,1,2,9,3,4],[]),([(2,1,0),(1,2,6),(0,3,7),(1,4,3)],[0,1,2,8,4,9,5],[]),([(2,1,0),(1,2,6),(1,4,3),(0,8,7)],[0,1,2,9,3,4,5],[]),([(2,1,0),(1,2,1),(0,3,7),(1,8,0)],[6,2,8,9,3,4,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q113 : ck112 [] d113 = true := by decide +kernel
private def d114 : List NodeSpec := [([(2,1,0),(1,2,1),(0,3,7),(1,4,3)],[6,0,2,8,4,9,5],[(0,[0,1,2])]),([(2,1,0),(1,2,1),(0,3,7),(3,4,3)],[9,6,0,2,8,4,5],[(18,[1])]),([(2,1,0),(1,2,1),(1,4,3),(0,8,7)],[6,0,2,9,3,4,5],[]),([(2,1,0),(0,3,6),(1,2,7),(1,4,2)],[0,1,8,3,9,5],[(1,[1,2,3]),(2,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q114 : ck112 [] d114 = true := by decide +kernel
private def lv_0_0_6_11 : List NodeSpec := (d112 ++ (d113 ++ d114))

private theorem ok_0_0_6_11 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6_11 := by
  have go {ids ds} (h : ck112 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 6 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_5) h
  exact (levelOK_append (go q112) (levelOK_append (go q113) (go q114)))
private def ck115 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_5) 6
private def d115 : List NodeSpec := [([(2,1,0),(0,3,1),(1,2,7),(2,3,2)],[9,6,0,8,3,4,5],[(7,[2])]),([(2,1,0),(0,3,1),(1,2,7),(1,4,2)],[6,0,8,3,9,5],[(4,[3]),(11,[]),(1,[1,2,3]),(10,[1])]),([(2,1,0),(1,3,2),(3,4,6),(2,3,8)],[0,1,2,9,7,4,5],[]),([(2,1,0),(1,3,2),(3,4,6),(2,7,8)],[0,1,2,3,9,4,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q115 : ck115 [] d115 = true := by decide +kernel
private def d116 : List NodeSpec := [([(2,1,0),(1,3,2),(3,4,1),(2,3,8)],[6,0,2,9,7,4,5],[]),([(2,1,0),(1,3,2),(3,4,1),(2,7,8)],[6,0,2,3,9,4,5],[]),([(2,1,0),(2,3,2),(3,4,1),(2,7,8)],[9,6,0,2,3,4,5],[]),([(2,1,0),(2,3,2),(3,4,1),(2,3,8)],[7,6,0,2,9,4,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q116 : ck115 [] d116 = true := by decide +kernel
private def d117 : List NodeSpec := [([(2,1,0),(3,4,6),(2,3,7),(1,8,2)],[0,1,2,3,9,4,5],[]),([(2,1,0),(3,4,1),(1,2,7),(0,3,8)],[6,0,9,2,3,4,5],[(18,[2])]),([(2,1,0),(3,4,1),(2,3,7),(1,8,2)],[6,0,2,3,9,4,5],[]),([(1,2,0),(2,6,1),(1,4,3),(2,8,7)],[0,1,9,2,3,4,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q117 : ck115 [] d117 = true := by decide +kernel
private def lv_0_0_6_12 : List NodeSpec := (d115 ++ (d116 ++ d117))

private theorem ok_0_0_6_12 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6_12 := by
  have go {ids ds} (h : ck115 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 6 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_5) h
  exact (levelOK_append (go q115) (levelOK_append (go q116) (go q117)))
private def ck118 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_5) 6
private def d118 : List NodeSpec := [([(1,2,0),(2,6,1),(1,4,3),(0,8,1)],[7,0,9,2,3,4,5],[]),([(1,2,0),(2,6,1),(1,4,3),(3,5,8)],[9,7,0,1,2,3,4],[]),([(1,2,0),(0,3,1),(1,7,0),(3,2,8)],[9,1,8,6,3,4,5],[]),([(1,2,0),(0,3,1),(1,7,0),(1,4,2)],[1,8,6,3,9,5],[(25,[1]),(1,[3]),(10,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q118 : ck118 [] d118 = true := by decide +kernel
private def d119 : List NodeSpec := [([(1,2,0),(0,3,1),(1,7,0),(1,4,2)],[1,8,6,3,4,9,5],[]),([(1,2,0),(0,3,1),(1,7,0),(1,4,6)],[1,8,2,3,4,9,5],[(4,[]),(26,[])]),([(1,2,0),(0,3,1),(1,7,0),(1,2,7)],[1,8,6,9,3,4,5],[(31,[])]),([(1,2,0),(0,3,1),(1,7,0),(1,4,2)],[7,1,8,6,3,9,5],[(31,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q119 : ck118 [] d119 = true := by decide +kernel
private def d120 : List NodeSpec := [([(1,2,0),(0,3,1),(1,2,7),(2,8,0)],[9,1,6,8,3,4,5],[(31,[])]),([(1,2,0),(0,3,1),(1,2,7),(1,4,6)],[0,1,8,3,4,9,5],[(4,[]),(31,[])]),([(1,2,0),(0,3,1),(1,6,7),(2,8,0)],[9,1,2,8,3,4,5],[(0,[])]),([(1,2,0),(0,3,1),(1,6,7),(2,8,2)],[9,0,1,8,3,4,5],[(0,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q120 : ck118 [26] d120 = true := by decide +kernel
private def lv_0_0_6_13 : List NodeSpec := (d118 ++ (d119 ++ d120))

private theorem ok_0_0_6_13 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6_13 := by
  have go {ids ds} (h : ck118 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 6 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_5) h
  exact (levelOK_append (go q118) (levelOK_append (go q119) (go q120)))
private def ck121 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_5) 6
private def d121 : List NodeSpec := [([(1,2,0),(0,3,1),(1,6,7),(1,4,2)],[0,1,8,3,9,5],[(31,[]),(2,[])]),([(1,2,0),(0,3,1),(1,6,7),(1,4,2)],[0,1,8,3,4,9,5],[(2,[])]),([(1,2,0),(0,3,1),(1,6,7),(1,4,2)],[0,7,1,8,3,9,5],[(31,[])]),([(1,2,0),(0,3,1),(1,4,6),(2,8,7)],[9,0,1,2,3,4,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q121 : ck121 [26] d121 = true := by decide +kernel
private def d122 : List NodeSpec := [([(1,2,0),(3,3,1),(1,0,7),(3,2,8)],[9,8,1,6,3,4,5],[]),([(1,2,0),(3,3,1),(1,0,7),(1,4,2)],[8,1,6,3,9,5],[(11,[]),(1,[1,3]),(10,[]),(2,[1,2]),(25,[1])]),([(1,2,0),(3,3,1),(1,6,7),(2,8,2)],[9,0,1,8,3,4,5],[(0,[])]),([(1,2,0),(1,3,6),(2,7,0),(1,4,2)],[8,1,6,3,9,5],[(25,[]),(6,[0,3]),(10,[]),(2,[0,1,2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q122 : ck121 [] d122 = true := by decide +kernel
private def d123 : List NodeSpec := [([(1,2,0),(2,3,6),(3,4,1),(1,7,8)],[9,0,1,2,3,4,5],[]),([(1,2,0),(2,3,6),(3,4,1),(1,0,8)],[7,9,1,2,3,4,5],[(4,[])]),([(1,2,0),(3,4,1),(1,6,7),(2,8,0)],[9,1,2,8,3,4,5],[(17,[])]),([(1,2,0),(3,4,1),(2,3,7),(1,8,0)],[1,2,6,3,9,4,5],[(3,[]),(17,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q123 : ck121 [] d123 = true := by decide +kernel
private def lv_0_0_6_14 : List NodeSpec := (d121 ++ (d122 ++ d123))

private theorem ok_0_0_6_14 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6_14 := by
  have go {ids ds} (h : ck121 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 6 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_5) h
  exact (levelOK_append (go q121) (levelOK_append (go q122) (go q123)))
private def ck124 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_5) 6
private def d124 : List NodeSpec := [([(1,2,0),(3,4,1),(2,3,7),(1,8,6)],[0,1,2,3,9,4,5],[]),([(1,2,0),(1,4,2),(0,7,1),(1,8,0)],[1,9,6,3,7,5],[(35,[]),(1,[1,2])]),([(1,2,0),(1,4,2),(0,7,3),(1,8,0)],[1,6,3,9,7,5],[(1,[1,2]),(3,[]),(5,[0,3]),(6,[0,1]),(2,[2,3]),(7,[0,1])]),([(1,2,0),(1,4,2),(0,7,3),(3,8,1)],[9,0,1,6,3,7,5],[(1,[1])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q124 : ck124 [2,27] d124 = true := by decide +kernel
private def d125 : List NodeSpec := [([(1,2,0),(1,4,2),(0,7,3),(1,5,8)],[0,1,6,3,7,9],[(10,[]),(11,[3]),(1,[1,2,3])]),([(1,2,0),(1,4,2),(2,7,3),(2,1,8)],[0,9,1,6,3,7,5],[(25,[])]),([(1,2,0),(1,4,3),(0,7,1),(1,8,0)],[1,9,2,6,3,4,5],[(3,[]),(17,[])]),([(1,2,0),(1,4,3),(0,7,1),(1,2,8)],[0,1,6,9,3,4,5],[(1,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q125 : ck124 [4,5,6,28,29] d125 = true := by decide +kernel
private def d126 : List NodeSpec := [([(1,2,0),(1,4,3),(0,7,1),(1,6,8)],[0,1,2,9,3,4,5],[(6,[]),(0,[]),(4,[]),(8,[])]),([(1,2,1),(2,6,0),(0,3,7),(1,4,3)],[8,0,1,2,4,9,5],[]),([(1,2,1),(2,6,0),(1,4,3),(0,8,7)],[9,0,1,2,3,4,5],[]),([(1,2,1),(2,6,0),(1,4,3),(2,8,0)],[7,9,1,2,3,4,5],[(5,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q126 : ck124 [] d126 = true := by decide +kernel
private def lv_0_0_6_15 : List NodeSpec := (d124 ++ (d125 ++ d126))

private theorem ok_0_0_6_15 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6_15 := by
  have go {ids ds} (h : ck124 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 6 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_5) h
  exact (levelOK_append (go q124) (levelOK_append (go q125) (go q126)))
private def ck127 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_5) 6
private def d127 : List NodeSpec := [([(1,2,1),(2,6,0),(1,4,3),(3,5,8)],[9,7,0,1,2,3,4],[]),([(1,2,1),(2,3,0),(2,6,7),(1,4,3)],[8,0,1,2,4,9,5],[]),([(1,2,1),(2,3,0),(2,6,7),(3,4,3)],[9,8,0,1,2,4,5],[]),([(1,2,1),(2,3,0),(1,4,7),(0,8,6)],[0,1,2,9,3,4,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q127 : ck127 [] d127 = true := by decide +kernel
private def d128 : List NodeSpec := [([(1,2,1),(2,3,0),(3,4,7),(2,6,8)],[0,1,2,9,3,4,5],[]),([(1,2,1),(1,3,1),(0,3,6),(2,7,8)],[9,0,2,8,4,5],[(3,[1,2,3])]),([(1,2,1),(0,3,6),(1,7,0),(1,4,0)],[1,2,8,3,4,9,5],[(26,[])]),([(1,2,1),(0,3,6),(1,7,0),(1,4,3)],[0,1,2,8,4,9,5],[(1,[0,1])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q128 : ck127 [] d128 = true := by decide +kernel
private def d129 : List NodeSpec := [([(1,2,1),(0,3,6),(1,7,0),(3,4,3)],[9,0,1,2,8,4,5],[(1,[0,1])]),([(1,2,1),(0,3,6),(1,4,3),(2,8,7)],[9,0,1,2,7,4,5],[]),([(1,2,1),(1,4,0),(0,7,3),(1,8,2)],[0,1,6,3,9,4,5],[(4,[])]),([(1,2,1),(1,4,0),(0,7,3),(3,8,6)],[9,0,1,2,3,4,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q129 : ck127 [] d129 = true := by decide +kernel
private def lv_0_0_6_16 : List NodeSpec := (d127 ++ (d128 ++ d129))

private theorem ok_0_0_6_16 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6_16 := by
  have go {ids ds} (h : ck127 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 6 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_5) h
  exact (levelOK_append (go q127) (levelOK_append (go q128) (go q129)))
private def ck130 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_5) 6
private def d130 : List NodeSpec := [([(1,2,1),(3,4,1),(2,3,7),(1,8,2)],[0,1,6,3,9,4,5],[(2,[])]),([(1,2,1),(1,4,3),(0,7,6),(1,8,0)],[0,1,2,9,3,4,5],[(6,[]),(0,[]),(8,[])]),([(3,2,1),(1,0,6),(1,4,3),(2,8,0)],[9,7,1,2,3,4,5],[(4,[])]),([(3,2,1),(1,0,6),(1,4,3),(0,8,7)],[0,9,1,2,3,4,5],[(0,[]),(2,[]),(8,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q130 : ck130 [] d130 = true := by decide +kernel
private def d131 : List NodeSpec := [([(1,3,0),(0,6,1),(1,2,7),(1,4,2)],[0,1,8,3,9,5],[(31,[]),(4,[3]),(2,[])]),([(2,3,0),(0,1,6),(1,0,7),(1,2,6)],[1,8,2,9,3,4,5],[]),([(2,3,0),(0,1,6),(1,0,7),(1,3,2)],[6,1,8,2,9,4,5],[(25,[1])]),([(2,3,0),(0,1,6),(1,0,7),(1,4,6)],[1,8,2,3,4,9,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q131 : ck130 [] d131 = true := by decide +kernel
private def d132 : List NodeSpec := [([(2,3,0),(0,1,6),(1,0,7),(1,4,2)],[6,1,8,2,3,9,5],[(4,[3])]),([(2,3,0),(0,1,6),(1,0,7),(2,4,2)],[9,6,1,8,2,3,5],[(4,[3])]),([(2,3,0),(0,1,6),(1,0,7),(1,4,3)],[6,1,8,2,4,9,5],[]),([(2,3,0),(0,1,6),(1,0,7),(1,5,2)],[6,1,8,2,3,4,9],[(4,[3])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q132 : ck130 [] d132 = true := by decide +kernel
private def lv_0_0_6_17 : List NodeSpec := (d130 ++ (d131 ++ d132))

private theorem ok_0_0_6_17 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6_17 := by
  have go {ids ds} (h : ck130 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 6 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_5) h
  exact (levelOK_append (go q130) (levelOK_append (go q131) (go q132)))
private def ck133 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_5) 6
private def d133 : List NodeSpec := [([(2,3,0),(0,1,6),(1,1,6),(2,8,7)],[9,0,2,3,4,5],[(31,[])]),([(2,3,0),(0,1,6),(1,1,6),(1,4,3)],[7,0,8,2,4,9,5],[]),([(2,3,0),(0,1,6),(1,2,7),(1,4,2)],[6,0,1,8,3,9,5],[(4,[3]),(31,[])]),([(2,3,0),(0,1,6),(1,2,7),(1,5,2)],[6,0,1,8,3,4,9],[(4,[3]),(31,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q133 : ck133 [] d133 = true := by decide +kernel
private def d134 : List NodeSpec := [([(2,3,0),(0,1,6),(1,4,6),(2,8,7)],[0,9,1,2,3,4,5],[(5,[])]),([(2,3,0),(0,1,6),(1,4,3),(2,8,7)],[6,0,9,1,2,4,5],[]),([(2,3,0),(1,1,6),(0,3,1),(1,4,3)],[0,8,7,2,4,9,5],[(0,[0,1,2])]),([(2,3,0),(1,1,6),(1,4,3),(0,8,1)],[0,9,7,2,3,4,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q134 : ck133 [] d134 = true := by decide +kernel
private def d135 : List NodeSpec := [([(2,3,0),(1,1,6),(1,4,3),(3,5,8)],[9,0,1,7,2,3,4],[]),([(2,3,0),(1,1,6),(1,4,6),(0,8,1)],[0,9,7,2,3,4,5],[]),([(2,3,0),(2,1,6),(1,2,7),(1,3,2)],[0,1,8,3,9,4,5],[(1,[])]),([(2,3,0),(2,1,6),(3,1,6),(1,7,8)],[7,9,0,2,3,4,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q135 : ck133 [] d135 = true := by decide +kernel
private def lv_0_0_6_18 : List NodeSpec := (d133 ++ (d134 ++ d135))

private theorem ok_0_0_6_18 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6_18 := by
  have go {ids ds} (h : ck133 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 6 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_5) h
  exact (levelOK_append (go q133) (levelOK_append (go q134) (go q135)))
private def ck136 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_5) 6
private def d136 : List NodeSpec := [([(2,3,0),(2,1,6),(1,2,6),(1,2,7)],[0,1,8,9,3,4,5],[(0,[])]),([(2,3,0),(2,1,6),(1,2,7),(1,3,2)],[6,0,1,8,9,4,5],[]),([(2,3,0),(2,1,6),(3,4,6),(1,7,8)],[9,0,1,2,3,4,5],[]),([(2,3,0),(3,1,6),(1,0,7),(1,4,3)],[6,8,1,2,4,9,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q136 : ck136 [] d136 = true := by decide +kernel
private def d137 : List NodeSpec := [([(2,3,0),(3,1,6),(1,4,3),(2,8,7)],[6,0,1,9,2,4,5],[]),([(2,3,0),(1,2,6),(0,7,1),(1,8,0)],[1,9,2,7,3,4,5],[(4,[])]),([(2,3,0),(1,2,6),(3,4,1),(1,0,8)],[9,1,2,7,3,4,5],[]),([(2,3,0),(1,2,6),(3,4,1),(1,7,8)],[0,1,2,9,3,4,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q137 : ck136 [] d137 = true := by decide +kernel
private def d138 : List NodeSpec := [([(2,3,0),(1,2,6),(3,4,1),(2,7,8)],[0,1,2,9,3,4,5],[(0,[]),(5,[]),(8,[])]),([(2,3,0),(1,2,6),(1,4,7),(2,8,2)],[9,0,1,7,3,4,5],[(0,[])]),([(2,3,0),(1,2,6),(0,7,1),(1,8,0)],[6,1,9,2,3,4,5],[(4,[])]),([(2,3,0),(1,2,6),(1,4,3),(2,8,2)],[9,6,0,1,7,4,5],[(7,[1])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q138 : ck136 [] d138 = true := by decide +kernel
private def lv_0_0_6_19 : List NodeSpec := (d136 ++ (d137 ++ d138))

private theorem ok_0_0_6_19 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6_19 := by
  have go {ids ds} (h : ck136 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 6 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_5) h
  exact (levelOK_append (go q136) (levelOK_append (go q137) (go q138)))
private def ck139 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_5) 6
private def d139 : List NodeSpec := [([(2,3,0),(3,2,6),(1,4,3),(2,8,7)],[6,0,1,2,9,4,5],[(7,[1])]),([(2,3,0),(0,3,1),(1,2,7),(1,4,2)],[6,0,1,8,3,9,5],[(4,[3]),(11,[]),(24,[])]),([(2,3,0),(0,3,1),(1,2,7),(1,5,2)],[6,0,1,8,3,4,9],[(4,[3]),(11,[]),(24,[])]),([(2,3,0),(0,3,1),(1,4,6),(2,8,7)],[9,0,1,2,3,4,5],[(5,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q139 : ck139 [] d139 = true := by decide +kernel
private def d140 : List NodeSpec := [([(2,3,0),(1,3,2),(0,7,1),(1,8,0)],[6,1,9,2,7,4,5],[(25,[2])]),([(2,3,0),(1,3,2),(3,4,6),(2,7,8)],[6,0,1,2,9,4,5],[]),([(2,3,0),(1,3,2),(3,4,1),(1,6,8)],[9,0,1,2,7,4,5],[]),([(2,3,0),(1,3,2),(3,4,1),(2,6,8)],[9,0,1,2,7,4,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q140 : ck139 [] d140 = true := by decide +kernel
private def d141 : List NodeSpec := [([(2,3,0),(1,3,2),(3,4,1),(1,0,8)],[6,9,1,2,7,4,5],[]),([(2,3,0),(2,3,2),(3,4,1),(1,6,8)],[7,9,0,1,2,4,5],[]),([(2,3,0),(2,3,2),(3,4,1),(1,0,8)],[7,6,9,1,2,4,5],[]),([(2,3,0),(3,4,1),(1,6,7),(3,2,8)],[9,0,1,2,3,4,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q141 : ck139 [] d141 = true := by decide +kernel
private def lv_0_0_6_20 : List NodeSpec := (d139 ++ (d140 ++ d141))

private theorem ok_0_0_6_20 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6_20 := by
  have go {ids ds} (h : ck139 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 6 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_5) h
  exact (levelOK_append (go q139) (levelOK_append (go q140) (go q141)))
private def ck142 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_5) 6
private def d142 : List NodeSpec := [([(2,3,0),(3,4,1),(1,6,7),(1,5,2)],[8,0,1,2,3,4,9],[]),([(2,3,0),(3,4,1),(2,6,7),(1,2,8)],[0,1,2,9,3,4,5],[(0,[]),(5,[]),(8,[])]),([(2,3,0),(3,4,1),(2,6,7),(1,5,2)],[8,0,1,2,3,4,9],[(5,[3]),(8,[]),(19,[])]),([(2,3,0),(3,4,1),(1,0,7),(1,5,2)],[6,8,1,2,3,4,9],[(4,[3])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q142 : ck142 [] d142 = true := by decide +kernel
private def d143 : List NodeSpec := [([(2,3,0),(3,4,1),(1,2,7),(2,8,6)],[9,0,1,2,3,4,5],[(0,[]),(2,[]),(8,[])]),([(0,3,1),(1,6,0),(1,2,7),(2,8,0)],[9,1,7,2,3,4,5],[(0,[])]),([(0,3,1),(1,6,0),(1,2,7),(1,4,2)],[0,1,7,8,3,9,5],[(3,[])]),([(0,3,1),(1,6,0),(1,3,2),(2,8,0)],[9,1,7,2,3,4,5],[(0,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q143 : ck142 [30] d143 = true := by decide +kernel
private def d144 : List NodeSpec := [([(0,3,1),(1,6,0),(1,4,0),(3,4,7)],[9,1,7,2,3,8,5],[]),([(0,3,1),(1,6,0),(1,4,0),(1,4,2)],[1,7,2,3,8,9,5],[(10,[])]),([(0,3,1),(1,6,0),(1,4,0),(2,8,2)],[9,1,7,2,3,4,5],[]),([(0,3,1),(1,6,0),(1,4,2),(1,8,0)],[1,7,2,3,8,9,5],[(4,[2]),(10,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q144 : ck142 [31,32] d144 = true := by decide +kernel
private def lv_0_0_6_21 : List NodeSpec := (d142 ++ (d143 ++ d144))

private theorem ok_0_0_6_21 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6_21 := by
  have go {ids ds} (h : ck142 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 6 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_5) h
  exact (levelOK_append (go q142) (levelOK_append (go q143) (go q144)))
private def ck145 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_5) 6
private def d145 : List NodeSpec := [([(0,3,1),(1,6,0),(1,4,3),(2,8,0)],[9,1,7,2,3,4,5],[(0,[])]),([(0,3,1),(1,6,0),(1,4,3),(2,8,7)],[9,0,1,2,3,4,5],[(5,[])]),([(0,3,1),(1,6,0),(1,2,6),(3,2,7)],[9,0,1,8,3,4,5],[(31,[])]),([(0,3,1),(1,6,0),(1,2,6),(1,4,2)],[0,1,7,8,3,9,5],[(31,[]),(4,[3])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q145 : ck145 [30] d145 = true := by decide +kernel
private def d146 : List NodeSpec := [([(0,3,1),(1,6,0),(1,3,1),(2,8,0)],[9,6,7,2,3,4,5],[]),([(0,3,1),(1,6,0),(1,3,1),(2,8,6)],[9,0,7,2,3,4,5],[(1,[0,2,3])]),([(0,3,1),(1,6,0),(1,3,1),(2,8,7)],[9,0,6,2,3,4,5],[(1,[0,2])]),([(0,3,1),(1,2,6),(1,7,0),(1,4,2)],[0,1,7,8,3,9,5],[(31,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q146 : ck145 [26] d146 = true := by decide +kernel
private def d147 : List NodeSpec := [([(0,3,1),(1,2,6),(1,7,0),(1,5,2)],[0,1,7,8,3,4,9],[(31,[])]),([(0,3,1),(1,2,6),(2,7,0),(1,4,2)],[8,0,1,3,9,5],[(10,[]),(1,[0,1,3])]),([(0,3,1),(1,2,6),(2,7,0),(1,4,2)],[8,0,1,3,4,9,5],[(2,[])]),([(0,3,1),(1,2,6),(2,7,0),(1,4,2)],[8,0,1,7,3,9,5],[(31,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q147 : ck145 [26] d147 = true := by decide +kernel
private def lv_0_0_6_22 : List NodeSpec := (d145 ++ (d146 ++ d147))

private theorem ok_0_0_6_22 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6_22 := by
  have go {ids ds} (h : ck145 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 6 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_5) h
  exact (levelOK_append (go q145) (levelOK_append (go q146) (go q147)))
private def ck148 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_5) 6
private def d148 : List NodeSpec := [([(0,3,1),(1,2,6),(2,7,0),(1,5,2)],[8,0,1,7,3,4,9],[(31,[])]),([(0,3,1),(1,2,6),(1,3,1),(1,4,2)],[0,7,8,9,5],[(31,[]),(0,[0,1,2,3]),(35,[])]),([(0,3,1),(1,2,6),(1,3,1),(1,5,2)],[0,7,8,4,9],[(31,[]),(34,[])]),([(0,3,1),(1,2,6),(1,4,0),(1,4,2)],[0,1,7,3,8,9,5],[(12,[]),(31,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q148 : ck148 [33] d148 = true := by decide +kernel
private def d149 : List NodeSpec := [([(0,3,1),(1,2,6),(1,4,2),(1,8,0)],[0,1,7,3,8,9,5],[(31,[]),(4,[2]),(11,[]),(12,[])]),([(0,3,1),(1,2,6),(1,4,2),(1,8,7)],[0,1,7,3,8,9,5],[(35,[])]),([(0,3,1),(1,2,6),(1,4,2),(3,4,7)],[9,0,1,7,3,8,5],[(35,[])]),([(0,3,1),(1,2,6),(2,7,0),(1,4,2)],[8,0,6,1,3,9,5],[(31,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q149 : ck148 [30,34] d149 = true := by decide +kernel
private def d150 : List NodeSpec := [([(0,3,1),(1,2,6),(1,3,1),(1,4,2)],[0,6,7,8,9,5],[(31,[]),(4,[3]),(35,[]),(0,[0,1,2,3])]),([(0,3,1),(1,3,1),(2,7,6),(3,5,7)],[9,8,0,2,4],[(11,[]),(16,[]),(18,[]),(27,[])]),([(0,3,1),(1,3,1),(2,7,6),(1,0,8)],[8,0,9,6,2,4,5],[]),([(0,3,1),(1,3,1),(2,7,6),(3,0,8)],[9,8,0,6,2,4,5],[(1,[0,1,2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q150 : ck148 [] d150 = true := by decide +kernel
private def lv_0_0_6_23 : List NodeSpec := (d148 ++ (d149 ++ d150))

private theorem ok_0_0_6_23 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6_23 := by
  have go {ids ds} (h : ck148 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 6 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_5) h
  exact (levelOK_append (go q148) (levelOK_append (go q149) (go q150)))
private def ck151 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_5) 6
private def d151 : List NodeSpec := [([(0,3,1),(1,3,1),(2,7,6),(1,2,8)],[8,0,6,2,9,4,5],[(0,[0,1,2,3])]),([(0,3,1),(1,3,1),(2,7,6),(3,2,8)],[9,8,0,6,2,4,5],[(3,[0,1,2])]),([(0,3,1),(1,3,1),(2,7,6),(1,4,2)],[8,0,6,2,9,5],[(31,[]),(0,[0,1,2,3]),(2,[0,1,2]),(4,[3])]),([(0,3,1),(1,3,1),(1,5,2),(0,8,7)],[0,6,2,9,4],[(19,[0]),(20,[]),(31,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q151 : ck151 [33,35] d151 = true := by decide +kernel
private def d152 : List NodeSpec := [([(0,3,1),(1,3,1),(2,7,6),(1,0,8)],[8,0,9,2,3,4,5],[]),([(0,3,1),(1,3,1),(2,7,6),(3,0,8)],[9,8,0,2,3,4,5],[(1,[0,1,2])]),([(0,3,1),(1,3,1),(2,7,6),(1,0,8)],[0,9,6,2,3,4,5],[(1,[0,1,2])]),([(0,3,1),(1,4,0),(1,4,2),(2,7,2)],[9,0,6,1,3,8,5],[(12,[]),(31,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q152 : ck151 [31,36] d152 = true := by decide +kernel
private def d153 : List NodeSpec := [([(0,3,1),(1,4,0),(2,7,2),(1,6,8)],[0,1,9,2,3,4,5],[(0,[]),(2,[]),(8,[])]),([(0,3,1),(1,4,2),(1,7,0),(2,8,6)],[9,0,1,2,3,7,5],[(3,[]),(12,[])]),([(0,3,1),(1,4,2),(1,7,0),(0,8,3)],[0,6,1,2,9,7,5],[(5,[]),(6,[1])]),([(0,3,1),(1,4,3),(2,7,6),(1,0,8)],[0,9,1,2,3,4,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q153 : ck151 [32,34,36] d153 = true := by decide +kernel
private def lv_0_0_6_24 : List NodeSpec := (d151 ++ (d152 ++ d153))

private theorem ok_0_0_6_24 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6_24 := by
  have go {ids ds} (h : ck151 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 6 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_5) h
  exact (levelOK_append (go q151) (levelOK_append (go q152) (go q153)))
private def ck154 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_5) 6
private def d154 : List NodeSpec := [([(2,3,1),(1,0,6),(1,4,3),(2,8,0)],[9,7,1,2,3,4,5],[(0,[])]),([(2,3,1),(1,0,6),(1,4,3),(3,5,8)],[9,0,7,1,2,3,4],[]),([(2,3,1),(2,3,6),(1,2,7),(1,4,2)],[0,1,8,3,9,5],[(31,[]),(4,[3]),(2,[])]),([(1,3,2),(2,6,0),(0,1,7),(1,0,8)],[7,1,9,2,3,4,5],[(4,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q154 : ck154 [] d154 = true := by decide +kernel
private def d155 : List NodeSpec := [([(1,3,2),(2,6,0),(3,4,1),(1,7,8)],[9,0,1,2,3,4,5],[]),([(1,3,2),(2,6,0),(3,4,1),(2,7,8)],[9,0,1,2,3,4,5],[(0,[]),(5,[]),(8,[])]),([(1,3,2),(2,6,0),(3,4,1),(1,0,8)],[7,9,1,2,3,4,5],[(4,[])]),([(1,3,2),(1,4,0),(0,7,1),(1,2,8)],[0,1,9,3,6,4,5],[(4,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q155 : ck154 [] d155 = true := by decide +kernel
private def d156 : List NodeSpec := [([(1,3,2),(1,4,0),(0,7,1),(2,3,8)],[9,0,1,2,6,4,5],[]),([(1,3,2),(1,4,0),(0,7,1),(2,6,8)],[9,0,1,2,3,4,5],[]),([(1,3,2),(3,4,1),(2,3,7),(1,8,0)],[0,1,2,9,6,4,5],[]),([(1,3,2),(3,4,1),(2,3,7),(2,6,8)],[9,0,1,2,8,4,5],[(5,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q156 : ck154 [] d156 = true := by decide +kernel
private def lv_0_0_6_25 : List NodeSpec := (d154 ++ (d155 ++ d156))

private theorem ok_0_0_6_25 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6_25 := by
  have go {ids ds} (h : ck154 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 6 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_5) h
  exact (levelOK_append (go q154) (levelOK_append (go q155) (go q156)))
private def ck157 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_5) 6
private def d157 : List NodeSpec := [([(1,3,2),(3,4,1),(2,6,7),(1,8,0)],[0,1,2,3,9,4,5],[]),([(2,3,2),(3,4,1),(2,6,7),(1,0,8)],[0,9,1,2,3,4,5],[]),([(2,3,2),(3,4,1),(2,3,7),(1,8,0)],[6,0,1,2,9,4,5],[]),([(1,4,0),(1,4,2),(0,6,1),(2,3,8)],[9,0,1,2,3,7,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q157 : ck157 [] d157 = true := by decide +kernel
private def d158 : List NodeSpec := [([(1,4,0),(0,6,1),(2,3,7),(1,2,8)],[0,1,2,9,3,4,5],[]),([(3,4,1),(1,2,6),(0,3,7),(1,8,0)],[0,1,2,9,3,4,5],[]),([(3,4,1),(1,2,6),(0,3,7),(1,4,2)],[0,1,8,7,3,9,5],[(35,[])]),([(3,4,1),(1,2,6),(2,3,7),(1,2,8)],[0,1,7,3,9,4,5],[(0,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q158 : ck157 [] d158 = true := by decide +kernel
private def d159 : List NodeSpec := [([(3,4,1),(1,2,6),(2,3,7),(1,4,2)],[8,0,1,7,3,9,5],[]),([(3,4,1),(2,3,6),(1,7,0),(2,8,2)],[9,0,1,2,3,4,5],[]),([(3,4,1),(2,3,6),(1,7,0),(1,5,2)],[0,1,2,3,8,4,9],[]),([(3,4,1),(2,3,6),(1,7,2),(2,8,0)],[9,0,1,2,3,4,5],[(0,[]),(5,[]),(8,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q159 : ck157 [] d159 = true := by decide +kernel
private def lv_0_0_6_26 : List NodeSpec := (d157 ++ (d158 ++ d159))

private theorem ok_0_0_6_26 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6_26 := by
  have go {ids ds} (h : ck157 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 6 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_5) h
  exact (levelOK_append (go q157) (levelOK_append (go q158) (go q159)))
private def ck160 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_5) 6
private def d160 : List NodeSpec := [([(1,4,2),(1,6,0),(0,7,1),(2,3,8)],[9,0,1,2,3,6,5],[]),([(1,4,2),(0,6,3),(3,7,1),(1,0,8)],[0,9,1,2,3,6,5],[(0,[0]),(5,[]),(8,[0])]),([(1,4,2),(2,6,3),(2,1,7),(1,8,0)],[0,1,9,2,3,6,5],[(3,[]),(5,[])]),([(1,4,2),(2,6,3),(2,1,7),(1,2,8)],[0,1,9,3,6,5],[(4,[0]),(10,[]),(7,[0,3])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q160 : ck160 [21,27,28,29,37] d160 = true := by decide +kernel
private def d161 : List NodeSpec := [([(1,4,3),(0,6,1),(1,7,0),(3,2,8)],[9,0,1,2,3,4,5],[(0,[]),(2,[]),(8,[])]),([(1,4,3),(0,6,1),(1,2,7),(2,8,0)],[9,0,1,2,3,4,5],[]),([(1,5,2),(1,6,0),(0,6,3),(1,4,8)],[0,1,2,3,9,7],[(20,[3]),(3,[1,2,3]),(1,[0,2,3]),(2,[0,2]),(7,[0,3])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q161 : ck160 [] d161 = true := by decide +kernel
private def lv_0_0_6_27 : List NodeSpec := (d160 ++ d161)

private theorem ok_0_0_6_27 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6_27 := by
  have go {ids ds} (h : ck160 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 6 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_5) h
  exact (levelOK_append (go q160) (go q161))
private def lv_0_0_6 : List NodeSpec := ((((lv_0_0_6_0 ++ (lv_0_0_6_1 ++ lv_0_0_6_2)) ++ ((lv_0_0_6_3 ++ lv_0_0_6_4) ++ (lv_0_0_6_5 ++ lv_0_0_6_6))) ++ ((lv_0_0_6_7 ++ (lv_0_0_6_8 ++ lv_0_0_6_9)) ++ ((lv_0_0_6_10 ++ lv_0_0_6_11) ++ (lv_0_0_6_12 ++ lv_0_0_6_13)))) ++ (((lv_0_0_6_14 ++ (lv_0_0_6_15 ++ lv_0_0_6_16)) ++ ((lv_0_0_6_17 ++ lv_0_0_6_18) ++ (lv_0_0_6_19 ++ lv_0_0_6_20))) ++ ((lv_0_0_6_21 ++ (lv_0_0_6_22 ++ lv_0_0_6_23)) ++ ((lv_0_0_6_24 ++ lv_0_0_6_25) ++ (lv_0_0_6_26 ++ lv_0_0_6_27)))))
private theorem ok_0_0_6 : LevelOK rd_0_0 (subGoal 0 0) 6 lv_0_0_6 := (levelOK_append (levelOK_append (levelOK_append (levelOK_append ok_0_0_6_0 (levelOK_append ok_0_0_6_1 ok_0_0_6_2)) (levelOK_append (levelOK_append ok_0_0_6_3 ok_0_0_6_4) (levelOK_append ok_0_0_6_5 ok_0_0_6_6))) (levelOK_append (levelOK_append ok_0_0_6_7 (levelOK_append ok_0_0_6_8 ok_0_0_6_9)) (levelOK_append (levelOK_append ok_0_0_6_10 ok_0_0_6_11) (levelOK_append ok_0_0_6_12 ok_0_0_6_13)))) (levelOK_append (levelOK_append (levelOK_append ok_0_0_6_14 (levelOK_append ok_0_0_6_15 ok_0_0_6_16)) (levelOK_append (levelOK_append ok_0_0_6_17 ok_0_0_6_18) (levelOK_append ok_0_0_6_19 ok_0_0_6_20))) (levelOK_append (levelOK_append ok_0_0_6_21 (levelOK_append ok_0_0_6_22 ok_0_0_6_23)) (levelOK_append (levelOK_append ok_0_0_6_24 ok_0_0_6_25) (levelOK_append ok_0_0_6_26 ok_0_0_6_27)))))
private def ck162 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d162 : List NodeSpec := [([(1,1,0),(1,2,0),(0,3,1)],[8,6,2,7,3,4,5],[(24,[]),(0,[0,1,2]),(25,[2]),(17,[]),(1,[2]),(7,[1])]),([(1,1,0),(1,2,0),(3,4,1)],[8,6,2,7,3,4,5],[(24,[]),(17,[]),(0,[0,1,2]),(2,[0,1]),(25,[])]),([(1,1,0),(1,2,0),(1,4,2)],[1,6,7,3,8,5],[(31,[]),(0,[0,1,2]),(17,[]),(10,[]),(11,[])]),([(1,1,0),(1,2,0),(1,4,2)],[1,6,7,3,4,8,5],[(24,[]),(17,[]),(2,[0,1]),(25,[]),(0,[0,1,2]),(11,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q162 : ck162 [0,1,2,3,4,5,6,7] d162 = true := by decide +kernel
private def d163 : List NodeSpec := [([(1,1,0),(1,2,0),(1,4,3)],[1,6,2,7,3,4,8,5],[(0,[0,1]),(3,[2]),(6,[1]),(17,[]),(25,[])]),([(1,1,0),(1,2,0),(3,4,3)],[8,1,6,2,7,3,4,5],[(17,[]),(18,[1]),(3,[2])]),([(1,1,0),(1,2,1),(0,3,7)],[0,6,2,8,3,4,5],[(6,[]),(3,[0,2]),(0,[0,1,2]),(1,[1,2]),(5,[0]),(11,[])]),([(1,1,0),(1,2,1),(1,4,3)],[0,6,2,7,3,4,8,5],[(0,[0,1]),(1,[1]),(1,[2]),(6,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q163 : ck162 [8,9,10,11,12,13,14,15,16] d163 = true := by decide +kernel
private def d164 : List NodeSpec := [([(1,1,0),(1,2,1),(3,4,3)],[8,0,6,2,7,3,4,5],[(5,[0]),(18,[1]),(1,[2])]),([(1,1,0),(3,2,1),(0,3,7)],[8,0,6,2,3,4,5],[(24,[]),(20,[]),(1,[]),(5,[0]),(7,[1])]),([(1,1,0),(3,2,1),(1,4,3)],[7,0,6,2,3,4,8,5],[(20,[]),(0,[0,1]),(1,[1]),(24,[])]),([(1,1,0),(3,2,1),(3,4,3)],[8,7,0,6,2,3,4,5],[(5,[0]),(18,[1])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q164 : ck162 [13,17] d164 = true := by decide +kernel
private def lv_0_0_7_0 : List NodeSpec := (d162 ++ (d163 ++ d164))

private theorem ok_0_0_7_0 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_0 := by
  have go {ids ds} (h : ck162 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q162) (levelOK_append (go q163) (go q164)))
private def ck165 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d165 : List NodeSpec := [([(1,1,0),(1,2,6),(0,3,7)],[0,1,2,8,4,5],[(3,[0,2]),(0,[0,1,2]),(1,[1,2]),(6,[]),(2,[0,1,2]),(26,[])]),([(1,1,0),(1,2,6),(0,3,7)],[0,1,2,8,3,4,5],[(26,[]),(3,[0,2]),(0,[0,1,2]),(1,[1,2]),(6,[]),(2,[0,1,2]),(5,[])]),([(1,1,0),(1,2,6),(3,3,7)],[8,0,1,2,4,5],[(3,[0,2]),(0,[0,1,2]),(7,[]),(1,[1,2]),(6,[])]),([(1,1,0),(1,2,6),(3,4,7)],[8,0,1,2,3,5],[(3,[0,2]),(0,[0,1,2]),(5,[]),(1,[1,2]),(6,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q165 : ck165 [18,19] d165 = true := by decide +kernel
private def d166 : List NodeSpec := [([(1,1,0),(1,2,6),(1,4,3)],[0,1,2,7,3,4,8,5],[(5,[]),(14,[]),(0,[0,1]),(0,[2]),(6,[]),(7,[])]),([(1,1,0),(1,2,6),(3,4,3)],[8,0,1,2,7,3,4,5],[(18,[]),(5,[]),(0,[2]),(14,[]),(26,[])]),([(1,1,0),(1,2,6),(3,5,7)],[8,0,1,2,3,4],[(14,[]),(3,[0,2]),(1,[1,2]),(6,[])]),([(1,1,0),(3,2,6),(0,3,7)],[8,0,1,2,3,4,5],[(24,[]),(26,[]),(1,[1,2]),(0,[0,1,2]),(2,[]),(5,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q166 : ck165 [19,20,21] d166 = true := by decide +kernel
private def d167 : List NodeSpec := [([(1,1,0),(3,2,6),(2,3,2)],[7,8,0,1,3,4,5],[(24,[]),(1,[1,2]),(7,[])]),([(1,1,0),(3,2,6),(3,4,7)],[8,0,1,2,3,5],[(24,[]),(1,[1,2]),(5,[]),(0,[0,1,2])]),([(1,1,0),(3,2,6),(1,4,3)],[7,0,1,2,3,4,8,5],[(5,[]),(14,[]),(24,[]),(0,[0,1]),(0,[2])]),([(1,1,0),(3,2,6),(3,4,3)],[8,7,0,1,2,3,4,5],[(5,[]),(18,[]),(0,[2]),(14,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q167 : ck165 [22,23,24] d167 = true := by decide +kernel
private def lv_0_0_7_1 : List NodeSpec := (d165 ++ (d166 ++ d167))

private theorem ok_0_0_7_1 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_1 := by
  have go {ids ds} (h : ck165 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q165) (levelOK_append (go q166) (go q167)))
private def ck168 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d168 : List NodeSpec := [([(1,1,0),(3,2,6),(3,5,7)],[8,0,1,2,3,4],[(14,[]),(3,[0,2]),(1,[1,2]),(20,[])]),([(1,1,0),(0,3,1),(2,6,7)],[8,0,6,2,3,4,5],[(24,[]),(1,[1,2]),(0,[0,1,2]),(5,[0])]),([(1,1,0),(0,3,1),(2,6,7)],[8,0,7,2,3,4,5],[(1,[1,2]),(20,[]),(6,[]),(0,[0,1,2]),(13,[])]),([(1,1,0),(0,3,1),(2,6,7)],[8,0,7,6,2,3,4,5],[(13,[]),(0,[0,1,2]),(6,[]),(20,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q168 : ck168 [0,25,26,27] d168 = true := by decide +kernel
private def d169 : List NodeSpec := [([(1,1,0),(0,3,1),(1,2,7)],[0,6,2,8,3,4,5],[(24,[]),(0,[0,1,2]),(1,[1,2]),(5,[0]),(4,[]),(7,[2])]),([(1,1,0),(0,3,1),(1,2,7)],[0,7,6,2,8,3,4,5],[(20,[]),(6,[2])]),([(1,1,0),(0,3,1),(3,3,6)],[8,0,7,6,2,3,4,5],[(6,[]),(0,[0,1,2]),(18,[])]),([(1,1,0),(0,3,1),(1,3,2)],[0,7,6,2,3,8,4,5],[(24,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q169 : ck168 [1,2,25,28,29,30,31,32,33,34] d169 = true := by decide +kernel
private def d170 : List NodeSpec := [([(1,1,0),(0,3,1),(2,3,2)],[8,0,7,6,2,3,4,5],[(11,[]),(6,[2]),(3,[0,1])]),([(1,1,0),(0,3,1),(0,4,6)],[0,7,8,6,2,3,5],[(24,[]),(13,[]),(0,[0,1,2]),(1,[2]),(18,[])]),([(1,1,0),(0,3,1),(3,4,6)],[8,0,7,6,2,3,5],[(24,[]),(0,[0,1,2]),(1,[1,2]),(5,[0]),(2,[0,1])]),([(1,1,0),(0,3,1),(3,4,6)],[8,0,7,6,2,3,4,5],[(5,[0]),(2,[0,1])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q170 : ck168 [27,28,33] d170 = true := by decide +kernel
private def lv_0_0_7_2 : List NodeSpec := (d168 ++ (d169 ++ d170))

private theorem ok_0_0_7_2 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_2 := by
  have go {ids ds} (h : ck168 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q168) (levelOK_append (go q169) (go q170)))
private def ck171 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d171 : List NodeSpec := [([(1,1,0),(0,3,1),(1,4,2)],[0,7,6,2,3,8,5],[(24,[]),(1,[1,2]),(0,[0,1,2]),(35,[]),(5,[0]),(2,[0,1])]),([(1,1,0),(0,3,1),(1,4,2)],[0,7,6,2,3,4,8,5],[(5,[0]),(10,[1]),(2,[0,1])]),([(1,1,0),(0,3,1),(2,4,2)],[8,0,7,6,2,3,5],[(24,[]),(13,[]),(0,[0,1,2]),(1,[2]),(7,[2])]),([(1,1,0),(0,3,1),(1,4,3)],[0,7,6,2,3,4,8,5],[(0,[0,1]),(1,[1]),(7,[]),(20,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q171 : ck171 [3,4,26,29,30,32,35,36] d171 = true := by decide +kernel
private def d172 : List NodeSpec := [([(1,1,0),(0,3,1),(3,4,3)],[8,0,7,6,2,3,4,5],[(5,[0]),(18,[])]),([(1,1,0),(0,3,1),(3,5,6)],[8,0,7,6,2,3,4],[(21,[]),(24,[]),(17,[2]),(20,[])]),([(1,1,0),(0,3,1),(1,5,2)],[0,7,6,2,3,4,8],[(20,[]),(24,[]),(17,[2]),(30,[])]),([(1,1,0),(0,3,1),(2,6,7)],[8,0,1,2,3,4,5],[(24,[]),(20,[]),(13,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q172 : ck171 [31,34] d172 = true := by decide +kernel
private def d173 : List NodeSpec := [([(1,1,0),(0,3,1),(3,4,6)],[8,0,7,1,2,3,5],[(20,[2]),(24,[]),(1,[1,2]),(2,[0]),(5,[])]),([(1,1,0),(2,3,1),(2,3,7)],[0,8,6,2,3,4,5],[(24,[]),(20,[]),(1,[]),(5,[0]),(7,[])]),([(1,1,0),(2,3,1),(1,4,3)],[7,0,6,2,3,4,8,5],[(1,[2]),(0,[0,1]),(1,[1]),(2,[0,1]),(13,[])]),([(1,1,0),(2,3,1),(3,4,3)],[8,7,0,6,2,3,4,5],[(5,[0]),(18,[]),(1,[2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q173 : ck171 [37,38] d173 = true := by decide +kernel
private def lv_0_0_7_3 : List NodeSpec := (d171 ++ (d172 ++ d173))

private theorem ok_0_0_7_3 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_3 := by
  have go {ids ds} (h : ck171 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q171) (levelOK_append (go q172) (go q173)))
private def ck174 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d174 : List NodeSpec := [([(1,1,0),(3,3,1),(2,6,7)],[0,1,8,2,3,4,5],[(24,[]),(20,[]),(13,[])]),([(1,1,0),(3,3,1),(0,3,6)],[7,0,1,8,2,3,4,5],[(6,[]),(1,[1,2])]),([(1,1,0),(3,3,1),(3,4,6)],[8,7,0,1,2,3,5],[(20,[2]),(24,[]),(1,[1,2]),(2,[0]),(5,[])]),([(1,1,0),(0,3,6),(1,2,7)],[0,1,2,8,3,4,5],[(3,[0,1]),(1,[1,2]),(0,[0,1,2]),(6,[2]),(2,[]),(4,[]),(5,[]),(26,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q174 : ck174 [39,40,41] d174 = true := by decide +kernel
private def d175 : List NodeSpec := [([(1,1,0),(0,3,6),(1,2,7)],[0,1,7,2,8,3,4,5],[(3,[0,1]),(6,[2]),(26,[])]),([(1,1,0),(0,3,6),(1,3,2)],[0,1,7,2,3,8,4,5],[(24,[])]),([(1,1,0),(0,3,6),(3,4,1)],[8,0,1,7,2,3,4,5],[(12,[]),(4,[]),(6,[]),(26,[])]),([(1,1,0),(0,3,6),(1,4,7)],[0,1,7,2,3,4,8,5],[(2,[0,1]),(0,[0,1]),(5,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q175 : ck174 [42,43,44,45] d175 = true := by decide +kernel
private def d176 : List NodeSpec := [([(1,1,0),(0,3,6),(1,4,2)],[0,1,7,2,3,8,5],[(3,[0,1]),(1,[1,2]),(0,[0,1,2]),(6,[2]),(5,[]),(10,[]),(2,[0,1]),(4,[2])]),([(1,1,0),(0,3,6),(1,4,2)],[0,1,7,2,3,4,8,5],[(10,[]),(5,[]),(2,[0,1]),(26,[])]),([(1,1,0),(0,3,6),(2,4,2)],[8,0,1,7,2,3,5],[(1,[1,2]),(3,[0,1]),(2,[0,1]),(0,[0,1,2]),(6,[2]),(4,[2])]),([(1,1,0),(0,3,6),(1,4,3)],[0,1,7,2,3,4,8,5],[(0,[0,1]),(2,[]),(5,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q176 : ck174 [39,40,42,46,47,48,49,50] d176 = true := by decide +kernel
private def lv_0_0_7_4 : List NodeSpec := (d174 ++ (d175 ++ d176))

private theorem ok_0_0_7_4 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_4 := by
  have go {ids ds} (h : ck174 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q174) (levelOK_append (go q175) (go q176)))
private def ck177 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d177 : List NodeSpec := [([(1,1,0),(0,3,6),(1,5,2)],[0,1,7,2,3,4,8],[(29,[]),(1,[1,2]),(2,[2]),(5,[2])]),([(1,1,0),(0,3,6),(2,6,7)],[8,0,1,7,2,3,4,5],[(6,[]),(1,[1,2])]),([(1,1,0),(0,3,6),(3,4,1)],[8,0,7,6,2,3,4,5],[(2,[0,1]),(4,[]),(6,[]),(12,[])]),([(1,1,0),(0,3,6),(0,4,6)],[0,1,7,8,2,3,5],[(24,[]),(2,[0,1]),(1,[1,2]),(0,[0,1,2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q177 : ck177 [41,43,51] d177 = true := by decide +kernel
private def d178 : List NodeSpec := [([(1,1,0),(0,3,6),(3,4,6)],[8,0,1,7,2,3,5],[(24,[]),(1,[1,2]),(0,[0,1,2]),(2,[0]),(5,[])]),([(1,1,0),(0,3,6),(3,4,6)],[8,0,1,7,2,3,4,5],[(2,[0,1]),(5,[]),(26,[])]),([(1,1,0),(0,3,6),(3,5,6)],[8,0,1,7,2,3,4],[(24,[]),(1,[1,2]),(21,[]),(2,[0,2]),(17,[2])]),([(1,1,0),(1,3,6),(2,7,2)],[8,0,1,3,4,5],[(11,[]),(0,[0,1,2]),(1,[1,2]),(6,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q178 : ck177 [52,53,54] d178 = true := by decide +kernel
private def d179 : List NodeSpec := [([(1,1,0),(1,3,6),(3,4,7)],[8,0,1,2,3,5],[(11,[]),(0,[0,1,2]),(5,[]),(1,[1,2])]),([(1,1,0),(1,3,6),(3,5,7)],[8,0,1,2,3,4],[(11,[]),(1,[1,2]),(6,[]),(8,[])]),([(1,1,0),(2,3,6),(2,3,7)],[0,1,8,2,3,4,5],[(24,[]),(1,[1,2]),(0,[0,1,2]),(2,[]),(5,[])]),([(1,1,0),(2,3,6),(1,4,7)],[0,1,2,3,8,5],[(24,[]),(0,[0,1,2]),(1,[1,2]),(5,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q179 : ck177 [] d179 = true := by decide +kernel
private def lv_0_0_7_5 : List NodeSpec := (d177 ++ (d178 ++ d179))

private theorem ok_0_0_7_5 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_5 := by
  have go {ids ds} (h : ck177 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q177) (levelOK_append (go q178) (go q179)))
private def ck180 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d180 : List NodeSpec := [([(1,1,0),(2,3,6),(1,4,3)],[7,0,1,2,3,4,8,5],[(14,[]),(0,[0,1]),(0,[2]),(5,[])]),([(1,1,0),(2,3,6),(1,5,7)],[0,1,2,3,4,8],[(24,[]),(14,[]),(1,[1,2])]),([(1,1,0),(3,3,6),(3,4,1)],[8,7,0,6,2,3,4,5],[(2,[0,1]),(4,[]),(12,[])]),([(1,1,0),(3,3,6),(3,4,6)],[8,7,0,1,2,3,5],[(24,[]),(1,[1,2]),(0,[0,1,2]),(2,[0]),(5,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q180 : ck180 [33,55,56,57,58,59] d180 = true := by decide +kernel
private def d181 : List NodeSpec := [([(1,1,0),(3,3,6),(3,4,6)],[8,7,0,1,2,3,4,5],[(2,[0,1]),(5,[]),(1,[2]),(7,[])]),([(1,1,0),(3,3,6),(3,5,6)],[8,7,0,1,2,3,4],[(24,[]),(1,[1,2]),(21,[]),(2,[0,2]),(17,[2])]),([(1,1,0),(1,3,2),(2,3,2)],[8,0,1,6,3,7,4,5],[(24,[]),(0,[1,2]),(2,[1,2]),(7,[])]),([(1,1,0),(1,3,2),(0,7,1)],[0,8,6,2,3,4,5],[(24,[]),(20,[]),(13,[]),(0,[1,2]),(1,[]),(7,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q181 : ck180 [34,60,61,62,63] d181 = true := by decide +kernel
private def d182 : List NodeSpec := [([(1,1,0),(1,3,2),(0,7,1)],[0,8,6,2,3,7,4,5],[(7,[]),(6,[1]),(0,[1,2]),(2,[1,2])]),([(1,1,0),(1,3,2),(0,7,6)],[0,1,8,2,3,4,5],[(3,[0,2]),(1,[1,2]),(0,[0,1,2]),(6,[1]),(2,[]),(5,[]),(4,[])]),([(1,1,0),(1,3,2),(0,7,6)],[0,1,8,2,3,7,4,5],[(3,[0,2]),(6,[1])]),([(1,1,0),(1,3,2),(3,4,1)],[8,0,6,2,3,7,4,5],[(2,[1]),(4,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q182 : ck180 [61,64,65] d182 = true := by decide +kernel
private def lv_0_0_7_6 : List NodeSpec := (d180 ++ (d181 ++ d182))

private theorem ok_0_0_7_6 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_6 := by
  have go {ids ds} (h : ck180 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q180) (levelOK_append (go q181) (go q182)))
private def ck183 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d183 : List NodeSpec := [([(1,1,0),(1,3,2),(3,4,6)],[8,0,1,2,3,7,5],[(3,[0,2]),(1,[1,2]),(0,[0,1,2]),(6,[1]),(4,[2]),(5,[])]),([(1,1,0),(1,3,2),(3,4,6)],[8,0,1,2,3,7,4,5],[(5,[]),(2,[0]),(7,[])]),([(1,1,0),(1,3,2),(3,5,6)],[8,0,1,2,3,7,4],[(3,[0,2]),(21,[1]),(1,[1,2]),(2,[0,2]),(4,[2]),(8,[]),(17,[2])]),([(1,1,0),(2,3,2),(0,1,7)],[8,7,0,6,2,3,4,5],[(24,[]),(11,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q183 : ck183 [28,62,63,66,67,68,69,70,71] d183 = true := by decide +kernel
private def d184 : List NodeSpec := [([(1,1,0),(2,3,2),(3,4,1)],[8,7,0,6,2,3,4,5],[(2,[1]),(4,[])]),([(1,1,0),(2,3,2),(3,4,6)],[8,7,0,1,2,3,5],[(3,[0,2]),(1,[1,2]),(0,[0,1,2]),(6,[1]),(4,[2]),(5,[])]),([(1,1,0),(2,3,2),(3,4,6)],[8,7,0,1,2,3,4,5],[(5,[]),(2,[0]),(11,[]),(26,[])]),([(1,1,0),(2,3,2),(3,5,6)],[8,7,0,1,2,3,4],[(3,[0,2]),(21,[1]),(1,[1,2]),(2,[0,2]),(4,[2]),(8,[]),(17,[2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q184 : ck183 [62,63,72,73,74,75,76,77] d184 = true := by decide +kernel
private def d185 : List NodeSpec := [([(1,1,0),(1,4,1),(0,7,3)],[0,6,2,8,3,4,5],[(24,[]),(17,[]),(0,[0,1,2])]),([(1,1,0),(3,4,1),(1,2,7)],[0,6,2,8,3,4,5],[(24,[]),(17,[]),(0,[0,1,2])]),([(1,1,0),(3,4,1),(2,3,7)],[0,6,2,8,3,4,5],[(17,[]),(0,[0,1,2]),(2,[0,2]),(12,[]),(4,[])]),([(1,1,0),(3,4,1),(3,5,6)],[8,7,0,6,2,3,4],[(17,[2]),(24,[]),(20,[]),(2,[0,2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q185 : ck183 [5,51,57,64,72,73,78,79,80,81,82] d185 = true := by decide +kernel
private def lv_0_0_7_7 : List NodeSpec := (d183 ++ (d184 ++ d185))

private theorem ok_0_0_7_7 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_7 := by
  have go {ids ds} (h : ck183 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q183) (levelOK_append (go q184) (go q185)))
private def ck186 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d186 : List NodeSpec := [([(1,1,0),(3,4,1),(1,5,2)],[7,0,6,2,3,4,8],[(17,[2]),(24,[]),(20,[]),(2,[2])]),([(1,1,0),(3,4,1),(1,3,7)],[0,1,6,2,3,8,4,5],[(6,[]),(12,[]),(20,[]),(0,[1,2]),(1,[1,2]),(2,[2]),(7,[])]),([(1,1,0),(3,4,1),(2,3,7)],[0,1,6,2,8,3,4,5],[(12,[]),(6,[]),(20,[]),(18,[]),(0,[1,2]),(1,[1,2]),(26,[])]),([(1,1,0),(0,4,6),(2,6,7)],[8,0,1,2,3,5],[(24,[]),(0,[0,1,2]),(1,[1,2]),(5,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q186 : ck186 [44,82,83] d186 = true := by decide +kernel
private def d187 : List NodeSpec := [([(1,1,0),(0,4,6),(3,5,6)],[8,0,1,7,2,3],[(24,[]),(14,[]),(1,[1,2])]),([(1,1,0),(1,4,6),(0,7,3)],[0,1,2,8,3,4,5],[(24,[]),(1,[1,2]),(2,[0,2]),(0,[0,1,2])]),([(1,1,0),(1,4,6),(3,5,7)],[8,0,1,2,3,4],[(24,[]),(15,[]),(1,[1,2])]),([(1,1,0),(3,4,6),(1,2,7)],[0,1,2,8,3,5],[(24,[]),(0,[0,1,2]),(1,[1,2]),(5,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q187 : ck186 [84,85,86,87] d187 = true := by decide +kernel
private def d188 : List NodeSpec := [([(1,1,0),(3,4,6),(1,2,7)],[7,0,1,2,8,3,5],[(5,[]),(0,[0,1,2]),(1,[1,2]),(3,[0,1]),(2,[0]),(6,[]),(2,[0,2])]),([(1,1,0),(3,4,6),(1,3,7)],[7,0,1,2,3,8,5],[(5,[]),(0,[0,1,2]),(1,[1,2]),(2,[0]),(3,[0,1]),(6,[])]),([(1,1,0),(3,4,6),(2,3,7)],[7,0,1,2,8,3,5],[(0,[0,1,2]),(5,[]),(1,[1,2]),(2,[0]),(3,[0,1]),(6,[])]),([(1,1,0),(3,4,6),(1,5,2)],[7,0,1,2,3,8],[(29,[]),(1,[1,2]),(5,[2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q188 : ck186 [66,67,68,75,76,77,88,89,90,91,92,93,94,95,96,97,98] d188 = true := by decide +kernel
private def lv_0_0_7_8 : List NodeSpec := (d186 ++ (d187 ++ d188))

private theorem ok_0_0_7_8 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_8 := by
  have go {ids ds} (h : ck186 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q186) (levelOK_append (go q187) (go q188)))
private def ck189 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d189 : List NodeSpec := [([(1,1,0),(3,4,6),(1,2,7)],[0,1,2,8,3,4,5],[(2,[0,2]),(5,[]),(0,[0,1,2]),(7,[]),(26,[]),(1,[1,2]),(3,[0,1]),(6,[])]),([(1,1,0),(3,4,6),(2,3,7)],[0,1,2,8,3,4,5],[(26,[]),(2,[0,2]),(0,[0,1,2]),(5,[]),(1,[1,2]),(3,[]),(6,[]),(8,[])]),([(1,1,0),(3,4,6),(1,5,2)],[7,0,1,2,3,4,8],[(5,[2]),(2,[0,2]),(3,[0,1]),(0,[0,1]),(7,[2]),(8,[]),(19,[])]),([(1,1,0),(3,4,6),(1,3,7)],[7,0,1,6,2,3,8,5],[(2,[0]),(6,[]),(0,[0,1,2]),(2,[0,2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q189 : ck189 [52,58,70,99,100,101] d189 = true := by decide +kernel
private def d190 : List NodeSpec := [([(1,1,0),(3,4,6),(2,3,7)],[7,0,1,6,2,8,3,5],[(2,[0]),(6,[]),(0,[0,1,2]),(2,[0,2])]),([(1,1,0),(3,4,6),(3,5,6)],[8,7,0,1,2,3],[(24,[]),(1,[1,2]),(21,[]),(17,[2])]),([(1,1,0),(3,4,6),(1,3,7)],[0,1,6,2,3,8,4,5],[(2,[0,2]),(6,[]),(0,[0,1,2]),(7,[])]),([(1,1,0),(3,4,6),(2,3,7)],[0,1,6,2,8,3,4,5],[(2,[0,2]),(0,[0,1,2]),(6,[]),(20,[]),(26,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q190 : ck189 [53,54,59,60,83,101,102,103,104,105,106] d190 = true := by decide +kernel
private def d191 : List NodeSpec := [([(1,1,0),(3,4,6),(3,5,6)],[8,7,0,1,2,3,4],[(17,[2]),(2,[0,2]),(24,[])]),([(1,1,0),(1,4,2),(0,7,6)],[0,1,8,2,3,5],[(35,[]),(0,[0,1,2]),(1,[1,2])]),([(1,1,0),(1,4,2),(0,7,3)],[0,1,6,2,8,3,7,5],[(6,[1]),(10,[]),(0,[0,1]),(0,[1,2]),(1,[1]),(5,[]),(11,[])]),([(1,1,0),(1,4,2),(2,7,3)],[8,0,1,6,2,3,7,5],[(6,[1]),(7,[1]),(0,[1,2]),(5,[]),(10,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q191 : ck189 [6,7,46,47,105,106,107,108,109,110,111,112,113,114] d191 = true := by decide +kernel
private def lv_0_0_7_9 : List NodeSpec := (d189 ++ (d190 ++ d191))

private theorem ok_0_0_7_9 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_9 := by
  have go {ids ds} (h : ck189 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q189) (levelOK_append (go q190) (go q191)))
private def ck192 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d192 : List NodeSpec := [([(1,1,0),(1,4,2),(3,5,6)],[8,0,1,2,3,7],[(1,[1,2]),(3,[0,2]),(20,[1]),(21,[1]),(17,[2]),(2,[0,2])]),([(1,1,0),(1,4,2),(0,7,3)],[0,1,6,2,8,3,4,5],[(6,[]),(10,[]),(20,[]),(0,[0]),(0,[1,2]),(1,[]),(3,[0]),(5,[]),(11,[]),(26,[])]),([(1,1,0),(1,4,2),(2,7,3)],[8,0,1,6,2,3,4,5],[(6,[]),(7,[]),(0,[1,2]),(2,[2]),(3,[0]),(4,[]),(5,[])]),([(1,1,0),(1,4,2),(3,5,6)],[8,0,1,2,3,4,7],[(17,[2]),(14,[]),(3,[0,2]),(4,[2]),(6,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q192 : ck192 [48,110,114,115,116,117,118,119] d192 = true := by decide +kernel
private def d193 : List NodeSpec := [([(1,1,0),(2,4,2),(2,6,7)],[0,1,8,2,3,5],[(3,[0,2]),(1,[1,2]),(0,[0,1,2]),(13,[]),(6,[1])]),([(1,1,0),(2,4,2),(3,5,6)],[8,7,0,1,2,3],[(14,[]),(3,[0,2]),(1,[1,2]),(6,[1]),(13,[2])]),([(1,1,0),(1,4,3),(2,7,0)],[8,1,6,2,3,4,5],[(17,[]),(0,[0,1,2]),(2,[0,2]),(3,[1,2]),(4,[]),(7,[])]),([(1,1,0),(1,4,3),(0,7,1)],[0,8,6,2,3,4,5],[(17,[]),(20,[]),(0,[0,1,2]),(2,[0,2]),(3,[1,2]),(7,[]),(6,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q193 : ck192 [8,9,14,17,35,37,120,121,122,123,124,125,126] d193 = true := by decide +kernel
private def d194 : List NodeSpec := [([(1,1,0),(1,4,3),(0,7,6)],[0,1,8,2,3,4,5],[(17,[]),(0,[0,1,2]),(2,[0,2]),(3,[]),(6,[]),(8,[])]),([(1,1,0),(1,4,3),(0,7,6)],[0,1,8,6,2,3,4,5],[(17,[]),(0,[0,1,2]),(2,[0,2]),(20,[])]),([(1,1,0),(1,4,3),(2,7,2)],[8,0,1,6,2,3,4,5],[(6,[]),(17,[]),(11,[]),(20,[]),(0,[0]),(0,[1,2]),(2,[0]),(2,[2])]),([(1,1,0),(1,4,3),(3,5,6)],[8,0,1,2,3,4,7],[(17,[2]),(14,[]),(21,[]),(3,[0,2]),(4,[2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q194 : ck192 [9,22,23,127,128,129,130,131,132] d194 = true := by decide +kernel
private def lv_0_0_7_10 : List NodeSpec := (d192 ++ (d193 ++ d194))

private theorem ok_0_0_7_10 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_10 := by
  have go {ids ds} (h : ck192 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q192) (levelOK_append (go q193) (go q194)))
private def ck195 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d195 : List NodeSpec := [([(1,1,0),(1,4,3),(3,5,6)],[8,0,1,6,2,3,4,7],[(21,[]),(17,[2]),(20,[]),(0,[1]),(1,[2]),(2,[0,2])]),([(1,1,0),(1,4,3),(1,5,2)],[0,1,6,2,3,4,7,8],[(29,[]),(5,[2]),(14,[]),(20,[]),(1,[2]),(30,[])]),([(1,1,0),(1,4,3),(3,5,7)],[8,0,1,6,2,3,4],[(32,[]),(20,[]),(2,[0,2]),(3,[1,2]),(7,[])]),([(1,1,0),(3,4,3),(2,6,7)],[0,1,8,6,2,3,4,5],[(17,[]),(2,[0,2]),(0,[0,1,2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q195 : ck195 [10,16,21,24,38,50,56,124,125,129,130,133] d195 = true := by decide +kernel
private def d196 : List NodeSpec := [([(1,1,0),(3,4,3),(1,2,7)],[0,1,6,2,8,3,4,5],[(6,[]),(17,[]),(18,[]),(0,[1,2]),(2,[0]),(4,[])]),([(1,1,0),(3,4,3),(3,5,6)],[8,7,0,1,2,3,4],[(17,[2]),(14,[]),(3,[0,2]),(4,[2]),(6,[])]),([(1,1,0),(3,4,3),(3,5,6)],[8,7,0,1,6,2,3,4],[(17,[2]),(0,[1]),(2,[0,2]),(6,[])]),([(1,1,0),(3,4,3),(1,5,2)],[7,0,1,6,2,3,4,8],[(17,[2]),(18,[2]),(14,[]),(30,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q196 : ck195 [133,134,135,136] d196 = true := by decide +kernel
private def d197 : List NodeSpec := [([(1,1,0),(3,5,6),(1,2,7)],[0,1,2,8,3,4],[(21,[]),(3,[0,1]),(1,[1,2]),(2,[0,1,2])]),([(1,1,0),(1,5,2),(0,7,6)],[0,1,8,2,3,4],[(30,[]),(1,[1,2]),(24,[])]),([(2,1,0),(1,2,6),(0,3,7)],[0,1,2,8,3,4,5],[(3,[0,2]),(26,[]),(0,[0,1,2]),(1,[1,2]),(2,[]),(4,[]),(5,[])]),([(2,1,0),(1,2,6),(1,4,3)],[0,1,2,7,3,4,8,5],[(7,[]),(0,[0,1]),(20,[]),(27,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q197 : ck195 [132,136,137,138] d197 = true := by decide +kernel
private def lv_0_0_7_11 : List NodeSpec := (d195 ++ (d196 ++ d197))

private theorem ok_0_0_7_11 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_11 := by
  have go {ids ds} (h : ck195 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q195) (levelOK_append (go q196) (go q197)))
private def ck198 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d198 : List NodeSpec := [([(2,1,0),(1,2,6),(3,4,3)],[8,0,1,2,7,3,4,5],[(18,[]),(26,[])]),([(2,1,0),(1,2,1),(0,3,7)],[6,0,2,8,3,4,5],[(27,[]),(3,[0,2]),(0,[0,1,2]),(5,[0]),(7,[1])]),([(2,1,0),(1,2,1),(1,4,3)],[6,0,2,7,3,4,8,5],[(0,[0,1]),(6,[]),(20,[])]),([(2,1,0),(1,2,1),(3,4,3)],[8,6,0,2,7,3,4,5],[(5,[0]),(18,[1])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q198 : ck198 [139,140,141,142] d198 = true := by decide +kernel
private def d199 : List NodeSpec := [([(2,1,0),(0,3,6),(1,2,7)],[0,1,2,8,3,4,5],[(3,[0,1]),(20,[]),(13,[]),(1,[1,2]),(26,[])]),([(2,1,0),(0,3,6),(1,3,2)],[7,0,1,2,3,8,4,5],[(31,[])]),([(2,1,0),(0,3,6),(1,4,2)],[7,0,1,2,3,8,5],[(4,[2]),(3,[0,1]),(0,[0,1,2]),(1,[1,2]),(2,[0,1]),(5,[]),(10,[]),(27,[2])]),([(2,1,0),(1,3,6),(0,3,1)],[0,8,2,7,4,5],[(11,[]),(4,[]),(0,[0,1,2]),(1,[1,2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q199 : ck198 [143] d199 = true := by decide +kernel
private def d200 : List NodeSpec := [([(2,1,0),(1,3,6),(3,5,7)],[8,0,1,2,3,4],[(11,[]),(1,[1,2]),(8,[]),(13,[2])]),([(2,1,0),(2,3,6),(1,4,3)],[0,7,1,2,3,4,8,5],[(13,[]),(0,[0,1]),(20,[])]),([(2,1,0),(0,3,1),(1,2,7)],[6,0,2,8,3,4,5],[(20,[]),(3,[0,1]),(1,[1,2]),(13,[]),(11,[]),(6,[])]),([(2,1,0),(0,3,1),(1,3,2)],[6,0,7,2,3,8,4,5],[(7,[]),(24,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q200 : ck198 [144,145] d200 = true := by decide +kernel
private def lv_0_0_7_12 : List NodeSpec := (d198 ++ (d199 ++ d200))

private theorem ok_0_0_7_12 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_12 := by
  have go {ids ds} (h : ck198 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q198) (levelOK_append (go q199) (go q200)))
private def ck201 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d201 : List NodeSpec := [([(2,1,0),(0,3,1),(2,3,2)],[8,6,0,7,2,3,4,5],[(11,[]),(24,[]),(3,[0,1])]),([(2,1,0),(0,3,1),(1,4,2)],[6,0,7,2,3,8,5],[(4,[2]),(1,[1,2]),(3,[0,1]),(11,[]),(0,[0,1,2]),(2,[0,1]),(5,[0]),(10,[1]),(24,[])]),([(2,1,0),(2,3,1),(1,4,3)],[7,6,0,2,3,4,8,5],[(13,[]),(0,[0,1]),(20,[])]),([(2,1,0),(2,3,1),(3,4,3)],[8,7,6,0,2,3,4,5],[(5,[0]),(18,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q201 : ck201 [144,145] d201 = true := by decide +kernel
private def d202 : List NodeSpec := [([(2,1,0),(1,3,2),(2,3,2)],[8,6,0,1,3,7,4,5],[(31,[])]),([(2,1,0),(1,3,2),(0,7,6)],[8,0,1,2,3,7,4,5],[(27,[1]),(3,[])]),([(2,1,0),(1,3,2),(0,7,1)],[6,0,8,2,3,7,4,5],[(7,[]),(24,[])]),([(2,1,0),(1,3,2),(3,4,6)],[8,0,1,2,3,7,4,5],[(7,[]),(4,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q202 : ck201 [146,147] d202 = true := by decide +kernel
private def d203 : List NodeSpec := [([(2,1,0),(1,3,2),(3,4,1)],[8,6,0,2,3,7,4,5],[(1,[1]),(4,[])]),([(2,1,0),(2,3,2),(0,1,7)],[8,7,6,0,2,3,4,5],[(11,[]),(24,[])]),([(2,1,0),(2,3,2),(3,4,6)],[8,7,0,1,2,3,4,5],[(11,[]),(26,[])]),([(2,1,0),(2,3,2),(3,4,1)],[8,7,6,0,2,3,4,5],[(1,[1]),(4,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q203 : ck201 [144,148,149,150,151] d203 = true := by decide +kernel
private def lv_0_0_7_13 : List NodeSpec := (d201 ++ (d202 ++ d203))

private theorem ok_0_0_7_13 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_13 := by
  have go {ids ds} (h : ck201 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q201) (levelOK_append (go q202) (go q203)))
private def ck204 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d204 : List NodeSpec := [([(2,1,0),(3,4,6),(1,2,7)],[0,1,2,8,3,4,5],[(3,[0,1]),(5,[]),(0,[0,1,2]),(1,[1,2]),(4,[]),(7,[]),(26,[])]),([(2,1,0),(3,4,6),(2,3,7)],[0,1,2,8,3,4,5],[(26,[]),(20,[]),(2,[0,2]),(1,[1,2]),(0,[0,1,2]),(3,[]),(5,[])]),([(2,1,0),(3,4,1),(1,2,7)],[6,0,2,8,3,4,5],[(17,[]),(2,[0,2]),(0,[0,1,2]),(4,[]),(3,[0,1])]),([(2,1,0),(3,4,1),(2,3,7)],[6,0,2,8,3,4,5],[(17,[]),(20,[]),(0,[0,1,2]),(2,[0,2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q204 : ck204 [146,148,150,151,152,153,154] d204 = true := by decide +kernel
private def d205 : List NodeSpec := [([(2,1,0),(1,4,2),(0,7,3)],[6,0,1,2,8,3,7,5],[(20,[1]),(27,[1]),(0,[0,1])]),([(2,1,0),(1,4,2),(2,7,3)],[8,6,0,1,2,3,7,5],[(4,[1]),(27,[1])]),([(2,1,0),(1,4,2),(0,7,3)],[6,0,1,2,8,3,4,5],[(20,[]),(27,[]),(0,[0]),(3,[0])]),([(2,1,0),(1,4,2),(2,7,3)],[8,6,0,1,2,3,4,5],[(4,[]),(27,[]),(3,[0])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q205 : ck204 [] d205 = true := by decide +kernel
private def d206 : List NodeSpec := [([(2,1,0),(1,4,3),(2,7,2)],[8,6,0,1,2,3,4,5],[(20,[]),(27,[]),(0,[0]),(2,[0]),(17,[])]),([(2,1,0),(3,4,3),(1,2,7)],[6,0,1,2,8,3,4,5],[(4,[]),(27,[]),(2,[0]),(17,[])]),([(1,2,0),(0,6,1),(2,3,7)],[8,0,1,2,3,4,5],[(13,[]),(3,[1,2]),(1,[1,2]),(0,[0,1,2])]),([(1,2,0),(0,6,1),(1,5,7)],[0,1,2,3,4,8],[(13,[]),(3,[1,2]),(1,[1,2]),(8,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q206 : ck204 [] d206 = true := by decide +kernel
private def lv_0_0_7_14 : List NodeSpec := (d204 ++ (d205 ++ d206))

private theorem ok_0_0_7_14 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_14 := by
  have go {ids ds} (h : ck204 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q204) (levelOK_append (go q205) (go q206)))
private def ck207 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d207 : List NodeSpec := [([(1,2,0),(2,6,1),(2,3,7)],[0,1,8,2,3,4,5],[(6,[]),(3,[1,2]),(1,[1,2]),(0,[0,1,2]),(2,[]),(5,[])]),([(1,2,0),(2,6,1),(1,4,3)],[7,0,1,2,3,4,8,5],[(6,[]),(0,[0,1]),(5,[])]),([(1,2,0),(2,6,1),(3,4,3)],[8,7,0,1,2,3,4,5],[(5,[]),(18,[])]),([(1,2,0),(1,3,0),(1,4,2)],[1,6,3,7,8,5],[(35,[]),(31,[]),(0,[0,1,2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q207 : ck207 [155,156,157] d207 = true := by decide +kernel
private def d208 : List NodeSpec := [([(1,2,0),(0,3,1),(1,7,0)],[1,8,2,6,3,4,5],[(31,[]),(26,[]),(0,[0,1,2])]),([(1,2,0),(0,3,1),(1,7,0)],[7,1,8,2,6,3,4,5],[(31,[]),(4,[])]),([(1,2,0),(0,3,1),(1,2,7)],[0,1,6,8,3,4,5],[(31,[]),(5,[0]),(11,[]),(26,[]),(0,[0,1,2])]),([(1,2,0),(0,3,1),(1,2,7)],[0,7,1,6,8,3,4,5],[(31,[]),(4,[]),(11,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q208 : ck207 [1,2,158,159,160,161,162,163,164,165] d208 = true := by decide +kernel
private def d209 : List NodeSpec := [([(1,2,0),(0,3,1),(1,6,7)],[0,1,2,8,3,4,5],[(31,[]),(0,[0,1,2]),(2,[]),(5,[])]),([(1,2,0),(0,3,1),(1,6,7)],[0,7,1,2,8,3,4,5],[(31,[])]),([(1,2,0),(0,3,1),(1,4,2)],[0,7,1,6,3,8,5],[(31,[]),(35,[]),(0,[0,1,2]),(5,[0])]),([(1,2,0),(0,3,1),(1,4,2)],[0,7,1,6,3,4,8,5],[(31,[]),(5,[0]),(10,[]),(2,[1])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q209 : ck207 [3,4,159,160,163,166,167,168,169,170] d209 = true := by decide +kernel
private def lv_0_0_7_15 : List NodeSpec := (d207 ++ (d208 ++ d209))

private theorem ok_0_0_7_15 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_15 := by
  have go {ids ds} (h : ck207 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q207) (levelOK_append (go q208) (go q209)))
private def ck210 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d210 : List NodeSpec := [([(1,2,0),(0,3,1),(1,4,6)],[0,7,1,2,3,4,8,5],[(31,[]),(4,[]),(5,[]),(2,[0]),(7,[]),(26,[])]),([(1,2,0),(3,3,1),(1,0,7)],[8,1,2,6,3,4,5],[(35,[]),(1,[1]),(0,[0,1,2]),(4,[]),(25,[1])]),([(1,2,0),(3,3,1),(1,6,7)],[0,1,2,8,3,4,5],[(11,[]),(0,[0,1,2]),(2,[]),(4,[]),(5,[]),(6,[]),(25,[1])]),([(1,2,0),(3,3,1),(1,4,2)],[7,0,1,6,3,8,5],[(35,[]),(31,[]),(0,[0,1,2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q210 : ck210 [161,165,171,172,173,174] d210 = true := by decide +kernel
private def d211 : List NodeSpec := [([(1,2,0),(0,3,6),(2,3,7)],[8,0,1,2,3,4,5],[(26,[]),(11,[]),(0,[0,1,2]),(2,[]),(4,[]),(5,[]),(6,[])]),([(1,2,0),(1,3,6),(2,7,0)],[8,1,2,6,3,4,5],[(35,[]),(1,[1]),(6,[0]),(25,[])]),([(1,2,0),(1,3,6),(2,7,2)],[8,0,1,6,3,4,5],[(31,[]),(11,[]),(5,[0])]),([(1,2,0),(1,3,6),(1,4,2)],[0,1,6,3,7,8,5],[(35,[]),(31,[]),(0,[0,1,2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q211 : ck210 [175] d211 = true := by decide +kernel
private def d212 : List NodeSpec := [([(1,2,0),(2,3,6),(2,1,7)],[7,0,8,1,2,3,4,5],[(26,[]),(6,[]),(25,[2])]),([(1,2,0),(2,3,6),(1,2,7)],[7,0,1,8,3,4,5],[(11,[]),(25,[])]),([(1,2,0),(2,3,6),(1,4,7)],[7,0,1,2,3,4,8,5],[(2,[0,1]),(5,[])]),([(1,2,0),(2,3,6),(3,4,1)],[8,7,0,1,2,3,4,5],[(5,[]),(1,[1]),(2,[]),(26,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q212 : ck210 [176,177] d212 = true := by decide +kernel
private def lv_0_0_7_16 : List NodeSpec := (d210 ++ (d211 ++ d212))

private theorem ok_0_0_7_16 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_16 := by
  have go {ids ds} (h : ck210 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q210) (levelOK_append (go q211) (go q212)))
private def ck213 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d213 : List NodeSpec := [([(1,2,0),(2,3,6),(1,2,7)],[0,1,8,6,3,4,5],[(31,[]),(3,[1]),(5,[0]),(11,[])]),([(1,2,0),(2,3,6),(1,2,7)],[7,0,1,8,6,3,4,5],[(25,[]),(11,[])]),([(1,2,0),(2,3,6),(1,4,2)],[7,0,1,6,3,8,5],[(31,[]),(35,[]),(0,[0,1,2]),(5,[0])]),([(1,2,0),(2,3,6),(1,4,2)],[7,0,1,6,3,4,8,5],[(2,[0,1]),(5,[0]),(11,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q213 : ck213 [] d213 = true := by decide +kernel
private def d214 : List NodeSpec := [([(1,2,0),(2,3,6),(1,4,6)],[7,0,1,2,3,4,8,5],[(2,[0,1]),(5,[]),(10,[1]),(11,[]),(26,[])]),([(1,2,0),(3,3,6),(1,5,7)],[0,1,2,3,4,8],[(14,[]),(3,[1,2]),(1,[1,2]),(7,[])]),([(1,2,0),(3,4,1),(1,0,7)],[8,1,2,6,3,4,5],[(31,[]),(17,[]),(0,[0,1,2]),(7,[0])]),([(1,2,0),(3,4,1),(1,6,7)],[0,1,2,8,3,4,5],[(17,[]),(0,[0,1,2]),(2,[0,2]),(7,[]),(26,[]),(3,[1,2]),(6,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q214 : ck213 [177,178] d214 = true := by decide +kernel
private def d215 : List NodeSpec := [([(1,2,0),(3,4,1),(2,3,7)],[0,1,2,6,8,3,4,5],[(25,[]),(17,[]),(26,[])]),([(1,2,0),(1,4,2),(2,7,0)],[8,1,6,3,7,5],[(35,[]),(31,[]),(0,[0,1,2])]),([(1,2,0),(1,4,2),(0,7,1)],[0,8,1,6,3,7,5],[(35,[]),(31,[]),(0,[0,1,2])]),([(1,2,0),(1,4,2),(0,7,3)],[0,1,6,8,3,7,5],[(10,[]),(1,[1,2]),(0,[0,1,2]),(11,[]),(2,[0]),(5,[0]),(24,[]),(25,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q215 : ck213 [5,6,179,180,181,182,183,184] d215 = true := by decide +kernel
private def lv_0_0_7_17 : List NodeSpec := (d213 ++ (d214 ++ d215))

private theorem ok_0_0_7_17 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_17 := by
  have go {ids ds} (h : ck213 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q213) (levelOK_append (go q214) (go q215)))
private def ck216 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d216 : List NodeSpec := [([(1,2,0),(1,4,2),(2,7,3)],[8,0,1,6,3,7,5],[(10,[]),(1,[1,2]),(0,[0,1,2]),(11,[]),(2,[0]),(24,[]),(25,[])]),([(1,2,0),(1,4,6),(0,7,3)],[0,1,2,8,3,4,5],[(35,[]),(26,[]),(0,[0,1,2]),(4,[]),(6,[])]),([(1,2,0),(1,4,6),(0,7,3)],[0,1,2,6,8,3,4,5],[(35,[]),(1,[1,2]),(26,[])]),([(1,2,0),(3,4,6),(2,3,7)],[0,1,2,8,3,4,5],[(2,[0,2]),(0,[0,1,2]),(3,[1,2]),(4,[]),(5,[]),(6,[]),(1,[1,2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q216 : ck216 [7,185] d216 = true := by decide +kernel
private def d217 : List NodeSpec := [([(1,2,0),(1,4,3),(0,7,1)],[0,8,1,2,6,3,4,5],[(25,[]),(4,[]),(17,[])]),([(1,2,0),(1,4,3),(2,7,6)],[8,0,1,2,3,4,5],[(11,[]),(17,[]),(0,[0,1,2]),(4,[]),(6,[])]),([(1,2,0),(1,4,3),(2,7,6)],[8,0,1,2,6,3,4,5],[(11,[]),(17,[])]),([(1,2,0),(1,4,3),(3,5,7)],[8,0,1,2,6,3,4],[(11,[]),(17,[]),(8,[]),(13,[2]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q217 : ck216 [8,9,10,21,156,157,186,187,188] d217 = true := by decide +kernel
private def d218 : List NodeSpec := [([(1,2,1),(2,6,0),(0,3,7)],[8,0,1,2,3,4,5],[(26,[]),(3,[1,2]),(0,[0,1,2]),(1,[0,2]),(2,[]),(4,[]),(5,[])]),([(1,2,1),(2,6,0),(1,4,3)],[7,0,1,2,3,4,8,5],[(7,[]),(27,[]),(0,[0,1])]),([(1,2,1),(2,6,0),(3,4,3)],[8,7,0,1,2,3,4,5],[(18,[]),(26,[])]),([(1,2,1),(1,3,0),(0,7,6)],[0,1,2,8,3,4,5],[(35,[]),(27,[]),(0,[0,1,2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q218 : ck216 [189,190,191,192] d218 = true := by decide +kernel
private def lv_0_0_7_18 : List NodeSpec := (d216 ++ (d217 ++ d218))

private theorem ok_0_0_7_18 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_18 := by
  have go {ids ds} (h : ck216 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q216) (levelOK_append (go q217) (go q218)))
private def ck219 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d219 : List NodeSpec := [([(1,2,1),(2,3,0),(2,1,7)],[8,0,2,6,3,4,5],[(27,[]),(3,[1,2]),(4,[]),(26,[])]),([(1,2,1),(2,3,0),(2,1,7)],[7,8,0,2,6,3,4,5],[(26,[]),(6,[])]),([(1,2,1),(2,3,0),(2,6,7)],[8,0,1,2,3,4,5],[(3,[1,2]),(1,[0,2]),(0,[0,1,2]),(2,[]),(5,[]),(4,[]),(6,[])]),([(1,2,1),(2,3,0),(2,6,7)],[7,8,0,1,2,3,4,5],[(1,[0,2]),(6,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q219 : ck219 [193,194] d219 = true := by decide +kernel
private def d220 : List NodeSpec := [([(1,2,1),(2,3,0),(1,4,7)],[0,1,2,6,3,4,8,5],[(5,[]),(2,[1]),(6,[])]),([(1,2,1),(2,3,0),(3,4,7)],[8,0,1,2,6,3,4,5],[(6,[]),(4,[]),(5,[])]),([(1,2,1),(2,3,0),(1,4,3)],[7,0,1,2,6,4,8,5],[]),([(1,2,1),(2,3,0),(3,4,3)],[8,7,0,1,2,6,4,5],[(1,[0]),(26,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q220 : ck219 [189,193,194,195,196] d220 = true := by decide +kernel
private def d221 : List NodeSpec := [([(1,2,1),(1,3,1),(0,3,6)],[0,2,8,7,4,5],[(35,[]),(0,[0,1,2]),(27,[])]),([(1,2,1),(3,3,1),(1,0,7)],[0,8,2,6,3,4,5],[(11,[]),(27,[]),(0,[0,1,2]),(2,[0,1,2])]),([(1,2,1),(3,3,1),(2,6,7)],[0,2,8,6,3,4,5],[(3,[1,2]),(27,[]),(0,[0,1,2]),(2,[0,1,2])]),([(1,2,1),(3,3,1),(2,6,7)],[0,1,2,8,3,4,5],[(27,[]),(3,[1,2]),(0,[0,1,2]),(2,[0,1,2]),(5,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q221 : ck219 [197] d221 = true := by decide +kernel
private def lv_0_0_7_19 : List NodeSpec := (d219 ++ (d220 ++ d221))

private theorem ok_0_0_7_19 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_19 := by
  have go {ids ds} (h : ck219 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q219) (levelOK_append (go q220) (go q221)))
private def ck222 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d222 : List NodeSpec := [([(1,2,1),(0,3,6),(1,7,0)],[0,1,2,8,3,4,5],[(27,[]),(3,[1,2]),(0,[0,1,2]),(2,[]),(5,[]),(26,[])]),([(1,2,1),(0,3,6),(1,7,0)],[0,1,2,7,8,3,4,5],[(27,[]),(7,[0]),(26,[])]),([(1,2,1),(0,3,6),(1,4,0)],[0,1,2,7,3,4,8,5],[(12,[]),(5,[]),(27,[]),(11,[]),(26,[])]),([(1,2,1),(0,3,6),(3,4,1)],[8,0,1,2,7,3,4,5],[(10,[]),(5,[]),(6,[]),(11,[]),(26,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q222 : ck222 [139,198,199,200] d222 = true := by decide +kernel
private def d223 : List NodeSpec := [([(1,2,1),(0,3,6),(1,4,7)],[0,1,2,7,3,4,8,5],[(35,[]),(26,[])]),([(1,2,1),(0,3,6),(1,4,3)],[0,1,2,7,4,8,5],[(11,[]),(0,[0,1,2]),(2,[0,1]),(1,[0,1]),(6,[])]),([(1,2,1),(0,3,6),(3,4,3)],[8,0,1,2,7,4,5],[(26,[]),(3,[1,2]),(2,[0,1]),(6,[]),(0,[0,1]),(1,[0,1])]),([(1,2,1),(0,3,6),(1,4,7)],[0,1,2,6,3,4,8,5],[(2,[0,1]),(5,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q223 : ck222 [12,13,140,141,189,199,200,201] d223 = true := by decide +kernel
private def d224 : List NodeSpec := [([(1,2,1),(0,3,6),(3,4,7)],[8,0,1,2,6,3,4,5],[(3,[]),(4,[]),(18,[])]),([(1,2,1),(0,3,6),(3,4,6)],[8,0,1,2,7,3,4,5],[(2,[0,1]),(5,[]),(6,[]),(11,[]),(26,[])]),([(1,2,1),(0,3,6),(1,4,3)],[0,1,2,7,6,4,8,5],[(6,[]),(0,[0,1]),(7,[])]),([(1,2,1),(0,3,6),(3,4,3)],[8,0,1,2,7,6,4,5],[(6,[]),(7,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q224 : ck222 [] d224 = true := by decide +kernel
private def lv_0_0_7_20 : List NodeSpec := (d222 ++ (d223 ++ d224))

private theorem ok_0_0_7_20 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_20 := by
  have go {ids ds} (h : ck222 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q222) (levelOK_append (go q223) (go q224)))
private def ck225 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d225 : List NodeSpec := [([(1,2,1),(1,3,6),(3,5,7)],[8,0,1,2,3,4],[(14,[]),(3,[1,2]),(6,[]),(7,[])]),([(1,2,1),(2,3,6),(2,3,7)],[0,1,2,8,3,4,5],[(11,[]),(26,[]),(27,[]),(0,[0,1,2]),(2,[]),(5,[])]),([(1,2,1),(3,3,6),(1,0,7)],[0,8,1,2,3,4,5],[(18,[]),(3,[1,2]),(0,[0,1,2]),(1,[0,1]),(4,[]),(6,[])]),([(1,2,1),(1,4,0),(0,7,3)],[0,1,2,6,8,3,4,5],[(6,[]),(26,[]),(3,[]),(4,[]),(18,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q225 : ck225 [202,203] d225 = true := by decide +kernel
private def d226 : List NodeSpec := [([(1,2,1),(3,4,1),(2,3,7)],[0,1,2,6,8,3,4,5],[(10,[]),(6,[]),(18,[]),(26,[])]),([(1,2,1),(1,4,6),(0,7,3)],[0,1,2,8,3,4,5],[(17,[]),(3,[1,2]),(0,[0,1,2]),(6,[])]),([(1,2,1),(3,4,6),(2,3,7)],[0,1,2,8,3,4,5],[(17,[]),(2,[0,2]),(0,[0,1,2]),(3,[1,2]),(6,[])]),([(1,2,1),(3,4,6),(2,3,7)],[0,1,2,6,8,3,4,5],[(35,[]),(26,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q226 : ck225 [204] d226 = true := by decide +kernel
private def d227 : List NodeSpec := [([(1,2,1),(1,4,3),(2,7,0)],[8,0,1,2,6,3,4,5],[(17,[]),(6,[])]),([(1,2,1),(1,4,3),(0,7,6)],[0,1,2,8,3,4,5],[(3,[1,2]),(2,[0,2]),(0,[0,1,2]),(7,[0]),(1,[]),(6,[])]),([(1,2,1),(1,4,3),(0,7,6)],[0,1,2,8,6,3,4,5],[(3,[1,2]),(5,[])]),([(1,2,1),(1,4,3),(3,5,7)],[8,0,1,2,6,3,4],[(11,[]),(20,[]),(2,[0,2]),(1,[1,2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q227 : ck225 [14,15,16,21,142,190,191,192,205] d227 = true := by decide +kernel
private def lv_0_0_7_21 : List NodeSpec := (d225 ++ (d226 ++ d227))

private theorem ok_0_0_7_21 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_21 := by
  have go {ids ds} (h : ck225 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q225) (levelOK_append (go q226) (go q227)))
private def ck228 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d228 : List NodeSpec := [([(3,2,1),(1,0,6),(0,3,7)],[0,8,1,2,3,4,5],[(24,[]),(1,[0,2]),(0,[0,1,2]),(2,[]),(5,[])]),([(3,2,1),(1,0,6),(3,4,7)],[8,0,1,2,3,5],[(24,[]),(0,[0,1,2]),(1,[0,2]),(5,[])]),([(3,2,1),(1,0,6),(1,4,3)],[0,7,1,2,3,4,8,5],[(5,[]),(14,[]),(0,[0,1]),(0,[2]),(1,[0]),(20,[]),(24,[])]),([(3,2,1),(1,0,6),(3,4,3)],[8,0,7,1,2,3,4,5],[(5,[]),(18,[]),(0,[2]),(14,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q228 : ck228 [206,207] d228 = true := by decide +kernel
private def d229 : List NodeSpec := [([(3,2,1),(1,0,6),(3,5,7)],[8,0,1,2,3,4],[(14,[]),(3,[1,2]),(1,[0,2]),(20,[])]),([(3,2,1),(0,3,6),(1,0,7)],[0,8,1,2,3,4,5],[(1,[0,1]),(13,[]),(0,[0,1,2]),(3,[1,2]),(26,[])]),([(3,2,1),(0,3,6),(1,3,1)],[7,0,2,8,4,5],[(11,[]),(13,[]),(0,[0,1,2])]),([(3,2,1),(1,3,6),(3,5,7)],[8,0,1,2,3,4],[(14,[]),(3,[1,2]),(7,[]),(20,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q229 : ck228 [] d229 = true := by decide +kernel
private def d230 : List NodeSpec := [([(3,2,1),(3,3,6),(1,0,7)],[0,8,1,2,3,4,5],[(1,[0,1]),(0,[0,1,2]),(3,[1,2]),(2,[0,1,2]),(4,[]),(5,[]),(7,[])]),([(3,2,1),(1,3,0),(2,7,2)],[6,8,0,1,3,4,5],[(11,[]),(1,[0,2]),(6,[])]),([(3,2,1),(2,3,0),(3,7,6)],[8,7,0,1,2,3,4,5],[(24,[])]),([(3,2,1),(2,3,0),(2,1,7)],[6,7,8,0,2,3,4,5],[(26,[]),(6,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q230 : ck228 [] d230 = true := by decide +kernel
private def lv_0_0_7_22 : List NodeSpec := (d228 ++ (d229 ++ d230))

private theorem ok_0_0_7_22 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_22 := by
  have go {ids ds} (h : ck228 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q228) (levelOK_append (go q229) (go q230)))
private def ck231 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d231 : List NodeSpec := [([(3,2,1),(2,3,0),(1,4,7)],[6,0,1,2,3,4,8,5],[(5,[]),(2,[1]),(4,[]),(24,[])]),([(3,2,1),(2,3,0),(3,4,7)],[8,6,0,1,2,3,4,5],[(4,[]),(24,[])]),([(3,2,1),(2,3,0),(1,4,3)],[6,7,0,1,2,4,8,5],[]),([(3,2,1),(2,3,0),(3,4,3)],[8,6,7,0,1,2,4,5],[(1,[0])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q231 : ck231 [] d231 = true := by decide +kernel
private def d232 : List NodeSpec := [([(3,2,1),(3,3,1),(1,0,7)],[6,0,8,2,3,4,5],[(11,[]),(4,[]),(0,[0,1,2]),(2,[0,1,2])]),([(3,2,1),(3,4,6),(2,3,7)],[0,1,2,8,3,4,5],[(17,[]),(3,[1,2]),(4,[]),(0,[0,1,2])]),([(3,2,1),(1,4,0),(0,7,3)],[6,0,1,2,8,3,4,5],[(4,[]),(24,[])]),([(3,2,1),(1,4,3),(2,7,0)],[6,8,0,1,2,3,4,5],[(17,[]),(4,[]),(24,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q232 : ck231 [17,206] d232 = true := by decide +kernel
private def d233 : List NodeSpec := [([(1,3,0),(2,3,0),(1,1,7)],[7,1,8,2,3,6,4,5],[(1,[2])]),([(1,3,0),(2,3,0),(2,1,7)],[7,8,1,2,3,6,4,5],[(0,[1,2]),(26,[])]),([(1,3,0),(2,3,1),(2,6,7)],[0,8,1,2,3,4,5],[(11,[]),(1,[1,2]),(0,[0,1,2]),(2,[]),(5,[])]),([(1,3,0),(0,6,1),(1,2,7)],[0,1,2,8,3,4,5],[(13,[]),(0,[0,1,2]),(1,[1,2]),(7,[2]),(3,[0,1]),(6,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q233 : ck231 [208] d233 = true := by decide +kernel
private def lv_0_0_7_23 : List NodeSpec := (d231 ++ (d232 ++ d233))

private theorem ok_0_0_7_23 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_23 := by
  have go {ids ds} (h : ck231 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q231) (levelOK_append (go q232) (go q233)))
private def ck234 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d234 : List NodeSpec := [([(1,3,0),(0,6,1),(1,4,2)],[0,7,1,2,3,8,5],[(31,[]),(4,[2]),(0,[0,1,2]),(2,[0,1]),(5,[]),(10,[])]),([(1,3,0),(3,4,1),(2,6,7)],[0,1,2,3,8,4,5],[(35,[]),(1,[1,2]),(0,[0,1,2])]),([(1,3,0),(1,4,6),(3,5,7)],[8,0,1,2,3,4],[(11,[]),(1,[1,2]),(2,[0,2]),(8,[])]),([(2,3,0),(0,1,6),(1,0,7)],[6,1,8,2,3,4,5],[(26,[]),(0,[0,1,2]),(4,[]),(1,[1])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q234 : ck234 [208,209,210,211,212,213,214,215] d234 = true := by decide +kernel
private def d235 : List NodeSpec := [([(2,3,0),(0,1,6),(2,1,7)],[6,8,0,1,2,3,4,5],[(26,[]),(6,[])]),([(2,3,0),(0,1,6),(1,1,6)],[7,0,8,2,3,4,5],[(31,[]),(26,[])]),([(2,3,0),(0,1,6),(1,2,7)],[6,0,1,2,8,3,4,5],[(31,[]),(26,[]),(4,[])]),([(2,3,0),(0,1,6),(1,2,6)],[7,0,1,2,8,3,4,5],[(24,[]),(27,[2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q235 : ck234 [209,216,217,218,219] d235 = true := by decide +kernel
private def d236 : List NodeSpec := [([(2,3,0),(0,1,6),(1,3,2)],[7,6,0,1,2,8,4,5],[(31,[])]),([(2,3,0),(0,1,6),(1,4,6)],[7,0,1,2,3,4,8,5],[(2,[0]),(5,[])]),([(2,3,0),(0,1,6),(1,4,2)],[7,6,0,1,2,3,8,5],[(31,[]),(4,[2])]),([(2,3,0),(0,1,6),(2,4,2)],[8,7,6,0,1,2,3,5],[(31,[]),(4,[2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q236 : ck234 [210,211,212,213,218,220] d236 = true := by decide +kernel
private def lv_0_0_7_24 : List NodeSpec := (d234 ++ (d235 ++ d236))

private theorem ok_0_0_7_24 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_24 := by
  have go {ids ds} (h : ck234 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q234) (levelOK_append (go q235) (go q236)))
private def ck237 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d237 : List NodeSpec := [([(2,3,0),(0,1,6),(1,4,3)],[7,6,0,1,2,4,8,5],[]),([(2,3,0),(0,1,6),(1,5,2)],[7,6,0,1,2,3,4,8],[(31,[]),(4,[2])]),([(2,3,0),(1,1,6),(0,3,1)],[0,8,7,2,3,4,5],[(24,[]),(26,[]),(1,[1,2]),(0,[0,1,2])]),([(2,3,0),(1,1,6),(1,4,3)],[0,1,7,2,3,4,8,5],[(6,[]),(12,[]),(0,[0,1]),(4,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q237 : ck237 [214,215,217,219,221,222,223,224] d237 = true := by decide +kernel
private def d238 : List NodeSpec := [([(2,3,0),(1,1,6),(3,4,3)],[8,0,1,7,2,3,4,5],[(26,[]),(13,[])]),([(2,3,0),(1,1,6),(1,4,6)],[0,1,7,2,3,4,8,5],[(2,[0,1]),(5,[]),(6,[])]),([(2,3,0),(1,1,6),(3,4,6)],[8,0,1,7,2,3,4,5],[(13,[])]),([(2,3,0),(1,1,6),(1,4,3)],[6,0,1,7,2,4,8,5],[])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q238 : ck237 [217,225] d238 = true := by decide +kernel
private def d239 : List NodeSpec := [([(2,3,0),(1,1,6),(3,4,3)],[8,6,0,1,7,2,4,5],[(1,[1]),(26,[])]),([(2,3,0),(2,1,6),(1,2,7)],[0,1,2,8,3,4,5],[(3,[0,1]),(1,[1,2]),(0,[0,1,2]),(4,[]),(2,[]),(5,[]),(6,[]),(25,[])]),([(2,3,0),(2,1,6),(2,3,1)],[8,7,0,2,3,4,5],[(31,[]),(4,[])]),([(2,3,0),(2,1,6),(1,3,2)],[7,0,1,2,3,8,4,5],[(25,[]),(4,[]),(6,[2]),(27,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q239 : ck237 [226] d239 = true := by decide +kernel
private def lv_0_0_7_25 : List NodeSpec := (d237 ++ (d238 ++ d239))

private theorem ok_0_0_7_25 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_25 := by
  have go {ids ds} (h : ck237 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q237) (levelOK_append (go q238) (go q239)))
private def ck240 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d240 : List NodeSpec := [([(2,3,0),(2,1,6),(2,3,2)],[8,7,0,1,2,3,4,5],[(26,[]),(11,[])]),([(2,3,0),(2,1,6),(1,4,2)],[7,0,1,2,3,8,5],[(31,[]),(4,[2]),(0,[0,1,2]),(2,[0,1]),(5,[]),(10,[])]),([(2,3,0),(2,1,6),(3,1,6)],[8,7,0,2,3,4,5],[(31,[]),(26,[])]),([(2,3,0),(2,1,6),(1,2,6)],[7,0,1,2,8,3,4,5],[(3,[0,1]),(27,[]),(4,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q240 : ck240 [216,227,228] d240 = true := by decide +kernel
private def d241 : List NodeSpec := [([(2,3,0),(2,1,6),(3,2,6)],[8,7,0,1,2,3,4,5],[(26,[]),(24,[]),(25,[1])]),([(2,3,0),(2,1,6),(1,2,7)],[6,0,1,2,8,3,4,5],[(3,[0,1]),(6,[])]),([(2,3,0),(2,1,6),(1,3,2)],[6,7,0,1,2,8,4,5],[(3,[0]),(6,[2]),(25,[1])]),([(2,3,0),(2,1,6),(2,3,2)],[8,6,7,0,1,2,4,5],[(1,[1]),(6,[2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q241 : ck240 [228,229] d241 = true := by decide +kernel
private def d242 : List NodeSpec := [([(2,3,0),(2,1,6),(1,4,6)],[7,0,1,2,3,4,8,5],[(2,[0,1]),(5,[]),(4,[]),(27,[])]),([(2,3,0),(2,1,6),(3,4,6)],[8,7,0,1,2,3,4,5],[]),([(2,3,0),(2,1,6),(1,4,2)],[6,7,0,1,2,3,8,5],[(31,[]),(4,[2])]),([(2,3,0),(2,1,6),(2,4,2)],[8,6,7,0,1,2,3,5],[(31,[]),(4,[2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q242 : ck240 [230] d242 = true := by decide +kernel
private def lv_0_0_7_26 : List NodeSpec := (d240 ++ (d241 ++ d242))

private theorem ok_0_0_7_26 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_26 := by
  have go {ids ds} (h : ck240 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q240) (levelOK_append (go q241) (go q242)))
private def ck243 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d243 : List NodeSpec := [([(2,3,0),(2,1,6),(1,4,3)],[6,7,0,1,2,4,8,5],[(2,[0]),(5,[0])]),([(2,3,0),(2,1,6),(3,4,3)],[8,6,7,0,1,2,4,5],[(1,[1])]),([(2,3,0),(2,1,6),(1,5,2)],[6,7,0,1,2,3,4,8],[(31,[]),(4,[2])]),([(2,3,0),(3,1,6),(1,0,7)],[6,8,1,2,3,4,5],[(31,[]),(26,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q243 : ck243 [231] d243 = true := by decide +kernel
private def d244 : List NodeSpec := [([(2,3,0),(3,1,6),(2,3,7)],[6,0,1,8,2,4,5],[(31,[]),(26,[]),(5,[0])]),([(2,3,0),(3,1,6),(1,4,7)],[6,0,1,2,3,8,5],[(31,[]),(26,[]),(17,[]),(0,[0,1,2])]),([(2,3,0),(3,1,6),(1,4,6)],[7,0,1,2,3,4,8,5],[(33,[]),(0,[0,2]),(5,[]),(13,[])]),([(2,3,0),(3,1,6),(1,4,3)],[7,6,0,1,2,4,8,5],[(33,[]),(0,[0,2]),(5,[0])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q244 : ck243 [231,232] d244 = true := by decide +kernel
private def d245 : List NodeSpec := [([(2,3,0),(3,1,6),(1,5,7)],[6,0,1,2,3,4,8],[(31,[]),(33,[]),(26,[])]),([(2,3,0),(1,2,6),(0,7,1)],[0,8,1,2,7,3,4,5],[(31,[]),(4,[])]),([(2,3,0),(1,2,6),(3,7,1)],[8,0,1,2,7,3,4,5],[(31,[]),(4,[])]),([(2,3,0),(1,2,6),(0,3,1)],[0,8,1,2,7,3,4,5],[(1,[1]),(1,[2]),(11,[]),(24,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q245 : ck243 [209,228,233] d245 = true := by decide +kernel
private def lv_0_0_7_27 : List NodeSpec := (d243 ++ (d244 ++ d245))

private theorem ok_0_0_7_27 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_27 := by
  have go {ids ds} (h : ck243 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q243) (levelOK_append (go q244) (go q245)))
private def ck246 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d246 : List NodeSpec := [([(2,3,0),(1,2,6),(2,3,2)],[8,0,1,7,3,4,5],[(11,[]),(26,[])]),([(2,3,0),(1,2,6),(3,4,1)],[8,0,1,2,7,3,4,5],[(5,[]),(1,[1]),(2,[])]),([(2,3,0),(1,2,6),(1,4,7)],[0,1,2,7,3,4,8,5],[(2,[0,1]),(1,[1]),(5,[]),(11,[])]),([(2,3,0),(1,2,6),(3,4,7)],[8,0,1,2,7,3,4,5],[(2,[0,1]),(5,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q246 : ck246 [234,235,236,237] d246 = true := by decide +kernel
private def d247 : List NodeSpec := [([(2,3,0),(1,2,6),(0,7,1)],[6,0,8,1,2,3,4,5],[(31,[]),(4,[])]),([(2,3,0),(1,2,6),(2,3,2)],[8,6,0,1,7,4,5],[(11,[]),(31,[])]),([(2,3,0),(1,2,6),(1,4,6)],[0,1,2,7,3,4,8,5],[(2,[0,1]),(3,[0]),(5,[])]),([(2,3,0),(1,2,6),(3,4,6)],[8,0,1,2,7,3,4,5],[(2,[0]),(5,[]),(10,[]),(18,[1])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q247 : ck246 [237,238] d247 = true := by decide +kernel
private def d248 : List NodeSpec := [([(2,3,0),(1,2,6),(1,4,3)],[6,0,1,2,7,4,8,5],[(3,[0,2]),(7,[1]),(12,[])]),([(2,3,0),(1,2,6),(3,4,3)],[8,6,0,1,2,7,4,5],[(1,[1]),(2,[0]),(3,[0,2]),(5,[0]),(11,[])]),([(2,3,0),(3,2,6),(2,1,7)],[6,0,8,1,2,3,4,5],[(26,[]),(3,[0,2]),(6,[])]),([(2,3,0),(3,2,6),(1,4,6)],[7,0,1,2,3,4,8,5],[(2,[0]),(5,[]),(10,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q248 : ck246 [239] d248 = true := by decide +kernel
private def lv_0_0_7_28 : List NodeSpec := (d246 ++ (d247 ++ d248))

private theorem ok_0_0_7_28 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_28 := by
  have go {ids ds} (h : ck246 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q246) (levelOK_append (go q247) (go q248)))
private def ck249 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d249 : List NodeSpec := [([(2,3,0),(3,2,6),(1,4,3)],[7,6,0,1,2,4,8,5],[(11,[])]),([(2,3,0),(0,3,1),(1,2,7)],[6,0,1,2,8,3,4,5],[(26,[]),(25,[]),(4,[]),(11,[]),(24,[])]),([(2,3,0),(0,3,1),(1,3,1)],[6,0,7,2,8,4,5],[(11,[]),(26,[]),(0,[0,1,2]),(18,[])]),([(2,3,0),(0,3,1),(1,3,2)],[6,0,7,1,2,8,4,5],[(24,[]),(1,[2]),(25,[1])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q249 : ck249 [210,240,241,242] d249 = true := by decide +kernel
private def d250 : List NodeSpec := [([(2,3,0),(0,3,1),(1,4,6)],[0,7,1,2,3,4,8,5],[(1,[2]),(18,[]),(1,[1]),(5,[])]),([(2,3,0),(0,3,1),(1,4,2)],[6,0,7,1,2,3,8,5],[(1,[1,2]),(11,[]),(24,[]),(4,[2])]),([(2,3,0),(0,3,1),(2,4,2)],[8,6,0,7,1,2,3,5],[(1,[1,2]),(24,[]),(4,[2]),(11,[])]),([(2,3,0),(0,3,1),(1,4,3)],[6,0,7,1,2,4,8,5],[(0,[0,1]),(1,[2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q250 : ck249 [211,212,213,214,222,241,243] d250 = true := by decide +kernel
private def d251 : List NodeSpec := [([(2,3,0),(0,3,1),(1,5,2)],[6,0,7,1,2,3,4,8],[(1,[1,2]),(11,[]),(24,[]),(4,[2])]),([(2,3,0),(1,3,1),(2,7,6)],[0,8,1,2,3,4,5],[(11,[]),(0,[0,1,2]),(1,[1,2]),(2,[]),(5,[]),(4,[])]),([(2,3,0),(1,3,1),(2,7,6)],[6,0,8,1,2,3,4,5],[(7,[]),(26,[])]),([(2,3,0),(1,3,1),(3,5,7)],[8,6,0,1,2,3,4],[(11,[]),(18,[]),(0,[0,1]),(1,[1,2]),(4,[2]),(6,[]),(8,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q251 : ck249 [215,242] d251 = true := by decide +kernel
private def lv_0_0_7_29 : List NodeSpec := (d249 ++ (d250 ++ d251))

private theorem ok_0_0_7_29 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_29 := by
  have go {ids ds} (h : ck249 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q249) (levelOK_append (go q250) (go q251)))
private def ck252 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d252 : List NodeSpec := [([(2,3,0),(2,3,1),(1,4,6)],[7,0,1,2,3,4,8,5],[(5,[]),(1,[1]),(2,[0]),(13,[])]),([(2,3,0),(2,3,1),(1,4,3)],[7,6,0,1,2,4,8,5],[(1,[2])]),([(2,3,0),(1,3,2),(0,7,1)],[6,0,8,1,2,7,4,5],[(24,[]),(1,[1]),(7,[]),(25,[2])]),([(2,3,0),(1,3,2),(2,7,2)],[8,6,0,1,7,4,5],[(11,[]),(24,[]),(25,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q252 : ck252 [231,244] d252 = true := by decide +kernel
private def d253 : List NodeSpec := [([(2,3,0),(1,3,2),(1,4,6)],[6,0,1,2,7,4,8,5],[(5,[0])]),([(2,3,0),(1,3,2),(3,4,6)],[8,6,0,1,2,7,4,5],[(18,[])]),([(2,3,0),(1,3,2),(3,4,1)],[8,6,0,1,2,7,4,5],[(1,[1])]),([(2,3,0),(1,3,2),(0,7,1)],[6,0,8,1,2,3,4,5],[(4,[]),(24,[]),(7,[]),(1,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q253 : ck252 [238,245,246,247,248] d253 = true := by decide +kernel
private def d254 : List NodeSpec := [([(2,3,0),(2,3,2),(1,4,6)],[7,6,0,1,2,4,8,5],[(1,[2]),(5,[0])]),([(2,3,0),(2,3,2),(3,4,1)],[8,7,6,0,1,2,4,5],[(1,[1]),(1,[2]),(26,[])]),([(2,3,0),(1,4,6),(2,7,2)],[8,0,1,2,3,4,5],[(2,[0,2]),(5,[]),(0,[0,1,2]),(4,[]),(6,[]),(1,[1,2]),(3,[0,1]),(25,[])]),([(2,3,0),(1,4,6),(1,5,2)],[0,1,2,3,4,7,8],[(5,[2]),(2,[0,2]),(3,[0,1]),(0,[0,1]),(4,[2]),(6,[2]),(8,[]),(19,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q254 : ck252 [249,250] d254 = true := by decide +kernel
private def lv_0_0_7_30 : List NodeSpec := (d252 ++ (d253 ++ d254))

private theorem ok_0_0_7_30 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_30 := by
  have go {ids ds} (h : ck252 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q252) (levelOK_append (go q253) (go q254)))
private def ck255 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d255 : List NodeSpec := [([(2,3,0),(1,4,6),(0,7,1)],[6,0,8,1,2,3,4,5],[(2,[0,2]),(26,[]),(4,[])]),([(2,3,0),(1,4,6),(2,7,2)],[8,6,0,1,2,3,4,5],[(2,[0,2]),(17,[]),(3,[0,1]),(25,[])]),([(2,3,0),(1,4,6),(1,5,2)],[6,0,1,2,3,4,7,8],[(17,[2]),(2,[0,2])]),([(2,3,0),(3,4,6),(1,2,7)],[0,1,2,8,3,4,5],[(3,[0,1]),(5,[]),(0,[0,1,2]),(1,[1,2]),(4,[]),(6,[]),(26,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q255 : ck255 [225,237] d255 = true := by decide +kernel
private def d256 : List NodeSpec := [([(2,3,0),(3,4,6),(1,5,2)],[7,0,1,2,3,4,8],[(5,[2]),(3,[0,1]),(0,[0,1]),(1,[1,2]),(4,[2]),(6,[2]),(8,[]),(12,[2]),(19,[])]),([(2,3,0),(3,4,6),(2,1,7)],[6,0,8,1,2,3,4,5],[(2,[0,2]),(26,[]),(5,[]),(6,[])]),([(2,3,0),(3,4,6),(1,2,7)],[6,0,1,2,8,3,4,5],[(3,[0,1]),(26,[]),(17,[]),(2,[0,2])]),([(2,3,0),(3,4,6),(1,5,2)],[7,6,0,1,2,3,4,8],[(2,[0,2]),(5,[2]),(12,[2]),(18,[2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q256 : ck255 [] d256 = true := by decide +kernel
private def d257 : List NodeSpec := [([(2,3,0),(1,4,1),(2,7,6)],[6,0,8,1,2,3,4,5],[(5,[])]),([(2,3,0),(3,4,1),(1,6,7)],[8,0,1,2,3,4,5],[(17,[]),(0,[0,1,2]),(2,[0,2]),(3,[]),(6,[])]),([(2,3,0),(3,4,1),(1,6,7)],[6,8,0,1,2,3,4,5],[(1,[]),(4,[]),(7,[])]),([(2,3,0),(3,4,1),(2,6,7)],[8,0,1,2,3,4,5],[(26,[]),(17,[]),(0,[0,1,2]),(2,[0,2]),(3,[]),(6,[]),(8,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q257 : ck255 [235,246,247,249,251,252,253,254] d257 = true := by decide +kernel
private def lv_0_0_7_31 : List NodeSpec := (d255 ++ (d256 ++ d257))

private theorem ok_0_0_7_31 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_31 := by
  have go {ids ds} (h : ck255 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q255) (levelOK_append (go q256) (go q257)))
private def ck258 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d258 : List NodeSpec := [([(2,3,0),(3,4,1),(1,0,7)],[6,8,1,2,3,4,5],[(17,[]),(0,[0,1,2]),(2,[0,2]),(4,[]),(7,[])]),([(2,3,0),(3,4,1),(1,2,7)],[6,0,1,2,8,3,4,5],[(17,[]),(26,[]),(2,[0]),(2,[2])]),([(2,3,0),(3,4,1),(1,5,2)],[7,6,0,1,2,3,4,8],[(5,[2]),(1,[2]),(2,[2])]),([(2,3,0),(1,4,3),(2,7,2)],[8,6,0,1,2,4,5],[(11,[]),(17,[]),(0,[0,1,2]),(12,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q258 : ck258 [177,234,235,239,248,250,252,254,255,256] d258 = true := by decide +kernel
private def d259 : List NodeSpec := [([(2,3,0),(1,4,3),(1,5,2)],[6,0,1,2,4,7,8],[(17,[2]),(11,[]),(0,[0,1]),(2,[0,2]),(12,[2])]),([(2,3,0),(1,4,3),(0,7,1)],[6,0,8,1,2,3,4,5],[(4,[]),(7,[]),(6,[]),(12,[])]),([(2,3,0),(1,4,3),(3,5,7)],[8,6,0,1,2,3,4],[(11,[]),(2,[0,2]),(0,[0,1]),(1,[1,2]),(13,[2]),(8,[])]),([(2,3,0),(3,4,3),(1,2,7)],[6,0,1,2,8,4,5],[(17,[]),(2,[0,2]),(3,[0,1]),(11,[]),(25,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q259 : ck258 [56,223,224] d259 = true := by decide +kernel
private def d260 : List NodeSpec := [([(2,3,0),(3,4,3),(1,5,2)],[7,6,0,1,2,4,8],[(17,[2]),(2,[0,2]),(0,[0,1]),(3,[0,1]),(11,[])]),([(0,3,1),(1,6,0),(1,2,7)],[0,1,7,2,8,3,4,5],[(3,[0,1]),(25,[0]),(27,[])]),([(0,3,1),(1,6,0),(3,2,7)],[8,0,1,2,3,4,5],[(1,[0,2]),(0,[0,1,2]),(3,[0,1]),(2,[]),(5,[]),(4,[]),(24,[])]),([(0,3,1),(1,6,0),(3,2,7)],[8,0,1,7,2,3,4,5],[(3,[0,1]),(4,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q260 : ck258 [158,167,257,258] d260 = true := by decide +kernel
private def lv_0_0_7_32 : List NodeSpec := (d258 ++ (d259 ++ d260))

private theorem ok_0_0_7_32 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_32 := by
  have go {ids ds} (h : ck258 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q258) (levelOK_append (go q259) (go q260)))
private def ck261 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d261 : List NodeSpec := [([(0,3,1),(1,6,0),(1,3,2)],[0,1,7,2,3,8,4,5],[(1,[0]),(1,[2]),(24,[])]),([(0,3,1),(1,6,0),(2,3,2)],[8,0,1,7,2,3,4,5],[(26,[]),(11,[])]),([(0,3,1),(1,6,0),(1,4,0)],[1,7,2,3,4,8,5],[(34,[]),(26,[]),(0,[0,1,2]),(1,[0])]),([(0,3,1),(1,6,0),(1,4,7)],[0,1,7,2,3,4,8,5],[(13,[]),(0,[0,1]),(5,[]),(20,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q261 : ck261 [161,210,259,260,261,262] d261 = true := by decide +kernel
private def d262 : List NodeSpec := [([(0,3,1),(1,6,0),(3,4,7)],[8,0,1,7,2,3,4,5],[(2,[0,1]),(4,[]),(5,[])]),([(0,3,1),(1,6,0),(1,4,2)],[0,1,7,2,3,8,5],[(1,[0,2]),(3,[0,1]),(0,[0,1,2]),(4,[2]),(5,[]),(10,[]),(2,[0,1]),(6,[2])]),([(0,3,1),(1,6,0),(1,4,2)],[0,1,7,2,3,4,8,5],[(10,[]),(5,[]),(1,[0,2]),(2,[0,1])]),([(0,3,1),(1,6,0),(2,4,2)],[8,0,1,7,2,3,5],[(1,[0,2]),(2,[0,1]),(3,[0,1]),(0,[0,1,2]),(4,[2]),(6,[2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q262 : ck261 [159,160,161,168,169,212,213,258,260,261,263] d262 = true := by decide +kernel
private def d263 : List NodeSpec := [([(0,3,1),(1,6,0),(1,4,3)],[0,1,7,2,3,4,8,5],[(1,[0]),(1,[2]),(0,[0,1]),(2,[]),(5,[]),(20,[])]),([(0,3,1),(1,6,0),(3,4,3)],[8,0,1,7,2,3,4,5],[(26,[]),(12,[])]),([(0,3,1),(1,6,0),(1,5,2)],[0,1,7,2,3,4,8],[(34,[]),(3,[0,1]),(1,[0,2]),(6,[2])]),([(0,3,1),(1,6,0),(1,2,6)],[0,1,7,2,8,3,4,5],[(31,[]),(20,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q263 : ck261 [162,214,215,257,264,265,266,267] d263 = true := by decide +kernel
private def lv_0_0_7_33 : List NodeSpec := (d261 ++ (d262 ++ d263))

private theorem ok_0_0_7_33 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_33 := by
  have go {ids ds} (h : ck261 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q261) (levelOK_append (go q262) (go q263)))
private def ck264 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d264 : List NodeSpec := [([(0,3,1),(1,6,0),(3,2,7)],[8,0,6,1,2,3,4,5],[(31,[]),(4,[])]),([(0,3,1),(1,6,0),(1,3,1)],[0,6,7,2,8,4,5],[(31,[]),(13,[]),(0,[0,1,2])]),([(0,3,1),(1,6,0),(1,3,1)],[0,6,7,2,3,8,4,5],[(1,[0,2]),(26,[])]),([(0,3,1),(1,6,0),(1,4,2)],[0,6,1,7,2,3,8,5],[(31,[]),(4,[2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q264 : ck264 [163,170,266,267,268,269,270] d264 = true := by decide +kernel
private def d265 : List NodeSpec := [([(0,3,1),(2,1,6),(1,0,7)],[0,8,1,2,3,4,5],[(11,[]),(1,[0,1]),(0,[0,1,2]),(2,[0,1,2]),(5,[]),(4,[])]),([(0,3,1),(2,1,6),(1,0,7)],[0,8,6,2,3,4,5],[(11,[]),(1,[0,1]),(4,[]),(0,[0,1,2]),(2,[0,1,2])]),([(0,3,1),(2,1,6),(1,3,7)],[0,6,2,8,4,5],[(11,[]),(13,[]),(0,[0,1,2])]),([(0,3,1),(1,2,6),(1,7,0)],[0,1,2,7,8,3,4,5],[(31,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q265 : ck264 [166,266,271,272] d265 = true := by decide +kernel
private def d266 : List NodeSpec := [([(0,3,1),(1,2,6),(2,7,0)],[8,0,1,2,3,4,5],[(3,[0,2]),(0,[0,1,2]),(2,[]),(5,[]),(1,[0,1]),(4,[]),(26,[])]),([(0,3,1),(1,2,6),(2,7,0)],[8,0,1,2,7,3,4,5],[(31,[]),(4,[])]),([(0,3,1),(1,2,6),(1,3,1)],[0,2,7,8,4,5],[(31,[]),(0,[0,1,2]),(35,[]),(4,[])]),([(0,3,1),(1,2,6),(2,3,2)],[8,0,1,7,3,4,5],[(11,[]),(26,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q266 : ck264 [28,144,164,166,273,274,275,276,277,278] d266 = true := by decide +kernel
private def lv_0_0_7_34 : List NodeSpec := (d264 ++ (d265 ++ d266))

private theorem ok_0_0_7_34 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_34 := by
  have go {ids ds} (h : ck264 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q264) (levelOK_append (go q265) (go q266)))
private def ck267 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d267 : List NodeSpec := [([(0,3,1),(1,2,6),(1,4,0)],[0,1,2,7,3,4,8,5],[(5,[]),(12,[]),(31,[]),(34,[])]),([(0,3,1),(1,2,6),(1,4,2)],[0,1,7,3,8,5],[(35,[]),(0,[0,1,2]),(24,[]),(1,[0,1,2]),(4,[2]),(3,[0])]),([(0,3,1),(1,2,6),(1,4,2)],[0,1,7,3,4,8,5],[(35,[]),(13,[]),(0,[0,1,2]),(1,[0,1,2])]),([(0,3,1),(1,2,6),(1,4,7)],[0,1,2,7,3,4,8,5],[(34,[]),(35,[]),(5,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q267 : ck267 [29,30,145,165,168,169,241,271,273,274,275,277,279,280,281,282] d267 = true := by decide +kernel
private def d268 : List NodeSpec := [([(0,3,1),(1,2,6),(3,4,7)],[8,0,1,2,7,3,4,5],[(34,[]),(5,[]),(35,[])]),([(0,3,1),(1,2,6),(1,5,2)],[0,1,7,3,4,8],[(34,[]),(11,[]),(1,[0,1,2]),(3,[0]),(24,[])]),([(0,3,1),(1,2,6),(2,7,0)],[8,0,6,1,2,3,4,5],[(31,[])]),([(0,3,1),(1,2,6),(1,3,1)],[0,6,2,7,8,4,5],[(31,[]),(20,[]),(13,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q268 : ck267 [31,242,257,272,276,278,282,283,284] d268 = true := by decide +kernel
private def d269 : List NodeSpec := [([(0,3,1),(1,2,6),(1,4,2)],[0,6,1,7,3,8,5],[(4,[2]),(35,[]),(0,[0,1,2]),(24,[]),(1,[0,1,2])]),([(0,3,1),(1,3,1),(2,7,6)],[8,0,2,7,4,5],[(11,[]),(0,[0,1,2]),(18,[]),(27,[])]),([(0,3,1),(1,3,1),(2,7,6)],[8,0,6,2,4,5],[(20,[]),(13,[]),(31,[]),(0,[0,1,2])]),([(0,3,1),(1,3,1),(2,7,6)],[8,0,6,2,7,4,5],[(11,[]),(20,[]),(13,[]),(27,[]),(0,[0,1,2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q269 : ck267 [32,170,267,281,283,284,285,286,287,288,289,290] d269 = true := by decide +kernel
private def lv_0_0_7_35 : List NodeSpec := (d267 ++ (d268 ++ d269))

private theorem ok_0_0_7_35 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_35 := by
  have go {ids ds} (h : ck267 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q267) (levelOK_append (go q268) (go q269)))
private def ck270 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d270 : List NodeSpec := [([(0,3,1),(1,3,1),(1,4,0)],[0,6,2,7,4,8,5],[(31,[]),(13,[]),(0,[0,1,2])]),([(0,3,1),(1,3,1),(1,4,2)],[0,6,2,7,8,5],[(31,[]),(35,[]),(0,[0,1,2])]),([(0,3,1),(1,3,1),(2,4,2)],[8,0,6,2,7,5],[(11,[]),(13,[]),(0,[0,1,2])]),([(0,3,1),(1,3,1),(1,5,2)],[0,6,2,7,4,8],[(31,[]),(20,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q270 : ck270 [277,278,284,290,291] d270 = true := by decide +kernel
private def d271 : List NodeSpec := [([(0,3,1),(1,3,1),(3,5,7)],[8,0,6,2,7,4],[(11,[]),(20,[]),(18,[])]),([(0,3,1),(1,3,1),(2,7,0)],[8,0,6,2,3,4,5],[(11,[]),(1,[0,1]),(0,[0,1,2]),(6,[]),(18,[])]),([(0,3,1),(1,3,1),(2,7,6)],[8,0,2,3,4,5],[(11,[]),(0,[0,1,2]),(18,[]),(1,[0,1,2])]),([(0,3,1),(1,3,1),(2,7,6)],[8,0,6,2,3,4,5],[(11,[]),(26,[]),(0,[0,1,2]),(13,[]),(1,[0,1,2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q271 : ck270 [268,269,270,285,292,293,294] d271 = true := by decide +kernel
private def d272 : List NodeSpec := [([(0,3,1),(1,3,1),(2,7,6)],[8,0,1,2,4,5],[(24,[]),(0,[0,1,2]),(13,[]),(27,[])]),([(0,3,1),(1,3,1),(2,7,6)],[8,0,1,2,3,4,5],[(11,[]),(13,[]),(27,[]),(0,[0,1,2])]),([(0,3,1),(1,3,2),(2,7,0)],[8,0,6,1,2,3,4,5],[(1,[1]),(1,[0]),(7,[]),(24,[])]),([(0,3,1),(1,4,0),(1,4,2)],[0,6,1,2,3,7,8,5],[(31,[]),(5,[]),(12,[]),(10,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q272 : ck270 [259,261,279,295] d272 = true := by decide +kernel
private def lv_0_0_7_36 : List NodeSpec := (d270 ++ (d271 ++ d272))

private theorem ok_0_0_7_36 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_36 := by
  have go {ids ds} (h : ck270 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q270) (levelOK_append (go q271) (go q272)))
private def ck273 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d273 : List NodeSpec := [([(0,3,1),(1,4,0),(2,7,2)],[8,0,6,1,2,3,4,5],[(12,[]),(31,[]),(4,[]),(5,[])]),([(0,3,1),(3,4,6),(1,2,7)],[0,1,2,8,3,4,5],[(3,[0,1]),(17,[]),(20,[]),(26,[])]),([(0,3,1),(3,4,6),(2,3,7)],[0,1,2,8,3,4,5],[(35,[]),(17,[]),(0,[0,1,2])]),([(0,3,1),(1,4,2),(1,7,0)],[0,6,1,2,3,7,8,5],[(31,[]),(4,[1]),(5,[]),(10,[]),(11,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q273 : ck273 [262,263,280,295,296,297,298] d273 = true := by decide +kernel
private def d274 : List NodeSpec := [([(0,3,1),(1,4,2),(1,7,6)],[0,6,1,2,3,7,8,5],[(35,[]),(13,[])]),([(0,3,1),(1,4,3),(2,7,0)],[8,0,6,1,2,3,4,5],[(1,[1]),(1,[0]),(7,[])]),([(0,3,1),(1,4,3),(2,7,6)],[8,0,1,2,3,4,5],[(11,[]),(0,[0,1,2]),(13,[]),(1,[])]),([(1,3,1),(1,3,2),(0,7,1)],[0,8,2,6,4,5],[(13,[]),(3,[0,2]),(7,[]),(0,[0,1,2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q274 : ck273 [35,36,264,265,281,299] d274 = true := by decide +kernel
private def d275 : List NodeSpec := [([(1,3,1),(2,6,2),(1,4,2)],[7,0,1,3,8,5],[(31,[]),(0,[0,1,2]),(11,[]),(2,[])]),([(1,3,1),(2,6,2),(3,5,7)],[8,0,1,2,3,4],[(11,[]),(14,[]),(20,[])]),([(1,3,1),(3,4,1),(2,6,7)],[0,1,2,3,8,4,5],[(24,[]),(20,[]),(27,[])]),([(1,3,1),(1,4,2),(3,5,6)],[8,0,1,2,3,7],[(31,[]),(11,[]),(8,[1]),(16,[1]),(2,[0,2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q275 : ck273 [] d275 = true := by decide +kernel
private def lv_0_0_7_37 : List NodeSpec := (d273 ++ (d274 ++ d275))

private theorem ok_0_0_7_37 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_37 := by
  have go {ids ds} (h : ck273 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q273) (levelOK_append (go q274) (go q275)))
private def ck276 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d276 : List NodeSpec := [([(1,3,1),(2,4,2),(3,5,6)],[8,7,0,1,2,3],[(11,[]),(14,[]),(1,[0,1,2]),(6,[1]),(13,[2])]),([(1,3,1),(1,4,6),(3,5,7)],[8,0,1,2,3,4],[(11,[]),(2,[0,2]),(6,[]),(8,[])]),([(1,3,1),(1,5,2),(0,7,6)],[0,1,2,3,8,4],[(31,[]),(11,[]),(19,[])]),([(1,3,1),(3,5,6),(1,2,7)],[0,1,2,8,3,4],[(31,[]),(16,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q276 : ck276 [291] d276 = true := by decide +kernel
private def d277 : List NodeSpec := [([(2,3,1),(1,0,6),(1,4,3)],[0,7,1,2,3,4,8,5],[(1,[0]),(1,[2]),(0,[0,1]),(13,[])]),([(2,3,1),(1,0,6),(3,4,3)],[8,0,7,1,2,3,4,5],[(12,[]),(26,[])]),([(2,3,1),(1,1,6),(3,5,7)],[8,0,1,2,3,4],[(11,[]),(14,[]),(6,[])]),([(2,3,1),(1,2,6),(2,3,2)],[8,0,1,7,3,4,5],[(31,[]),(11,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q277 : ck276 [231,300,301] d277 = true := by decide +kernel
private def d278 : List NodeSpec := [([(2,3,1),(2,3,6),(1,7,0)],[0,1,8,2,3,4,5],[(31,[]),(13,[]),(0,[0,1,2]),(26,[])]),([(2,3,1),(2,3,6),(1,2,7)],[0,1,2,8,3,4,5],[(31,[]),(20,[]),(13,[]),(11,[])]),([(2,3,1),(2,3,6),(1,4,2)],[0,7,1,2,3,8,5],[(31,[]),(4,[2]),(0,[0,1,2]),(2,[0,1]),(5,[]),(10,[])]),([(2,3,1),(3,3,1),(1,6,7)],[6,8,0,2,3,4,5],[(27,[]),(11,[]),(0,[0,1,2]),(18,[]),(4,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q278 : ck276 [302] d278 = true := by decide +kernel
private def lv_0_0_7_38 : List NodeSpec := (d276 ++ (d277 ++ d278))

private theorem ok_0_0_7_38 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_38 := by
  have go {ids ds} (h : ck276 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q276) (levelOK_append (go q277) (go q278)))
private def ck279 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d279 : List NodeSpec := [([(2,3,1),(3,3,1),(1,0,7)],[6,0,8,2,3,4,5],[(11,[]),(27,[]),(0,[0,1,2]),(2,[0,1,2])]),([(2,3,1),(1,3,2),(2,7,6)],[0,1,8,2,7,4,5],[(31,[]),(18,[]),(0,[0,1,2])]),([(2,3,1),(1,3,2),(2,7,2)],[8,6,0,1,7,4,5],[(31,[]),(11,[])]),([(2,3,1),(1,3,2),(2,7,6)],[0,1,8,2,3,4,5],[(31,[]),(18,[]),(0,[0,1,2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q279 : ck279 [] d279 = true := by decide +kernel
private def d280 : List NodeSpec := [([(2,3,1),(1,4,6),(2,7,2)],[8,0,1,2,3,4,5],[(17,[]),(2,[0,2]),(0,[0,1,2]),(3,[0,1]),(6,[]),(26,[])]),([(2,3,1),(1,4,6),(1,5,2)],[0,1,2,3,4,7,8],[(17,[2]),(2,[0,2]),(3,[0,1]),(0,[0,1]),(8,[]),(19,[])]),([(2,3,1),(1,4,3),(2,7,0)],[6,8,0,1,2,3,4,5],[(1,[1]),(1,[0]),(13,[])]),([(2,3,1),(1,4,3),(3,5,7)],[8,6,0,1,2,3,4],[(11,[]),(20,[]),(2,[0,2]),(1,[1,2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q280 : ck279 [37,38,56,300,301] d280 = true := by decide +kernel
private def d281 : List NodeSpec := [([(3,3,1),(1,0,6),(1,2,7)],[0,7,1,2,8,3,4,5],[(11,[]),(25,[0])]),([(3,3,1),(1,0,6),(3,2,7)],[8,0,1,2,3,4,5],[(11,[]),(0,[0,1,2]),(1,[0,2]),(2,[]),(5,[]),(4,[])]),([(3,3,1),(1,0,6),(3,2,7)],[8,0,7,1,2,3,4,5],[(3,[0,1]),(4,[])]),([(3,3,1),(1,0,6),(1,4,7)],[0,7,1,2,3,4,8,5],[(13,[]),(5,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q281 : ck279 [172,174] d281 = true := by decide +kernel
private def lv_0_0_7_39 : List NodeSpec := (d279 ++ (d280 ++ d281))

private theorem ok_0_0_7_39 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_39 := by
  have go {ids ds} (h : ck279 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q279) (levelOK_append (go q280) (go q281)))
private def ck282 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d282 : List NodeSpec := [([(3,3,1),(1,0,6),(3,4,7)],[8,0,7,1,2,3,4,5],[(2,[0,1]),(5,[])]),([(3,3,1),(1,0,6),(1,4,2)],[0,7,1,2,3,8,5],[(35,[]),(0,[0,1,2]),(1,[0,2]),(4,[2])]),([(3,3,1),(1,0,6),(2,4,2)],[8,0,7,1,2,3,5],[(11,[]),(2,[0,1]),(0,[0,1,2]),(1,[0,2]),(4,[2])]),([(3,3,1),(1,0,6),(1,5,2)],[0,7,1,2,3,4,8],[(11,[]),(20,[]),(2,[0,1,2]),(5,[2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q282 : ck282 [173] d282 = true := by decide +kernel
private def d283 : List NodeSpec := [([(3,3,1),(3,4,6),(1,0,7)],[8,1,2,3,4,5],[(11,[]),(0,[0,1,2]),(2,[0,2]),(4,[])]),([(3,3,1),(3,4,6),(1,5,7)],[0,1,2,3,4,8],[(11,[]),(2,[0,2]),(4,[]),(8,[])]),([(1,3,2),(2,6,0),(0,1,7)],[8,7,0,1,2,3,4,5],[(31,[]),(4,[])]),([(1,3,2),(2,6,0),(2,1,7)],[7,8,0,1,2,3,4,5],[(31,[]),(4,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q283 : ck282 [303] d283 = true := by decide +kernel
private def d284 : List NodeSpec := [([(1,3,2),(2,6,0),(1,4,7)],[7,0,1,2,3,4,8,5],[(2,[0,1]),(5,[])]),([(1,3,2),(2,6,0),(3,4,7)],[8,7,0,1,2,3,4,5],[(18,[]),(5,[])]),([(1,3,2),(2,6,0),(3,4,1)],[8,7,0,1,2,3,4,5],[(5,[]),(1,[0,2]),(2,[])]),([(1,3,2),(2,6,0),(2,1,7)],[8,0,1,2,3,6,4,5],[(31,[]),(4,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q284 : ck282 [226,304,305,306] d284 = true := by decide +kernel
private def lv_0_0_7_40 : List NodeSpec := (d282 ++ (d283 ++ d284))

private theorem ok_0_0_7_40 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_40 := by
  have go {ids ds} (h : ck282 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q282) (levelOK_append (go q283) (go q284)))
private def ck285 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d285 : List NodeSpec := [([(1,3,2),(2,6,0),(0,6,1)],[7,0,8,1,2,3,4,5],[(1,[0,2]),(7,[]),(24,[]),(4,[])]),([(1,3,2),(0,6,1),(1,7,0)],[0,1,8,2,3,4,5],[(13,[]),(3,[1,2]),(0,[0,1,2]),(6,[]),(7,[]),(1,[0,1])]),([(1,3,2),(0,6,1),(1,7,0)],[0,1,8,2,3,6,4,5],[(1,[0,1]),(6,[0]),(7,[])]),([(1,3,2),(1,4,0),(0,7,1)],[0,8,1,2,3,6,4,5],[(4,[]),(7,[]),(3,[]),(27,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q285 : ck285 [238,244,303,307,308,309] d285 = true := by decide +kernel
private def d286 : List NodeSpec := [([(1,3,2),(3,4,1),(1,0,7)],[0,8,1,2,3,6,4,5],[(7,[]),(1,[0,1]),(17,[])]),([(1,3,2),(3,4,1),(2,3,7)],[0,1,2,8,6,4,5],[(18,[]),(3,[1,2]),(4,[])]),([(1,3,2),(3,4,1),(2,3,7)],[7,0,1,2,8,6,4,5],[(4,[]),(7,[])]),([(1,3,2),(3,4,1),(2,6,7)],[0,1,2,3,8,4,5],[(3,[1,2]),(2,[0,2]),(0,[0,1,2]),(1,[]),(4,[]),(6,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q286 : ck285 [64,65,148,149,247,248,305,306,310,311,312] d286 = true := by decide +kernel
private def d287 : List NodeSpec := [([(1,3,2),(3,4,1),(2,6,7)],[7,0,1,2,3,8,4,5],[(2,[0,2]),(7,[])]),([(1,3,2),(1,4,6),(2,7,0)],[8,1,2,3,4,5],[(17,[]),(3,[1,2]),(0,[0,1,2]),(7,[])]),([(1,3,2),(1,4,6),(0,7,1)],[0,8,2,3,4,5],[(3,[1,2]),(0,[0,1,2]),(4,[]),(2,[0,2]),(7,[])]),([(1,3,2),(1,4,6),(2,7,1)],[8,0,2,3,4,5],[(3,[1,2]),(0,[0,1,2]),(6,[]),(2,[0,2]),(7,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q287 : ck285 [] d287 = true := by decide +kernel
private def lv_0_0_7_41 : List NodeSpec := (d285 ++ (d286 ++ d287))

private theorem ok_0_0_7_41 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_41 := by
  have go {ids ds} (h : ck285 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q285) (levelOK_append (go q286) (go q287)))
private def ck288 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d288 : List NodeSpec := [([(1,3,2),(1,4,6),(3,5,7)],[8,0,1,2,3,4],[(17,[]),(3,[1,2]),(7,[]),(8,[])]),([(2,3,2),(3,0,6),(2,1,7)],[6,0,8,1,2,3,4,5],[(26,[]),(6,[0]),(1,[0,2])]),([(2,3,2),(0,1,6),(1,0,7)],[6,0,8,1,2,3,4,5],[(26,[]),(1,[0])]),([(2,3,2),(1,1,6),(3,5,7)],[8,0,1,2,3,4],[(11,[]),(14,[]),(6,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q288 : ck288 [] d288 = true := by decide +kernel
private def d289 : List NodeSpec := [([(2,3,2),(2,1,6),(1,7,0)],[0,1,8,2,3,4,5],[(11,[]),(0,[0,1,2]),(4,[]),(2,[0,1,2]),(5,[])]),([(2,3,2),(3,1,6),(2,3,7)],[6,0,1,2,8,4,5],[(31,[]),(26,[]),(11,[])]),([(2,3,2),(1,4,6),(3,5,7)],[8,0,1,2,3,4],[(11,[]),(17,[]),(8,[])]),([(2,3,2),(1,4,0),(0,7,1)],[6,0,8,1,2,3,4,5],[(11,[]),(26,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q289 : ck288 [] d289 = true := by decide +kernel
private def d290 : List NodeSpec := [([(2,3,2),(3,4,1),(2,6,7)],[8,0,1,2,3,4,5],[(26,[]),(3,[1,2]),(2,[0,2]),(0,[0,1,2]),(1,[]),(6,[])]),([(2,3,2),(3,4,1),(2,6,7)],[7,8,0,1,2,3,4,5],[(11,[])]),([(2,3,2),(3,4,1),(1,0,7)],[6,0,8,1,2,3,4,5],[(11,[]),(26,[]),(1,[0,1])]),([(2,3,2),(3,4,1),(2,3,7)],[6,0,1,2,8,4,5],[(3,[1,2]),(26,[]),(2,[0,2]),(4,[]),(6,[0])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q290 : ck288 [72,73,150,151,177,250,313,314] d290 = true := by decide +kernel
private def lv_0_0_7_42 : List NodeSpec := (d288 ++ (d289 ++ d290))

private theorem ok_0_0_7_42 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_42 := by
  have go {ids ds} (h : ck288 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q288) (levelOK_append (go q289) (go q290)))
private def ck291 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d291 : List NodeSpec := [([(2,3,2),(3,4,1),(2,3,7)],[7,6,0,1,2,8,4,5],[(4,[]),(7,[])]),([(1,4,0),(1,4,2),(0,6,1)],[0,8,1,2,3,7,5],[(1,[1,2]),(4,[1]),(3,[0,2]),(0,[0,1,2]),(5,[]),(7,[1])]),([(1,4,0),(1,4,2),(2,6,2)],[8,0,1,3,7,5],[(12,[]),(5,[]),(0,[0,1,2]),(31,[]),(35,[])]),([(1,4,0),(1,4,2),(0,6,3)],[0,1,2,8,3,7,5],[(1,[1,2]),(3,[0,2]),(5,[]),(0,[0,1,2]),(4,[1]),(6,[1])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q291 : ck291 [295,315] d291 = true := by decide +kernel
private def d292 : List NodeSpec := [([(1,4,0),(0,6,1),(1,2,7)],[0,1,2,8,3,4,5],[(3,[0,1]),(1,[1,2]),(0,[0,1,2]),(2,[1,2]),(4,[]),(7,[]),(26,[])]),([(1,4,0),(0,6,1),(2,3,7)],[8,0,1,2,3,4,5],[(20,[]),(26,[]),(1,[1,2]),(2,[1,2]),(0,[0,1,2]),(3,[])]),([(1,4,0),(2,6,1),(2,3,7)],[0,8,1,2,3,4,5],[(24,[]),(1,[1,2]),(0,[0,1,2]),(2,[1,2])]),([(1,4,0),(2,6,2),(2,3,7)],[0,1,8,2,3,4,5],[(3,[0,2]),(26,[]),(0,[0,1,2]),(12,[]),(4,[]),(6,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q292 : ck291 [307,308,315,316] d292 = true := by decide +kernel
private def d293 : List NodeSpec := [([(1,4,0),(0,6,3),(1,7,2)],[0,1,2,3,8,4,5],[(12,[]),(3,[0,1]),(0,[0,1,2]),(4,[]),(6,[]),(26,[])]),([(1,4,1),(1,4,2),(2,6,2)],[8,0,1,3,7,5],[(17,[]),(13,[]),(0,[0,1,2])]),([(1,4,1),(1,4,2),(0,6,3)],[0,1,2,8,3,7,5],[(13,[]),(17,[]),(3,[0,2]),(0,[0,1,2])]),([(1,4,1),(0,6,3),(1,7,0)],[0,1,2,3,8,4,5],[(31,[]),(13,[]),(0,[0,1,2]),(26,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q293 : ck291 [202] d293 = true := by decide +kernel
private def lv_0_0_7_43 : List NodeSpec := (d291 ++ (d292 ++ d293))

private theorem ok_0_0_7_43 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_43 := by
  have go {ids ds} (h : ck291 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q291) (levelOK_append (go q292) (go q293)))
private def ck294 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d294 : List NodeSpec := [([(1,4,1),(0,6,3),(1,7,2)],[0,1,2,3,8,4,5],[(31,[]),(13,[]),(0,[0,1,2]),(26,[])]),([(1,4,1),(2,6,3),(1,0,7)],[0,8,1,2,3,4,5],[(11,[]),(2,[1,2]),(0,[0,1,2]),(4,[]),(6,[])]),([(3,4,1),(1,0,6),(1,5,2)],[0,7,1,2,3,4,8],[(17,[2]),(3,[0,1]),(14,[1]),(1,[0,2]),(0,[0,1]),(4,[2]),(7,[2]),(19,[])]),([(3,4,1),(1,2,6),(1,7,0)],[0,1,2,7,8,3,4,5],[(17,[]),(2,[1,2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q294 : ck294 [178,254,255] d294 = true := by decide +kernel
private def d295 : List NodeSpec := [([(3,4,1),(1,2,6),(2,7,0)],[8,0,1,2,3,4,5],[(3,[0,2]),(17,[]),(0,[0,1,2]),(7,[]),(26,[]),(4,[])]),([(3,4,1),(1,2,6),(2,7,0)],[8,0,1,2,7,3,4,5],[(17,[]),(2,[1,2])]),([(3,4,1),(1,2,6),(0,3,7)],[0,1,8,2,3,4,5],[(3,[0,2]),(26,[]),(0,[0,1,2]),(1,[]),(2,[1,2]),(4,[])]),([(3,4,1),(1,2,6),(0,3,7)],[0,1,8,2,7,3,4,5],[(35,[]),(5,[]),(26,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q295 : ck294 [78,153,178,317,318] d295 = true := by decide +kernel
private def d296 : List NodeSpec := [([(3,4,1),(1,2,6),(2,3,7)],[8,0,1,2,7,3,4,5],[(35,[]),(26,[])]),([(3,4,1),(1,2,6),(1,4,2)],[0,1,7,3,8,5],[(17,[]),(0,[0,1,2]),(35,[]),(2,[1]),(4,[2]),(24,[])]),([(3,4,1),(1,2,6),(2,3,6)],[0,1,2,7,8,3,4,5],[(3,[0,2]),(18,[]),(5,[]),(26,[])]),([(3,4,1),(1,2,6),(0,3,7)],[6,0,1,8,2,3,4,5],[(35,[]),(5,[]),(26,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q296 : ck294 [318,319,320] d296 = true := by decide +kernel
private def lv_0_0_7_44 : List NodeSpec := (d294 ++ (d295 ++ d296))

private theorem ok_0_0_7_44 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_44 := by
  have go {ids ds} (h : ck294 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q294) (levelOK_append (go q295) (go q296)))
private def ck297 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d297 : List NodeSpec := [([(3,4,1),(1,3,6),(2,7,0)],[8,0,1,2,3,4,5],[(11,[]),(2,[1,2]),(0,[0,1,2]),(4,[]),(6,[])]),([(3,4,1),(2,3,6),(1,7,0)],[0,1,2,3,8,4,5],[(17,[]),(0,[0,1,2]),(3,[]),(4,[]),(6,[]),(26,[]),(2,[1,2])]),([(3,4,1),(2,3,6),(1,7,0)],[0,1,2,7,3,8,4,5],[(1,[0,1]),(26,[])]),([(3,4,1),(2,3,6),(1,7,2)],[0,1,2,3,8,4,5],[(3,[0,1]),(0,[0,1,2]),(2,[1,2]),(4,[]),(1,[]),(6,[]),(26,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q297 : ck297 [79,80,83,154,179,180,204,310,314,321,322,323] d297 = true := by decide +kernel
private def d298 : List NodeSpec := [([(3,4,1),(2,3,6),(1,7,2)],[0,1,2,7,3,8,4,5],[(26,[]),(3,[0,1])]),([(3,4,1),(2,3,6),(1,4,2)],[0,1,2,7,3,8,5],[(17,[]),(3,[0,1]),(0,[0,1,2]),(4,[2]),(6,[2])]),([(3,4,1),(2,3,6),(1,5,2)],[0,1,2,7,3,4,8],[(20,[]),(3,[0,1]),(2,[1,2]),(1,[2])]),([(3,4,1),(2,3,6),(1,7,2)],[6,0,1,2,3,8,4,5],[(3,[0,1]),(7,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q298 : ck297 [82,254,319,322] d298 = true := by decide +kernel
private def d299 : List NodeSpec := [([(1,4,2),(1,6,0),(0,7,1)],[0,8,1,2,3,6,5],[(31,[]),(4,[0]),(0,[0,1,2]),(2,[1,2]),(7,[0])]),([(1,4,2),(1,6,0),(0,7,3)],[0,1,2,8,3,6,5],[(35,[]),(0,[0,1,2]),(1,[0,2]),(4,[0]),(6,[0]),(5,[])]),([(1,4,2),(0,6,1),(1,7,0)],[0,1,8,2,3,6,5],[(31,[]),(35,[]),(0,[0,1,2])]),([(1,4,2),(1,6,1),(0,7,3)],[0,1,2,8,3,6,5],[(17,[]),(3,[1,2]),(0,[0,1,2]),(6,[0]),(4,[0])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q299 : ck297 [181,298,324] d299 = true := by decide +kernel
private def lv_0_0_7_45 : List NodeSpec := (d297 ++ (d298 ++ d299))

private theorem ok_0_0_7_45 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_45 := by
  have go {ids ds} (h : ck297 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q297) (levelOK_append (go q298) (go q299)))
private def ck300 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d300 : List NodeSpec := [([(1,4,2),(2,6,1),(1,5,7)],[0,1,2,3,6,8],[(31,[]),(10,[]),(8,[0]),(21,[0])]),([(1,4,2),(3,6,1),(2,3,7)],[0,1,2,8,3,6,5],[(17,[]),(3,[1,2]),(0,[0,1,2]),(4,[0]),(6,[0])]),([(1,4,2),(0,6,3),(1,7,0)],[0,1,2,3,8,6,5],[(35,[]),(0,[0,1,2]),(1,[0,1]),(4,[0]),(6,[0])]),([(1,4,2),(0,6,3),(3,7,1)],[8,0,1,2,3,6,5],[(35,[]),(4,[0]),(0,[0,1,2]),(1,[0])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q300 : ck300 [107,108,182,183,325] d300 = true := by decide +kernel
private def d301 : List NodeSpec := [([(1,4,2),(0,6,3),(1,5,7)],[0,1,2,3,6,8],[(35,[]),(20,[0]),(22,[0])]),([(1,4,2),(1,6,3),(2,7,0)],[8,1,2,3,6,5],[(11,[]),(17,[]),(0,[0,1,2])]),([(1,4,2),(1,6,3),(0,7,1)],[0,8,2,3,6,5],[(11,[]),(17,[]),(0,[0,1,2])]),([(1,4,2),(1,6,3),(0,7,1)],[0,8,1,2,3,6,5],[(4,[0]),(11,[]),(17,[]),(0,[0,1,2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q301 : ck300 [111,184] d301 = true := by decide +kernel
private def d302 : List NodeSpec := [([(1,4,2),(1,6,3),(2,7,1)],[8,0,2,3,6,5],[(11,[]),(17,[]),(0,[0,1,2])]),([(1,4,2),(1,6,3),(2,7,2)],[8,0,1,3,6,5],[(17,[]),(11,[]),(0,[0,1,2])]),([(1,4,2),(1,6,3),(3,5,7)],[8,0,1,2,3,6],[(11,[]),(17,[]),(15,[])]),([(1,4,2),(2,6,3),(1,0,7)],[0,8,1,2,3,6,5],[(10,[]),(1,[0,1]),(0,[0,1,2]),(4,[0]),(6,[0]),(7,[0])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q302 : ck300 [] d302 = true := by decide +kernel
private def lv_0_0_7_46 : List NodeSpec := (d300 ++ (d301 ++ d302))

private theorem ok_0_0_7_46 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_46 := by
  have go {ids ds} (h : ck300 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q300) (levelOK_append (go q301) (go q302)))
private def ck303 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d303 : List NodeSpec := [([(1,4,2),(2,6,3),(2,1,7)],[0,8,1,2,3,6,5],[(10,[]),(4,[0]),(0,[0,1,2]),(7,[0]),(1,[0]),(6,[0])]),([(1,4,2),(3,6,3),(1,2,7)],[0,1,8,3,6,5],[(17,[]),(18,[]),(0,[0,1,2])]),([(1,4,2),(1,4,3),(0,7,1)],[0,8,1,2,3,6,5],[(17,[]),(3,[1,2]),(4,[0]),(0,[0,1,2]),(7,[0]),(6,[0])]),([(1,4,2),(1,4,3),(3,5,7)],[8,0,1,2,3,6],[(11,[]),(17,[]),(15,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q303 : ck303 [112,185,326,327] d303 = true := by decide +kernel
private def d304 : List NodeSpec := [([(1,4,2),(0,6,1),(1,7,0)],[0,1,8,2,3,4,5],[(31,[]),(35,[]),(0,[0,1,2])]),([(1,4,2),(2,6,1),(1,5,7)],[0,1,2,3,4,8],[(22,[]),(3,[1,2]),(2,[1,2]),(6,[])]),([(1,4,2),(0,6,3),(1,7,0)],[0,1,2,3,8,4,5],[(10,[]),(1,[0,1]),(0,[0,1,2]),(4,[]),(6,[]),(26,[])]),([(1,4,2),(0,6,3),(1,5,7)],[0,1,2,3,4,8],[(20,[]),(3,[1,2]),(2,[1,2]),(22,[]),(11,[2])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q304 : ck303 [115] d304 = true := by decide +kernel
private def d305 : List NodeSpec := [([(1,4,2),(2,6,3),(1,0,7)],[0,8,1,2,3,4,5],[(3,[1,2]),(7,[]),(2,[1,2]),(0,[0,1,2]),(4,[]),(6,[])]),([(1,4,3),(2,6,0),(1,5,2)],[7,0,1,2,3,4,8],[(30,[]),(17,[2]),(4,[2]),(6,[2])]),([(1,4,3),(0,6,1),(1,7,0)],[0,1,8,2,3,4,5],[(20,[]),(2,[1,2]),(0,[0,1,2]),(17,[]),(3,[]),(6,[]),(7,[])]),([(1,4,3),(0,6,1),(1,2,7)],[0,1,2,8,3,4,5],[(20,[]),(3,[0,1]),(2,[1,2]),(7,[2]),(1,[]),(6,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q305 : ck303 [125,126,186,187,188,328,329] d305 = true := by decide +kernel
private def lv_0_0_7_47 : List NodeSpec := (d303 ++ (d304 ++ d305))

private theorem ok_0_0_7_47 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_47 := by
  have go {ids ds} (h : ck303 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q303) (levelOK_append (go q304) (go q305)))
private def ck306 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d306 : List NodeSpec := [([(1,4,3),(2,6,1),(3,5,6)],[8,7,0,1,2,3,4],[(11,[]),(15,[]),(17,[])]),([(1,4,3),(2,6,2),(3,5,7)],[8,0,1,2,3,4],[(11,[]),(20,[]),(2,[1,2])]),([(1,4,3),(1,5,2),(0,7,6)],[0,1,2,3,4,8],[(29,[]),(2,[1,2]),(11,[])]),([(1,4,3),(3,5,6),(1,2,7)],[0,1,2,8,3,4],[(32,[]),(11,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q306 : ck306 [] d306 = true := by decide +kernel
private def d307 : List NodeSpec := [([(3,4,3),(1,1,6),(3,5,7)],[8,0,1,2,3,4],[(24,[]),(18,[]),(8,[])]),([(3,4,3),(2,1,6),(1,7,0)],[0,1,8,2,3,4,5],[(35,[]),(20,[]),(17,[])]),([(3,4,3),(1,2,6),(2,7,0)],[8,0,1,2,3,4,5],[(3,[0,2]),(17,[]),(0,[0,1,2]),(4,[]),(6,[]),(18,[])]),([(1,5,2),(1,6,0),(0,6,3)],[0,1,2,8,3,4,7],[(19,[]),(20,[]),(14,[]),(1,[0]),(7,[0])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q307 : ck306 [330] d307 = true := by decide +kernel
private def d308 : List NodeSpec := [([(1,5,2),(1,6,0),(2,7,2)],[8,0,1,3,4,6],[(20,[]),(23,[]),(14,[])]),([(1,5,2),(1,6,0),(0,7,3)],[0,1,2,8,3,4,6],[(20,[]),(3,[1,2]),(1,[0,2]),(2,[0,1,2]),(5,[0])]),([(1,5,2),(0,6,1),(1,7,0)],[1,8,2,3,4,6],[(30,[]),(34,[])]),([(1,5,2),(0,6,1),(1,7,0)],[0,1,8,2,3,4,6],[(30,[]),(33,[]),(20,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q308 : ck306 [] d308 = true := by decide +kernel
private def lv_0_0_7_48 : List NodeSpec := (d306 ++ (d307 ++ d308))

private theorem ok_0_0_7_48 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_48 := by
  have go {ids ds} (h : ck306 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q306) (levelOK_append (go q307) (go q308)))
private def ck309 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_6) 7
private def d309 : List NodeSpec := [([(1,5,2),(1,6,1),(2,7,2)],[8,0,1,3,4,6],[(22,[]),(24,[]),(14,[])]),([(1,5,2),(1,6,1),(0,7,3)],[0,1,2,8,4,6],[(22,[]),(3,[1,2]),(20,[]),(14,[])]),([(1,5,2),(1,6,1),(0,7,3)],[0,1,2,8,3,4,6],[(22,[]),(3,[1,2]),(20,[]),(14,[])]),([(1,5,2),(1,6,1),(2,7,3)],[8,0,1,2,4,6],[(11,[]),(14,[]),(20,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q309 : ck309 [] d309 = true := by decide +kernel
private def d310 : List NodeSpec := [([(1,5,2),(2,6,1),(3,6,1)],[8,7,0,2,3,4],[(19,[]),(14,[]),(22,[])]),([(1,5,2),(3,6,1),(1,2,7)],[0,1,8,3,4,6],[(22,[]),(21,[]),(14,[])]),([(1,5,2),(0,6,3),(1,7,0)],[0,1,2,3,8,4,6],[(29,[]),(30,[]),(2,[0]),(5,[0])]),([(1,5,2),(0,6,3),(1,4,7)],[0,1,2,3,8,6],[(29,[]),(30,[]),(17,[0]),(2,[0,1])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q310 : ck309 [330] d310 = true := by decide +kernel
private def d311 : List NodeSpec := [([(1,5,2),(0,6,3),(1,4,7)],[0,1,2,3,4,8,6],[(17,[0]),(2,[0,1]),(19,[]),(14,[]),(4,[0]),(6,[0])]),([(1,5,2),(1,6,3),(0,7,1)],[0,8,2,3,4,6],[(14,[]),(11,[]),(20,[])]),([(1,5,2),(1,6,3),(2,7,1)],[8,0,2,3,4,6],[(11,[]),(14,[]),(20,[])]),([(1,5,2),(1,6,3),(2,7,2)],[8,0,1,3,4,6],[(14,[]),(11,[]),(20,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q311 : ck309 [] d311 = true := by decide +kernel
private def lv_0_0_7_49 : List NodeSpec := (d309 ++ (d310 ++ d311))

private theorem ok_0_0_7_49 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_49 := by
  have go {ids ds} (h : ck309 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 7 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_6) h
  exact (levelOK_append (go q309) (levelOK_append (go q310) (go q311)))
private def lv_0_0_7_50 : List NodeSpec := [([(1, 5, 2), (2, 6, 3), (1, 0, 7)], [0, 8, 1, 2, 3, 4, 6], [(29, []), (11, []), (2, [0]), (5, [0]), (22, [])]), ([(1, 5, 2), (2, 6, 3), (3, 6, 3)], [8, 7, 0, 1, 2, 4], [(11, []), (14, []), (20, [])]), ([(1, 5, 2), (3, 6, 3), (1, 2, 7)], [0, 1, 8, 3, 4, 6], [(14, []), (16, []), (20, [])]), ([(1, 5, 2), (1, 6, 4), (0, 7, 3)], [0, 1, 2, 8, 3, 4, 6], [(30, []), (20, []), (22, []), (2, [0, 2])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_0_0_7_50 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7_50 :=
  levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK [] ok_0_0_6)
    (by decide +kernel : levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev [] lv_0_0_6) 7 lv_0_0_7_50 = true)
private def lv_0_0_7 : List NodeSpec := (((((lv_0_0_7_0 ++ (lv_0_0_7_1 ++ lv_0_0_7_2)) ++ (lv_0_0_7_3 ++ (lv_0_0_7_4 ++ lv_0_0_7_5))) ++ ((lv_0_0_7_6 ++ (lv_0_0_7_7 ++ lv_0_0_7_8)) ++ (lv_0_0_7_9 ++ (lv_0_0_7_10 ++ lv_0_0_7_11)))) ++ (((lv_0_0_7_12 ++ (lv_0_0_7_13 ++ lv_0_0_7_14)) ++ (lv_0_0_7_15 ++ (lv_0_0_7_16 ++ lv_0_0_7_17))) ++ ((lv_0_0_7_18 ++ (lv_0_0_7_19 ++ lv_0_0_7_20)) ++ ((lv_0_0_7_21 ++ lv_0_0_7_22) ++ (lv_0_0_7_23 ++ lv_0_0_7_24))))) ++ ((((lv_0_0_7_25 ++ (lv_0_0_7_26 ++ lv_0_0_7_27)) ++ (lv_0_0_7_28 ++ (lv_0_0_7_29 ++ lv_0_0_7_30))) ++ ((lv_0_0_7_31 ++ (lv_0_0_7_32 ++ lv_0_0_7_33)) ++ ((lv_0_0_7_34 ++ lv_0_0_7_35) ++ (lv_0_0_7_36 ++ lv_0_0_7_37)))) ++ (((lv_0_0_7_38 ++ (lv_0_0_7_39 ++ lv_0_0_7_40)) ++ (lv_0_0_7_41 ++ (lv_0_0_7_42 ++ lv_0_0_7_43))) ++ ((lv_0_0_7_44 ++ (lv_0_0_7_45 ++ lv_0_0_7_46)) ++ ((lv_0_0_7_47 ++ lv_0_0_7_48) ++ (lv_0_0_7_49 ++ lv_0_0_7_50))))))
private theorem ok_0_0_7 : LevelOK rd_0_0 (subGoal 0 0) 7 lv_0_0_7 := (levelOK_append (levelOK_append (levelOK_append (levelOK_append (levelOK_append ok_0_0_7_0 (levelOK_append ok_0_0_7_1 ok_0_0_7_2)) (levelOK_append ok_0_0_7_3 (levelOK_append ok_0_0_7_4 ok_0_0_7_5))) (levelOK_append (levelOK_append ok_0_0_7_6 (levelOK_append ok_0_0_7_7 ok_0_0_7_8)) (levelOK_append ok_0_0_7_9 (levelOK_append ok_0_0_7_10 ok_0_0_7_11)))) (levelOK_append (levelOK_append (levelOK_append ok_0_0_7_12 (levelOK_append ok_0_0_7_13 ok_0_0_7_14)) (levelOK_append ok_0_0_7_15 (levelOK_append ok_0_0_7_16 ok_0_0_7_17))) (levelOK_append (levelOK_append ok_0_0_7_18 (levelOK_append ok_0_0_7_19 ok_0_0_7_20)) (levelOK_append (levelOK_append ok_0_0_7_21 ok_0_0_7_22) (levelOK_append ok_0_0_7_23 ok_0_0_7_24))))) (levelOK_append (levelOK_append (levelOK_append (levelOK_append ok_0_0_7_25 (levelOK_append ok_0_0_7_26 ok_0_0_7_27)) (levelOK_append ok_0_0_7_28 (levelOK_append ok_0_0_7_29 ok_0_0_7_30))) (levelOK_append (levelOK_append ok_0_0_7_31 (levelOK_append ok_0_0_7_32 ok_0_0_7_33)) (levelOK_append (levelOK_append ok_0_0_7_34 ok_0_0_7_35) (levelOK_append ok_0_0_7_36 ok_0_0_7_37)))) (levelOK_append (levelOK_append (levelOK_append ok_0_0_7_38 (levelOK_append ok_0_0_7_39 ok_0_0_7_40)) (levelOK_append ok_0_0_7_41 (levelOK_append ok_0_0_7_42 ok_0_0_7_43))) (levelOK_append (levelOK_append ok_0_0_7_44 (levelOK_append ok_0_0_7_45 ok_0_0_7_46)) (levelOK_append (levelOK_append ok_0_0_7_47 ok_0_0_7_48) (levelOK_append ok_0_0_7_49 ok_0_0_7_50))))))
private def ck312 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_7) 8
private def d312 : List NodeSpec := [([(1,1,0),(2,1,0)],[7,1,6,2,3,4,5],[(24,[]),(20,[]),(13,[]),(0,[])]),([(1,1,0),(1,2,0)],[1,6,2,7,3,4,5],[(31,[]),(0,[0,1]),(2,[0,1]),(3,[]),(11,[])]),([(1,1,0),(1,2,1)],[0,6,2,7,3,4,5],[(6,[]),(3,[0]),(0,[0,1]),(1,[1]),(2,[0,1]),(11,[]),(17,[])]),([(1,1,0),(3,2,1)],[7,0,6,2,3,4,5],[(24,[]),(0,[0,1]),(1,[1]),(2,[0,1]),(11,[]),(17,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q312 : ck312 [0,1,2,3,4,5,6,7,8,9,10,11] d312 = true := by decide +kernel
private def d313 : List NodeSpec := [([(1,1,0),(1,2,6)],[0,1,2,7,3,4,5],[(6,[]),(3,[0]),(0,[0,1]),(1,[1]),(2,[0,1]),(2,[]),(5,[]),(7,[])]),([(1,1,0),(3,2,6)],[7,0,1,2,3,4,5],[(24,[]),(0,[0,1]),(1,[1]),(2,[0,1]),(2,[]),(5,[]),(7,[])]),([(1,1,0),(0,3,1)],[0,7,6,2,3,4,5],[(0,[0,1]),(1,[1]),(24,[]),(13,[]),(7,[]),(17,[])]),([(1,1,0),(0,3,1)],[0,7,1,6,2,3,4,5],[(24,[]),(20,[]),(13,[]),(1,[1]),(0,[1]),(7,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q313 : ck312 [0,9,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44] d313 = true := by decide +kernel
private def d314 : List NodeSpec := [([(1,1,0),(2,3,1)],[7,0,6,2,3,4,5],[(24,[]),(1,[1]),(0,[0,1]),(2,[0,1]),(7,[]),(17,[])]),([(1,1,0),(3,3,1)],[7,0,1,6,2,3,4,5],[(24,[]),(20,[]),(13,[]),(1,[1]),(0,[1])]),([(1,1,0),(0,3,6)],[0,1,7,2,3,4,5],[(1,[1]),(24,[]),(0,[0,1]),(2,[0,1]),(26,[]),(5,[]),(4,[])]),([(1,1,0),(0,3,6)],[0,1,7,6,2,3,4,5],[(24,[]),(1,[1]),(0,[0,1]),(2,[0,1]),(17,[]),(7,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q314 : ck312 [19,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66] d314 = true := by decide +kernel
private def lv_0_0_8_0 : List NodeSpec := (d312 ++ (d313 ++ d314))

private theorem ok_0_0_8_0 : LevelOK rd_0_0 (subGoal 0 0) 8 lv_0_0_8_0 := by
  have go {ids ds} (h : ck312 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 8 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_7) h
  exact (levelOK_append (go q312) (levelOK_append (go q313) (go q314)))
private def ck315 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_7) 8
private def d315 : List NodeSpec := [([(1,1,0),(1,3,6)],[0,1,2,3,7,4,5],[(11,[]),(0,[0,1]),(1,[1]),(6,[]),(2,[]),(3,[]),(5,[])]),([(1,1,0),(2,3,6)],[7,0,1,2,3,4,5],[(24,[]),(0,[0,1]),(1,[1]),(2,[0,1]),(2,[]),(5,[]),(26,[])]),([(1,1,0),(3,3,6)],[7,0,1,2,3,4,5],[(11,[]),(1,[1]),(0,[0,1]),(18,[]),(4,[]),(6,[])]),([(1,1,0),(3,3,6)],[7,0,1,6,2,3,4,5],[(24,[]),(0,[0,1]),(1,[1]),(2,[0,1]),(17,[]),(18,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q315 : ck315 [30,45,61,67,68,69,70,71,72,73,74,75,76,77] d315 = true := by decide +kernel
private def d316 : List NodeSpec := [([(1,1,0),(1,3,2)],[0,1,6,2,3,7,4,5],[(24,[]),(0,[0,1]),(1,[1]),(7,[]),(2,[0]),(2,[1]),(17,[])]),([(1,1,0),(2,3,2)],[7,0,1,6,2,3,4,5],[(24,[]),(0,[0,1]),(1,[1]),(11,[]),(2,[0]),(2,[1]),(17,[]),(26,[])]),([(1,1,0),(1,4,1)],[0,6,2,3,4,7,5],[(24,[]),(17,[]),(0,[0,1]),(1,[])]),([(1,1,0),(3,4,1)],[7,0,6,2,3,4,5],[(17,[]),(0,[0,1]),(24,[]),(2,[0]),(4,[]),(12,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q316 : ck315 [1,9,19,20,31,32,53,62,74,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96] d316 = true := by decide +kernel
private def d317 : List NodeSpec := [([(1,1,0),(3,4,1)],[7,0,1,6,2,3,4,5],[(24,[]),(20,[]),(17,[]),(0,[1]),(2,[]),(12,[]),(18,[])]),([(1,1,0),(0,4,6)],[0,1,7,6,2,3,5],[(24,[]),(0,[0,1]),(1,[1]),(2,[0]),(18,[])]),([(1,1,0),(1,4,6)],[0,1,2,3,4,7,5],[(24,[]),(0,[0,1]),(1,[1]),(2,[0]),(7,[])]),([(1,1,0),(3,4,6)],[7,0,1,2,3,5],[(1,[1]),(0,[0,1]),(24,[]),(5,[]),(2,[0])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q317 : ck315 [21,33,44,50,54,63,84,89,97,98,99,100,101,102,103,104,105,106,107] d317 = true := by decide +kernel
private def lv_0_0_8_1 : List NodeSpec := (d315 ++ (d316 ++ d317))

private theorem ok_0_0_8_1 : LevelOK rd_0_0 (subGoal 0 0) 8 lv_0_0_8_1 := by
  have go {ids ds} (h : ck315 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 8 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_7) h
  exact (levelOK_append (go q315) (levelOK_append (go q316) (go q317)))
private def ck318 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_7) 8
private def d318 : List NodeSpec := [([(1,1,0),(3,4,6)],[7,0,1,2,3,4,5],[(5,[]),(0,[0,1]),(1,[1]),(2,[0]),(3,[0,1]),(6,[]),(13,[]),(7,[])]),([(1,1,0),(3,4,6)],[7,0,1,6,2,3,5],[(24,[]),(0,[0,1]),(1,[1]),(2,[0]),(17,[])]),([(1,1,0),(3,4,6)],[7,0,1,6,2,3,4,5],[(24,[]),(17,[]),(0,[0,1]),(2,[0])]),([(1,1,0),(1,4,2)],[0,1,6,2,3,7,5],[(24,[]),(0,[0,1]),(1,[1]),(17,[]),(2,[0]),(10,[]),(11,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q318 : ck318 [2,21,34,35,36,56,64,65,75,76,85,90,108,109,110,111,112,113,114,115,116,117,118,119,120] d318 = true := by decide +kernel
private def d319 : List NodeSpec := [([(1,1,0),(1,4,2)],[0,1,6,2,3,4,7,5],[(17,[]),(24,[]),(0,[0,1]),(2,[0]),(10,[]),(11,[])]),([(1,1,0),(2,4,2)],[7,0,1,6,2,3,5],[(24,[]),(0,[0,1]),(2,[0]),(1,[1]),(11,[])]),([(1,1,0),(1,4,3)],[0,1,6,2,3,4,7,5],[(17,[]),(0,[0,1]),(2,[0]),(6,[]),(13,[]),(3,[1]),(7,[]),(1,[]),(3,[0])]),([(1,1,0),(3,4,3)],[7,0,1,6,2,3,4,5],[(17,[]),(0,[0,1]),(2,[0]),(18,[]),(13,[]),(3,[1]),(6,[]),(26,[]),(3,[0])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q319 : ck318 [3,4,5,7,8,10,11,16,17,22,23,37,38,39,40,46,47,57,58,59,72,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139] d319 = true := by decide +kernel
private def d320 : List NodeSpec := [([(1,1,0),(3,5,6)],[7,0,1,2,3,4],[(1,[1]),(14,[]),(21,[]),(20,[]),(3,[0,1])]),([(1,1,0),(3,5,6)],[7,0,1,6,2,3,4],[(24,[]),(1,[1]),(21,[]),(2,[0,1]),(0,[])]),([(1,1,0),(1,5,2)],[0,1,6,2,3,4,7],[(29,[]),(1,[1]),(2,[0,1]),(2,[1]),(11,[])]),([(2,1,0),(1,2,6)],[0,1,2,7,3,4,5],[(27,[]),(3,[0]),(0,[0,1]),(2,[0,1]),(5,[]),(7,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q320 : ck318 [24,41,42,60,66,77,86,91,95,96,100,107,110,113,116,120,123,125,131,132,133,137,138,139,140,141,142,143,144] d320 = true := by decide +kernel
private def lv_0_0_8_2 : List NodeSpec := (d318 ++ (d319 ++ d320))

private theorem ok_0_0_8_2 : LevelOK rd_0_0 (subGoal 0 0) 8 lv_0_0_8_2 := by
  have go {ids ds} (h : ck318 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 8 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_7) h
  exact (levelOK_append (go q318) (levelOK_append (go q319) (go q320)))
private def ck321 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_7) 8
private def d321 : List NodeSpec := [([(2,1,0),(3,2,6)],[7,0,1,2,3,4,5],[(31,[]),(13,[]),(0,[0,1])]),([(2,1,0),(1,2,1)],[6,0,2,7,3,4,5],[(27,[]),(3,[0]),(0,[0,1]),(2,[0,1]),(11,[]),(17,[])]),([(2,1,0),(3,2,1)],[7,6,0,2,3,4,5],[(31,[]),(13,[]),(0,[0,1]),(1,[])]),([(2,1,0),(0,3,6)],[7,0,1,2,3,4,5],[(13,[]),(0,[0,1]),(1,[1]),(3,[0,1]),(20,[]),(26,[]),(27,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q321 : ck321 [145,146,147,148,149,150] d321 = true := by decide +kernel
private def d322 : List NodeSpec := [([(2,1,0),(1,3,6)],[0,1,2,3,7,4,5],[(11,[]),(1,[1]),(0,[0,1]),(13,[]),(5,[]),(6,[])]),([(2,1,0),(2,3,6)],[0,7,1,2,3,4,5],[(31,[]),(0,[0,1]),(13,[]),(5,[]),(26,[])]),([(2,1,0),(3,3,6)],[7,0,1,2,3,4,5],[(11,[]),(0,[0,1]),(4,[]),(1,[1]),(2,[]),(5,[])]),([(2,1,0),(0,3,1)],[6,0,7,2,3,4,5],[(13,[]),(0,[0,1]),(1,[1]),(3,[0,1]),(7,[]),(20,[]),(27,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q322 : ck321 [151,152,153,154,155,156,157] d322 = true := by decide +kernel
private def d323 : List NodeSpec := [([(2,1,0),(2,3,1)],[7,6,0,2,3,4,5],[(31,[]),(0,[0,1]),(13,[]),(7,[]),(17,[])]),([(2,1,0),(1,3,2)],[6,0,1,2,3,7,4,5],[(31,[]),(0,[0,1]),(4,[]),(2,[0]),(7,[]),(17,[]),(2,[1])]),([(2,1,0),(2,3,2)],[7,6,0,1,2,3,4,5],[(31,[]),(0,[0,1]),(4,[]),(2,[0]),(11,[]),(17,[]),(26,[]),(2,[1])]),([(2,1,0),(1,4,6)],[0,1,2,3,4,7,5],[(31,[]),(13,[]),(0,[0,1])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q323 : ck321 [149,155,156,158,159,160,161,162,163,164,165,166,167] d323 = true := by decide +kernel
private def lv_0_0_8_3 : List NodeSpec := (d321 ++ (d322 ++ d323))

private theorem ok_0_0_8_3 : LevelOK rd_0_0 (subGoal 0 0) 8 lv_0_0_8_3 := by
  have go {ids ds} (h : ck321 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 8 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_7) h
  exact (levelOK_append (go q321) (levelOK_append (go q322) (go q323)))
private def ck324 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_7) 8
private def d324 : List NodeSpec := [([(2,1,0),(3,4,6)],[7,0,1,2,3,4,5],[(20,[]),(1,[1]),(2,[0]),(3,[0,1]),(0,[0,1]),(5,[]),(7,[])]),([(2,1,0),(1,4,1)],[6,0,2,3,4,7,5],[(31,[]),(13,[]),(0,[0,1])]),([(2,1,0),(3,4,1)],[7,6,0,2,3,4,5],[(17,[]),(20,[]),(2,[0]),(3,[0,1]),(0,[0,1])]),([(2,1,0),(1,4,2)],[6,0,1,2,3,7,5],[(31,[]),(0,[0,1]),(17,[]),(2,[0]),(10,[]),(11,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q324 : ck324 [150,157,163,164,166,167,168,169,170,171,172,173] d324 = true := by decide +kernel
private def d325 : List NodeSpec := [([(2,1,0),(1,4,2)],[6,0,1,2,3,4,7,5],[(31,[]),(13,[]),(17,[]),(0,[0,1]),(2,[])]),([(2,1,0),(2,4,2)],[7,6,0,1,2,3,5],[(31,[]),(13,[]),(0,[0,1])]),([(2,1,0),(1,4,3)],[6,0,1,2,3,4,7,5],[(34,[]),(17,[]),(0,[0,1]),(27,[]),(3,[0]),(3,[1]),(7,[])]),([(2,1,0),(3,4,3)],[7,6,0,1,2,3,4,5],[(34,[]),(17,[]),(18,[]),(0,[0,1]),(3,[0]),(3,[1]),(26,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q325 : ck324 [143,144,146,147,153,158,159,174,175,176,177] d325 = true := by decide +kernel
private def d326 : List NodeSpec := [([(2,1,0),(1,5,2)],[6,0,1,2,3,4,7],[(31,[]),(34,[])]),([(1,2,0),(0,6,1)],[0,7,1,2,3,4,5],[(13,[]),(3,[1]),(0,[0,1]),(1,[1]),(7,[])]),([(1,2,0),(2,6,1)],[7,0,1,2,3,4,5],[(6,[]),(3,[1]),(0,[0,1]),(1,[1]),(2,[0,1]),(5,[]),(7,[])]),([(1,2,0),(1,3,0)],[1,2,6,3,7,4,5],[(35,[]),(31,[]),(0,[0,1]),(1,[]),(3,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q326 : ck324 [178,179,180,181,182,183] d326 = true := by decide +kernel
private def lv_0_0_8_4 : List NodeSpec := (d324 ++ (d325 ++ d326))

private theorem ok_0_0_8_4 : LevelOK rd_0_0 (subGoal 0 0) 8 lv_0_0_8_4 := by
  have go {ids ds} (h : ck324 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 8 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_7) h
  exact (levelOK_append (go q324) (levelOK_append (go q325) (go q326)))
private def ck327 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_7) 8
private def d327 : List NodeSpec := [([(1,2,0),(0,3,1)],[0,7,1,2,6,3,4,5],[(31,[]),(0,[0,1]),(11,[]),(2,[0]),(4,[]),(17,[]),(2,[1]),(26,[])]),([(1,2,0),(3,3,1)],[7,0,1,2,6,3,4,5],[(31,[]),(35,[]),(0,[0,1])]),([(1,2,0),(0,3,6)],[0,1,2,7,3,4,5],[(31,[]),(0,[0,1]),(2,[0,1]),(11,[]),(3,[]),(5,[]),(26,[])]),([(1,2,0),(1,3,6)],[0,1,2,3,7,4,5],[(18,[]),(0,[0,1]),(3,[1]),(1,[1]),(4,[]),(6,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q327 : ck327 [0,184,185,186,187,188,189,190,191,192,193,194,195,196] d327 = true := by decide +kernel
private def d328 : List NodeSpec := [([(1,2,0),(1,3,6)],[0,1,2,6,3,7,4,5],[(31,[]),(35,[]),(0,[0,1])]),([(1,2,0),(2,3,6)],[7,0,1,2,3,4,5],[(31,[]),(0,[0,1]),(11,[]),(2,[0,1]),(3,[1]),(26,[]),(4,[]),(5,[]),(1,[1])]),([(1,2,0),(2,3,6)],[7,0,1,2,6,3,4,5],[(31,[]),(0,[0,1]),(11,[]),(2,[0,1]),(17,[])]),([(1,2,0),(3,3,6)],[7,0,1,2,3,4,5],[(31,[]),(18,[]),(0,[0,1])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q328 : ck327 [196,197,198,199,200,201,202,203,204,205,206,207,208,209] d328 = true := by decide +kernel
private def d329 : List NodeSpec := [([(1,2,0),(3,4,1)],[7,0,1,2,6,3,4,5],[(31,[]),(17,[]),(0,[0,1]),(35,[])]),([(1,2,0),(1,4,2)],[0,1,6,3,7,5],[(31,[]),(0,[0,1]),(1,[1]),(17,[]),(2,[0]),(3,[])]),([(1,2,0),(1,4,2)],[0,1,6,3,4,7,5],[(17,[]),(31,[]),(0,[0,1]),(2,[0]),(35,[])]),([(1,2,0),(1,4,6)],[0,1,2,3,4,7,5],[(5,[]),(31,[]),(0,[0,1]),(35,[]),(3,[1]),(1,[1]),(4,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q329 : ck327 [1,2,3,183,190,191,192,195,199,203,206,207,210,211,212,213,214,215,216,217] d329 = true := by decide +kernel
private def lv_0_0_8_5 : List NodeSpec := (d327 ++ (d328 ++ d329))

private theorem ok_0_0_8_5 : LevelOK rd_0_0 (subGoal 0 0) 8 lv_0_0_8_5 := by
  have go {ids ds} (h : ck327 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 8 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_7) h
  exact (levelOK_append (go q327) (levelOK_append (go q328) (go q329)))
private def ck330 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_7) 8
private def d330 : List NodeSpec := [([(1,2,0),(1,4,6)],[0,1,2,6,3,4,7,5],[(31,[]),(17,[]),(35,[]),(0,[0,1]),(12,[])]),([(1,2,0),(3,4,6)],[7,0,1,2,3,4,5],[(31,[]),(0,[0,1]),(2,[0]),(7,[])]),([(1,2,0),(1,4,3)],[0,1,2,6,3,4,7,5],[(11,[]),(17,[]),(0,[0,1]),(13,[]),(25,[]),(24,[])]),([(1,2,0),(3,4,3)],[7,0,1,2,6,3,4,5],[(35,[]),(17,[]),(0,[0,1]),(13,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q330 : ck330 [4,5,16,17,181,182,208,218,219,220,221,222,223] d330 = true := by decide +kernel
private def d331 : List NodeSpec := [([(1,2,1),(3,2,1)],[7,0,1,6,3,4,5],[(27,[]),(13,[]),(0,[0,1])]),([(1,2,1),(2,6,0)],[7,0,1,2,3,4,5],[(27,[]),(3,[1]),(0,[0,1]),(2,[0,1]),(5,[]),(7,[])]),([(1,2,1),(1,3,0)],[0,1,2,6,3,7,4,5],[(35,[]),(27,[]),(0,[0,1])]),([(1,2,1),(2,3,0)],[7,0,1,2,6,3,4,5],[(27,[]),(3,[1]),(0,[0,1]),(11,[]),(2,[0]),(26,[]),(2,[1]),(17,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q331 : ck330 [224,225,226,227,228,229,230,231,232,233,234,235] d331 = true := by decide +kernel
private def d332 : List NodeSpec := [([(1,2,1),(0,3,1)],[0,7,1,2,6,3,4,5],[(27,[]),(13,[]),(3,[1]),(0,[0,1]),(11,[])]),([(1,2,1),(1,3,1)],[0,2,6,3,7,4,5],[(11,[]),(27,[]),(0,[0,1]),(3,[])]),([(1,2,1),(3,3,1)],[7,0,2,6,3,4,5],[(35,[]),(0,[0,1]),(27,[]),(4,[])]),([(1,2,1),(3,3,1)],[7,0,1,2,6,3,4,5],[(13,[]),(27,[]),(11,[]),(0,[0,1])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q332 : ck330 [236,237,238,239] d332 = true := by decide +kernel
private def lv_0_0_8_6 : List NodeSpec := (d330 ++ (d331 ++ d332))

private theorem ok_0_0_8_6 : LevelOK rd_0_0 (subGoal 0 0) 8 lv_0_0_8_6 := by
  have go {ids ds} (h : ck330 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 8 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_7) h
  exact (levelOK_append (go q330) (levelOK_append (go q331) (go q332)))
private def ck333 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_7) 8
private def d333 : List NodeSpec := [([(1,2,1),(0,3,6)],[0,1,2,7,3,4,5],[(3,[1]),(27,[]),(0,[0,1]),(11,[]),(2,[0,1]),(26,[]),(5,[])]),([(1,2,1),(0,3,6)],[0,1,2,7,6,3,4,5],[(27,[]),(3,[1]),(0,[0,1]),(11,[]),(2,[0,1])]),([(1,2,1),(1,3,6)],[0,1,2,3,7,4,5],[(18,[]),(27,[]),(0,[0,1]),(3,[1])]),([(1,2,1),(2,3,6)],[7,0,1,2,3,4,5],[(27,[]),(3,[1]),(0,[0,1]),(2,[0,1]),(11,[]),(5,[]),(26,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q333 : ck333 [6,145,224,236,240,241,242,243,244,245,246,247,248,249,250,251,252,253] d333 = true := by decide +kernel
private def d334 : List NodeSpec := [([(1,2,1),(3,3,6)],[7,0,1,2,3,4,5],[(18,[]),(3,[1]),(0,[0,1]),(27,[]),(4,[])]),([(1,2,1),(3,3,6)],[7,0,1,2,6,3,4,5],[(35,[]),(27,[]),(0,[0,1])]),([(1,2,1),(1,4,0)],[0,1,2,6,3,4,7,5],[(27,[]),(3,[1]),(35,[]),(0,[0,1]),(5,[]),(12,[])]),([(1,2,1),(3,4,1)],[7,0,1,2,6,3,4,5],[(27,[]),(4,[]),(3,[1]),(0,[0,1]),(10,[]),(11,[]),(18,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q334 : ck333 [233,242,243,253,254,255,256] d334 = true := by decide +kernel
private def d335 : List NodeSpec := [([(1,2,1),(1,4,6)],[0,1,2,3,4,7,5],[(17,[]),(0,[0,1]),(3,[1]),(6,[]),(7,[])]),([(1,2,1),(3,4,6)],[7,0,1,2,3,4,5],[(17,[]),(3,[1]),(0,[0,1]),(6,[]),(13,[]),(7,[])]),([(1,2,1),(3,4,6)],[7,0,1,2,6,3,4,5],[(27,[]),(3,[1]),(35,[]),(0,[0,1])]),([(1,2,1),(1,4,3)],[0,1,2,6,3,4,7,5],[(11,[]),(0,[0,1]),(2,[0]),(6,[]),(13,[]),(1,[1]),(1,[0])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q335 : ck333 [7,16,146,225,234,245,248,249,250,257,258,259,260,261,262,263] d335 = true := by decide +kernel
private def lv_0_0_8_7 : List NodeSpec := (d333 ++ (d334 ++ d335))

private theorem ok_0_0_8_7 : LevelOK rd_0_0 (subGoal 0 0) 8 lv_0_0_8_7 := by
  have go {ids ds} (h : ck333 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 8 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_7) h
  exact (levelOK_append (go q333) (levelOK_append (go q334) (go q335)))
private def ck336 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_7) 8
private def d336 : List NodeSpec := [([(1,2,1),(3,4,3)],[7,0,1,2,6,3,4,5],[(35,[]),(0,[0,1]),(6,[]),(13,[]),(1,[1]),(1,[0]),(5,[])]),([(3,2,1),(1,0,6)],[0,7,1,2,3,4,5],[(24,[]),(0,[0,1]),(1,[0]),(2,[0,1]),(2,[]),(5,[]),(7,[])]),([(3,2,1),(0,3,6)],[7,0,1,2,3,4,5],[(13,[]),(0,[0,1]),(3,[1]),(1,[0,1]),(11,[]),(24,[]),(26,[])]),([(3,2,1),(1,3,6)],[0,1,2,3,7,4,5],[(31,[]),(18,[]),(0,[0,1])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q336 : ck336 [8,9,17,147,226,233,235,246,248,251,264,265,266,267,268,269,270,271] d336 = true := by decide +kernel
private def d337 : List NodeSpec := [([(3,2,1),(2,3,6)],[0,1,2,7,3,4,5],[(31,[]),(0,[0,1]),(13,[]),(11,[]),(3,[]),(5,[]),(26,[])]),([(3,2,1),(3,3,6)],[7,0,1,2,3,4,5],[(13,[]),(3,[1]),(0,[0,1]),(7,[]),(1,[])]),([(3,2,1),(1,3,0)],[6,0,1,2,3,7,4,5],[(35,[]),(1,[0]),(0,[0,1]),(24,[]),(4,[]),(27,[])]),([(3,2,1),(2,3,0)],[6,7,0,1,2,3,4,5],[(31,[]),(0,[0,1]),(11,[]),(4,[]),(2,[0]),(26,[]),(2,[1]),(17,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q337 : ck336 [272,273,274,275,276,277,278,279] d337 = true := by decide +kernel
private def d338 : List NodeSpec := [([(3,2,1),(1,3,1)],[6,0,2,3,7,4,5],[(31,[]),(11,[]),(0,[0,1])]),([(3,2,1),(3,3,1)],[7,6,0,2,3,4,5],[(11,[]),(13,[]),(0,[0,1]),(3,[])]),([(3,2,1),(1,4,6)],[0,1,2,3,4,7,5],[(13,[]),(17,[]),(3,[1]),(0,[0,1])]),([(3,2,1),(3,4,6)],[7,0,1,2,3,4,5],[(17,[]),(0,[0,1]),(3,[1]),(4,[]),(7,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q338 : ck336 [270,280,281] d338 = true := by decide +kernel
private def lv_0_0_8_8 : List NodeSpec := (d336 ++ (d337 ++ d338))

private theorem ok_0_0_8_8 : LevelOK rd_0_0 (subGoal 0 0) 8 lv_0_0_8_8 := by
  have go {ids ds} (h : ck336 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 8 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_7) h
  exact (levelOK_append (go q336) (levelOK_append (go q337) (go q338)))
private def ck339 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_7) 8
private def d339 : List NodeSpec := [([(3,2,1),(1,4,0)],[6,0,1,2,3,4,7,5],[(31,[]),(13,[]),(0,[0,1]),(11,[])]),([(3,2,1),(1,4,3)],[6,0,1,2,3,4,7,5],[(11,[]),(13,[]),(0,[0,1]),(1,[0]),(1,[1]),(20,[]),(24,[])]),([(3,2,1),(3,4,3)],[7,6,0,1,2,3,4,5],[(35,[]),(13,[]),(0,[0,1]),(1,[0]),(1,[1]),(5,[])]),([(1,3,0),(2,3,0)],[7,1,2,3,6,4,5],[(11,[]),(0,[0,1]),(18,[]),(26,[]),(1,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q339 : ck339 [10,11,266,267,277,278,279,282,283,284,285] d339 = true := by decide +kernel
private def d340 : List NodeSpec := [([(1,3,0),(0,3,1)],[0,7,1,2,3,6,4,5],[(11,[]),(1,[1]),(0,[0,1]),(18,[]),(27,[])]),([(1,3,0),(2,3,1)],[7,0,1,2,3,6,4,5],[(11,[]),(27,[]),(18,[]),(0,[0,1])]),([(1,3,0),(1,3,2)],[0,1,2,6,7,4,5],[(18,[]),(3,[0]),(1,[1]),(0,[0,1]),(24,[])]),([(1,3,0),(2,3,2)],[7,0,1,2,6,4,5],[(35,[]),(1,[1]),(0,[0,1]),(24,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q340 : ck339 [286] d340 = true := by decide +kernel
private def d341 : List NodeSpec := [([(1,3,0),(0,6,1)],[0,7,1,2,3,4,5],[(13,[]),(0,[0,1]),(1,[1]),(11,[]),(6,[]),(20,[])]),([(1,3,0),(0,6,1)],[0,7,1,2,3,6,4,5],[(11,[]),(1,[1]),(18,[]),(0,[0,1]),(27,[])]),([(1,3,0),(2,6,1)],[7,0,1,2,3,4,5],[(24,[]),(1,[1]),(0,[0,1]),(18,[]),(4,[]),(5,[])]),([(1,3,0),(2,6,1)],[7,0,1,2,3,6,4,5],[(11,[]),(27,[]),(18,[]),(0,[0,1]),(4,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q341 : ck339 [287,288] d341 = true := by decide +kernel
private def lv_0_0_8_9 : List NodeSpec := (d339 ++ (d340 ++ d341))

private theorem ok_0_0_8_9 : LevelOK rd_0_0 (subGoal 0 0) 8 lv_0_0_8_9 := by
  have go {ids ds} (h : ck339 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 8 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_7) h
  exact (levelOK_append (go q339) (levelOK_append (go q340) (go q341)))
private def ck342 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_7) 8
private def d342 : List NodeSpec := [([(1,3,0),(2,6,2)],[7,0,1,2,3,4,5],[(35,[]),(0,[0,1]),(31,[]),(4,[])]),([(1,3,0),(1,4,1)],[0,1,2,3,6,4,7,5],[(31,[]),(18,[]),(0,[0,1]),(13,[])]),([(1,3,0),(3,4,1)],[7,0,1,2,3,6,4,5],[(35,[]),(17,[]),(0,[0,1]),(2,[]),(4,[]),(6,[])]),([(1,3,0),(1,4,2)],[0,1,2,3,6,7,5],[(35,[]),(1,[1]),(0,[0,1]),(24,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q342 : ck342 [183,196,198,273,288,289] d342 = true := by decide +kernel
private def d343 : List NodeSpec := [([(1,3,0),(2,4,2)],[7,0,1,2,3,6,5],[(11,[]),(2,[0]),(0,[0,1]),(1,[1]),(13,[]),(24,[])]),([(1,3,0),(1,4,3)],[0,1,2,6,4,7,5],[(11,[]),(1,[1]),(2,[0]),(0,[0,1])]),([(1,3,0),(3,4,3)],[7,0,1,2,6,4,5],[(35,[]),(1,[1]),(0,[0,1])]),([(1,3,0),(1,4,6)],[0,1,2,3,4,7,5],[(11,[]),(0,[0,1]),(1,[1]),(2,[0]),(4,[]),(6,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q343 : ck342 [290] d343 = true := by decide +kernel
private def d344 : List NodeSpec := [([(1,3,0),(3,4,6)],[7,0,1,2,3,4,5],[(35,[]),(0,[0,1]),(1,[1]),(5,[])]),([(1,3,0),(1,5,2)],[0,1,2,3,6,4,7],[(30,[]),(35,[]),(1,[1]),(20,[]),(24,[])]),([(2,3,0),(0,1,6)],[7,6,0,1,2,3,4,5],[(26,[]),(0,[0,1]),(27,[]),(1,[1]),(2,[0,1]),(3,[0,1]),(4,[]),(17,[])]),([(2,3,0),(1,1,6)],[0,1,7,2,3,4,5],[(24,[]),(1,[1]),(0,[0,1]),(2,[0,1]),(4,[]),(5,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q344 : ck342 [291,292,293,294,295,296,297,298,299,300,301,302,303,304] d344 = true := by decide +kernel
private def lv_0_0_8_10 : List NodeSpec := (d342 ++ (d343 ++ d344))

private theorem ok_0_0_8_10 : LevelOK rd_0_0 (subGoal 0 0) 8 lv_0_0_8_10 := by
  have go {ids ds} (h : ck342 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 8 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_7) h
  exact (levelOK_append (go q342) (levelOK_append (go q343) (go q344)))
private def ck345 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_7) 8
private def d345 : List NodeSpec := [([(2,3,0),(1,1,6)],[6,0,1,7,2,3,4,5],[(31,[]),(0,[0,1]),(2,[0,1]),(26,[]),(4,[]),(7,[]),(17,[])]),([(2,3,0),(2,1,6)],[7,0,1,2,3,4,5],[(13,[]),(0,[0,1]),(1,[1]),(3,[0,1]),(6,[]),(20,[])]),([(2,3,0),(2,1,6)],[6,7,0,1,2,3,4,5],[(1,[1]),(0,[0,1]),(26,[]),(27,[]),(2,[0,1]),(3,[0,1]),(4,[]),(17,[])]),([(2,3,0),(3,1,6)],[7,6,0,1,2,3,4,5],[(31,[]),(26,[]),(0,[0,1]),(2,[0]),(2,[0,1]),(4,[]),(17,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q345 : ck345 [228,229,274,275,284,285,292,293,305,306,307,308,309,310,311,312,313,314,315,316,317,318,319,320,321,322,323,324,325,326,327,328,329,330,331,332] d345 = true := by decide +kernel
private def d346 : List NodeSpec := [([(2,3,0),(1,2,6)],[0,1,2,7,3,4,5],[(35,[]),(0,[0,1]),(31,[]),(3,[0]),(4,[]),(5,[]),(1,[1])]),([(2,3,0),(1,2,6)],[6,0,1,2,7,3,4,5],[(3,[0]),(1,[1]),(0,[0,1]),(2,[0,1]),(31,[]),(11,[]),(26,[]),(17,[])]),([(2,3,0),(3,2,6)],[7,6,0,1,2,3,4,5],[(26,[]),(3,[0]),(0,[0,1]),(11,[]),(31,[]),(2,[0,1]),(17,[])]),([(2,3,0),(0,3,1)],[6,0,7,1,2,3,4,5],[(26,[]),(1,[1]),(0,[0,1]),(27,[]),(4,[]),(2,[0]),(2,[1]),(3,[0]),(3,[1]),(7,[]),(17,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q346 : ck345 [201,274,291,295,302,315,316,333,334,335,336,337,338,339,340,341,342,343,344,345,346,347,348,349,350,351,352,353,354,355,356] d346 = true := by decide +kernel
private def d347 : List NodeSpec := [([(2,3,0),(1,3,1)],[6,0,1,2,3,7,4,5],[(11,[]),(27,[]),(0,[0,1]),(18,[])]),([(2,3,0),(2,3,1)],[7,6,0,1,2,3,4,5],[(31,[]),(26,[]),(0,[0,1]),(1,[]),(2,[0]),(2,[1]),(4,[]),(17,[])]),([(2,3,0),(3,3,1)],[7,6,0,1,2,3,4,5],[(11,[]),(27,[]),(0,[0,1]),(18,[]),(1,[1]),(4,[]),(26,[])]),([(2,3,0),(1,3,2)],[6,0,1,2,7,4,5],[(31,[]),(0,[0,1]),(18,[]),(3,[0]),(17,[]),(1,[1])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q347 : ck345 [296,310,318,327,350,357,358,359,360,361,362,363,364,365,366] d347 = true := by decide +kernel
private def lv_0_0_8_11 : List NodeSpec := (d345 ++ (d346 ++ d347))

private theorem ok_0_0_8_11 : LevelOK rd_0_0 (subGoal 0 0) 8 lv_0_0_8_11 := by
  have go {ids ds} (h : ck345 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 8 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_7) h
  exact (levelOK_append (go q345) (levelOK_append (go q346) (go q347)))
private def ck348 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_7) 8
private def d348 : List NodeSpec := [([(2,3,0),(1,3,2)],[6,0,1,2,3,7,4,5],[(18,[]),(31,[]),(0,[0,1]),(3,[0])]),([(2,3,0),(2,3,2)],[7,6,0,1,2,4,5],[(31,[]),(0,[0,1]),(3,[0]),(11,[]),(26,[]),(2,[0,1]),(17,[]),(1,[1])]),([(2,3,0),(2,3,2)],[7,6,0,1,2,3,4,5],[(35,[]),(26,[]),(0,[0,1]),(1,[]),(24,[])]),([(2,3,0),(1,4,6)],[0,1,2,3,4,7,5],[(5,[]),(0,[0,1]),(1,[1]),(35,[]),(2,[0]),(4,[]),(6,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q348 : ck348 [149,196,232,276,311,312,319,336,341,351,352,360,363,367,368,369,370,371] d348 = true := by decide +kernel
private def d349 : List NodeSpec := [([(2,3,0),(1,4,6)],[6,0,1,2,3,4,7,5],[(17,[]),(2,[0]),(0,[0,1]),(3,[0,1]),(18,[]),(27,[])]),([(2,3,0),(3,4,6)],[7,0,1,2,3,4,5],[(5,[]),(0,[0,1]),(1,[1]),(3,[0,1]),(18,[]),(26,[]),(2,[0]),(4,[]),(6,[]),(12,[])]),([(2,3,0),(3,4,6)],[7,6,0,1,2,3,4,5],[(26,[]),(17,[]),(0,[0,1]),(2,[0]),(3,[0,1]),(12,[]),(18,[]),(27,[])]),([(2,3,0),(1,4,1)],[6,0,1,2,3,4,7,5],[(31,[]),(2,[0]),(0,[0,1]),(18,[]),(13,[]),(26,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q349 : ck348 [233,277,297,305,306,320,321,330,342,343,347,364,365,368,372,373,374,375,376,377,378,379,380] d349 = true := by decide +kernel
private def d350 : List NodeSpec := [([(2,3,0),(3,4,1)],[7,6,0,1,2,3,4,5],[(17,[]),(0,[0,1]),(2,[0]),(18,[]),(3,[1]),(4,[]),(6,[]),(26,[]),(1,[]),(3,[0])]),([(2,3,0),(1,4,2)],[6,0,1,2,3,7,5],[(35,[]),(31,[]),(0,[0,1]),(3,[0]),(17,[]),(1,[1]),(2,[0])]),([(2,3,0),(1,4,2)],[6,0,1,2,3,4,7,5],[(35,[]),(17,[]),(0,[0,1]),(13,[]),(24,[]),(2,[0])]),([(2,3,0),(2,4,2)],[7,6,0,1,2,3,5],[(31,[]),(2,[0]),(0,[0,1]),(3,[0]),(11,[]),(13,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q350 : ck348 [150,203,298,299,313,322,323,337,353,354,366,369,381,382,383,384,385,386] d350 = true := by decide +kernel
private def lv_0_0_8_12 : List NodeSpec := (d348 ++ (d349 ++ d350))

private theorem ok_0_0_8_12 : LevelOK rd_0_0 (subGoal 0 0) 8 lv_0_0_8_12 := by
  have go {ids ds} (h : ck348 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 8 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_7) h
  exact (levelOK_append (go q348) (levelOK_append (go q349) (go q350)))
private def ck351 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_7) 8
private def d351 : List NodeSpec := [([(2,3,0),(1,4,3)],[6,0,1,2,4,7,5],[(17,[]),(0,[0,1]),(11,[]),(2,[0]),(12,[])]),([(2,3,0),(1,4,3)],[6,0,1,2,3,4,7,5],[(11,[]),(17,[]),(0,[0,1]),(12,[]),(13,[]),(27,[])]),([(2,3,0),(3,4,3)],[7,6,0,1,2,4,5],[(17,[]),(0,[0,1]),(2,[0]),(3,[0,1]),(26,[]),(18,[])]),([(2,3,0),(3,4,3)],[7,6,0,1,2,3,4,5],[(35,[]),(26,[]),(17,[]),(0,[0,1]),(13,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q351 : ck351 [72,234,235,278,279,300,303,304,307,308,324,325,331,344,345,348,355,361,387,388,389,390,391,392] d351 = true := by decide +kernel
private def d352 : List NodeSpec := [([(2,3,0),(1,5,2)],[6,0,1,2,3,4,7],[(31,[]),(35,[]),(3,[0]),(22,[]),(30,[]),(20,[]),(0,[0]),(1,[1])]),([(0,3,1),(1,6,0)],[0,1,7,2,3,4,5],[(1,[0]),(0,[0,1]),(13,[]),(3,[0,1]),(27,[]),(5,[])]),([(0,3,1),(1,6,0)],[0,6,1,7,2,3,4,5],[(13,[]),(1,[0]),(0,[0,1]),(3,[0,1]),(26,[]),(20,[]),(27,[])]),([(0,3,1),(2,1,6)],[7,0,1,2,3,4,5],[(11,[]),(13,[]),(0,[0,1]),(1,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q352 : ck351 [184,185,188,189,291,301,326,356,371,374,376,379,386,388,392,393,394,395,396,397,398,399,400,401,402,403,404,405,406,407,408,409,410,411,412] d352 = true := by decide +kernel
private def d353 : List NodeSpec := [([(0,3,1),(2,1,6)],[7,0,6,2,3,4,5],[(11,[]),(13,[]),(0,[0,1])]),([(0,3,1),(1,2,6)],[0,1,2,7,3,4,5],[(35,[]),(0,[0,1]),(3,[0]),(1,[0,1]),(24,[]),(4,[]),(5,[])]),([(0,3,1),(1,2,6)],[0,6,1,2,7,3,4,5],[(20,[]),(3,[0]),(13,[]),(1,[0,1]),(24,[]),(11,[]),(26,[])]),([(0,3,1),(2,3,6)],[7,0,1,2,3,4,5],[(24,[]),(0,[0,1]),(27,[]),(18,[]),(5,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q353 : ck351 [28,29,154,186,187,188,189,349,407,413,414,415,416,417,418,419,420,421,422,423,424,425,426,427,428] d353 = true := by decide +kernel
private def lv_0_0_8_13 : List NodeSpec := (d351 ++ (d352 ++ d353))

private theorem ok_0_0_8_13 : LevelOK rd_0_0 (subGoal 0 0) 8 lv_0_0_8_13 := by
  have go {ids ds} (h : ck351 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 8 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_7) h
  exact (levelOK_append (go q351) (levelOK_append (go q352) (go q353)))
private def ck354 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_7) 8
private def d354 : List NodeSpec := [([(0,3,1),(2,3,6)],[7,0,6,1,2,4,5],[(24,[]),(13,[]),(0,[0,1])]),([(0,3,1),(2,3,6)],[7,0,6,1,2,3,4,5],[(24,[]),(13,[]),(0,[0,1]),(27,[]),(7,[])]),([(0,3,1),(1,3,1)],[0,6,2,7,4,5],[(31,[]),(0,[0,1]),(13,[]),(35,[])]),([(0,3,1),(1,3,1)],[0,6,2,3,7,4,5],[(11,[]),(0,[0,1]),(18,[]),(1,[0,1]),(4,[]),(6,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q354 : ck354 [270,350,409,410,414,418,427,429,430,431,432,433,434,435,436,437,438,439] d354 = true := by decide +kernel
private def d355 : List NodeSpec := [([(0,3,1),(1,3,1)],[0,6,1,2,7,4,5],[(24,[]),(13,[]),(0,[0,1])]),([(0,3,1),(1,3,1)],[0,6,1,2,3,7,4,5],[(11,[]),(20,[]),(27,[]),(13,[]),(0,[0])]),([(0,3,1),(1,3,2)],[0,6,1,2,3,7,4,5],[(18,[]),(3,[0]),(0,[0,1]),(24,[]),(1,[1]),(1,[0])]),([(0,3,1),(2,3,2)],[7,0,6,1,2,3,4,5],[(35,[]),(26,[]),(0,[0,1]),(24,[]),(1,[1]),(3,[0])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q355 : ck354 [31,32,149,155,156,351,396,397,419,440,441,442] d355 = true := by decide +kernel
private def d356 : List NodeSpec := [([(0,3,1),(1,4,0)],[0,6,1,2,3,4,7,5],[(34,[]),(1,[0]),(5,[]),(12,[]),(18,[]),(3,[0]),(26,[]),(0,[0,1]),(3,[1]),(27,[])]),([(0,3,1),(1,4,6)],[0,1,2,3,4,7,5],[(34,[]),(17,[]),(35,[]),(0,[0,1])]),([(0,3,1),(3,4,6)],[7,0,1,2,3,4,5],[(17,[]),(20,[]),(3,[0,1]),(0,[0,1]),(2,[0]),(18,[]),(26,[])]),([(0,3,1),(1,4,2)],[0,6,1,2,3,7,5],[(35,[]),(0,[0,1]),(3,[0]),(24,[]),(1,[0,1]),(4,[1]),(5,[]),(2,[0])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q356 : ck354 [36,150,157,190,192,353,398,401,411,420,421,428,432,433,443,444,445,446,447,448] d356 = true := by decide +kernel
private def lv_0_0_8_14 : List NodeSpec := (d354 ++ (d355 ++ d356))

private theorem ok_0_0_8_14 : LevelOK rd_0_0 (subGoal 0 0) 8 lv_0_0_8_14 := by
  have go {ids ds} (h : ck354 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 8 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_7) h
  exact (levelOK_append (go q354) (levelOK_append (go q355) (go q356)))
private def ck357 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_7) 8
private def d357 : List NodeSpec := [([(0,3,1),(1,4,2)],[0,6,1,2,3,4,7,5],[(35,[]),(13,[]),(0,[0,1]),(1,[0,1]),(5,[])]),([(0,3,1),(2,4,2)],[7,0,6,1,2,3,5],[(13,[]),(3,[0]),(0,[0,1]),(1,[0,1]),(11,[]),(24,[])]),([(0,3,1),(1,4,3)],[0,6,1,2,3,4,7,5],[(11,[]),(13,[]),(0,[0,1]),(1,[0]),(1,[1]),(20,[])]),([(0,3,1),(3,4,3)],[7,0,6,1,2,3,4,5],[(35,[]),(34,[]),(26,[]),(5,[]),(1,[1])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q357 : ck357 [37,38,39,40,191,192,354,355,402,403,404,405,422,434,443,449,450] d357 = true := by decide +kernel
private def d358 : List NodeSpec := [([(0,3,1),(1,5,2)],[0,6,1,2,3,4,7],[(34,[]),(3,[0]),(1,[0,1]),(11,[]),(24,[])]),([(1,3,1),(2,3,1)],[7,0,2,3,6,4,5],[(11,[]),(27,[]),(0,[0,1])]),([(1,3,1),(3,3,1)],[7,0,1,2,6,4,5],[(11,[]),(13,[]),(0,[0,1])]),([(1,3,1),(1,3,2)],[0,1,2,6,7,4,5],[(31,[]),(18,[]),(3,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q358 : ck357 [42,356,406,414,425,435,451] d358 = true := by decide +kernel
private def d359 : List NodeSpec := [([(1,3,1),(2,3,2)],[7,0,1,2,6,4,5],[(31,[]),(11,[]),(0,[0,1])]),([(1,3,1),(2,6,0)],[7,0,1,2,3,4,5],[(31,[]),(18,[]),(0,[0,1]),(1,[]),(5,[])]),([(1,3,1),(2,6,2)],[7,0,1,2,3,4,5],[(31,[]),(35,[]),(0,[0,1])]),([(1,3,1),(1,4,0)],[0,1,2,3,6,4,7,5],[(31,[]),(18,[]),(0,[0,1]),(33,[]),(5,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q359 : ck357 [270,432,437,452,453] d359 = true := by decide +kernel
private def lv_0_0_8_15 : List NodeSpec := (d357 ++ (d358 ++ d359))

private theorem ok_0_0_8_15 : LevelOK rd_0_0 (subGoal 0 0) 8 lv_0_0_8_15 := by
  have go {ids ds} (h : ck357 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 8 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_7) h
  exact (levelOK_append (go q357) (levelOK_append (go q358) (go q359)))
private def ck360 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_7) 8
private def d360 : List NodeSpec := [([(1,3,1),(3,4,1)],[7,0,1,2,3,6,4,5],[(24,[]),(20,[]),(27,[]),(18,[]),(0,[1])]),([(1,3,1),(1,4,2)],[0,1,2,3,6,7,5],[(31,[]),(0,[0,1]),(11,[]),(2,[0]),(3,[]),(5,[]),(10,[])]),([(1,3,1),(2,4,2)],[7,0,1,2,3,6,5],[(31,[]),(0,[0,1]),(2,[0]),(11,[])]),([(1,3,1),(1,4,6)],[0,1,2,3,4,7,5],[(11,[]),(17,[]),(0,[0,1]),(6,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q360 : ck360 [433,434,452,454,455,456,457] d360 = true := by decide +kernel
private def d361 : List NodeSpec := [([(1,3,1),(3,4,6)],[7,0,1,2,3,4,5],[(35,[]),(17,[]),(0,[0,1])]),([(1,3,1),(1,5,2)],[0,1,2,3,6,4,7],[(29,[]),(35,[]),(31,[])]),([(1,3,1),(3,5,6)],[7,0,1,2,3,4],[(31,[]),(33,[]),(16,[]),(35,[]),(20,[])]),([(1,3,1),(3,5,6)],[7,0,1,2,3,6,4],[(11,[]),(27,[]),(18,[]),(0,[0])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q361 : ck360 [359,435,436,453,455,456,458,459] d361 = true := by decide +kernel
private def d362 : List NodeSpec := [([(2,3,1),(1,0,6)],[0,7,1,2,3,4,5],[(31,[]),(0,[0,1]),(2,[0,1]),(1,[]),(4,[]),(5,[])]),([(2,3,1),(1,1,6)],[0,1,2,3,7,4,5],[(11,[]),(27,[]),(0,[0,1]),(18,[])]),([(2,3,1),(1,2,6)],[0,1,2,7,3,4,5],[(31,[]),(35,[]),(0,[0,1]),(4,[]),(5,[])]),([(2,3,1),(2,3,6)],[0,7,1,2,3,4,5],[(13,[]),(0,[0,1]),(11,[]),(31,[]),(20,[]),(26,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q362 : ck360 [45,327,414,460,461,462,463,464,465,466] d362 = true := by decide +kernel
private def lv_0_0_8_16 : List NodeSpec := (d360 ++ (d361 ++ d362))

private theorem ok_0_0_8_16 : LevelOK rd_0_0 (subGoal 0 0) 8 lv_0_0_8_16 := by
  have go {ids ds} (h : ck360 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 8 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_7) h
  exact (levelOK_append (go q360) (levelOK_append (go q361) (go q362)))
private def ck363 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_7) 8
private def d363 : List NodeSpec := [([(2,3,1),(3,3,1)],[7,6,0,2,3,4,5],[(11,[]),(0,[0,1]),(18,[]),(27,[]),(4,[])]),([(2,3,1),(3,3,1)],[7,6,0,1,2,4,5],[(24,[]),(13,[]),(0,[0,1])]),([(2,3,1),(3,3,1)],[7,6,0,1,2,3,4,5],[(11,[]),(27,[]),(13,[]),(0,[0,1])]),([(2,3,1),(1,3,2)],[6,0,1,2,7,4,5],[(31,[]),(0,[0,1]),(18,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q363 : ck363 [438,440,441,467,468,469,470] d363 = true := by decide +kernel
private def d364 : List NodeSpec := [([(2,3,1),(1,3,2)],[6,0,1,2,3,7,4,5],[(31,[]),(18,[]),(0,[0,1])]),([(2,3,1),(2,3,2)],[7,6,0,1,2,4,5],[(31,[]),(0,[0,1]),(11,[]),(26,[]),(3,[])]),([(2,3,1),(2,3,2)],[7,6,0,1,2,3,4,5],[(35,[]),(31,[]),(0,[0,1]),(4,[])]),([(2,3,1),(1,4,6)],[0,1,2,3,4,7,5],[(17,[]),(0,[0,1]),(35,[]),(2,[0]),(13,[]),(6,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q364 : ck363 [463,470,471,472,473] d364 = true := by decide +kernel
private def d365 : List NodeSpec := [([(2,3,1),(1,4,6)],[6,0,1,2,3,4,7,5],[(24,[]),(2,[0]),(27,[]),(0,[0,1]),(13,[]),(18,[]),(26,[])]),([(2,3,1),(3,4,6)],[7,0,1,2,3,4,5],[(24,[]),(17,[]),(0,[0,1]),(13,[])]),([(2,3,1),(1,4,0)],[6,0,1,2,3,4,7,5],[(31,[]),(0,[0,1]),(18,[]),(5,[]),(12,[]),(26,[]),(13,[])]),([(2,3,1),(3,4,1)],[7,6,0,1,2,3,4,5],[(24,[]),(20,[]),(27,[]),(2,[0]),(18,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q365 : ck363 [] d365 = true := by decide +kernel
private def lv_0_0_8_17 : List NodeSpec := (d363 ++ (d364 ++ d365))

private theorem ok_0_0_8_17 : LevelOK rd_0_0 (subGoal 0 0) 8 lv_0_0_8_17 := by
  have go {ids ds} (h : ck363 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 8 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_7) h
  exact (levelOK_append (go q363) (levelOK_append (go q364) (go q365)))
private def ck366 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_7) 8
private def d366 : List NodeSpec := [([(2,3,1),(1,4,2)],[6,0,1,2,3,7,5],[(31,[]),(35,[]),(0,[0,1]),(2,[0]),(5,[])]),([(2,3,1),(1,4,2)],[6,0,1,2,3,4,7,5],[(31,[]),(35,[]),(0,[0,1]),(5,[]),(2,[0])]),([(2,3,1),(2,4,2)],[7,6,0,1,2,3,5],[(31,[]),(2,[0]),(0,[0,1]),(11,[]),(13,[])]),([(2,3,1),(1,4,3)],[6,0,1,2,3,4,7,5],[(11,[]),(0,[0,1]),(2,[0]),(13,[]),(1,[1]),(1,[0])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q366 : ck366 [46,72,158,361,460,466,474,475] d366 = true := by decide +kernel
private def d367 : List NodeSpec := [([(2,3,1),(3,4,3)],[7,6,0,1,2,3,4,5],[(35,[]),(26,[]),(5,[]),(0,[0,1]),(1,[1])]),([(2,3,1),(1,5,2)],[6,0,1,2,3,4,7],[(29,[]),(31,[]),(35,[]),(20,[])]),([(3,3,1),(1,0,6)],[0,7,1,2,3,4,5],[(35,[]),(1,[0]),(0,[0,1]),(13,[]),(5,[]),(27,[])]),([(3,3,1),(1,0,6)],[6,0,7,1,2,3,4,5],[(11,[]),(13,[]),(0,[0,1]),(1,[0])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q367 : ck366 [47,159,193,194,237,280,413,461,468,473,476,477,478,479,480,481,482,483] d367 = true := by decide +kernel
private def d368 : List NodeSpec := [([(3,3,1),(1,2,6)],[0,1,2,7,3,4,5],[(35,[]),(0,[0,1]),(4,[]),(24,[]),(1,[])]),([(3,3,1),(1,4,6)],[0,1,2,3,4,7,5],[(34,[]),(17,[]),(11,[]),(0,[0,1])]),([(3,3,1),(3,4,6)],[7,0,1,2,3,4,5],[(11,[]),(17,[]),(0,[0,1]),(1,[]),(4,[])]),([(3,3,1),(1,4,0)],[6,0,1,2,3,4,7,5],[(35,[]),(34,[]),(1,[0]),(5,[]),(12,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q368 : ck366 [194,484,485] d368 = true := by decide +kernel
private def lv_0_0_8_18 : List NodeSpec := (d366 ++ (d367 ++ d368))

private theorem ok_0_0_8_18 : LevelOK rd_0_0 (subGoal 0 0) 8 lv_0_0_8_18 := by
  have go {ids ds} (h : ck366 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 8 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_7) h
  exact (levelOK_append (go q366) (levelOK_append (go q367) (go q368)))
private def ck369 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_7) 8
private def d369 : List NodeSpec := [([(3,3,1),(1,4,2)],[6,0,1,2,3,7,5],[(35,[]),(0,[0,1]),(1,[0,1]),(24,[]),(4,[1])]),([(3,3,1),(2,4,2)],[6,7,0,1,2,3,5],[(11,[]),(13,[]),(0,[0,1]),(1,[1])]),([(3,3,1),(1,5,2)],[6,0,1,2,3,4,7],[(34,[]),(11,[]),(1,[1])]),([(1,3,2),(2,3,2)],[7,0,1,3,6,4,5],[(11,[]),(0,[0,1]),(18,[]),(1,[0,1])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q369 : ck369 [78,160,195,363,466,470,481,482,483] d369 = true := by decide +kernel
private def d370 : List NodeSpec := [([(1,3,2),(2,6,0)],[7,0,1,2,3,4,5],[(31,[]),(18,[]),(0,[0,1]),(3,[1]),(4,[]),(5,[]),(1,[0])]),([(1,3,2),(2,6,0)],[7,0,1,2,3,6,4,5],[(18,[]),(3,[1]),(31,[]),(0,[0,1])]),([(1,3,2),(0,6,1)],[0,7,1,2,3,4,5],[(13,[]),(3,[1]),(0,[0,1]),(1,[0,1]),(7,[]),(6,[])]),([(1,3,2),(0,6,1)],[0,7,1,2,3,6,4,5],[(18,[]),(3,[1]),(0,[0,1]),(24,[]),(1,[0,1])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q370 : ck369 [79,80,161,162,362,367,442,451,486,487,488,489,490,491,492,493,494] d370 = true := by decide +kernel
private def d371 : List NodeSpec := [([(1,3,2),(2,6,1)],[7,0,1,2,3,4,5],[(27,[]),(3,[1]),(0,[0,1]),(18,[]),(4,[]),(5,[])]),([(1,3,2),(2,6,1)],[7,0,1,2,3,6,4,5],[(31,[]),(18,[]),(0,[0,1]),(4,[])]),([(1,3,2),(1,4,0)],[0,1,2,3,6,4,7,5],[(18,[]),(31,[]),(0,[0,1]),(3,[1]),(1,[0]),(5,[]),(12,[]),(13,[])]),([(1,3,2),(1,4,1)],[0,1,2,3,6,4,7,5],[(31,[]),(18,[]),(0,[0,1]),(13,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q371 : ck369 [163,495] d371 = true := by decide +kernel
private def lv_0_0_8_19 : List NodeSpec := (d369 ++ (d370 ++ d371))

private theorem ok_0_0_8_19 : LevelOK rd_0_0 (subGoal 0 0) 8 lv_0_0_8_19 := by
  have go {ids ds} (h : ck369 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 8 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_7) h
  exact (levelOK_append (go q369) (levelOK_append (go q370) (go q371)))
private def ck372 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_7) 8
private def d372 : List NodeSpec := [([(1,3,2),(3,4,1)],[7,0,1,2,3,6,4,5],[(18,[]),(3,[1]),(0,[0,1]),(1,[0,1]),(24,[]),(4,[])]),([(1,3,2),(1,4,6)],[0,1,2,3,4,7,5],[(17,[]),(0,[0,1]),(3,[1]),(7,[]),(1,[]),(4,[]),(6,[])]),([(1,3,2),(3,4,6)],[7,0,1,2,3,4,5],[(17,[]),(18,[]),(3,[1]),(0,[0,1])]),([(2,3,2),(1,0,6)],[0,7,1,2,3,4,5],[(35,[]),(0,[0,1]),(31,[]),(4,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q372 : ck372 [83,163,164,196,366,490,496,497,498,499,500,501,502,503,504] d372 = true := by decide +kernel
private def d373 : List NodeSpec := [([(2,3,2),(3,0,6)],[7,6,0,1,2,3,4,5],[(35,[]),(26,[]),(0,[0,1]),(25,[]),(24,[])]),([(2,3,2),(0,1,6)],[7,6,0,1,2,3,4,5],[(35,[]),(26,[]),(0,[0,1]),(24,[]),(1,[0])]),([(2,3,2),(1,1,6)],[0,1,7,2,3,4,5],[(11,[]),(27,[]),(0,[0,1]),(2,[]),(5,[])]),([(2,3,2),(2,1,6)],[0,7,1,2,3,4,5],[(11,[]),(13,[]),(0,[0,1]),(1,[]),(3,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q373 : ck372 [87,165,336,419,505,506,507,508] d373 = true := by decide +kernel
private def d374 : List NodeSpec := [([(2,3,2),(3,1,6)],[7,6,0,1,2,3,4,5],[(31,[]),(35,[]),(0,[0,1]),(4,[])]),([(2,3,2),(1,4,6)],[0,1,2,3,4,7,5],[(11,[]),(17,[]),(0,[0,1]),(4,[]),(6,[])]),([(2,3,2),(3,4,6)],[7,0,1,2,3,4,5],[(17,[]),(0,[0,1]),(3,[1]),(11,[]),(26,[]),(4,[]),(6,[]),(10,[])]),([(2,3,2),(1,4,0)],[6,0,1,2,3,4,7,5],[(31,[]),(18,[]),(0,[0,1]),(5,[]),(3,[1]),(1,[0]),(12,[]),(26,[]),(11,[]),(13,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q374 : ck372 [166,463,509,510,511] d374 = true := by decide +kernel
private def lv_0_0_8_20 : List NodeSpec := (d372 ++ (d373 ++ d374))

private theorem ok_0_0_8_20 : LevelOK rd_0_0 (subGoal 0 0) 8 lv_0_0_8_20 := by
  have go {ids ds} (h : ck372 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 8 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_7) h
  exact (levelOK_append (go q372) (levelOK_append (go q373) (go q374)))
private def ck375 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_7) 8
private def d375 : List NodeSpec := [([(2,3,2),(1,4,1)],[6,0,1,2,3,4,7,5],[(31,[]),(0,[0,1]),(2,[0]),(11,[]),(18,[]),(26,[]),(13,[])]),([(2,3,2),(3,4,1)],[7,6,0,1,2,3,4,5],[(35,[]),(0,[0,1]),(1,[0,1]),(24,[]),(4,[])]),([(1,4,0),(1,4,2)],[0,1,2,3,6,7,5],[(5,[]),(31,[]),(0,[0,1]),(1,[1]),(3,[0]),(35,[])]),([(1,4,0),(0,6,1)],[0,7,1,2,3,4,5],[(20,[]),(1,[1]),(2,[1]),(3,[0,1]),(0,[0,1]),(7,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q375 : ck375 [88,166,167,203,369,443,495,511,512,513,514,515,516,517,518,519,520,521] d375 = true := by decide +kernel
private def d376 : List NodeSpec := [([(1,4,0),(2,6,1)],[7,0,1,2,3,4,5],[(24,[]),(1,[1]),(0,[0,1]),(2,[1]),(7,[])]),([(1,4,0),(2,6,2)],[7,0,1,2,3,4,5],[(12,[]),(3,[0]),(0,[0,1]),(31,[]),(35,[]),(4,[])]),([(1,4,0),(0,6,3)],[0,1,2,7,3,4,5],[(33,[]),(3,[0,1]),(18,[]),(26,[]),(0,[0,1]),(4,[]),(5,[]),(6,[])]),([(1,4,0),(2,6,3)],[7,0,1,2,3,4,5],[(11,[]),(1,[1]),(0,[0,1]),(2,[1]),(4,[]),(6,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q376 : ck375 [255,282,444,518,519,522,523,524] d376 = true := by decide +kernel
private def d377 : List NodeSpec := [([(1,4,0),(1,5,2)],[0,1,2,3,4,6,7],[(33,[]),(3,[0]),(31,[]),(34,[]),(11,[])]),([(1,4,1),(3,4,1)],[7,0,1,2,3,6,5],[(24,[]),(17,[]),(0,[0,1])]),([(1,4,1),(1,4,2)],[0,1,2,3,6,7,5],[(17,[]),(3,[0]),(0,[0,1]),(13,[]),(6,[1]),(2,[]),(11,[])]),([(1,4,1),(2,6,0)],[7,0,1,2,3,4,5],[(31,[]),(13,[]),(0,[0,1])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q377 : ck375 [376,525,526] d377 = true := by decide +kernel
private def lv_0_0_8_21 : List NodeSpec := (d375 ++ (d376 ++ d377))

private theorem ok_0_0_8_21 : LevelOK rd_0_0 (subGoal 0 0) 8 lv_0_0_8_21 := by
  have go {ids ds} (h : ck375 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 8 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_7) h
  exact (levelOK_append (go q375) (levelOK_append (go q376) (go q377)))
private def ck378 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_7) 8
private def d378 : List NodeSpec := [([(1,4,1),(2,6,2)],[7,0,1,2,3,4,5],[(31,[]),(13,[]),(0,[0,1]),(2,[])]),([(1,4,1),(0,6,3)],[0,1,2,7,3,4,5],[(34,[]),(31,[]),(18,[]),(26,[]),(0,[0,1])]),([(1,4,1),(2,6,3)],[7,0,1,2,3,4,5],[(11,[]),(13,[]),(0,[0,1]),(1,[])]),([(1,4,1),(1,5,2)],[0,1,2,3,4,6,7],[(29,[]),(34,[]),(31,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q378 : ck378 [92,525,526,527,528,529] d378 = true := by decide +kernel
private def d379 : List NodeSpec := [([(3,4,1),(1,0,6)],[0,7,1,2,3,4,5],[(17,[]),(0,[0,1]),(4,[]),(27,[]),(3,[0,1]),(2,[1]),(7,[])]),([(3,4,1),(1,2,6)],[0,1,2,7,3,4,5],[(3,[0]),(0,[0,1]),(2,[1]),(1,[0,1]),(35,[]),(4,[]),(24,[])]),([(3,4,1),(1,2,6)],[6,0,1,2,7,3,4,5],[(17,[]),(3,[0]),(0,[0,1]),(35,[]),(4,[]),(24,[])]),([(3,4,1),(1,3,6)],[0,1,2,3,7,4,5],[(11,[]),(2,[1]),(0,[0,1]),(1,[0,1]),(4,[]),(6,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q379 : ck378 [93,97,99,170,210,211,383,384,385,496,512,513,514,530,531,532,533,534,535,536,537,538,539,540] d379 = true := by decide +kernel
private def d380 : List NodeSpec := [([(3,4,1),(1,3,6)],[6,0,1,2,3,7,4,5],[(35,[]),(20,[]),(17,[])]),([(3,4,1),(2,3,6)],[0,1,2,7,3,4,5],[(2,[1]),(0,[0,1]),(4,[]),(1,[0,1]),(3,[0,1]),(18,[]),(26,[])]),([(3,4,1),(2,3,6)],[6,0,1,2,7,3,4,5],[(17,[]),(20,[]),(3,[0,1]),(18,[]),(0,[0,1]),(2,[1])]),([(3,4,1),(1,4,2)],[6,0,1,2,3,7,5],[(17,[]),(3,[0]),(0,[0,1]),(24,[]),(4,[1]),(2,[]),(11,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q380 : ck378 [94,98,171,212,256,383,446,497,498,512,513,515,516,537,538,541,542,543,544,545,546,547] d380 = true := by decide +kernel
private def lv_0_0_8_22 : List NodeSpec := (d378 ++ (d379 ++ d380))

private theorem ok_0_0_8_22 : LevelOK rd_0_0 (subGoal 0 0) 8 lv_0_0_8_22 := by
  have go {ids ds} (h : ck378 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 8 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_7) h
  exact (levelOK_append (go q378) (levelOK_append (go q379) (go q380)))
private def ck381 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_7) 8
private def d381 : List NodeSpec := [([(3,4,1),(1,5,2)],[6,0,1,2,3,4,7],[(20,[]),(35,[]),(1,[0,1]),(3,[0]),(2,[1])]),([(1,4,2),(1,6,0)],[0,1,2,3,6,7,5],[(5,[]),(31,[]),(0,[0,1]),(1,[0]),(3,[1]),(35,[])]),([(1,4,2),(2,6,0)],[7,0,1,2,3,6,5],[(35,[]),(17,[]),(0,[0,1]),(1,[0]),(2,[])]),([(1,4,2),(0,6,1)],[0,7,1,2,3,6,5],[(35,[]),(0,[0,1]),(1,[0,1]),(24,[]),(4,[0]),(5,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q381 : ck381 [96,213,214,386,447,518,530,546,548,549,550] d381 = true := by decide +kernel
private def d382 : List NodeSpec := [([(1,4,2),(1,6,1)],[0,1,2,3,6,7,5],[(17,[]),(24,[]),(0,[0,1]),(11,[])]),([(1,4,2),(2,6,1)],[7,0,1,2,3,6,5],[(35,[]),(31,[]),(0,[0,1])]),([(1,4,2),(3,6,1)],[7,0,1,2,3,6,5],[(17,[]),(3,[1]),(0,[0,1]),(24,[]),(4,[0]),(10,[]),(11,[])]),([(1,4,2),(0,6,3)],[0,1,2,7,3,6,5],[(35,[]),(0,[0,1]),(1,[0,1]),(24,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q382 : ck381 [118,172,215,525,537,551,552,553,554,555,556] d382 = true := by decide +kernel
private def d383 : List NodeSpec := [([(1,4,2),(1,6,3)],[0,1,2,3,6,7,5],[(17,[]),(11,[]),(0,[0,1]),(1,[0]),(24,[])]),([(1,4,2),(2,6,3)],[7,0,1,2,3,6,5],[(10,[]),(0,[0,1]),(11,[]),(1,[0,1]),(24,[])]),([(1,4,2),(3,6,3)],[7,0,1,2,3,6,5],[(35,[]),(17,[]),(0,[0,1])]),([(1,4,2),(1,4,3)],[0,1,2,3,6,7,5],[(17,[]),(11,[]),(0,[0,1]),(3,[]),(24,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q383 : ck381 [119,173,216,557,558,559,560,561,562,563,564,565,566,567] d383 = true := by decide +kernel
private def lv_0_0_8_23 : List NodeSpec := (d381 ++ (d382 ++ d383))

private theorem ok_0_0_8_23 : LevelOK rd_0_0 (subGoal 0 0) 8 lv_0_0_8_23 := by
  have go {ids ds} (h : ck381 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 8 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_7) h
  exact (levelOK_append (go q381) (levelOK_append (go q382) (go q383)))
private def ck384 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_7) 8
private def d384 : List NodeSpec := [([(1,4,2),(3,4,3)],[7,0,1,2,3,6,5],[(35,[]),(17,[]),(0,[0,1]),(3,[])]),([(1,4,2),(2,6,0)],[7,0,1,2,3,4,5],[(35,[]),(17,[]),(0,[0,1]),(1,[0])]),([(1,4,2),(0,6,1)],[0,7,1,2,3,4,5],[(35,[]),(0,[0,1]),(4,[]),(1,[0,1]),(3,[])]),([(1,4,2),(2,6,1)],[7,0,1,2,3,4,5],[(35,[]),(27,[]),(0,[0,1]),(3,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q384 : ck384 [565,568,569] d384 = true := by decide +kernel
private def d385 : List NodeSpec := [([(1,4,2),(0,6,3)],[0,1,2,7,3,4,5],[(10,[]),(0,[0,1]),(1,[0,1]),(11,[]),(26,[]),(3,[]),(4,[]),(5,[]),(6,[])]),([(1,4,2),(2,6,3)],[7,0,1,2,3,4,5],[(7,[]),(3,[1]),(0,[0,1]),(2,[1]),(1,[0,1]),(4,[]),(6,[])]),([(1,4,3),(3,4,3)],[7,0,1,2,3,6,5],[(11,[]),(17,[]),(0,[0,1])]),([(1,4,3),(2,6,0)],[7,0,1,2,3,4,5],[(17,[]),(11,[]),(0,[0,1]),(2,[1]),(4,[]),(6,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q385 : ck384 [121,122,126,174,175,221,260,283,449,474,570,571,572,573] d385 = true := by decide +kernel
private def d386 : List NodeSpec := [([(1,4,3),(0,6,1)],[0,7,1,2,3,4,5],[(20,[]),(2,[1]),(11,[]),(1,[0,1]),(0,[0,1]),(6,[])]),([(1,4,3),(0,6,1)],[0,7,1,2,3,4,6,5],[(11,[]),(17,[]),(0,[0,1]),(13,[]),(6,[]),(20,[])]),([(1,4,3),(2,6,1)],[7,0,1,2,3,4,5],[(24,[]),(2,[1]),(27,[]),(0,[0,1]),(4,[]),(7,[])]),([(1,4,3),(2,6,1)],[7,0,1,2,3,4,6,5],[(11,[]),(17,[]),(0,[0,1]),(13,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q386 : ck384 [127,220,389,566,574,575,576] d386 = true := by decide +kernel
private def lv_0_0_8_24 : List NodeSpec := (d384 ++ (d385 ++ d386))

private theorem ok_0_0_8_24 : LevelOK rd_0_0 (subGoal 0 0) 8 lv_0_0_8_24 := by
  have go {ids ds} (h : ck384 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 8 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_7) h
  exact (levelOK_append (go q384) (levelOK_append (go q385) (go q386)))
private def ck387 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_7) 8
private def d387 : List NodeSpec := [([(1,4,3),(2,6,2)],[7,0,1,2,3,4,5],[(11,[]),(0,[0,1]),(2,[1]),(1,[0,1]),(4,[]),(6,[])]),([(1,4,3),(1,5,2)],[0,1,2,3,4,6,7],[(30,[]),(2,[1]),(1,[0,1]),(34,[]),(24,[])]),([(1,4,3),(3,5,6)],[7,0,1,2,3,4],[(2,[1]),(11,[]),(20,[]),(1,[0,1]),(15,[])]),([(1,4,3),(3,5,6)],[7,0,1,2,3,4,6],[(11,[]),(17,[]),(15,[]),(0,[]),(20,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q387 : ck387 [130,133,134,176,221,223,263,387,388,390,475,561,567,573,576,577,578,579] d387 = true := by decide +kernel
private def d388 : List NodeSpec := [([(3,4,3),(1,0,6)],[0,7,1,2,3,4,5],[(35,[]),(17,[]),(0,[0,1])]),([(3,4,3),(1,1,6)],[0,1,7,2,3,4,5],[(24,[]),(18,[]),(0,[0,1]),(27,[])]),([(3,4,3),(2,1,6)],[0,7,1,2,3,4,5],[(35,[]),(20,[]),(1,[])]),([(3,4,3),(1,2,6)],[0,1,2,7,3,4,5],[(18,[]),(3,[0]),(0,[0,1]),(1,[0,1]),(4,[]),(6,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q388 : ck387 [136,177,391,565,580,581,582] d388 = true := by decide +kernel
private def d389 : List NodeSpec := [([(3,4,3),(1,5,2)],[6,0,1,2,3,4,7],[(35,[]),(34,[]),(1,[0,1]),(30,[]),(0,[0]),(24,[])]),([(1,5,2),(1,6,0)],[0,1,2,3,4,6,7],[(20,[]),(3,[1]),(14,[]),(1,[0]),(11,[])]),([(1,5,2),(2,6,0)],[7,0,1,2,3,4,6],[(29,[]),(22,[]),(30,[]),(1,[0])]),([(1,5,2),(0,6,1)],[0,7,1,2,3,4,6],[(30,[]),(34,[]),(1,[0])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q389 : ck387 [139,376,392,583,584,585,586,587] d389 = true := by decide +kernel
private def lv_0_0_8_25 : List NodeSpec := (d387 ++ (d388 ++ d389))

private theorem ok_0_0_8_25 : LevelOK rd_0_0 (subGoal 0 0) 8 lv_0_0_8_25 := by
  have go {ids ds} (h : ck387 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 8 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_7) h
  exact (levelOK_append (go q387) (levelOK_append (go q388) (go q389)))
private def ck390 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_7) 8
private def d390 : List NodeSpec := [([(1,5,2),(1,6,1)],[0,1,2,3,4,6,7],[(22,[]),(3,[1]),(14,[]),(20,[]),(11,[])]),([(1,5,2),(2,6,1)],[7,0,1,2,3,4,6],[(30,[]),(31,[]),(20,[])]),([(1,5,2),(3,6,1)],[7,0,1,2,3,4,6],[(29,[]),(22,[]),(14,[])]),([(1,5,2),(0,6,3)],[0,1,2,7,3,4,6],[(29,[]),(33,[]),(30,[]),(2,[0]),(2,[0,1])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q390 : ck390 [583,588,589,590,591,592,593,594,595,596] d390 = true := by decide +kernel
private def d391 : List NodeSpec := [([(1,5,2),(1,6,3)],[0,1,2,3,4,6,7],[(14,[]),(11,[]),(20,[]),(22,[])]),([(1,5,2),(2,6,3)],[7,0,1,2,3,4,6],[(29,[]),(35,[]),(1,[0])]),([(1,5,2),(3,6,3)],[7,0,1,2,3,4,6],[(14,[]),(3,[1]),(20,[]),(22,[]),(11,[]),(19,[])]),([(1,5,2),(1,6,4)],[0,1,2,3,4,6,7],[(20,[]),(35,[]),(22,[]),(3,[1]),(30,[]),(9,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q391 : ck390 [597,598,599,600,601,602,603] d391 = true := by decide +kernel
private def d392 : List NodeSpec := [([(1,5,2),(2,6,4)],[7,0,1,2,3,4,6],[(29,[]),(14,[]),(30,[]),(2,[0])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q392 : ck390 [] d392 = true := by decide +kernel
private def lv_0_0_8_26 : List NodeSpec := (d390 ++ (d391 ++ d392))

private theorem ok_0_0_8_26 : LevelOK rd_0_0 (subGoal 0 0) 8 lv_0_0_8_26 := by
  have go {ids ds} (h : ck390 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 8 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_7) h
  exact (levelOK_append (go q390) (levelOK_append (go q391) (go q392)))
private def lv_0_0_8 : List NodeSpec := ((((lv_0_0_8_0 ++ (lv_0_0_8_1 ++ lv_0_0_8_2)) ++ (lv_0_0_8_3 ++ (lv_0_0_8_4 ++ lv_0_0_8_5))) ++ ((lv_0_0_8_6 ++ (lv_0_0_8_7 ++ lv_0_0_8_8)) ++ ((lv_0_0_8_9 ++ lv_0_0_8_10) ++ (lv_0_0_8_11 ++ lv_0_0_8_12)))) ++ (((lv_0_0_8_13 ++ (lv_0_0_8_14 ++ lv_0_0_8_15)) ++ ((lv_0_0_8_16 ++ lv_0_0_8_17) ++ (lv_0_0_8_18 ++ lv_0_0_8_19))) ++ ((lv_0_0_8_20 ++ (lv_0_0_8_21 ++ lv_0_0_8_22)) ++ ((lv_0_0_8_23 ++ lv_0_0_8_24) ++ (lv_0_0_8_25 ++ lv_0_0_8_26)))))
private theorem ok_0_0_8 : LevelOK rd_0_0 (subGoal 0 0) 8 lv_0_0_8 := (levelOK_append (levelOK_append (levelOK_append (levelOK_append ok_0_0_8_0 (levelOK_append ok_0_0_8_1 ok_0_0_8_2)) (levelOK_append ok_0_0_8_3 (levelOK_append ok_0_0_8_4 ok_0_0_8_5))) (levelOK_append (levelOK_append ok_0_0_8_6 (levelOK_append ok_0_0_8_7 ok_0_0_8_8)) (levelOK_append (levelOK_append ok_0_0_8_9 ok_0_0_8_10) (levelOK_append ok_0_0_8_11 ok_0_0_8_12)))) (levelOK_append (levelOK_append (levelOK_append ok_0_0_8_13 (levelOK_append ok_0_0_8_14 ok_0_0_8_15)) (levelOK_append (levelOK_append ok_0_0_8_16 ok_0_0_8_17) (levelOK_append ok_0_0_8_18 ok_0_0_8_19))) (levelOK_append (levelOK_append ok_0_0_8_20 (levelOK_append ok_0_0_8_21 ok_0_0_8_22)) (levelOK_append (levelOK_append ok_0_0_8_23 ok_0_0_8_24) (levelOK_append ok_0_0_8_25 ok_0_0_8_26)))))
private def ck393 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_8) 9
private def d393 : List NodeSpec := [([(1,1,0)],[0,1,6,2,3,4,5],[(0,[0]),(1,[]),(24,[]),(2,[0]),(3,[]),(2,[])]),([(2,1,0)],[6,0,1,2,3,4,5],[(0,[0]),(13,[]),(1,[]),(27,[]),(3,[0]),(2,[])]),([(1,2,0)],[0,1,2,6,3,4,5],[(31,[]),(0,[0]),(3,[]),(1,[]),(2,[0])]),([(1,2,1)],[0,1,2,6,3,4,5],[(3,[]),(27,[]),(0,[0]),(2,[0]),(1,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q393 : ck393 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96] d393 = true := by decide +kernel
private def d394 : List NodeSpec := [([(3,2,1)],[6,0,1,2,3,4,5],[(3,[]),(13,[]),(0,[0]),(24,[]),(1,[0]),(2,[])]),([(1,3,0)],[0,1,2,3,6,4,5],[(35,[]),(1,[]),(0,[0]),(2,[]),(3,[])]),([(2,3,0)],[6,0,1,2,3,4,5],[(0,[0]),(1,[]),(2,[0]),(3,[0])]),([(0,3,1)],[0,6,1,2,3,4,5],[(13,[]),(0,[0]),(1,[0]),(3,[0]),(2,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q394 : ck393 [3,6,7,12,13,36,38,39,42,43,59,60,63,65,76,78,79,80,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184] d394 = true := by decide +kernel
private def d395 : List NodeSpec := [([(1,3,1)],[0,1,2,3,6,4,5],[(31,[]),(0,[0]),(35,[]),(1,[]),(2,[]),(3,[])]),([(2,3,1)],[6,0,1,2,3,4,5],[(31,[]),(0,[0]),(2,[0]),(1,[]),(3,[])]),([(3,3,1)],[6,0,1,2,3,4,5],[(35,[]),(0,[0]),(1,[0]),(13,[]),(2,[]),(3,[])]),([(1,3,2)],[0,1,2,3,6,4,5],[(3,[]),(18,[]),(0,[0]),(1,[0]),(2,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q395 : ck393 [8,9,12,13,16,42,44,45,61,63,81,82,83,86,87,101,104,105,113,114,140,141,142,143,144,163,164,167,168,169,170,171,172,173,174,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242] d395 = true := by decide +kernel
private def lv_0_0_9_0 : List NodeSpec := (d393 ++ (d394 ++ d395))

private theorem ok_0_0_9_0 : LevelOK rd_0_0 (subGoal 0 0) 9 lv_0_0_9_0 := by
  have go {ids ds} (h : ck393 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 9 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_8) h
  exact (levelOK_append (go q393) (levelOK_append (go q394) (go q395)))
private def ck396 (ids : List Nat) := levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev ids lv_0_0_8) 9
private def d396 : List NodeSpec := [([(2,3,2)],[6,0,1,2,3,4,5],[(35,[]),(0,[0]),(3,[]),(1,[0]),(2,[])]),([(1,4,0)],[0,1,2,3,4,6,5],[(0,[0]),(2,[]),(1,[]),(3,[0]),(5,[]),(12,[])]),([(1,4,1)],[0,1,2,3,4,6,5],[(31,[]),(2,[]),(0,[0]),(13,[]),(1,[]),(3,[])]),([(3,4,1)],[6,0,1,2,3,4,5],[(17,[]),(0,[0]),(2,[]),(3,[0]),(4,[]),(1,[0])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q396 : ck396 [17,18,19,20,22,46,48,49,50,65,68,71,87,90,91,92,98,107,108,115,121,122,127,145,146,149,151,152,175,176,178,188,191,192,195,209,210,213,214,215,226,227,231,238,239,240,243,244,245,246,247,248,249,250,251,252,253,254,255,256,257,258,259,260,261,262,263,264,265,266,267,268,269,270,271,272,273,274,275,276] d396 = true := by decide +kernel
private def d397 : List NodeSpec := [([(1,4,2)],[0,1,2,3,6,5],[(0,[0]),(3,[]),(1,[0]),(2,[])]),([(1,4,2)],[0,1,2,3,4,6,5],[(35,[]),(0,[0]),(2,[]),(1,[0]),(3,[]),(5,[])]),([(2,4,2)],[6,0,1,2,3,5],[(0,[0]),(3,[]),(2,[]),(1,[0])]),([(1,4,3)],[0,1,2,3,4,6,5],[(0,[0]),(2,[]),(11,[]),(1,[0]),(3,[]),(17,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q397 : ck396 [27,28,29,30,51,52,53,54,69,70,71,74,92,95,107,109,123,124,125,127,153,154,155,156,157,179,180,181,182,193,194,195,216,217,218,219,226,228,229,241,250,254,262,275,277,278,279,280,281,282,283,284,285,286,287,288,289,290,291,292,293,294,295,296,297,298,299,300,301,302,303] d397 = true := by decide +kernel
private def d398 : List NodeSpec := [([(3,4,3)],[6,0,1,2,3,4,5],[(35,[]),(0,[0]),(17,[]),(2,[]),(1,[]),(3,[])]),([(1,5,2)],[0,1,2,3,4,6],[(3,[]),(1,[0]),(2,[0]),(0,[])])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem q398 : ck396 [31,34,55,56,75,96,110,126,129,149,158,159,160,178,183,184,197,213,220,221,230,250,260,267,276,288,294,301,304,305,306,307,308,309,310,311,312,313,314,315,316,317,318,319,320] d398 = true := by decide +kernel
private def lv_0_0_9_1 : List NodeSpec := (d396 ++ (d397 ++ d398))

private theorem ok_0_0_9_1 : LevelOK rd_0_0 (subGoal 0 0) 9 lv_0_0_9_1 := by
  have go {ids ds} (h : ck396 ids ds = true) : LevelOK rd_0_0 (subGoal 0 0) 9 ds :=
    levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK ids ok_0_0_8) h
  exact (levelOK_append (go q396) (levelOK_append (go q397) (go q398)))
private def lv_0_0_9 : List NodeSpec := (lv_0_0_9_0 ++ lv_0_0_9_1)
private theorem ok_0_0_9 : LevelOK rd_0_0 (subGoal 0 0) 9 lv_0_0_9 := (levelOK_append ok_0_0_9_0 ok_0_0_9_1)
private def lv_0_0_10_0 : List NodeSpec := [([], [0, 1, 2, 3, 4, 5], [(0, []), (1, []), (2, []), (3, [])])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem ok_0_0_10_0 : LevelOK rd_0_0 (subGoal 0 0) 10 lv_0_0_10_0 :=
  levelCheck_sound pp_0_0 (raw_faithful _ _ _) sl_0_0_ok (fun m hm => by simp only [List.mem_singleton] at hm; subst m; decide +kernel) (selectPrevOK [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21] ok_0_0_9)
    (by decide +kernel : levelCheck (freeVars 0 0) rd_0_0 (subGoal 0 0) sl_0_0 [[]] (selectPrev [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21] lv_0_0_9) 10 lv_0_0_10_0 = true)
private def lv_0_0_10 : List NodeSpec := lv_0_0_10_0
private theorem ok_0_0_10 : LevelOK rd_0_0 (subGoal 0 0) 10 lv_0_0_10 := ok_0_0_10_0
private theorem lower_0_0 : Lower (freeVars 0 0) (subGoal 0 0) 11 :=
  lower_of_search (xs := [(inputs.getD 0 zero, 4, 5), (inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 1, 5), (inputs.getD 3 zero, 3, 11), (inputs.getD 4 zero, 1, 17), (inputs.getD 5 zero, 9, 41)]) ok_0_0_10 (List.mem_cons_self) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Cube0_0

theorem rootCertificate : Impossible target 10 inputs.toFinset := by
  have ht : subGoal 0 0 = target := by decide +kernel
  have hraw : (freeVars 0 0).toFinset = inputs.toFinset := by decide +kernel
  have hc : Impossible (subGoal 0 0) 10 (freeVars 0 0).toFinset :=
    impossible_of_top ok_0_0_10 (spec := ([], [0, 1, 2, 3, 4, 5], [(0, []), (1, []), (2, []), (3, [])])) (by decide +kernel) (by decide +kernel)
  simpa only [ht, hraw] using hc

end PEqualNP.Outside.L_meta_37945_aux.Frontier

theorem PEqualNP.Outside.L_meta_37945 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075680 * 2 ^ 32 + 4276812000) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075680 * 2 ^ 32 + 4276812000) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  exact PEqualNP.Outside.L_meta_37945_aux.Frontier.main_from_root PEqualNP.Outside.L_meta_37945_aux.Frontier.rootCertificate
