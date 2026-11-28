import Mathlib
import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_50892

open PEqualNP.CircuitLowerBounds

abbrev B : ℕ := 6
abbrev Mx : ℕ := 2 ^ B - 1

abbrev Col := Fin B → Bool

def zc : Col := fun _ => false

def Rep (c : Col) (v : ℕ) : Prop := v < 2 ^ B ∧ ∀ t : Fin B, v.testBit t.val = c t

instance (c : Col) (v : ℕ) : Decidable (Rep c v) := by
  unfold Rep; infer_instance

theorem rep_unique {c : Col} {v w : ℕ} (hv : Rep c v) (hw : Rep c w) : v = w := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < B
  · rw [hv.2 ⟨i, hi⟩, hw.2 ⟨i, hi⟩]
  · have h1 : v < 2 ^ i := lt_of_lt_of_le hv.1 (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h2 : w < 2 ^ i := lt_of_lt_of_le hw.1 (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_eq_false_of_lt h1, Nat.testBit_eq_false_of_lt h2]

theorem rep_zc : Rep zc 0 := ⟨by positivity, fun t => by simp [zc]⟩

theorem rep_true : Rep (fun _ => true) Mx := by
  refine ⟨Nat.sub_lt (by positivity) (by norm_num), fun t => ?_⟩
  rw [Nat.testBit_two_pow_sub_one]
  simp [t.isLt]

theorem rep_and {c d : Col} {v w : ℕ} (hv : Rep c v) (hw : Rep d w) :
    Rep (fun t => c t && d t) (v &&& w) :=
  ⟨Nat.and_lt_two_pow _ hw.1, fun t => by rw [Nat.testBit_and, hv.2, hw.2]⟩

theorem rep_or {c d : Col} {v w : ℕ} (hv : Rep c v) (hw : Rep d w) :
    Rep (fun t => c t || d t) (v ||| w) :=
  ⟨Nat.or_lt_two_pow hv.1 hw.1, fun t => by rw [Nat.testBit_or, hv.2, hw.2]⟩

theorem rep_not {c : Col} {v : ℕ} (hv : Rep c v) : Rep (fun t => !c t) (Mx ^^^ v) := by
  refine ⟨Nat.xor_lt_two_pow (Nat.sub_lt (by positivity) (by norm_num)) hv.1, fun t => ?_⟩
  rw [Nat.testBit_xor, hv.2, Nat.testBit_two_pow_sub_one]
  simp [t.isLt]

def T1 : ℕ := 10
def T2 : ℕ := 12
def T3 : ℕ := 42

def full (S : ℕ) : Bool := S.testBit T1 && S.testBit T2 && S.testBit T3

def miss (S : ℕ) : ℕ :=
  (if S.testBit T1 then 0 else 1) + (if S.testBit T2 then 0 else 1) + (if S.testBit T3 then 0 else 1)

def mem (S : ℕ) : List ℕ := (List.range (2 ^ B)).filter fun v => S.testBit v

def ins (S v : ℕ) : ℕ := S ||| (1 <<< v)

def monoL (S : ℕ) : List ℕ :=
  [Mx, 0] ++ (mem S).flatMap (fun a => (mem S).flatMap fun b => [a &&& b, a ||| b])

def notL (S : ℕ) : List ℕ := Mx :: (mem S).map (Mx ^^^ ·)

def bits (l : List ℕ) : ℕ := l.foldr (fun x acc => ins acc x) 0

def tryNew (n S A N : ℕ) (f : ℕ → ℕ → Bool) : Bool :=
  (List.range (2 ^ B)).any fun v => !S.testBit v &&
    ((A.testBit v && f n (ins S v)) || (decide (0 < n) && N.testBit v && f (n - 1) (ins S v)))

def ok : ℕ → ℕ → ℕ → Bool
  | 0, _, S => full S
  | k + 1, n, S => full S || (decide (miss S ≤ k + 1) &&
      (ok k n S || (decide (0 < n) && ok k (n - 1) S) ||
        tryNew n S (bits (monoL S)) (bits (notL S)) (ok k)))

theorem testBit_ins (S v t : ℕ) : (ins S v).testBit t = (S.testBit t || decide (t = v)) := by
  simp [ins, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, eq_comm]

theorem testBit_bits (l : List ℕ) (v : ℕ) : (bits l).testBit v = true ↔ v ∈ l := by
  induction l with
  | nil => simp [bits]
  | cons x l ih =>
    simp only [bits, List.foldr_cons] at ih ⊢
    rw [testBit_ins, Bool.or_eq_true, ih, decide_eq_true_eq, List.mem_cons]
    tauto

theorem miss_ins (S v : ℕ) (h12 : T1 ≠ T2) (h13 : T1 ≠ T3) (h23 : T2 ≠ T3) :
    miss S ≤ miss (ins S v) + 1 := by
  unfold miss
  simp only [testBit_ins]
  by_cases a : S.testBit T1 <;> by_cases b : S.testBit T2 <;> by_cases c : S.testBit T3 <;>
    by_cases e1 : T1 = v <;> by_cases e2 : T2 = v <;> by_cases e3 : T3 = v <;>
    simp_all <;> omega

theorem ok_miss : ∀ k n S, ok k n S = true → miss S ≤ k
  | 0, n, S, h => by
    simp only [ok, full, Bool.and_eq_true] at h
    simp [miss, h.1.1, h.1.2, h.2]
  | k + 1, n, S, h => by
    simp only [ok, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h | ⟨h, _⟩
    · simp only [full, Bool.and_eq_true] at h
      simp [miss, h.1.1, h.1.2, h.2]
    · exact h

def colStep (w : List Col) (g : Gate) : List Col :=
  w ++ [fun t => g.op.eval (g.inputs.map fun i => w.getD i zc t)]

def Inv (W : List Col) (S : ℕ) : Prop := ∀ i, ∃ v, Rep (W.getD i zc) v ∧ S.testBit v = true

def GoodGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def isNot (g : Gate) : Bool :=
  match g.op with
  | GateOp.not => true
  | _ => false

def nb (g : Gate) : ℕ := if isNot g then 1 else 0

theorem inv_snoc {W : List Col} {S : ℕ} (h : Inv W S) (c : Col) (v : ℕ) (hc : Rep c v)
    (hv : S.testBit v = true) : Inv (W ++ [c]) S := by
  intro i
  rcases lt_trichotomy i W.length with hi | rfl | hi
  · rw [List.getD_append _ _ _ _ hi]; exact h i
  · rw [List.getD_append_right _ _ _ _ (le_refl _)]; simpa using ⟨v, hc, hv⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    obtain ⟨u, hu, hs⟩ := h W.length
    rw [List.getD_eq_default _ _ (le_refl _)] at hu
    exact ⟨u, hu, hs⟩

theorem inv_ins {W : List Col} {S : ℕ} (h : Inv W S) (v : ℕ) : Inv W (ins S v) := by
  intro i
  obtain ⟨u, hu, hs⟩ := h i
  exact ⟨u, hu, by rw [testBit_ins, hs]; rfl⟩

theorem mem_mem {S v : ℕ} (hv : v < 2 ^ B) (h : S.testBit v = true) : v ∈ mem S := by
  simp [mem, hv, h]

theorem rep_false : Rep (fun _ => false) 0 := ⟨by positivity, fun t => by simp⟩

theorem new_mem {W : List Col} {S : ℕ} (h : Inv W S) (g : Gate) (hg : GoodGate g) (v : ℕ)
    (hv : Rep (fun t => g.op.eval (g.inputs.map fun i => W.getD i zc t)) v) :
    (isNot g = false ∧ v ∈ monoL S) ∨ (isNot g = true ∧ v ∈ notL S) ∨ S.testBit v = true := by
  obtain ⟨hop, hlen⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  obtain ⟨op, ins'⟩ := g
  simp only at hop hlen hv
  match ins', hlen with
  | [], _ =>
    rcases hop with rfl | rfl | rfl
    · have := rep_unique hv (by simpa [GateOp.eval] using rep_true)
      subst this; left; simp [monoL, isNot]
    · have := rep_unique hv (by simpa [GateOp.eval] using rep_false)
      subst this; left; simp [monoL, isNot]
    · have := rep_unique hv (by simpa [GateOp.eval] using rep_true)
      subst this; right; left; simp [notL, isNot]
  | [a], _ =>
    obtain ⟨va, ra, sa⟩ := h a
    rcases hop with rfl | rfl | rfl
    · have := rep_unique hv (by simpa [GateOp.eval] using ra)
      subst this; exact Or.inr (Or.inr sa)
    · have := rep_unique hv (by simpa [GateOp.eval] using ra)
      subst this; exact Or.inr (Or.inr sa)
    · have := rep_unique hv (by simpa [GateOp.eval] using rep_not ra)
      subst this; right; left
      exact ⟨rfl, List.mem_cons_of_mem _ (List.mem_map.2 ⟨va, mem_mem ra.1 sa, rfl⟩)⟩
  | [a, b], _ =>
    obtain ⟨va, ra, sa⟩ := h a
    obtain ⟨vb, rb, sb⟩ := h b
    rcases hop with rfl | rfl | rfl
    · have := rep_unique hv (by simpa [GateOp.eval] using rep_and ra rb)
      subst this; left
      refine ⟨rfl, ?_⟩
      simp only [monoL, List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨va, mem_mem ra.1 sa, vb, mem_mem rb.1 sb, by simp⟩
    · have := rep_unique hv (by simpa [GateOp.eval] using rep_or ra rb)
      subst this; left
      refine ⟨rfl, ?_⟩
      simp only [monoL, List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨va, mem_mem ra.1 sa, vb, mem_mem rb.1 sb, by simp⟩
    · have := rep_unique hv (by simpa [GateOp.eval] using rep_not ra)
      subst this; right; left
      exact ⟨rfl, List.mem_cons_of_mem _ (List.mem_map.2 ⟨va, mem_mem ra.1 sa, rfl⟩)⟩

theorem col_ex : ∀ c : Col, ∃ v, v < 2 ^ B ∧ ∀ t : Fin B, v.testBit t.val = c t := by
  decide +kernel

theorem sound (h12 : T1 ≠ T2) (h13 : T1 ≠ T3) (h23 : T2 ≠ T3) :
    ∀ (gs : List Gate) (hg : ∀ g ∈ gs, GoodGate g) (W : List Col) (S n : ℕ)
    (h : Inv W S) (hn : (gs.filter fun g => isNot g).length ≤ n)
    (ht : ∀ x ∈ [T1, T2, T3], ∃ i, Rep ((gs.foldl colStep W).getD i zc) x),
    ok gs.length n S = true
  | [], _, W, S, n, h, _, ht => by
    have hx : ∀ x ∈ [T1, T2, T3], S.testBit x = true := by
      intro x hx
      obtain ⟨i, hi⟩ := ht x hx
      obtain ⟨u, hu, hs⟩ := h i
      simp only [List.foldl_nil] at hi
      rw [rep_unique hi hu]; exact hs
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
    simp [ok, full, hx.1, hx.2.1, hx.2.2]
  | g :: gs, hg, W, S, n, h, hn, ht => by
    have hgg := hg g (by simp)
    have hrest : ∀ g ∈ gs, GoodGate g := fun g' hg' => hg g' (by simp [hg'])
    obtain ⟨v, hv⟩ : ∃ v, Rep (fun t => g.op.eval (g.inputs.map fun i => W.getD i zc t)) v :=
      col_ex _
    have ht' : ∀ x ∈ [T1, T2, T3], ∃ i, Rep ((gs.foldl colStep (colStep W g)).getD i zc) x := by
      simpa using ht
    have hn' : (gs.filter fun g => isNot g).length ≤ n - nb g := by
      simp only [List.filter_cons] at hn
      unfold nb
      split_ifs at hn ⊢ <;> (try simp only [List.length_cons] at hn) <;> omega
    have hpos : isNot g = true → 0 < n := by
      intro hi; simp only [List.filter_cons, hi, if_true, List.length_cons] at hn; omega
    simp only [List.length_cons, ok, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      List.any_eq_true, Bool.not_eq_true']
    by_cases hvS : S.testBit v = true
    · have hinv : Inv (colStep W g) S := inv_snoc h _ v hv hvS
      have r := sound h12 h13 h23 gs hrest (colStep W g) S _ hinv hn' ht'
      have hm := ok_miss _ _ _ r
      right
      refine ⟨by omega, Or.inl ?_⟩
      by_cases hi : isNot g = true
      · simp only [nb, hi, if_true] at r
        exact Or.inr ⟨hpos hi, r⟩
      · simp only [nb, hi, Bool.false_eq_true, if_false, Nat.sub_zero] at r
        exact Or.inl r
    · have hvS' : S.testBit v = false := by simpa using hvS
      have hinv : Inv (colStep W g) (ins S v) :=
        inv_snoc (inv_ins h v) _ v hv (by rw [testBit_ins]; simp)
      have r := sound h12 h13 h23 gs hrest (colStep W g) (ins S v) _ hinv hn' ht'
      have hm := ok_miss _ _ _ r
      have hmi := miss_ins S v h12 h13 h23
      right
      refine ⟨by omega, Or.inr ?_⟩
      unfold tryNew
      rw [List.any_eq_true]
      refine ⟨v, List.mem_range.2 hv.1, ?_⟩
      simp only [hvS', Bool.not_false, Bool.true_and, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_eq]
      rcases new_mem h g hgg v hv with ⟨hi, hc⟩ | ⟨hi, hc⟩ | hc
      · simp only [nb, hi, Bool.false_eq_true, if_false, Nat.sub_zero] at r
        exact Or.inl ⟨(testBit_bits _ _).2 hc, r⟩
      · simp only [nb, hi, if_true] at r
        exact Or.inr ⟨⟨hpos hi, (testBit_bits _ _).2 hc⟩, r⟩
      · exact absurd hc hvS

theorem fold_col (gs : List Gate) (W : List Col) (t : Fin B) (i : ℕ) :
    (gs.foldl colStep W).getD i zc t =
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (W.map (· t))).getD i false := by
  induction gs generalizing W with
  | nil =>
    simp only [List.foldl_nil]
    exact (List.getD_map (· t) (l := W) (d := zc) (n := i)).symm
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih]
    congr 2
    simp only [colStep, List.map_append, List.map_cons, List.map_nil]
    congr 3
    exact List.map_congr_left fun j _ => (List.getD_map (· t) (l := W) (d := zc) (n := j)).symm

def xs (t : Fin B) : List Bool :=
  (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true]

def W0 : List Col := List.ofFn (fun j : Fin 7 => fun t : Fin B => (xs t).getD j false)

def reps : List ℕ := [62, 60, 56, 48, 32, 0, 63]

def S0 : ℕ := 15060318633198616577

theorem W0_map (t : Fin B) : W0.map (· t) = xs t := by
  fin_cases t <;> decide

theorem inv0 : Inv W0 S0 := by
  intro i
  by_cases hi : i < 7
  · refine ⟨reps.getD i 0, ?_, ?_⟩ <;> interval_cases i <;> decide
  · refine ⟨0, ?_, by decide⟩
    rw [List.getD_eq_default _ _ (by simp [W0]; omega)]
    exact rep_zc

set_option maxRecDepth 100000 in
theorem search : ∀ m < 7, ok m 2 S0 = false := by
  decide +kernel

end PEqualNP.Outside.L_meta_50892

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_50892 in
theorem PEqualNP.Outside.L_meta_50892 : (¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (10 : Nat).testBit t.val ∧
    w.getD q.val false = (12 : Nat).testBit t.val ∧
    w.getD r.val false = (42 : Nat).testBit t.val)) := by
  rintro ⟨D, p, q, r, hfan, -, hnot, hsize, h⟩
  have hcol : ∀ i (t : Fin B), (D.gates.foldl colStep W0).getD i zc t =
      (D.wires (xs t)).getD i false := by
    intro i t
    rw [fold_col, W0_map]
    rfl
  have hrep : ∀ (i x : ℕ), x < 2 ^ B → (∀ t : Fin B, (D.wires (xs t)).getD i false = x.testBit t.val) →
      Rep ((D.gates.foldl colStep W0).getD i zc) x :=
    fun i x hx hb => ⟨hx, fun t => by rw [hcol, hb]⟩
  have ht : ∀ x ∈ [T1, T2, T3], ∃ i, Rep ((D.gates.foldl colStep W0).getD i zc) x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨p.val, hrep _ _ (by decide) fun t => (h t).1⟩
    · exact ⟨q.val, hrep _ _ (by decide) fun t => (h t).2.1⟩
    · exact ⟨r.val, hrep _ _ (by decide) fun t => (h t).2.2⟩
  have hn : (D.gates.filter fun g => isNot g).length ≤ 2 := by
    have e : (D.gates.filter fun g => isNot g) =
        D.gates.filter (fun g => @decide (g.op = GateOp.not)
          (PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq g.op GateOp.not)) := by
      apply List.filter_congr
      intro g _
      obtain ⟨op, ins⟩ := g
      cases op <;> rfl
    rw [e]
    exact hnot
  have hok := sound (by decide) (by decide) (by decide) D.gates hfan W0 S0 2 inv0 hn ht
  have hlt : D.gates.length < 7 := by
    have : D.size = D.gates.length := rfl
    omega
  rw [search _ hlt] at hok
  exact absurd hok (by decide)
