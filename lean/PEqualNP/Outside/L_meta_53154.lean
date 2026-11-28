import PEqualNP.Defs
import Mathlib.Data.List.Dedup
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs

namespace PEqualNP.Outside.L_meta_53154_aux

open PEqualNP.CircuitLowerBounds

abbrev B : ℕ := 5
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
  · have h1 : v < 2 ^ i := lt_of_lt_of_le hv.1 (Nat.pow_le_pow_right (by decide) (by omega))
    have h2 : w < 2 ^ i := lt_of_lt_of_le hw.1 (Nat.pow_le_pow_right (by decide) (by omega))
    rw [Nat.testBit_eq_false_of_lt h1, Nat.testBit_eq_false_of_lt h2]

theorem rep_zc : Rep zc 0 := ⟨by decide, fun t => by simp [zc]⟩

theorem rep_true : Rep (fun _ => true) Mx := by
  refine ⟨by decide, fun t => ?_⟩
  rw [Nat.testBit_two_pow_sub_one]
  simp [t.isLt]

theorem rep_and {c d : Col} {v w : ℕ} (hv : Rep c v) (hw : Rep d w) :
    Rep (fun t => c t && d t) (v &&& w) :=
  ⟨Nat.and_lt_two_pow _ hw.1, fun t => by rw [Nat.testBit_and, hv.2, hw.2]⟩

theorem rep_or {c d : Col} {v w : ℕ} (hv : Rep c v) (hw : Rep d w) :
    Rep (fun t => c t || d t) (v ||| w) :=
  ⟨Nat.or_lt_two_pow hv.1 hw.1, fun t => by rw [Nat.testBit_or, hv.2, hw.2]⟩

theorem rep_not {c : Col} {v : ℕ} (hv : Rep c v) : Rep (fun t => !c t) (Mx ^^^ v) := by
  refine ⟨Nat.xor_lt_two_pow (by decide) hv.1, fun t => ?_⟩
  rw [Nat.testBit_xor, hv.2, Nat.testBit_two_pow_sub_one]
  simp [t.isLt]

def T1 : ℕ := 6
def T2 : ℕ := 12
def T3 : ℕ := 29

def full (S : ℕ) : Bool := S.testBit T1 && S.testBit T2 && S.testBit T3

def miss (S : ℕ) : ℕ :=
  (if S.testBit T1 then 0 else 1) + (if S.testBit T2 then 0 else 1) + (if S.testBit T3 then 0 else 1)

def mem (S : ℕ) : List ℕ := (List.range (2 ^ B)).filter fun v => S.testBit v

def ins (S v : ℕ) : ℕ := S ||| (1 <<< v)

def monoL (S : ℕ) : List ℕ :=
  [Mx, 0] ++ (mem S).flatMap (fun a => (mem S).flatMap fun b => [a &&& b, a ||| b])

def notL (S : ℕ) : List ℕ := Mx :: (mem S).map (Mx ^^^ ·)

def bits (l : List ℕ) : ℕ := l.foldr (fun x acc => ins acc x) 0

theorem testBit_ins (S v t : ℕ) : (ins S v).testBit t = (S.testBit t || decide (t = v)) := by
  simp [ins, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, eq_comm]

theorem testBit_bits (l : List ℕ) (v : ℕ) : (bits l).testBit v = true ↔ v ∈ l := by
  induction l with
  | nil => simp [bits]
  | cons x l ih =>
    simp only [bits, List.foldr_cons] at ih ⊢
    rw [testBit_ins, Bool.or_eq_true, ih, decide_eq_true_eq, List.mem_cons]
    exact or_comm

theorem miss_ins (S v : ℕ) (h12 : T1 ≠ T2) (h13 : T1 ≠ T3) (h23 : T2 ≠ T3) :
    miss S ≤ miss (ins S v) + 1 := by
  unfold miss
  simp only [testBit_ins]
  by_cases a : S.testBit T1 <;> by_cases b : S.testBit T2 <;> by_cases c : S.testBit T3 <;>
    by_cases e1 : T1 = v <;> by_cases e2 : T2 = v <;> by_cases e3 : T3 = v <;>
    simp_all <;> omega

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

theorem rep_false : Rep (fun _ => false) 0 := ⟨by decide, fun t => by simp⟩

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

def step1 (p : ℕ × ℕ) : List (ℕ × ℕ) :=
  let S := p.1
  let n := p.2
  let A := bits (monoL S)
  let N := bits (notL S)
  [(S, n)] ++ (if 0 < n then [(S, n - 1)] else []) ++
    (List.range (2 ^ B)).flatMap fun v =>
      if S.testBit v then []
      else
        (if A.testBit v then [(ins S v, n)] else []) ++
        (if 0 < n && N.testBit v then [(ins S v, n - 1)] else [])

theorem mem_step1_dec {S n : ℕ} (hn : 0 < n) : (S, n - 1) ∈ step1 (S, n) := by
  simp [step1, hn]

theorem mem_step1_mono {S n v : ℕ} (hv : v < 2 ^ B) (hS : S.testBit v = false) (hA : v ∈ monoL S) :
    (ins S v, n) ∈ step1 (S, n) := by
  unfold step1
  rw [List.mem_append]
  refine Or.inr (List.mem_flatMap.2 ⟨v, List.mem_range.2 hv, ?_⟩)
  have hb : (bits (monoL S)).testBit v = true := (testBit_bits (monoL S) v).2 hA
  simp [hS, hb]

theorem mem_step1_not {S n v : ℕ} (hv : v < 2 ^ B) (hS : S.testBit v = false)
    (hn : 0 < n) (hN : v ∈ notL S) :
    (ins S v, n - 1) ∈ step1 (S, n) := by
  unfold step1
  rw [List.mem_append]
  refine Or.inr (List.mem_flatMap.2 ⟨v, List.mem_range.2 hv, ?_⟩)
  have hb : (bits (notL S)).testBit v = true := (testBit_bits (notL S) v).2 hN
  simp [hS, hn, hb]

def nextLayer (rem : ℕ) (L : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  ((L.flatMap step1).filter fun p => decide (miss p.1 ≤ rem)).dedup

theorem mem_nextLayer {rem : ℕ} {L : List (ℕ × ℕ)} {p q : ℕ × ℕ}
    (hp : p ∈ L) (hq : q ∈ step1 p) (hm : miss q.1 ≤ rem) :
    q ∈ nextLayer rem L := by
  unfold nextLayer
  rw [List.mem_dedup, List.mem_filter]
  exact ⟨List.mem_flatMap.2 ⟨p, hp, hq⟩, decide_eq_true hm⟩

theorem miss_foldl (h12 : T1 ≠ T2) (h13 : T1 ≠ T3) (h23 : T2 ≠ T3) :
    ∀ (gs : List Gate) (W : List Col) (S : ℕ),
    Inv W S →
    (∀ x ∈ [T1, T2, T3], ∃ i, Rep ((gs.foldl colStep W).getD i zc) x) →
    miss S ≤ gs.length
  | [], W, S, h, ht => by
    have hx : ∀ x ∈ [T1, T2, T3], S.testBit x = true := by
      intro x hx
      obtain ⟨i, hi⟩ := ht x hx
      obtain ⟨u, hu, hs⟩ := h i
      simp only [List.foldl_nil] at hi
      rw [rep_unique hi hu]; exact hs
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
    simp [miss, hx.1, hx.2.1, hx.2.2]
  | g :: gs, W, S, h, ht => by
    obtain ⟨v, hv⟩ : ∃ v, Rep (fun t => g.op.eval (g.inputs.map fun i => W.getD i zc t)) v :=
      col_ex _
    have hinv : Inv (colStep W g) (ins S v) :=
      inv_snoc (inv_ins h v) _ v hv (by rw [testBit_ins]; simp)
    have ht' : ∀ x ∈ [T1, T2, T3], ∃ i, Rep ((gs.foldl colStep (colStep W g)).getD i zc) x := by
      simpa using ht
    have hm' := miss_foldl h12 h13 h23 gs (colStep W g) (ins S v) hinv ht'
    have hmi := miss_ins S v h12 h13 h23
    simp only [List.length_cons]
    omega

def bfs : ℕ → List (ℕ × ℕ) → List (ℕ × ℕ)
  | 0, L => L.filter fun p => full p.1
  | k + 1, L => bfs k (nextLayer k L)

theorem sound_bfs (h12 : T1 ≠ T2) (h13 : T1 ≠ T3) (h23 : T2 ≠ T3) :
    ∀ (k : ℕ) (gs : List Gate), gs.length ≤ k →
    (∀ g ∈ gs, GoodGate g) →
    ∀ (W : List Col) (L : List (ℕ × ℕ)) (S n : ℕ),
    (S, n) ∈ L →
    Inv W S →
    (gs.filter fun g => isNot g).length ≤ n →
    (∀ x ∈ [T1, T2, T3], ∃ i, Rep ((gs.foldl colStep W).getD i zc) x) →
    ∃ q, q ∈ bfs k L
  | 0, gs, hlen, _, W, L, S, n, hmem, h, _, ht => by
    cases gs with
    | nil =>
      have hx : ∀ x ∈ [T1, T2, T3], S.testBit x = true := by
        intro x hx
        obtain ⟨i, hi⟩ := ht x hx
        obtain ⟨u, hu, hs⟩ := h i
        simp only [List.foldl_nil] at hi
        rw [rep_unique hi hu]; exact hs
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
      refine ⟨(S, n), ?_⟩
      simp [bfs, hmem, full, hx.1, hx.2.1, hx.2.2]
    | cons g gs' =>
      simp at hlen
  | k + 1, [], _, hg, W, L, S, n, hmem, h, hn, ht => by
    have hm0 : miss S ≤ ([].length : ℕ) := miss_foldl h12 h13 h23 [] W S h ht
    have hnext : (S, n) ∈ nextLayer k L :=
      mem_nextLayer hmem (by simp [step1]) (by dsimp only; simp at hm0; omega)
    exact sound_bfs h12 h13 h23 k [] (by simp) hg W (nextLayer k L) S n hnext h hn ht
  | k + 1, g :: gs, hlen, hg, W, L, S, n, hmem, h, hn, ht => by
    have hlen' : gs.length ≤ k := by simp at hlen; omega
    have hgg := hg g (by simp)
    have hrest : ∀ g' ∈ gs, GoodGate g' := fun g' hg' => hg g' (by simp [hg'])
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
    by_cases hvS : S.testBit v = true
    · have hinv : Inv (colStep W g) S := inv_snoc h _ v hv hvS
      have hm : miss S ≤ k := le_trans (miss_foldl h12 h13 h23 gs (colStep W g) S hinv ht') hlen'
      have hstep : (S, n - nb g) ∈ step1 (S, n) := by
        by_cases hi : isNot g = true
        · simp only [nb, hi, if_true]
          exact mem_step1_dec (hpos hi)
        · simp only [nb, hi, Bool.false_eq_true, if_false, Nat.sub_zero]
          simp [step1]
      have hnext : (S, n - nb g) ∈ nextLayer k L := mem_nextLayer hmem hstep hm
      exact sound_bfs h12 h13 h23 k gs hlen' hrest (colStep W g) (nextLayer k L) S (n - nb g) hnext hinv hn' ht'
    · have hvS' : S.testBit v = false := by simpa using hvS
      have hinv : Inv (colStep W g) (ins S v) :=
        inv_snoc (inv_ins h v) _ v hv (by rw [testBit_ins]; simp)
      have hm : miss (ins S v) ≤ k :=
        le_trans (miss_foldl h12 h13 h23 gs (colStep W g) (ins S v) hinv ht') hlen'
      have hstep : (ins S v, n - nb g) ∈ step1 (S, n) := by
        rcases new_mem h g hgg v hv with ⟨hi, hc⟩ | ⟨hi, hc⟩ | hc
        · simp only [nb, hi, Bool.false_eq_true, if_false, Nat.sub_zero]
          exact mem_step1_mono hv.1 hvS' hc
        · simp only [nb, hi, if_true]
          exact mem_step1_not hv.1 hvS' (hpos hi) hc
        · exact absurd hc hvS
      have hnext : (ins S v, n - nb g) ∈ nextLayer k L := mem_nextLayer hmem hstep hm
      exact sound_bfs h12 h13 h23 k gs hlen' hrest (colStep W g) (nextLayer k L) (ins S v) (n - nb g) hnext hinv hn' ht'

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
  (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false, true]

def W0 : List Col := List.ofFn (fun j : Fin 6 => fun t : Fin B => (xs t).getD j false)

def reps : List ℕ := [30, 28, 24, 16, 0, 31]

def S0 : ℕ := 3506503681

theorem W0_map (t : Fin B) : W0.map (· t) = xs t := by
  fin_cases t <;> decide

theorem inv0 : Inv W0 S0 := by
  intro i
  by_cases hi : i < 6
  · refine ⟨reps.getD i 0, ?_, ?_⟩ <;> interval_cases i <;> decide
  · refine ⟨0, ?_, by decide⟩
    rw [List.getD_eq_default _ _ (by simp [W0]; omega)]
    exact rep_zc

set_option maxRecDepth 100000 in
theorem search : bfs 6 [(S0, 2)] = [] := by
  decide +kernel

def wit3 : Circuit :=
  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.not, [2]⟩, ⟨GateOp.not, [3]⟩,
    ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.and, [1, 8]⟩], 9⟩

end PEqualNP.Outside.L_meta_53154_aux

theorem PEqualNP.Outside.L_meta_53154 : (
  let fits := fun (b : Nat) =>
    ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (6+D.size)),
      PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 D ∧
      PEqualNP.NotBracket.notCount D ≤ b ∧ D.size ≤ 6 ∧
      ∀ t : Fin 5,
        let xs := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true]
        let w := D.wires xs
        w.getD p.val false = (6 : Nat).testBit t.val ∧
        w.getD q.val false = (12 : Nat).testBit t.val ∧
        w.getD r.val false = (29 : Nat).testBit t.val
  fits 3 ∧ ¬ fits 2) := by
  dsimp only
  refine ⟨?_, ?_⟩
  · refine ⟨PEqualNP.Outside.L_meta_53154_aux.wit3, ⟨9, by decide⟩, ⟨11, by decide⟩, ⟨10, by decide⟩, ?_, ?_, by decide, by decide, ?_⟩
    · simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_53154_aux.wit3]
    · intro j hj
      change j < 6 at hj
      interval_cases j <;> simp [PEqualNP.MetaComplexity.NestedCover.gateAt, PEqualNP.Outside.L_meta_53154_aux.wit3]
    · decide
  · rintro ⟨D, p, q, r, hfan, -, hnot, hsize, h⟩
    have hcol : ∀ i (t : Fin PEqualNP.Outside.L_meta_53154_aux.B),
        (D.gates.foldl PEqualNP.Outside.L_meta_53154_aux.colStep PEqualNP.Outside.L_meta_53154_aux.W0).getD i PEqualNP.Outside.L_meta_53154_aux.zc t =
        (D.wires (PEqualNP.Outside.L_meta_53154_aux.xs t)).getD i false := by
      intro i t
      rw [PEqualNP.Outside.L_meta_53154_aux.fold_col, PEqualNP.Outside.L_meta_53154_aux.W0_map]
      rfl
    have hrep : ∀ (i x : ℕ), x < 2 ^ PEqualNP.Outside.L_meta_53154_aux.B →
        (∀ t : Fin PEqualNP.Outside.L_meta_53154_aux.B, (D.wires (PEqualNP.Outside.L_meta_53154_aux.xs t)).getD i false = x.testBit t.val) →
        PEqualNP.Outside.L_meta_53154_aux.Rep ((D.gates.foldl PEqualNP.Outside.L_meta_53154_aux.colStep PEqualNP.Outside.L_meta_53154_aux.W0).getD i PEqualNP.Outside.L_meta_53154_aux.zc) x :=
      fun i x hx hb => ⟨hx, fun t => by rw [hcol, hb]⟩
    have ht : ∀ x ∈ [PEqualNP.Outside.L_meta_53154_aux.T1, PEqualNP.Outside.L_meta_53154_aux.T2, PEqualNP.Outside.L_meta_53154_aux.T3],
        ∃ i, PEqualNP.Outside.L_meta_53154_aux.Rep ((D.gates.foldl PEqualNP.Outside.L_meta_53154_aux.colStep PEqualNP.Outside.L_meta_53154_aux.W0).getD i PEqualNP.Outside.L_meta_53154_aux.zc) x := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨p.val, hrep _ _ (by decide) fun t => (h t).1⟩
      · exact ⟨q.val, hrep _ _ (by decide) fun t => (h t).2.1⟩
      · exact ⟨r.val, hrep _ _ (by decide) fun t => (h t).2.2⟩
    have hn : (D.gates.filter fun g => PEqualNP.Outside.L_meta_53154_aux.isNot g).length ≤ 2 := by
      have e : (D.gates.filter fun g => PEqualNP.Outside.L_meta_53154_aux.isNot g) =
          D.gates.filter (fun g => @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not)
            (PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq g.op PEqualNP.CircuitLowerBounds.GateOp.not)) := by
        apply List.filter_congr
        intro g _
        obtain ⟨op, ins'⟩ := g
        cases op <;> rfl
      rw [e]
      exact hnot
    have hlen : D.gates.length ≤ 6 := by
      have : D.size = D.gates.length := rfl
      omega
    obtain ⟨q, hq⟩ := PEqualNP.Outside.L_meta_53154_aux.sound_bfs (by decide) (by decide) (by decide) 6 D.gates hlen hfan PEqualNP.Outside.L_meta_53154_aux.W0 [(PEqualNP.Outside.L_meta_53154_aux.S0, 2)] PEqualNP.Outside.L_meta_53154_aux.S0 2 (by simp) PEqualNP.Outside.L_meta_53154_aux.inv0 hn ht
    rw [PEqualNP.Outside.L_meta_53154_aux.search] at hq
    cases hq
