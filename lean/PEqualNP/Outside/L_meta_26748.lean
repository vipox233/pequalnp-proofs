import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_26748_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def matA (n : ℕ) (i j : Fin n) : Bool :=
  ((if i.val = 1 ∨ j.val = 1 then decide (i.val = 3 ∨ j.val = 3)
    else decide (i.val = 2 ∨ j.val = 2)) || decide (4 ≤ i.val ∧ i = j))

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma eval_eq (C : Circuit) (x : List Bool) :
    C.eval x = (C.gates.foldl stp x).getD C.output false := rfl

lemma foldl_len (gs : List Gate) (x : List Bool) :
    (gs.foldl stp x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, stp, List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_snoc (l : List Bool) (b : Bool) (w : ℕ) :
    (l ++ [b]).getD w false =
      if w < l.length then l.getD w false else if w = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

lemma getD_stp_eq (w : List Bool) (g : Gate) :
    (stp w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  rw [stp, getD_snoc]; simp

lemma getD_stp_lt (w : List Bool) (g : Gate) {i : ℕ} (hi : i < w.length) :
    (stp w g).getD i false = w.getD i false := by
  rw [stp, getD_snoc]; simp [hi]

lemma getD_stp_ne (w : List Bool) (g : Gate) {i : ℕ} (h1 : i ≠ w.length) :
    (stp w g).getD i false = w.getD i false := by
  rw [stp, getD_snoc]
  by_cases hlt : i < w.length
  · simp [hlt]
  · simp only [hlt, ite_false, h1]
    exact (List.getD_eq_default _ _ (by omega)).symm

lemma foldl_getD_lt (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (gs.foldl stp x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (stp x g) (by simp [stp]; omega), getD_stp_lt x g hw]

lemma oneEach_len {n : ℕ} (u v : Fin n) : (oneEach u v).length = n + n := by
  simp [oneEach]

lemma oneEach_getD_left {n : ℕ} (u v : Fin n) {k : ℕ} (hk : k < n) :
    (oneEach u v).getD k false = decide (u.val = k) := by
  unfold oneEach
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hk])]
  simp [hk, Fin.ext_iff, eq_comm]

lemma oneEach_getD_right {n : ℕ} (u v : Fin n) {k : ℕ} (hk : k < n) :
    (oneEach u v).getD (n + k) false = decide (v.val = k) := by
  unfold oneEach
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp [hk, Fin.ext_iff, eq_comm]

-- ============================================================
-- PART 1: Explicit (2n - 1)-gate FanInTwo circuit with unique NOT
-- ============================================================

def base7 (n : ℕ) : List Gate :=
  [ ⟨.or, [1, n + 1]⟩,
    ⟨.or, [2, n + 2]⟩,
    ⟨.or, [3, n + 3]⟩,
    ⟨.not, [2 * n + 0]⟩,
    ⟨.and, [2 * n + 0, 2 * n + 2]⟩,
    ⟨.and, [2 * n + 3, 2 * n + 1]⟩,
    ⟨.or, [2 * n + 4, 2 * n + 5]⟩ ]

def diagLoop (n : ℕ) : ℕ → List Gate
  | 0 => []
  | t + 1 =>
    diagLoop n t ++
      [ ⟨.and, [4 + t, n + (4 + t)]⟩,
        ⟨.or, [2 * n + 6 + 2 * t, 2 * n + 7 + 2 * t]⟩ ]

lemma diagLoop_len (n t : ℕ) : (diagLoop n t).length = 2 * t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [diagLoop, ih]; omega

lemma diagLoop_fanInTwo (n t : ℕ) :
    ∀ g ∈ diagLoop n t,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction t with
  | zero => intro g hg; cases hg
  | succ t ih =>
    intro g hg
    simp only [diagLoop, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | rfl | rfl
    · exact ih g h
    · simp
    · simp

lemma diagLoop_no_not (n t : ℕ) : ∀ g ∈ diagLoop n t, g.op ≠ GateOp.not := by
  induction t with
  | zero => intro g hg; cases hg
  | succ t ih =>
    intro g hg
    simp only [diagLoop, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | rfl | rfl
    · exact ih g h
    · simp
    · simp

lemma base7_eval (n : ℕ) (hn : 4 ≤ n) (i j : Fin n) :
    ((base7 n).foldl stp (oneEach i j)).getD (2 * n + 6) false =
      if i.val = 1 ∨ j.val = 1 then decide (i.val = 3 ∨ j.val = 3)
      else decide (i.val = 2 ∨ j.val = 2) := by
  set w0 := oneEach i j
  have hl0 : w0.length = 2 * n := by rw [oneEach_len]; omega
  have h1 : w0.getD 1 false = decide (i.val = 1) := oneEach_getD_left i j (by omega)
  have h2 : w0.getD 2 false = decide (i.val = 2) := oneEach_getD_left i j (by omega)
  have h3 : w0.getD 3 false = decide (i.val = 3) := oneEach_getD_left i j (by omega)
  have h1' : w0.getD (n + 1) false = decide (j.val = 1) := oneEach_getD_right i j (by omega)
  have h2' : w0.getD (n + 2) false = decide (j.val = 2) := oneEach_getD_right i j (by omega)
  have h3' : w0.getD (n + 3) false = decide (j.val = 3) := oneEach_getD_right i j (by omega)
  simp only [base7, List.foldl_cons, List.foldl_nil]
  set w1 := stp w0 ⟨.or, [1, n + 1]⟩
  set w2 := stp w1 ⟨.or, [2, n + 2]⟩
  set w3 := stp w2 ⟨.or, [3, n + 3]⟩
  set w4 := stp w3 ⟨.not, [2 * n + 0]⟩
  set w5 := stp w4 ⟨.and, [2 * n + 0, 2 * n + 2]⟩
  set w6 := stp w5 ⟨.and, [2 * n + 3, 2 * n + 1]⟩
  have hl1 : w1.length = 2 * n + 1 := by simp [w1, stp, hl0]
  have hl2 : w2.length = 2 * n + 2 := by simp [w2, stp, hl1]
  have hl3 : w3.length = 2 * n + 3 := by simp [w3, stp, hl2]
  have hl4 : w4.length = 2 * n + 4 := by simp [w4, stp, hl3]
  have hl5 : w5.length = 2 * n + 5 := by simp [w5, stp, hl4]
  have hl6 : w6.length = 2 * n + 6 := by simp [w6, stp, hl5]
  have g1 : ∀ k < 2 * n, w1.getD k false = w0.getD k false := fun k hk => getD_stp_lt w0 _ (by omega)
  have g2 : ∀ k < 2 * n + 1, w2.getD k false = w1.getD k false := fun k hk => getD_stp_lt w1 _ (by omega)
  have g3 : ∀ k < 2 * n + 2, w3.getD k false = w2.getD k false := fun k hk => getD_stp_lt w2 _ (by omega)
  have g4 : ∀ k < 2 * n + 3, w4.getD k false = w3.getD k false := fun k hk => getD_stp_lt w3 _ (by omega)
  have g5 : ∀ k < 2 * n + 4, w5.getD k false = w4.getD k false := fun k hk => getD_stp_lt w4 _ (by omega)
  have g6 : ∀ k < 2 * n + 5, w6.getD k false = w5.getD k false := fun k hk => getD_stp_lt w5 _ (by omega)
  have hv0 : w1.getD (2 * n) false = (decide (i.val = 1) || decide (j.val = 1)) := by
    rw [show 2 * n = w0.length by omega, getD_stp_eq]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false, h1, h1']
  have hv1 : w2.getD (2 * n + 1) false = (decide (i.val = 2) || decide (j.val = 2)) := by
    rw [show 2 * n + 1 = w1.length by omega, getD_stp_eq]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
    rw [g1 2 (by omega), g1 (n + 2) (by omega), h2, h2']
  have hv2 : w3.getD (2 * n + 2) false = (decide (i.val = 3) || decide (j.val = 3)) := by
    rw [show 2 * n + 2 = w2.length by omega, getD_stp_eq]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
    rw [g2 3 (by omega), g1 3 (by omega), g2 (n + 3) (by omega), g1 (n + 3) (by omega), h3, h3']
  have hv0_3 : w3.getD (2 * n) false = (decide (i.val = 1) || decide (j.val = 1)) := by
    rw [g3 _ (by omega), g2 _ (by omega), hv0]
  have hv3 : w4.getD (2 * n + 3) false = !(decide (i.val = 1) || decide (j.val = 1)) := by
    rw [show 2 * n + 3 = w3.length by omega, getD_stp_eq]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons, Nat.add_zero, hv0_3]
  have hv4 : w5.getD (2 * n + 4) false =
      ((decide (i.val = 1) || decide (j.val = 1)) && (decide (i.val = 3) || decide (j.val = 3))) := by
    rw [show 2 * n + 4 = w4.length by omega, getD_stp_eq]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true, Nat.add_zero]
    rw [g4 (2 * n) (by omega), hv0_3, g4 (2 * n + 2) (by omega), hv2]
  have hv5 : w6.getD (2 * n + 5) false =
      (!(decide (i.val = 1) || decide (j.val = 1)) && (decide (i.val = 2) || decide (j.val = 2))) := by
    rw [show 2 * n + 5 = w5.length by omega, getD_stp_eq]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
    rw [g5 (2 * n + 3) (by omega), hv3, g5 (2 * n + 1) (by omega), g4 (2 * n + 1) (by omega),
      g3 (2 * n + 1) (by omega), hv1]
  rw [show 2 * n + 6 = w6.length by omega, getD_stp_eq]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rw [g6 (2 * n + 4) (by omega), hv4, hv5]
  by_cases hi1 : i.val = 1 <;> by_cases hj1 : j.val = 1 <;>
    by_cases hi2 : i.val = 2 <;> by_cases hj2 : j.val = 2 <;>
    by_cases hi3 : i.val = 3 <;> by_cases hj3 : j.val = 3 <;>
    simp [hi1, hj1, hi2, hj2, hi3, hj3]

lemma diagLoop_eval (n : ℕ) (hn : 4 ≤ n) (i j : Fin n) :
    ∀ t : ℕ, 4 + t ≤ n →
      ((base7 n ++ diagLoop n t).foldl stp (oneEach i j)).getD (2 * n + 6 + 2 * t) false =
        (((if i.val = 1 ∨ j.val = 1 then decide (i.val = 3 ∨ j.val = 3)
          else decide (i.val = 2 ∨ j.val = 2)) || decide (4 ≤ i.val ∧ i.val < 4 + t ∧ i = j))) := by
  intro t
  induction t with
  | zero =>
    intro _
    simp only [diagLoop, List.append_nil, Nat.mul_zero, Nat.add_zero]
    rw [base7_eval n hn i j]
    have hf : ¬ (4 ≤ i.val ∧ i.val < 4 ∧ i = j) := by omega
    simp [hf]
  | succ t ih =>
    intro ht
    have hprev := ih (by omega)
    have hcat : base7 n ++ diagLoop n (t + 1) =
        (base7 n ++ diagLoop n t) ++
          [⟨.and, [4 + t, n + (4 + t)]⟩, ⟨.or, [2 * n + 6 + 2 * t, 2 * n + 7 + 2 * t]⟩] := by
      simp [diagLoop, List.append_assoc]
    rw [hcat, List.foldl_append]
    set w := (base7 n ++ diagLoop n t).foldl stp (oneEach i j)
    have hwlen : w.length = 2 * n + 7 + 2 * t := by
      simp only [w, foldl_len, oneEach_len, List.length_append, base7, List.length_cons,
        List.length_nil, diagLoop_len]
      omega
    have hlt1 : 4 + t < (oneEach i j).length := by rw [oneEach_len]; omega
    have hlt2 : n + (4 + t) < (oneEach i j).length := by rw [oneEach_len]; omega
    have hw1 : w.getD (4 + t) false = decide (i.val = 4 + t) := by
      rw [foldl_getD_lt _ _ _ hlt1, oneEach_getD_left i j (by omega)]
    have hw2 : w.getD (n + (4 + t)) false = decide (j.val = 4 + t) := by
      rw [foldl_getD_lt _ _ _ hlt2, oneEach_getD_right i j (by omega)]
    simp only [List.foldl_cons, List.foldl_nil]
    set wa := stp w ⟨.and, [4 + t, n + (4 + t)]⟩
    have hwalen : wa.length = 2 * n + 8 + 2 * t := by simp [wa, stp, hwlen]; omega
    have hwa_lt : ∀ k < 2 * n + 7 + 2 * t, wa.getD k false = w.getD k false :=
      fun k hk => getD_stp_lt w _ (by omega)
    have hva : wa.getD (2 * n + 7 + 2 * t) false = (decide (i.val = 4 + t) && decide (j.val = 4 + t)) := by
      rw [show 2 * n + 7 + 2 * t = w.length by omega, getD_stp_eq]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true, hw1, hw2]
    rw [show 2 * n + 6 + 2 * (t + 1) = wa.length by omega, getD_stp_eq]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
    rw [hwa_lt (2 * n + 6 + 2 * t) (by omega), hprev, hva, Bool.or_assoc]
    congr 1
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Fin.ext_iff]
    omega

lemma part1 (n : ℕ) (hn : 4 ≤ n) :
    ∃ C : Circuit, FanInTwo C ∧ Represents (matA n) C ∧ C.size = 2 * n - 1 ∧
      ∃! j : Fin C.gates.length, (C.gates.get j).op = GateOp.not := by
  let C : Circuit := ⟨base7 n ++ diagLoop n (n - 4), 2 * n + 6 + 2 * (n - 4)⟩
  have hlen : C.gates.length = 2 * n - 1 := by
    simp [C, base7, diagLoop_len]; omega
  refine ⟨C, ?_, ?_, hlen, ?_⟩
  · intro g hg
    simp only [C, List.mem_append] at hg
    rcases hg with hb | hd
    · simp only [base7, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · exact diagLoop_fanInTwo n (n - 4) g hd
  · intro i j
    rw [eval_eq]
    have h := diagLoop_eval n hn i j (n - 4) (by omega)
    simpa [C, matA, show 4 + (n - 4) = n by omega, i.isLt] using h
  · refine ⟨⟨3, by omega⟩, ?_, ?_⟩
    · simp [C, List.get_eq_getElem, base7]
    · intro k hk
      ext
      by_cases hlt : k.val < 7
      · have hk' : ((base7 n)[k.val]'(by simp [base7]; omega)).op = GateOp.not := by
          simpa [C, List.get_eq_getElem, List.getElem_append_left (show k.val < (base7 n).length by simp [base7]; omega)] using hk
        interval_cases hkv : k.val <;> simp [base7] at hk' ⊢
      · exfalso
        have hk_lt_n : k.val < 2 * n - 1 := hlen ▸ k.isLt
        have hklt : k.val - 7 < (diagLoop n (n - 4)).length := by rw [diagLoop_len]; omega
        have hmem : C.gates[k.val] ∈ diagLoop n (n - 4) := by
          have : C.gates[k.val] = (diagLoop n (n - 4))[k.val - 7]'hklt := by
            simp only [C]
            rw [List.getElem_append_right (show (base7 n).length ≤ k.val by simp [base7]; omega)]
            simp [base7]
          rw [this]
          exact List.getElem_mem _
        exact diagLoop_no_not n (n - 4) _ hmem (by simpa [List.get_eq_getElem] using hk)

-- ============================================================
-- PART 4: Explicit (4n - 7)-gate Monotone2 circuit
-- ============================================================

def orChain (base startIdx off : ℕ) : ℕ → List Gate
  | 0 => []
  | t + 1 =>
    let prev := if t = 0 then base else off + (t - 1)
    orChain base startIdx off t ++ [⟨.or, [prev, startIdx + t]⟩]

lemma orChain_len (base startIdx off t : ℕ) : (orChain base startIdx off t).length = t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [orChain, ih]

lemma orChain_mono2 (base startIdx off t : ℕ) :
    ∀ g ∈ orChain base startIdx off t,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  induction t with
  | zero => intro g hg; cases hg
  | succ t ih =>
    intro g hg
    simp only [orChain, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | rfl
    · exact ih g h
    · simp

lemma orChain_eval (base startIdx : ℕ) (x : List Bool) (_hb : base < x.length) :
    ∀ t : ℕ, startIdx + t ≤ x.length →
      ((orChain base startIdx x.length t).foldl stp x).getD
        (if t = 0 then base else x.length + (t - 1)) false =
        (x.getD base false || decide (∃ k < t, x.getD (startIdx + k) false = true)) := by
  intro t
  induction t with
  | zero => intro _; simp [orChain]
  | succ t ih =>
    intro ht
    have hprev := ih (by omega)
    simp only [orChain, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set w := (orChain base startIdx x.length t).foldl stp x
    have hwlen : w.length = x.length + t := by simp [w, foldl_len, orChain_len]
    have hst : w.getD (startIdx + t) false = x.getD (startIdx + t) false :=
      foldl_getD_lt _ _ _ (by omega)
    rw [show (if t + 1 = 0 then base else x.length + (t + 1 - 1)) = w.length by simp [hwlen]]
    rw [getD_stp_eq]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false, hprev, hst]
    rw [Bool.or_assoc]
    congr 1

def core9 (n wX wY off : ℕ) : List Gate :=
  [ ⟨.or, [1, n + 2]⟩,
    ⟨.or, [3, n + 3]⟩,
    ⟨.or, [2, n + 1]⟩,
    ⟨.or, [wY, off + 1]⟩,
    ⟨.and, [off + 2, off + 3]⟩,
    ⟨.or, [2, wX]⟩,
    ⟨.or, [off + 1, off + 5]⟩,
    ⟨.and, [off + 0, off + 6]⟩,
    ⟨.or, [off + 4, off + 7]⟩ ]

lemma core9_bool (a0 a1 a2 a3 b0 b1 b2 b3 : Bool) :
    ∀ u v : Fin 4,
      a0 = decide (u = 0) → a1 = decide (u = 1) → a2 = decide (u = 2) → a3 = decide (u = 3) →
      b0 = decide (v = 0) → b1 = decide (v = 1) → b2 = decide (v = 2) → b3 = decide (v = 3) →
      (((a2 || b1) && (b0 || (a3 || b3))) || ((a1 || b2) && ((a3 || b3) || (a2 || a0)))) =
        (if u.val = 1 ∨ v.val = 1 then decide (u.val = 3 ∨ v.val = 3)
         else decide (u.val = 2 ∨ v.val = 2)) := by
  intro u v h0 h1 h2 h3 g0 g1 g2 g3
  subst h0; subst h1; subst h2; subst h3; subst g0; subst g1; subst g2; subst g3
  revert u v
  decide

lemma core9_eval (n wX wY : ℕ) (hn : 4 ≤ n) (w : List Bool)
    (hwX : wX < w.length) (hwY : wY < w.length) (hwlen : 2 * n ≤ w.length)
    (i j : Fin n)
    (hX : w.getD wX false = decide (i.val = 0 ∨ 4 ≤ i.val))
    (hY : w.getD wY false = decide (j.val = 0 ∨ 4 ≤ j.val))
    (h1 : w.getD 1 false = decide (i.val = 1))
    (h2 : w.getD 2 false = decide (i.val = 2))
    (h3 : w.getD 3 false = decide (i.val = 3))
    (h1' : w.getD (n + 1) false = decide (j.val = 1))
    (h2' : w.getD (n + 2) false = decide (j.val = 2))
    (h3' : w.getD (n + 3) false = decide (j.val = 3)) :
    ((core9 n wX wY w.length).foldl stp w).getD (w.length + 8) false =
      if i.val = 1 ∨ j.val = 1 then decide (i.val = 3 ∨ j.val = 3)
      else decide (i.val = 2 ∨ j.val = 2) := by
  set off := w.length
  simp only [core9, List.foldl_cons, List.foldl_nil]
  set s1 := stp w ⟨.or, [1, n + 2]⟩
  set s2 := stp s1 ⟨.or, [3, n + 3]⟩
  set s3 := stp s2 ⟨.or, [2, n + 1]⟩
  set s4 := stp s3 ⟨.or, [wY, off + 1]⟩
  set s5 := stp s4 ⟨.and, [off + 2, off + 3]⟩
  set s6 := stp s5 ⟨.or, [2, wX]⟩
  set s7 := stp s6 ⟨.or, [off + 1, off + 5]⟩
  set s8 := stp s7 ⟨.and, [off + 0, off + 6]⟩
  have hl1 : s1.length = off + 1 := by simp [s1, stp, off]
  have hl2 : s2.length = off + 2 := by simp [s2, stp, hl1]
  have hl3 : s3.length = off + 3 := by simp [s3, stp, hl2]
  have hl4 : s4.length = off + 4 := by simp [s4, stp, hl3]
  have hl5 : s5.length = off + 5 := by simp [s5, stp, hl4]
  have hl6 : s6.length = off + 6 := by simp [s6, stp, hl5]
  have hl7 : s7.length = off + 7 := by simp [s7, stp, hl6]
  have hl8 : s8.length = off + 8 := by simp [s8, stp, hl7]
  have g1 : ∀ k < off, s1.getD k false = w.getD k false := fun k hk => getD_stp_lt w _ hk
  have g2 : ∀ k < off + 1, s2.getD k false = s1.getD k false := fun k hk => getD_stp_lt s1 _ (by omega)
  have g3 : ∀ k < off + 2, s3.getD k false = s2.getD k false := fun k hk => getD_stp_lt s2 _ (by omega)
  have g4 : ∀ k < off + 3, s4.getD k false = s3.getD k false := fun k hk => getD_stp_lt s3 _ (by omega)
  have g5 : ∀ k < off + 4, s5.getD k false = s4.getD k false := fun k hk => getD_stp_lt s4 _ (by omega)
  have g6 : ∀ k < off + 5, s6.getD k false = s5.getD k false := fun k hk => getD_stp_lt s5 _ (by omega)
  have g7 : ∀ k < off + 6, s7.getD k false = s6.getD k false := fun k hk => getD_stp_lt s6 _ (by omega)
  have g8 : ∀ k < off + 7, s8.getD k false = s7.getD k false := fun k hk => getD_stp_lt s7 _ (by omega)
  have hv0 : s1.getD off false = (decide (i.val = 1) || decide (j.val = 2)) := by
    rw [show off = w.length from rfl, getD_stp_eq]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false, h1, h2']
  have hv1 : s2.getD (off + 1) false = (decide (i.val = 3) || decide (j.val = 3)) := by
    rw [show off + 1 = s1.length by omega, getD_stp_eq]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
    rw [g1 3 (by omega), g1 (n + 3) (by omega), h3, h3']
  have hv2 : s3.getD (off + 2) false = (decide (i.val = 2) || decide (j.val = 1)) := by
    rw [show off + 2 = s2.length by omega, getD_stp_eq]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
    rw [g2 2 (by omega), g1 2 (by omega), g2 (n + 1) (by omega), g1 (n + 1) (by omega), h2, h1']
  have hv1_3 : s3.getD (off + 1) false = (decide (i.val = 3) || decide (j.val = 3)) := by
    rw [g3 (off + 1) (by omega), hv1]
  have hv3 : s4.getD (off + 3) false = (decide (j.val = 0 ∨ 4 ≤ j.val) || (decide (i.val = 3) || decide (j.val = 3))) := by
    rw [show off + 3 = s3.length by omega, getD_stp_eq]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
    rw [g3 wY (by omega), g2 wY (by omega), g1 wY hwY, hY, hv1_3]
  have hv4 : s5.getD (off + 4) false =
      ((decide (i.val = 2) || decide (j.val = 1)) &&
       (decide (j.val = 0 ∨ 4 ≤ j.val) || (decide (i.val = 3) || decide (j.val = 3)))) := by
    rw [show off + 4 = s4.length by omega, getD_stp_eq]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
    rw [g4 (off + 2) (by omega), hv2, hv3]
  have hv5 : s6.getD (off + 5) false = (decide (i.val = 2) || decide (i.val = 0 ∨ 4 ≤ i.val)) := by
    rw [show off + 5 = s5.length by omega, getD_stp_eq]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
    rw [g5 2 (by omega), g4 2 (by omega), g3 2 (by omega), g2 2 (by omega), g1 2 (by omega), h2,
      g5 wX (by omega), g4 wX (by omega), g3 wX (by omega), g2 wX (by omega), g1 wX hwX, hX]
  have hv6 : s7.getD (off + 6) false =
      ((decide (i.val = 3) || decide (j.val = 3)) || (decide (i.val = 2) || decide (i.val = 0 ∨ 4 ≤ i.val))) := by
    rw [show off + 6 = s6.length by omega, getD_stp_eq]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
    rw [g6 (off + 1) (by omega), g5 (off + 1) (by omega), g4 (off + 1) (by omega), hv1_3, hv5]
  have hv7 : s8.getD (off + 7) false =
      ((decide (i.val = 1) || decide (j.val = 2)) &&
       ((decide (i.val = 3) || decide (j.val = 3)) || (decide (i.val = 2) || decide (i.val = 0 ∨ 4 ≤ i.val)))) := by
    rw [show off + 7 = s7.length by omega, getD_stp_eq]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true, Nat.add_zero]
    rw [g7 off (by omega), g6 off (by omega), g5 off (by omega), g4 off (by omega),
      g3 off (by omega), g2 off (by omega), hv0, hv6]
  rw [show off + 8 = s8.length by omega, getD_stp_eq]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rw [g8 (off + 4) (by omega), g7 (off + 4) (by omega), g6 (off + 4) (by omega), hv4, hv7]
  let u : Fin 4 := if hi : i.val < 4 then ⟨i.val, hi⟩ else ⟨0, by omega⟩
  let v : Fin 4 := if hj : j.val < 4 then ⟨j.val, hj⟩ else ⟨0, by omega⟩
  have hu0 : decide (i.val = 0 ∨ 4 ≤ i.val) = decide (u = 0) := by
    simp only [u]; split_ifs with hi <;> (simp [Fin.ext_iff]; omega)
  have hu1 : decide (i.val = 1) = decide (u = 1) := by
    simp only [u]; split_ifs with hi; simp [Fin.ext_iff]; simp; omega
  have hu2 : decide (i.val = 2) = decide (u = 2) := by
    simp only [u]; split_ifs with hi; simp [Fin.ext_iff]; simp [Fin.ext_iff]; omega
  have hu3 : decide (i.val = 3) = decide (u = 3) := by
    simp only [u]; split_ifs with hi; simp [Fin.ext_iff]; simp [Fin.ext_iff]; omega
  have hv0' : decide (j.val = 0 ∨ 4 ≤ j.val) = decide (v = 0) := by
    simp only [v]; split_ifs with hj <;> (simp [Fin.ext_iff]; omega)
  have hv1' : decide (j.val = 1) = decide (v = 1) := by
    simp only [v]; split_ifs with hj; simp [Fin.ext_iff]; simp; omega
  have hv2' : decide (j.val = 2) = decide (v = 2) := by
    simp only [v]; split_ifs with hj; simp [Fin.ext_iff]; simp [Fin.ext_iff]; omega
  have hv3' : decide (j.val = 3) = decide (v = 3) := by
    simp only [v]; split_ifs with hj; simp [Fin.ext_iff]; simp [Fin.ext_iff]; omega
  have hres := core9_bool _ _ _ _ _ _ _ _ u v hu0 hu1 hu2 hu3 hv0' hv1' hv2' hv3'
  rw [hres]
  have h1eq : (u.val = 1 ∨ v.val = 1) ↔ (i.val = 1 ∨ j.val = 1) := by
    simp only [u, v]; split_ifs <;> simp <;> omega
  have h2eq : (u.val = 2 ∨ v.val = 2) ↔ (i.val = 2 ∨ j.val = 2) := by
    simp only [u, v]; split_ifs <;> simp <;> omega
  have h3eq : (u.val = 3 ∨ v.val = 3) ↔ (i.val = 3 ∨ j.val = 3) := by
    simp only [u, v]; split_ifs <;> simp <;> omega
  by_cases h : i.val = 1 ∨ j.val = 1
  · simp [h, h1eq.mpr h, h3eq]
  · simp [h, mt h1eq.mp h, h2eq]

def diagLoopAt (n baseOut : ℕ) : ℕ → List Gate
  | 0 => []
  | t + 1 =>
    diagLoopAt n baseOut t ++
      [ ⟨.and, [4 + t, n + (4 + t)]⟩,
        ⟨.or, [baseOut + 2 * t, baseOut + 1 + 2 * t]⟩ ]

lemma diagLoopAt_len (n baseOut t : ℕ) : (diagLoopAt n baseOut t).length = 2 * t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [diagLoopAt, ih]; omega

lemma diagLoopAt_mono2 (n baseOut t : ℕ) :
    ∀ g ∈ diagLoopAt n baseOut t,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  induction t with
  | zero => intro g hg; cases hg
  | succ t ih =>
    intro g hg
    simp only [diagLoopAt, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | rfl | rfl
    · exact ih g h
    · simp
    · simp

lemma diagLoopAt_eval (n : ℕ) (w0 : List Bool) (i j : Fin n) (hw0 : 2 * n ≤ w0.length)
    (hleft : ∀ k < n, w0.getD k false = decide (i.val = k))
    (hright : ∀ k < n, w0.getD (n + k) false = decide (j.val = k))
    (h0pos : 0 < w0.length) :
    ∀ t : ℕ, 4 + t ≤ n →
      ((diagLoopAt n (w0.length - 1) t).foldl stp w0).getD (w0.length - 1 + 2 * t) false =
        (w0.getD (w0.length - 1) false || decide (4 ≤ i.val ∧ i.val < 4 + t ∧ i = j)) := by
  intro t
  induction t with
  | zero =>
    intro _
    simp only [diagLoopAt, List.foldl_nil, Nat.mul_zero, Nat.add_zero]
    have hf : ¬ (4 ≤ i.val ∧ i.val < 4 ∧ i = j) := by omega
    simp [hf]
  | succ t ih =>
    intro ht
    have hprev := ih (by omega)
    simp only [diagLoopAt, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set w := (diagLoopAt n (w0.length - 1) t).foldl stp w0
    have hwlen : w.length = w0.length + 2 * t := by simp [w, foldl_len, diagLoopAt_len]
    have hw1 : w.getD (4 + t) false = decide (i.val = 4 + t) := by
      rw [foldl_getD_lt _ _ _ (by omega), hleft (4 + t) (by omega)]
    have hw2 : w.getD (n + (4 + t)) false = decide (j.val = 4 + t) := by
      rw [foldl_getD_lt _ _ _ (by omega), hright (4 + t) (by omega)]
    set wa := stp w ⟨.and, [4 + t, n + (4 + t)]⟩
    have hwalen : wa.length = w0.length + 2 * t + 1 := by simp [wa, stp, hwlen]
    have hwa_lt : ∀ k < w0.length + 2 * t, wa.getD k false = w.getD k false :=
      fun k hk => getD_stp_lt w _ (by omega)
    have hva : wa.getD (w0.length - 1 + 1 + 2 * t) false = (decide (i.val = 4 + t) && decide (j.val = 4 + t)) := by
      rw [show w0.length - 1 + 1 + 2 * t = w.length by omega, getD_stp_eq]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true, hw1, hw2]
    rw [show w0.length - 1 + 2 * (t + 1) = wa.length by omega, getD_stp_eq]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
    rw [hwa_lt (w0.length - 1 + 2 * t) (by omega), hprev, hva, Bool.or_assoc]
    congr 1
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Fin.ext_iff]
    omega

lemma part4 (n : ℕ) (hn : 4 ≤ n) : RepSizeAtMost (matA n) (4 * n - 7) := by
  let t := n - 4
  let gsX := orChain 0 4 (2 * n) t
  let gsY := orChain n (n + 4) (2 * n + t) t
  let wX := if t = 0 then 0 else 2 * n + (t - 1)
  let wY := if t = 0 then n else 2 * n + t + (t - 1)
  let gsC := core9 n wX wY (2 * n + 2 * t)
  let gsD := diagLoopAt n (2 * n + 2 * t + 8) t
  let C : Circuit := ⟨gsX ++ gsY ++ gsC ++ gsD, 2 * n + 2 * t + 8 + 2 * t⟩
  refine ⟨C, ?_, ?_, ?_⟩
  · intro g hg
    simp only [C, List.mem_append] at hg
    rcases hg with ((h | h) | h) | h
    · exact orChain_mono2 0 4 (2 * n) t g h
    · exact orChain_mono2 n (n + 4) (2 * n + t) t g h
    · simp only [gsC, core9, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · exact diagLoopAt_mono2 n (2 * n + 2 * t + 8) t g h
  · simp [Circuit.size, C, gsX, gsY, gsC, gsD, orChain_len, core9, diagLoopAt_len, t]
    omega
  · intro i j
    rw [eval_eq]
    simp only [C, List.foldl_append]
    set x0 := oneEach i j
    have hx0len : x0.length = 2 * n := by simp [x0, oneEach_len]; omega
    set w1 := gsX.foldl stp x0
    have hw1len : w1.length = 2 * n + t := by simp [w1, foldl_len, hx0len, gsX, orChain_len]
    have hw1X : w1.getD wX false = decide (i.val = 0 ∨ 4 ≤ i.val) := by
      have h := orChain_eval 0 4 x0 (by omega) t (by omega)
      simp only [hx0len] at h
      change w1.getD wX false = _
      rw [h, oneEach_getD_left i j (by omega)]
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      constructor
      · rintro (h0 | ⟨k, hk, hv⟩)
        · exact Or.inl h0
        · rw [oneEach_getD_left i j (by omega)] at hv
          have := of_decide_eq_true hv
          exact Or.inr (by omega)
      · rintro (h0 | h4)
        · exact Or.inl h0
        · refine Or.inr ⟨i.val - 4, by omega, ?_⟩
          rw [oneEach_getD_left i j (by omega)]
          simp [show 4 + (i.val - 4) = i.val by omega]
    set w2 := gsY.foldl stp w1
    have hw2len : w2.length = 2 * n + 2 * t := by
      simp [w2, foldl_len, hw1len, gsY, orChain_len]; omega
    have hw2X : w2.getD wX false = decide (i.val = 0 ∨ 4 ≤ i.val) := by
      rw [foldl_getD_lt _ _ _ (by simp only [wX, hw1len]; split_ifs <;> omega), hw1X]
    have hw2Y : w2.getD wY false = decide (j.val = 0 ∨ 4 ≤ j.val) := by
      have h := orChain_eval n (n + 4) w1 (by omega) t (by omega)
      simp only [hw1len] at h
      change w2.getD wY false = _
      have hx0n : x0.getD n false = decide (j.val = 0) := by
        simpa using oneEach_getD_right i j (show 0 < n by omega)
      rw [h, foldl_getD_lt _ _ _ (by omega), hx0n]
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      constructor
      · rintro (h0 | ⟨k, hk, hv⟩)
        · exact Or.inl h0
        · rw [foldl_getD_lt _ _ _ (by omega), show n + 4 + k = n + (4 + k) by omega,
              oneEach_getD_right i j (by omega)] at hv
          have := of_decide_eq_true hv
          exact Or.inr (by omega)
      · rintro (h0 | h4)
        · exact Or.inl h0
        · refine Or.inr ⟨j.val - 4, by omega, ?_⟩
          rw [foldl_getD_lt _ _ _ (by omega), show n + 4 + (j.val - 4) = n + j.val by omega,
              oneEach_getD_right i j j.isLt]
          simp
    have hw2_in : ∀ k < 2 * n, w2.getD k false = x0.getD k false := by
      intro k hk
      rw [foldl_getD_lt _ _ _ (by omega), foldl_getD_lt _ _ _ (by omega)]
    set w3 := gsC.foldl stp w2
    have hw3len : w3.length = 2 * n + 2 * t + 9 := by
      simp only [w3, foldl_len, hw2len, gsC, core9, List.length_cons, List.length_nil]
    have hw3_val : w3.getD (2 * n + 2 * t + 8) false =
        if i.val = 1 ∨ j.val = 1 then decide (i.val = 3 ∨ j.val = 3)
        else decide (i.val = 2 ∨ j.val = 2) := by
      have hc := core9_eval n wX wY hn w2
        (by simp only [wX, hw2len]; split_ifs <;> omega)
        (by simp only [wY, hw2len]; split_ifs <;> omega)
        (by omega) i j hw2X hw2Y
        (by rw [hw2_in 1 (by omega), oneEach_getD_left i j (by omega)])
        (by rw [hw2_in 2 (by omega), oneEach_getD_left i j (by omega)])
        (by rw [hw2_in 3 (by omega), oneEach_getD_left i j (by omega)])
        (by rw [hw2_in (n + 1) (by omega), oneEach_getD_right i j (by omega)])
        (by rw [hw2_in (n + 2) (by omega), oneEach_getD_right i j (by omega)])
        (by rw [hw2_in (n + 3) (by omega), oneEach_getD_right i j (by omega)])
      simpa only [hw2len, w3, gsC] using hc
    have hd := diagLoopAt_eval n w3 i j (by omega)
      (fun k hk => by rw [foldl_getD_lt _ _ _ (by omega), hw2_in k (by omega), oneEach_getD_left i j hk])
      (fun k hk => by rw [foldl_getD_lt _ _ _ (by omega), hw2_in (n + k) (by omega), oneEach_getD_right i j hk])
      (by omega) t (by omega)
    have hsub : w3.length - 1 = 2 * n + 2 * t + 8 := by omega
    rw [hsub] at hd
    rw [hd, hw3_val]
    simp [matA, show 4 + t = n by omega, i.isLt]

-- ============================================================
-- PART 2: General FanInTwo Lower Bound (2n - 1 <= C.size)
-- ============================================================

def effInputs (g : Gate) : List ℕ :=
  match g.op with
  | .not => match g.inputs with | [] => [] | a :: _ => [a]
  | _ => g.inputs

lemma effInputs_eval (g : Gate) (w1 w2 : List Bool)
    (h : ∀ i ∈ effInputs g, w1.getD i false = w2.getD i false) :
    g.op.eval (g.inputs.map fun i => w1.getD i false) =
      g.op.eval (g.inputs.map fun i => w2.getD i false) := by
  cases hop : g.op with
  | not =>
    cases hin : g.inputs with
    | nil => rfl
    | cons a tl =>
      simp only [GateOp.eval, List.map_cons, List.headD_cons]
      have ha : a ∈ effInputs g := by simp [effInputs, hop, hin]
      rw [h a ha]
  | and =>
    congr 1
    apply List.map_congr_left
    intro i hi
    exact h i (by simp [effInputs, hop, hi])
  | or =>
    congr 1
    apply List.map_congr_left
    intro i hi
    exact h i (by simp [effInputs, hop, hi])
  | mod _ =>
    congr 1
    apply List.map_congr_left
    intro i hi
    exact h i (by simp [effInputs, hop, hi])
  | maj =>
    congr 1
    apply List.map_congr_left
    intro i hi
    exact h i (by simp [effInputs, hop, hi])

def DependsOn (N : ℕ) (f : List Bool → Bool) (R : Finset ℕ) : Prop :=
  ∀ x y : List Bool, x.length = N → y.length = N →
    (∀ i ∈ R, x.getD i false = y.getD i false) → f x = f y

def UnateOn (N : ℕ) (f : List Bool → Bool) (R : Finset ℕ) (sgn : ℕ → Bool) : Prop :=
  ∀ x y : List Bool, x.length = N → y.length = N →
    (∀ i ∈ R, if sgn i then (x.getD i false = true → y.getD i false = true)
              else (y.getD i false = true → x.getD i false = true)) →
    f x = true → f y = true

lemma mono_step_andOr (g : Gate) (hop : g.op = .and ∨ g.op = .or) (x y : List Bool) (s : Bool)
    (h : ∀ i ∈ g.inputs, if s then (x.getD i false = true → y.getD i false = true)
                         else (y.getD i false = true → x.getD i false = true)) :
    if s then
      (g.op.eval (g.inputs.map fun i => x.getD i false) = true →
       g.op.eval (g.inputs.map fun i => y.getD i false) = true)
    else
      (g.op.eval (g.inputs.map fun i => y.getD i false) = true →
       g.op.eval (g.inputs.map fun i => x.getD i false) = true) := by
  cases s with
  | true =>
    simp only [ite_true] at h ⊢
    rcases hop with h1 | h1 <;> rw [h1]
    · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
      intro hx b hb
      rcases hb with ⟨i, hi, rfl⟩
      exact h i hi (hx _ ⟨i, hi, rfl⟩)
    · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
      rintro ⟨_, ⟨i, hi, rfl⟩, hxi⟩
      exact ⟨_, ⟨i, hi, rfl⟩, h i hi hxi⟩
  | false =>
    simp only [Bool.false_eq_true, ite_false] at h ⊢
    rcases hop with h1 | h1 <;> rw [h1]
    · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
      intro hy b hb
      rcases hb with ⟨i, hi, rfl⟩
      exact h i hi (hy _ ⟨i, hi, rfl⟩)
    · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
      rintro ⟨_, ⟨i, hi, rfl⟩, hyi⟩
      exact ⟨_, ⟨i, hi, rfl⟩, h i hi hyi⟩

def ConeInv (N s : ℕ) (f : List Bool → Bool) : Prop :=
  (∃ R : Finset ℕ, R.card ≤ s + 1 ∧ UnateOn N f R (fun _ => true)) ∨
  (∃ (R : Finset ℕ) (sgn : ℕ → Bool), R.card ≤ s ∧ UnateOn N f R sgn) ∨
  (∃ R : Finset ℕ, R.card + 1 ≤ s ∧ DependsOn N f R)

lemma coneInv_step (N s : ℕ) (g : Gate) (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (f : List Bool → Bool) (hf : ConeInv (N + 1) s f) :
    ConeInv N (s + 1) (fun x => f (stp x g)) := by
  have hop_mem : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hg.1
  rcases hf with ⟨R, hRc, hMono⟩ | ⟨R, sgn, hRc, hUn⟩ | ⟨R, hRc, hDep⟩
  · -- Case A: MonoOn (sgn = const true), R.card <= s + 1
    by_cases ht : N ∈ R
    · rcases hop_mem with hnot | hnot | hnot
      · -- g.op = .and
        let R' := R.erase N ∪ g.inputs.toFinset
        refine Or.inl ⟨R', ?_, ?_⟩
        · have h1 : R'.card ≤ (R.erase N).card + g.inputs.toFinset.card :=
            Finset.card_union_le (R.erase N) g.inputs.toFinset
          have h2 := Finset.card_erase_of_mem ht
          have h3 := List.toFinset_card_le g.inputs
          have hpos : 0 < R.card := Finset.card_pos.mpr ⟨N, ht⟩
          omega
        · intro x y hx hy hxy
          apply hMono (stp x g) (stp y g) (by simp [stp, hx]) (by simp [stp, hy])
          intro i hi
          simp only [ite_true]
          by_cases hiN : i = N
          · subst hiN
            rw [← hx, getD_stp_eq, hx, ← hy, getD_stp_eq]
            exact mono_step_andOr g (Or.inl hnot) x y true (fun a ha =>
              hxy a (Finset.mem_union_right _ (List.mem_toFinset.mpr ha)))
          · have hiR' : i ∈ R' := Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hiN, hi⟩)
            rw [getD_stp_ne x g (by omega), getD_stp_ne y g (by omega)]
            exact hxy i hiR'
      · -- g.op = .or
        let R' := R.erase N ∪ g.inputs.toFinset
        refine Or.inl ⟨R', ?_, ?_⟩
        · have h1 : R'.card ≤ (R.erase N).card + g.inputs.toFinset.card :=
            Finset.card_union_le (R.erase N) g.inputs.toFinset
          have h2 := Finset.card_erase_of_mem ht
          have h3 := List.toFinset_card_le g.inputs
          have hpos : 0 < R.card := Finset.card_pos.mpr ⟨N, ht⟩
          omega
        · intro x y hx hy hxy
          apply hMono (stp x g) (stp y g) (by simp [stp, hx]) (by simp [stp, hy])
          intro i hi
          simp only [ite_true]
          by_cases hiN : i = N
          · subst hiN
            rw [← hx, getD_stp_eq, hx, ← hy, getD_stp_eq]
            exact mono_step_andOr g (Or.inr hnot) x y true (fun a ha =>
              hxy a (Finset.mem_union_right _ (List.mem_toFinset.mpr ha)))
          · have hiR' : i ∈ R' := Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hiN, hi⟩)
            rw [getD_stp_ne x g (by omega), getD_stp_ne y g (by omega)]
            exact hxy i hiR'
      · -- g.op = .not
        cases hin : g.inputs with
        | nil =>
          refine Or.inr (Or.inr ⟨R.erase N, ?_, ?_⟩)
          · have h2 := Finset.card_erase_of_mem ht
            have hpos : 0 < R.card := Finset.card_pos.mpr ⟨N, ht⟩
            omega
          · intro x y hx hy hxy
            have heq : ∀ i ∈ R, (stp x g).getD i false = (stp y g).getD i false := by
              intro i hi
              by_cases hiN : i = N
              · subst hiN
                rw [← hx, getD_stp_eq, hx, ← hy, getD_stp_eq, hnot, hin]
                rfl
              · rw [getD_stp_ne x g (by omega), getD_stp_ne y g (by omega)]
                exact hxy i (Finset.mem_erase.mpr ⟨hiN, hi⟩)
            apply Bool.eq_iff_iff.mpr
            constructor
            · exact hMono _ _ (by simp [stp, hx]) (by simp [stp, hy])
                (fun i hi => by simp only [ite_true]; intro h; rwa [← heq i hi])
            · exact hMono _ _ (by simp [stp, hy]) (by simp [stp, hx])
                (fun i hi => by simp only [ite_true]; intro h; rwa [heq i hi])
        | cons a tl =>
          by_cases ha : a ∈ R.erase N
          · refine Or.inr (Or.inr ⟨R.erase N, ?_, ?_⟩)
            · have h2 := Finset.card_erase_of_mem ht
              have hpos : 0 < R.card := Finset.card_pos.mpr ⟨N, ht⟩
              omega
            · intro x y hx hy hxy
              have heq : ∀ i ∈ R, (stp x g).getD i false = (stp y g).getD i false := by
                intro i hi
                by_cases hiN : i = N
                · subst hiN
                  rw [← hx, getD_stp_eq, hx, ← hy, getD_stp_eq, hnot, hin]
                  simp only [GateOp.eval, List.map_cons, List.headD_cons, hxy a ha]
                · rw [getD_stp_ne x g (by omega), getD_stp_ne y g (by omega)]
                  exact hxy i (Finset.mem_erase.mpr ⟨hiN, hi⟩)
              apply Bool.eq_iff_iff.mpr
              constructor
              · exact hMono _ _ (by simp [stp, hx]) (by simp [stp, hy])
                  (fun i hi => by simp only [ite_true]; intro h; rwa [← heq i hi])
              · exact hMono _ _ (by simp [stp, hy]) (by simp [stp, hx])
                  (fun i hi => by simp only [ite_true]; intro h; rwa [heq i hi])
          · refine Or.inr (Or.inl ⟨insert a (R.erase N), Function.update (fun _ => true) a false, ?_, ?_⟩)
            · have h2 := Finset.card_erase_of_mem ht
              have hpos : 0 < R.card := Finset.card_pos.mpr ⟨N, ht⟩
              have h1 := Finset.card_insert_le a (R.erase N)
              omega
            · intro x y hx hy hxy
              apply hMono (stp x g) (stp y g) (by simp [stp, hx]) (by simp [stp, hy])
              intro i hi
              simp only [ite_true]
              by_cases hiN : i = N
              · subst hiN
                rw [← hx, getD_stp_eq, hx, ← hy, getD_stp_eq, hnot, hin]
                simp only [GateOp.eval, List.map_cons, List.headD_cons]
                have ha_dir := hxy a (Finset.mem_insert_self a _)
                simp only [Function.update_self, Bool.false_eq_true, ite_false] at ha_dir
                cases hxa : x.getD a false <;> cases hya : y.getD a false <;> simp_all
              · have hi' : i ∈ R.erase N := Finset.mem_erase.mpr ⟨hiN, hi⟩
                have hia : i ≠ a := fun e => ha (e ▸ hi')
                have hidir := hxy i (Finset.mem_insert_of_mem hi')
                simp only [Function.update_of_ne hia, ite_true] at hidir
                rw [getD_stp_ne x g (by omega), getD_stp_ne y g (by omega)]
                exact hidir
    · -- N ∉ R: stays Case A
      refine Or.inl ⟨R, by omega, ?_⟩
      intro x y hx hy hxy
      apply hMono (stp x g) (stp y g) (by simp [stp, hx]) (by simp [stp, hy])
      intro i hi
      have hiN : i ≠ N := fun e => ht (e ▸ hi)
      rw [getD_stp_ne x g (by omega), getD_stp_ne y g (by omega)]
      exact hxy i hi
  · -- Case B: UnateOn R sgn, R.card <= s
    by_cases ht : N ∈ R
    · let R' := R.erase N ∪ (effInputs g).toFinset
      by_cases hbig : R'.card ≤ R.card
      · -- Upgrades to Case C!
        refine Or.inr (Or.inr ⟨R', by omega, ?_⟩)
        intro x y hx hy hxy
        have heq : ∀ i ∈ R, (stp x g).getD i false = (stp y g).getD i false := by
          intro i hi
          by_cases hiN : i = N
          · subst hiN
            rw [← hx, getD_stp_eq, hx, ← hy, getD_stp_eq]
            exact effInputs_eval g x y (fun a ha => hxy a (Finset.mem_union_right _ (List.mem_toFinset.mpr ha)))
          · rw [getD_stp_ne x g (by omega), getD_stp_ne y g (by omega)]
            exact hxy i (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hiN, hi⟩))
        apply Bool.eq_iff_iff.mpr
        constructor
        · exact hUn _ _ (by simp [stp, hx]) (by simp [stp, hy])
            (fun i hi => by split_ifs <;> intro h <;> first | rwa [← heq i hi] | rwa [heq i hi])
        · exact hUn _ _ (by simp [stp, hy]) (by simp [stp, hx])
            (fun i hi => by split_ifs <;> intro h <;> first | rwa [heq i hi] | rwa [← heq i hi])
      · -- R'.card > R.card: must be non-shared binary AND/OR!
        have hpos : 0 < R.card := Finset.card_pos.mpr ⟨N, ht⟩
        have herase : (R.erase N).card = R.card - 1 := Finset.card_erase_of_mem ht
        have heff_len : (effInputs g).length = 2 := by
          have h1 : R'.card ≤ (R.erase N).card + (effInputs g).toFinset.card :=
            Finset.card_union_le (R.erase N) (effInputs g).toFinset
          have h2 := List.toFinset_card_le (effInputs g)
          have h3 : (effInputs g).length ≤ 2 := by
            rcases hop_mem with h | h | h
            · simpa [effInputs, h] using hg.2
            · simpa [effInputs, h] using hg.2
            · cases hin : g.inputs <;> simp [effInputs, h, hin]
          omega
        have hop_ao : g.op = .and ∨ g.op = .or := by
          rcases hop_mem with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exfalso; cases hin : g.inputs <;> simp [effInputs, h, hin] at heff_len
        have heff_eq : effInputs g = g.inputs := by rcases hop_ao with h | h <;> simp [effInputs, h]
        rw [heff_eq] at heff_len
        rcases hgin : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> simp [hgin] at heff_len
        have hR'eq : R' = insert a (insert b (R.erase N)) := by
          ext v; simp [R', heff_eq, hgin]
        have ha_not : a ∉ R.erase N := by
          intro ha
          have : R' = insert b (R.erase N) := by
            rw [hR'eq]; ext v; simp; grind
          have hc := Finset.card_insert_le b (R.erase N)
          rw [← this] at hc; omega
        have hb_not : b ∉ R.erase N := by
          intro hb
          have : R' = insert a (R.erase N) := by
            rw [hR'eq]; ext v; simp; grind
          have hc := Finset.card_insert_le a (R.erase N)
          rw [← this] at hc; omega
        have hR'card : R'.card ≤ s + 1 := by
          rw [hR'eq]
          have h1 := Finset.card_insert_le a (insert b (R.erase N))
          have h2 := Finset.card_insert_le b (R.erase N)
          omega
        let sgn' := Function.update (Function.update sgn a (sgn N)) b (sgn N)
        refine Or.inr (Or.inl ⟨R', sgn', hR'card, ?_⟩)
        intro x y hx hy hxy
        apply hUn (stp x g) (stp y g) (by simp [stp, hx]) (by simp [stp, hy])
        intro i hi
        by_cases hiN : i = N
        · subst hiN
          have hm := mono_step_andOr g hop_ao x y (sgn i) (fun u hu => by
            rw [hgin] at hu
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
            rcases hu with rfl | rfl
            · have h1 := hxy u (by rw [hR'eq]; simp)
              by_cases hub : u = b
              · subst hub; simpa [sgn'] using h1
              · simpa [sgn', Function.update_of_ne hub] using h1
            · have h1 := hxy u (by rw [hR'eq]; simp)
              simpa [sgn'] using h1)
          simp only [show (stp x g).getD i false = g.op.eval (g.inputs.map fun a => x.getD a false) by rw [← hx, getD_stp_eq],
            show (stp y g).getD i false = g.op.eval (g.inputs.map fun a => y.getD a false) by rw [← hy, getD_stp_eq]]
          exact hm
        · have hi' : i ∈ R.erase N := Finset.mem_erase.mpr ⟨hiN, hi⟩
          have hia : i ≠ a := fun e => ha_not (e ▸ hi')
          have hib : i ≠ b := fun e => hb_not (e ▸ hi')
          have hdir := hxy i (by rw [hR'eq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hi'))
          simp only [sgn', Function.update_of_ne hib, Function.update_of_ne hia] at hdir
          rw [getD_stp_ne x g (by omega), getD_stp_ne y g (by omega)]
          exact hdir
    · -- N ∉ R: upgrades to Case C!
      refine Or.inr (Or.inr ⟨R, by omega, ?_⟩)
      intro x y hx hy hxy
      have heq : ∀ i ∈ R, (stp x g).getD i false = (stp y g).getD i false := by
        intro i hi
        have hiN : i ≠ N := fun e => ht (e ▸ hi)
        rw [getD_stp_ne x g (by omega), getD_stp_ne y g (by omega)]
        exact hxy i hi
      apply Bool.eq_iff_iff.mpr
      constructor
      · exact hUn _ _ (by simp [stp, hx]) (by simp [stp, hy])
          (fun i hi => by split_ifs <;> intro h <;> first | rwa [← heq i hi] | rwa [heq i hi])
      · exact hUn _ _ (by simp [stp, hy]) (by simp [stp, hx])
          (fun i hi => by split_ifs <;> intro h <;> first | rwa [heq i hi] | rwa [← heq i hi])
  · -- Case C: DependsOn, R.card + 1 <= s
    by_cases ht : N ∈ R
    · let R' := R.erase N ∪ (effInputs g).toFinset
      refine Or.inr (Or.inr ⟨R', ?_, ?_⟩)
      · have h1 : R'.card ≤ (R.erase N).card + (effInputs g).toFinset.card :=
          Finset.card_union_le (R.erase N) (effInputs g).toFinset
        have h2 := Finset.card_erase_of_mem ht
        have h3 := List.toFinset_card_le (effInputs g)
        have h4 : (effInputs g).length ≤ 2 := by
          rcases hop_mem with h | h | h
          · simpa [effInputs, h] using hg.2
          · simpa [effInputs, h] using hg.2
          · cases hin : g.inputs <;> simp [effInputs, h, hin]
        have hpos : 0 < R.card := Finset.card_pos.mpr ⟨N, ht⟩
        omega
      · intro x y hx hy hxy
        apply hDep (stp x g) (stp y g) (by simp [stp, hx]) (by simp [stp, hy])
        intro i hi
        by_cases hiN : i = N
        · subst hiN
          rw [← hx, getD_stp_eq, hx, ← hy, getD_stp_eq]
          exact effInputs_eval g x y (fun a ha => hxy a (Finset.mem_union_right _ (List.mem_toFinset.mpr ha)))
        · rw [getD_stp_ne x g (by omega), getD_stp_ne y g (by omega)]
          exact hxy i (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hiN, hi⟩))
    · refine Or.inr (Or.inr ⟨R, by omega, ?_⟩)
      intro x y hx hy hxy
      apply hDep (stp x g) (stp y g) (by simp [stp, hx]) (by simp [stp, hy])
      intro i hi
      have hiN : i ≠ N := fun e => ht (e ▸ hi)
      rw [getD_stp_ne x g (by omega), getD_stp_ne y g (by omega)]
      exact hxy i hi

lemma coneInv_circuit (N : ℕ) (C : Circuit) (hC : FanInTwo C) :
    ConeInv N C.size (fun x => C.eval x) := by
  suffices ∀ (gs : List Gate) (M : ℕ) (out : ℕ),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      ConeInv M gs.length (fun x => (gs.foldl stp x).getD out false) by
    exact this C.gates N C.output hC
  intro gs
  induction gs with
  | nil =>
    intro M out _
    refine Or.inl ⟨{out}, by simp, ?_⟩
    intro x y _ _ hxy
    simpa using hxy out (Finset.mem_singleton_self out)
  | cons g gs ih =>
    intro M out hg
    have htail := ih (M + 1) out (fun g' h => hg g' (List.mem_cons_of_mem g h))
    simpa [List.foldl_cons, List.length_cons, Nat.add_comm] using
      coneInv_step M gs.length g (hg g (List.mem_cons_self ..)) _ htail

lemma matA_rows_distinct (n : ℕ) (hn : 4 ≤ n) (i1 i2 : Fin n) (hne : i1 ≠ i2) :
    ∃ j : Fin n, matA n i1 j ≠ matA n i2 j := by
  have hne' : i1.val ≠ i2.val := fun e => hne (Fin.ext e)
  by_cases h1 : i1.val < 4
  · by_cases h2 : i2.val < 4
    · have h4 : ∀ a b : Fin 4, a ≠ b → ∃ c : Fin 4,
          (if a.val = 1 ∨ c.val = 1 then decide (a.val = 3 ∨ c.val = 3)
           else decide (a.val = 2 ∨ c.val = 2)) ≠
          (if b.val = 1 ∨ c.val = 1 then decide (b.val = 3 ∨ c.val = 3)
           else decide (b.val = 2 ∨ c.val = 2)) := by decide
      obtain ⟨c, hc⟩ := h4 ⟨i1.val, h1⟩ ⟨i2.val, h2⟩ (fun e => hne' (congrArg (Fin.val : Fin 4 → ℕ) e))
      refine ⟨⟨c.val, by omega⟩, ?_⟩
      simpa [matA, show ¬(4 ≤ i1.val) by omega, show ¬(4 ≤ i2.val) by omega] using hc
    · by_cases hi10 : i1.val = 2
      · refine ⟨⟨0, by omega⟩, ?_⟩
        simp [matA, hi10, show i2.val ≠ 1 by omega, show i2.val ≠ 2 by omega, show ¬(4 ≤ 2) by omega,
          show i2 ≠ ⟨0, by omega⟩ from fun e => by have := congrArg Fin.val e; simp at this; omega]
      · refine ⟨i2, ?_⟩
        simp [matA, show ¬(4 ≤ i1.val) by omega, show 4 ≤ i2.val by omega,
          show i1.val ≠ 2 by omega, show i2.val ≠ 1 by omega, show i2.val ≠ 2 by omega,
          show i2.val ≠ 3 by omega]
        by_cases hi11 : i1.val = 1 <;> simp [hi11]
  · by_cases hi22 : i2.val = 2
    · refine ⟨⟨0, by omega⟩, ?_⟩
      simp [matA, hi22, show i1.val ≠ 1 by omega, show i1.val ≠ 2 by omega,
        show i1 ≠ ⟨0, by omega⟩ from fun e => by have := congrArg Fin.val e; simp at this; omega]
    · refine ⟨i1, ?_⟩
      simp [matA, show 4 ≤ i1.val by omega, show i1.val ≠ 1 by omega, show i1.val ≠ 2 by omega,
        show i1.val ≠ 3 by omega, hi22, hne.symm]
      by_cases hi21 : i2.val = 1 <;> simp [hi21]

lemma matA_symm (n : ℕ) (i j : Fin n) : matA n i j = matA n j i := by
  unfold matA
  have h1 : (i.val = 1 ∨ j.val = 1) ↔ (j.val = 1 ∨ i.val = 1) := or_comm
  have h2 : (i.val = 2 ∨ j.val = 2) ↔ (j.val = 2 ∨ i.val = 2) := or_comm
  have h3 : (i.val = 3 ∨ j.val = 3) ↔ (j.val = 3 ∨ i.val = 3) := or_comm
  have h4 : (4 ≤ i.val ∧ i = j) ↔ (4 ≤ j.val ∧ j = i) := by
    constructor <;> rintro ⟨h, rfl⟩ <;> exact ⟨h, rfl⟩
  by_cases hc : i.val = 1 ∨ j.val = 1
  · simp [hc, h1.mp hc, h3, h4]
  · simp [hc, mt h1.mpr hc, h2, h4]

lemma matA_cols_distinct (n : ℕ) (hn : 4 ≤ n) (j1 j2 : Fin n) (hne : j1 ≠ j2) :
    ∃ i : Fin n, matA n i j1 ≠ matA n i j2 := by
  obtain ⟨i, hi⟩ := matA_rows_distinct n hn j1 j2 hne
  exact ⟨i, by rwa [matA_symm n i j1, matA_symm n i j2]⟩

lemma matA_row_incomp (n : ℕ) (hn : 4 ≤ n) (i0 : Fin n) :
    ∃ u : Fin n, (∃ v1 : Fin n, matA n i0 v1 = true ∧ matA n u v1 = false) ∧
                 (∃ v2 : Fin n, matA n i0 v2 = false ∧ matA n u v2 = true) := by
  by_cases h1 : i0.val = 1
  · exact ⟨⟨0, by omega⟩, ⟨⟨3, by omega⟩, by simp [matA, h1]⟩, ⟨⟨2, by omega⟩, by simp [matA, h1]⟩⟩
  · by_cases h2 : i0.val = 2
    · exact ⟨⟨3, by omega⟩, ⟨⟨0, by omega⟩, by simp [matA, h2]⟩, ⟨⟨1, by omega⟩, by simp [matA, h2]⟩⟩
    · refine ⟨⟨1, by omega⟩, ⟨⟨2, by omega⟩, ?_⟩, ⟨⟨3, by omega⟩, ?_⟩⟩
      · simp [matA, h1]
      · simp [matA, h1, h2, show ¬(4 ≤ i0.val ∧ i0 = ⟨3, by omega⟩) from fun ⟨ha, he⟩ => by
          have := congrArg Fin.val he; simp at this; omega]

lemma matA_col_incomp (n : ℕ) (hn : 4 ≤ n) (j0 : Fin n) :
    ∃ v : Fin n, (∃ u1 : Fin n, matA n u1 j0 = true ∧ matA n u1 v = false) ∧
                 (∃ u2 : Fin n, matA n u2 j0 = false ∧ matA n u2 v = true) := by
  obtain ⟨v, ⟨u1, h1⟩, ⟨u2, h2⟩⟩ := matA_row_incomp n hn j0
  exact ⟨v, ⟨u1, by simpa [matA_symm] using h1⟩, ⟨u2, by simpa [matA_symm] using h2⟩⟩

lemma dep_card_lb (n : ℕ) (hn : 4 ≤ n) (C : Circuit) (hrep : Represents (matA n) C)
    (R : Finset ℕ) (hDep : DependsOn (n + n) (fun x => C.eval x) R) :
    2 * n - 2 ≤ R.card := by
  let RL : Finset (Fin n) := Finset.univ.filter (fun i => i.val ∈ R)
  let RR : Finset (Fin n) := Finset.univ.filter (fun j => n + j.val ∈ R)
  have hL : n - 1 ≤ RL.card := by
    by_contra hlt
    have hcompl : 2 ≤ (Finset.univ \ RL).card := by
      have h1 : RL.card + (Finset.univ \ RL).card = n := by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
        have := Finset.card_le_univ RL
        rw [Fintype.card_fin] at this
        omega
      omega
    obtain ⟨i1, hi1, i2, hi2, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < (Finset.univ \ RL).card)
    have hni1 : i1.val ∉ R := by simpa [RL] using (Finset.mem_sdiff.mp hi1).2
    have hni2 : i2.val ∉ R := by simpa [RL] using (Finset.mem_sdiff.mp hi2).2
    obtain ⟨j, hj⟩ := matA_rows_distinct n hn i1 i2 hne
    apply hj
    rw [← hrep i1 j, ← hrep i2 j]
    apply hDep _ _ (oneEach_len i1 j) (oneEach_len i2 j)
    intro k hk
    by_cases hkn : k < n
    · rw [oneEach_getD_left i1 j hkn, oneEach_getD_left i2 j hkn]
      have h1 : i1.val ≠ k := fun e => hni1 (e ▸ hk)
      have h2 : i2.val ≠ k := fun e => hni2 (e ▸ hk)
      simp [h1, h2]
    · by_cases hk2 : k < n + n
      · have hkm : k - n < n := by omega
        have hk' : k = n + (k - n) := by omega
        rw [hk', oneEach_getD_right i1 j hkm, oneEach_getD_right i2 j hkm]
      · rw [List.getD_eq_default _ _ (by rw [oneEach_len]; omega),
            List.getD_eq_default _ _ (by rw [oneEach_len]; omega)]
  have hR : n - 1 ≤ RR.card := by
    by_contra hlt
    have hcompl : 2 ≤ (Finset.univ \ RR).card := by
      have h1 : RR.card + (Finset.univ \ RR).card = n := by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
        have := Finset.card_le_univ RR
        rw [Fintype.card_fin] at this
        omega
      omega
    obtain ⟨j1, hj1, j2, hj2, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < (Finset.univ \ RR).card)
    have hnj1 : n + j1.val ∉ R := by simpa [RR] using (Finset.mem_sdiff.mp hj1).2
    have hnj2 : n + j2.val ∉ R := by simpa [RR] using (Finset.mem_sdiff.mp hj2).2
    obtain ⟨i, hi⟩ := matA_cols_distinct n hn j1 j2 hne
    apply hi
    rw [← hrep i j1, ← hrep i j2]
    apply hDep _ _ (oneEach_len i j1) (oneEach_len i j2)
    intro k hk
    by_cases hkn : k < n
    · rw [oneEach_getD_left i j1 hkn, oneEach_getD_left i j2 hkn]
    · by_cases hk2 : k < n + n
      · have hkm : k - n < n := by omega
        have hk' : k = n + (k - n) := by omega
        rw [hk', oneEach_getD_right i j1 hkm, oneEach_getD_right i j2 hkm]
        have h1 : j1.val ≠ k - n := fun e => hnj1 (by rw [← e] at hk'; exact hk' ▸ hk)
        have h2 : j2.val ≠ k - n := fun e => hnj2 (by rw [← e] at hk'; exact hk' ▸ hk)
        simp [h1, h2]
      · rw [List.getD_eq_default _ _ (by rw [oneEach_len]; omega),
            List.getD_eq_default _ _ (by rw [oneEach_len]; omega)]
  let SL := RL.image (fun i : Fin n => i.val)
  let SR := RR.image (fun j : Fin n => n + j.val)
  have hSL : SL.card = RL.card := Finset.card_image_of_injective _ Fin.val_injective
  have hSR : SR.card = RR.card := Finset.card_image_of_injective _ (fun a b h => Fin.ext (by omega))
  have hdisj : Disjoint SL SR := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    rcases Finset.mem_image.mp hk1 with ⟨i, _, rfl⟩
    rcases Finset.mem_image.mp hk2 with ⟨j, _, he⟩
    omega
  have hsub : SL ∪ SR ⊆ R := by
    intro k hk
    rcases Finset.mem_union.mp hk with h | h
    · rcases Finset.mem_image.mp h with ⟨i, hi, rfl⟩; exact (Finset.mem_filter.mp hi).2
    · rcases Finset.mem_image.mp h with ⟨j, hj, rfl⟩; exact (Finset.mem_filter.mp hj).2
  have htot := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hSL, hSR] at htot
  omega

lemma unate_card_lb (n : ℕ) (hn : 4 ≤ n) (C : Circuit) (hrep : Represents (matA n) C)
    (R : Finset ℕ) (sgn : ℕ → Bool) (hUn : UnateOn (n + n) (fun x => C.eval x) R sgn) :
    2 * n ≤ R.card := by
  have hall : Finset.range (2 * n) ⊆ R := by
    intro k hk
    have hkl : k < 2 * n := Finset.mem_range.mp hk
    by_contra hkR
    by_cases hkn : k < n
    · let i0 : Fin n := ⟨k, hkn⟩
      obtain ⟨u, ⟨v1, h1t, h1f⟩, ⟨v2, h2f, h2t⟩⟩ := matA_row_incomp n hn i0
      by_cases hs : sgn u.val = true
      · have htrue : C.eval (oneEach u v1) = true := by
          apply hUn (oneEach i0 v1) (oneEach u v1) (oneEach_len ..) (oneEach_len ..) ?_ (by dsimp only; rw [hrep, h1t])
          intro w hw
          have hw0 : w ≠ i0.val := fun e => hkR (by simpa [i0, e] using hw)
          by_cases hwu : w = u.val
          · subst hwu
            simp only [hs, ite_true]
            rw [oneEach_getD_left u v1 u.isLt]; simp
          · by_cases hwn : w < n
            · rw [oneEach_getD_left i0 v1 hwn, oneEach_getD_left u v1 hwn]
              simp [show i0.val ≠ w by omega, show u.val ≠ w by omega]
            · by_cases hw2 : w < n + n
              · have hwm : w - n < n := by omega
                have hw' : w = n + (w - n) := by omega
                rw [hw', oneEach_getD_right i0 v1 hwm, oneEach_getD_right u v1 hwm]
                split_ifs <;> intro h <;> exact h
              · rw [List.getD_eq_default _ _ (by rw [oneEach_len]; omega),
                    List.getD_eq_default _ _ (by rw [oneEach_len]; omega)]
                split_ifs <;> intro h <;> exact h
        rw [hrep, h1f] at htrue; cases htrue
      · have hsf : sgn u.val = false := Bool.eq_false_iff.mpr hs
        have htrue : C.eval (oneEach i0 v2) = true := by
          apply hUn (oneEach u v2) (oneEach i0 v2) (oneEach_len ..) (oneEach_len ..) ?_ (by dsimp only; rw [hrep, h2t])
          intro w hw
          have hw0 : w ≠ i0.val := fun e => hkR (by simpa [i0, e] using hw)
          by_cases hwu : w = u.val
          · subst hwu
            simp only [hsf, Bool.false_eq_true, ite_false]
            rw [oneEach_getD_left u v2 u.isLt]; simp
          · by_cases hwn : w < n
            · rw [oneEach_getD_left u v2 hwn, oneEach_getD_left i0 v2 hwn]
              simp [show i0.val ≠ w by omega, show u.val ≠ w by omega]
            · by_cases hw2 : w < n + n
              · have hwm : w - n < n := by omega
                have hw' : w = n + (w - n) := by omega
                rw [hw', oneEach_getD_right u v2 hwm, oneEach_getD_right i0 v2 hwm]
                split_ifs <;> intro h <;> exact h
              · rw [List.getD_eq_default _ _ (by rw [oneEach_len]; omega),
                    List.getD_eq_default _ _ (by rw [oneEach_len]; omega)]
                split_ifs <;> intro h <;> exact h
        rw [hrep, h2f] at htrue; cases htrue
    · let j0 : Fin n := ⟨k - n, by omega⟩
      obtain ⟨v, ⟨u1, h1t, h1f⟩, ⟨u2, h2f, h2t⟩⟩ := matA_col_incomp n hn j0
      by_cases hs : sgn (n + v.val) = true
      · have htrue : C.eval (oneEach u1 v) = true := by
          apply hUn (oneEach u1 j0) (oneEach u1 v) (oneEach_len ..) (oneEach_len ..) ?_ (by dsimp only; rw [hrep, h1t])
          intro w hw
          have hw0 : w ≠ n + j0.val := fun e => hkR (by have hwk : w = k := (by simp [j0] at e; omega); exact hwk ▸ hw)
          by_cases hwv : w = n + v.val
          · subst hwv
            simp only [hs, ite_true]
            rw [oneEach_getD_right u1 v v.isLt]; simp
          · by_cases hwn : w < n
            · rw [oneEach_getD_left u1 j0 hwn, oneEach_getD_left u1 v hwn]
              split_ifs <;> intro h <;> exact h
            · by_cases hw2 : w < n + n
              · have hwm : w - n < n := by omega
                have hw' : w = n + (w - n) := by omega
                rw [hw', oneEach_getD_right u1 j0 hwm, oneEach_getD_right u1 v hwm]
                simp [show j0.val ≠ w - n by omega, show v.val ≠ w - n by omega]
              · rw [List.getD_eq_default _ _ (by rw [oneEach_len]; omega),
                    List.getD_eq_default _ _ (by rw [oneEach_len]; omega)]
                split_ifs <;> intro h <;> exact h
        rw [hrep, h1f] at htrue; cases htrue
      · have hsf : sgn (n + v.val) = false := Bool.eq_false_iff.mpr hs
        have htrue : C.eval (oneEach u2 j0) = true := by
          apply hUn (oneEach u2 v) (oneEach u2 j0) (oneEach_len ..) (oneEach_len ..) ?_ (by dsimp only; rw [hrep, h2t])
          intro w hw
          have hw0 : w ≠ n + j0.val := fun e => hkR (by have hwk : w = k := (by simp [j0] at e; omega); exact hwk ▸ hw)
          by_cases hwv : w = n + v.val
          · subst hwv
            simp only [hsf, Bool.false_eq_true, ite_false]
            rw [oneEach_getD_right u2 v v.isLt]; simp
          · by_cases hwn : w < n
            · rw [oneEach_getD_left u2 v hwn, oneEach_getD_left u2 j0 hwn]
              split_ifs <;> intro h <;> exact h
            · by_cases hw2 : w < n + n
              · have hwm : w - n < n := by omega
                have hw' : w = n + (w - n) := by omega
                rw [hw', oneEach_getD_right u2 v hwm, oneEach_getD_right u2 j0 hwm]
                simp [show j0.val ≠ w - n by omega, show v.val ≠ w - n by omega]
              · rw [List.getD_eq_default _ _ (by rw [oneEach_len]; omega),
                    List.getD_eq_default _ _ (by rw [oneEach_len]; omega)]
                split_ifs <;> intro h <;> exact h
        rw [hrep, h2f] at htrue; cases htrue
  have hle := Finset.card_le_card hall
  simpa using hle

lemma part2 (n : ℕ) (hn : 4 ≤ n) (C : Circuit) (hC : FanInTwo C) (hrep : Represents (matA n) C) :
    2 * n - 1 ≤ C.size := by
  rcases coneInv_circuit (n + n) C hC with ⟨R, hRc, hUn⟩ | ⟨R, sgn, hRc, hUn⟩ | ⟨R, hRc, hDep⟩
  · have := unate_card_lb n hn C hrep R (fun _ => true) hUn; omega
  · have := unate_card_lb n hn C hrep R sgn hUn; omega
  · have := dep_card_lb n hn C hrep R hDep; omega

-- ============================================================
-- PART 3A: Monotone2 restriction drops at least 2 gates per extra index
-- ============================================================

lemma mono2_eval_mono (gs : List Gate)
    (hgs : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ (x y : List Bool), x.length = y.length →
      (∀ i, x.getD i false = true → y.getD i false = true) →
      ∀ i, (gs.foldl stp x).getD i false = true → (gs.foldl stp y).getD i false = true := by
  induction gs with
  | nil => intro x y _ h i hi; exact h i hi
  | cons g gs ih =>
    intro x y hlen h
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')) (stp x g) (stp y g)
      (by simp [stp, hlen])
    intro i hi
    by_cases hieq : i = x.length
    · subst hieq
      rw [getD_stp_eq] at hi
      rw [hlen, getD_stp_eq]
      exact mono_step_andOr g (hgs g (List.mem_cons_self ..)).1 x y true (fun a _ => h a) hi
    · rw [getD_stp_ne x g hieq] at hi
      rw [getD_stp_ne y g (by omega)]
      exact h i hi

def IsInit {α : Type} (l1 l2 : List α) : Prop := ∃ r, l1 ++ r = l2

lemma isInit_rfl {α : Type} (l : List α) : IsInit l l := ⟨[], by simp⟩

lemma isInit_append {α : Type} (l1 l2 : List α) : IsInit l1 (l1 ++ l2) := ⟨l2, rfl⟩

lemma isInit_trans {α : Type} {l1 l2 l3 : List α} (h1 : IsInit l1 l2) (h2 : IsInit l2 l3) :
    IsInit l1 l3 := by
  obtain ⟨r1, rfl⟩ := h1
  obtain ⟨r2, rfl⟩ := h2
  exact ⟨r1 ++ r2, (List.append_assoc ..).symm⟩

lemma isInit_len_le {α : Type} {l1 l2 : List α} (h : IsInit l1 l2) : l1.length ≤ l2.length := by
  obtain ⟨r, rfl⟩ := h; simp

lemma isInit_getD_opt {l1 l2 : List (Option ℕ)} (h : IsInit l1 l2) {i : ℕ} (hi : i < l1.length) :
    l2.getD i none = l1.getD i none := by
  obtain ⟨r, rfl⟩ := h
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_opt_snoc (l : List (Option ℕ)) (v : Option ℕ) (i : ℕ) :
    (l ++ [v]).getD i none = if i < l.length then l.getD i none else if i = l.length then v else none := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

-- Compile Monotone2 circuit gs under initial wire environment (none = false, some w' = new wire)
def elimStep (n2 : ℕ) (st : List (Option ℕ) × List Gate) (g : Gate) : List (Option ℕ) × List Gate :=
  match g.op, g.inputs with
  | .and, [] => (st.1 ++ [some (n2 + st.2.length)], st.2 ++ [⟨.and, []⟩])
  | .and, [a] => (st.1 ++ [st.1.getD a none], st.2)
  | .and, [a, b] =>
    match st.1.getD a none, st.1.getD b none with
    | some a', some b' => (st.1 ++ [some (n2 + st.2.length)], st.2 ++ [⟨.and, [a', b']⟩])
    | _, _ => (st.1 ++ [none], st.2)
  | .or, [] => (st.1 ++ [none], st.2)
  | .or, [a] => (st.1 ++ [st.1.getD a none], st.2)
  | .or, [a, b] =>
    match st.1.getD a none, st.1.getD b none with
    | some a', some b' => (st.1 ++ [some (n2 + st.2.length)], st.2 ++ [⟨.or, [a', b']⟩])
    | some a', none => (st.1 ++ [some a'], st.2)
    | none, some b' => (st.1 ++ [some b'], st.2)
    | none, none => (st.1 ++ [none], st.2)
  | _, _ => (st.1 ++ [none], st.2)

lemma elimStep_len (n2 : ℕ) (st : List (Option ℕ) × List Gate) (g : Gate) :
    (elimStep n2 st g).1.length = st.1.length + 1 ∧ (elimStep n2 st g).2.length ≤ st.2.length + 1 := by
  rcases g with ⟨op, ins⟩
  unfold elimStep
  cases op <;> cases ins with
  | nil => simp
  | cons a tl =>
    cases tl with
    | nil => simp
    | cons b tl2 =>
      cases tl2 with
      | nil =>
        cases ha : st.1.getD a none <;> cases hb : st.1.getD b none <;> simp only [ha, hb] <;> simp
      | cons _ _ => simp

lemma elimStep_isInit_gates (n2 : ℕ) (st : List (Option ℕ) × List Gate) (g : Gate) :
    IsInit st.2 (elimStep n2 st g).2 := by
  rcases g with ⟨op, ins⟩
  unfold elimStep
  cases op <;> cases ins with
  | nil => first | exact isInit_rfl _ | exact isInit_append _ _
  | cons a tl =>
    cases tl with
    | nil => exact isInit_rfl _
    | cons b tl2 =>
      cases tl2 with
      | nil =>
        cases ha : st.1.getD a none <;> cases hb : st.1.getD b none <;> simp only [ha, hb] <;>
          first | exact isInit_rfl _ | exact isInit_append _ _
      | cons _ _ => exact isInit_rfl _

lemma elimStep_isInit_env (n2 : ℕ) (st : List (Option ℕ) × List Gate) (g : Gate) :
    IsInit st.1 (elimStep n2 st g).1 := by
  rcases g with ⟨op, ins⟩
  unfold elimStep
  cases op <;> cases ins with
  | nil => exact isInit_append _ _
  | cons a tl =>
    cases tl with
    | nil => exact isInit_append _ _
    | cons b tl2 =>
      cases tl2 with
      | nil =>
        cases ha : st.1.getD a none <;> cases hb : st.1.getD b none <;> simp only [ha, hb] <;>
          exact isInit_append _ _
      | cons _ _ => exact isInit_append _ _

lemma elim_foldl_isInit_gates (n2 : ℕ) (gs : List Gate) (st : List (Option ℕ) × List Gate) :
    IsInit st.2 (gs.foldl (elimStep n2) st).2 := by
  induction gs generalizing st with
  | nil => exact isInit_rfl _
  | cons g gs ih => exact isInit_trans (elimStep_isInit_gates n2 st g) (ih _)

lemma elim_foldl_isInit_env (n2 : ℕ) (gs : List Gate) (st : List (Option ℕ) × List Gate) :
    IsInit st.1 (gs.foldl (elimStep n2) st).1 := by
  induction gs generalizing st with
  | nil => exact isInit_rfl _
  | cons g gs ih => exact isInit_trans (elimStep_isInit_env n2 st g) (ih _)

lemma elimStep_mono2 (n2 : ℕ) (st : List (Option ℕ) × List Gate) (g : Gate)
    (h : ∀ g' ∈ st.2, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2) :
    ∀ g' ∈ (elimStep n2 st g).2, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2 := by
  rcases g with ⟨op, ins⟩
  unfold elimStep
  cases op <;> cases ins with
  | nil =>
    intro g' hg'
    first
    | exact h g' hg'
    | (simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg';
       rcases hg' with hg' | rfl <;> first | exact h g' hg' | simp)
  | cons a tl =>
    cases tl with
    | nil => exact h
    | cons b tl2 =>
      cases tl2 with
      | nil =>
        cases ha : st.1.getD a none <;> cases hb : st.1.getD b none <;> simp only [ha, hb]
        all_goals intro g' hg'
        all_goals first
          | exact h g' hg'
          | (simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg';
             rcases hg' with hg' | rfl <;> first | exact h g' hg' | simp)
      | cons _ _ => exact h

lemma elimStep_spec_clean (n2 : ℕ) (st : List (Option ℕ) × List Gate) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hbound : ∀ i j, st.1.getD i none = some j → j < n2 + st.2.length)
    (oldW newW : List Bool)
    (hlen_old : oldW.length = st.1.length)
    (hlen_new : newW.length = n2 + st.2.length)
    (hmatch : ∀ i, oldW.getD i false = match st.1.getD i none with
      | none => false | some j => newW.getD j false) :
    (∀ i j, (elimStep n2 st g).1.getD i none = some j → j < n2 + (elimStep n2 st g).2.length) ∧
    (∀ i, (stp oldW g).getD i false =
      match (elimStep n2 st g).1.getD i none with
      | none => false
      | some j => (((elimStep n2 st g).2.drop st.2.length).foldl stp newW).getD j false) := by
  have hno : ∀ (v : Option ℕ),
      (g.op.eval (g.inputs.map fun a => oldW.getD a false) = match v with | none => false | some j => newW.getD j false) →
      (∀ j, v = some j → j < n2 + st.2.length) →
      (∀ i j, (st.1 ++ [v]).getD i none = some j → j < n2 + st.2.length) ∧
      (∀ i, (stp oldW g).getD i false = match (st.1 ++ [v]).getD i none with
        | none => false | some j => ((st.2.drop st.2.length).foldl stp newW).getD j false) := by
    intro v hv hv_b
    constructor
    · intro i j hij
      rw [getD_opt_snoc] at hij
      split_ifs at hij with h1 h2
      · exact hbound i j hij
      · exact hv_b j hij
    · intro i
      rw [List.drop_length, List.foldl_nil, stp, getD_snoc, getD_opt_snoc, hlen_old]
      split_ifs with h1 h2
      · exact hmatch i
      · exact hv
      · rfl
  have hemit : ∀ (g' : Gate),
      (g.op.eval (g.inputs.map fun a => oldW.getD a false) = g'.op.eval (g'.inputs.map fun a => newW.getD a false)) →
      (∀ i j, (st.1 ++ [some (n2 + st.2.length)]).getD i none = some j → j < n2 + (st.2 ++ [g']).length) ∧
      (∀ i, (stp oldW g).getD i false = match (st.1 ++ [some (n2 + st.2.length)]).getD i none with
        | none => false | some j => (((st.2 ++ [g']).drop st.2.length).foldl stp newW).getD j false) := by
    intro g' hv
    constructor
    · intro i j hij
      rw [getD_opt_snoc] at hij
      simp only [List.length_append, List.length_singleton]
      split_ifs at hij with h1 h2
      · have := hbound i j hij; omega
      · cases hij; omega
    · intro i
      have hdrop : (st.2 ++ [g']).drop st.2.length = [g'] := by simp
      rw [hdrop, List.foldl_cons, List.foldl_nil, stp, getD_snoc, getD_opt_snoc, hlen_old]
      split_ifs with h1 h2
      · rw [hmatch i]
        cases hm : st.1.getD i none with
        | none => rfl
        | some j =>
          dsimp only
          have hj : j < newW.length := by rw [hlen_new]; exact hbound i j hm
          rw [getD_stp_lt newW g' hj]
      · dsimp only
        rw [← hlen_new, getD_stp_eq, hv]
      · rfl
  obtain ⟨hop, hlen⟩ := hg
  rcases g with ⟨op, ins⟩
  simp only at hop hlen
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> simp at hlen
  · rcases hop with rfl | rfl
    · exact hemit ⟨.and, []⟩ rfl
    · exact hno none rfl (fun _ h => by cases h)
  · rcases hop with rfl | rfl
    · exact hno (st.1.getD a none) (by
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          id_eq, Bool.and_true, hmatch a]) (fun j hj => hbound a j hj)
    · exact hno (st.1.getD a none) (by
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
          id_eq, Bool.or_false, hmatch a]) (fun j hj => hbound a j hj)
  · rcases hop with rfl | rfl
    · unfold elimStep
      cases ha : st.1.getD a none with
      | none =>
        simp only [ha]
        exact hno none (by
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
            id_eq, Bool.and_true, hmatch a, ha, Bool.false_and]) (fun _ h => by cases h)
      | some a' =>
        cases hb : st.1.getD b none with
        | none =>
          simp only [ha, hb]
          exact hno none (by
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
              id_eq, Bool.and_true, hmatch b, hb, Bool.and_false]) (fun _ h => by cases h)
        | some b' =>
          simp only [ha, hb]
          exact hemit ⟨.and, [a', b']⟩ (by
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
              id_eq, Bool.and_true, hmatch a, hmatch b, ha, hb])
    · unfold elimStep
      cases ha : st.1.getD a none with
      | none =>
        cases hb : st.1.getD b none with
        | none =>
          simp only [ha, hb]
          exact hno none (by
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
              id_eq, Bool.or_false, hmatch a, hmatch b, ha, hb]) (fun _ h => by cases h)
        | some b' =>
          simp only [ha, hb]
          exact hno (some b') (by
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
              id_eq, Bool.or_false, hmatch a, hmatch b, ha, hb, Bool.false_or])
            (fun j hj => by cases hj; exact hbound b b' hb)
      | some a' =>
        cases hb : st.1.getD b none with
        | none =>
          simp only [ha, hb]
          exact hno (some a') (by
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
              id_eq, Bool.or_false, hmatch a, hmatch b, ha, hb, Bool.or_false])
            (fun j hj => by cases hj; exact hbound a a' ha)
        | some b' =>
          simp only [ha, hb]
          exact hemit ⟨.or, [a', b']⟩ (by
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
              id_eq, Bool.or_false, hmatch a, hmatch b, ha, hb])

lemma elim_foldl_spec (n2 : ℕ) (gs : List Gate)
    (hgs : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ (st : List (Option ℕ) × List Gate),
      (∀ g' ∈ st.2, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2) →
      (∀ i j, st.1.getD i none = some j → j < n2 + st.2.length) →
      ∀ (oldW newW : List Bool),
      oldW.length = st.1.length →
      newW.length = n2 + st.2.length →
      (∀ i, oldW.getD i false = match st.1.getD i none with | none => false | some j => newW.getD j false) →
      let res := gs.foldl (elimStep n2) st
      res.1.length = st.1.length + gs.length ∧
      res.2.length ≤ st.2.length + gs.length ∧
      (∀ g' ∈ res.2, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2) ∧
      (∀ i, (gs.foldl stp oldW).getD i false = match res.1.getD i none with
        | none => false | some j => ((res.2.drop st.2.length).foldl stp newW).getD j false) := by
  induction gs with
  | nil =>
    intro st hmono _ oldW newW _ _ hmatch
    refine ⟨by simp, by simp, hmono, fun i => by simpa using hmatch i⟩
  | cons g gs ih =>
    intro st hmono hbound oldW newW hlen_old hlen_new hmatch
    have hg := hgs g (List.mem_cons_self ..)
    have hstep_len := elimStep_len n2 st g
    have hstep_mono := elimStep_mono2 n2 st g hmono
    obtain ⟨hstep_bound, hstep_match⟩ := elimStep_spec_clean n2 st g hg hbound oldW newW hlen_old hlen_new hmatch
    set st1 := elimStep n2 st g
    set midW := (st1.2.drop st.2.length).foldl stp newW
    have hinit1 : IsInit st.2 st1.2 := elimStep_isInit_gates n2 st g
    have hmid_len : midW.length = n2 + st1.2.length := by
      have hsub : st.2.length ≤ st1.2.length := isInit_len_le hinit1
      simp only [midW, foldl_len, hlen_new, List.length_drop]
      omega
    have htail := ih (fun g' h => hgs g' (List.mem_cons_of_mem g h)) st1 hstep_mono hstep_bound
      (stp oldW g) midW (by simp [stp, hlen_old, hstep_len.1]) hmid_len hstep_match
    have hinit_res : IsInit st1.2 (gs.foldl (elimStep n2) st1).2 := elim_foldl_isInit_gates n2 gs st1
    have ht1 : (gs.foldl (elimStep n2) st1).1.length = st1.1.length + gs.length := htail.1
    have ht2 : (gs.foldl (elimStep n2) st1).2.length ≤ st1.2.length + gs.length := htail.2.1
    refine ⟨by simp only [List.foldl_cons, List.length_cons]; change (gs.foldl (elimStep n2) st1).1.length = _; omega,
            by simp only [List.foldl_cons, List.length_cons]; change (gs.foldl (elimStep n2) st1).2.length ≤ _; omega,
            htail.2.2.1, ?_⟩
    intro i
    have hcomb : ((gs.foldl (elimStep n2) st1).2.drop st.2.length) =
        (st1.2.drop st.2.length) ++ ((gs.foldl (elimStep n2) st1).2.drop st1.2.length) := by
      obtain ⟨r1, hr1⟩ := hinit1
      obtain ⟨r2, hr2⟩ := hinit_res
      rw [← hr2, ← hr1, List.append_assoc]
      simp
    simp only [List.foldl_cons]
    change (gs.foldl stp (stp oldW g)).getD i false =
      match (gs.foldl (elimStep n2) st1).1.getD i none with
      | none => false
      | some j => (((gs.foldl (elimStep n2) st1).2.drop st.2.length).foldl stp newW).getD j false
    rw [hcomb, List.foldl_append]
    exact htail.2.2.2 i

-- Check that when elimStep keeps a gate (length increases by 1), NONE of its inputs mapped to none
lemma elimStep_kept_inputs (n2 : ℕ) (st : List (Option ℕ) × List Gate) (g : Gate)
    (hkept : (elimStep n2 st g).2.length = st.2.length + 1) :
    ∀ a ∈ g.inputs, st.1.getD a none ≠ none := by
  rcases g with ⟨op, ins⟩
  unfold elimStep at hkept
  cases op <;> cases ins with
  | nil => intro a ha; cases ha
  | cons a tl =>
    cases tl with
    | nil => simp at hkept
    | cons b tl2 =>
      cases tl2 with
      | nil =>
        cases ha : st.1.getD a none <;> cases hb : st.1.getD b none <;>
          simp only [ha, hb] at hkept
        all_goals first
          | (simp at hkept; done)
          | (intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu;
             rcases hu with rfl | rfl; (rw [ha]; simp); (rw [hb]; simp))
      | cons _ _ => simp at hkept

-- And when elimStep drops a gate AND outputs some j, AT MOST ONE input mapped to none
lemma elimStep_dropped_some_not_both (n2 : ℕ) (st : List (Option ℕ) × List Gate) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (u v : ℕ) (huv : u ≠ v) (hu : st.1.getD u none = none) (hv : st.1.getD v none = none)
    (hsome : (elimStep n2 st g).1.getD st.1.length none ≠ none) :
    u ∉ g.inputs ∨ v ∉ g.inputs := by
  by_contra hboth
  push Not at hboth
  obtain ⟨hu_in, hv_in⟩ := hboth
  obtain ⟨hop, hlen⟩ := hg
  rcases g with ⟨op, ins⟩
  simp only at hop hlen hu_in hv_in hsome
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> simp at hlen hu_in hv_in
  · rcases hu_in with rfl; rcases hv_in with rfl; exact huv rfl
  · have hnone_ab : st.1.getD a none = none ∧ st.1.getD b none = none := by
      rcases hu_in with rfl | rfl <;> rcases hv_in with rfl | rfl
      · exact absurd rfl huv
      · exact ⟨hu, hv⟩
      · exact ⟨hv, hu⟩
      · exact absurd rfl huv
    rcases hop with rfl | rfl <;> (
      unfold elimStep at hsome
      simp only [hnone_ab.1, hnone_ab.2, getD_opt_snoc, lt_irrefl, ite_false, ite_true] at hsome
      exact hsome rfl)

-- Independence lemma allowing `bad` gates to output into `bad` wire indices
lemma bad_wire_indep (gs : List Gate) (bad : ℕ → Prop) :
    ∀ (x y : List Bool), x.length = y.length →
      (∀ (j : ℕ) (g : Gate), gs[j]? = some g → ¬ bad (x.length + j) → ∀ a ∈ g.inputs, ¬ bad a) →
      (∀ i < x.length, ¬ bad i → x.getD i false = y.getD i false) →
      ∀ i, ¬ bad i → (gs.foldl stp x).getD i false = (gs.foldl stp y).getD i false := by
  induction gs with
  | nil =>
    intro x y hlen _ h i hi
    by_cases hilt : i < x.length
    · exact h i hilt hi
    · rw [List.foldl_nil, List.foldl_nil,
          List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  | cons g gs ih =>
    intro x y hlen hgood h
    apply ih (stp x g) (stp y g) (by simp [stp, hlen])
    · intro j g' hj hnb a ha
      have h' := hgood (j + 1) g' (by simpa using hj) (by simpa [stp, Nat.add_assoc, Nat.add_comm 1 j] using hnb)
      exact h' a ha
    · intro i hilt hi
      by_cases hix : i < x.length
      · rw [getD_stp_lt x g hix, getD_stp_lt y g (by omega)]
        exact h i hix hi
      · have hieq : i = x.length := by simp [stp] at hilt; omega
        subst hieq
        have hg := hgood 0 g rfl (by simpa using hi)
        have hval : g.op.eval (g.inputs.map fun a => x.getD a false) =
            g.op.eval (g.inputs.map fun a => y.getD a false) := by
          congr 1
          apply List.map_congr_left
          intro a ha
          by_cases halt : a < x.length
          · exact h a halt (hg a ha)
          · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
        rw [getD_stp_eq, hlen, getD_stp_eq, hval]

-- ============================================================
-- PART 3B: Exact A4 lower bound (¬ RepSizeAtMost (matA 4) 8)
-- Adapted from L_meta_10085 (BitVec 128 = 64 true/false pairs)
-- ============================================================

section LiveA4

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

lemma compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero => exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := fun hh => sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

lemma live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h1 := Finset.card_insert_le a (insert b rest)
      have h2 := Finset.card_insert_le b rest
      omega

lemma live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

lemma first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end LiveA4

abbrev W := BitVec 128
def ops (x y : W) : List W := [x &&& y, x ||| y]
def sep (x : W) : BitVec 64 := x.setWidth 64 &&& ~~~((x >>> 64).setWidth 64)
def cuts (ws : List W) : BitVec 64 := ws.foldr (fun w v => sep w ||| v) 0
def target : W := (0 : BitVec 64) ++ (-1 : BitVec 64)
abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 64) (w : W) : Prop :=
  w.getLsbD i.val = true ∧ w.getLsbD (64 + i.val) = false

lemma ops_differs (i : Fin 64) (a b z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold differs at hd ⊢
  rcases hz with rfl | rfl
  · simp only [BitVec.getLsbD_and, Bool.and_eq_true, Bool.and_eq_false_iff] at hd
    obtain ⟨⟨ha, hb⟩, hf⟩ := hd
    rcases hf with hf | hf
    · exact .inl ⟨ha, hf⟩
    · exact .inr ⟨hb, hf⟩
  · simp only [BitVec.getLsbD_or, Bool.or_eq_true, Bool.or_eq_false_iff] at hd
    obtain ⟨ht, hfa, hfb⟩ := hd
    rcases ht with ht | ht
    · exact .inl ⟨ht, hfa⟩
    · exact .inr ⟨ht, hfb⟩

lemma sep_spec (a : W) (i : Fin 64) : (sep a).getLsbD i.val = true ↔ differs i a := by
  have hi : i.val < 64 := i.isLt
  simp [sep, differs, hi, Nat.add_comm]

lemma cuts_spec (ws : List W) (i : Fin 64) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih, sep_spec]
    simp

lemma cuts_full {g : W} (hg : g = target) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by subst hg; unfold differs; decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j, hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 64)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

lemma ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

lemma recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by ext v; simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

lemma singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

noncomputable section FastA4

def M64 : ℕ := 0xffffffffffffffff
def P64 : ℕ := 0x10000000000000000

def nsep (x : ℕ) : ℕ :=
  Nat.land (Nat.mod x P64) (Nat.sub M64 (Nat.mod (Nat.shiftRight x 64) P64))

def ncuts (ws : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun w _ ih => Nat.lor (nsep w) ih) ws

def len (ws : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun _ _ ih => Nat.succ ih) ws

def nisGoal (ws : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun w t _ => List.rec (motive := fun _ => Bool)
      (Nat.beq w M64) (fun _ _ _ => false) t) ws

def frc (w : ℕ) (k : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k Nat.zero) (fun m _ => k (Nat.succ m)) w

def revK (xs : List ℕ) (acc : List ℕ) (k : List ℕ → Bool) : Bool :=
  List.rec (motive := fun _ => List ℕ → Bool) (fun acc => k acc) (fun x _ ih acc => ih (x :: acc))
    xs acc

def insK (w : ℕ) (l : List ℕ) (k : List ℕ → Bool) : Bool :=
  List.rec (motive := fun _ => (List ℕ → Bool) → Bool) (fun k => k [w])
    (fun x xs ih k => Bool.rec (ih (fun l2 => k (x :: l2))) (k (w :: x :: xs)) (Nat.ble w x)) l k

def call (next : List ℕ → Bool) (c : List ℕ) : Bool := Bool.rec false true (next c)

def orB (x y : Bool) : Bool := Bool.rec y true x

def one0 (next : List ℕ → Bool) (base : ℕ) (pre mid post : List ℕ) (w : ℕ) : Bool :=
  Bool.rec false
    (frc w (fun w2 => revK mid post (fun m => revK pre m (fun r =>
      insK w2 r (fun c => call next c)))))
    (Nat.beq (Nat.lor (nsep w) base) M64)

def pair0 (next : List ℕ → Bool) (a b _sa _sb base : ℕ) (pre mid post : List ℕ) : Bool :=
  orB (one0 next base pre mid post (Nat.land a b))
    (one0 next base pre mid post (Nat.lor a b))

def oneG (next : List ℕ → Bool) (extra a b sa sb base : ℕ) (pre mid post : List ℕ) (w : ℕ) :
    Bool :=
  frc w (fun w2 => revK mid post (fun m => revK pre m (fun r =>
    orB (Bool.rec false (insK w2 r (fun c => call next c))
      (Nat.beq (Nat.lor (nsep w2) base) M64))
    (orB (Bool.rec false (insK a r (fun r1 => insK w2 r1 (fun c => call next c)))
      (Nat.beq (Nat.lor (Nat.lor (nsep w2) base) sa) M64))
    (orB (Bool.rec false (insK b r (fun r1 => insK w2 r1 (fun c => call next c)))
      (Nat.beq (Nat.lor (Nat.lor (nsep w2) base) sb) M64))
      (Bool.rec false
        (insK b r (fun r1 => insK a r1 (fun r2 => insK w2 r2 (fun c => call next c))))
        (Nat.ble 2 extra)))))))

def pairG (next : List ℕ → Bool) (extra a b sa sb base : ℕ) (pre mid post : List ℕ) : Bool :=
  orB (oneG next extra a b sa sb base pre mid post (Nat.land a b))
    (oneG next extra a b sa sb base pre mid post (Nat.lor a b))

def innerAux (P : ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → Bool) (a sa : ℕ)
    (pre : List ℕ) (preCut : ℕ) (rest mid : List ℕ) (midCut : ℕ) : Bool :=
  List.rec (motive := fun _ => List ℕ → ℕ → Bool) (fun _ _ => false)
    (fun b post ih mid midCut =>
      Bool.rec (ih (b :: mid) (Nat.lor midCut (nsep b))) true
        (P a b sa (nsep b) (Nat.lor (Nat.lor preCut midCut) (ncuts post)) pre mid post))
    rest mid midCut

def outerAux (P : ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → Bool) (ws pre : List ℕ)
    (preCut : ℕ) : Bool :=
  List.rec (motive := fun _ => List ℕ → ℕ → Bool) (fun _ _ => false)
    (fun a rest ih pre preCut =>
      Bool.rec (ih (a :: pre) (Nat.lor preCut (nsep a))) true
        (innerAux P a (nsep a) pre preCut rest [] 0))
    ws pre preCut

def stepF (k1 : ℕ) (next : List ℕ → Bool) (ws : List ℕ) : Bool :=
  Bool.rec
    (Bool.rec (outerAux (pairG next (Nat.sub (Nat.succ (Nat.succ k1)) (len ws))) ws [] 0)
      (outerAux (pair0 next) ws [] 0) (Nat.beq (len ws) (Nat.succ (Nat.succ k1))))
    true (nisGoal ws)

def nopt (k : ℕ) (ws : List ℕ) : Bool :=
  Nat.rec (motive := fun _ => List ℕ → Bool) (fun ws => nisGoal ws)
    (fun k1 ih ws => stepF k1 ih ws) k ws

def ins (w : ℕ) : List ℕ → List ℕ
  | [] => [w]
  | x :: xs => if Nat.ble w x = true then w :: x :: xs else x :: ins w xs

def cutR (l : List ℕ) : ℕ := l.foldr (fun x c => Nat.lor c (nsep x)) 0
def baseOf (pre mid post : List ℕ) : ℕ := Nat.lor (Nat.lor (cutR pre) (cutR mid)) (ncuts post)
def rOf (pre mid post : List ℕ) : List ℕ := pre.reverse ++ (mid.reverse ++ post)
def opsN (a b : ℕ) : List ℕ := [Nat.land a b, Nat.lor a b]
abbrev Split := List ℕ × ℕ × List ℕ × ℕ × List ℕ

def innerS (pre : List ℕ) (a : ℕ) : List ℕ → List ℕ → List Split
  | [], _ => []
  | b :: post, mid => (pre, a, mid, b, post) :: innerS pre a post (b :: mid)

def outerS : List ℕ → List ℕ → List Split
  | [], _ => []
  | a :: rest, pre => innerS pre a rest [] ++ outerS rest (a :: pre)

def kids0 (base : ℕ) (r : List ℕ) (w : ℕ) : List (List ℕ) :=
  if Nat.beq (Nat.lor (nsep w) base) M64 = true then [ins w r] else []

def kidsG (extra a b sa sb base : ℕ) (r : List ℕ) (w : ℕ) : List (List ℕ) :=
  (if Nat.beq (Nat.lor (nsep w) base) M64 = true then [ins w r] else []) ++
  ((if Nat.beq (Nat.lor (Nat.lor (nsep w) base) sa) M64 = true then [ins w (ins a r)] else []) ++
  ((if Nat.beq (Nat.lor (Nat.lor (nsep w) base) sb) M64 = true then [ins w (ins b r)] else []) ++
   (if Nat.ble 2 extra = true then [ins w (ins a (ins b r))] else [])))

def kidsPair0 (t : Split) : List (List ℕ) :=
  (opsN t.2.1 t.2.2.2.1).flatMap (kids0 (baseOf t.1 t.2.2.1 t.2.2.2.2) (rOf t.1 t.2.2.1 t.2.2.2.2))

def kidsPairG (extra : ℕ) (t : Split) : List (List ℕ) :=
  (opsN t.2.1 t.2.2.2.1).flatMap
    (kidsG extra t.2.1 t.2.2.2.1 (nsep t.2.1) (nsep t.2.2.2.1) (baseOf t.1 t.2.2.1 t.2.2.2.2)
      (rOf t.1 t.2.2.1 t.2.2.2.2))

def kidsL (k1 : ℕ) (ws : List ℕ) : List (List ℕ) :=
  if Nat.beq (len ws) (Nat.succ (Nat.succ k1)) = true then (outerS ws []).flatMap kidsPair0
  else (outerS ws []).flatMap (kidsPairG (Nat.sub (Nat.succ (Nat.succ k1)) (len ws)))

lemma brec {α : Type} (f t : α) (c : Bool) :
    (Bool.rec (motive := fun _ => α) f t c) = if c = true then t else f := by
  cases c <;> rfl

lemma frc_eq (w : ℕ) (k : ℕ → Bool) : frc w k = k w := by cases w <;> rfl

lemma revK_eq (xs : List ℕ) : ∀ (acc : List ℕ) (k : List ℕ → Bool),
    revK xs acc k = k (xs.reverse ++ acc) := by
  induction xs with
  | nil => intro acc k; rfl
  | cons x xs ih =>
    intro acc k
    have e : revK (x :: xs) acc k = revK xs (x :: acc) k := rfl
    rw [e, ih]; simp

lemma insK_eq (w : ℕ) (l : List ℕ) : ∀ k : List ℕ → Bool, insK w l k = k (ins w l) := by
  induction l with
  | nil => intro k; rfl
  | cons x xs ih =>
    intro k
    have e : insK w (x :: xs) k =
        Bool.rec (insK w xs (fun l2 => k (x :: l2))) (k (w :: x :: xs)) (Nat.ble w x) := rfl
    rw [e, brec, ih]
    by_cases h : Nat.ble w x = true <;> simp [ins, h]

lemma call_eq (next : List ℕ → Bool) (c : List ℕ) : call next c = next c := by
  unfold call; cases next c <;> rfl

lemma orB_eq (x y : Bool) : orB x y = (x || y) := by cases x <;> rfl

lemma one0_eq (next : List ℕ → Bool) (base : ℕ) (pre mid post : List ℕ) (w : ℕ) :
    one0 next base pre mid post w = (kids0 base (rOf pre mid post) w).any next := by
  unfold one0 kids0 rOf; rw [brec]
  generalize Nat.beq (Nat.lor (nsep w) base) M64 = c
  cases c <;> simp [frc_eq, revK_eq, insK_eq, call_eq]

lemma oneG_eq (next : List ℕ → Bool) (extra a b sa sb base : ℕ) (pre mid post : List ℕ) (w : ℕ) :
    oneG next extra a b sa sb base pre mid post w =
      (kidsG extra a b sa sb base (rOf pre mid post) w).any next := by
  unfold oneG kidsG rOf
  simp only [frc_eq, revK_eq, insK_eq, call_eq, orB_eq, brec, List.any_append]
  generalize Nat.beq (Nat.lor (nsep w) base) M64 = c1
  generalize Nat.beq (Nat.lor (Nat.lor (nsep w) base) sa) M64 = c2
  generalize Nat.beq (Nat.lor (Nat.lor (nsep w) base) sb) M64 = c3
  generalize Nat.ble 2 extra = c4
  cases c1 <;> cases c2 <;> cases c3 <;> cases c4 <;> simp

lemma pair0_eq (next : List ℕ → Bool) (a b sa sb base : ℕ) (pre mid post : List ℕ) :
    pair0 next a b sa sb base pre mid post =
      ((opsN a b).flatMap (kids0 base (rOf pre mid post))).any next := by
  unfold pair0 opsN
  simp only [orB_eq, one0_eq, List.flatMap_cons, List.flatMap_nil, List.any_append,
    List.any_nil, Bool.or_false]

lemma pairG_eq (next : List ℕ → Bool) (extra a b sa sb base : ℕ) (pre mid post : List ℕ) :
    pairG next extra a b sa sb base pre mid post =
      ((opsN a b).flatMap (kidsG extra a b sa sb base (rOf pre mid post))).any next := by
  unfold pairG opsN
  simp only [orB_eq, oneG_eq, List.flatMap_cons, List.flatMap_nil, List.any_append,
    List.any_nil, Bool.or_false]

def HP (P : ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → Bool) (t : Split) : Bool :=
  P t.2.1 t.2.2.2.1 (nsep t.2.1) (nsep t.2.2.2.1) (baseOf t.1 t.2.2.1 t.2.2.2.2)
    t.1 t.2.2.1 t.2.2.2.2

lemma innerAux_eq (P : ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → Bool) (a : ℕ)
    (pre : List ℕ) : ∀ rest mid : List ℕ,
    innerAux P a (nsep a) pre (cutR pre) rest mid (cutR mid) =
      (innerS pre a rest mid).any (HP P) := by
  intro rest
  induction rest with
  | nil => intro mid; rfl
  | cons b post ih =>
    intro mid
    have e : innerAux P a (nsep a) pre (cutR pre) (b :: post) mid (cutR mid) =
        Bool.rec (innerAux P a (nsep a) pre (cutR pre) post (b :: mid) (Nat.lor (cutR mid) (nsep b)))
          true (P a b (nsep a) (nsep b) (Nat.lor (Nat.lor (cutR pre) (cutR mid)) (ncuts post))
            pre mid post) := rfl
    have c : Nat.lor (cutR mid) (nsep b) = cutR (b :: mid) := rfl
    rw [e, brec, c, ih]
    simp only [innerS, List.any_cons, HP, baseOf]
    cases P a b (nsep a) (nsep b) (Nat.lor (Nat.lor (cutR pre) (cutR mid)) (ncuts post))
      pre mid post <;> simp

lemma outerAux_eq (P : ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → Bool) :
    ∀ ws pre : List ℕ, outerAux P ws pre (cutR pre) = (outerS ws pre).any (HP P) := by
  intro ws
  induction ws with
  | nil => intro pre; rfl
  | cons a rest ih =>
    intro pre
    have e : outerAux P (a :: rest) pre (cutR pre) =
        Bool.rec (outerAux P rest (a :: pre) (Nat.lor (cutR pre) (nsep a))) true
          (innerAux P a (nsep a) pre (cutR pre) rest [] 0) := rfl
    have c : Nat.lor (cutR pre) (nsep a) = cutR (a :: pre) := rfl
    have z : (0 : ℕ) = cutR [] := rfl
    rw [e, brec, c, ih, z, innerAux_eq]
    simp only [outerS, List.any_append]
    cases (innerS pre a rest []).any (HP P) <;> simp

lemma nopt_succ (k : ℕ) (ws : List ℕ) :
    nopt (k + 1) ws = (nisGoal ws || (kidsL k ws).any (nopt k)) := by
  have e : nopt (k + 1) ws = stepF k (nopt k) ws := rfl
  rw [e]
  unfold stepF kidsL
  rw [brec, brec]
  have z : (0 : ℕ) = cutR [] := rfl
  rw [z, outerAux_eq, outerAux_eq]
  have h0 : (outerS ws []).any (HP (pair0 (nopt k))) =
      ((outerS ws []).flatMap kidsPair0).any (nopt k) := by
    rw [List.any_flatMap]
    refine List.any_congr rfl fun t => ?_
    exact pair0_eq (nopt k) t.2.1 t.2.2.2.1 (nsep t.2.1) (nsep t.2.2.2.1)
      (baseOf t.1 t.2.2.1 t.2.2.2.2) t.1 t.2.2.1 t.2.2.2.2
  have hG : ∀ extra, (outerS ws []).any (HP (pairG (nopt k) extra)) =
      ((outerS ws []).flatMap (kidsPairG extra)).any (nopt k) := by
    intro extra
    rw [List.any_flatMap]
    refine List.any_congr rfl fun t => ?_
    exact pairG_eq (nopt k) extra t.2.1 t.2.2.2.1 (nsep t.2.1) (nsep t.2.2.2.1)
      (baseOf t.1 t.2.2.1 t.2.2.2.2) t.1 t.2.2.1 t.2.2.2.2
  rw [h0, hG]
  cases nisGoal ws <;> cases Nat.beq (len ws) (Nat.succ (Nat.succ k)) <;> simp

lemma negOne64 : (-1 : BitVec 64).toNat = M64 := by decide

lemma beq_of_eq {a b : ℕ} (h : a = b) : Nat.beq a b = true := h ▸ Nat.beq_refl a

lemma nsep_toNat (w : W) : nsep w.toNat = (sep w).toNat := by
  simp only [nsep, sep, BitVec.toNat_and, BitVec.toNat_not, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight]
  rfl

lemma ncuts_cons (w : ℕ) (ws : List ℕ) : ncuts (w :: ws) = Nat.lor (nsep w) (ncuts ws) := rfl
lemma cuts_cons (a : W) (l : List W) : cuts (a :: l) = sep a ||| cuts l := rfl

lemma ncuts_map (l : List W) : ncuts (l.map BitVec.toNat) = (cuts l).toNat := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, ncuts_cons, cuts_cons, BitVec.toNat_or, ih, nsep_toNat]; rfl

lemma ncuts_append (l1 l2 : List ℕ) : ncuts (l1 ++ l2) = Nat.lor (ncuts l1) (ncuts l2) := by
  induction l1 with
  | nil => have e : ncuts ([] : List ℕ) = 0 := rfl; rw [List.nil_append, e]; exact (Nat.zero_or _).symm
  | cons a l ih => rw [List.cons_append, ncuts_cons, ih, ncuts_cons]; exact (Nat.or_assoc _ _ _).symm

lemma cutR_eq (l : List ℕ) : cutR l = ncuts l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have e : cutR (a :: l) = Nat.lor (cutR l) (nsep a) := rfl
    rw [e, ih, ncuts_cons]; exact Nat.or_comm _ _

lemma ncuts_reverse (l : List ℕ) : ncuts l.reverse = ncuts l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have e1 : ncuts [a] = nsep a ||| 0 := rfl
    have e2 : ncuts (a :: l) = nsep a ||| ncuts l := rfl
    rw [List.reverse_cons, ncuts_append, ih, e1, e2]
    change (ncuts l ||| (nsep a ||| 0)) = (nsep a ||| ncuts l)
    rw [Nat.or_zero, Nat.or_comm]

lemma baseOf_map (xs ys zs : List W) :
    baseOf (xs.map BitVec.toNat).reverse (ys.map BitVec.toNat).reverse (zs.map BitVec.toNat) =
      (cuts (xs ++ (ys ++ zs))).toNat := by
  rw [← ncuts_map, List.map_append, List.map_append, ncuts_append, ncuts_append]
  unfold baseOf
  rw [cutR_eq, cutR_eq, ncuts_reverse, ncuts_reverse]
  exact Nat.or_assoc _ _ _

lemma opsN_map (a b : W) : opsN a.toNat b.toNat = (ops a b).map BitVec.toNat := by
  simp only [opsN, ops, List.map_cons, List.map_nil, BitVec.toNat_and, BitVec.toNat_or]; rfl

lemma len_eq (l : List ℕ) : len l = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => have e : len (a :: l) = Nat.succ (len l) := rfl; rw [e, ih]; rfl

def insW (w : W) : List W → List W
  | [] => [w]
  | x :: xs => if Nat.ble w.toNat x.toNat = true then w :: x :: xs else x :: insW w xs

lemma insW_map (w : W) (l : List W) : (insW w l).map BitVec.toNat = ins w.toNat (l.map BitVec.toNat) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [insW, ins, List.map_cons]; split_ifs <;> simp [ih]

lemma insW_perm (w : W) (l : List W) : (insW w l).Perm (w :: l) := by
  induction l with
  | nil => exact .refl _
  | cons x xs ih =>
    simp only [insW]; split_ifs
    · exact .refl _
    · exact (ih.cons x).trans (.swap _ _ _)

lemma mem_innerS (pre : List ℕ) (a b : ℕ) (zs : List ℕ) : ∀ ys mid : List ℕ,
    (pre, a, ys.reverse ++ mid, b, zs) ∈ innerS pre a (ys ++ b :: zs) mid := by
  intro ys; induction ys with
  | nil => intro mid; simp [innerS]
  | cons y ys ih =>
    intro mid; simp only [List.cons_append, innerS, List.reverse_cons, List.append_assoc]
    exact List.mem_cons_of_mem _ (ih (y :: mid))

lemma mem_outerS (a b : ℕ) (ys zs : List ℕ) : ∀ xs pre : List ℕ,
    (xs.reverse ++ pre, a, ys.reverse, b, zs) ∈ outerS (xs ++ a :: (ys ++ b :: zs)) pre := by
  intro xs; induction xs with
  | nil =>
    intro pre; simp only [List.nil_append, List.reverse_nil, outerS]
    exact List.mem_append_left _ (by simpa using mem_innerS pre a b zs ys [])
  | cons x xs ih =>
    intro pre; simp only [List.cons_append, outerS, List.reverse_cons, List.append_assoc]
    exact List.mem_append_right _ (ih (x :: pre))

lemma split_two {α : Type} {a b : α} {l : List α} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b) :
    (∃ xs ys zs, l = xs ++ a :: (ys ++ b :: zs)) ∨ (∃ xs ys zs, l = xs ++ b :: (ys ++ a :: zs)) := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem ha
  rcases List.mem_append.mp hb with h | h
  · obtain ⟨s1, s2, rfl⟩ := List.append_of_mem h; exact .inr ⟨s1, s2, t, by simp⟩
  · rcases List.mem_cons.mp h with h | h
    · exact absurd h.symm hne
    · obtain ⟨t1, t2, rfl⟩ := List.append_of_mem h; exact .inl ⟨s, t1, t2, rfl⟩

lemma nisGoal_goal {g : W} (hg : g = target) : nisGoal [g.toNat] = true := by
  subst hg; decide +kernel

lemma guard1 {z : W} {r : List W} (h : cuts (z :: r) = -1) :
    Nat.beq (Nat.lor (nsep z.toNat) (cuts r).toNat) M64 = true := by
  rw [cuts_cons] at h
  have e := congrArg BitVec.toNat h
  rw [BitVec.toNat_or, ← nsep_toNat, negOne64] at e
  exact beq_of_eq e

lemma guard2 {z a : W} {r : List W} (h : cuts (z :: a :: r) = -1) :
    Nat.beq (Nat.lor (Nat.lor (nsep z.toNat) (cuts r).toNat) (nsep a.toNat)) M64 = true := by
  rw [cuts_cons, cuts_cons] at h
  have e := congrArg BitVec.toNat h
  rw [BitVec.toNat_or, BitVec.toNat_or, ← nsep_toNat, ← nsep_toNat, negOne64] at e
  refine beq_of_eq (Eq.trans ?_ e)
  change (nsep z.toNat ||| (cuts r).toNat ||| nsep a.toNat) =
    (nsep z.toNat ||| (nsep a.toNat ||| (cuts r).toNat))
  rw [Nat.or_assoc, Nat.or_comm (cuts r).toNat]

lemma child_of_split {g : W} (hg : g = target) {k : ℕ} {ws xs ys zs : List W}
    {a b z : W} {needed : Finset W} (hn : ws.Nodup)
    (hsplit : ws = xs ++ a :: (ys ++ b :: zs)) (hz : z ∈ basicOps a b) (hout : z ∉ ws.toFinset)
    (hs : ws.toFinset = insert a (insert b needed))
    (tail : live basicOps g k (insert z needed)) :
    ∃ cW : List W, cW.Nodup ∧ cW.length ≤ k + 1 ∧ live basicOps g k cW.toFinset ∧
      cW.map BitVec.toNat ∈ kidsL k (ws.map BitVec.toNat) := by
  have p1 : (xs ++ a :: (ys ++ b :: zs)).Perm (a :: (xs ++ (ys ++ b :: zs))) := List.perm_middle
  have p2 : (xs ++ (ys ++ b :: zs)).Perm (b :: (xs ++ (ys ++ zs))) := by
    rw [← List.append_assoc, ← List.append_assoc]; exact List.perm_middle
  have perm : ws.Perm (a :: b :: (xs ++ (ys ++ zs))) := hsplit ▸ p1.trans (p2.cons a)
  obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hs
  have hznew : z ∉ kept := fun hu =>
    hout (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu))))
  have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
  have hl2 : live basicOps g k (z :: kept).toFinset := by simpa [hfin] using tail
  have hc := live_card hl2
  rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
  have hcut := cuts_full hg hl2
  have hlen2 := perm.length_eq
  simp only [List.length_cons] at hlen2
  have hmap : ws.map BitVec.toNat = xs.map BitVec.toNat ++
      a.toNat :: (ys.map BitVec.toNat ++ b.toNat :: zs.map BitVec.toNat) := by rw [hsplit]; simp
  have ht := mem_outerS a.toNat b.toNat (ys.map BitVec.toNat) (zs.map BitVec.toNat) (xs.map BitVec.toNat) []
  rw [List.append_nil, ← hmap] at ht
  have hzN : z.toNat ∈ opsN a.toNat b.toNat := by
    rw [opsN_map]; exact List.mem_map_of_mem (List.mem_toFinset.mp hz)
  have hr : rOf (xs.map BitVec.toNat).reverse (ys.map BitVec.toNat).reverse (zs.map BitVec.toNat) =
      (xs ++ (ys ++ zs)).map BitVec.toNat := by simp [rOf]
  have hbase := baseOf_map xs ys zs
  have hlenN : len (ws.map BitVec.toNat) = ws.length := by rw [len_eq, List.length_map]
  have live_of (cW : List W) (hp : cW.Perm (z :: kept)) :
      cW.Nodup ∧ cW.length ≤ k + 1 ∧ live basicOps g k cW.toFinset :=
    ⟨hp.nodup_iff.mpr hnd, by rw [hp.length_eq, List.length_cons]; exact hc,
     by rw [List.toFinset_eq_of_perm _ _ hp]; exact hl2⟩
  have hmemL : ∀ {c : List ℕ},
      (Nat.beq (len (ws.map BitVec.toNat)) (Nat.succ (Nat.succ k)) = true →
        c ∈ kids0 (baseOf (xs.map BitVec.toNat).reverse (ys.map BitVec.toNat).reverse (zs.map BitVec.toNat))
          (rOf (xs.map BitVec.toNat).reverse (ys.map BitVec.toNat).reverse (zs.map BitVec.toNat)) z.toNat) →
      (¬ Nat.beq (len (ws.map BitVec.toNat)) (Nat.succ (Nat.succ k)) = true →
        c ∈ kidsG (Nat.sub (Nat.succ (Nat.succ k)) (len (ws.map BitVec.toNat))) a.toNat b.toNat
          (nsep a.toNat) (nsep b.toNat)
          (baseOf (xs.map BitVec.toNat).reverse (ys.map BitVec.toNat).reverse (zs.map BitVec.toNat))
          (rOf (xs.map BitVec.toNat).reverse (ys.map BitVec.toNat).reverse (zs.map BitVec.toNat)) z.toNat) →
      c ∈ kidsL k (ws.map BitVec.toNat) := by
    intro c h0 hG
    unfold kidsL
    split_ifs with hd
    · exact List.mem_flatMap.mpr ⟨_, ht, List.mem_flatMap.mpr ⟨_, hzN, h0 hd⟩⟩
    · exact List.mem_flatMap.mpr ⟨_, ht, List.mem_flatMap.mpr ⟨_, hzN, hG hd⟩⟩
  simp only [keepChoices, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · refine ⟨insW z (xs ++ (ys ++ zs)), (live_of _ (insW_perm _ _)).1, (live_of _ (insW_perm _ _)).2.1,
      (live_of _ (insW_perm _ _)).2.2, ?_⟩
    rw [insW_map]
    refine hmemL (fun _ => ?_) (fun _ => ?_)
    · simp only [hr, hbase, kids0, guard1 hcut, ite_true, List.mem_singleton]
    · simp only [hr, hbase, kidsG, guard1 hcut, ite_true, List.mem_append, List.mem_singleton, true_or]
  · have hp : (insW z (insW a (xs ++ (ys ++ zs)))).Perm (z :: a :: (xs ++ (ys ++ zs))) :=
      (insW_perm _ _).trans ((insW_perm _ _).cons z)
    refine ⟨_, (live_of _ hp).1, (live_of _ hp).2.1, (live_of _ hp).2.2, ?_⟩
    rw [insW_map, insW_map]
    refine hmemL (fun hd => ?_) (fun _ => ?_)
    · exfalso; rw [hlenN] at hd; have := Nat.eq_of_beq_eq_true hd; simp only [List.length_cons] at hc; omega
    · simp only [hr, hbase, kidsG, guard2 hcut, ite_true, List.mem_append, List.mem_singleton, true_or, or_true]
  · have hp : (insW z (insW b (xs ++ (ys ++ zs)))).Perm (z :: b :: (xs ++ (ys ++ zs))) :=
      (insW_perm _ _).trans ((insW_perm _ _).cons z)
    refine ⟨_, (live_of _ hp).1, (live_of _ hp).2.1, (live_of _ hp).2.2, ?_⟩
    rw [insW_map, insW_map]
    refine hmemL (fun hd => ?_) (fun _ => ?_)
    · exfalso; rw [hlenN] at hd; have := Nat.eq_of_beq_eq_true hd; simp only [List.length_cons] at hc; omega
    · simp only [hr, hbase, kidsG, guard2 hcut, ite_true, List.mem_append, List.mem_singleton, true_or, or_true]
  · have hp : (insW z (insW a (insW b (xs ++ (ys ++ zs))))).Perm (z :: a :: b :: (xs ++ (ys ++ zs))) :=
      (insW_perm _ _).trans (((insW_perm _ _).trans ((insW_perm _ _).cons a)).cons z)
    refine ⟨_, (live_of _ hp).1, (live_of _ hp).2.1, (live_of _ hp).2.2, ?_⟩
    rw [insW_map, insW_map, insW_map]
    simp only [List.length_cons] at hc
    refine hmemL (fun hd => ?_) (fun _ => ?_)
    · exfalso; rw [hlenN] at hd; have := Nat.eq_of_beq_eq_true hd; omega
    · have hble : Nat.ble 2 (Nat.sub (Nat.succ (Nat.succ k)) (len (ws.map BitVec.toNat))) = true := by
        rw [hlenN]; apply Nat.ble_eq_true_of_le; change 2 ≤ k + 2 - ws.length; omega
      simp only [hr, kidsG, hble, ite_true, List.mem_append, List.mem_singleton, or_true]

lemma child_exists {g : W} (hg : g = target) {k : ℕ} {ws : List W}
    (hn : ws.Nodup) (hl : live basicOps g (k + 1) ws.toFinset) :
    ws = [g] ∨ ∃ cW : List W, cW.Nodup ∧ cW.length ≤ k + 1 ∧ live basicOps g k cW.toFinset ∧
      cW.map BitVec.toNat ∈ kidsL k (ws.map BitVec.toNat) := by
  rcases first_live hl with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
  · exact .inl (singleton_list hn done)
  · right
    rcases split_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab with
      ⟨xs, ys, zs, e⟩ | ⟨xs, ys, zs, e⟩
    · exact child_of_split hg hn e hz hout hs tail
    · exact child_of_split hg hn e (ops_swap a b ▸ hz) hout (by rw [hs, Finset.insert_comm]) tail

lemma nopt_complete {g : W} (hg : g = target) : ∀ (k : ℕ) (ws : List W),
    ws.Nodup → live basicOps g k ws.toFinset → nopt k (ws.map BitVec.toNat) = true := by
  intro k; induction k with
  | zero => intro ws hn h; rw [singleton_list hn h]; exact nisGoal_goal hg
  | succ k ih =>
    intro ws hn hl
    rw [nopt_succ]
    rcases child_exists hg hn hl with e | ⟨cW, hcn, _, hcl, hmem⟩
    · rw [e]; simp [nisGoal_goal hg]
    · rw [Bool.or_eq_true]; exact .inr (List.any_eq_true.mpr ⟨_, hmem, ih cW hcn hcl⟩)

def rootsN (n : ℕ) (insN : List ℕ) : List (List ℕ) :=
  insN.sublists.filter (fun ws => Nat.ble ws.length (n + 1) && Nat.beq (ncuts ws) M64)

def allKids (m : ℕ) (insN : List ℕ) : List (List ℕ) := (rootsN (m + 1) insN).flatMap (kidsL m)
def isort (l : List ℕ) : List ℕ := l.foldr ins []
def sortK (l : List ℕ) (k : List ℕ → Bool) : Bool :=
  List.rec (motive := fun _ => (List ℕ → Bool) → Bool) (fun k => k [])
    (fun x _ ih k => ih (fun s => frc x (fun x2 => insK x2 s k))) l k

lemma sortK_eq (l : List ℕ) : ∀ k : List ℕ → Bool, sortK l k = k (isort l) := by
  induction l with
  | nil => intro k; rfl
  | cons x xs ih =>
    intro k
    have e : sortK (x :: xs) k = sortK xs (fun s => frc x (fun x2 => insK x2 s k)) := rfl
    rw [e, ih, frc_eq, insK_eq]; rfl

def isortW (l : List W) : List W := l.foldr insW []
lemma isortW_map (l : List W) : (isortW l).map BitVec.toNat = isort (l.map BitVec.toNat) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have e1 : isortW (x :: xs) = insW x (isortW xs) := rfl
    have e2 : isort (x.toNat :: xs.map BitVec.toNat) = ins x.toNat (isort (xs.map BitVec.toNat)) := rfl
    rw [List.map_cons, e1, e2, insW_map, ih]

lemma isortW_perm (l : List W) : (isortW l).Perm l := by
  induction l with
  | nil => exact .refl _
  | cons x xs ih => exact (insW_perm x (isortW xs)).trans (ih.cons x)

def dead (m : ℕ) (c : List ℕ) : Bool := sortK c (fun c2 => Bool.rec true false (nopt m c2))

lemma dead_eq (m : ℕ) (c : List ℕ) : dead m c = !nopt m (isort c) := by
  unfold dead; rw [sortK_eq, brec]; cases nopt m (isort c) <;> rfl

lemma refute (m : ℕ) (inputs : List W) (hnd : inputs.Nodup)
    (h0 : (rootsN (m + 1) (inputs.map BitVec.toNat)).all (fun ws => !nisGoal ws) = true)
    (hk : (allKids m (inputs.map BitVec.toNat)).all (dead m) = true) :
    ∀ t, t = target → build basicOps t (m + 1) inputs.toFinset → False := by
  intro g hg hb
  classical
  obtain ⟨s, hs, hl⟩ := compress hb
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd2 : ws.Nodup := hnd.filter _
  have hl2 : live basicOps g (m + 1) ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl2
  rw [List.toFinset_card_of_nodup hnd2] at sz
  have hroot : ws.map BitVec.toNat ∈ rootsN (m + 1) (inputs.map BitVec.toNat) := by
    unfold rootsN
    refine List.mem_filter.mpr ⟨List.mem_sublists.mpr ((List.filter_sublist).map _), ?_⟩
    rw [Bool.and_eq_true]
    refine ⟨Nat.ble_eq_true_of_le (by rw [List.length_map]; exact sz), ?_⟩
    rw [ncuts_map, cuts_full hg hl2, negOne64]; exact Nat.beq_refl _
  rcases child_exists hg hnd2 hl2 with e | ⟨cW, hcn, _, hcl, hmem⟩
  · have h1 := List.all_eq_true.mp h0 _ hroot
    rw [e] at h1
    simp only [List.map_cons, List.map_nil, nisGoal_goal hg] at h1
    exact absurd h1 (by decide)
  · have hd := List.all_eq_true.mp hk _ (List.mem_flatMap.mpr ⟨_, hroot, hmem⟩)
    have hp := isortW_perm cW
    have e : (isortW cW).toFinset = cW.toFinset := List.toFinset_eq_of_perm _ _ hp
    have run := nopt_complete hg m (isortW cW) (hp.nodup_iff.mpr hcn) (e ▸ hcl)
    rw [isortW_map] at run
    rw [dead_eq, run] at hd
    exact absurd hd (by decide)

end FastA4

def holds (av : Finset W) (z : W) : Prop := z = 0 ∨ z = BitVec.allOnes 128 ∨ z ∈ av
lemma holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h | h | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (Finset.mem_insert_of_mem h))

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

lemma or_all (x : W) : x ||| BitVec.allOnes 128 = BitVec.allOnes 128 := by
  apply BitVec.eq_of_getElem_eq; intro i hi; rw [BitVec.getElem_or, BitVec.getElem_allOnes, Bool.or_true]
lemma all_or (x : W) : BitVec.allOnes 128 ||| x = BitVec.allOnes 128 := by
  apply BitVec.eq_of_getElem_eq; intro i hi; rw [BitVec.getElem_or, BitVec.getElem_allOnes, Bool.true_or]

lemma and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  rcases hx with rfl | rfl | ha
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl (.inl rfl)
  · rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl | rfl | hb
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl (.inl rfl)
  · rw [BitVec.and_allOnes]; exact .inl (.inr (.inr ha))
  by_cases h : x = y
  · subst h; rw [BitVec.and_self]; exact .inl (.inr (.inr ha))
  · exact .inr ⟨x, ha, y, hb, h, x &&& y, by simp [basicOps, ops], .inr (.inr (Finset.mem_insert_self _ _))⟩

lemma or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  rcases hx with rfl | rfl | ha
  · rw [show (0 : W) ||| y = y from BitVec.zero_or]; exact .inl hy
  · rw [all_or]; exact .inl (.inr (.inl rfl))
  rcases hy with rfl | rfl | hb
  · rw [show x ||| (0 : W) = x from BitVec.or_zero]; exact .inl (.inr (.inr ha))
  · rw [or_all]; exact .inl (.inr (.inl rfl))
  by_cases h : x = y
  · subst h; rw [BitVec.or_self]; exact .inl (.inr (.inr ha))
  · exact .inr ⟨x, ha, y, hb, h, x ||| y, by simp [basicOps, ops], .inr (.inr (Finset.mem_insert_self _ _))⟩

def bit128 (k : Fin 128) (z : W) : Bool := z[k.val]
lemma read_bit128 (w : List W) (i : ℕ) (k : Fin 128) :
    (w.map (bit128 k)).getD i false = bit128 k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_none (Nat.le_of_not_gt h), bit128]

lemma bit128_zero (k : Fin 128) : (0 : W)[k.val] = false := by change (0#128)[k.val] = false; simp
lemma bit128_ones (k : Fin 128) : (BitVec.allOnes 128)[k.val] = true := by rw [BitVec.getElem_allOnes]

def action128 (w : List W) (g : Gate) : W := match g.op with
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (BitVec.allOnes 128)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

lemma action128_spec (w : List W) (g : Gate)
    (hg : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) (k : Fin 128) :
    stp (w.map (bit128 k)) g = (w ++ [action128 w g]).map (bit128 k) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or at hop
  change args.length ≤ 2 at cap
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl | rfl <;>
    simp only [stp, List.map_cons, List.map_nil, read_bit128, List.map_append] <;>
    simp only [action128, GateOp.eval, List.foldr_cons, List.foldr_nil, List.all_cons, List.all_nil,
      List.any_cons, List.any_nil, List.map_cons, List.map_nil, id_eq, Bool.and_true,
      Bool.or_false, bit128, BitVec.getElem_and, BitVec.getElem_or, bit128_zero k, bit128_ones k]

lemma available_read128 {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]; exact .inl rfl

lemma gate_reach128 (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) :
    reachable av (action128 w g) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or at hop
  change args.length ≤ 2 at cap
  have hor0 : ∀ x : W, x ||| 0 = x := fun x => BitVec.or_zero
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at cap
  · rcases hop with rfl | rfl
    · exact .inl (.inr (.inl rfl))
    · exact .inl (.inl rfl)
  · rcases hop with rfl | rfl
    · simp only [action128, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, BitVec.and_allOnes]
      exact Or.inl (available_read128 hw i)
    · simp only [action128, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, hor0]
      exact Or.inl (available_read128 hw i)
  · rcases hop with rfl | rfl
    · simp only [action128, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, BitVec.and_allOnes]
      exact and_reach (available_read128 hw i) (available_read128 hw j)
    · simp only [action128, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, hor0]
      exact or_reach (available_read128 hw i) (available_read128 hw j)

lemma compile128 (gs : List Gate) (out : ℕ)
    (hgs : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) :
    ∀ (w : List W) (av : Finset W),
      (∀ u ∈ w, holds av u) →
      (∀ k : Fin 128, (gs.foldl stp (w.map (bit128 k))).getD out false = bit128 k target) →
      build basicOps target gs.length av := by
  induction gs with
  | nil =>
    intro w av hw he
    have heq : w.getD out 0 = target := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      have h1 := he ⟨i, hi⟩
      rw [List.foldl_nil, read_bit128] at h1; exact h1
    rcases available_read128 hw out with h0 | h1 | hm
    · exfalso; rw [heq] at h0; exact absurd h0 (by decide)
    · exfalso; rw [heq] at h1; exact absurd h1 (by decide)
    · rwa [heq] at hm
  | cons g gs ih =>
    intro w av hw he
    have hg := hgs g (List.mem_cons_self ..)
    have htail_ev : ∀ k : Fin 128,
        (gs.foldl stp ((w ++ [action128 w g]).map (bit128 k))).getD out false = bit128 k target := by
      intro k
      have h1 := he k
      rwa [List.foldl_cons, action128_spec w g hg k] at h1
    rcases gate_reach128 w av hw g hg with hhold | ⟨a, ha, b, hb, hab, z, hz, hhold⟩
    · refine Or.inl (ih (fun g' h => hgs g' (List.mem_cons_of_mem g h)) (w ++ [action128 w g]) av ?_ htail_ev)
      intro u hu
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with h | rfl
      · exact hw u h
      · exact hhold
    · refine Or.inr ⟨a, ha, b, hb, hab, z, hz,
        ih (fun g' h => hgs g' (List.mem_cons_of_mem g h)) (w ++ [action128 w g]) (insert z av) ?_ htail_ev⟩
      intro u hu
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with h | rfl
      · exact holds_insert (hw u h)
      · exact hhold

def inputsA4 : List W :=
  [ BitVec.ofNat 128 172471884603763330805475614925919355391,
    BitVec.ofNat 128 18645609146352792516519513385444048384,
    BitVec.ofNat 128 21309267595831762876022336196307582976,
    BitVec.ofNat 128 127855605574990577265357142924097224704,
    BitVec.ofNat 128 215756334407796599138172541819693039616,
    BitVec.ofNat 128 27302499107159446184921552385680080896,
    BitVec.ofNat 128 10654633797915881456439880249753207295,
    BitVec.ofNat 128 86568899608066536683840632976641883648 ]

def uArrA4 : Array (Fin 4) :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 0,
    0, 0, 0, 1, 1, 1, 2, 3, 3, 0, 0, 0, 1, 1, 1, 2, 3, 3, 0, 0, 0, 1, 1, 1, 2, 3, 3, 0, 0, 0, 1, 1,
    1, 2, 3, 3, 0, 0, 0, 1, 1, 1, 2, 3, 3, 0, 0, 0, 1, 1, 1, 2, 3, 3, 0, 0, 0, 1, 1, 1, 2, 3, 3, 0]

def vArrA4 : Array (Fin 4) :=
  #[2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    0, 1, 3, 0, 1, 2, 1, 0, 3, 0, 1, 3, 0, 1, 2, 1, 0, 3, 0, 1, 3, 0, 1, 2, 1, 0, 3, 0, 1, 3, 0, 1,
    2, 1, 0, 3, 0, 1, 3, 0, 1, 2, 1, 0, 3, 0, 1, 3, 0, 1, 2, 1, 0, 3, 0, 1, 3, 0, 1, 2, 1, 0, 3, 0]

def uOfA4 (k : Fin 128) : Fin 4 := uArrA4.getD k.val 0
def vOfA4 (k : Fin 128) : Fin 4 := vArrA4.getD k.val 0

lemma sample_inputsA4 : ∀ k : Fin 128, inputsA4.map (bit128 k) = oneEach (uOfA4 k) (vOfA4 k) := by
  decide +kernel

lemma sample_targetA4 : ∀ k : Fin 128, matA 4 (uOfA4 k) (vOfA4 k) = bit128 k target := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
lemma roots_okA4 :
    (rootsN (7 + 1) (inputsA4.map BitVec.toNat)).all (fun ws => !nisGoal ws) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
lemma kids_okA4 :
    (allKids 7 (inputsA4.map BitVec.toNat)).all (dead 7) = true := by
  decide +kernel

lemma not_rep_A4_8 : ¬ RepSizeAtMost (matA 4) 8 := by
  rintro ⟨C, hmono, hsize, hrep⟩
  have hg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
    intro g h
    obtain ⟨hop, hlen⟩ := hmono g h
    exact ⟨by simpa using hop, hlen⟩
  have he : ∀ k : Fin 128,
      (C.gates.foldl stp (inputsA4.map (bit128 k))).getD C.output false = bit128 k target := by
    intro k
    have h := hrep (uOfA4 k) (vOfA4 k)
    rw [← sample_inputsA4 k, sample_targetA4 k] at h
    exact h
  have run := compile128 C.gates C.output hg inputsA4 inputsA4.toFinset
    (fun u hu => .inr (.inr (List.mem_toFinset.mpr hu))) he
  have lift : ∀ {a b : ℕ}, a ≤ b → build basicOps target a inputsA4.toFinset →
      build basicOps target b inputsA4.toFinset := by
    intro a b h hr
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact refute 7 inputsA4 (by decide) roots_okA4 kids_okA4 target rfl (lift hsize run)

-- ============================================================
-- Combine Part 3A (restrict n+1 -> n drops >= 2) with Part 3B (n = 4)
-- ============================================================

lemma ofFn_append_getD_left {α : Type} {m : ℕ} (f g : Fin m → α) (d : α) {k : ℕ} (hk : k < m) :
    (List.ofFn f ++ List.ofFn g).getD k d = f ⟨k, hk⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hk]), List.getElem?_ofFn]
  simp [hk]

lemma ofFn_append_getD_right {α : Type} {m : ℕ} (f g : Fin m → α) (d : α) {k : ℕ} (hk : k < m) :
    (List.ofFn f ++ List.ofFn g).getD (m + k) d = g ⟨k, hk⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp), List.length_ofFn,
    Nat.add_sub_cancel_left, List.getElem?_ofFn]
  simp [hk]

def initEnv (n : ℕ) : List (Option ℕ) :=
  List.ofFn (fun i : Fin (n + 1) => if i.val < n then some i.val else none) ++
  List.ofFn (fun j : Fin (n + 1) => if j.val < n then some (n + j.val) else none)

lemma initEnv_len (n : ℕ) : (initEnv n).length = 2 * n + 2 := by
  simp [initEnv]; omega

lemma initEnv_getD_left (n : ℕ) {k : ℕ} (hk : k < n + 1) :
    (initEnv n).getD k none = if k < n then some k else none := by
  exact ofFn_append_getD_left _ _ none hk

lemma initEnv_getD_right (n : ℕ) {k : ℕ} (hk : k < n + 1) :
    (initEnv n).getD (n + 1 + k) none = if k < n then some (n + k) else none := by
  exact ofFn_append_getD_right _ _ none hk

lemma restrict_step (n s : ℕ) (hn : 4 ≤ n) (hrep : RepSizeAtMost (matA (n + 1)) (s + 2)) :
    RepSizeAtMost (matA n) s := by
  obtain ⟨C, hmono, hsize, hrepC⟩ := hrep
  have hgs : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨hop, hlen⟩ := hmono g hg
    exact ⟨by simpa using hop, hlen⟩
  let env0 := initEnv n
  have henv0_len : env0.length = 2 * n + 2 := initEnv_len n
  have hbound0 : ∀ i j, env0.getD i none = some j → j < 2 * n + ([] : List Gate).length := by
    intro i j hij
    by_cases h1 : i < n + 1
    · rw [initEnv_getD_left n h1] at hij
      split_ifs at hij with hlt
      · cases hij; simp; omega
    · by_cases h2 : i < 2 * n + 2
      · have hkm : i - (n + 1) < n + 1 := by omega
        have heq : i = n + 1 + (i - (n + 1)) := by omega
        rw [heq, initEnv_getD_right n hkm] at hij
        split_ifs at hij with hlt
        · cases hij; simp; omega
      · rw [List.getD_eq_default _ _ (by omega)] at hij; cases hij
  have hmatch0 : ∀ (u v : Fin n) (i : ℕ),
      (oneEach u.castSucc v.castSucc).getD i false =
        match env0.getD i none with | none => false | some j => (oneEach u v).getD j false := by
    intro u v i
    by_cases h1 : i < n + 1
    · rw [oneEach_getD_left u.castSucc v.castSucc h1, initEnv_getD_left n h1]
      split_ifs with hlt
      · dsimp only; rw [oneEach_getD_left u v hlt]; rfl
      · have : u.val ≠ i := by have := u.isLt; omega
        simp [this]
    · by_cases h2 : i < 2 * n + 2
      · have hkm : i - (n + 1) < n + 1 := by omega
        have heq : i = n + 1 + (i - (n + 1)) := by omega
        rw [heq, oneEach_getD_right u.castSucc v.castSucc hkm, initEnv_getD_right n hkm]
        split_ifs with hlt
        · dsimp only; rw [oneEach_getD_right u v hlt]; rfl
        · have : v.val ≠ i - (n + 1) := by have := v.isLt; omega
          simp [this]
      · rw [List.getD_eq_default _ _ (by rw [oneEach_len]; omega),
            List.getD_eq_default _ _ (by omega)]
  set res := C.gates.foldl (elimStep (2 * n)) (env0, [])
  have hspec := fun u v : Fin n =>
    elim_foldl_spec (2 * n) C.gates hgs (env0, []) (fun _ h => by cases h) hbound0
      (oneEach u.castSucc v.castSucc) (oneEach u v)
      (by rw [oneEach_len, henv0_len]; omega) (by rw [oneEach_len]; simp; omega) (hmatch0 u v)
  have hout_some : res.1.getD C.output none ≠ none := by
    intro hnone
    let p2 : Fin n := ⟨2, by omega⟩
    have h1 := (hspec p2 p2).2.2.2 C.output
    rw [hnone] at h1
    have h2 : C.eval (oneEach p2.castSucc p2.castSucc) = true := by
      rw [hrepC]; simp [matA, p2]
    rw [eval_eq, h1] at h2
    cases h2
  obtain ⟨out', hout'⟩ := Option.ne_none_iff_exists'.mp hout_some
  -- Prove res.2.length + 2 <= C.gates.length (hence res.2.length <= s)
  have hdrop2 : res.2.length + 2 ≤ C.gates.length := by
    by_contra hlt
    have hcontra_u : ∀ (bad : ℕ → Prop),
        bad n → ¬ bad C.output →
        (∀ i < 2 * n + 2, i ≠ n → ¬ bad i) →
        (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → ¬ bad (2 * n + 2 + j) → ∀ a ∈ g.inputs, ¬ bad a) →
        False := by
      intro bad hbn hbo hother hgood
      let ln : Fin (n + 1) := ⟨n, by omega⟩
      let l0 : Fin (n + 1) := ⟨0, by omega⟩
      let x1 := oneEach ln ln
      let x0 := List.ofFn (fun _ : Fin (n + 1) => false) ++ List.ofFn (fun j : Fin (n + 1) => decide (j = ln))
      let x2 := oneEach l0 ln
      have hx1_len : x1.length = 2 * n + 2 := by rw [oneEach_len]; omega
      have hx0_len : x0.length = 2 * n + 2 := by simp [x0]; omega
      have hx2_len : x2.length = 2 * n + 2 := by rw [oneEach_len]; omega
      have heq01 : C.eval x1 = C.eval x0 := by
        rw [eval_eq, eval_eq]
        apply bad_wire_indep C.gates bad x1 x0 (by omega) (by simpa [hx1_len] using hgood) ?_ C.output hbo
        intro i hi hnb
        have hin : i ≠ n := fun e => hnb (e ▸ hbn)
        by_cases h1 : i < n + 1
        · rw [oneEach_getD_left ln ln h1, ofFn_append_getD_left _ _ false h1]
          simp [ln, hin.symm]
        · have hkm : i - (n + 1) < n + 1 := by omega
          have heq : i = n + 1 + (i - (n + 1)) := by omega
          rw [heq, oneEach_getD_right ln ln hkm, ofFn_append_getD_right _ _ false hkm]
          simp [Fin.ext_iff, eq_comm]
      have hx1_true : C.eval x1 = true := by rw [hrepC]; simp [matA, ln, hn]
      have hx0_true : C.eval x0 = true := by rw [← heq01, hx1_true]
      have hx2_true : C.eval x2 = true := by
        rw [eval_eq] at hx0_true ⊢
        apply mono2_eval_mono C.gates hgs x0 x2 (by omega) ?_ C.output hx0_true
        intro i hi
        by_cases h1 : i < n + 1
        · rw [ofFn_append_getD_left _ _ false h1] at hi; cases hi
        · by_cases h2 : i < 2 * n + 2
          · have hkm : i - (n + 1) < n + 1 := by omega
            have heq : i = n + 1 + (i - (n + 1)) := by omega
            rw [heq] at hi ⊢
            rw [ofFn_append_getD_right _ _ false hkm] at hi
            rw [oneEach_getD_right l0 ln hkm]
            simpa [Fin.ext_iff, eq_comm] using hi
          · rw [List.getD_eq_default _ _ (by omega)] at hi; cases hi
      rw [hrepC] at hx2_true
      simp [matA, l0, ln, show ¬(4 ≤ 0) by omega, show n ≠ 1 by omega, show n ≠ 2 by omega] at hx2_true
    have hcontra_v : ∀ (bad : ℕ → Prop),
        bad (2 * n + 1) → ¬ bad C.output →
        (∀ i < 2 * n + 2, i ≠ 2 * n + 1 → ¬ bad i) →
        (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → ¬ bad (2 * n + 2 + j) → ∀ a ∈ g.inputs, ¬ bad a) →
        False := by
      intro bad hbv hbo hother hgood
      let ln : Fin (n + 1) := ⟨n, by omega⟩
      let l0 : Fin (n + 1) := ⟨0, by omega⟩
      let x1 := oneEach ln ln
      let x0 := List.ofFn (fun i : Fin (n + 1) => decide (i = ln)) ++ List.ofFn (fun _ : Fin (n + 1) => false)
      let x2 := oneEach ln l0
      have hx1_len : x1.length = 2 * n + 2 := by rw [oneEach_len]; omega
      have hx0_len : x0.length = 2 * n + 2 := by simp [x0]; omega
      have hx2_len : x2.length = 2 * n + 2 := by rw [oneEach_len]; omega
      have heq01 : C.eval x1 = C.eval x0 := by
        rw [eval_eq, eval_eq]
        apply bad_wire_indep C.gates bad x1 x0 (by omega) (by simpa [hx1_len] using hgood) ?_ C.output hbo
        intro i hi hnb
        have hiv : i ≠ 2 * n + 1 := fun e => hnb (e ▸ hbv)
        by_cases h1 : i < n + 1
        · rw [oneEach_getD_left ln ln h1, ofFn_append_getD_left _ _ false h1]
          simp [Fin.ext_iff, eq_comm]
        · have hkm : i - (n + 1) < n + 1 := by omega
          have heq : i = n + 1 + (i - (n + 1)) := by omega
          rw [heq, oneEach_getD_right ln ln hkm, ofFn_append_getD_right _ _ false hkm]
          have hne : n ≠ i - (n + 1) := by omega
          simp [ln, hne]
      have hx1_true : C.eval x1 = true := by rw [hrepC]; simp [matA, ln, hn]
      have hx0_true : C.eval x0 = true := by rw [← heq01, hx1_true]
      have hx2_true : C.eval x2 = true := by
        rw [eval_eq] at hx0_true ⊢
        apply mono2_eval_mono C.gates hgs x0 x2 (by omega) ?_ C.output hx0_true
        intro i hi
        by_cases h1 : i < n + 1
        · rw [ofFn_append_getD_left _ _ false h1] at hi
          rw [oneEach_getD_left ln l0 h1]
          simpa [Fin.ext_iff, eq_comm] using hi
        · by_cases h2 : i < 2 * n + 2
          · have hkm : i - (n + 1) < n + 1 := by omega
            have heq : i = n + 1 + (i - (n + 1)) := by omega
            rw [heq, ofFn_append_getD_right _ _ false hkm] at hi; cases hi
          · rw [List.getD_eq_default _ _ (by omega)] at hi; cases hi
      rw [hrepC] at hx2_true
      simp [matA, l0, ln, show n ≠ 1 by omega, show n ≠ 2 by omega] at hx2_true
      omega
    have hlen_le : ∀ (l : List Gate) (st : List (Option ℕ) × List Gate),
        (l.foldl (elimStep (2 * n)) st).2.length ≤ st.2.length + l.length := by
      intro l; induction l with
      | nil => intro st; simp
      | cons x xs ihx =>
        intro st; have hx := elimStep_len (2 * n) st x; have hxs := ihx (elimStep (2 * n) st x)
        simp only [List.foldl_cons, List.length_cons]; omega
    have hzero_drop : ∀ (gs2 : List Gate) (st : List (Option ℕ) × List Gate),
        (gs2.foldl (elimStep (2 * n)) st).2.length = st.2.length + gs2.length →
        ∀ g ∈ gs2, ∀ a ∈ g.inputs, (gs2.foldl (elimStep (2 * n)) st).1.getD a none ≠ none := by
      intro gs2; induction gs2 with
      | nil => intro st _ g hg; cases hg
      | cons g2 tl2 ih2 =>
        intro st hlen g hg a ha
        have h1 := elimStep_len (2 * n) st g2
        have h2 := hlen_le tl2 (elimStep (2 * n) st g2)
        simp only [List.foldl_cons, List.length_cons] at hlen
        have hkept1 : (elimStep (2 * n) st g2).2.length = st.2.length + 1 := by omega
        have hkept2 : (tl2.foldl (elimStep (2 * n)) (elimStep (2 * n) st g2)).2.length =
            (elimStep (2 * n) st g2).2.length + tl2.length := by omega
        rcases List.mem_cons.mp hg with rfl | hmem
        · have hne := elimStep_kept_inputs (2 * n) st g hkept1 a ha
          have halt : a < st.1.length := by by_contra hge; apply hne; rw [List.getD_eq_default _ _ (by omega)]
          have hp : IsInit st.1 (tl2.foldl (elimStep (2 * n)) (elimStep (2 * n) st g)).1 :=
            isInit_trans (elimStep_isInit_env (2 * n) st g) (elim_foldl_isInit_env (2 * n) tl2 _)
          rw [List.foldl_cons, isInit_getD_opt hp halt]; exact hne
        · exact ih2 (elimStep (2 * n) st g2) hkept2 g hmem a ha
    have hu0 : env0.getD n none = none := by rw [initEnv_getD_left n (by omega)]; simp
    have hv0 : env0.getD (2 * n + 1) none = none := by
      have : 2 * n + 1 = n + 1 + n := by omega
      rw [this, initEnv_getD_right n (by omega)]; simp
    have hu_res : res.1.getD n none = none := by
      have hlt_u : n < (env0, ([] : List Gate)).1.length := by simp only [henv0_len]; omega
      rw [isInit_getD_opt (elim_foldl_isInit_env (2 * n) C.gates (env0, [])) hlt_u]; exact hu0
    have hv_res : res.1.getD (2 * n + 1) none = none := by
      have hlt_v : 2 * n + 1 < (env0, ([] : List Gate)).1.length := by simp only [henv0_len]; omega
      rw [isInit_getD_opt (elim_foldl_isInit_env (2 * n) C.gates (env0, [])) hlt_v]; exact hv0
    have hle_all : res.2.length ≤ C.gates.length := by simpa [res] using hlen_le C.gates (env0, [])
    by_cases h0 : res.2.length = C.gates.length
    · have hall := hzero_drop C.gates (env0, []) (by simpa [res] using h0)
      apply hcontra_u (fun i => i = n) rfl (fun e => by rw [e] at hout_some; exact hout_some hu_res) (fun i _ hin => hin)
      intro j g hj _ a ha he
      have hmem : g ∈ C.gates := List.mem_of_getElem? hj
      exact hall g hmem a ha (by rw [he]; exact hu_res)
    · have h1drop : C.gates.length = res.2.length + 1 := by omega
      have hsplit : ∀ (l : List Gate) (st : List (Option ℕ) × List Gate),
          (l.foldl (elimStep (2 * n)) st).2.length + 1 = st.2.length + l.length →
          ∃ pre g0 post, l = pre ++ g0 :: post ∧
            (pre.foldl (elimStep (2 * n)) st).2.length = st.2.length + pre.length ∧
            (elimStep (2 * n) (pre.foldl (elimStep (2 * n)) st) g0).2.length = (pre.foldl (elimStep (2 * n)) st).2.length ∧
            (post.foldl (elimStep (2 * n)) (elimStep (2 * n) (pre.foldl (elimStep (2 * n)) st) g0)).2.length =
              (elimStep (2 * n) (pre.foldl (elimStep (2 * n)) st) g0).2.length + post.length := by
        intro l; induction l with
        | nil => intro st h; simp at h
        | cons x xs ihx =>
          intro st h
          have hx := elimStep_len (2 * n) st x
          have hle2 := hlen_le xs (elimStep (2 * n) st x)
          simp only [List.foldl_cons, List.length_cons] at h
          by_cases hkx : (elimStep (2 * n) st x).2.length = st.2.length + 1
          · obtain ⟨pre, g0, post, rfl, hp1, hp2, hp3⟩ := ihx (elimStep (2 * n) st x) (by omega)
            exact ⟨x :: pre, g0, post, rfl, by simpa [List.foldl_cons, List.length_cons] using by omega,
              by simpa [List.foldl_cons] using hp2, by simpa [List.foldl_cons] using hp3⟩
          · have hge : st.2.length ≤ (elimStep (2 * n) st x).2.length :=
              isInit_len_le (elimStep_isInit_gates (2 * n) st x)
            have hkx0 : (elimStep (2 * n) st x).2.length = st.2.length := by omega
            exact ⟨[], x, xs, rfl, by simp, hkx0, by simp only [List.foldl_nil]; omega⟩
      obtain ⟨pre, g0, post, hgs_eq, hpre0, hg0drop, hpost0⟩ :=
        hsplit C.gates (env0, []) (by simpa [res] using h1drop.symm)
      set stP := pre.foldl (elimStep (2 * n)) (env0, [])
      set stM := elimStep (2 * n) stP g0
      have hres_eq : res = post.foldl (elimStep (2 * n)) stM := by
        simp [res, hgs_eq, List.foldl_append, stP, stM]
      have hstP_len : stP.1.length = 2 * n + 2 + pre.length := by
        have hlen_env : ∀ (l : List Gate) (s0 : List (Option ℕ) × List Gate),
            (l.foldl (elimStep (2 * n)) s0).1.length = s0.1.length + l.length := by
          intro l; induction l with
          | nil => intro s0; simp
          | cons y ys ihy =>
            intro s0; simp only [List.foldl_cons, ihy, (elimStep_len (2 * n) s0 y).1, List.length_cons]; omega
        rw [hlen_env pre (env0, []), henv0_len]
      have hpre_ok := hzero_drop pre (env0, []) hpre0
      have hpost_ok := hzero_drop post stM hpost0
      have hstP_init : IsInit stP.1 res.1 := by
        rw [hres_eq]
        exact isInit_trans (elimStep_isInit_env (2 * n) stP g0) (elim_foldl_isInit_env (2 * n) post stM)
      have hpre_ok_res : ∀ g ∈ pre, ∀ a ∈ g.inputs, res.1.getD a none ≠ none := by
        intro g hg a ha
        have hne : stP.1.getD a none ≠ none := hpre_ok g hg a ha
        have halt : a < stP.1.length := by by_contra hge; apply hne; rw [List.getD_eq_default _ _ (by omega)]
        rw [isInit_getD_opt hstP_init halt]; exact hne
      have hpost_ok_res : ∀ g ∈ post, ∀ a ∈ g.inputs, res.1.getD a none ≠ none := by
        intro g hg a ha; rw [hres_eq]; exact hpost_ok g hg a ha
      have hu_stP : stP.1.getD n none = none := by
        have hlt_u : n < (env0, ([] : List Gate)).1.length := by simp only [henv0_len]; omega
        rw [isInit_getD_opt (elim_foldl_isInit_env (2 * n) pre (env0, [])) hlt_u]; exact hu0
      have hv_stP : stP.1.getD (2 * n + 1) none = none := by
        have hlt_v : 2 * n + 1 < (env0, ([] : List Gate)).1.length := by simp only [henv0_len]; omega
        rw [isInit_getD_opt (elim_foldl_isInit_env (2 * n) pre (env0, [])) hlt_v]; exact hv0
      by_cases hmid : stM.1.getD stP.1.length none = none
      · have hmid_res : res.1.getD (2 * n + 2 + pre.length) none = none := by
          have hpM : IsInit stM.1 res.1 := by rw [hres_eq]; exact elim_foldl_isInit_env (2 * n) post stM
          have hltM : stP.1.length < stM.1.length := by rw [(elimStep_len (2 * n) stP g0).1]; omega
          rw [← hstP_len, isInit_getD_opt hpM hltM]; exact hmid
        apply hcontra_u (fun i => i = n ∨ i = 2 * n + 2 + pre.length) (Or.inl rfl)
          (by rintro (he | he); rw [he] at hout_some; exact hout_some hu_res; rw [he] at hout_some; exact hout_some hmid_res)
          (fun i hi hin => by rintro (h | h) <;> omega)
        intro j g hj hnb a ha hbad
        rw [hgs_eq] at hj
        by_cases hjp : j < pre.length
        · rw [List.getElem?_append_left hjp] at hj
          have hg_mem : g ∈ pre := List.mem_of_getElem? hj
          rcases hbad with ha_eq | ha_eq
          · rw [ha_eq] at ha; exact hpre_ok_res g hg_mem n ha hu_res
          · rw [ha_eq] at ha; exact hpre_ok_res g hg_mem _ ha hmid_res
        · by_cases hje : j = pre.length
          · exact hnb (Or.inr (by omega))
          · have hgt : pre.length + 1 ≤ j := by omega
            rw [List.getElem?_append_right (by omega)] at hj
            have hsub : j - pre.length = (j - pre.length - 1) + 1 := by omega
            rw [hsub, List.getElem?_cons_succ] at hj
            have hg_mem : g ∈ post := List.mem_of_getElem? hj
            rcases hbad with ha_eq | ha_eq
            · rw [ha_eq] at ha; exact hpost_ok_res g hg_mem n ha hu_res
            · rw [ha_eq] at ha; exact hpost_ok_res g hg_mem _ ha hmid_res
      · have hg0_mem : g0 ∈ C.gates := by rw [hgs_eq]; simp
        have hnotboth := elimStep_dropped_some_not_both (2 * n) stP g0 (hgs g0 hg0_mem) n (2 * n + 1)
          (by omega) hu_stP hv_stP hmid
        rcases hnotboth with hu_g0 | hv_g0
        · apply hcontra_u (fun i => i = n) rfl (fun e => by rw [e] at hout_some; exact hout_some hu_res) (fun i _ hin => hin)
          intro j g hj _ a ha hbad
          rw [hbad] at ha
          have hg_mem : g ∈ C.gates := List.mem_of_getElem? hj
          rw [hgs_eq] at hg_mem
          simp only [List.mem_append, List.mem_cons] at hg_mem
          rcases hg_mem with h | rfl | h
          · exact hpre_ok_res g h n ha hu_res
          · exact hu_g0 ha
          · exact hpost_ok_res g h n ha hu_res
        · apply hcontra_v (fun i => i = 2 * n + 1) rfl (fun e => by rw [e] at hout_some; exact hout_some hv_res) (fun i _ hiv => hiv)
          intro j g hj _ a ha hbad
          rw [hbad] at ha
          have hg_mem : g ∈ C.gates := List.mem_of_getElem? hj
          rw [hgs_eq] at hg_mem
          simp only [List.mem_append, List.mem_cons] at hg_mem
          rcases hg_mem with h | rfl | h
          · exact hpre_ok_res g h (2 * n + 1) ha hv_res
          · exact hv_g0 ha
          · exact hpost_ok_res g h (2 * n + 1) ha hv_res
  -- Construct C' = ⟨res.2, out'⟩
  refine ⟨⟨res.2, out'⟩, ?_, ?_, ?_⟩
  · intro g hg
    have h := (hspec ⟨0, by omega⟩ ⟨0, by omega⟩).2.2.1 g hg
    exact ⟨by simpa using h.1, h.2⟩
  · simp only [Circuit.size] at hsize ⊢
    omega
  · intro u v
    have h1 := (hspec u v).2.2.2 C.output
    rw [hout'] at h1
    have h2 : C.eval (oneEach u.castSucc v.castSucc) = matA (n + 1) u.castSucc v.castSucc :=
      hrepC u.castSucc v.castSucc
    rw [eval_eq, h1] at h2
    dsimp only at h2
    rw [List.length_nil, List.drop_zero] at h2
    rw [eval_eq]
    change (res.2.foldl stp (oneEach u v)).getD out' false = _
    rw [h2]
    unfold matA
    simp [Fin.ext_iff]

lemma part3 (n : ℕ) (hn : 4 ≤ n) : ¬ RepSizeAtMost (matA n) (2 * n) := by
  induction n, hn using Nat.le_induction with
  | base => exact not_rep_A4_8
  | succ k hk ih =>
    intro h
    exact ih (restrict_step k (2 * k) hk (by simpa [Nat.mul_add] using h))

end PEqualNP.Outside.L_meta_26748_aux

theorem PEqualNP.Outside.L_meta_26748 :
    ∀ (n : Nat), 4 ≤ n →
      let A := fun (i j : Fin n) =>
        ((if i.val = 1 ∨ j.val = 1 then decide (i.val = 3 ∨ j.val = 3)
          else decide (i.val = 2 ∨ j.val = 2)) || decide (4 ≤ i.val ∧ i = j))
      (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.Represents.Represents A C ∧
        C.size = 2*n-1 ∧ ∃! j : Fin C.gates.length,
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      (∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C →
        2*n-1 ≤ C.size) ∧
      (¬ PEqualNP.Represents.RepSizeAtMost A (2*n)) ∧
        PEqualNP.Represents.RepSizeAtMost A (4*n-7) := by
  intro n hn
  refine ⟨PEqualNP.Outside.L_meta_26748_aux.part1 n hn,
          PEqualNP.Outside.L_meta_26748_aux.part2 n hn,
          PEqualNP.Outside.L_meta_26748_aux.part3 n hn,
          PEqualNP.Outside.L_meta_26748_aux.part4 n hn⟩
