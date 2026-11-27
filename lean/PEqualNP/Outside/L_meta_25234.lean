import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25234

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def orG (a b : ℕ) : Gate :=
  { op := GateOp.or, inputs := [a, b] }

def andG (a b : ℕ) : Gate :=
  { op := GateOp.and, inputs := [a, b] }

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl step w

def orChain (acc next base : ℕ) : ℕ → List Gate
  | 0 => []
  | k + 1 => orG acc next :: orChain base (next + 1) (base + 1) k

def orChainOut (acc base : ℕ) : ℕ → ℕ
  | 0 => acc
  | k + 1 => base + k

def finalGates (n iY iR b : ℕ) : List Gate :=
  [ orG (n + 1) iY
  , andG 0 b
  , orG n iY
  , andG 1 (b + 2)
  , andG n iR
  , orG (b + 1) (b + 3)
  , orG (b + 5) (b + 4)
  ]

def buildCircuit (n : ℕ) : Circuit :=
  let k := n - 3
  let gY := orChain (n + 2) (n + 3) (2 * n) k
  let iY := orChainOut (n + 2) (2 * n) k
  let b1 := 2 * n + k
  let gR := orChain 2 3 b1 k
  let iR := orChainOut 2 b1 k
  let b2 := b1 + k
  { gates := gY ++ gR ++ finalGates n iY iR b2
  , output := b2 + 6 }

lemma bool_eq_of_iff {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

lemma getD_append_left_lt (a b : List Bool) (i : ℕ) (hi : i < a.length) :
    (a ++ b).getD i false = a.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_right_le (a b : List Bool) (i : ℕ) (hi : a.length ≤ i) :
    (a ++ b).getD i false = b.getD (i - a.length) false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

lemma step_orG (w : List Bool) (a b : ℕ) :
    step w (orG a b) = w ++ [w.getD a false || w.getD b false] := by
  simp [step, orG, GateOp.eval]

lemma step_andG (w : List Bool) (a b : ℕ) :
    step w (andG a b) = w ++ [w.getD a false && w.getD b false] := by
  simp [step, andG, GateOp.eval]

lemma run_append (gs1 gs2 : List Gate) (w : List Bool) :
    run (gs1 ++ gs2) w = run gs2 (run gs1 w) := by
  simp [run, List.foldl_append]

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    rw [run, List.foldl_cons]
    change (run gs (step w g)).length = _
    rw [ih]
    simp [step]
    omega

lemma run_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have h1 : i < (step w g).length := by
      simp [step]
      omega
    rw [run, List.foldl_cons]
    change (run gs (step w g)).getD i false = w.getD i false
    rw [ih (step w g) h1]
    exact getD_append_left_lt w _ i hi

lemma orChain_length (acc next base k : ℕ) :
    (orChain acc next base k).length = k := by
  induction k generalizing acc next base with
  | zero => rfl
  | succ k ih => simp [orChain, ih]

lemma orChainOut_lt (acc base k : ℕ) (hacc : acc < base) :
    orChainOut acc base k < base + k := by
  cases k with
  | zero => simpa [orChainOut] using hacc
  | succ k => simp [orChainOut]

lemma orChain_mono (acc next base k : ℕ) :
    ∀ g ∈ orChain acc next base k,
      g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction k generalizing acc next base with
  | zero =>
    intro g hg
    cases hg
  | succ k ih =>
    intro g hg
    simp only [orChain, List.mem_cons] at hg
    rcases hg with rfl | hg
    · simp [orG]
    · exact ih base (next + 1) (base + 1) g hg

lemma orChain_eval (k acc next base : ℕ) (w : List Bool)
    (hlen : w.length = base) (hacc : acc < base) (hnext : next + k ≤ base) :
    (run (orChain acc next base k) w).getD (orChainOut acc base k) false =
      (w.getD acc false || decide (∃ j : ℕ, j < k ∧ w.getD (next + j) false = true)) := by
  induction k generalizing acc next base w with
  | zero =>
    simp [orChain, orChainOut, run]
  | succ m ih =>
    have hout : orChainOut acc base (m + 1) = orChainOut base (base + 1) m := by
      cases m with
      | zero => simp [orChainOut]
      | succ m' =>
        simp [orChainOut]
        omega
    rw [orChain, hout]
    change (run (orChain base (next + 1) (base + 1) m) (step w (orG acc next))).getD
      (orChainOut base (base + 1) m) false = _
    have hlen' : (step w (orG acc next)).length = base + 1 := by
      simp [step, hlen]
    have hacc' : base < base + 1 := by omega
    have hnext' : (next + 1) + m ≤ base + 1 := by omega
    rw [ih base (next + 1) (base + 1) (step w (orG acc next)) hlen' hacc' hnext']
    have hbase : (step w (orG acc next)).getD base false =
        (w.getD acc false || w.getD next false) := by
      rw [step_orG, ← hlen, getD_append_right_le w _ w.length (le_refl _)]
      simp
    rw [hbase]
    have hex : (∃ j : ℕ, j < m ∧ (step w (orG acc next)).getD (next + 1 + j) false = true) ↔
        (∃ j : ℕ, j < m ∧ w.getD (next + (j + 1)) false = true) := by
      constructor
      · rintro ⟨j, hj, hval⟩
        refine ⟨j, hj, ?_⟩
        have hlt : next + 1 + j < w.length := by omega
        rw [step_orG, getD_append_left_lt w _ _ hlt] at hval
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hval
      · rintro ⟨j, hj, hval⟩
        refine ⟨j, hj, ?_⟩
        have hlt : next + 1 + j < w.length := by omega
        rw [step_orG, getD_append_left_lt w _ _ hlt]
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hval
    have hiff : ((w.getD acc false || w.getD next false) ||
          decide (∃ j : ℕ, j < m ∧ (step w (orG acc next)).getD (next + 1 + j) false = true)) = true ↔
        (w.getD acc false ||
          decide (∃ j : ℕ, j < m + 1 ∧ w.getD (next + j) false = true)) = true := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, hex]
      constructor
      · rintro ((ha | h0) | ⟨j, hj, hv⟩)
        · exact Or.inl ha
        · exact Or.inr ⟨0, by omega, by simpa using h0⟩
        · exact Or.inr ⟨j + 1, by omega, hv⟩
      · rintro (ha | ⟨j, hj, hv⟩)
        · exact Or.inl (Or.inl ha)
        · cases j with
          | zero => exact Or.inl (Or.inr (by simpa using hv))
          | succ j' => exact Or.inr ⟨j', by omega, hv⟩
    exact bool_eq_of_iff hiff

lemma oneEach_length {n : ℕ} (u v : Fin n) :
    (oneEach u v).length = 2 * n := by
  simp [oneEach]
  omega

lemma oneEach_getD_left {n : ℕ} (u v : Fin n) (i : ℕ) (hi : i < n) :
    (oneEach u v).getD i false = decide (i = u.val) := by
  unfold oneEach
  have hlen : (List.ofFn (fun x : Fin n => decide (x = u))).length = n := by simp
  rw [getD_append_left_lt _ _ i (by omega)]
  simp [List.getD_eq_getElem?_getD, hi, Fin.ext_iff]

lemma oneEach_getD_right {n : ℕ} (u v : Fin n) (j : ℕ) (hj : j < n) :
    (oneEach u v).getD (n + j) false = decide (j = v.val) := by
  unfold oneEach
  have hlen : (List.ofFn (fun x : Fin n => decide (x = u))).length = n := by simp
  rw [getD_append_right_le _ _ (n + j) (by omega)]
  have hsub : n + j - (List.ofFn (fun x : Fin n => decide (x = u))).length = j := by omega
  rw [hsub]
  simp [List.getD_eq_getElem?_getD, hj, Fin.ext_iff]

lemma buildCircuit_mono (n : ℕ) : Monotone2 (buildCircuit n) := by
  intro g hg
  simp only [buildCircuit, List.mem_append] at hg
  rcases hg with (hg | hg) | hg
  · exact orChain_mono _ _ _ _ g hg
  · exact orChain_mono _ _ _ _ g hg
  · simp only [finalGates, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [orG, andG]

lemma buildCircuit_size (n : ℕ) (hn : 3 ≤ n) :
    (buildCircuit n).size ≤ 2 * n + 1 := by
  simp [Circuit.size, buildCircuit, finalGates, orChain_length]
  omega

lemma finalGates_eval (n iY iR b : ℕ) (w : List Bool)
    (hlen : w.length = b) (hn : 3 ≤ n) (hb : 2 * n ≤ b)
    (hiY : iY < b) (hiR : iR < b) :
    (run (finalGates n iY iR b) w).getD (b + 6) false =
      (((w.getD 0 false && (w.getD (n + 1) false || w.getD iY false)) ||
        (w.getD 1 false && (w.getD n false || w.getD iY false))) ||
        (w.getD n false && w.getD iR false)) := by
  set v0 := w.getD (n + 1) false || w.getD iY false
  set v1 := w.getD 0 false && v0
  set v2 := w.getD n false || w.getD iY false
  set v3 := w.getD 1 false && v2
  set v4 := w.getD n false && w.getD iR false
  set v5 := v1 || v3
  set v6 := v5 || v4
  have h0 : step w (orG (n + 1) iY) = w ++ [v0] := step_orG w (n + 1) iY
  have h1 : step (w ++ [v0]) (andG 0 b) = w ++ [v0, v1] := by
    rw [step_andG]
    have ha : (w ++ [v0]).getD 0 false = w.getD 0 false :=
      getD_append_left_lt w [v0] 0 (by omega)
    have hb0 : (w ++ [v0]).getD b false = v0 := by
      rw [← hlen, getD_append_right_le w [v0] w.length (le_refl _)]
      simp
    rw [ha, hb0]
    simp [v1, List.append_assoc]
  have h2 : step (w ++ [v0, v1]) (orG n iY) = w ++ [v0, v1, v2] := by
    rw [step_orG]
    have ha : (w ++ [v0, v1]).getD n false = w.getD n false :=
      getD_append_left_lt w [v0, v1] n (by omega)
    have hb0 : (w ++ [v0, v1]).getD iY false = w.getD iY false :=
      getD_append_left_lt w [v0, v1] iY (by omega)
    rw [ha, hb0]
    simp [v2, List.append_assoc]
  have h3 : step (w ++ [v0, v1, v2]) (andG 1 (b + 2)) = w ++ [v0, v1, v2, v3] := by
    rw [step_andG]
    have ha : (w ++ [v0, v1, v2]).getD 1 false = w.getD 1 false :=
      getD_append_left_lt w [v0, v1, v2] 1 (by omega)
    have hb0 : (w ++ [v0, v1, v2]).getD (b + 2) false = v2 := by
      rw [getD_append_right_le w [v0, v1, v2] (b + 2) (by omega), hlen]
      simp
    rw [ha, hb0]
    simp [v3, List.append_assoc]
  have h4 : step (w ++ [v0, v1, v2, v3]) (andG n iR) = w ++ [v0, v1, v2, v3, v4] := by
    rw [step_andG]
    have ha : (w ++ [v0, v1, v2, v3]).getD n false = w.getD n false :=
      getD_append_left_lt w [v0, v1, v2, v3] n (by omega)
    have hb0 : (w ++ [v0, v1, v2, v3]).getD iR false = w.getD iR false :=
      getD_append_left_lt w [v0, v1, v2, v3] iR (by omega)
    rw [ha, hb0]
    simp [v4, List.append_assoc]
  have h5 : step (w ++ [v0, v1, v2, v3, v4]) (orG (b + 1) (b + 3)) =
      w ++ [v0, v1, v2, v3, v4, v5] := by
    rw [step_orG]
    have ha : (w ++ [v0, v1, v2, v3, v4]).getD (b + 1) false = v1 := by
      rw [getD_append_right_le w [v0, v1, v2, v3, v4] (b + 1) (by omega), hlen]
      simp
    have hb0 : (w ++ [v0, v1, v2, v3, v4]).getD (b + 3) false = v3 := by
      rw [getD_append_right_le w [v0, v1, v2, v3, v4] (b + 3) (by omega), hlen]
      simp
    rw [ha, hb0]
    simp [v5, List.append_assoc]
  have h6 : step (w ++ [v0, v1, v2, v3, v4, v5]) (orG (b + 5) (b + 4)) =
      w ++ [v0, v1, v2, v3, v4, v5, v6] := by
    rw [step_orG]
    have ha : (w ++ [v0, v1, v2, v3, v4, v5]).getD (b + 5) false = v5 := by
      rw [getD_append_right_le w [v0, v1, v2, v3, v4, v5] (b + 5) (by omega), hlen]
      simp
    have hb0 : (w ++ [v0, v1, v2, v3, v4, v5]).getD (b + 4) false = v4 := by
      rw [getD_append_right_le w [v0, v1, v2, v3, v4, v5] (b + 4) (by omega), hlen]
      simp
    rw [ha, hb0]
    simp [v6, List.append_assoc]
  have hrun : run (finalGates n iY iR b) w = w ++ [v0, v1, v2, v3, v4, v5, v6] := by
    simp only [finalGates, run, List.foldl_cons, List.foldl_nil, h0, h1, h2, h3, h4, h5, h6]
  rw [hrun, getD_append_right_le w [v0, v1, v2, v3, v4, v5, v6] (b + 6) (by omega), hlen]
  simp [v6, v5, v4, v3, v2, v1, v0]

lemma buildCircuit_represents (n : ℕ) (hn : 3 ≤ n) :
    Represents
      (fun (u : Fin n) (v : Fin n) =>
        decide ((u.val = 0 ∧ v.val ≠ 0) ∨ (u.val = 1 ∧ v.val ≠ 1) ∨ (2 ≤ u.val ∧ v.val = 0)))
      (buildCircuit n) := by
  intro u v
  set k := n - 3
  set gY := orChain (n + 2) (n + 3) (2 * n) k
  set iY := orChainOut (n + 2) (2 * n) k
  set b1 := 2 * n + k
  set gR := orChain 2 3 b1 k
  set iR := orChainOut 2 b1 k
  set b2 := b1 + k
  set w0 := oneEach u v
  set w1 := run gY w0
  set w2 := run gR w1
  have hw0 : w0.length = 2 * n := oneEach_length u v
  have hw1 : w1.length = b1 := by
    simp [w1, gY, b1, run_length, hw0, orChain_length]
  have hw2 : w2.length = b2 := by
    simp [w2, gR, b2, run_length, hw1, orChain_length]
  have hiY_lt1 : iY < b1 := orChainOut_lt (n + 2) (2 * n) k (by omega)
  have hiY_lt2 : iY < b2 := by omega
  have hiR_lt2 : iR < b2 := orChainOut_lt 2 b1 k (by omega)
  have heval_eq : (buildCircuit n).eval w0 = (run (finalGates n iY iR b2) w2).getD (b2 + 6) false := by
    change (run (gY ++ gR ++ finalGates n iY iR b2) w0).getD (b2 + 6) false = _
    rw [run_append, run_append]
  rw [heval_eq]
  rw [finalGates_eval n iY iR b2 w2 hw2 hn (by omega) hiY_lt2 hiR_lt2]
  have hw2_lt0 : ∀ idx < 2 * n, w2.getD idx false = w0.getD idx false := by
    intro idx hidx
    have h1 : idx < w1.length := by omega
    have h0 : idx < w0.length := by omega
    rw [show w2 = run gR w1 from rfl, run_getD_lt gR w1 idx h1]
    rw [show w1 = run gY w0 from rfl, run_getD_lt gY w0 idx h0]
  have h0_val : w2.getD 0 false = decide (0 = u.val) := by
    rw [hw2_lt0 0 (by omega)]
    exact oneEach_getD_left u v 0 (by omega)
  have h1_val : w2.getD 1 false = decide (1 = u.val) := by
    rw [hw2_lt0 1 (by omega)]
    exact oneEach_getD_left u v 1 (by omega)
  have hn_val : w2.getD n false = decide (0 = v.val) := by
    rw [hw2_lt0 n (by omega)]
    simpa using oneEach_getD_right u v 0 (by omega)
  have hn1_val : w2.getD (n + 1) false = decide (1 = v.val) := by
    rw [hw2_lt0 (n + 1) (by omega)]
    exact oneEach_getD_right u v 1 (by omega)
  have hiY_val : w2.getD iY false = decide (2 ≤ v.val) := by
    rw [show w2 = run gR w1 from rfl, run_getD_lt gR w1 iY (by omega)]
    have hchain := orChain_eval k (n + 2) (n + 3) (2 * n) w0 hw0 (by omega) (by omega)
    rw [show w1 = run gY w0 from rfl, show gY = orChain (n + 2) (n + 3) (2 * n) k from rfl,
      show iY = orChainOut (n + 2) (2 * n) k from rfl, hchain]
    have hiff : (w0.getD (n + 2) false ||
          decide (∃ j : ℕ, j < k ∧ w0.getD (n + 3 + j) false = true)) = true ↔
        decide (2 ≤ v.val) = true := by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      rw [oneEach_getD_right u v 2 (by omega)]
      simp only [decide_eq_true_eq]
      constructor
      · rintro (h2 | ⟨j, hj, hv⟩)
        · omega
        · have hj3 : 3 + j < n := by omega
          have heq : n + 3 + j = n + (3 + j) := by omega
          rw [heq, oneEach_getD_right u v (3 + j) hj3, decide_eq_true_eq] at hv
          omega
      · intro hv2
        by_cases hv : v.val = 2
        · exact Or.inl hv.symm
        · refine Or.inr ⟨v.val - 3, by omega, ?_⟩
          have hj3 : 3 + (v.val - 3) < n := by omega
          have heq : n + 3 + (v.val - 3) = n + (3 + (v.val - 3)) := by omega
          rw [heq, oneEach_getD_right u v (3 + (v.val - 3)) hj3, decide_eq_true_eq]
          omega
    exact bool_eq_of_iff hiff
  have hiR_val : w2.getD iR false = decide (2 ≤ u.val) := by
    have hchain := orChain_eval k 2 3 b1 w1 hw1 (by omega) (by omega)
    rw [show w2 = run gR w1 from rfl, show gR = orChain 2 3 b1 k from rfl,
      show iR = orChainOut 2 b1 k from rfl, hchain]
    have hiff : (w1.getD 2 false ||
          decide (∃ j : ℕ, j < k ∧ w1.getD (3 + j) false = true)) = true ↔
        decide (2 ≤ u.val) = true := by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      rw [show w1 = run gY w0 from rfl, run_getD_lt gY w0 2 (by omega),
        oneEach_getD_left u v 2 (by omega)]
      simp only [decide_eq_true_eq]
      constructor
      · rintro (h2 | ⟨j, hj, hu⟩)
        · omega
        · have hj3 : 3 + j < n := by omega
          rw [run_getD_lt gY w0 (3 + j) (by omega),
            oneEach_getD_left u v (3 + j) hj3, decide_eq_true_eq] at hu
          omega
      · intro hu2
        by_cases hu : u.val = 2
        · exact Or.inl hu.symm
        · refine Or.inr ⟨u.val - 3, by omega, ?_⟩
          have hj3 : 3 + (u.val - 3) < n := by omega
          rw [run_getD_lt gY w0 (3 + (u.val - 3)) (by omega),
            oneEach_getD_left u v (3 + (u.val - 3)) hj3, decide_eq_true_eq]
          omega
    exact bool_eq_of_iff hiff
  rw [h0_val, h1_val, hn_val, hn1_val, hiY_val, hiR_val]
  have hfinal : (((decide (0 = u.val) && (decide (1 = v.val) || decide (2 ≤ v.val))) ||
        (decide (1 = u.val) && (decide (0 = v.val) || decide (2 ≤ v.val)))) ||
        (decide (0 = v.val) && decide (2 ≤ u.val))) = true ↔
      decide ((u.val = 0 ∧ v.val ≠ 0) ∨ (u.val = 1 ∧ v.val ≠ 1) ∨ (2 ≤ u.val ∧ v.val = 0)) = true := by
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    omega
  exact bool_eq_of_iff hfinal

lemma main :
    ∀ n : ℕ, 3 ≤ n →
      RepSizeAtMost
        (fun (u : Fin n) (v : Fin n) =>
          decide ((u.val = 0 ∧ v.val ≠ 0) ∨ (u.val = 1 ∧ v.val ≠ 1) ∨ (2 ≤ u.val ∧ v.val = 0)))
        (2 * n + 1) := by
  intro n hn
  exact ⟨buildCircuit n, buildCircuit_mono n, buildCircuit_size n hn, buildCircuit_represents n hn⟩

end PEqualNP.Outside.L_meta_25234

theorem PEqualNP.Outside.L_meta_25234 : (∀ n : ℕ, 3 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun (u : Fin n) (v : Fin n) => decide ((u.val = 0 ∧ v.val ≠ 0) ∨ (u.val = 1 ∧ v.val ≠ 1) ∨ (2 ≤ u.val ∧ v.val = 0))) (2 * n + 1)) :=
  PEqualNP.Outside.L_meta_25234.main
