import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1311

private theorem andEval (xs : List Bool) : PEqualNP.CircuitLowerBounds.GateOp.and.eval xs = xs.all id := rfl
private theorem orEval (xs : List Bool) : PEqualNP.CircuitLowerBounds.GateOp.or.eval xs = xs.any id := rfl
private theorem notEval_nil : PEqualNP.CircuitLowerBounds.GateOp.not.eval [] = true := rfl
private theorem notEval_cons (a : Bool) (as : List Bool) :
    PEqualNP.CircuitLowerBounds.GateOp.not.eval (a :: as) = !a := rfl

private def run (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private theorem run_snoc (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (g : PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp only [run, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem run_length (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih =>
    rw [run_snoc, List.length_append, List.length_singleton, ih, List.length_append, List.length_singleton]
    omega

private theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (ht : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left ht, ← List.getD_eq_getElem?_getD]

private theorem getD_at (l : List Bool) (b : Bool) :
    (l ++ [b]).getD l.length false = b := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]; simp

private theorem run_prefix (gs hs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool)
    (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_lt _ _ _ (by rw [run_length, List.length_append]; omega), ih]

private theorem run_input (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool)
    (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have h := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using h

private theorem run_gate (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool)
    (j : ℕ) (hj : j < gs.length) :
    (run gs x).getD (x.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i => if i < x.length + j then (run gs x).getD i false else false) := by
  have hsp : gs = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by
    have h1 : gs.take (j + 1) = gs.take j ++ [gs[j]] := List.take_succ_eq_append_getElem hj
    rw [← h1, List.take_append_drop]
  have htl : (gs.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
  have h1 : (run gs x).getD (x.length + j) false = (run (gs.take j ++ [gs[j]]) x).getD (x.length + j) false := by
    conv_lhs => rw [hsp]
    exact run_prefix _ _ _ _ (by rw [List.length_append, htl, List.length_singleton]; omega)
  rw [h1, run_snoc]
  have hlen : (run (gs.take j) x).length = x.length + j := by rw [run_length, htl]
  conv_lhs => rw [← hlen, getD_at]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hilt : i < x.length + j
  · rw [ite_eq_left hilt]
    conv_rhs => rw [hsp, List.append_assoc]
    exact (run_prefix (gs.take j) _ x i (by rw [htl]; exact hilt)).symm
  · rw [ite_eq_right hilt, List.getD_eq_default _ _ (by omega)]

private theorem sum_pow_lt (m : ℕ) (f : Fin m → Bool) :
    (∑ k : Fin m, if f k = true then 2 ^ (m - 1 - k.val) else 0) < 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_succ]
    have hrest : (∑ x : Fin m, if f x.succ = true then 2 ^ (m - 1 - x.val) else 0) < 2 ^ m :=
      ih (fun x => f x.succ)
    have hsub : ∀ x : Fin m, m + 1 - 1 - x.succ.val = m - 1 - x.val := fun x => by
      simp [Fin.val_succ]; omega
    simp only [hsub]
    simp only [Fin.val_zero, Nat.add_sub_cancel, Nat.sub_zero]
    have hp : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [Nat.pow_succ, Nat.mul_two]
    cases hf0 : f 0 <;> simp only [↓reduceIte, Bool.false_eq_true] <;> omega

private theorem binary_eq_of_sum_eq (m : ℕ) (f g : Fin m → Bool)
    (heq : (∑ k : Fin m, if f k = true then 2 ^ (m - 1 - k.val) else 0) =
           (∑ k : Fin m, if g k = true then 2 ^ (m - 1 - k.val) else 0)) :
    ∀ k : Fin m, f k = g k := by
  induction m with
  | zero => intro k; exact Fin.elim0 k
  | succ m ih =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at heq
    have hsub : ∀ x : Fin m, m + 1 - 1 - x.succ.val = m - 1 - x.val := fun x => by
      simp [Fin.val_succ]; omega
    simp only [hsub] at heq
    simp only [Fin.val_zero, Nat.add_sub_cancel, Nat.sub_zero] at heq
    have hf := sum_pow_lt m (fun x => f x.succ)
    have hg := sum_pow_lt m (fun x => g x.succ)
    have h0 : f 0 = g 0 := by
      cases hf0 : f 0 <;> cases hg0 : g 0 <;>
        simp only [hf0, hg0, ↓reduceIte, Bool.false_eq_true, Nat.zero_add] at heq ⊢ <;> omega
    have htail : (∑ x : Fin m, if f x.succ = true then 2 ^ (m - 1 - x.val) else 0) =
                 (∑ x : Fin m, if g x.succ = true then 2 ^ (m - 1 - x.val) else 0) := by
      rw [h0] at heq
      cases hg0 : g 0 <;> simp only [hg0, ↓reduceIte, Bool.false_eq_true, Nat.zero_add] at heq <;> omega
    intro k
    refine Fin.cases h0 (fun x => ih (fun y => f y.succ) (fun y => g y.succ) htail x) k

private theorem binary_lt_first_diff (m : ℕ) (f g : Fin m → Bool)
    (hlt : (∑ k : Fin m, if f k = true then 2 ^ (m - 1 - k.val) else 0) <
           (∑ k : Fin m, if g k = true then 2 ^ (m - 1 - k.val) else 0)) :
    ∃ r : Fin m, (∀ k : Fin m, k.val < r.val → f k = g k) ∧ f r = false ∧ g r = true := by
  induction m with
  | zero => simp at hlt
  | succ m ih =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at hlt
    have hsub : ∀ x : Fin m, m + 1 - 1 - x.succ.val = m - 1 - x.val := fun x => by
      simp [Fin.val_succ]; omega
    simp only [hsub] at hlt
    simp only [Fin.val_zero, Nat.add_sub_cancel, Nat.sub_zero] at hlt
    have hf := sum_pow_lt m (fun x => f x.succ)
    have hg := sum_pow_lt m (fun x => g x.succ)
    cases hf0 : f 0 <;> cases hg0 : g 0 <;>
      simp only [hf0, hg0, ↓reduceIte, Bool.false_eq_true, Nat.zero_add] at hlt
    · obtain ⟨r, hpre, hfr, hgr⟩ := ih (fun y => f y.succ) (fun y => g y.succ) hlt
      refine ⟨r.succ, ?_, hfr, hgr⟩
      intro k
      refine Fin.cases ?_ ?_ k
      · intro _; rw [hf0, hg0]
      · intro y hy; exact hpre y (by simpa [Fin.val_succ] using hy)
    · exact ⟨0, fun k hk => by simp at hk, hf0, hg0⟩
    · omega
    · obtain ⟨r, hpre, hfr, hgr⟩ := ih (fun y => f y.succ) (fun y => g y.succ) (by omega)
      refine ⟨r.succ, ?_, hfr, hgr⟩
      intro k
      refine Fin.cases ?_ ?_ k
      · intro _; rw [hf0, hg0]
      · intro y hy; exact hpre y (by simpa [Fin.val_succ] using hy)

private theorem filter_range_length_eq {α : Type*} (l : List α) (d : α) (p : α → Bool) :
    ((List.range l.length).filter (fun i => p (l.getD i d))).length = (l.filter p).length := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton xs x ih =>
    rw [List.length_append, List.length_singleton, List.range_succ, List.filter_append,
        List.filter_append, List.length_append, List.length_append]
    have h1 : (List.range xs.length).filter (fun i => p ((xs ++ [x]).getD i d)) =
              (List.range xs.length).filter (fun i => p (xs.getD i d)) := by
      refine List.filter_congr fun i hi => ?_
      rw [List.mem_range] at hi
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hi, ← List.getD_eq_getElem?_getD]
    have h2 : ([xs.length].filter (fun i => p ((xs ++ [x]).getD i d))).length = ([x].filter p).length := by
      have hget : (xs ++ [x]).getD xs.length d = x := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]; simp
      simp only [List.filter_cons, List.filter_nil, hget]
      cases p x <;> rfl
    rw [h1, ih, h2]

private theorem pairwise_filter_range (m : ℕ) (p : ℕ → Bool) :
    ((List.range m).filter p).Pairwise (· < ·) :=
  List.Pairwise.filter p List.pairwise_lt_range

private theorem filter_range_no_between (m : ℕ) (p : ℕ → Bool) (j u v : ℕ)
    (hu : ((List.range m).filter p)[j]? = some u)
    (hv : ((List.range m).filter p)[j + 1]? = some v) :
    u < v ∧ ∀ k, u < k → k < v → p k = false := by
  let L := (List.range m).filter p
  have huL : L[j]? = some u := hu
  have hvL : L[j + 1]? = some v := hv
  have hpw : L.Pairwise (· < ·) := pairwise_filter_range m p
  have hj1 : j + 1 < L.length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hvL; cases hvL
  have hj : j < L.length := by omega
  have hu' : L[j] = u := Option.some.inj ((List.getElem?_eq_getElem hj).symm.trans huL)
  have hv' : L[j + 1] = v := Option.some.inj ((List.getElem?_eq_getElem hj1).symm.trans hvL)
  have huv : u < v := by rw [← hu', ← hv']; exact List.pairwise_iff_getElem.mp hpw j (j + 1) hj hj1 (by omega)
  refine ⟨huv, ?_⟩
  intro k huk hkv
  by_contra hpk
  have hpk_true : p k = true := by cases hp : p k <;> simp_all
  have hv_lt : v < m := by
    have hvmem : v ∈ L := hv' ▸ List.getElem_mem hj1
    exact List.mem_range.mp (List.mem_filter.mp hvmem).1
  have hk_mem : k ∈ L := List.mem_filter.mpr ⟨List.mem_range.mpr (by omega), hpk_true⟩
  obtain ⟨r, hr, hkr⟩ := List.mem_iff_getElem.mp hk_mem
  have hlt_ord : ∀ a b (ha : a < L.length) (hb : b < L.length), a < b → L[a] < L[b] :=
    fun a b ha hb hab => List.pairwise_iff_getElem.mp hpw a b ha hb hab
  rcases Nat.lt_trichotomy r j with h1 | rfl | h2
  · have := hlt_ord r j hr hj h1; omega
  · omega
  · rcases Nat.lt_trichotomy r (j + 1) with h3 | rfl | h4
    · omega
    · omega
    · have := hlt_ord (j + 1) r hj1 hr h4; omega

private theorem binary_bit_of_mul_pow (b j : ℕ) (hjb : j + 2 ≤ b) (q : ℕ) (hq : q < 4)
    (f : Fin b → Bool)
    (hsum : (∑ k : Fin b, if f k = true then 2 ^ (b - 1 - k.val) else 0) = q * 2 ^ (b - 2 - j)) :
    (∀ k : Fin b, k.val < j → f k = false) ∧
    f ⟨j, by omega⟩ = decide (2 ≤ q) ∧
    f ⟨j + 1, by omega⟩ = decide (q % 2 = 1) := by
  let g : Fin b → Bool := fun k =>
    if k.val = j then decide (2 ≤ q)
    else if k.val = j + 1 then decide (q % 2 = 1)
    else false
  have hgsum : (∑ k : Fin b, if g k = true then 2 ^ (b - 1 - k.val) else 0) = q * 2 ^ (b - 2 - j) := by
    let kj : Fin b := ⟨j, by omega⟩
    let kj1 : Fin b := ⟨j + 1, by omega⟩
    have hne : kj ≠ kj1 := by intro h; have := congrArg Fin.val h; dsimp [kj, kj1] at this; omega
    have hzero : ∀ k : Fin b, k ≠ kj → k ≠ kj1 → (if g k = true then 2 ^ (b - 1 - k.val) else 0) = 0 := by
      intro k hk1 hk2
      have h1 : k.val ≠ j := fun h => hk1 (Fin.ext h)
      have h2 : k.val ≠ j + 1 := fun h => hk2 (Fin.ext h)
      simp [g, h1, h2]
    have hsplit : (∑ k : Fin b, if g k = true then 2 ^ (b - 1 - k.val) else 0) =
        (if g kj = true then 2 ^ (b - 1 - j) else 0) +
        (if g kj1 = true then 2 ^ (b - 1 - (j + 1)) else 0) := by
      have hsub : ({kj, kj1} : Finset (Fin b)) ⊆ Finset.univ := Finset.subset_univ _
      rw [← Finset.sum_subset hsub (fun k _ hk => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
        exact hzero k hk.1 hk.2)]
      rw [Finset.sum_pair hne]
    rw [hsplit]
    have hgj : g kj = decide (2 ≤ q) := by simp [g, kj]
    have hgj1 : g kj1 = decide (q % 2 = 1) := by
      have h1 : j + 1 ≠ j := by omega
      simp [g, kj1, h1]
    rw [hgj, hgj1]
    have hp1 : b - 1 - (j + 1) = b - 2 - j := by omega
    have hp0 : 2 ^ (b - 1 - j) = 2 * 2 ^ (b - 2 - j) := by
      have he : b - 1 - j = (b - 2 - j) + 1 := by omega
      rw [he, Nat.pow_succ, Nat.mul_comm]
    rw [hp1, hp0]
    have : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> simp <;> omega
  have hfeq : ∀ k : Fin b, f k = g k := binary_eq_of_sum_eq b f g (hsum.trans hgsum.symm)
  refine ⟨fun k hk => ?_, ?_, ?_⟩
  · rw [hfeq k]; simp [g, show k.val ≠ j by omega, show k.val ≠ j + 1 by omega]
  · rw [hfeq ⟨j, by omega⟩]; simp [g]
  · rw [hfeq ⟨j + 1, by omega⟩]; simp [g, show j + 1 ≠ j by omega]

set_option maxHeartbeats 1200000 in
private theorem main_clean
    (n l : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C)
    (x : Nat → Finset (Fin n)) (hx : ∀ t < l, x t ⊆ x (t + 1))
    (obs : List (Fin (n + 2 + C.size))) :
    letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq
    let wire := fun t i => (C.wires (List.ofFn (fun j : Fin n => decide (j ∈ x t)) ++ [false, true])).getD i false
    let fall := fun t => obs.any (fun w => wire t w.val && !(wire (t + 1) w.val))
    let op := fun i => (C.gates.getD i ⟨.or, []⟩).op
    let gates := (List.range C.size).filter (fun i => decide (op i = .not))
    let b := PEqualNP.NotBracket.notCount C
    ((Finset.range l).filter (fun t => fall t = true)).card + 1 = 2 ^ b →
      (∀ j u v, gates[j]? = some u → gates[j + 1]? = some v →
        (∃ a, u < a ∧ a < v ∧ op a = .and) ∧ (∃ o, u < o ∧ o < v ∧ op o = .or)) ∧
      b - 1 ≤ (C.gates.filter (fun g => decide (g.op = .and))).length ∧
      b - 1 ≤ (C.gates.filter (fun g => decide (g.op = .or))).length ∧
      b + 2 * (b - 1) ≤ C.size := by
  dsimp only
  intro hsat
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq
  let inp : ℕ → List Bool := fun t => List.ofFn (fun j : Fin n => decide (j ∈ x t)) ++ [false, true]
  let wire : ℕ → ℕ → Bool := fun t i => (C.wires (inp t)).getD i false
  let fall : ℕ → Bool := fun t => obs.any (fun w => wire t w.val && !(wire (t + 1) w.val))
  let op : ℕ → PEqualNP.CircuitLowerBounds.GateOp := fun i => (C.gates.getD i ⟨.or, []⟩).op
  let gates : List ℕ := (List.range C.size).filter (fun i => decide (op i = .not))
  let b : ℕ := PEqualNP.NotBracket.notCount C
  have hsat_eq : ((Finset.range l).filter (fun t => fall t = true)).card + 1 = 2 ^ b := hsat
  have hinp_len : ∀ t, (inp t).length = n + 2 := fun t => by simp [inp]
  have hx_mono : ∀ t1 t2, t1 ≤ t2 → t2 ≤ l → x t1 ⊆ x t2 := by
    intro t1 t2 hle h2l
    induction hle with
    | refl => exact Finset.Subset.refl _
    | @step m h1m ih => exact Finset.Subset.trans (ih (by omega)) (hx m (by omega))
  have hgates_len : gates.length = b := by
    dsimp only [gates, b, PEqualNP.NotBracket.notCount]
    exact filter_range_length_eq C.gates ⟨.or, []⟩ (fun g => decide (g.op = .not))
  have hgates_lt : ∀ k : Fin gates.length, gates[k] < C.gates.length := fun k =>
    List.mem_range.mp (List.mem_filter.mp (List.getElem_mem k.isLt)).1
  have hgates_not : ∀ k : Fin gates.length, op gates[k] = .not := fun k =>
    of_decide_eq_true (List.mem_filter.mp (List.getElem_mem k.isLt)).2
  have hgates_mem : ∀ u < C.gates.length, op u = .not → ∃ k : Fin gates.length, gates[k] = u := by
    intro u hu hop
    have hm : u ∈ gates := List.mem_filter.mpr ⟨List.mem_range.mpr hu, decide_eq_true hop⟩
    obtain ⟨k, hk, heq⟩ := List.mem_iff_getElem.mp hm
    exact ⟨⟨k, hk⟩, heq⟩
  have hpref_mono : ∀ (t1 t2 : ℕ), t1 ≤ t2 → t2 ≤ l → ∀ (k : ℕ), k ≤ C.gates.length →
      (∀ u < k, op u = .not → wire t1 (n + 2 + u) = true → wire t2 (n + 2 + u) = true) →
      ∀ w < n + 2 + k, wire t1 w = true → wire t2 w = true := by
    intro t1 t2 h12 h2l k hk hnot w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw hwt1
      by_cases hw_in : w < n + 2
      · have h1 : wire t1 w = (inp t1).getD w false := run_input C.gates (inp t1) w (by rw [hinp_len]; exact hw_in)
        have h2 : wire t2 w = (inp t2).getD w false := run_input C.gates (inp t2) w (by rw [hinp_len]; exact hw_in)
        rw [h1] at hwt1; rw [h2]
        by_cases hwn : w < n
        · have hv1 : (inp t1).getD w false = decide (⟨w, hwn⟩ ∈ x t1) := by
            dsimp only [inp]; rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hwn]), List.getElem?_ofFn]; simp [hwn]
          have hv2 : (inp t2).getD w false = decide (⟨w, hwn⟩ ∈ x t2) := by
            dsimp only [inp]; rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hwn]), List.getElem?_ofFn]; simp [hwn]
          rw [hv1] at hwt1; rw [hv2]
          exact decide_eq_true (hx_mono t1 t2 h12 h2l (of_decide_eq_true hwt1))
        · have hcase : w = n ∨ w = n + 1 := by omega
          rcases hcase with hw_n | hw_n1
          · rw [hw_n] at hwt1
            have : (inp t1).getD n false = false := by
              dsimp only [inp]; rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]; simp
            rw [this] at hwt1; cases hwt1
          · rw [hw_n1]
            dsimp only [inp]; rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]; simp
      · let m : ℕ := w - (n + 2)
        have hwm : w = n + 2 + m := by omega
        have hmC : m < C.gates.length := by omega
        have hmk : m < k := by omega
        rw [hwm] at hwt1 ⊢
        have hg_eq : C.gates[m] = C.gates.getD m ⟨.or, []⟩ := (List.getD_eq_getElem C.gates _ hmC).symm
        have hgm_mem : C.gates[m] ∈ C.gates := List.getElem_mem hmC
        have hgm_op : (C.gates[m]).op = op m := congrArg PEqualNP.CircuitLowerBounds.Gate.op hg_eq
        rcases (hfan _ hgm_mem).1 with h1 | h1
        · have hand : (C.gates[m]).op = .and := h1
          have rg1 := run_gate C.gates (inp t1) m hmC
          have rg2 := run_gate C.gates (inp t2) m hmC
          rw [hinp_len] at rg1 rg2
          change (run C.gates (inp t1)).getD (n + 2 + m) false = true at hwt1
          change (run C.gates (inp t2)).getD (n + 2 + m) false = true
          rw [rg1, hand, andEval] at hwt1
          rw [rg2, hand, andEval]
          rw [List.all_eq_true] at hwt1 ⊢
          intro b' hb'
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb'
          have hilt : i < n + 2 + m := hrb m hmC i (by change i ∈ (C.gates.getD m ⟨.or, []⟩).inputs; rw [← hg_eq]; exact hi)
          have hprev := hwt1 _ (List.mem_map.mpr ⟨i, hi, rfl⟩)
          simp only [id_eq, ite_eq_left hilt] at hprev ⊢
          exact ih i (by omega) (by omega) hprev
        · rcases h1 with hor | hnot'
          · have rg1 := run_gate C.gates (inp t1) m hmC
            have rg2 := run_gate C.gates (inp t2) m hmC
            rw [hinp_len] at rg1 rg2
            change (run C.gates (inp t1)).getD (n + 2 + m) false = true at hwt1
            change (run C.gates (inp t2)).getD (n + 2 + m) false = true
            rw [rg1, hor, orEval] at hwt1
            rw [rg2, hor, orEval]
            rw [List.any_eq_true] at hwt1 ⊢
            obtain ⟨b', hb', hbt⟩ := hwt1
            obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb'
            have hilt : i < n + 2 + m := hrb m hmC i (by change i ∈ (C.gates.getD m ⟨.or, []⟩).inputs; rw [← hg_eq]; exact hi)
            simp only [id_eq, ite_eq_left hilt] at hbt
            refine ⟨if i < n + 2 + m then (run C.gates (inp t2)).getD i false else false, List.mem_map.mpr ⟨i, hi, rfl⟩, ?_⟩
            simp only [id_eq, ite_eq_left hilt]
            exact ih i (by omega) (by omega) hbt
          · have hnot_op : op m = .not := hgm_op.symm.trans hnot'
            exact hnot m hmk hnot_op hwt1
  let bits : ℕ → Fin gates.length → Bool := fun t k => wire t (n + 2 + gates[k])
  let inv : ℕ → ℕ := fun t => ∑ k : Fin gates.length, if bits t k = true then 2 ^ (gates.length - 1 - k.val) else 0
  have hinv_lt : ∀ t, inv t < 2 ^ gates.length := fun t => sum_pow_lt gates.length (bits t)
  have hinv_dec : ∀ t < l, inv (t + 1) ≤ inv t := by
    intro t ht
    by_contra hgt
    have hlt : inv t < inv (t + 1) := by omega
    obtain ⟨r, hpre, hfr, hgr⟩ := binary_lt_first_diff gates.length (bits t) (bits (t + 1)) hlt
    let u : ℕ := gates[r]
    have huC : u < C.gates.length := hgates_lt r
    have hu_not : (C.gates[u]).op = .not := by
      have hg_eq : C.gates[u] = C.gates.getD u ⟨.or, []⟩ := (List.getD_eq_getElem C.gates _ huC).symm
      rw [hg_eq]; exact hgates_not r
    have hprev_eq : ∀ m < u, op m = .not → wire t (n + 2 + m) = true → wire (t + 1) (n + 2 + m) = true := by
      intro m hmu hmnot hwm
      obtain ⟨k, hkm⟩ := hgates_mem m (by omega) hmnot
      have hkr : k.val < r.val := by
        have hpw := List.pairwise_iff_getElem.mp (pairwise_filter_range C.size (fun i => decide (op i = .not)))
        by_contra hge
        rcases Nat.eq_or_lt_of_le (Nat.le_of_not_lt hge) with heq | hlt'
        · have h1 : k = r := Fin.ext heq.symm; rw [h1] at hkm; dsimp only [u] at hmu; omega
        · have hlt_u : gates[r.val] < gates[k.val] := hpw r.val k.val r.isLt k.isLt hlt'
          have hkm' : gates[k.val] = m := hkm
          have hu_eq : gates[r.val] = u := rfl
          omega
      have heq := hpre k hkr
      dsimp only [bits] at heq
      rw [hkm] at heq; rw [← heq]; exact hwm
    have hmono_u : ∀ w < n + 2 + u, wire t w = true → wire (t + 1) w = true :=
      hpref_mono t (t + 1) (Nat.le_succ t) (by omega) u (Nat.le_of_lt huC) hprev_eq
    have rg1 := run_gate C.gates (inp t) u huC
    have rg2 := run_gate C.gates (inp (t + 1)) u huC
    rw [hinp_len] at rg1 rg2
    dsimp only [bits] at hfr hgr
    change (run C.gates (inp t)).getD (n + 2 + u) false = false at hfr
    change (run C.gates (inp (t + 1))).getD (n + 2 + u) false = true at hgr
    rw [rg1, hu_not] at hfr
    rw [rg2, hu_not] at hgr
    rcases hinps : (C.gates[u]).inputs with _ | ⟨w_in, rest⟩
    · rw [hinps, List.map_nil, notEval_nil] at hfr; cases hfr
    · rw [hinps, List.map_cons, notEval_cons] at hfr hgr
      have hwlt : w_in < n + 2 + u := hrb u huC w_in (by
        change w_in ∈ (C.gates.getD u ⟨.or, []⟩).inputs
        rw [List.getD_eq_getElem C.gates _ huC, hinps]; exact List.mem_cons_self)
      simp only [ite_eq_left hwlt] at hfr hgr
      change (!wire t w_in) = false at hfr
      change (!wire (t + 1) w_in) = true at hgr
      have h1 : wire t w_in = true := by cases h : wire t w_in <;> simp_all
      have h2 : wire (t + 1) w_in = false := by cases h : wire (t + 1) w_in <;> simp_all
      have h3 := hmono_u w_in hwlt h1
      rw [h2] at h3; cases h3
  have hinv_strict : ∀ t < l, fall t = true → inv (t + 1) < inv t := by
    intro t ht hfall
    have hle := hinv_dec t ht
    by_contra hnotlt
    have heq : inv t = inv (t + 1) := by omega
    have hbits := binary_eq_of_sum_eq gates.length (bits t) (bits (t + 1)) heq
    have hall : ∀ w < n + 2 + C.gates.length, wire t w = true → wire (t + 1) w = true := by
      refine hpref_mono t (t + 1) (Nat.le_succ t) (by omega) C.gates.length le_rfl ?_
      intro u huC hunot hwt
      obtain ⟨k, hku⟩ := hgates_mem u huC hunot
      have hk := hbits k; dsimp only [bits] at hk; rw [hku] at hk; rw [← hk]; exact hwt
    dsimp only [fall] at hfall
    obtain ⟨w, _, hw⟩ := List.any_eq_true.mp hfall
    have h1 : wire t w.val = true := by cases h : wire t w.val <;> simp_all
    have h2 : wire (t + 1) w.val = false := by cases h : wire (t + 1) w.val <;> simp_all
    have h3 := hall w.val w.isLt h1
    rw [h2] at h3; cases h3
  have hcount : ∀ m ≤ l, inv m + ((Finset.range m).filter (fun t => fall t = true)).card ≤ inv 0 := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have hprev := ih (by omega)
      rw [Finset.range_add_one, Finset.filter_insert]
      by_cases hf : fall m = true
      · rw [ite_eq_left hf, Finset.card_insert_of_notMem (by simp)]
        have hst := hinv_strict m (by omega) hf
        omega
      · rw [ite_eq_right hf]
        have hle := hinv_dec m (by omega)
        omega
  have hinv_l_le := hcount l le_rfl
  have hinv0_lt : inv 0 < 2 ^ b := hgates_len ▸ hinv_lt 0
  have hinv0_eq : inv 0 = 2 ^ b - 1 := by omega
  have hinvl_eq : inv l = 0 := by omega
  have hstep_drop : ∀ t < l, inv t ≤ inv (t + 1) + 1 := by
    intro t ht
    by_contra hgt
    have hdrop2 : inv (t + 1) + 2 ≤ inv t := by omega
    have htail : ∀ k, t + 1 + k ≤ l →
        inv (t + 1 + k) + (((Finset.range (t + 1 + k)).filter (fun s => fall s = true)).card -
                           ((Finset.range (t + 1)).filter (fun s => fall s = true)).card) ≤ inv (t + 1) := by
      intro k
      induction k with
      | zero => intro _; simp
      | succ k ih =>
        intro hk
        have h1 := ih (by omega)
        have heq1 : t + 1 + (k + 1) = (t + 1 + k) + 1 := by omega
        rw [heq1, Finset.range_add_one, Finset.filter_insert]
        have hsub_le : ((Finset.range (t + 1)).filter (fun s => fall s = true)).card ≤
            ((Finset.range (t + 1 + k)).filter (fun s => fall s = true)).card :=
          Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono (by omega)))
        by_cases hf : fall (t + 1 + k) = true
        · rw [ite_eq_left hf, Finset.card_insert_of_notMem (by simp)]
          have hst := hinv_strict (t + 1 + k) (by omega) hf
          omega
        · rw [ite_eq_right hf]
          have hle := hinv_dec (t + 1 + k) (by omega)
          omega
    have htail_l := htail (l - (t + 1)) (by omega)
    have hadd : t + 1 + (l - (t + 1)) = l := by omega
    rw [hadd] at htail_l
    have hpre_t := hcount t (by omega)
    have hsub1 : ((Finset.range (t + 1)).filter (fun s => fall s = true)).card ≤
        ((Finset.range t).filter (fun s => fall s = true)).card + 1 := by
      rw [Finset.range_add_one, Finset.filter_insert]
      by_cases hf : fall t = true
      · rw [ite_eq_left hf, Finset.card_insert_of_notMem (by simp)]
      · rw [ite_eq_right hf]; omega
    have hsub2 : ((Finset.range (t + 1)).filter (fun s => fall s = true)).card ≤
        ((Finset.range l).filter (fun s => fall s = true)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono (by omega)))
    omega
  have hsurj : ∀ val < 2 ^ b, ∃ t ≤ l, inv t = val := by
    intro val hval
    have hreach : ∀ m ≤ l, inv m ≤ val → ∃ t ≤ m, inv t = val := by
      intro m
      induction m with
      | zero => intro _ h0; exact ⟨0, le_rfl, by omega⟩
      | succ m ih =>
        intro hm hle
        by_cases hprev : inv m ≤ val
        · obtain ⟨t, htm, ht⟩ := ih (by omega) hprev
          exact ⟨t, by omega, ht⟩
        · have hstep := hstep_drop m (by omega)
          exact ⟨m + 1, le_rfl, by omega⟩
    exact hreach l le_rfl (by omega)
  have hinv_antitone : ∀ t1 t2, t1 ≤ t2 → t2 ≤ l → inv t2 ≤ inv t1 := by
    intro t1 t2 h12 h2l
    induction h12 with
    | refl => exact le_rfl
    | @step m h1m ih => exact le_trans (hinv_dec m (by omega)) (ih (by omega))
  have hBetween : ∀ j u v, gates[j]? = some u → gates[j + 1]? = some v →
      (∃ a, u < a ∧ a < v ∧ op a = .and) ∧ (∃ o, u < o ∧ o < v ∧ op o = .or) := by
    intro j u v hu hv
    have hj1 : j + 1 < gates.length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at hv; cases hv
    have hj : j < gates.length := by omega
    have hu' : gates[j] = u := Option.some.inj ((List.getElem?_eq_getElem hj).symm.trans hu)
    have hv' : gates[j + 1] = v := Option.some.inj ((List.getElem?_eq_getElem hj1).symm.trans hv)
    obtain ⟨huv, hnoNot⟩ := filter_range_no_between C.size (fun i => decide (op i = .not)) j u v hu hv
    have hjb : j + 2 ≤ b := by omega
    let d : ℕ := 2 ^ (b - 2 - j)
    have hd_pos : 0 < d := Nat.pow_pos (by omega)
    have h3d_lt : 3 * d < 2 ^ b := by
      have hpow : 4 * d ≤ 2 ^ b := by
        have h1 : 2 ^ (b - 2 - j + 2) ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) (by omega)
        have h2 : 2 ^ (b - 2 - j + 2) = 4 * d := by rw [Nat.pow_add]; dsimp [d]; omega
        omega
      omega
    obtain ⟨t0, ht0l, ht0⟩ := hsurj (3 * d) h3d_lt
    obtain ⟨t1, ht1l, ht1⟩ := hsurj (2 * d) (by omega)
    obtain ⟨t2, ht2l, ht2⟩ := hsurj (1 * d) (by omega)
    obtain ⟨t3, ht3l, ht3⟩ := hsurj 0 (by omega)
    have h01 : t0 ≤ t1 := by
      by_contra h; have := hinv_antitone t1 t0 (by omega) ht0l; omega
    have h12 : t1 ≤ t2 := by
      by_contra h; have := hinv_antitone t2 t1 (by omega) ht1l; omega
    have h23 : t2 ≤ t3 := by
      by_contra h; have := hinv_antitone t3 t2 (by omega) ht2l; omega
    let bitsB : ℕ → Fin b → Bool := fun t k => bits t ⟨k.val, by omega⟩
    have hsum_eq : ∀ t, (∑ k : Fin b, if bitsB t k = true then 2 ^ (b - 1 - k.val) else 0) = inv t := by
      intro t
      dsimp only [inv, bitsB]
      refine Finset.sum_bij (fun k _ => ⟨k.val, by omega⟩) (fun _ _ => Finset.mem_univ _)
        (fun a _ b' _ h => Fin.ext (by simpa using congrArg Fin.val h))
        (fun k _ => ⟨⟨k.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩) (fun k _ => by simp [hgates_len])
    have hb0 := binary_bit_of_mul_pow b j hjb 3 (by omega) (bitsB t0) ((hsum_eq t0).trans ht0)
    have hb1 := binary_bit_of_mul_pow b j hjb 2 (by omega) (bitsB t1) ((hsum_eq t1).trans ht1)
    have hb2 := binary_bit_of_mul_pow b j hjb 1 (by omega) (bitsB t2) ((hsum_eq t2).trans ht2)
    have hb3 := binary_bit_of_mul_pow b j hjb 0 (by omega) (bitsB t3) ((hsum_eq t3).trans (by simpa using ht3))
    have hu_t0 : wire t0 (n + 2 + u) = true := by
      have h := hb0.2.1; dsimp only [bitsB, bits] at h; change wire t0 (n + 2 + gates[j]) = _ at h; rw [hu'] at h; simpa using h
    have hu_t3 : wire t3 (n + 2 + u) = false := by
      have h := hb3.2.1; dsimp only [bitsB, bits] at h; change wire t3 (n + 2 + gates[j]) = _ at h; rw [hu'] at h; simpa using h
    have hv_t0 : wire t0 (n + 2 + v) = true := by
      have h := hb0.2.2; dsimp only [bitsB, bits] at h; change wire t0 (n + 2 + gates[j + 1]) = _ at h; rw [hv'] at h; simpa using h
    have hv_t1 : wire t1 (n + 2 + v) = false := by
      have h := hb1.2.2; dsimp only [bitsB, bits] at h; change wire t1 (n + 2 + gates[j + 1]) = _ at h; rw [hv'] at h; simpa using h
    have hv_t2 : wire t2 (n + 2 + v) = true := by
      have h := hb2.2.2; dsimp only [bitsB, bits] at h; change wire t2 (n + 2 + gates[j + 1]) = _ at h; rw [hv'] at h; simpa using h
    have hv_t3 : wire t3 (n + 2 + v) = false := by
      have h := hb3.2.2; dsimp only [bitsB, bits] at h; change wire t3 (n + 2 + gates[j + 1]) = _ at h; rw [hv'] at h; simpa using h
    have hvC : v < C.gates.length := hv' ▸ hgates_lt ⟨j + 1, hj1⟩
    have huC : u < C.gates.length := hu' ▸ hgates_lt ⟨j, hj⟩
    have hmono12 : ∀ w < n + 2 + u, wire t1 w = true → wire t2 w = true := by
      refine hpref_mono t1 t2 h12 ht2l u (Nat.le_of_lt huC) ?_
      intro m hmu hmnot hwm
      obtain ⟨k, hkm⟩ := hgates_mem m (by omega) hmnot
      have hkj : k.val < j := by
        have hpw := List.pairwise_iff_getElem.mp (pairwise_filter_range C.size (fun i => decide (op i = .not)))
        by_contra hge
        rcases Nat.eq_or_lt_of_le (Nat.le_of_not_lt hge) with heq | hlt'
        · have h1 : k = ⟨j, hj⟩ := Fin.ext heq.symm; rw [h1] at hkm; change gates[j] = m at hkm; rw [hu'] at hkm; omega
        · have hlt_u : gates[j] < gates[k.val] := hpw j k.val hj k.isLt hlt'
          have hkm' : gates[k.val] = m := hkm
          rw [hu', hkm'] at hlt_u; omega
      have h1 := hb1.1 ⟨k.val, by omega⟩ hkj
      dsimp only [bitsB, bits] at h1; rw [hkm] at h1; rw [h1] at hwm; cases hwm
    have hv_op : (C.gates[v]).op = .not := by
      have hg_eq : C.gates[v] = C.gates.getD v ⟨.or, []⟩ := (List.getD_eq_getElem C.gates _ hvC).symm
      rw [hg_eq]; exact hv' ▸ hgates_not ⟨j + 1, hj1⟩
    have hv_nonnil : (C.gates[v]).inputs ≠ [] := by
      intro hnil
      have rg1 := run_gate C.gates (inp t1) v hvC
      rw [hinp_len, hv_op, hnil, List.map_nil, notEval_nil] at rg1
      change (run C.gates (inp t1)).getD (n + 2 + v) false = false at hv_t1
      rw [rg1] at hv_t1; cases hv_t1
    rcases hvinp : (C.gates[v]).inputs with _ | ⟨w_in, w_rest⟩
    · exact absurd hvinp hv_nonnil
    have hw_in_lt : w_in < n + 2 + v := hrb v hvC w_in (by
      change w_in ∈ (C.gates.getD v ⟨.or, []⟩).inputs
      rw [List.getD_eq_getElem C.gates _ hvC, hvinp]; exact List.mem_cons_self)
    have hwin_eval : ∀ t, wire t (n + 2 + v) = !(wire t w_in) := by
      intro t
      have rg := run_gate C.gates (inp t) v hvC
      rw [hinp_len, hv_op, hvinp, List.map_cons, notEval_cons, ite_eq_left hw_in_lt] at rg
      exact rg
    have hwin_t0 : wire t0 w_in = false := by
      have h := hwin_eval t0; rw [hv_t0] at h; cases h1 : wire t0 w_in <;> rw [h1] at h <;> first | rfl | cases h
    have hwin_t1 : wire t1 w_in = true := by
      have h := hwin_eval t1; rw [hv_t1] at h; cases h1 : wire t1 w_in <;> rw [h1] at h <;> first | rfl | cases h
    have hwin_t2 : wire t2 w_in = false := by
      have h := hwin_eval t2; rw [hv_t2] at h; cases h1 : wire t2 w_in <;> rw [h1] at h <;> first | rfl | cases h
    have hwin_t3 : wire t3 w_in = true := by
      have h := hwin_eval t3; rw [hv_t3] at h; cases h1 : wire t3 w_in <;> rw [h1] at h <;> first | rfl | cases h
    constructor
    · by_contra hnoAnd
      have hall_or : ∀ m (hum : u < m) (hmv : m < v), (C.gates[m]'(by omega)).op = .or := by
        intro m hum hmv
        have hmC : m < C.gates.length := by omega
        have hg_eq : C.gates[m] = C.gates.getD m ⟨.or, []⟩ := (List.getD_eq_getElem C.gates _ hmC).symm
        have hop_eq : (C.gates[m]).op = op m := congrArg PEqualNP.CircuitLowerBounds.Gate.op hg_eq
        rcases (hfan _ (List.getElem_mem hmC)).1 with hand | hor | hnot'
        · exact absurd ⟨m, hum, hmv, hop_eq.symm.trans hand⟩ hnoAnd
        · exact hor
        · have hnf := hnoNot m hum hmv
          have : op m = .not := hop_eq.symm.trans hnot'
          rw [this] at hnf; simp at hnf
      have hinv_or : ∀ w < n + 2 + v, (wire t1 w = true → wire t2 w = true) ∨ wire t0 w = true := by
        intro w
        induction w using Nat.strong_induction_on with
        | ind w ih =>
          intro hwv
          by_cases hwu : w < n + 2 + u
          · exact Or.inl (hmono12 w hwu)
          · by_cases hweq : w = n + 2 + u
            · subst hweq; exact Or.inr hu_t0
            · let m : ℕ := w - (n + 2)
              have hwm : w = n + 2 + m := by omega
              have hum : u < m := by omega
              have hmv : m < v := by omega
              have hmC : m < C.gates.length := by omega
              have hor_m : (C.gates[m]).op = .or := hall_or m hum hmv
              rw [hwm]
              by_cases hex0 : ∃ i ∈ (C.gates[m]).inputs, wire t0 i = true
              · right
                obtain ⟨i, hi, hit0⟩ := hex0
                have hilt : i < n + 2 + m := hrb m hmC i (by
                  change i ∈ (C.gates.getD m ⟨.or, []⟩).inputs
                  rw [List.getD_eq_getElem C.gates _ hmC]; exact hi)
                have rg := run_gate C.gates (inp t0) m hmC
                rw [hinp_len, hor_m, orEval] at rg
                change (run C.gates (inp t0)).getD (n + 2 + m) false = true
                rw [rg, List.any_eq_true]
                refine ⟨if i < n + 2 + m then (run C.gates (inp t0)).getD i false else false, List.mem_map.mpr ⟨i, hi, rfl⟩, ?_⟩
                simp only [id_eq, ite_eq_left hilt]; exact hit0
              · left
                intro ht1m
                have rg1 := run_gate C.gates (inp t1) m hmC
                have rg2 := run_gate C.gates (inp t2) m hmC
                rw [hinp_len, hor_m, orEval] at rg1 rg2
                change (run C.gates (inp t1)).getD (n + 2 + m) false = true at ht1m
                change (run C.gates (inp t2)).getD (n + 2 + m) false = true
                rw [rg1, List.any_eq_true] at ht1m
                rw [rg2, List.any_eq_true]
                obtain ⟨b', hb', hbt⟩ := ht1m
                obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb'
                have hilt : i < n + 2 + m := hrb m hmC i (by
                  change i ∈ (C.gates.getD m ⟨.or, []⟩).inputs
                  rw [List.getD_eq_getElem C.gates _ hmC]; exact hi)
                simp only [id_eq, ite_eq_left hilt] at hbt
                rcases ih i (by omega) (by omega) with himp | hit0
                · refine ⟨if i < n + 2 + m then (run C.gates (inp t2)).getD i false else false, List.mem_map.mpr ⟨i, hi, rfl⟩, ?_⟩
                  simp only [id_eq, ite_eq_left hilt]
                  exact himp hbt
                · exact absurd ⟨i, hi, hit0⟩ hex0
      rcases hinv_or w_in hw_in_lt with himp | ht0w
      · have := himp hwin_t1; rw [hwin_t2] at this; cases this
      · rw [hwin_t0] at ht0w; cases ht0w
    · by_contra hnoOr
      have hall_and : ∀ m (hum : u < m) (hmv : m < v), (C.gates[m]'(by omega)).op = .and := by
        intro m hum hmv
        have hmC : m < C.gates.length := by omega
        have hg_eq : C.gates[m] = C.gates.getD m ⟨.or, []⟩ := (List.getD_eq_getElem C.gates _ hmC).symm
        have hop_eq : (C.gates[m]).op = op m := congrArg PEqualNP.CircuitLowerBounds.Gate.op hg_eq
        rcases (hfan _ (List.getElem_mem hmC)).1 with hand | hor | hnot'
        · exact hand
        · exact absurd ⟨m, hum, hmv, hop_eq.symm.trans hor⟩ hnoOr
        · have hnf := hnoNot m hum hmv
          have : op m = .not := hop_eq.symm.trans hnot'
          rw [this] at hnf; simp at hnf
      have hinv_and : ∀ w < n + 2 + v, (wire t1 w = true → wire t2 w = true) ∨ wire t3 w = false := by
        intro w
        induction w using Nat.strong_induction_on with
        | ind w ih =>
          intro hwv
          by_cases hwu : w < n + 2 + u
          · exact Or.inl (hmono12 w hwu)
          · by_cases hweq : w = n + 2 + u
            · subst hweq; exact Or.inr hu_t3
            · let m : ℕ := w - (n + 2)
              have hwm : w = n + 2 + m := by omega
              have hum : u < m := by omega
              have hmv : m < v := by omega
              have hmC : m < C.gates.length := by omega
              have hand_m : (C.gates[m]).op = .and := hall_and m hum hmv
              rw [hwm]
              by_cases hex3 : ∃ i ∈ (C.gates[m]).inputs, wire t3 i = false
              · right
                obtain ⟨i, hi, hit3⟩ := hex3
                have hilt : i < n + 2 + m := hrb m hmC i (by
                  change i ∈ (C.gates.getD m ⟨.or, []⟩).inputs
                  rw [List.getD_eq_getElem C.gates _ hmC]; exact hi)
                have rg := run_gate C.gates (inp t3) m hmC
                rw [hinp_len, hand_m, andEval] at rg
                change (run C.gates (inp t3)).getD (n + 2 + m) false = false
                rw [rg, List.all_eq_false]
                refine ⟨if i < n + 2 + m then (run C.gates (inp t3)).getD i false else false, List.mem_map.mpr ⟨i, hi, rfl⟩, ?_⟩
                simp only [id_eq, ite_eq_left hilt]
                change ¬ wire t3 i = true
                rw [hit3]; decide
              · left
                intro ht1m
                have rg1 := run_gate C.gates (inp t1) m hmC
                have rg2 := run_gate C.gates (inp t2) m hmC
                rw [hinp_len, hand_m, andEval] at rg1 rg2
                change (run C.gates (inp t1)).getD (n + 2 + m) false = true at ht1m
                change (run C.gates (inp t2)).getD (n + 2 + m) false = true
                rw [rg1, List.all_eq_true] at ht1m
                rw [rg2, List.all_eq_true]
                intro b' hb'
                obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb'
                have hilt : i < n + 2 + m := hrb m hmC i (by
                  change i ∈ (C.gates.getD m ⟨.or, []⟩).inputs
                  rw [List.getD_eq_getElem C.gates _ hmC]; exact hi)
                have hbt := ht1m _ (List.mem_map.mpr ⟨i, hi, rfl⟩)
                simp only [id_eq, ite_eq_left hilt] at hbt ⊢
                rcases ih i (by omega) (by omega) with himp | hit3
                · exact himp hbt
                · exact absurd ⟨i, hi, hit3⟩ hex3
      rcases hinv_and w_in hw_in_lt with himp | ht3w
      · have := himp hwin_t1; rw [hwin_t2] at this; cases this
      · rw [hwin_t3] at ht3w; cases ht3w
  let idxAnd : Finset ℕ := (Finset.range C.size).filter (fun i => op i = .and)
  let idxOr : Finset ℕ := (Finset.range C.size).filter (fun i => op i = .or)
  let idxNot : Finset ℕ := (Finset.range C.size).filter (fun i => op i = .not)
  have hcard_eq : ∀ (target : PEqualNP.CircuitLowerBounds.GateOp),
      ((Finset.range C.size).filter (fun i => op i = target)).card =
      (C.gates.filter (fun g => decide (g.op = target))).length := by
    intro target
    have h1 : ((Finset.range C.size).filter (fun i => op i = target)).card =
        ((List.range C.size).filter (fun i => decide (op i = target))).length := by
      have hnd : ((List.range C.size).filter (fun i => decide (op i = target))).Nodup :=
        List.Nodup.filter _ List.nodup_range
      rw [← List.toFinset_card_of_nodup hnd]
      congr 1; ext i; simp
    rw [h1]
    exact filter_range_length_eq C.gates ⟨.or, []⟩ (fun g => decide (g.op = target))
  have hAnd_ge : b - 1 ≤ idxAnd.card := by
    have hex : ∀ j : Fin (b - 1), ∃ a, gates[j.val]'(by omega) < a ∧ a < gates[j.val + 1]'(by omega) ∧ op a = .and := by
      intro j
      exact (hBetween j.val (gates[j.val]'(by omega)) (gates[j.val + 1]'(by omega))
        (List.getElem?_eq_getElem (by omega)) (List.getElem?_eq_getElem (by omega))).1
    let f : Fin (b - 1) → ℕ := fun j => (hex j).choose
    have hf_mem : ∀ j : Fin (b - 1), f j ∈ idxAnd := by
      intro j
      obtain ⟨h1, h2, h3⟩ := (hex j).choose_spec
      have hvlt : gates[j.val + 1]'(by omega) < C.size := hgates_lt ⟨j.val + 1, by omega⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by dsimp only [f]; omega), h3⟩
    have hf_inj : Function.Injective f := by
      intro j1 j2 heq
      have hpw := List.pairwise_iff_getElem.mp (pairwise_filter_range C.size (fun i => decide (op i = .not)))
      have hglen : (List.filter (fun i => decide (op i = .not)) (List.range C.size)).length = b := hgates_len
      obtain ⟨h1a, h1b, _⟩ := (hex j1).choose_spec
      obtain ⟨h2a, h2b, _⟩ := (hex j2).choose_spec
      by_contra hne
      rcases Nat.lt_trichotomy j1.val j2.val with hlt | heq' | hgt
      · have hle : gates[j1.val + 1]'(by omega) ≤ gates[j2.val]'(by omega) := by
          rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hlt) with he | hlt'
          · exact le_of_eq (by congr 1)
          · exact le_of_lt (hpw (j1.val + 1) j2.val (by omega) (by omega) hlt')
        change (hex j1).choose = (hex j2).choose at heq; omega
      · exact hne (Fin.ext heq')
      · have hle : gates[j2.val + 1]'(by omega) ≤ gates[j1.val]'(by omega) := by
          rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hgt) with he | hlt'
          · exact le_of_eq (by congr 1)
          · exact le_of_lt (hpw (j2.val + 1) j1.val (by omega) (by omega) hlt')
        change (hex j1).choose = (hex j2).choose at heq; omega
    have hcard := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin (b - 1)))) f (fun j _ => hf_mem j) (fun a _ b' _ h => hf_inj h)
    simpa using hcard
  have hOr_ge : b - 1 ≤ idxOr.card := by
    have hex : ∀ j : Fin (b - 1), ∃ o, gates[j.val]'(by omega) < o ∧ o < gates[j.val + 1]'(by omega) ∧ op o = .or := by
      intro j
      exact (hBetween j.val (gates[j.val]'(by omega)) (gates[j.val + 1]'(by omega))
        (List.getElem?_eq_getElem (by omega)) (List.getElem?_eq_getElem (by omega))).2
    let f : Fin (b - 1) → ℕ := fun j => (hex j).choose
    have hf_mem : ∀ j : Fin (b - 1), f j ∈ idxOr := by
      intro j
      obtain ⟨h1, h2, h3⟩ := (hex j).choose_spec
      have hvlt : gates[j.val + 1]'(by omega) < C.size := hgates_lt ⟨j.val + 1, by omega⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by dsimp only [f]; omega), h3⟩
    have hf_inj : Function.Injective f := by
      intro j1 j2 heq
      have hpw := List.pairwise_iff_getElem.mp (pairwise_filter_range C.size (fun i => decide (op i = .not)))
      have hglen : (List.filter (fun i => decide (op i = .not)) (List.range C.size)).length = b := hgates_len
      obtain ⟨h1a, h1b, _⟩ := (hex j1).choose_spec
      obtain ⟨h2a, h2b, _⟩ := (hex j2).choose_spec
      by_contra hne
      rcases Nat.lt_trichotomy j1.val j2.val with hlt | heq' | hgt
      · have hle : gates[j1.val + 1]'(by omega) ≤ gates[j2.val]'(by omega) := by
          rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hlt) with he | hlt'
          · exact le_of_eq (by congr 1)
          · exact le_of_lt (hpw (j1.val + 1) j2.val (by omega) (by omega) hlt')
        change (hex j1).choose = (hex j2).choose at heq; omega
      · exact hne (Fin.ext heq')
      · have hle : gates[j2.val + 1]'(by omega) ≤ gates[j1.val]'(by omega) := by
          rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hgt) with he | hlt'
          · exact le_of_eq (by congr 1)
          · exact le_of_lt (hpw (j2.val + 1) j1.val (by omega) (by omega) hlt')
        change (hex j1).choose = (hex j2).choose at heq; omega
    have hcard := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin (b - 1)))) f (fun j _ => hf_mem j) (fun a _ b' _ h => hf_inj h)
    simpa using hcard
  have hNot_eq : idxNot.card = b := hcard_eq .not
  have hAnd_len : b - 1 ≤ (C.gates.filter (fun g => decide (g.op = .and))).length := by
    rw [← hcard_eq .and]; exact hAnd_ge
  have hOr_len : b - 1 ≤ (C.gates.filter (fun g => decide (g.op = .or))).length := by
    rw [← hcard_eq .or]; exact hOr_ge
  have hdisj1 : Disjoint idxNot idxAnd := by
    refine Finset.disjoint_left.mpr fun i h1 h2 => ?_
    have e1 := (Finset.mem_filter.mp h1).2
    have e2 := (Finset.mem_filter.mp h2).2
    rw [e1] at e2; cases e2
  have hdisj2 : Disjoint (idxNot ∪ idxAnd) idxOr := by
    refine Finset.disjoint_left.mpr fun i h1 h2 => ?_
    have e2 := (Finset.mem_filter.mp h2).2
    rcases Finset.mem_union.mp h1 with h | h
    · have e1 := (Finset.mem_filter.mp h).2; rw [e1] at e2; cases e2
    · have e1 := (Finset.mem_filter.mp h).2; rw [e1] at e2; cases e2
  have hsub : idxNot ∪ idxAnd ∪ idxOr ⊆ Finset.range C.size := by
    intro i hi
    rcases Finset.mem_union.mp hi with h | h
    · rcases Finset.mem_union.mp h with h' | h'
      · exact (Finset.mem_filter.mp h').1
      · exact (Finset.mem_filter.mp h').1
    · exact (Finset.mem_filter.mp h).1
  have htot : idxNot.card + idxAnd.card + idxOr.card ≤ C.size := by
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj2, Finset.card_union_of_disjoint hdisj1, Finset.card_range] at h1
    exact h1
  refine ⟨hBetween, hAnd_len, hOr_len, by omega⟩

end PEqualNP.Outside.L_lib_1311

theorem PEqualNP.Outside.L_lib_1311 :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    ∀ (n l : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C →
      ∀ x : Nat → Finset (Fin n), (∀ t<l, x t ⊆ x (t+1)) → ∀ obs : List (Fin (n+2+C.size)),
      let wire := fun t i => (C.wires (List.ofFn (fun j : Fin n => decide (j ∈ x t)) ++ [false,true])).getD i false
      let fall := fun t => obs.any (fun w => wire t w.val && !(wire (t+1) w.val))
      let op := fun i => (C.gates.getD i ⟨.or,[]⟩).op
      let gates := (List.range C.size).filter (fun i => decide (op i=.not))
      let b := PEqualNP.NotBracket.notCount C
      ((Finset.range l).filter (fun t => fall t=true)).card+1=2^b →
        (∀ j u v, gates[j]?=some u → gates[j+1]?=some v →
          (∃ a, u<a ∧ a<v ∧ op a=.and) ∧ (∃ o, u<o ∧ o<v ∧ op o=.or)) ∧
        b-1 ≤ (C.gates.filter (fun g => decide (g.op=.and))).length ∧
        b-1 ≤ (C.gates.filter (fun g => decide (g.op=.or))).length ∧
        b+2*(b-1) ≤ C.size := by
  dsimp only
  intro n l C hfan hrb x hx obs hsat
  have hres := PEqualNP.Outside.L_lib_1311.main_clean n l C hfan hrb x hx obs
  dsimp only at hres
  have hdec : ∀ (P : Prop) (d1 d2 : Decidable P), @decide P d1 = @decide P d2 :=
    fun _ _ _ => decide_eq_decide.mpr Iff.rfl
  have hwire : ∀ t,
      List.ofFn (fun j : Fin n => @decide (j ∈ x t) (Classical.propDecidable _)) =
      List.ofFn (fun j : Fin n => decide (j ∈ x t)) := fun t => by
    congr 1; funext j; exact hdec _ _ _
  have hsat' :
      ((Finset.range l).filter (fun t =>
        obs.any (fun w =>
          (C.wires (List.ofFn (fun j : Fin n => decide (j ∈ x t)) ++ [false, true])).getD w.val false &&
          !((C.wires (List.ofFn (fun j : Fin n => decide (j ∈ x (t + 1))) ++ [false, true])).getD w.val false)) = true)).card + 1 =
      2 ^ PEqualNP.NotBracket.notCount C := by
    have hfeq :
        @Finset.filter ℕ
          (fun t => obs.any (fun w =>
            (C.wires (List.ofFn (fun j : Fin n => @decide (j ∈ x t) (Classical.propDecidable _)) ++ [false, true])).getD w.val false &&
            !((C.wires (List.ofFn (fun j : Fin n => @decide (j ∈ x (t + 1)) (Classical.propDecidable _)) ++ [false, true])).getD w.val false)) = true)
          (fun t => Classical.propDecidable _) (Finset.range l) =
        (Finset.range l).filter (fun t =>
          obs.any (fun w =>
            (C.wires (List.ofFn (fun j : Fin n => decide (j ∈ x t)) ++ [false, true])).getD w.val false &&
            !((C.wires (List.ofFn (fun j : Fin n => decide (j ∈ x (t + 1))) ++ [false, true])).getD w.val false)) = true) := by
      ext t
      simp only [Finset.mem_filter, hwire]
    rw [← hfeq]
    exact hsat
  obtain ⟨h1, h2, h3, h4⟩ := hres hsat'
  have hfilt : ∀ (op0 : PEqualNP.CircuitLowerBounds.GateOp),
      (C.gates.filter (fun g => @decide (g.op = op0) (Classical.propDecidable _))) =
      (C.gates.filter (fun g => @decide (g.op = op0) (PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq _ _))) :=
    fun op0 => List.filter_congr fun g _ => hdec _ _ _
  have hgates :
      (List.range C.size).filter (fun i => @decide ((C.gates.getD i ⟨.or, []⟩).op = .not) (Classical.propDecidable _)) =
      (List.range C.size).filter (fun i => @decide ((C.gates.getD i ⟨.or, []⟩).op = .not) (PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq _ _)) :=
    List.filter_congr fun i _ => hdec _ _ _
  refine ⟨?_, ?_, ?_, h4⟩
  · rw [hgates]; exact h1
  · rw [hfilt .and]; exact h2
  · rw [hfilt .or]; exact h3
