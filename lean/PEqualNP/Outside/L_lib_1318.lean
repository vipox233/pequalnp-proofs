import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1318

open PEqualNP.CircuitLowerBounds

private theorem andEval (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl

private theorem any_congr {α : Type*} (l : List α) (f g : α → Bool) (h : ∀ a ∈ l, f a = g a) :
    l.any f = l.any g := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true]
  exact ⟨fun ⟨a, ha, hfa⟩ => ⟨a, ha, (h a ha) ▸ hfa⟩, fun ⟨a, ha, hga⟩ => ⟨a, ha, (h a ha).symm ▸ hga⟩⟩

private theorem all_congr {α : Type*} (l : List α) (f g : α → Bool) (h : ∀ a ∈ l, f a = g a) :
    l.all f = l.all g := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  exact ⟨fun hf a ha => (h a ha) ▸ hf a ha, fun hg a ha => (h a ha).symm ▸ hg a ha⟩
private theorem orEval (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
private theorem notEval_nil : GateOp.not.eval [] = true := rfl
private theorem notEval_cons (a : Bool) (as : List Bool) : GateOp.not.eval (a :: as) = !a := rfl

private def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp only [run, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih =>
    rw [run_snoc, List.length_append, List.length_singleton, ih, List.length_append, List.length_singleton]
    omega

private theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (ht : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left ht, ← List.getD_eq_getElem?_getD]

private theorem getD_eq (l : List Bool) (b : Bool) :
    (l ++ [b]).getD l.length false = b := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]
  simp

private theorem run_prefix (gs1 gs2 : List Gate) (x : List Bool) (w : ℕ)
    (hw : w < x.length + gs1.length) :
    (run (gs1 ++ gs2) x).getD w false = (run gs1 x).getD w false := by
  induction gs2 using List.reverseRecOn with
  | nil => simp
  | append_singleton gs2 g ih =>
    rw [← List.append_assoc, run_snoc, getD_lt]
    · exact ih
    · rw [run_length, List.length_append]; omega

private theorem run_input (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  simpa [run] using run_prefix [] gs x w (by simpa using hw)

private theorem run_gate (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length) :
    (run gs x).getD (x.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < x.length + j then (run gs x).getD i false else false) := by
  have hsplit : gs = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by
    have h1 := (List.take_append_drop j gs).symm
    have h2 : gs.drop j = gs[j] :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simpa [List.append_assoc] using h1
  have hlen : (gs.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
  have hp1 : (run gs x).getD (x.length + j) false =
      (run (gs.take j ++ [gs[j]]) x).getD (x.length + j) false := by
    conv_lhs => rw [hsplit]
    exact run_prefix (gs.take j ++ [gs[j]]) (gs.drop (j + 1)) x (x.length + j) (by rw [List.length_append, List.length_singleton, hlen]; omega)
  rw [hp1, run_snoc]
  have hrlen : (run (gs.take j) x).length = x.length + j := by rw [run_length, hlen]
  rw [← hrlen, getD_eq]
  congr 1
  apply List.map_congr_left
  intro i _
  rw [hrlen]
  by_cases hi : i < x.length + j
  · rw [if_pos hi]
    have htake : (run gs x).getD i false = (run (gs.take j) x).getD i false := by
      conv_lhs => rw [hsplit, List.append_assoc]
      exact run_prefix (gs.take j) ([gs[j]] ++ gs.drop (j + 1)) x i (by rw [hlen]; exact hi)
    exact htake.symm
  · rw [if_neg hi]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

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
      apply List.filter_congr
      intro i hi
      have hilt : i < xs.length := List.mem_range.mp hi
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hilt, ← List.getD_eq_getElem?_getD]
    have h2 : ([xs.length].filter (fun i => p ((xs ++ [x]).getD i d))).length = ([x].filter p).length := by
      have hg : (xs ++ [x]).getD xs.length d = x := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]; simp
      cases hp : p x <;> simp [hg, hp]
    rw [h1, ih, h2]

private theorem pairwise_filter_range (n : ℕ) (p : ℕ → Bool) :
    ((List.range n).filter p).Pairwise (· < ·) :=
  List.Pairwise.filter p List.pairwise_lt_range

private def fitsClean (t : ℕ) (I : Type) (n b : ℕ) (x : I → Finset (Fin n)) (ok : I → Finset (Fin t) → Prop) : Prop :=
  ∃ (C : Circuit) (tap : Fin t → ℕ),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C ∧
    C.output < n + 2 + C.size ∧ (∀ a, tap a < n + 2 + C.size) ∧ PEqualNP.NotBracket.notCount C ≤ b ∧
    ∀ i, ok i (Finset.univ.filter (fun a =>
      (C.wires (List.ofFn (fun j : Fin n => decide (j ∈ x i)) ++ [false, true])).getD (tap a) false = true))

-- Part 1: upper bound on bad blocks
set_option maxHeartbeats 800000 in
private theorem part1_clean (t n m k b : ℕ) (x : Fin m → Finset (Fin n)) (block : Fin m → Fin k)
    (ok : Fin m → Finset (Fin t) → Prop)
    (hblk : ∀ i j, block i < block j → x i ⊆ x j)
    (hfits : fitsClean t (Fin m) n b x ok)
    (Bad : Finset (Fin k))
    (hBad : ∀ j ∈ Bad, ¬ ∃ w : Finset (Fin t), ∀ i, block i = j → ok i w) :
    Bad.card < (t + 1) * 2 ^ b := by
  let _ : DecidableEq GateOp := PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq
  obtain ⟨C, tap, hfan, hrb, _hout, htap, hnot_le, hok⟩ := hfits
  let inp : Fin m → List Bool := fun i => List.ofFn (fun j : Fin n => decide (j ∈ x i)) ++ [false, true]
  let wire : Fin m → ℕ → Bool := fun i w => (run C.gates (inp i)).getD w false
  let W : Fin m → Finset (Fin t) := fun i => Finset.univ.filter (fun a => wire i (tap a) = true)
  let op : ℕ → GateOp := fun u => (C.gates.getD u ⟨.or, []⟩).op
  let gates : List ℕ := (List.range C.size).filter (fun u => decide (op u = .not))
  have hinp_len : ∀ i, (inp i).length = n + 2 := fun i => by simp [inp]
  have hgates_len : gates.length = PEqualNP.NotBracket.notCount C := by
    dsimp only [gates, PEqualNP.NotBracket.notCount]
    exact filter_range_length_eq C.gates ⟨.or, []⟩ (fun g => decide (g.op = .not))
  have hgates_lt : ∀ r : Fin gates.length, gates[r] < C.gates.length := fun r =>
    List.mem_range.mp (List.mem_filter.mp (List.getElem_mem r.isLt)).1
  have hgates_not : ∀ r : Fin gates.length, op gates[r] = .not := fun r =>
    of_decide_eq_true (List.mem_filter.mp (List.getElem_mem r.isLt)).2
  have hgates_mem : ∀ u < C.gates.length, op u = .not → ∃ r : Fin gates.length, gates[r] = u := by
    intro u hu hop
    have hm : u ∈ gates := List.mem_filter.mpr ⟨List.mem_range.mpr hu, decide_eq_true hop⟩
    obtain ⟨r, hr, heq⟩ := List.mem_iff_getElem.mp hm
    exact ⟨⟨r, hr⟩, heq⟩
  have hpref_mono : ∀ (i1 i2 : Fin m), x i1 ⊆ x i2 → ∀ (u : ℕ), u ≤ C.gates.length →
      (∀ v < u, op v = .not → wire i1 (n + 2 + v) = true → wire i2 (n + 2 + v) = true) →
      ∀ w < n + 2 + u, wire i1 w = true → wire i2 w = true := by
    intro i1 i2 hsub u hu hnot w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw hwt1
      by_cases hwin : w < n + 2
      · have h1 : wire i1 w = (inp i1).getD w false := run_input C.gates (inp i1) w (by rw [hinp_len]; exact hwin)
        have h2 : wire i2 w = (inp i2).getD w false := run_input C.gates (inp i2) w (by rw [hinp_len]; exact hwin)
        rw [h1] at hwt1; rw [h2]
        by_cases hwn : w < n
        · have hv1 : (inp i1).getD w false = decide (⟨w, hwn⟩ ∈ x i1) := by
            dsimp only [inp]; rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hwn]), List.getElem?_ofFn]; simp [hwn]
          have hv2 : (inp i2).getD w false = decide (⟨w, hwn⟩ ∈ x i2) := by
            dsimp only [inp]; rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hwn]), List.getElem?_ofFn]; simp [hwn]
          rw [hv1] at hwt1; rw [hv2]
          exact decide_eq_true (hsub (of_decide_eq_true hwt1))
        · rcases (show w = n ∨ w = n + 1 by omega) with hwn1 | hwn2
          · rw [hwn1] at hwt1
            have : (inp i1).getD n false = false := by
              dsimp only [inp]; rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]; simp
            rw [this] at hwt1; cases hwt1
          · rw [hwn2]; dsimp only [inp]; rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]; simp
      · let v : ℕ := w - (n + 2)
        have hwv : w = n + 2 + v := by omega
        have hvu : v < u := by omega
        have hvC : v < C.gates.length := by omega
        rw [hwv] at hwt1 ⊢
        have hg_eq : C.gates[v] = C.gates.getD v ⟨.or, []⟩ := (List.getD_eq_getElem C.gates _ hvC).symm
        have hop_eq : (C.gates[v]).op = op v := congrArg Gate.op hg_eq
        rcases (hfan _ (List.getElem_mem hvC)).1 with hand | hor | hnot'
        · have rg1 := run_gate C.gates (inp i1) v hvC
          have rg2 := run_gate C.gates (inp i2) v hvC
          rw [hinp_len, hand, andEval] at rg1 rg2
          change (run C.gates (inp i1)).getD (n + 2 + v) false = true at hwt1
          change (run C.gates (inp i2)).getD (n + 2 + v) false = true
          rw [rg1, List.all_eq_true] at hwt1
          rw [rg2, List.all_eq_true]
          intro b' hb'
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb'
          have hqlt : q < n + 2 + v := hrb v hvC q (by
            change q ∈ (C.gates.getD v ⟨.or, []⟩).inputs
            rw [List.getD_eq_getElem C.gates _ hvC]; exact hq)
          have hbt := hwt1 _ (List.mem_map.mpr ⟨q, hq, rfl⟩)
          simp only [id_eq, if_pos hqlt] at hbt ⊢
          exact ih q (by omega) (by omega) hbt
        · have rg1 := run_gate C.gates (inp i1) v hvC
          have rg2 := run_gate C.gates (inp i2) v hvC
          rw [hinp_len, hor, orEval] at rg1 rg2
          change (run C.gates (inp i1)).getD (n + 2 + v) false = true at hwt1
          change (run C.gates (inp i2)).getD (n + 2 + v) false = true
          rw [rg1, List.any_eq_true] at hwt1
          rw [rg2, List.any_eq_true]
          obtain ⟨b', hb', hbt⟩ := hwt1
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb'
          have hqlt : q < n + 2 + v := hrb v hvC q (by
            change q ∈ (C.gates.getD v ⟨.or, []⟩).inputs
            rw [List.getD_eq_getElem C.gates _ hvC]; exact hq)
          simp only [id_eq, if_pos hqlt] at hbt
          refine ⟨if q < n + 2 + v then (run C.gates (inp i2)).getD q false else false,
            List.mem_map.mpr ⟨q, hq, rfl⟩, ?_⟩
          simp only [id_eq, if_pos hqlt]
          exact ih q (by omega) (by omega) hbt
        · exact hnot v hvu (hop_eq.symm.trans hnot') hwt1
  let bits : Fin m → Fin gates.length → Bool := fun i r => wire i (n + 2 + gates[r])
  let inv : Fin m → ℕ := fun i =>
    ∑ r : Fin gates.length, if bits i r = true then 2 ^ (gates.length - 1 - r.val) else 0
  have hinv_lt_b : ∀ i, inv i < 2 ^ b := fun i => by
    have h1 : inv i < 2 ^ gates.length := sum_pow_lt gates.length (bits i)
    have h2 : 2 ^ gates.length ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hinv_le : ∀ i1 i2, x i1 ⊆ x i2 → inv i2 ≤ inv i1 := by
    intro i1 i2 hsub
    by_contra hlt
    have hlt' : inv i1 < inv i2 := by omega
    obtain ⟨r, hpre, hfr, hgr⟩ := binary_lt_first_diff gates.length (bits i1) (bits i2) hlt'
    let u : ℕ := gates[r]
    have huC : u < C.gates.length := hgates_lt r
    have hu_not : (C.gates[u]).op = .not := by
      have hg_eq : C.gates[u] = C.gates.getD u ⟨.or, []⟩ := (List.getD_eq_getElem C.gates _ huC).symm
      rw [hg_eq]; exact hgates_not r
    have hprev_eq : ∀ v < u, op v = .not → wire i1 (n + 2 + v) = true → wire i2 (n + 2 + v) = true := by
      intro v hvu hvnot hwm
      obtain ⟨s, hsv⟩ := hgates_mem v (by omega) hvnot
      have hsr : s.val < r.val := by
        have hpw := List.pairwise_iff_getElem.mp (pairwise_filter_range C.size (fun i => decide (op i = .not)))
        by_contra hge
        rcases Nat.eq_or_lt_of_le (Nat.le_of_not_lt hge) with heq | hlt2
        · have h1 : s = r := Fin.ext heq.symm; rw [h1] at hsv; dsimp only [u] at hvu; omega
        · have hlt_u : gates[r.val] < gates[s.val] := hpw r.val s.val r.isLt s.isLt hlt2
          have hsv' : gates[s.val] = v := hsv
          have hu_eq : gates[r.val] = u := rfl
          omega
      have heq := hpre s hsr
      dsimp only [bits] at heq
      rw [hsv] at heq; rw [← heq]; exact hwm
    have hmono_u := hpref_mono i1 i2 hsub u (Nat.le_of_lt huC) hprev_eq
    have rg1 := run_gate C.gates (inp i1) u huC
    have rg2 := run_gate C.gates (inp i2) u huC
    rw [hinp_len] at rg1 rg2
    dsimp only [bits] at hfr hgr
    change (run C.gates (inp i1)).getD (n + 2 + u) false = false at hfr
    change (run C.gates (inp i2)).getD (n + 2 + u) false = true at hgr
    rw [rg1, hu_not] at hfr
    rw [rg2, hu_not] at hgr
    rcases hinps : (C.gates[u]).inputs with _ | ⟨w_in, rest⟩
    · rw [hinps, List.map_nil, notEval_nil] at hfr; cases hfr
    · rw [hinps, List.map_cons, notEval_cons] at hfr hgr
      have hwlt : w_in < n + 2 + u := hrb u huC w_in (by
        change w_in ∈ (C.gates.getD u ⟨.or, []⟩).inputs
        rw [List.getD_eq_getElem C.gates _ huC, hinps]; exact List.mem_cons_self)
      simp only [if_pos hwlt] at hfr hgr
      change (!wire i1 w_in) = false at hfr
      change (!wire i2 w_in) = true at hgr
      have h1 : wire i1 w_in = true := by cases h : wire i1 w_in <;> rw [h] at hfr <;> first | rfl | cases hfr
      have h2 : wire i2 w_in = false := by cases h : wire i2 w_in <;> rw [h] at hgr <;> first | rfl | cases hgr
      have h3 := hmono_u w_in hwlt h1
      rw [h2] at h3; cases h3
  have hW_sub : ∀ i1 i2, x i1 ⊆ x i2 → inv i2 = inv i1 → W i1 ⊆ W i2 := by
    intro i1 i2 hsub heq
    have hbits := binary_eq_of_sum_eq gates.length (bits i2) (bits i1) heq
    have hall : ∀ w < n + 2 + C.gates.length, wire i1 w = true → wire i2 w = true := by
      refine hpref_mono i1 i2 hsub C.gates.length le_rfl ?_
      intro u huC hunot hwt
      obtain ⟨r, hru⟩ := hgates_mem u huC hunot
      have hr := hbits r; dsimp only [bits] at hr; rw [hru] at hr; rw [hr]; exact hwt
    intro a ha
    have ha' : wire i1 (tap a) = true := (Finset.mem_filter.mp ha).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, hall (tap a) (htap a) ha'⟩
  have hBad_two : ∀ j ∈ Bad, ∃ i1 i2 : Fin m, block i1 = j ∧ block i2 = j ∧ W i1 ≠ W i2 := by
    intro j hj
    by_contra hno
    push_neg at hno
    by_cases hex : ∃ i0 : Fin m, block i0 = j
    · obtain ⟨i0, hi0⟩ := hex
      apply hBad j hj
      refine ⟨W i0, fun i hi => ?_⟩
      have heq := hno i i0 hi hi0
      rw [← heq]
      exact hok i
    · apply hBad j hj
      exact ⟨∅, fun i hi => absurd ⟨i, hi⟩ hex⟩
  let S : Fin k → Finset (Fin m) := fun j => Finset.univ.filter (fun i => block i = j)
  have hS_ne : ∀ j ∈ Bad, (S j).Nonempty := by
    intro j hj
    obtain ⟨i1, _, hi1, _, _⟩ := hBad_two j hj
    exact ⟨i1, Finset.mem_filter.mpr ⟨Finset.mem_univ i1, hi1⟩⟩
  let Nmax : Fin k → ℕ := fun j =>
    if h : (S j).Nonempty then ((S j).image inv).max' (h.image inv) else 0
  have hNmax_ge : ∀ j ∈ Bad, ∀ i ∈ S j, inv i ≤ Nmax j := by
    intro j hj i hi
    dsimp only [Nmax]
    rw [dif_pos (hS_ne j hj)]
    exact Finset.le_max' _ _ (Finset.mem_image_of_mem inv hi)
  have hNmax_ex : ∀ j ∈ Bad, ∃ i ∈ S j, inv i = Nmax j := by
    intro j hj
    dsimp only [Nmax]
    rw [dif_pos (hS_ne j hj)]
    have hm := Finset.max'_mem ((S j).image inv) ((hS_ne j hj).image inv)
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hm
    exact ⟨i, hi, heq⟩
  let T : Fin k → Finset (Fin m) := fun j => (S j).filter (fun i => inv i = Nmax j)
  have hT_ne : ∀ j ∈ Bad, (T j).Nonempty := by
    intro j hj
    obtain ⟨i, hi, heq⟩ := hNmax_ex j hj
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, heq⟩⟩
  let Wmin : Fin k → ℕ := fun j =>
    if h : (T j).Nonempty then ((T j).image (fun i => (W i).card)).min' (h.image _) else 0
  have hWmin_le : ∀ j ∈ Bad, ∀ i ∈ T j, Wmin j ≤ (W i).card := by
    intro j hj i hi
    dsimp only [Wmin]
    rw [dif_pos (hT_ne j hj)]
    exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ hi)
  have hWmin_ex : ∀ j ∈ Bad, ∃ i ∈ T j, (W i).card = Wmin j := by
    intro j hj
    dsimp only [Wmin]
    rw [dif_pos (hT_ne j hj)]
    have hm := Finset.min'_mem ((T j).image (fun i => (W i).card)) ((hT_ne j hj).image _)
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hm
    exact ⟨i, hi, heq⟩
  have hW_card_le : ∀ i, (W i).card ≤ t := fun i => by
    have := Finset.card_le_univ (W i); simpa using this
  let Φ : Fin k → ℕ := fun j => (t + 1) * Nmax j + (t - Wmin j)
  have hΦ_mem : ∀ j ∈ Bad, Φ j ∈ Finset.Ico 1 ((t + 1) * 2 ^ b) := by
    intro j hj
    obtain ⟨i0, hi0, hN0⟩ := hNmax_ex j hj
    have hNlt : Nmax j < 2 ^ b := hN0 ▸ hinv_lt_b i0
    have hupper : Φ j < (t + 1) * 2 ^ b := by
      have h1 : (t + 1) * (Nmax j + 1) ≤ (t + 1) * 2 ^ b := Nat.mul_le_mul_left (t + 1) (by omega)
      have h2 : t - Wmin j ≤ t := Nat.sub_le t (Wmin j)
      dsimp only [Φ]; nlinarith
    have hlower : 1 ≤ Φ j := by
      by_cases hNpos : 1 ≤ Nmax j
      · dsimp only [Φ]; nlinarith
      · have hNzero : Nmax j = 0 := by omega
        obtain ⟨i1, i2, h1, h2, hne⟩ := hBad_two j hj
        have hi1S : i1 ∈ S j := Finset.mem_filter.mpr ⟨Finset.mem_univ i1, h1⟩
        have hi2S : i2 ∈ S j := Finset.mem_filter.mpr ⟨Finset.mem_univ i2, h2⟩
        have hi1T : i1 ∈ T j := Finset.mem_filter.mpr ⟨hi1S, by have := hNmax_ge j hj i1 hi1S; omega⟩
        have hi2T : i2 ∈ T j := Finset.mem_filter.mpr ⟨hi2S, by have := hNmax_ge j hj i2 hi2S; omega⟩
        have hlt_t : Wmin j < t := by
          by_cases hu1 : W i1 = Finset.univ
          · have hu2 : W i2 ≠ Finset.univ := fun h => hne (hu1.trans h.symm)
            have hc : (W i2).card < t := by
              have hss : W i2 ⊂ Finset.univ := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hu2⟩
              simpa using Finset.card_lt_card hss
            have := hWmin_le j hj i2 hi2T; omega
          · have hc : (W i1).card < t := by
              have hss : W i1 ⊂ Finset.univ := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hu1⟩
              simpa using Finset.card_lt_card hss
            have := hWmin_le j hj i1 hi1T; omega
        dsimp only [Φ]; omega
    exact Finset.mem_Ico.mpr ⟨hlower, hupper⟩
  have hΦ_anti : ∀ j1 ∈ Bad, ∀ j2 ∈ Bad, j1 < j2 → Φ j2 < Φ j1 := by
    intro j1 hj1 j2 hj2 hlt
    obtain ⟨i2, hi2T, hi2W⟩ := hWmin_ex j2 hj2
    have hi2S : i2 ∈ S j2 := (Finset.mem_filter.mp hi2T).1
    have hi2blk : block i2 = j2 := (Finset.mem_filter.mp hi2S).2
    have hi2N : inv i2 = Nmax j2 := (Finset.mem_filter.mp hi2T).2
    have hN2le1 : Nmax j2 ≤ Nmax j1 := by
      obtain ⟨i1, hi1S, hi1N⟩ := hNmax_ex j1 hj1
      have hi1blk : block i1 = j1 := (Finset.mem_filter.mp hi1S).2
      have hsub := hblk i1 i2 (by rw [hi1blk, hi2blk]; exact hlt)
      have := hinv_le i1 i2 hsub
      omega
    rcases Nat.lt_or_eq_of_le hN2le1 with hNlt | hNeq
    · have h1 : (t + 1) * (Nmax j2 + 1) ≤ (t + 1) * Nmax j1 := Nat.mul_le_mul_left (t + 1) (by omega)
      have h2 : t - Wmin j2 ≤ t := Nat.sub_le t (Wmin j2)
      dsimp only [Φ]; nlinarith
    · obtain ⟨ia, ib, ha, hb, hne⟩ := hBad_two j1 hj1
      have haS : ia ∈ S j1 := Finset.mem_filter.mpr ⟨Finset.mem_univ ia, ha⟩
      have hbS : ib ∈ S j1 := Finset.mem_filter.mpr ⟨Finset.mem_univ ib, hb⟩
      have hsuba : x ia ⊆ x i2 := hblk ia i2 (by rw [ha, hi2blk]; exact hlt)
      have hsubb : x ib ⊆ x i2 := hblk ib i2 (by rw [hb, hi2blk]; exact hlt)
      have hNa : inv ia = Nmax j1 := by
        have h1 := hNmax_ge j1 hj1 ia haS
        have h2 := hinv_le ia i2 hsuba
        omega
      have hNb : inv ib = Nmax j1 := by
        have h1 := hNmax_ge j1 hj1 ib hbS
        have h2 := hinv_le ib i2 hsubb
        omega
      have haT : ia ∈ T j1 := Finset.mem_filter.mpr ⟨haS, hNa⟩
      have hbT : ib ∈ T j1 := Finset.mem_filter.mpr ⟨hbS, hNb⟩
      have hWa : W ia ⊆ W i2 := hW_sub ia i2 hsuba (by omega)
      have hWb : W ib ⊆ W i2 := hW_sub ib i2 hsubb (by omega)
      have hWlt : Wmin j1 < Wmin j2 := by
        by_cases heqa : W ia = W i2
        · have hneb : W ib ≠ W i2 := fun h => hne (heqa.trans h.symm)
          have hc : (W ib).card < (W i2).card :=
            Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hWb, hneb⟩)
          have := hWmin_le j1 hj1 ib hbT; omega
        · have hc : (W ia).card < (W i2).card :=
            Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hWa, heqa⟩)
          have := hWmin_le j1 hj1 ia haT; omega
      have hW2le : Wmin j2 ≤ t := hi2W ▸ hW_card_le i2
      dsimp only [Φ]; rw [hNeq]; omega
  have hΦ_inj : Set.InjOn Φ (Bad : Set (Fin k)) := by
    intro j1 hj1 j2 hj2 heq
    rcases lt_trichotomy j1 j2 with hlt | rfl | hgt
    · have := hΦ_anti j1 hj1 j2 hj2 hlt; omega
    · rfl
    · have := hΦ_anti j2 hj2 j1 hj1 hgt; omega
  have hcard := Finset.card_le_card_of_injOn Φ hΦ_mem hΦ_inj
  rw [Nat.card_Ico] at hcard
  have hpos : 0 < (t + 1) * 2 ^ b := Nat.mul_pos (by omega) (Nat.pow_pos (by omega))
  omega

-- Part 2: circuit builder helpers
private def Ctx (n : ℕ) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) ∧
  (∀ i < gs.length, ∀ w ∈ (gs.getD i ⟨.or, []⟩).inputs, w < n + 2 + i)

private theorem ctx_nil (n : ℕ) : Ctx n [] := ⟨by simp, by intro i hi; simp at hi⟩

private theorem ctx_snoc (n : ℕ) (gs : List Gate) (g : Gate) (hctx : Ctx n gs)
    (hfan : (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hrb : ∀ w ∈ g.inputs, w < n + 2 + gs.length) :
    Ctx n (gs ++ [g]) := by
  refine ⟨?_, ?_⟩
  · intro g' hg'
    rcases List.mem_append.mp hg' with h1 | h2
    · exact hctx.1 g' h1
    · rw [List.mem_singleton.mp h2]; exact hfan
  · intro i hi w hw
    rw [List.length_append, List.length_singleton] at hi
    by_cases hlt : i < gs.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, ← List.getD_eq_getElem?_getD] at hw
      exact hctx.2 i hlt w hw
    · have hieq : i = gs.length := by omega
      subst hieq
      have hge : (gs ++ [g]).getD gs.length ⟨.or, []⟩ = g := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]; simp
      rw [hge] at hw
      exact hrb w hw

private theorem ctx_to_fanInTwo (n : ℕ) (gs : List Gate) (o : ℕ) (h : Ctx n gs) :
    PEqualNP.MetaComplexity.FanInTwo ⟨gs, o⟩ := by
  intro g hg
  obtain ⟨ho, hl⟩ := h.1 g hg
  exact ⟨by simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using ho, hl⟩

private theorem ctx_to_readsBack (n : ℕ) (gs : List Gate) (o : ℕ) (h : Ctx n gs) :
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) ⟨gs, o⟩ := h.2

private theorem notCount_snoc (gs : List Gate) (g : Gate) :
    PEqualNP.NotBracket.notCount ⟨gs ++ [g], 0⟩ =
    PEqualNP.NotBracket.notCount ⟨gs, 0⟩ + (match g.op with | .not => 1 | _ => 0) := by
  dsimp only [PEqualNP.NotBracket.notCount]
  rw [List.filter_append, List.length_append]
  cases h : g.op <;> simp [h]

private def addAnd (n : ℕ) (gs : List Gate) (a b : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨.and, [a, b]⟩], n + 2 + gs.length)

private def addOr (n : ℕ) (gs : List Gate) (a b : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨.or, [a, b]⟩], n + 2 + gs.length)

private def addNot (n : ℕ) (gs : List Gate) (a : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨.not, [a]⟩], n + 2 + gs.length)

private def addAndList (n : ℕ) (gs : List Gate) : List ℕ → List Gate × ℕ
  | [] => (gs, n + 1)
  | w :: ws =>
    let r := addAndList n gs ws
    addAnd n r.1 w r.2

private def addOrList (n : ℕ) (gs : List Gate) : List ℕ → List Gate × ℕ
  | [] => (gs, n)
  | w :: ws =>
    let r := addOrList n gs ws
    addOr n r.1 w r.2

private theorem addAndList_spec (n : ℕ) (gs : List Gate) (ws : List ℕ)
    (hctx : Ctx n gs) (hws : ∀ w ∈ ws, w < n + 2 + gs.length) :
    let r := addAndList n gs ws
    (∃ ext, r.1 = gs ++ ext) ∧
    Ctx n r.1 ∧
    r.2 < n + 2 + r.1.length ∧
    PEqualNP.NotBracket.notCount ⟨r.1, 0⟩ = PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ∧
    ∀ x : List Bool, x.length = n + 2 → x.getD (n + 1) false = true →
      (run r.1 x).getD r.2 false = ws.all (fun w => (run gs x).getD w false) := by
  induction ws with
  | nil =>
    refine ⟨⟨[], by simp [addAndList]⟩, hctx, by simp [addAndList]; omega, rfl, ?_⟩
    intro x hlen htrue
    dsimp only [addAndList]
    rw [run_input gs x (n + 1) (by omega), htrue]; simp
  | cons w ws ih =>
    have hw : w < n + 2 + gs.length := hws w List.mem_cons_self
    have hws' : ∀ u ∈ ws, u < n + 2 + gs.length := fun u hu => hws u (List.mem_cons_of_mem _ hu)
    obtain ⟨⟨ext, hext⟩, hctx1, hw1, hnot1, hev1⟩ := ih hws'
    set r1 := addAndList n gs ws
    have hlen1 : gs.length ≤ r1.1.length := by rw [hext, List.length_append]; omega
    refine ⟨⟨ext ++ [⟨.and, [w, r1.2]⟩], by simp [addAndList, addAnd, hext, r1, List.append_assoc]⟩, ?_, ?_, ?_, ?_⟩
    · exact ctx_snoc n r1.1 ⟨.and, [w, r1.2]⟩ hctx1 ⟨Or.inl rfl, by simp⟩ (by
        intro u hu; simp at hu; rcases hu with rfl | rfl <;> omega)
    · simp only [addAndList, addAnd, r1, List.length_append, List.length_singleton]; omega
    · dsimp only [addAndList, addAnd, r1]
      rw [notCount_snoc]; simpa using hnot1
    · intro x hlen htrue
      dsimp only [addAndList, addAnd, r1]
      rw [run_snoc]
      have hrlen : (run r1.1 x).length = n + 2 + r1.1.length := by rw [run_length, hlen]
      rw [← hrlen, getD_eq, andEval]
      simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
      have hpref_w : (run r1.1 x).getD w false = (run gs x).getD w false := by
        rw [hext]; exact run_prefix gs ext x w (by omega)
      rw [hpref_w, hev1 x hlen htrue]

private theorem addOrList_spec (n : ℕ) (gs : List Gate) (ws : List ℕ)
    (hctx : Ctx n gs) (hws : ∀ w ∈ ws, w < n + 2 + gs.length) :
    let r := addOrList n gs ws
    (∃ ext, r.1 = gs ++ ext) ∧
    Ctx n r.1 ∧
    r.2 < n + 2 + r.1.length ∧
    PEqualNP.NotBracket.notCount ⟨r.1, 0⟩ = PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ∧
    ∀ x : List Bool, x.length = n + 2 → x.getD n false = false →
      (run r.1 x).getD r.2 false = ws.any (fun w => (run gs x).getD w false) := by
  induction ws with
  | nil =>
    refine ⟨⟨[], by simp [addOrList]⟩, hctx, by simp [addOrList]; omega, rfl, ?_⟩
    intro x hlen hfalse
    dsimp only [addOrList]
    rw [run_input gs x n (by omega), hfalse]; simp
  | cons w ws ih =>
    have hw : w < n + 2 + gs.length := hws w List.mem_cons_self
    have hws' : ∀ u ∈ ws, u < n + 2 + gs.length := fun u hu => hws u (List.mem_cons_of_mem _ hu)
    obtain ⟨⟨ext, hext⟩, hctx1, hw1, hnot1, hev1⟩ := ih hws'
    set r1 := addOrList n gs ws
    have hlen1 : gs.length ≤ r1.1.length := by rw [hext, List.length_append]; omega
    refine ⟨⟨ext ++ [⟨.or, [w, r1.2]⟩], by simp [addOrList, addOr, hext, r1, List.append_assoc]⟩, ?_, ?_, ?_, ?_⟩
    · exact ctx_snoc n r1.1 ⟨.or, [w, r1.2]⟩ hctx1 ⟨Or.inr (Or.inl rfl), by simp⟩ (by
        intro u hu; simp at hu; rcases hu with rfl | rfl <;> omega)
    · simp only [addOrList, addOr, r1, List.length_append, List.length_singleton]; omega
    · dsimp only [addOrList, addOr, r1]
      rw [notCount_snoc]; simpa using hnot1
    · intro x hlen hfalse
      dsimp only [addOrList, addOr, r1]
      rw [run_snoc]
      have hrlen : (run r1.1 x).length = n + 2 + r1.1.length := by rw [run_length, hlen]
      rw [← hrlen, getD_eq, orEval]
      simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
      have hpref_w : (run r1.1 x).getD w false = (run gs x).getD w false := by
        rw [hext]; exact run_prefix gs ext x w (by omega)
      rw [hpref_w, hev1 x hlen hfalse]

-- Dual-rail layered antichain for Part 2
private def layerX (t k : ℕ) (z : Fin k × Finset (Fin t)) : Finset (Fin (2 * t * k)) :=
  Finset.univ.filter fun p : Fin (2 * t * k) =>
    p.val < 2 * t * z.1.val ∨
    (2 * t * z.1.val ≤ p.val ∧ p.val < 2 * t * (z.1.val + 1) ∧
      ∃ a : Fin t, (p.val = 2 * t * z.1.val + 2 * a.val ∧ a ∈ z.2) ∨
                   (p.val = 2 * t * z.1.val + 2 * a.val + 1 ∧ a ∉ z.2))

private theorem layerX_sub_iff (t k : ℕ) (ht : 1 ≤ t) (z z' : Fin k × Finset (Fin t)) :
    layerX t k z ⊆ layerX t k z' ↔ z.1 < z'.1 ∨ z = z' := by
  constructor
  · intro hsub
    by_cases hlt : z.1 < z'.1
    · exact Or.inl hlt
    · by_cases heq1 : z.1 = z'.1
      · right
        apply Prod.ext heq1
        ext a
        constructor
        · intro ha
          let p : Fin (2 * t * k) := ⟨2 * t * z.1.val + 2 * a.val, by
            have h1 : 2 * t * (z.1.val + 1) ≤ 2 * t * k := Nat.mul_le_mul_left (2 * t) (by omega)
            have h2 : 2 * t * (z.1.val + 1) = 2 * t * z.1.val + 2 * t := by ring
            omega⟩
          have hpz : p ∈ layerX t k z := by
            have h2 : 2 * t * (z.1.val + 1) = 2 * t * z.1.val + 2 * t := by ring
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ p, Or.inr ⟨by dsimp [p]; omega, by dsimp [p]; omega, a, Or.inl ⟨rfl, ha⟩⟩⟩
          have hpz' := (Finset.mem_filter.mp (hsub hpz)).2
          rcases hpz' with h1 | ⟨_, _, a', ha'⟩
          · dsimp [p] at h1; rw [heq1] at h1; omega
          · rcases ha' with ⟨he, hm⟩ | ⟨he, _⟩
            · dsimp [p] at he; rw [heq1] at he
              have : a = a' := Fin.ext (by omega)
              rwa [this]
            · dsimp [p] at he; rw [heq1] at he; omega
        · intro ha
          by_contra hna
          let p : Fin (2 * t * k) := ⟨2 * t * z.1.val + 2 * a.val + 1, by
            have h1 : 2 * t * (z.1.val + 1) ≤ 2 * t * k := Nat.mul_le_mul_left (2 * t) (by omega)
            have h2 : 2 * t * (z.1.val + 1) = 2 * t * z.1.val + 2 * t := by ring
            omega⟩
          have hpz : p ∈ layerX t k z := by
            have h2 : 2 * t * (z.1.val + 1) = 2 * t * z.1.val + 2 * t := by ring
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ p, Or.inr ⟨by dsimp [p]; omega, by dsimp [p]; omega, a, Or.inr ⟨rfl, hna⟩⟩⟩
          have hpz' := (Finset.mem_filter.mp (hsub hpz)).2
          rcases hpz' with h1 | ⟨_, _, a', ha'⟩
          · dsimp [p] at h1; rw [heq1] at h1; omega
          · rcases ha' with ⟨he, _⟩ | ⟨he, hna'⟩
            · dsimp [p] at he; rw [heq1] at he; omega
            · dsimp [p] at he; rw [heq1] at he
              have : a = a' := Fin.ext (by omega)
              exact hna' (this ▸ ha)
      · exfalso
        have hgt : z'.1.val < z.1.val := by
          have : z.1.val ≠ z'.1.val := fun h => heq1 (Fin.ext h)
          have : ¬ (z.1.val < z'.1.val) := hlt
          omega
        let a0 : Fin t := ⟨0, by omega⟩
        have h2z : 2 * t * (z.1.val + 1) = 2 * t * z.1.val + 2 * t := by ring
        have h2z' : 2 * t * (z'.1.val + 1) = 2 * t * z'.1.val + 2 * t := by ring
        have hbound : 2 * t * z.1.val + 1 < 2 * t * k := by
          have h1 : 2 * t * (z.1.val + 1) ≤ 2 * t * k := Nat.mul_le_mul_left (2 * t) (by omega)
          omega
        by_cases ha0 : a0 ∈ z.2
        · let p : Fin (2 * t * k) := ⟨2 * t * z.1.val, by omega⟩
          have hpz : p ∈ layerX t k z :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ p, Or.inr ⟨by dsimp [p]; omega, by dsimp [p]; omega, a0, Or.inl ⟨by simp [p, a0], ha0⟩⟩⟩
          have hpz' := (Finset.mem_filter.mp (hsub hpz)).2
          have hmul : 2 * t * (z'.1.val + 1) ≤ 2 * t * z.1.val := Nat.mul_le_mul_left (2 * t) (by omega)
          rcases hpz' with h1 | ⟨_, h2, _⟩ <;> dsimp [p] at * <;> omega
        · let p : Fin (2 * t * k) := ⟨2 * t * z.1.val + 1, hbound⟩
          have hpz : p ∈ layerX t k z :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ p, Or.inr ⟨by dsimp [p]; omega, by dsimp [p]; omega, a0, Or.inr ⟨by simp [p, a0], ha0⟩⟩⟩
          have hpz' := (Finset.mem_filter.mp (hsub hpz)).2
          have hmul : 2 * t * (z'.1.val + 1) ≤ 2 * t * z.1.val := Nat.mul_le_mul_left (2 * t) (by omega)
          rcases hpz' with h1 | ⟨_, h2, _⟩ <;> dsimp [p] at * <;> omega
  · rintro (hlt | rfl)
    · intro p hp
      have hp' := (Finset.mem_filter.mp hp).2
      have hmul : 2 * t * (z.1.val + 1) ≤ 2 * t * z'.1.val := Nat.mul_le_mul_left (2 * t) (by omega)
      have h2z : 2 * t * (z.1.val + 1) = 2 * t * z.1.val + 2 * t := by ring
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ p, Or.inl ?_⟩
      rcases hp' with h1 | ⟨_, h2, _⟩ <;> omega
    · exact Finset.Subset.refl _

private theorem layerX_inj (t k : ℕ) (ht : 1 ≤ t) : Function.Injective (layerX t k) := by
  intro z1 z2 h
  have h1 := (layerX_sub_iff t k ht z1 z2).mp (h ▸ Finset.Subset.refl _)
  have h2 := (layerX_sub_iff t k ht z2 z1).mp (h.symm ▸ Finset.Subset.refl _)
  rcases h1 with hlt1 | rfl
  · rcases h2 with hlt2 | heq
    · exact absurd (lt_trans hlt1 hlt2) (lt_irrefl _)
    · exact heq.symm
  · rfl

private theorem layerX_mem_even (t k : ℕ) (z : Fin k × Finset (Fin t)) (j : ℕ) (hj : j < k) (a : Fin t) :
    (⟨2 * t * j + 2 * a.val, by
        have h1 : 2 * t * (j + 1) ≤ 2 * t * k := Nat.mul_le_mul_left (2 * t) (by omega)
        have h2 : 2 * t * (j + 1) = 2 * t * j + 2 * t := by ring
        omega⟩ : Fin (2 * t * k)) ∈ layerX t k z ↔ j < z.1.val ∨ (j = z.1.val ∧ a ∈ z.2) := by
  have h2j : 2 * t * (j + 1) = 2 * t * j + 2 * t := by ring
  have h2z : 2 * t * (z.1.val + 1) = 2 * t * z.1.val + 2 * t := by ring
  simp only [layerX, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (h1 | ⟨h1, h2, a', ha'⟩)
    · left
      by_contra hge
      have hmul : 2 * t * z.1.val ≤ 2 * t * j := Nat.mul_le_mul_left (2 * t) (by omega)
      omega
    · right
      have hjeq : j = z.1.val := by
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
        · have := Nat.mul_le_mul_left (2 * t) (show j + 1 ≤ z.1.val by omega); omega
        · have := Nat.mul_le_mul_left (2 * t) (show z.1.val + 1 ≤ j by omega); omega
      subst hjeq
      refine ⟨rfl, ?_⟩
      rcases ha' with ⟨he, hm⟩ | ⟨he, _⟩
      · have : a = a' := Fin.ext (by omega); rwa [this]
      · omega
  · rintro (hlt | ⟨rfl, ha⟩)
    · left
      have hmul : 2 * t * (j + 1) ≤ 2 * t * z.1.val := Nat.mul_le_mul_left (2 * t) (by omega)
      omega
    · right
      exact ⟨by omega, by omega, a, Or.inl ⟨rfl, ha⟩⟩

private theorem layerX_mem_odd (t k : ℕ) (z : Fin k × Finset (Fin t)) (j : ℕ) (hj : j < k) (a : Fin t) :
    (⟨2 * t * j + 2 * a.val + 1, by
        have h1 : 2 * t * (j + 1) ≤ 2 * t * k := Nat.mul_le_mul_left (2 * t) (by omega)
        have h2 : 2 * t * (j + 1) = 2 * t * j + 2 * t := by ring
        omega⟩ : Fin (2 * t * k)) ∈ layerX t k z ↔ j < z.1.val ∨ (j = z.1.val ∧ a ∉ z.2) := by
  have h2j : 2 * t * (j + 1) = 2 * t * j + 2 * t := by ring
  have h2z : 2 * t * (z.1.val + 1) = 2 * t * z.1.val + 2 * t := by ring
  simp only [layerX, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (h1 | ⟨h1, h2, a', ha'⟩)
    · left
      by_contra hge
      have hmul : 2 * t * z.1.val ≤ 2 * t * j := Nat.mul_le_mul_left (2 * t) (by omega)
      omega
    · right
      have hjeq : j = z.1.val := by
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
        · have := Nat.mul_le_mul_left (2 * t) (show j + 1 ≤ z.1.val by omega); omega
        · have := Nat.mul_le_mul_left (2 * t) (show z.1.val + 1 ≤ j by omega); omega
      subst hjeq
      refine ⟨rfl, ?_⟩
      rcases ha' with ⟨he, _⟩ | ⟨he, hna⟩
      · omega
      · have : a = a' := Fin.ext (by omega); rwa [this]
  · rintro (hlt | ⟨rfl, hna⟩)
    · left
      have hmul : 2 * t * (j + 1) ≤ 2 * t * z.1.val := Nat.mul_le_mul_left (2 * t) (by omega)
      omega
    · right
      exact ⟨by omega, by omega, a, Or.inr ⟨rfl, hna⟩⟩

private def mintermWires (t : ℕ) (j : ℕ) (S : Finset (Fin t)) : List ℕ :=
  List.ofFn fun a : Fin t => if a ∈ S then 2 * t * j + 2 * a.val else 2 * t * j + 2 * a.val + 1

private theorem mintermWires_eval (t k : ℕ) (ht : 1 ≤ t) (gs : List Gate) (j : ℕ) (hj : j < k)
    (S : Finset (Fin t)) (z : Fin k × Finset (Fin t)) :
    let inp := List.ofFn (fun p : Fin (2 * t * k) => decide (p ∈ layerX t k z)) ++ [false, true]
    (mintermWires t j S).all (fun w => (run gs inp).getD w false) =
      decide (j < z.1.val ∨ (j = z.1.val ∧ z.2 = S)) := by
  intro inp
  have hinp_len : inp.length = 2 * t * k + 2 := by simp [inp]
  have hget : ∀ a : Fin t,
      (run gs inp).getD (if a ∈ S then 2 * t * j + 2 * a.val else 2 * t * j + 2 * a.val + 1) false =
      decide (j < z.1.val ∨ (j = z.1.val ∧ (a ∈ z.2 ↔ a ∈ S))) := by
    intro a
    have hmul : 2 * t * (j + 1) ≤ 2 * t * k := Nat.mul_le_mul_left (2 * t) (by omega)
    have h2j : 2 * t * (j + 1) = 2 * t * j + 2 * t := by ring
    by_cases ha : a ∈ S
    · rw [if_pos ha]
      have hwlt : 2 * t * j + 2 * a.val < 2 * t * k := by omega
      rw [run_input gs inp _ (by omega)]
      dsimp only [inp]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hwlt]), List.getElem?_ofFn]
      simp only [hwlt, ↓reduceDIte, Option.getD_some, decide_eq_decide]
      rw [layerX_mem_even t k z j hj a]
      simp [ha]
    · rw [if_neg ha]
      have hwlt : 2 * t * j + 2 * a.val + 1 < 2 * t * k := by omega
      rw [run_input gs inp _ (by omega)]
      dsimp only [inp]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hwlt]), List.getElem?_ofFn]
      simp only [hwlt, ↓reduceDIte, Option.getD_some, decide_eq_decide]
      rw [layerX_mem_odd t k z j hj a]
      simp [ha]
  apply Bool.eq_iff_iff.mpr
  rw [List.all_eq_true, decide_eq_true_iff]
  simp only [mintermWires, List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff, hget, decide_eq_true_iff]
  constructor
  · intro hall
    by_cases hlt : j < z.1.val
    · exact Or.inl hlt
    · right
      have a0 : Fin t := ⟨0, by omega⟩
      have h0 := hall a0
      rcases h0 with h | ⟨hjeq, _⟩
      · exact absurd h hlt
      · refine ⟨hjeq, ?_⟩
        ext a
        rcases hall a with h | ⟨_, hiff⟩
        · exact absurd h hlt
        · exact hiff
  · rintro (hlt | ⟨rfl, rfl⟩) a
    · exact Or.inl hlt
    · exact Or.inr ⟨rfl, Iff.rfl⟩

private theorem le_of_testBit_imp (d top m : ℕ) (htop : top < 2 ^ d) (hm : m < 2 ^ d)
    (himp : ∀ i : Fin d, m.testBit (d - 1 - i.val) = false → top.testBit (d - 1 - i.val) = false) :
    top ≤ m := by
  by_contra hgt
  have hlt : m < top := by omega
  have hsum : ∀ x < 2 ^ d, (∑ i : Fin d, if x.testBit (d - 1 - i.val) = true then 2 ^ (d - 1 - i.val) else 0) = x := by
    intro x hx
    clear htop hm himp hgt hlt top m
    induction d generalizing x with
    | zero => simp at hx; subst hx; simp
    | succ d ih =>
      rw [Fin.sum_univ_succ]
      have hsub : ∀ i : Fin d, d + 1 - 1 - i.succ.val = d - 1 - i.val := fun i => by simp [Fin.val_succ]; omega
      simp only [hsub]
      simp only [Fin.val_zero, Nat.add_sub_cancel, Nat.sub_zero]
      have hmod : x % 2 ^ d < 2 ^ d := Nat.mod_lt x (Nat.pow_pos (by omega))
      have htb_mod : ∀ i : Fin d, x.testBit (d - 1 - i.val) = (x % 2 ^ d).testBit (d - 1 - i.val) := fun i => by
        rw [Nat.testBit_mod_two_pow]; simp [show d - 1 - i.val < d by omega]
      simp only [htb_mod]
      rw [ih (x % 2 ^ d) hmod]
      have hdiv : x / 2 ^ d < 2 :=
        Nat.div_lt_of_lt_mul (by rw [← Nat.pow_succ]; exact hx)
      have h01 : x / 2 ^ d = 0 ∨ x / 2 ^ d = 1 := by
        cases h : x / 2 ^ d with
        | zero => exact Or.inl rfl
        | succ k =>
          cases k with
          | zero => exact Or.inr rfl
          | succ k' => rw [h] at hdiv; omega
      have htop_bit : x.testBit d = decide (x / 2 ^ d = 1) := by
        rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
        rcases h01 with h0 | h1
        · rw [h0]; rfl
        · rw [h1]; rfl
      rw [htop_bit]
      have hdm := Nat.div_add_mod x (2 ^ d)
      rcases h01 with h0 | h1
      · rw [h0] at hdm ⊢; simp at hdm ⊢; omega
      · rw [h1] at hdm ⊢; simp at hdm ⊢; omega
  rw [← hsum m hm, ← hsum top htop] at hlt
  obtain ⟨r, _, hmr, htr⟩ := binary_lt_first_diff d
    (fun i => m.testBit (d - 1 - i.val)) (fun i => top.testBit (d - 1 - i.val)) hlt
  have := himp r hmr
  rw [htr] at this; cases this

private theorem eq_of_testBit_eq (b x y : ℕ) (hx : x < 2 ^ b) (hy : y < 2 ^ b)
    (heq : ∀ i : Fin b, x.testBit (b - 1 - i.val) = y.testBit (b - 1 - i.val)) :
    x = y := by
  have h1 := le_of_testBit_imp b x y hx hy (fun i hi => by rw [heq i, hi])
  have h2 := le_of_testBit_imp b y x hy hx (fun i hi => by rw [← heq i, hi])
  omega

private def phaseQ (t k : ℕ) (z : Fin k × Finset (Fin t)) : ℕ :=
  if z.1.val % (t + 1) = t ∧ z.2 = Finset.univ then z.1.val / (t + 1) + 1 else z.1.val / (t + 1)

private theorem phaseQ_lt (t k b : ℕ) (hk : k < (t + 1) * 2 ^ b) (z : Fin k × Finset (Fin t)) :
    phaseQ t k z < 2 ^ b := by
  dsimp only [phaseQ]
  have hdm := Nat.div_add_mod z.1.val (t + 1)
  have hlt : z.1.val < (t + 1) * 2 ^ b := lt_trans z.1.isLt hk
  have hdiv_lt : z.1.val / (t + 1) < 2 ^ b := Nat.div_lt_of_lt_mul hlt
  split_ifs with h
  · by_contra hge
    have heq : z.1.val / (t + 1) + 1 = 2 ^ b := by omega
    have h1 : (t + 1) * 2 ^ b = (t + 1) * (z.1.val / (t + 1)) + (t + 1) := by rw [← heq, Nat.mul_add, Nat.mul_one]
    have h2 : z.1.val = (t + 1) * (z.1.val / (t + 1)) + t := by omega
    omega
  · exact hdiv_lt

private theorem phaseQ_le_iff (t k : ℕ) (z : Fin k × Finset (Fin t)) (q : ℕ) (hq : 1 ≤ q) :
    q ≤ phaseQ t k z ↔ q * (t + 1) - 1 < z.1.val ∨ (q * (t + 1) - 1 = z.1.val ∧ z.2 = Finset.univ) := by
  dsimp only [phaseQ]
  have hdm := Nat.div_add_mod z.1.val (t + 1)
  have hmod : z.1.val % (t + 1) < t + 1 := Nat.mod_lt _ (by omega)
  have hqmul : q * (t + 1) = (q - 1) * (t + 1) + (t + 1) := by
    have hq1 : q = (q - 1) + 1 := by omega
    conv_lhs => rw [hq1]
    ring
  have hsub1 : q * (t + 1) - 1 = (q - 1) * (t + 1) + t := by omega
  rw [hsub1]
  split_ifs with h
  · have hzval : z.1.val = (z.1.val / (t + 1)) * (t + 1) + t := by rw [Nat.mul_comm]; omega
    constructor
    · intro hle
      rcases Nat.lt_or_eq_of_le hle with hlt | heq
      · left
        have : (q - 1) + 1 ≤ z.1.val / (t + 1) := by omega
        have := Nat.mul_le_mul_right (t + 1) this
        nlinarith
      · right; refine ⟨?_, h.2⟩
        have : q - 1 = z.1.val / (t + 1) := by omega
        rw [this, ← hzval]
    · rintro (hlt | ⟨heq, _⟩)
      · by_contra hgt
        have : z.1.val / (t + 1) ≤ q - 1 := by omega
        have := Nat.mul_le_mul_right (t + 1) this
        nlinarith
      · have h1 : (q - 1) * (t + 1) = (z.1.val / (t + 1)) * (t + 1) := by omega
        have h2 : q - 1 = z.1.val / (t + 1) := Nat.eq_of_mul_eq_mul_right (by omega) h1
        omega
  · constructor
    · intro hle
      left
      have hq_le : q * (t + 1) ≤ (z.1.val / (t + 1)) * (t + 1) := Nat.mul_le_mul_right (t + 1) hle
      rw [Nat.mul_comm] at hdm
      omega
    · rintro (hlt | ⟨heq, huniv⟩)
      · by_contra hgt
        have : z.1.val / (t + 1) ≤ q - 1 := by omega
        have h1 := Nat.mul_le_mul_right (t + 1) this
        rw [Nat.mul_comm] at hdm
        nlinarith
      · exfalso
        have hrem : z.1.val % (t + 1) = t := by
          rw [← heq, Nat.mul_comm (q - 1), Nat.mul_add_mod]; exact Nat.mod_eq_of_lt (by omega)
        exact h ⟨hrem, huniv⟩

private def buildMinterm (n t k : ℕ) (gs : List Gate) (j : ℕ) (S : Finset (Fin t)) : List Gate × ℕ :=
  if j < k then addAndList n gs (mintermWires t j S) else (gs, n)

private theorem buildMinterm_spec (t k : ℕ) (ht : 1 ≤ t) (gs : List Gate) (hctx : Ctx (2 * t * k) gs)
    (j : ℕ) (S : Finset (Fin t)) :
    let n := 2 * t * k
    let r := buildMinterm n t k gs j S
    (∃ ext, r.1 = gs ++ ext) ∧
    Ctx n r.1 ∧
    r.2 < n + 2 + r.1.length ∧
    PEqualNP.NotBracket.notCount ⟨r.1, 0⟩ = PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ∧
    ∀ z : Fin k × Finset (Fin t),
      let inp := List.ofFn (fun p : Fin n => decide (p ∈ layerX t k z)) ++ [false, true]
      (run r.1 inp).getD r.2 false = decide (j < z.1.val ∨ (j = z.1.val ∧ z.2 = S)) := by
  intro n
  dsimp only [buildMinterm]
  by_cases hj : j < k
  · rw [if_pos hj]
    have hws : ∀ w ∈ mintermWires t j S, w < n + 2 + gs.length := by
      intro w hw
      simp only [mintermWires, List.mem_ofFn] at hw
      obtain ⟨a, rfl⟩ := hw
      have hmul : 2 * t * (j + 1) ≤ 2 * t * k := Nat.mul_le_mul_left (2 * t) (by omega)
      have h2j : 2 * t * (j + 1) = 2 * t * j + 2 * t := by ring
      split_ifs <;> dsimp only [n] <;> omega
    obtain ⟨hext, hctx1, hw1, hnot1, hev1⟩ := addAndList_spec n gs (mintermWires t j S) hctx hws
    refine ⟨hext, hctx1, hw1, hnot1, ?_⟩
    intro z
    let inp := List.ofFn (fun p : Fin n => decide (p ∈ layerX t k z)) ++ [false, true]
    have hinp_len : inp.length = n + 2 := by simp [inp]
    have htrue : inp.getD (n + 1) false = true := by
      dsimp only [inp]; rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]; simp
    exact (hev1 inp hinp_len htrue).trans (mintermWires_eval t k ht gs j hj S z)
  · rw [if_neg hj]
    refine ⟨⟨[], by simp⟩, hctx, by omega, rfl, ?_⟩
    intro z
    dsimp only
    let inp := List.ofFn (fun p : Fin n => decide (p ∈ layerX t k z)) ++ [false, true]
    have hinp_len : inp.length = n + 2 := by simp [inp]
    have hfalse : inp.getD n false = false := by
      dsimp only [inp]; rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]; simp
    change (run gs inp).getD n false = _
    rw [run_input gs inp n (by omega), hfalse]
    have hnz : ¬ (j < z.1.val ∨ (j = z.1.val ∧ z.2 = S)) := by
      rintro (h | ⟨h, _⟩) <;> omega
    exact (decide_eq_false hnz).symm

-- Build a list of trigger wires for q = 0 .. M-1
private def buildTrigs (t k : ℕ) : ℕ → List Gate → List Gate × List ℕ
  | 0, gs => (gs, [])
  | m + 1, gs =>
    let r1 := buildTrigs t k m gs
    if m = 0 then (r1.1, r1.2 ++ [2 * t * k + 1])
    else
      let r2 := buildMinterm (2 * t * k) t k r1.1 (m * (t + 1) - 1) Finset.univ
      (r2.1, r1.2 ++ [r2.2])

private theorem buildTrigs_spec (t k : ℕ) (ht : 1 ≤ t) (M : ℕ) (gs : List Gate) (hctx : Ctx (2 * t * k) gs) :
    let n := 2 * t * k
    let r := buildTrigs t k M gs
    (∃ ext, r.1 = gs ++ ext) ∧
    Ctx n r.1 ∧
    r.2.length = M ∧
    (∀ w ∈ r.2, w < n + 2 + r.1.length) ∧
    PEqualNP.NotBracket.notCount ⟨r.1, 0⟩ = PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ∧
    ∀ q (hq : q < M) (z : Fin k × Finset (Fin t)),
      let inp := List.ofFn (fun p : Fin n => decide (p ∈ layerX t k z)) ++ [false, true]
      (run r.1 inp).getD (r.2.getD q 0) false = decide (q ≤ phaseQ t k z) := by
  intro n
  induction M with
  | zero =>
    exact ⟨⟨[], by simp [buildTrigs]⟩, hctx, rfl, by simp [buildTrigs], rfl, fun q hq => by omega⟩
  | succ m ih =>
    obtain ⟨⟨ext1, hext1⟩, hctx1, hlen1, hw1, hnot1, hev1⟩ := ih
    set r1 := buildTrigs t k m gs
    dsimp only [buildTrigs]
    by_cases hm0 : m = 0
    · rw [if_pos hm0]
      refine ⟨⟨ext1, hext1⟩, hctx1, by simp [r1, hlen1], ?_, hnot1, ?_⟩
      · intro w hw
        rcases List.mem_append.mp hw with h | h
        · exact hw1 w h
        · rw [List.mem_singleton.mp h]; dsimp only [n]; omega
      · intro q hq z
        dsimp only
        let inp := List.ofFn (fun p : Fin n => decide (p ∈ layerX t k z)) ++ [false, true]
        have hq0 : q = 0 := by omega
        subst hq0
        have hlen0 : r1.2.length = 0 := by omega
        have hr1_nil : r1.2 = [] := List.eq_nil_of_length_eq_zero hlen0
        change (run r1.1 inp).getD ((r1.2 ++ [2 * t * k + 1]).getD 0 0) false = _
        simp only [hr1_nil, List.nil_append, List.getD_cons_zero]
        have hinp_len : inp.length = n + 2 := by simp [inp]
        have htrue : inp.getD (n + 1) false = true := by
          dsimp only [inp]; rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]; simp
        rw [run_input r1.1 inp (n + 1) (by omega), htrue]; simp
    · rw [if_neg hm0]
      obtain ⟨⟨ext2, hext2⟩, hctx2, hw2, hnot2, hev2⟩ := buildMinterm_spec t k ht r1.1 hctx1 (m * (t + 1) - 1) Finset.univ
      set r2 := buildMinterm n t k r1.1 (m * (t + 1) - 1) Finset.univ
      have hlen12 : r1.1.length ≤ r2.1.length := by rw [hext2, List.length_append]; omega
      refine ⟨⟨ext1 ++ ext2, by rw [hext2, hext1, List.append_assoc]⟩, hctx2,
        by simp [r1, hlen1], ?_, by rw [hnot2, hnot1], ?_⟩
      · intro w hw
        rcases List.mem_append.mp hw with h | h
        · have := hw1 w h; dsimp only [n] at *; omega
        · rw [List.mem_singleton.mp h]; exact hw2
      · intro q hq z
        dsimp only
        let inp := List.ofFn (fun p : Fin n => decide (p ∈ layerX t k z)) ++ [false, true]
        change (run r2.1 inp).getD ((r1.2 ++ [r2.2]).getD q 0) false = _
        by_cases hqm : q < m
        · have hget : (r1.2 ++ [r2.2]).getD q 0 = r1.2.getD q 0 := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
          rw [hget]
          have hmem : r1.2.getD q 0 ∈ r1.2 := by
            rw [List.getD_eq_getElem r1.2 0 (by omega)]; exact List.getElem_mem (by omega)
          have hlt := hw1 _ hmem
          have hpref : (run r2.1 inp).getD (r1.2.getD q 0) false = (run r1.1 inp).getD (r1.2.getD q 0) false := by
            rw [hext2]; exact run_prefix r1.1 ext2 inp _ (by dsimp only [n] at hlt; simp only [inp, List.length_append, List.length_ofFn, List.length_cons, List.length_nil]; omega)
          rw [hpref]
          exact hev1 q hqm z
        · have hqeq : q = m := by omega
          subst hqeq
          have hget : (r1.2 ++ [r2.2]).getD q 0 = r2.2 := by
            rw [← hlen1, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]; simp
          rw [hget, hev2 z]
          exact decide_eq_decide.mpr (phaseQ_le_iff t k z q (by omega)).symm

-- Stage 2: build binary encoding of phaseQ using exactly d NOT gates (for d = 0 .. b)
private def buildBits (n b : ℕ) (trigs : List ℕ) : ℕ → List Gate → List Gate × List ℕ × List ℕ
  | 0, gs => (gs, [], [])
  | d + 1, gs =>
    let r1 := buildBits n b trigs d gs
    let gs1 := r1.1
    let pos1 := r1.2.1
    let neg1 := r1.2.2
    -- Build terms for m = 0 .. 2^d - 1
    let termsRes := (List.range (2 ^ d)).foldl
      (fun (acc : List Gate × List ℕ) (m : ℕ) =>
        let th := m * 2 ^ (b - d) + 2 ^ (b - 1 - d)
        let trigW := trigs.getD th n
        let negWs := (List.range d).map fun i =>
          if m.testBit (d - 1 - i) = false then neg1.getD i n else n + 1
        let rAnd := addAndList n acc.1 (trigW :: negWs)
        (rAnd.1, acc.2 ++ [rAnd.2]))
      (gs1, [])
    let rOr := addOrList n termsRes.1 termsRes.2
    let rNot := addNot n rOr.1 rOr.2
    (rNot.1, pos1 ++ [rOr.2], neg1 ++ [rNot.2])

set_option maxHeartbeats 800000 in
private theorem buildBits_spec (t k b : ℕ) (hk : k < (t + 1) * 2 ^ b)
    (gs0 : List Gate) (trigs : List ℕ)
    (hctx0 : Ctx (2 * t * k) gs0)
    (htrigs_len : trigs.length = 2 ^ b)
    (htrigs_lt : ∀ w ∈ trigs, w < 2 * t * k + 2 + gs0.length)
    (htrigs_eval : ∀ q < 2 ^ b, ∀ z : Fin k × Finset (Fin t),
      let inp := List.ofFn (fun p : Fin (2 * t * k) => decide (p ∈ layerX t k z)) ++ [false, true]
      (run gs0 inp).getD (trigs.getD q 0) false = decide (q ≤ phaseQ t k z))
    (d : ℕ) (hd : d ≤ b) :
    let n := 2 * t * k
    let r := buildBits n b trigs d gs0
    (∃ ext, r.1 = gs0 ++ ext) ∧
    Ctx n r.1 ∧
    r.2.1.length = d ∧ r.2.2.length = d ∧
    (∀ w ∈ r.2.1, w < n + 2 + r.1.length) ∧
    (∀ w ∈ r.2.2, w < n + 2 + r.1.length) ∧
    PEqualNP.NotBracket.notCount ⟨r.1, 0⟩ = PEqualNP.NotBracket.notCount ⟨gs0, 0⟩ + d ∧
    (∀ i < d, ∀ z : Fin k × Finset (Fin t),
      let inp := List.ofFn (fun p : Fin n => decide (p ∈ layerX t k z)) ++ [false, true]
      (run r.1 inp).getD (r.2.1.getD i 0) false = (phaseQ t k z).testBit (b - 1 - i) ∧
      (run r.1 inp).getD (r.2.2.getD i 0) false = !((phaseQ t k z).testBit (b - 1 - i))) := by
  intro n
  induction d with
  | zero =>
    refine ⟨⟨[], by simp [buildBits]⟩, hctx0, rfl, rfl, by simp [buildBits], by simp [buildBits], by simp [buildBits], ?_⟩
    intro i hi; omega
  | succ d ih =>
    obtain ⟨⟨ext1, hext1⟩, hctx1, hplen1, hnlen1, hplt1, hnlt1, hnot1, hev1⟩ := ih (by omega)
    set r1 := buildBits n b trigs d gs0
    set gs1 := r1.1
    set pos1 := r1.2.1
    set neg1 := r1.2.2
    have hgs01 : gs0.length ≤ gs1.length := by rw [hext1, List.length_append]; omega
    let mkTerm : ℕ → List ℕ := fun m =>
      let th := m * 2 ^ (b - d) + 2 ^ (b - 1 - d)
      let trigW := trigs.getD th n
      let negWs := (List.range d).map fun i =>
        if m.testBit (d - 1 - i) = false then neg1.getD i n else n + 1
      trigW :: negWs
    have hth_lt : ∀ m < 2 ^ d, m * 2 ^ (b - d) + 2 ^ (b - 1 - d) < 2 ^ b := by
      intro m hm
      have h1 : 2 ^ (b - d) = 2 * 2 ^ (b - 1 - d) := by
        have he : b - d = (b - 1 - d) + 1 := by omega
        rw [he, Nat.pow_succ, Nat.mul_comm]
      have h2 : 2 ^ d * 2 ^ (b - d) = 2 ^ b := by
        rw [← Nat.pow_add, Nat.add_sub_of_le (by omega)]
      have h3 : (m + 1) * 2 ^ (b - d) ≤ 2 ^ d * 2 ^ (b - d) := Nat.mul_le_mul_right _ (by omega)
      have hp : 0 < 2 ^ (b - 1 - d) := Nat.pow_pos (by omega)
      nlinarith
    have hmk_lt : ∀ m < 2 ^ d, ∀ w ∈ mkTerm m, w < n + 2 + gs1.length := by
      intro m hm w hw
      simp only [mkTerm, List.mem_cons, List.mem_map, List.mem_range] at hw
      rcases hw with rfl | ⟨i, hi, rfl⟩
      · have hth := hth_lt m hm
        have hmem : trigs.getD (m * 2 ^ (b - d) + 2 ^ (b - 1 - d)) n ∈ trigs := by
          rw [List.getD_eq_getElem trigs n (by omega)]; exact List.getElem_mem (by omega)
        have := htrigs_lt _ hmem; omega
      · split_ifs
        · have hmem : neg1.getD i n ∈ neg1 := by
            rw [List.getD_eq_getElem neg1 n (by omega)]; exact List.getElem_mem (by omega)
          exact hnlt1 _ hmem
        · omega
    have hmk_eval : ∀ m < 2 ^ d, ∀ z : Fin k × Finset (Fin t),
        let inp := List.ofFn (fun p : Fin n => decide (p ∈ layerX t k z)) ++ [false, true]
        (mkTerm m).all (fun w => (run gs1 inp).getD w false) =
          decide (m = phaseQ t k z / 2 ^ (b - d) ∧ (phaseQ t k z).testBit (b - 1 - d) = true) := by
      intro m hm z inp
      have hinp_len : inp.length = n + 2 := by simp [inp]
      have htrue : inp.getD (n + 1) false = true := by
        dsimp only [inp]; rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]; simp
      have hQlt : phaseQ t k z < 2 ^ b := phaseQ_lt t k b hk z
      have hth := hth_lt m hm
      have htrig_ev : (run gs1 inp).getD (trigs.getD (m * 2 ^ (b - d) + 2 ^ (b - 1 - d)) n) false =
          decide (m * 2 ^ (b - d) + 2 ^ (b - 1 - d) ≤ phaseQ t k z) := by
        have hgd : trigs.getD (m * 2 ^ (b - d) + 2 ^ (b - 1 - d)) n =
            trigs.getD (m * 2 ^ (b - d) + 2 ^ (b - 1 - d)) 0 := by
          rw [List.getD_eq_getElem trigs n (by omega), List.getD_eq_getElem trigs 0 (by omega)]
        rw [hgd]
        have hmem : trigs.getD (m * 2 ^ (b - d) + 2 ^ (b - 1 - d)) 0 ∈ trigs := by
          rw [List.getD_eq_getElem trigs 0 (by omega)]; exact List.getElem_mem (by omega)
        have hlt := htrigs_lt _ hmem
        rw [hext1, run_prefix gs0 ext1 inp _ (by omega)]
        exact htrigs_eval _ hth z
      apply Bool.eq_iff_iff.mpr
      simp only [mkTerm, List.all_cons, List.all_eq_true, Bool.and_eq_true, List.mem_map, List.mem_range,
        forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, htrig_ev, decide_eq_true_iff]
      have htop_lt : phaseQ t k z / 2 ^ (b - d) < 2 ^ d := by
        have h2 : 2 ^ (b - d) * 2 ^ d = 2 ^ b := by
          rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
        exact Nat.div_lt_of_lt_mul (by rwa [h2])
      have hneg_ev : ∀ i < d, (run gs1 inp).getD (if m.testBit (d - 1 - i) = false then neg1.getD i n else n + 1) false = true ↔
          (m.testBit (d - 1 - i) = false → (phaseQ t k z / 2 ^ (b - d)).testBit (d - 1 - i) = false) := by
        intro i hi
        have htb_shift : (phaseQ t k z / 2 ^ (b - d)).testBit (d - 1 - i) = (phaseQ t k z).testBit (b - 1 - i) := by
          have hexp : (b - d) + (d - 1 - i) = b - 1 - i := by omega
          rw [Nat.testBit, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← Nat.pow_add, hexp]
        by_cases hmb : m.testBit (d - 1 - i) = false
        · rw [if_pos hmb]
          have hgd : neg1.getD i n = neg1.getD i 0 := by
            rw [List.getD_eq_getElem neg1 n (by omega), List.getD_eq_getElem neg1 0 (by omega)]
          rw [hgd, (hev1 i hi z).2, htb_shift]
          cases (phaseQ t k z).testBit (b - 1 - i) <;> simp [hmb]
        · rw [if_neg hmb, run_input gs1 inp (n + 1) (by omega), htrue]
          simp [hmb]
      have hpow_split : 2 ^ (b - d) = 2 * 2 ^ (b - 1 - d) := by
        have he : b - d = (b - 1 - d) + 1 := by omega
        rw [he, Nat.pow_succ, Nat.mul_comm]
      have hbit_iff : (phaseQ t k z).testBit (b - 1 - d) = true ↔
          2 ^ (b - 1 - d) ≤ phaseQ t k z % 2 ^ (b - d) := by
        have hmod : phaseQ t k z % 2 ^ (b - d) < 2 ^ (b - d) := Nat.mod_lt _ (Nat.pow_pos (by omega))
        have htb : (phaseQ t k z).testBit (b - 1 - d) = (phaseQ t k z % 2 ^ (b - d)).testBit (b - 1 - d) := by
          rw [Nat.testBit_mod_two_pow]; simp [show b - 1 - d < b - d by omega]
        rw [htb, Nat.testBit, Nat.shiftRight_eq_div_pow]
        have hq : (phaseQ t k z % 2 ^ (b - d)) / 2 ^ (b - 1 - d) < 2 :=
          Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm, ← hpow_split]; exact hmod)
        have h01 : (phaseQ t k z % 2 ^ (b - d)) / 2 ^ (b - 1 - d) = 0 ∨
                   (phaseQ t k z % 2 ^ (b - d)) / 2 ^ (b - 1 - d) = 1 := by
          cases h : (phaseQ t k z % 2 ^ (b - d)) / 2 ^ (b - 1 - d) with
          | zero => exact Or.inl rfl
          | succ k =>
            cases k with
            | zero => exact Or.inr rfl
            | succ k' => rw [h] at hq; omega
        have hdm2 := Nat.div_add_mod (phaseQ t k z % 2 ^ (b - d)) (2 ^ (b - 1 - d))
        have hmr2 := Nat.mod_lt (phaseQ t k z % 2 ^ (b - d)) (Nat.pow_pos (a := 2) (n := b - 1 - d) (by omega))
        rcases h01 with h0 | h1
        · rw [h0]; rw [h0, Nat.mul_zero, Nat.zero_add] at hdm2
          simp only [Nat.and_zero]; constructor <;> [intro h; intro h] <;> [cases h; omega]
        · rw [h1]; rw [h1, Nat.mul_one] at hdm2
          change true = true ↔ _
          exact ⟨fun _ => by omega, fun _ => rfl⟩
      constructor
      · rintro ⟨hle, hnegs⟩
        have himp : ∀ i : Fin d, m.testBit (d - 1 - i.val) = false → (phaseQ t k z / 2 ^ (b - d)).testBit (d - 1 - i.val) = false :=
          fun i => (hneg_ev i.val i.isLt).mp (hnegs i.val i.isLt)
        have htop_le : phaseQ t k z / 2 ^ (b - d) ≤ m := le_of_testBit_imp d _ m htop_lt hm himp
        have hdm := Nat.div_add_mod (phaseQ t k z) (2 ^ (b - d))
        have hmod := Nat.mod_lt (phaseQ t k z) (Nat.pow_pos (a := 2) (n := b - d) (by omega))
        have hmeq : m = phaseQ t k z / 2 ^ (b - d) := by
          by_contra hne
          have hlt : phaseQ t k z / 2 ^ (b - d) + 1 ≤ m := by omega
          have := Nat.mul_le_mul_right (2 ^ (b - d)) hlt
          nlinarith
        refine ⟨hmeq, hbit_iff.mpr ?_⟩
        rw [hmeq] at hle; nlinarith
      · rintro ⟨rfl, hbit⟩
        have hrem := hbit_iff.mp hbit
        have hdm := Nat.div_add_mod (phaseQ t k z) (2 ^ (b - d))
        refine ⟨by nlinarith, fun i hi => (hneg_ev i hi).mpr (fun h => h)⟩
    -- Prove foldl invariant over List.range (2 ^ d)
    have hfold : ∀ (L : List ℕ), (∀ m ∈ L, m < 2 ^ d) →
        ∀ (acc : List Gate × List ℕ),
          (∃ ext, acc.1 = gs1 ++ ext) → Ctx n acc.1 →
          (∀ w ∈ acc.2, w < n + 2 + acc.1.length) →
          PEqualNP.NotBracket.notCount ⟨acc.1, 0⟩ = PEqualNP.NotBracket.notCount ⟨gs1, 0⟩ →
          (∀ z : Fin k × Finset (Fin t),
            let inp := List.ofFn (fun p : Fin n => decide (p ∈ layerX t k z)) ++ [false, true]
            acc.2.any (fun w => (run acc.1 inp).getD w false) =
              acc.2.any (fun w => (run acc.1 inp).getD w false)) →
          let res := L.foldl (fun (acc : List Gate × List ℕ) (m : ℕ) =>
            let rAnd := addAndList n acc.1 (mkTerm m)
            (rAnd.1, acc.2 ++ [rAnd.2])) acc
          (∃ ext, res.1 = acc.1 ++ ext) ∧ Ctx n res.1 ∧
          (∀ w ∈ res.2, w < n + 2 + res.1.length) ∧
          PEqualNP.NotBracket.notCount ⟨res.1, 0⟩ = PEqualNP.NotBracket.notCount ⟨gs1, 0⟩ ∧
          ∀ z : Fin k × Finset (Fin t),
            let inp := List.ofFn (fun p : Fin n => decide (p ∈ layerX t k z)) ++ [false, true]
            res.2.any (fun w => (run res.1 inp).getD w false) =
              (acc.2.any (fun w => (run acc.1 inp).getD w false) ||
               L.any (fun m => decide (m = phaseQ t k z / 2 ^ (b - d) ∧ (phaseQ t k z).testBit (b - 1 - d) = true))) := by
      intro L
      induction L with
      | nil =>
        intro _ acc _ hctxA hwA hnotA _
        refine ⟨⟨[], by simp⟩, hctxA, hwA, hnotA, ?_⟩
        intro z inp; simp
      | cons m L' ihL =>
        intro hL acc ⟨extA, hextA⟩ hctxA hwA hnotA _
        have hm : m < 2 ^ d := hL m List.mem_cons_self
        have hL' : ∀ m' ∈ L', m' < 2 ^ d := fun m' hm' => hL m' (List.mem_cons_of_mem _ hm')
        have hlenA : gs1.length ≤ acc.1.length := by rw [hextA, List.length_append]; omega
        have hwsA : ∀ w ∈ mkTerm m, w < n + 2 + acc.1.length := fun w hw => by have := hmk_lt m hm w hw; omega
        obtain ⟨⟨extM, hextM⟩, hctxM, hwM, hnotM, hevM⟩ := addAndList_spec n acc.1 (mkTerm m) hctxA hwsA
        set rAnd := addAndList n acc.1 (mkTerm m)
        have hlenAM : acc.1.length ≤ rAnd.1.length := by rw [hextM, List.length_append]; omega
        have hacc1_ext : ∃ ext, rAnd.1 = gs1 ++ ext := ⟨extA ++ extM, by rw [hextM, hextA, List.append_assoc]⟩
        have hacc1_w : ∀ w ∈ acc.2 ++ [rAnd.2], w < n + 2 + rAnd.1.length := by
          intro w hw
          rcases List.mem_append.mp hw with h | h
          · have := hwA w h; omega
          · rw [List.mem_singleton.mp h]; exact hwM
        have hacc1_not : PEqualNP.NotBracket.notCount ⟨rAnd.1, 0⟩ = PEqualNP.NotBracket.notCount ⟨gs1, 0⟩ := by
          rw [hnotM, hnotA]
        obtain ⟨⟨extR, hextR⟩, hctxR, hwR, hnotR, hevR⟩ := ihL hL' (rAnd.1, acc.2 ++ [rAnd.2]) hacc1_ext hctxM hacc1_w hacc1_not (fun _ => rfl)
        refine ⟨⟨extM ++ extR, by simpa [List.foldl_cons, List.append_assoc, rAnd] using by rw [hextR, hextM, List.append_assoc]⟩,
          hctxR, hwR, hnotR, ?_⟩
        intro z inp
        have hevR' := hevR z
        dsimp only at hevR' ⊢
        rw [List.foldl_cons, hevR']
        have hinp_len : inp.length = n + 2 := by simp [inp]
        have htrue : inp.getD (n + 1) false = true := by
          dsimp only [inp]; rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]; simp
        have hany_acc : (acc.2 ++ [rAnd.2]).any (fun w => (run rAnd.1 inp).getD w false) =
            (acc.2.any (fun w => (run acc.1 inp).getD w false) ||
             decide (m = phaseQ t k z / 2 ^ (b - d) ∧ (phaseQ t k z).testBit (b - 1 - d) = true)) := by
          rw [List.any_append, List.any_cons, List.any_nil, Bool.or_false]
          have h1 : acc.2.any (fun w => (run rAnd.1 inp).getD w false) = acc.2.any (fun w => (run acc.1 inp).getD w false) := by
            apply any_congr
            intro w hw
            have := hwA w hw
            rw [hextM]; exact run_prefix acc.1 extM inp w (by omega)
          have h2 : (run rAnd.1 inp).getD rAnd.2 false = (mkTerm m).all (fun w => (run gs1 inp).getD w false) := by
            rw [hevM inp hinp_len htrue]
            apply all_congr
            intro w hw
            have := hmk_lt m hm w hw
            rw [hextA]; exact run_prefix gs1 extA inp w (by omega)
          rw [h1, h2, hmk_eval m hm z]
        rw [hany_acc, List.any_cons, Bool.or_assoc]
    obtain ⟨⟨extF, hextF⟩, hctxF, hwF, hnotF, hevF⟩ :=
      hfold (List.range (2 ^ d)) (fun m hm => List.mem_range.mp hm) (gs1, []) ⟨[], by simp⟩ hctx1 (by simp) rfl (fun _ => rfl)
    set termsRes := (List.range (2 ^ d)).foldl
      (fun (acc : List Gate × List ℕ) (m : ℕ) =>
        let th := m * 2 ^ (b - d) + 2 ^ (b - 1 - d)
        let trigW := trigs.getD th n
        let negWs := (List.range d).map fun i =>
          if m.testBit (d - 1 - i) = false then neg1.getD i n else n + 1
        let rAnd := addAndList n acc.1 (trigW :: negWs)
        (rAnd.1, acc.2 ++ [rAnd.2]))
      (gs1, [])
    obtain ⟨⟨extOr, hextOr⟩, hctxOr, hwOr, hnotOr, hevOr⟩ := addOrList_spec n termsRes.1 termsRes.2 hctxF hwF
    set rOr := addOrList n termsRes.1 termsRes.2
    set rNot := addNot n rOr.1 rOr.2
    have hctxNot : Ctx n rNot.1 := ctx_snoc n rOr.1 ⟨.not, [rOr.2]⟩ hctxOr ⟨Or.inr (Or.inr rfl), by simp⟩
      (by intro u hu; simp at hu; subst hu; exact hwOr)
    have hnotNot : PEqualNP.NotBracket.notCount ⟨rNot.1, 0⟩ = PEqualNP.NotBracket.notCount ⟨gs0, 0⟩ + (d + 1) := by
      dsimp only [rNot, addNot]
      rw [notCount_snoc]; simp only [↓reduceIte]
      rw [hnotOr, hnotF, hnot1]; omega
    have hlen_gs1_rNot : gs1.length ≤ rNot.1.length := by
      have : rNot.1 = gs1 ++ (extF ++ extOr ++ [⟨.not, [rOr.2]⟩]) := by
        dsimp only [rNot, addNot]; rw [hextOr, hextF]; simp [List.append_assoc]
      rw [this, List.length_append]; omega
    have hrOr_lt_rNot : rOr.2 < n + 2 + rNot.1.length := by
      dsimp only [rNot, addNot]; rw [List.length_append, List.length_singleton]; omega
    have hrNot_lt : rNot.2 < n + 2 + rNot.1.length := by
      dsimp only [rNot, addNot]; rw [List.length_append, List.length_singleton]; omega
    refine ⟨⟨ext1 ++ extF ++ extOr ++ [⟨.not, [rOr.2]⟩], ?_⟩, hctxNot,
      by simp [buildBits, r1, pos1, hplen1], by simp [buildBits, r1, neg1, hnlen1], ?_, ?_, hnotNot, ?_⟩
    · change rNot.1 = gs0 ++ (ext1 ++ extF ++ extOr ++ [⟨.not, [rOr.2]⟩])
      dsimp only [rNot, addNot]
      rw [hextOr, hextF, hext1]; simp [List.append_assoc]
    · intro w hw
      change w ∈ pos1 ++ [rOr.2] at hw
      change w < n + 2 + rNot.1.length
      rcases List.mem_append.mp hw with h | h
      · have := hplt1 w h; omega
      · rw [List.mem_singleton.mp h]; exact hrOr_lt_rNot
    · intro w hw
      change w ∈ neg1 ++ [rNot.2] at hw
      change w < n + 2 + rNot.1.length
      rcases List.mem_append.mp hw with h | h
      · have := hnlt1 w h; omega
      · rw [List.mem_singleton.mp h]; exact hrNot_lt
    · intro i hi z inp
      have hinp_len : inp.length = n + 2 := by simp [inp]
      have hfalse : inp.getD n false = false := by
        dsimp only [inp]; rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]; simp
      by_cases hid : i < d
      · dsimp only [buildBits, r1, gs1, pos1, neg1, termsRes, rOr, rNot]
        have hp_gd : (pos1 ++ [rOr.2]).getD i 0 = pos1.getD i 0 := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
        have hn_gd : (neg1 ++ [rNot.2]).getD i 0 = neg1.getD i 0 := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
        rw [hp_gd, hn_gd]
        have hpmem : pos1.getD i 0 ∈ pos1 := by
          rw [List.getD_eq_getElem pos1 0 (by omega)]; exact List.getElem_mem (by omega)
        have hnmem : neg1.getD i 0 ∈ neg1 := by
          rw [List.getD_eq_getElem neg1 0 (by omega)]; exact List.getElem_mem (by omega)
        have hplt := hplt1 _ hpmem
        have hnlt := hnlt1 _ hnmem
        have hext_all : rNot.1 = gs1 ++ (extF ++ extOr ++ [⟨.not, [rOr.2]⟩]) := by
          dsimp only [rNot, addNot]; rw [hextOr, hextF]; simp [List.append_assoc]
        change (run rNot.1 inp).getD (pos1.getD i 0) false = _ ∧ (run rNot.1 inp).getD (neg1.getD i 0) false = _
        rw [hext_all, run_prefix gs1 _ inp _ (by omega), run_prefix gs1 _ inp _ (by omega)]
        exact hev1 i hid z
      · have hieq : i = d := by omega
        rw [hieq]
        change (run rNot.1 inp).getD ((pos1 ++ [rOr.2]).getD d 0) false = _ ∧
               (run rNot.1 inp).getD ((neg1 ++ [rNot.2]).getD d 0) false = _
        have hp_gd : (pos1 ++ [rOr.2]).getD d 0 = rOr.2 := by
          rw [← hplen1, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]; simp
        have hn_gd : (neg1 ++ [rNot.2]).getD d 0 = rNot.2 := by
          rw [← hnlen1, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]; simp
        rw [hp_gd, hn_gd]
        have hev_or : (run rOr.1 inp).getD rOr.2 false = (phaseQ t k z).testBit (b - 1 - d) := by
          rw [hevOr inp hinp_len hfalse]
          have hfev := hevF z
          dsimp only at hfev
          rw [hfev]
          simp only [List.any_nil, Bool.false_or]
          have hQlt : phaseQ t k z < 2 ^ b := phaseQ_lt t k b hk z
          have htop_lt : phaseQ t k z / 2 ^ (b - d) < 2 ^ d := by
            have h2 : 2 ^ (b - d) * 2 ^ d = 2 ^ b := by
              rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
            exact Nat.div_lt_of_lt_mul (by rwa [h2])
          apply Bool.eq_iff_iff.mpr
          rw [List.any_eq_true]
          simp only [List.mem_range, decide_eq_true_iff]
          constructor
          · rintro ⟨m, _, rfl, hb⟩; exact hb
          · intro hb; exact ⟨phaseQ t k z / 2 ^ (b - d), htop_lt, rfl, hb⟩
        have hev_or_in_not : (run rNot.1 inp).getD rOr.2 false = (phaseQ t k z).testBit (b - 1 - d) := by
          dsimp only [rNot, addNot]
          rw [run_prefix rOr.1 [⟨.not, [rOr.2]⟩] inp rOr.2 (by omega), hev_or]
        have hev_not : (run rNot.1 inp).getD rNot.2 false = !((phaseQ t k z).testBit (b - 1 - d)) := by
          dsimp only [rNot, addNot]
          rw [run_snoc]
          have hrlen : (run rOr.1 inp).length = n + 2 + rOr.1.length := by rw [run_length, hinp_len]
          rw [← hrlen, getD_eq, List.map_cons, List.map_nil, notEval_cons, hev_or]
        exact ⟨hev_or_in_not, hev_not⟩

-- Stage 3+4: build one tap wire for a : Fin t, and fold over all a : Fin t
private def buildTap (n t k b : ℕ) (posW negW : List ℕ) (gs : List Gate) (a : Fin t) : List Gate × ℕ :=
  let S_a : Finset (Fin t) := Finset.univ.filter fun c : Fin t => c.val < a.val
  let branches := (List.range (2 ^ b)).foldl
    (fun (acc : List Gate × List ℕ) (q : ℕ) =>
      let eqWs := (List.range b).map fun i =>
        if q.testBit (b - 1 - i) then posW.getD i n else negW.getD i n
      let rEq := addAndList n acc.1 eqWs
      let rMt := buildMinterm n t k rEq.1 (q * (t + 1) + a.val) S_a
      let rBr := addAnd n rMt.1 rEq.2 rMt.2
      (rBr.1, acc.2 ++ [rBr.2]))
    (gs, [])
  addOrList n branches.1 branches.2

set_option maxHeartbeats 800000 in
private theorem buildTap_spec (t k b : ℕ) (ht : 1 ≤ t) (hk : k < (t + 1) * 2 ^ b)
    (gsB : List Gate) (posW negW : List ℕ)
    (hplen : posW.length = b) (hnlen : negW.length = b)
    (hplt : ∀ w ∈ posW, w < 2 * t * k + 2 + gsB.length)
    (hnlt : ∀ w ∈ negW, w < 2 * t * k + 2 + gsB.length)
    (hevb : ∀ i < b, ∀ z : Fin k × Finset (Fin t),
      let inp := List.ofFn (fun p : Fin (2 * t * k) => decide (p ∈ layerX t k z)) ++ [false, true]
      (run gsB inp).getD (posW.getD i 0) false = (phaseQ t k z).testBit (b - 1 - i) ∧
      (run gsB inp).getD (negW.getD i 0) false = !((phaseQ t k z).testBit (b - 1 - i)))
    (gs : List Gate) (hextB : ∃ ext, gs = gsB ++ ext) (hctx : Ctx (2 * t * k) gs) (a : Fin t) :
    let n := 2 * t * k
    let S_a : Finset (Fin t) := Finset.univ.filter fun c : Fin t => c.val < a.val
    let r := buildTap n t k b posW negW gs a
    (∃ ext, r.1 = gs ++ ext) ∧
    Ctx n r.1 ∧
    r.2 < n + 2 + r.1.length ∧
    PEqualNP.NotBracket.notCount ⟨r.1, 0⟩ = PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ∧
    ∀ z : Fin k × Finset (Fin t),
      let inp := List.ofFn (fun p : Fin n => decide (p ∈ layerX t k z)) ++ [false, true]
      (run r.1 inp).getD r.2 false =
        decide (phaseQ t k z * (t + 1) + a.val < z.1.val ∨
          (phaseQ t k z * (t + 1) + a.val = z.1.val ∧ z.2 = S_a)) := by
  intro n S_a
  obtain ⟨extB, rfl⟩ := hextB
  have hfold : ∀ (L : List ℕ), (∀ q ∈ L, q < 2 ^ b) →
      ∀ (acc : List Gate × List ℕ),
        (∃ ext, acc.1 = gsB ++ ext) → Ctx n acc.1 →
        (∀ w ∈ acc.2, w < n + 2 + acc.1.length) →
        PEqualNP.NotBracket.notCount ⟨acc.1, 0⟩ = PEqualNP.NotBracket.notCount ⟨gsB ++ extB, 0⟩ →
        let res := L.foldl (fun (acc : List Gate × List ℕ) (q : ℕ) =>
          let eqWs := (List.range b).map fun i =>
            if q.testBit (b - 1 - i) then posW.getD i n else negW.getD i n
          let rEq := addAndList n acc.1 eqWs
          let rMt := buildMinterm n t k rEq.1 (q * (t + 1) + a.val) S_a
          let rBr := addAnd n rMt.1 rEq.2 rMt.2
          (rBr.1, acc.2 ++ [rBr.2])) acc
        (∃ ext, res.1 = acc.1 ++ ext) ∧ Ctx n res.1 ∧
        (∀ w ∈ res.2, w < n + 2 + res.1.length) ∧
        PEqualNP.NotBracket.notCount ⟨res.1, 0⟩ = PEqualNP.NotBracket.notCount ⟨gsB ++ extB, 0⟩ ∧
        ∀ z : Fin k × Finset (Fin t),
          let inp := List.ofFn (fun p : Fin n => decide (p ∈ layerX t k z)) ++ [false, true]
          res.2.any (fun w => (run res.1 inp).getD w false) =
            (acc.2.any (fun w => (run acc.1 inp).getD w false) ||
             L.any (fun q => decide (phaseQ t k z = q ∧
               (q * (t + 1) + a.val < z.1.val ∨ (q * (t + 1) + a.val = z.1.val ∧ z.2 = S_a))))) := by
    intro L
    induction L with
    | nil =>
      intro _ acc _ hctxA hwA hnotA
      refine ⟨⟨[], by simp⟩, hctxA, hwA, hnotA, ?_⟩
      intro z inp; simp
    | cons q L' ihL =>
      intro hL acc ⟨extA, hextA⟩ hctxA hwA hnotA
      have hq : q < 2 ^ b := hL q List.mem_cons_self
      have hL' : ∀ q' ∈ L', q' < 2 ^ b := fun q' hq' => hL q' (List.mem_cons_of_mem _ hq')
      have hlenBA : gsB.length ≤ acc.1.length := by rw [hextA, List.length_append]; omega
      let eqWs := (List.range b).map fun i => if q.testBit (b - 1 - i) then posW.getD i n else negW.getD i n
      have heqWs_lt : ∀ w ∈ eqWs, w < n + 2 + acc.1.length := by
        intro w hw
        simp only [eqWs, List.mem_map, List.mem_range] at hw
        obtain ⟨i, hi, rfl⟩ := hw
        split_ifs
        · have hmem : posW.getD i n ∈ posW := by
            rw [List.getD_eq_getElem posW n (by omega)]; exact List.getElem_mem (by omega)
          have := hplt _ hmem; omega
        · have hmem : negW.getD i n ∈ negW := by
            rw [List.getD_eq_getElem negW n (by omega)]; exact List.getElem_mem (by omega)
          have := hnlt _ hmem; omega
      obtain ⟨⟨extEq, hextEq⟩, hctxEq, hwEq, hnotEq, hevEq⟩ := addAndList_spec n acc.1 eqWs hctxA heqWs_lt
      set rEq := addAndList n acc.1 eqWs
      obtain ⟨⟨extMt, hextMt⟩, hctxMt, hwMt, hnotMt, hevMt⟩ := buildMinterm_spec t k ht rEq.1 hctxEq (q * (t + 1) + a.val) S_a
      set rMt := buildMinterm n t k rEq.1 (q * (t + 1) + a.val) S_a
      have hlenEqMt : rEq.1.length ≤ rMt.1.length := by rw [hextMt, List.length_append]; omega
      set rBr := addAnd n rMt.1 rEq.2 rMt.2
      have hctxBr : Ctx n rBr.1 := ctx_snoc n rMt.1 ⟨.and, [rEq.2, rMt.2]⟩ hctxMt ⟨Or.inl rfl, by simp⟩
        (by intro u hu; simp at hu; rcases hu with rfl | rfl <;> omega)
      have hwBr : rBr.2 < n + 2 + rBr.1.length := by
        dsimp only [rBr, addAnd]; rw [List.length_append, List.length_singleton]; omega
      have hnotBr : PEqualNP.NotBracket.notCount ⟨rBr.1, 0⟩ = PEqualNP.NotBracket.notCount ⟨gsB ++ extB, 0⟩ := by
        dsimp only [rBr, addAnd]; rw [notCount_snoc]; simpa [hnotMt, hnotEq] using hnotA
      have hext1 : ∃ ext, rBr.1 = acc.1 ++ ext :=
        ⟨extEq ++ extMt ++ [⟨.and, [rEq.2, rMt.2]⟩], by dsimp only [rBr, addAnd]; rw [hextMt, hextEq]; simp [List.append_assoc]⟩
      have hext1B : ∃ ext, rBr.1 = gsB ++ ext :=
        ⟨extA ++ extEq ++ extMt ++ [⟨.and, [rEq.2, rMt.2]⟩], by dsimp only [rBr, addAnd]; rw [hextMt, hextEq, hextA]; simp [List.append_assoc]⟩
      have hlenABr : acc.1.length ≤ rBr.1.length := by
        obtain ⟨ext, h⟩ := hext1; rw [h, List.length_append]; omega
      have hw1 : ∀ w ∈ acc.2 ++ [rBr.2], w < n + 2 + rBr.1.length := by
        intro w hw; rcases List.mem_append.mp hw with h | h
        · have := hwA w h; omega
        · rw [List.mem_singleton.mp h]; exact hwBr
      obtain ⟨⟨extR, hextR⟩, hctxR, hwR, hnotR, hevR⟩ := ihL hL' (rBr.1, acc.2 ++ [rBr.2]) hext1B hctxBr hw1 hnotBr
      refine ⟨⟨(extEq ++ extMt ++ [⟨.and, [rEq.2, rMt.2]⟩]) ++ extR, ?_⟩, hctxR, hwR, hnotR, ?_⟩
      · change (List.foldl _ (rBr.1, acc.2 ++ [rBr.2]) L').1 = _
        rw [hextR]
        dsimp only [rBr, addAnd]; rw [hextMt, hextEq]; simp [List.append_assoc]
      · intro z inp
        have hevR' := hevR z
        dsimp only at hevR' ⊢
        rw [List.foldl_cons, hevR']
        have hinp_len : inp.length = n + 2 := by simp [inp]
        have htrue : inp.getD (n + 1) false = true := by
          dsimp only [inp]; rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]; simp
        have hQlt : phaseQ t k z < 2 ^ b := phaseQ_lt t k b hk z
        have heq_eval : (run rEq.1 inp).getD rEq.2 false = decide (phaseQ t k z = q) := by
          rw [hevEq inp hinp_len htrue]
          apply Bool.eq_iff_iff.mpr
          rw [List.all_eq_true, decide_eq_true_iff]
          simp only [eqWs, List.mem_map, List.mem_range, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
          have hbit : ∀ i < b, (run acc.1 inp).getD (if q.testBit (b - 1 - i) = true then posW.getD i n else negW.getD i n) false = true ↔
              (phaseQ t k z).testBit (b - 1 - i) = q.testBit (b - 1 - i) := by
            intro i hi
            by_cases hqb : q.testBit (b - 1 - i) = true
            · rw [if_pos hqb]
              have hgd : posW.getD i n = posW.getD i 0 := by
                rw [List.getD_eq_getElem posW n (by omega), List.getD_eq_getElem posW 0 (by omega)]
              have hmem : posW.getD i 0 ∈ posW := by
                rw [List.getD_eq_getElem posW 0 (by omega)]; exact List.getElem_mem (by omega)
              rw [hgd, hextA, run_prefix gsB extA inp _ (by have := hplt _ hmem; omega), (hevb i hi z).1, hqb]
            · rw [if_neg hqb]
              have hqb' : q.testBit (b - 1 - i) = false := by cases h : q.testBit (b - 1 - i) <;> simp_all
              have hgd : negW.getD i n = negW.getD i 0 := by
                rw [List.getD_eq_getElem negW n (by omega), List.getD_eq_getElem negW 0 (by omega)]
              have hmem : negW.getD i 0 ∈ negW := by
                rw [List.getD_eq_getElem negW 0 (by omega)]; exact List.getElem_mem (by omega)
              rw [hgd, hextA, run_prefix gsB extA inp _ (by have := hnlt _ hmem; omega), (hevb i hi z).2, hqb']
              cases (phaseQ t k z).testBit (b - 1 - i) <;> simp
          constructor
          · intro hall
            exact eq_of_testBit_eq b (phaseQ t k z) q hQlt hq (fun i => (hbit i.val i.isLt).mp (hall i.val i.isLt))
          · rintro rfl i hi
            exact (hbit i hi).mpr rfl
        have hbr_eval : (run rBr.1 inp).getD rBr.2 false =
            decide (phaseQ t k z = q ∧ (q * (t + 1) + a.val < z.1.val ∨ (q * (t + 1) + a.val = z.1.val ∧ z.2 = S_a))) := by
          dsimp only [rBr, addAnd]
          rw [run_snoc]
          have hrlen : (run rMt.1 inp).length = n + 2 + rMt.1.length := by rw [run_length, hinp_len]
          rw [← hrlen, getD_eq, andEval]
          simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          have hpEq : (run rMt.1 inp).getD rEq.2 false = (run rEq.1 inp).getD rEq.2 false := by
            rw [hextMt]; exact run_prefix rEq.1 extMt inp rEq.2 (by omega)
          rw [hpEq, heq_eval, hevMt z]
          apply Bool.eq_iff_iff.mpr; simp
        have hany_acc : (acc.2 ++ [rBr.2]).any (fun w => (run rBr.1 inp).getD w false) =
            (acc.2.any (fun w => (run acc.1 inp).getD w false) ||
             decide (phaseQ t k z = q ∧ (q * (t + 1) + a.val < z.1.val ∨ (q * (t + 1) + a.val = z.1.val ∧ z.2 = S_a)))) := by
          rw [List.any_append, List.any_cons, List.any_nil, Bool.or_false, hbr_eval]
          congr 1
          apply any_congr
          intro w hw
          obtain ⟨ext, he⟩ := hext1
          rw [he]; exact run_prefix acc.1 ext inp w (by have := hwA w hw; omega)
        rw [hany_acc, List.any_cons, Bool.or_assoc]
  obtain ⟨⟨extF, hextF⟩, hctxF, hwF, hnotF, hevF⟩ :=
    hfold (List.range (2 ^ b)) (fun q hq => List.mem_range.mp hq) (gsB ++ extB, []) ⟨extB, rfl⟩ hctx (by simp) rfl
  set branches := (List.range (2 ^ b)).foldl
    (fun (acc : List Gate × List ℕ) (q : ℕ) =>
      let eqWs := (List.range b).map fun i => if q.testBit (b - 1 - i) then posW.getD i n else negW.getD i n
      let rEq := addAndList n acc.1 eqWs
      let rMt := buildMinterm n t k rEq.1 (q * (t + 1) + a.val) S_a
      let rBr := addAnd n rMt.1 rEq.2 rMt.2
      (rBr.1, acc.2 ++ [rBr.2]))
    (gsB ++ extB, [])
  obtain ⟨⟨extOr, hextOr⟩, hctxOr, hwOr, hnotOr, hevOr⟩ := addOrList_spec n branches.1 branches.2 hctxF hwF
  refine ⟨⟨extF ++ extOr, by dsimp only [buildTap]; rw [hextOr, hextF, List.append_assoc]⟩,
    hctxOr, hwOr, by dsimp only [buildTap]; rw [hnotOr, hnotF], ?_⟩
  intro z inp
  have hinp_len : inp.length = n + 2 := by simp [inp]
  have hfalse : inp.getD n false = false := by
    dsimp only [inp]; rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]; simp
  dsimp only [buildTap]
  rw [hevOr inp hinp_len hfalse]
  have hfev := hevF z
  dsimp only at hfev
  rw [hfev]
  simp only [List.any_nil, Bool.false_or]
  have hQlt : phaseQ t k z < 2 ^ b := phaseQ_lt t k b hk z
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true, decide_eq_true_iff]
  simp only [List.mem_range, decide_eq_true_iff]
  constructor
  · rintro ⟨q, _, rfl, h⟩; exact h
  · intro h; exact ⟨phaseQ t k z, hQlt, rfl, h⟩

private def buildAllTaps (n t k b : ℕ) (posW negW : List ℕ) (gs : List Gate) : ℕ → List Gate × List ℕ
  | 0 => (gs, [])
  | m + 1 =>
    let r1 := buildAllTaps n t k b posW negW gs m
    if h : m < t then
      let r2 := buildTap n t k b posW negW r1.1 ⟨m, h⟩
      (r2.1, r1.2 ++ [r2.2])
    else (r1.1, r1.2 ++ [n])

private theorem part2_construct (t k b : ℕ) (ht : 1 ≤ t) (hk : k < (t + 1) * 2 ^ b) :
    fitsClean t (Fin k × Finset (Fin t)) (2 * t * k) b (layerX t k) (fun z w => w ≠ z.2) := by
  let n := 2 * t * k
  obtain ⟨_, hctxT, hlenT, hwT, hnotT, hevT⟩ := buildTrigs_spec t k ht (2 ^ b) [] (ctx_nil n)
  set rT := buildTrigs t k (2 ^ b) []
  obtain ⟨_, hctxB, hplenB, hnlenB, hpltB, hnltB, hnotB, hevB⟩ :=
    buildBits_spec t k b hk rT.1 rT.2 hctxT hlenT hwT hevT b le_rfl
  set rB := buildBits n b rT.2 b rT.1
  have hnotB_eq : PEqualNP.NotBracket.notCount ⟨rB.1, 0⟩ = b := by
    rw [hnotB, hnotT]; simp [PEqualNP.NotBracket.notCount]
  have hallTaps : ∀ m ≤ t,
      let r := buildAllTaps n t k b rB.2.1 rB.2.2 rB.1 m
      (∃ ext, r.1 = rB.1 ++ ext) ∧
      Ctx n r.1 ∧
      r.2.length = m ∧
      (∀ w ∈ r.2, w < n + 2 + r.1.length) ∧
      PEqualNP.NotBracket.notCount ⟨r.1, 0⟩ = b ∧
      ∀ (a : Fin t), a.val < m → ∀ z : Fin k × Finset (Fin t),
        let inp := List.ofFn (fun p : Fin n => decide (p ∈ layerX t k z)) ++ [false, true]
        let S_a : Finset (Fin t) := Finset.univ.filter fun c : Fin t => c.val < a.val
        (run r.1 inp).getD (r.2.getD a.val 0) false =
          decide (phaseQ t k z * (t + 1) + a.val < z.1.val ∨
            (phaseQ t k z * (t + 1) + a.val = z.1.val ∧ z.2 = S_a)) := by
    intro m
    induction m with
    | zero =>
      intro _
      exact ⟨⟨[], by simp [buildAllTaps]⟩, hctxB, rfl, by simp [buildAllTaps], hnotB_eq, fun a ha => by omega⟩
    | succ m ih =>
      intro hm
      obtain ⟨⟨ext1, hext1⟩, hctx1, hlen1, hw1, hnot1, hev1⟩ := ih (by omega)
      set r1 := buildAllTaps n t k b rB.2.1 rB.2.2 rB.1 m
      have hmt : m < t := by omega
      obtain ⟨⟨ext2, hext2⟩, hctx2, hw2, hnot2, hev2⟩ :=
        buildTap_spec t k b ht hk rB.1 rB.2.1 rB.2.2 hplenB hnlenB hpltB hnltB hevB r1.1 ⟨ext1, hext1⟩ hctx1 ⟨m, hmt⟩
      set r2 := buildTap n t k b rB.2.1 rB.2.2 r1.1 ⟨m, hmt⟩
      have hlen12 : r1.1.length ≤ r2.1.length := by rw [hext2, List.length_append]; omega
      dsimp only [buildAllTaps]
      rw [dif_pos hmt]
      refine ⟨⟨ext1 ++ ext2, by rw [hext2, hext1, List.append_assoc]⟩, hctx2, by simp [r1, hlen1], ?_, by rw [hnot2, hnot1], ?_⟩
      · intro w hw
        change w < n + 2 + r2.1.length
        rcases List.mem_append.mp hw with h | h
        · have := hw1 w h; omega
        · rw [List.mem_singleton.mp h]; exact hw2
      · intro a ha z
        dsimp only
        let inp := List.ofFn (fun p : Fin n => decide (p ∈ layerX t k z)) ++ [false, true]
        change (run r2.1 inp).getD ((r1.2 ++ [r2.2]).getD a.val 0) false = _
        by_cases ham : a.val < m
        · have hget : (r1.2 ++ [r2.2]).getD a.val 0 = r1.2.getD a.val 0 := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
          rw [hget]
          have hmem : r1.2.getD a.val 0 ∈ r1.2 := by
            rw [List.getD_eq_getElem r1.2 0 (by omega)]; exact List.getElem_mem (by omega)
          have hlt := hw1 _ hmem
          rw [hext2, run_prefix r1.1 ext2 inp _ (by dsimp only [n] at hlt; simp only [inp, List.length_append, List.length_ofFn, List.length_cons, List.length_nil]; omega)]
          exact hev1 a ham z
        · have haeq : a = ⟨m, hmt⟩ := Fin.ext (show a.val = m by omega)
          subst haeq
          have hget : (r1.2 ++ [r2.2]).getD m 0 = r2.2 := by
            rw [← hlen1, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]; simp
          rw [hget]
          exact hev2 z
  obtain ⟨_, hctxF, hlenF, hwF, hnotF, hevF⟩ := hallTaps t le_rfl
  set rF := buildAllTaps n t k b rB.2.1 rB.2.2 rB.1 t
  refine ⟨⟨rF.1, 0⟩, fun a => rF.2.getD a.val 0,
    ctx_to_fanInTwo n rF.1 0 hctxF,
    ctx_to_readsBack n rF.1 0 hctxF,
    by dsimp [Circuit.size]; omega,
    ?_,
    by rw [hnotF],
    ?_⟩
  · intro a
    have hmem : rF.2.getD a.val 0 ∈ rF.2 := by
      rw [List.getD_eq_getElem rF.2 0 (by omega)]; exact List.getElem_mem (by omega)
    exact hwF _ hmem
  · intro z
    let Wz := Finset.univ.filter fun a : Fin t =>
      (Circuit.wires ⟨rF.1, 0⟩ (List.ofFn (fun p : Fin n => decide (p ∈ layerX t k z)) ++ [false, true])).getD (rF.2.getD a.val 0) false = true
    change Wz ≠ z.2
    have hmemW : ∀ a : Fin t, a ∈ Wz ↔
        phaseQ t k z * (t + 1) + a.val < z.1.val ∨
        (phaseQ t k z * (t + 1) + a.val = z.1.val ∧ z.2 = Finset.univ.filter (fun c : Fin t => c.val < a.val)) := by
      intro a
      simp only [Wz, Finset.mem_filter, Finset.mem_univ, true_and]
      change (run rF.1 _).getD (rF.2.getD a.val 0) false = true ↔ _
      rw [hevF a a.isLt z, decide_eq_true_iff]
    have hdm := Nat.div_add_mod z.1.val (t + 1)
    have hmod := Nat.mod_lt z.1.val (show 0 < t + 1 by omega)
    by_cases hfull : z.1.val % (t + 1) = t ∧ z.2 = Finset.univ
    · have hQ : phaseQ t k z = z.1.val / (t + 1) + 1 := by simp [phaseQ, hfull]
      intro heq
      let a0 : Fin t := ⟨0, by omega⟩
      have ha0 : a0 ∈ Wz := by rw [heq, hfull.2]; exact Finset.mem_univ a0
      rcases (hmemW a0).mp ha0 with h1 | ⟨h1, _⟩ <;> rw [hQ] at h1 <;> nlinarith
    · have hQ : phaseQ t k z = z.1.val / (t + 1) := by simp [phaseQ, hfull]
      by_cases hrem : z.1.val % (t + 1) = t
      · have hne_univ : z.2 ≠ Finset.univ := fun hu => hfull ⟨hrem, hu⟩
        have hW_univ : Wz = Finset.univ := by
          ext a
          simp only [Finset.mem_univ, iff_true]
          refine (hmemW a).mpr (Or.inl ?_)
          rw [hQ]; have := a.isLt; nlinarith
        rw [hW_univ]; exact hne_univ.symm
      · let r := z.1.val % (t + 1)
        have hrt : r < t := by omega
        let Sr : Finset (Fin t) := Finset.univ.filter fun c : Fin t => c.val < r
        by_cases hzr : z.2 = Sr
        · intro heq
          let ar : Fin t := ⟨r, hrt⟩
          have harW : ar ∈ Wz := (hmemW ar).mpr (Or.inr ⟨by rw [hQ]; dsimp [ar, r]; nlinarith, hzr⟩)
          rw [heq, hzr] at harW
          have := (Finset.mem_filter.mp harW).2
          dsimp [ar] at this; omega
        · have hW_eq : Wz = Sr := by
            ext a
            rw [hmemW a]
            simp only [Sr, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro (h1 | ⟨h1, h2⟩)
              · rw [hQ] at h1; dsimp [r]; nlinarith
              · exfalso
                have haeq : a.val = r := by rw [hQ] at h1; dsimp [r]; nlinarith
                apply hzr; rw [h2]; ext c; simp [Sr, haeq]
            · intro hlt
              left; rw [hQ]; dsimp [r] at hlt; nlinarith
          rw [hW_eq]; exact fun h => hzr h.symm

private theorem main_clean (t : ℕ) :
    (∀ (n m k b : ℕ) (x : Fin m → Finset (Fin n)) (block : Fin m → Fin k)
      (ok : Fin m → Finset (Fin t) → Prop), Function.Injective x →
      (∀ i j, block i < block j → x i ⊆ x j) → fitsClean t (Fin m) n b x ok →
      ∀ (Bad : Finset (Fin k)),
        (∀ j ∈ Bad, ¬ ∃ w : Finset (Fin t), ∀ i, block i = j → ok i w) →
        Bad.card < (t + 1) * 2 ^ b) ∧
    (1 ≤ t → ∀ k : ℕ,
      let I := Fin k × Finset (Fin t)
      ∃ x : I → Finset (Fin (2 * t * k)), Function.Injective x ∧
        (∀ z z' : I, x z ⊆ x z' ↔ z.1 < z'.1 ∨ z = z') ∧
        ∀ b, fitsClean t I (2 * t * k) b x (fun z w => w ≠ z.2) ↔ k < (t + 1) * 2 ^ b) := by
  refine ⟨fun n m k b x block ok _ hblk hfits Bad hBad =>
      part1_clean t n m k b x block ok hblk hfits Bad hBad, ?_⟩
  intro ht k
  refine ⟨layerX t k, layerX_inj t k ht, layerX_sub_iff t k ht, ?_⟩
  intro b
  constructor
  · intro hfits
    let I := Fin k × Finset (Fin t)
    let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
    have hfits' : fitsClean t (Fin (Fintype.card I)) (2 * t * k) b
        (fun i => layerX t k (e.symm i)) (fun i w => w ≠ (e.symm i).2) := by
      obtain ⟨C, tap, h1, h2, h3, h4, h5, h6⟩ := hfits
      exact ⟨C, tap, h1, h2, h3, h4, h5, fun i => h6 (e.symm i)⟩
    have hblk' : ∀ i j : Fin (Fintype.card I), (e.symm i).1 < (e.symm j).1 →
        layerX t k (e.symm i) ⊆ layerX t k (e.symm j) :=
      fun i j hlt => (layerX_sub_iff t k ht _ _).mpr (Or.inl hlt)
    have hBad : ∀ j ∈ (Finset.univ : Finset (Fin k)),
        ¬ ∃ w : Finset (Fin t), ∀ i : Fin (Fintype.card I), (e.symm i).1 = j → w ≠ (e.symm i).2 := by
      intro j _ ⟨w, hw⟩
      have := hw (e (j, w)) (by simp)
      simp at this
    have hcard := part1_clean t (2 * t * k) (Fintype.card I) k b
      (fun i => layerX t k (e.symm i)) (fun i => (e.symm i).1) (fun i w => w ≠ (e.symm i).2)
      hblk' hfits' Finset.univ hBad
    simpa using hcard
  · exact part2_construct t k b ht

end PEqualNP.Outside.L_lib_1318

theorem PEqualNP.Outside.L_lib_1318 :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    ∀ t : Nat,
      let fits := fun (I : Type) (n b : Nat) (x : I → Finset (Fin n)) (ok : I → Finset (Fin t) → Prop) =>
        ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin t → Nat),
          PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
          C.output < n+2+C.size ∧ (∀ a, tap a < n+2+C.size) ∧ PEqualNP.NotBracket.notCount C ≤ b ∧
          ∀ i, ok i (Finset.univ.filter (fun a =>
            (C.wires (List.ofFn (fun j : Fin n => decide (j ∈ x i)) ++ [false,true])).getD (tap a) false = true))
      (∀ (n m k b : Nat) (x : Fin m → Finset (Fin n)) (block : Fin m → Fin k)
        (ok : Fin m → Finset (Fin t) → Prop), Function.Injective x →
        (∀ i j, block i < block j → x i ⊆ x j) → fits (Fin m) n b x ok →
        (Finset.univ.filter (fun j : Fin k => ¬ ∃ w : Finset (Fin t), ∀ i, block i = j → ok i w)).card <
          (t+1)*2^b) ∧
      (1 ≤ t → ∀ k : Nat,
        let I := Fin k × Finset (Fin t)
        ∃ x : I → Finset (Fin (2*t*k)), Function.Injective x ∧
          (∀ z z' : I, x z ⊆ x z' ↔ z.1 < z'.1 ∨ z = z') ∧
          ∀ b, fits I (2*t*k) b x (fun z w => w ≠ z.2) ↔ k < (t+1)*2^b) := by
  dsimp only
  intro t
  have hdec : ∀ (P : Prop) (d1 d2 : Decidable P), @decide P d1 = @decide P d2 :=
    fun _ _ _ => decide_eq_decide.mpr Iff.rfl
  have hfits_iff : ∀ (I : Type) (n b : Nat) (x : I → Finset (Fin n)) (ok : I → Finset (Fin t) → Prop),
      (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin t → Nat),
        PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C ∧
        C.output < n + 2 + C.size ∧ (∀ a, tap a < n + 2 + C.size) ∧ PEqualNP.NotBracket.notCount C ≤ b ∧
        ∀ i, ok i (@Finset.filter (Fin t) (fun a =>
          (C.wires (List.ofFn (fun j : Fin n => @decide (j ∈ x i) (Classical.propDecidable _)) ++ [false, true])).getD (tap a) false = true)
          (fun a => Classical.propDecidable _) Finset.univ)) ↔
      PEqualNP.Outside.L_lib_1318.fitsClean t I n b x ok := by
    intro I n b x ok
    constructor <;> rintro ⟨C, tap, h1, h2, h3, h4, h5, h6⟩ <;> refine ⟨C, tap, h1, h2, h3, h4, h5, fun i => ?_⟩
    · have hwire : List.ofFn (fun j : Fin n => @decide (j ∈ x i) (Classical.propDecidable _)) =
          List.ofFn (fun j : Fin n => decide (j ∈ x i)) := by
        congr 1; funext j; exact hdec _ _ _
      have hf : @Finset.filter (Fin t) (fun a =>
          (C.wires (List.ofFn (fun j : Fin n => @decide (j ∈ x i) (Classical.propDecidable _)) ++ [false, true])).getD (tap a) false = true)
          (fun a => Classical.propDecidable _) Finset.univ =
          Finset.univ.filter (fun a =>
            (C.wires (List.ofFn (fun j : Fin n => decide (j ∈ x i)) ++ [false, true])).getD (tap a) false = true) := by
        ext a; simp only [Finset.mem_filter, hwire]
      rw [← hf]; exact h6 i
    · have hwire : List.ofFn (fun j : Fin n => @decide (j ∈ x i) (Classical.propDecidable _)) =
          List.ofFn (fun j : Fin n => decide (j ∈ x i)) := by
        congr 1; funext j; exact hdec _ _ _
      have hf : @Finset.filter (Fin t) (fun a =>
          (C.wires (List.ofFn (fun j : Fin n => @decide (j ∈ x i) (Classical.propDecidable _)) ++ [false, true])).getD (tap a) false = true)
          (fun a => Classical.propDecidable _) Finset.univ =
          Finset.univ.filter (fun a =>
            (C.wires (List.ofFn (fun j : Fin n => decide (j ∈ x i)) ++ [false, true])).getD (tap a) false = true) := by
        ext a; simp only [Finset.mem_filter, hwire]
      rw [hf]; exact h6 i
  obtain ⟨hp1, hp2⟩ := PEqualNP.Outside.L_lib_1318.main_clean t
  refine ⟨?_, ?_⟩
  · intro n m k b x block ok hinj hblk hfits
    refine hp1 n m k b x block ok hinj hblk ((hfits_iff _ _ _ _ _).mp hfits) _ ?_
    intro j hj
    exact ((@Finset.mem_filter _ _ (fun j => Classical.propDecidable _) _ _).mp hj).2
  · intro ht k
    obtain ⟨x, hinj, hsub, hiff⟩ := hp2 ht k
    exact ⟨x, hinj, hsub, fun b => (hfits_iff _ _ _ _ _).trans (hiff b)⟩
