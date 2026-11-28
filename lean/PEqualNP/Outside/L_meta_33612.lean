import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33612

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Credit: the wiresFrom lemmas below are copied from PEqualNP.MetaComplexity.Helpers
-- (Shannon and RepReads), via PEqualNP.Outside.L_meta_33599, inlined because those modules are not built here.


/-- Run gates on a wire list: the fold inside `Circuit.wires`. -/
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem wiresFrom_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    wiresFrom (gs ++ [g]) x = wiresFrom gs x ++
      [g.op.eval (g.inputs.map fun i => (wiresFrom gs x).getD i false)] := by
  rw [wiresFrom_append]; rfl

theorem getD_snoc (V : List Bool) (e : Bool) (i : ℕ) :
    (V ++ [e]).getD i false = if i = V.length then e else V.getD i false := by
  split_ifs with h
  · subst h; simp
  · rcases Nat.lt_or_gt_of_ne h with h | h
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

/-- A gate with its inputs renamed by `r`. -/
def rg (r : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map r⟩

theorem getD_prefix (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ hi]

/-- Renaming wires: the copied gates read the renamed wires and agree with the old ones. -/
theorem ren (x y : List Bool) (d : ℕ) (r : ℕ → ℕ) (hy : y.length = x.length + d)
    (hr : ∀ w, x.length ≤ w → r w = w + d) (hlt : ∀ w, w < x.length → r w < y.length)
    (hv : ∀ w, w < x.length → y.getD (r w) false = x.getD w false) (gs : List Gate) :
    ∀ w, (wiresFrom (gs.map (rg r)) y).getD (r w) false = (wiresFrom gs x).getD w false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro w
    by_cases h : w < x.length
    · exact hv w h
    · have := hr w (by omega)
      simp only [List.map_nil]
      show y.getD (r w) false = x.getD w false
      rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  | append_singleton gs g ih =>
    intro w
    rw [List.map_append, List.map_singleton, wiresFrom_snoc, wiresFrom_snoc, getD_snoc,
      getD_snoc, length_wiresFrom, length_wiresFrom, List.length_map]
    by_cases hw : w = x.length + gs.length
    · have := hr w (by omega)
      rw [if_pos (by omega), if_pos hw]
      simp only [rg, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a _
      exact ih a
    · have : r w ≠ y.length + gs.length := by
        by_cases h : w < x.length
        · have := hlt w h; omega
        · have := hr w (by omega); omega
      rw [if_neg this, if_neg hw]
      exact ih w


theorem ofFn_getD {k : ℕ} (x : Fin k → Bool) (i : ℕ) (h : i < k) :
    (List.ofFn x).getD i false = x ⟨i, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

/-- The old input: bits zero and one merged by OR, the rest shifted down. -/
def merge {m : ℕ} (x : Fin (m + 2) → Bool) : Fin (m + 1) → Bool :=
  fun i => if h : i.val = 0 then (x 0 || x 1) else x ⟨i.val + 1, by omega⟩

theorem count_merge {m : ℕ} (x : Fin (m + 2) → Bool) :
    (List.ofFn x).count true =
      (List.ofFn (merge x)).count true + (if (x 0 && x 1) = true then 1 else 0) := by
  have e1 : List.ofFn x = x 0 :: x 1 :: List.ofFn (fun i : Fin m => x i.succ.succ) := by
    rw [List.ofFn_succ, List.ofFn_succ]; rfl
  have e2 : List.ofFn (merge x) = (x 0 || x 1) :: List.ofFn (fun i : Fin m => x i.succ.succ) := by
    rw [List.ofFn_succ]
    refine congrArg₂ List.cons (by simp [merge]) ?_
    congr 1
  rw [e1, e2]
  cases x 0 <;> cases x 1 <;> simp <;> omega

/-- The renaming of old wires. -/
def rn (m : ℕ) (w : ℕ) : ℕ := if w < m + 1 then (if w = 0 then m + 2 else w + 1) else w + 3

/-- The new gates. -/
def newGates (m : ℕ) (C : Circuit) : List Gate :=
  [⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [0, 1]⟩] ++ C.gates.map (rg (rn m)) ++
    [⟨GateOp.or, [rn m C.output, m + 3]⟩]

theorem key (m : ℕ) (C : Circuit) (x : Fin (m + 2) → Bool) :
    (Circuit.mk (newGates m C) (m + 4 + C.gates.length)).eval (List.ofFn x) =
      (C.eval (List.ofFn (merge x)) || (x 0 && x 1)) := by
  let x' := List.ofFn x
  have hx'l : x'.length = m + 2 := by simp [x']
  let Y := wiresFrom [⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [0, 1]⟩] x'
  have hY : Y = x' ++ [x 0 || x 1, x 0 && x 1] := by
    have h0 : x'.getD 0 false = x 0 := ofFn_getD x 0 (by omega)
    have h1 : x'.getD 1 false = x 1 := ofFn_getD x 1 (by omega)
    have hl : (x' ++ [x 0 || x 1]).length = m + 3 := by simp [hx'l]
    show wiresFrom [⟨GateOp.and, [0, 1]⟩] (x' ++ [GateOp.or.eval ([0, 1].map fun i => x'.getD i false)]) = _
    show (x' ++ [GateOp.or.eval ([0, 1].map fun i => x'.getD i false)]) ++
      [GateOp.and.eval ([0, 1].map fun i =>
        (x' ++ [GateOp.or.eval ([0, 1].map fun i => x'.getD i false)]).getD i false)] = _
    simp only [List.map_cons, List.map_nil, h0, h1, GateOp.eval, List.any_cons, List.any_nil,
      List.all_cons, List.all_nil, id, Bool.or_false, Bool.and_true]
    rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega), h0, h1]
    simp
  have hYl : Y.length = m + 4 := by rw [hY]; simp [hx'l]
  let xo := List.ofFn (merge x)
  have hxol : xo.length = m + 1 := by simp [xo]
  have hren := ren xo Y 3 (rn m) (by rw [hYl, hxol])
    (fun w hw => by rw [hxol] at hw; simp only [rn]; rw [if_neg (by omega)])
    (fun w hw => by rw [hxol] at hw; rw [hYl]; simp only [rn]; split_ifs <;> omega)
    (fun w hw => by
      rw [hxol] at hw
      simp only [xo]
      rw [ofFn_getD _ w hw, hY]
      simp only [rn, merge]
      rw [if_pos hw]
      by_cases h0 : w = 0
      · subst h0
        rw [if_pos rfl, dif_pos rfl, List.getD_append_right _ _ _ _ (by omega)]
        simp [hx'l]
      · rw [if_neg h0, dif_neg h0, List.getD_append _ _ _ _ (by omega)]
        exact ofFn_getD x (w + 1) (by omega)) C.gates
  show (wiresFrom (newGates m C) x').getD (m + 4 + C.gates.length) false = _
  simp only [newGates]
  rw [wiresFrom_snoc, getD_snoc, wiresFrom_append, length_wiresFrom, length_wiresFrom,
    List.length_map, hx'l, if_pos (by simp)]
  change GateOp.or.eval ([rn m C.output, m + 3].map fun i =>
    (wiresFrom (C.gates.map (rg (rn m))) Y).getD i false) = _
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
    Bool.or_false]
  rw [hren C.output, getD_prefix (C.gates.map (rg (rn m))) Y (m + 3) (by omega), hY,
    List.getD_append_right _ _ _ _ (by omega)]
  congr 1
  simp [hx'l]

end PEqualNP.Outside.L_meta_33612

open PEqualNP.Outside.L_meta_33612 in
theorem PEqualNP.Outside.L_meta_33612 : ∀ n s : ℕ, (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ (∀ x : Fin n → Bool, (List.ofFn x).count true = 2 → C.eval (List.ofFn x) = true) ∧ (∀ x : Fin n → Bool, (List.ofFn x).count true ≤ 1 → C.eval (List.ofFn x) = false)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.size ≤ s + 3 ∧ (∀ x : Fin (n + 1) → Bool, (List.ofFn x).count true = 2 → D.eval (List.ofFn x) = true) ∧ (∀ x : Fin (n + 1) → Bool, (List.ofFn x).count true ≤ 1 → D.eval (List.ofFn x) = false) := by
  intro n s ⟨C, hC, hs, h2, h1⟩
  rcases n with _ | m
  · refine ⟨⟨[], 1⟩, fun g hg => by simp at hg, by simp [PEqualNP.CircuitLowerBounds.Circuit.size], fun x hx => ?_,
      fun x _ => ?_⟩
    · have h := List.count_le_length (a := true) (l := List.ofFn x)
      rw [List.length_ofFn] at h; omega
    · show (List.ofFn x).getD 1 false = false
      rw [List.getD_eq_default _ _ (by simp)]
  · refine ⟨⟨newGates m C, m + 4 + C.gates.length⟩, ?_, ?_, fun x hx => ?_, fun x hx => ?_⟩
    · intro g hg
      simp only [newGates, List.mem_append, List.mem_cons, List.mem_singleton, List.mem_map,
        List.not_mem_nil, or_false] at hg
      rcases hg with ((rfl | rfl) | ⟨g', hg', rfl⟩) | rfl
      · exact ⟨by simp, by simp⟩
      · exact ⟨by simp, by simp⟩
      · exact ⟨(hC g' hg').1, by simp only [rg, List.length_map]; exact (hC g' hg').2⟩
      · exact ⟨by simp, by simp⟩
    · have : C.gates.length ≤ s := hs
      show (newGates m C).length ≤ s + 3
      simp [newGates]; omega
    · rw [key]
      have hc := count_merge x
      by_cases hb : (x 0 && x 1) = true
      · rw [hb]; simp
      · rw [if_neg hb] at hc
        rw [h2 (merge x) (by omega)]; simp
    · rw [key]
      have hc := count_merge x
      by_cases hb : (x 0 && x 1) = true
      · rw [if_pos hb] at hc
        have : (List.ofFn x).count true ≥ 2 := by
          have : (List.ofFn x).count true = (List.ofFn (merge x)).count true + 1 := hc
          rw [Bool.and_eq_true] at hb
          have e1 : List.ofFn x = x 0 :: x 1 :: List.ofFn (fun i : Fin m => x i.succ.succ) := by
            rw [List.ofFn_succ, List.ofFn_succ]; rfl
          rw [e1, hb.1, hb.2]; simp [List.count_cons]
        omega
      · rw [if_neg hb] at hc
        rw [h1 (merge x) (by omega)]
        simpa using hb
