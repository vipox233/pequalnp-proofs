import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27567
open PEqualNP.CircuitLowerBounds

private def target (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
  (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

private def high (v i : Fin 9) : Bool :=
  (([273, 266, 140, 266, 273, 161, 98, 161, 273] : List Nat).getD v.val 0).testBit i.val

private def low (v i : Fin 9) : Bool := if i = v then false else high v i

private theorem separates (v : Fin 9) : target (high v) ≠ target (low v) := by
  fin_cases v <;> decide

private theorem or_fixed (v : Fin 9) :
    (high v 0 || high v 4) = (low v 0 || low v 4) := by
  fin_cases v <;> decide

private theorem and_fixed (v : Fin 9) :
    (high v 2 && high v 6) = (low v 2 && low v 6) := by
  fin_cases v <;> decide

private def first : Gate := ⟨.or, [0, 4]⟩
private def second : Gate := ⟨.and, [2, 6]⟩

private def value (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

private def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [value g w]) w

private def warm (x : Fin 9 → Bool) : List Bool :=
  (List.ofFn x ++ [x 0 || x 4]) ++ [x 2 && x 6]

private theorem ofFn_getD {n : Nat} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

private theorem prefix_run (gs : List Gate) (out : Nat) (x : Fin 9 → Bool) :
    (Circuit.mk (first :: second :: gs) out).wires (List.ofFn x) = run gs (warm x) := by
  have hx (i : Fin 9) : (List.ofFn x ++ [x 0 || x 4]).getD i.val false = x i := by
    rw [List.getD_append _ _ _ _ (by simp), ofFn_getD]
  have h₀ : (List.ofFn x).getD 0 false = x 0 := ofFn_getD x 0
  have h₄ : (List.ofFn x).getD 4 false = x 4 := ofFn_getD x 4
  have h₂ : (List.ofFn x ++ [x 0 || x 4]).getD 2 false = x 2 := hx 2
  have h₆ : (List.ofFn x ++ [x 0 || x 4]).getD 6 false = x 6 := hx 6
  change run gs ((List.ofFn x ++ [value first (List.ofFn x)]) ++
    [value second (List.ofFn x ++ [value first (List.ofFn x)])]) = run gs (warm x)
  have hfirst : value first (List.ofFn x) = (x 0 || x 4) := by
    change ((List.ofFn x).getD 0 false || ((List.ofFn x).getD 4 false || false)) = _
    rw [h₀, h₄, Bool.or_false]
  have hsecond : value second (List.ofFn x ++ [x 0 || x 4]) = (x 2 && x 6) := by
    change ((List.ofFn x ++ [x 0 || x 4]).getD 2 false &&
      ((List.ofFn x ++ [x 0 || x 4]).getD 6 false && true)) = _
    rw [h₂, h₆, Bool.and_true]
  rw [hfirst, hsecond, warm]

private def Agree (v : Nat) (w w' : List Bool) : Prop :=
  w.length = w'.length ∧ ∀ i, i ≠ v → w.getD i false = w'.getD i false

private theorem agree_append {v : Nat} {w w' : List Bool} (h : Agree v w w')
    {a a' : Bool} (ha : a = a') : Agree v (w ++ [a]) (w' ++ [a']) := by
  refine ⟨by simpa using h.1, ?_⟩
  intro i hi
  by_cases hb : i < w.length
  · have hb' : i < w'.length := h.1 ▸ hb
    rw [List.getD_append _ _ _ _ hb, List.getD_append _ _ _ _ hb']
    exact h.2 i hi
  · have hb' : w'.length ≤ i := by rw [← h.1]; omega
    rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ hb', h.1, ha]

private theorem agree_warm (v : Fin 9) : Agree v.val (warm (high v)) (warm (low v)) := by
  have h : Agree v.val (List.ofFn (high v)) (List.ofFn (low v)) := by
    refine ⟨by simp, ?_⟩
    intro i hi
    by_cases hb : i < 9
    · let j : Fin 9 := ⟨i, hb⟩
      have hj : j ≠ v := fun he => hi (congrArg Fin.val he)
      change (List.ofFn (high v)).getD j.val false = (List.ofFn (low v)).getD j.val false
      rw [ofFn_getD, ofFn_getD]
      simp [low, hj]
    · rw [List.getD_eq_default _ _ (by simpa using (show 9 ≤ i by omega)),
        List.getD_eq_default _ _ (by simpa using (show 9 ≤ i by omega))]
  exact agree_append (agree_append h (or_fixed v)) (and_fixed v)

private theorem agree_run {v : Nat} {w w' : List Bool} (h : Agree v w w')
    (gs : List Gate) (hz : v ∉ gs.flatMap Gate.inputs) : Agree v (run gs w) (run gs w') := by
  induction gs generalizing w w' with
  | nil => exact h
  | cons g gs ih =>
    have hn : v ∉ g.inputs ∧ v ∉ gs.flatMap Gate.inputs := by simpa using hz
    have hv : value g w = value g w' := by
      apply congrArg g.op.eval
      apply List.map_congr_left
      intro i hi
      exact h.2 i (fun e => hn.1 (e ▸ hi))
    exact ih (agree_append h hv) hn.2

private theorem capacity (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hg := h g (by simp)
    have hs := ih (fun d hd => h d (by simp [hd]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

private theorem impossible (gs : List Gate) (out : Nat)
    (hsize : (first :: second :: gs).length ≤ 11)
    (hfan : ∀ g ∈ first :: second :: gs, g.inputs.length ≤ 2)
    (hout : out + 1 = 9 + (first :: second :: gs).length)
    (heval : ∀ x : Fin 9 → Bool, (Circuit.mk (first :: second :: gs) out).eval (List.ofFn x) = target x)
    (hlive : ∀ j : Fin (first :: second :: gs).length, j.val + 1 < (first :: second :: gs).length →
      ∃ k : Fin (first :: second :: gs).length, j.val < k.val ∧
        9 + j.val ∈ ((first :: second :: gs).get k).inputs) : False := by
  simp only [List.length_cons] at hsize hout
  have hsub : List.range (10 + gs.length) ⊆ gs.flatMap Gate.inputs := by
    intro i hi
    have hr := List.mem_range.mp hi
    by_cases hv : i < 9
    · let v : Fin 9 := ⟨i, hv⟩
      by_contra hn
      have ha := (agree_run (agree_warm v) gs hn).2 out (show out ≠ v.val by
        change out ≠ i
        omega)
      rw [← prefix_run gs out, ← prefix_run gs out] at ha
      change (Circuit.mk (first :: second :: gs) out).eval (List.ofFn (high v)) =
        (Circuit.mk (first :: second :: gs) out).eval (List.ofFn (low v)) at ha
      exact separates v ((heval (high v)).symm.trans (ha.trans (heval (low v))))
    · let j : Fin (first :: second :: gs).length := ⟨i - 9, by simp; omega⟩
      have hj : j.val + 1 < (first :: second :: gs).length := by
        change i - 9 + 1 < (first :: second :: gs).length
        simp only [List.length_cons]
        omega
      obtain ⟨k, _, hk⟩ := hlive j hj
      have hm : i ∈ (first :: second :: gs).flatMap Gate.inputs := by
        refine List.mem_flatMap.mpr ⟨_, List.get_mem _ k, ?_⟩
        have he : 9 + j.val = i := by change 9 + (i - 9) = i; omega
        simpa only [he] using hk
      simpa [first, second, show i ≠ 0 by omega, show i ≠ 2 by omega,
        show i ≠ 4 by omega, show i ≠ 6 by omega] using hm
  have hl := (List.nodup_range.subperm hsub).length_le
  simp only [List.length_range] at hl
  have hu := capacity gs (fun g hg => hfan g (by simp [hg]))
  omega

end PEqualNP.Outside.L_meta_27567

open PEqualNP.Outside.L_meta_27567

theorem PEqualNP.Outside.L_meta_27567 :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 6]⟩) := by
  rintro ⟨⟨gates, out⟩, hfan, hsize, heval, hout, _, _, hlive, hfirst, hsecond⟩
  cases gates with
  | nil => simp at hfirst
  | cons g gates =>
    cases gates with
    | nil => simp at hsecond
    | cons d gs =>
      have hg : g = first := Option.some.inj hfirst
      have hd : d = second := Option.some.inj hsecond
      subst g
      subst d
      exact impossible gs out hsize (fun g hg => (hfan g hg).2) hout heval hlive
