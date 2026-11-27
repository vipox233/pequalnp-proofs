import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27725
open PEqualNP.CircuitLowerBounds

def occTarget (x : Fin 9 → Bool) : Bool :=
  ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
    (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))

def occFirst : Gate := ⟨.or, [0, 4]⟩

def occSecond : Gate := ⟨.or, [1, 8]⟩

def occProbe (m : ℕ) (i : Fin 9) : Bool := m.testBit i.val

lemma occWitness (i : Fin 9) : ∃ x y : Fin 9 → Bool,
    occTarget x ≠ occTarget y ∧ (x 0 || x 4) = (y 0 || y 4) ∧
    (x 1 || x 8) = (y 1 || y 8) ∧ (∀ j, j ≠ i → x j = y j) := by
  refine ⟨occProbe (![176, 264, 80, 132, 69, 66, 20, 12, 10] i),
    occProbe (![177, 266, 84, 140, 85, 98, 84, 140, 266] i), ?_⟩
  fin_cases i <;> decide

def occStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def occAgree (a b : List Bool) (i : ℕ) : Prop :=
  a.length = b.length ∧ ∀ j, j ≠ i → a.getD j false = b.getD j false

lemma occAppend {a b : List Bool} {i : ℕ} (h : occAgree a b i) (z : Bool) :
    occAgree (a ++ [z]) (b ++ [z]) i := by
  refine ⟨by simp [h.1], ?_⟩
  intro j hj
  by_cases hjl : j < a.length
  · rw [List.getD_append _ _ _ _ hjl, List.getD_append _ _ _ _ (h.1 ▸ hjl)]
    exact h.2 j hj
  · rw [List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by have := h.1; omega), h.1]

lemma occFold (gs : List Gate) {i : ℕ} (hn : i ∉ gs.flatMap Gate.inputs)
    {a b : List Bool} (h : occAgree a b i) :
    occAgree (gs.foldl occStep a) (gs.foldl occStep b) i := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    have hp : i ∉ g.inputs ∧ i ∉ gs.flatMap Gate.inputs := by simpa using hn
    have he : g.inputs.map (fun k => a.getD k false) = g.inputs.map (fun k => b.getD k false) := by
      apply List.map_congr_left
      intro k hk
      exact h.2 k (fun he => hp.1 (he ▸ hk))
    apply ih hp.2
    unfold occStep
    rw [he]
    exact occAppend h _

lemma occInitial (x : Fin 9 → Bool) (j : ℕ) (hj : j < 9) :
    (List.ofFn x).getD j false = x ⟨j, hj⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp only [List.getElem_ofFn]

lemma occPrefix (x : Fin 9 → Bool) :
    occStep (occStep (List.ofFn x) occFirst) occSecond =
      (List.ofFn x ++ [x 0 || x 4]) ++ [x 1 || x 8] := by
  simp [occStep, occFirst, occSecond, GateOp.eval]

lemma occTailInput (C : Circuit) (gs : List Gate) (hg : C.gates = occFirst :: occSecond :: gs)
    (hcomp : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = occTarget x)
    (hout : C.output + 1 = 9 + C.size) (i : Fin 9) :
    i.val ∈ gs.flatMap Gate.inputs := by
  by_contra hn
  obtain ⟨x, y, hxy, h04, h18, hsame⟩ := occWitness i
  have hbase : occAgree (List.ofFn x) (List.ofFn y) i.val := by
    refine ⟨by simp, ?_⟩
    intro j hji
    by_cases hj : j < 9
    · rw [occInitial x j hj, occInitial y j hj]
      exact hsame _ (fun h => hji (congrArg Fin.val h))
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  have hpre : occAgree (occStep (occStep (List.ofFn x) occFirst) occSecond)
      (occStep (occStep (List.ofFn y) occFirst) occSecond) i.val := by
    rw [occPrefix, occPrefix, h04, h18]
    exact occAppend (occAppend hbase _) _
  have ho : C.output ≠ i.val := by
    have hz : C.size = gs.length + 2 := by simp [Circuit.size, hg]
    have hi := i.isLt
    omega
  apply hxy
  rw [← hcomp, ← hcomp]
  change (C.gates.foldl occStep (List.ofFn x)).getD C.output false =
    (C.gates.foldl occStep (List.ofFn y)).getD C.output false
  rw [hg]
  exact (occFold gs hn hpre).2 _ ho

lemma occCap (gs : List Gate) (hf : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hh := hf g (by simp)
    have ht := ih (fun a ha => hf a (by simp [ha]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

lemma occSplit (C : Circuit) (h0 : C.gates.head? = some occFirst)
    (h1 : C.gates.tail.head? = some occSecond) :
    ∃ gs, C.gates = occFirst :: occSecond :: gs := by
  cases hg : C.gates with
  | nil => simp [hg] at h0
  | cons a t =>
    cases ht : t with
    | nil => simp [hg, ht] at h1
    | cons b gs =>
      have ha : a = occFirst := by simpa [hg] using h0
      have hb : b = occSecond := by simpa [hg, ht] using h1
      exact ⟨gs, by simp [ha, hb]⟩

lemma occRigidTail (C : Circuit) (gs : List Gate) (hg : C.gates = occFirst :: occSecond :: gs)
    (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (hout : C.output + 1 = 9 + C.size)
    (hlive : ∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs)
    (hinputs : ∀ i : Fin 9, i.val ∈ gs.flatMap Gate.inputs) :
    12 ≤ C.size := by
  let r := gs.flatMap Gate.inputs ++ [C.output]
  have hlen : C.size = gs.length + 2 := by simp [Circuit.size, hg]
  have hgs : ∀ g ∈ gs, g.inputs.length ≤ 2 := fun g hm => (hf g (by simp [hg, hm])).2
  have hsub : Finset.range (9 + C.size) ⊆ r.toFinset := by
    intro j hj
    have hb := Finset.mem_range.mp hj
    apply List.mem_toFinset.mpr
    by_cases hsmall : j < 9
    · exact List.mem_append_left _ (hinputs ⟨j, hsmall⟩)
    by_cases hlast : j = C.output
    · simp [r, hlast]
    have hidx : j - 9 < C.gates.length := by change j - 9 < C.size; omega
    let k : Fin C.gates.length := ⟨j - 9, hidx⟩
    have hjk : 9 + k.val = j := by dsimp [k]; omega
    have hnlast : k.val + 1 < C.gates.length := by change j - 9 + 1 < C.size; omega
    obtain ⟨n, _, hn⟩ := hlive k hnlast
    have hall : j ∈ C.gates.flatMap Gate.inputs :=
      List.mem_flatMap.mpr ⟨C.gates.get n, List.get_mem _ _, hjk ▸ hn⟩
    simp only [hg, List.flatMap_cons, occFirst, occSecond, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hall
    apply List.mem_append_left
    rcases hall with (h | h) | (h | h) | ha <;> omega
  have hcard : 9 + C.size ≤ r.toFinset.card := by
    simpa only [Finset.card_range] using Finset.card_le_card hsub
  have hcl := List.toFinset_card_le r
  have hrl : r.length = (gs.flatMap Gate.inputs).length + 1 := by simp [r]
  have hc := occCap gs hgs
  omega

end PEqualNP.Outside.L_meta_27725

open PEqualNP.Outside.L_meta_27725 in
theorem PEqualNP.Outside.L_meta_27725 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
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
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 8]⟩)) := by
  rintro ⟨C, hf, hs, hc, hout, _, _, hlive, h0, h1⟩
  obtain ⟨gs, hg⟩ := occSplit C h0 h1
  have hmin := occRigidTail C gs hg hf hout hlive (occTailInput C gs hg hc hout)
  omega
