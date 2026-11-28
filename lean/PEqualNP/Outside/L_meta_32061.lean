import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_32061_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Finset

private def expand (p : ℕ) (a : Gate) (F : Finset ℕ) : Finset ℕ :=
  if p ∈ F then F.erase p ∪ a.inputs.toFinset else F

private def frontier (n : ℕ) : List Gate → Finset ℕ → Finset ℕ
  | [], F => F
  | a :: as, F => frontier n as (expand (n + as.length) a F)

private lemma expand_card (p : ℕ) (a : Gate) (F : Finset ℕ)
    (h : a.inputs.length ≤ 2) : (expand p a F).card ≤ F.card + 1 := by
  unfold expand
  split
  · rename_i hp
    have h₁ := Finset.card_union_le (F.erase p) a.inputs.toFinset
    have h₂ := List.toFinset_card_le a.inputs
    have h₃ := Finset.card_erase_add_one hp
    omega
  · omega

private lemma expand_card_small (p : ℕ) (a : Gate) (F : Finset ℕ)
    (h : a.inputs.length ≤ 1) : (expand p a F).card ≤ F.card := by
  unfold expand
  split
  · rename_i hp
    have h₁ := Finset.card_union_le (F.erase p) a.inputs.toFinset
    have h₂ := List.toFinset_card_le a.inputs
    have h₃ := Finset.card_erase_add_one hp
    omega
  · omega

private lemma frontier_card (n : ℕ) (gs : List Gate) (F : Finset ℕ)
    (h : ∀ a ∈ gs, a.inputs.length ≤ 2) :
    (frontier n gs F).card ≤ F.card + gs.length := by
  induction gs generalizing F with
  | nil => simp [frontier]
  | cons a as ih =>
    have ht : ∀ a ∈ as, a.inputs.length ≤ 2 := fun b hb => h b (List.mem_cons_of_mem _ hb)
    have h₁ := ih (expand (n + as.length) a F) ht
    have h₂ := expand_card (n + as.length) a F (h a (by simp))
    simp only [frontier, List.length_cons]
    omega

private lemma frontier_card_small (n : ℕ) (gs : List Gate) (F : Finset ℕ)
    (h : ∀ a ∈ gs, a.inputs.length ≤ 2)
    (hs : ∃ a ∈ gs, a.inputs.length ≤ 1) :
    (frontier n gs F).card + 1 ≤ F.card + gs.length := by
  induction gs generalizing F with
  | nil => simp at hs
  | cons a as ih =>
    have ht : ∀ a ∈ as, a.inputs.length ≤ 2 := fun b hb => h b (List.mem_cons_of_mem _ hb)
    simp only [frontier, List.length_cons]
    rcases hs with ⟨b, hb, hs⟩
    rcases List.mem_cons.mp hb with rfl | hb
    · have h₁ := frontier_card n as (expand (n + as.length) b F) ht
      have h₂ := expand_card_small (n + as.length) b F hs
      omega
    · have h₁ := ih (expand (n + as.length) a F) ht ⟨b, hb, hs⟩
      have h₂ := expand_card (n + as.length) a F (h a (by simp))
      omega

private def readsEarlier (n : ℕ) : List Gate → Prop
  | [] => True
  | a :: as => readsEarlier n as ∧ ∀ i ∈ a.inputs, i < n + as.length

private lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]

private lemma readsEarlier_of_readsBack (n : ℕ) (gs : List Gate)
    (h : ReadsBack n ⟨gs, 0⟩) : readsEarlier n gs.reverse := by
  induction gs using List.reverseRecOn with
  | nil => trivial
  | append_singleton gs a ih =>
    rw [List.reverse_append, List.reverse_singleton]
    change readsEarlier n gs.reverse ∧ ∀ i ∈ a.inputs, i < n + gs.reverse.length
    constructor
    · apply ih
      intro j hj i hi
      have hj' : j < (Circuit.mk (gs ++ [a]) 0).gates.length := by
        change j < (gs ++ [a]).length
        simp only [List.length_append, List.length_singleton]
        exact Nat.lt_succ_of_lt hj
      apply h j hj' i
      rw [gateAt_eq_getElem _ _ hj']
      change i ∈ (gs ++ [a])[j].inputs
      rw [List.getElem_append_left hj]
      rwa [gateAt_eq_getElem _ _ hj] at hi
    · intro i hi
      rw [List.length_reverse]
      have hj' : gs.length < (Circuit.mk (gs ++ [a]) 0).gates.length := by simp
      apply h gs.length hj' i
      rw [gateAt_eq_getElem _ _ hj']
      change i ∈ (gs ++ [a])[gs.length].inputs
      simpa [List.getElem_append_right (le_refl gs.length)] using hi

private lemma expand_lt {p : ℕ} {a : Gate} {F : Finset ℕ}
    (hF : ∀ i ∈ F, i < p + 1) (ha : ∀ i ∈ a.inputs, i < p) :
    ∀ i ∈ expand p a F, i < p := by
  intro i hi
  unfold expand at hi
  split at hi
  · rcases Finset.mem_union.mp hi with he | hin
    · have hn := (Finset.mem_erase.mp he).1
      have hlt := hF i (Finset.mem_erase.mp he).2
      omega
    · exact ha i (List.mem_toFinset.mp hin)
  · rename_i hn
    have hlt := hF i hi
    have hne : i ≠ p := by rintro rfl; exact hn hi
    omega

private lemma frontier_lt {n : ℕ} (gs : List Gate) (F : Finset ℕ)
    (hgs : readsEarlier n gs) (hF : ∀ i ∈ F, i < n + gs.length) :
    ∀ i ∈ frontier n gs F, i < n := by
  induction gs generalizing F with
  | nil => simpa [frontier] using hF
  | cons a as ih =>
    exact ih _ hgs.1 (expand_lt hF hgs.2)

private def reverseWires (x : List Bool) : List Gate → List Bool
  | [] => x
  | a :: as =>
    let w := reverseWires x as
    w ++ [a.op.eval (a.inputs.map fun i => w.getD i false)]

private lemma reverseWires_eq (x : List Bool) (gs : List Gate) :
    reverseWires x gs = (Circuit.mk gs.reverse 0).wires x := by
  induction gs with
  | nil => rfl
  | cons a as ih =>
    simp only [reverseWires, List.reverse_cons, ih, Circuit.wires, List.foldl_append,
      List.foldl_cons, List.foldl_nil]

private lemma reverseWires_length (x : List Bool) (gs : List Gate) :
    (reverseWires x gs).length = x.length + gs.length := by
  induction gs with
  | nil => simp [reverseWires]
  | cons a as ih => simp [reverseWires, ih, Nat.add_assoc]

private lemma getD_reverseWires_last {n : ℕ} {x : List Bool} (hx : x.length = n)
    (a : Gate) (as : List Gate) :
    (reverseWires x (a :: as)).getD (n + as.length) false =
      a.op.eval (a.inputs.map fun i => (reverseWires x as).getD i false) := by
  have hlen := reverseWires_length x as
  rw [hx] at hlen
  rw [← hlen]
  simp only [reverseWires, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

private lemma getD_reverseWires_earlier {n i : ℕ} {x : List Bool} (hx : x.length = n)
    (a : Gate) (as : List Gate) (hi : i < n + as.length) :
    (reverseWires x (a :: as)).getD i false = (reverseWires x as).getD i false := by
  have hlen := reverseWires_length x as
  rw [hx] at hlen
  simp only [reverseWires, List.getD_eq_getElem?_getD, List.getElem?_append_left (hlen ▸ hi)]

private lemma frontier_congr {n : ℕ} (gs : List Gate) (F : Finset ℕ)
    (hgs : readsEarlier n gs) (hF : ∀ i ∈ F, i < n + gs.length)
    {x y : List Bool} (hx : x.length = n) (hy : y.length = n)
    (heq : ∀ i ∈ frontier n gs F, x.getD i false = y.getD i false) :
    ∀ i ∈ F, (reverseWires x gs).getD i false = (reverseWires y gs).getD i false := by
  induction gs generalizing F with
  | nil => exact heq
  | cons a as ih =>
    have ht := ih _ hgs.1 (expand_lt hF hgs.2) heq
    intro i hi
    by_cases he : i = n + as.length
    · subst i
      rw [getD_reverseWires_last hx, getD_reverseWires_last hy]
      congr 1
      apply List.map_congr_left
      intro j hj
      apply ht
      exact by simp [expand, hi, hj]
    · have hil := hF i hi
      simp only [List.length_cons] at hil
      have hil' : i < n + as.length := by omega
      rw [getD_reverseWires_earlier hx _ _ hil', getD_reverseWires_earlier hy _ _ hil']
      apply ht
      by_cases hp : n + as.length ∈ F <;> simp [expand, hp, hi, he]

private lemma frontier_or {n : ℕ} (gs : List Gate) (F : Finset ℕ)
    (hgs : readsEarlier n gs) (hF : ∀ i ∈ F, i < n + gs.length)
    (hor : ∀ a ∈ gs, a.op = .or)
    {x : List Bool} (hx : x.length = n) :
    (∃ i ∈ F, (reverseWires x gs).getD i false = true) ↔
      ∃ i ∈ frontier n gs F, x.getD i false = true := by
  induction gs generalizing F with
  | nil => rfl
  | cons a as ih =>
    let p := n + as.length
    have hlt : ∀ i ∈ F, i < p + 1 := hF
    have hread : ∀ i ∈ a.inputs, i < p := hgs.2
    have hlast : (reverseWires x (a :: as)).getD p false = true ↔
        ∃ i ∈ a.inputs, (reverseWires x as).getD i false = true := by
      rw [getD_reverseWires_last hx, hor a (by simp)]
      simp [GateOp.eval, List.any_eq_true]
    simp only [frontier]
    rw [← ih (expand p a F) hgs.1 (expand_lt hlt hread)
      (fun b hb => hor b (List.mem_cons_of_mem _ hb))]
    by_cases hp : p ∈ F
    · simp only [expand, ite_eq_left hp]
      constructor
      · rintro ⟨i, hi, hv⟩
        by_cases he : i = p
        · subst i
          obtain ⟨j, hj, hjv⟩ := hlast.mp hv
          exact ⟨j, Finset.mem_union_right _ (List.mem_toFinset.mpr hj), hjv⟩
        · have hi' : i < p := by have := hlt i hi; omega
          rw [getD_reverseWires_earlier hx _ _ hi'] at hv
          exact ⟨i, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨he, hi⟩), hv⟩
      · rintro ⟨i, hi, hv⟩
        rcases Finset.mem_union.mp hi with hi | hi
        · obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hi
          have hi' : i < p := by have := hlt i hm; omega
          exact ⟨i, hm, (getD_reverseWires_earlier hx _ _ hi').trans hv⟩
        · exact ⟨p, hp, hlast.mpr ⟨i, List.mem_toFinset.mp hi, hv⟩⟩
    · simp only [expand, ite_eq_right hp]
      apply exists_congr
      intro i
      refine and_congr_right fun hi => ?_
      have hne : i ≠ p := by rintro rfl; exact hp hi
      have hi' : i < p := by have := hlt i hi; omega
      rw [getD_reverseWires_earlier hx _ _ hi']

private def inputsUsed (n : ℕ) (C : Circuit) : Finset ℕ :=
  frontier n C.gates.reverse {C.output}

private lemma readsEarlier_circuit {n : ℕ} (C : Circuit) (h : ReadsBack n C) :
    readsEarlier n C.gates.reverse :=
  readsEarlier_of_readsBack n C.gates h

private lemma input_used_lt {n : ℕ} (C : Circuit) (h : ReadsBack n C)
    (ho : C.output < n + C.size) :
    ∀ i ∈ inputsUsed n C, i < n := by
  apply frontier_lt C.gates.reverse {C.output} (readsEarlier_circuit C h)
  simpa [Circuit.size] using ho

private lemma inputsUsed_card {n : ℕ} (C : Circuit)
    (h : ∀ a ∈ C.gates, a.inputs.length ≤ 2) :
    (inputsUsed n C).card ≤ C.size + 1 := by
  have h' : ∀ a ∈ C.gates.reverse, a.inputs.length ≤ 2 := by simpa using h
  simpa [inputsUsed, Circuit.size, Nat.add_comm] using
    frontier_card n C.gates.reverse {C.output} h'

private lemma inputsUsed_card_small {n : ℕ} (C : Circuit)
    (h : ∀ a ∈ C.gates, a.inputs.length ≤ 2)
    (hs : ∃ a ∈ C.gates, a.inputs.length ≤ 1) :
    (inputsUsed n C).card ≤ C.size := by
  have h' : ∀ a ∈ C.gates.reverse, a.inputs.length ≤ 2 := by simpa using h
  have hs' : ∃ a ∈ C.gates.reverse, a.inputs.length ≤ 1 := by simpa using hs
  have hc := frontier_card_small n C.gates.reverse {C.output} h' hs'
  simp only [inputsUsed, Circuit.size]
  simp only [List.length_reverse, Finset.card_singleton] at hc
  omega

private lemma eval_eq_of_eq_on_frontier {n : ℕ} (C : Circuit)
    (h : ReadsBack n C) (ho : C.output < n + C.size)
    {x y : List Bool} (hx : x.length = n) (hy : y.length = n)
    (heq : ∀ i ∈ inputsUsed n C, x.getD i false = y.getD i false) :
    C.eval x = C.eval y := by
  have hout : ∀ i ∈ ({C.output} : Finset ℕ), i < n + C.gates.reverse.length := by
    simpa [Circuit.size] using ho
  have he := frontier_congr C.gates.reverse {C.output}
    (readsEarlier_circuit C h) hout hx hy heq C.output (by simp)
  simpa [Circuit.eval, reverseWires_eq, Circuit.wires] using he

private lemma eval_or_iff {n : ℕ} (C : Circuit) (h : ReadsBack n C)
    (ho : C.output < n + C.size) (hor : ∀ a ∈ C.gates, a.op = .or)
    {x : List Bool} (hx : x.length = n) :
    C.eval x = true ↔ ∃ i ∈ inputsUsed n C, x.getD i false = true := by
  have hout : ∀ i ∈ ({C.output} : Finset ℕ), i < n + C.gates.reverse.length := by
    simpa [Circuit.size] using ho
  have hor' : ∀ a ∈ C.gates.reverse, a.op = .or := by simpa using hor
  have he := frontier_or C.gates.reverse {C.output} (readsEarlier_circuit C h) hout hor' hx
  simpa [Circuit.eval, reverseWires_eq, Circuit.wires, inputsUsed] using he

private def namedRows (N : ℕ) (F : Finset ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun x => x.val ∈ F

private def namedCols (N : ℕ) (F : Finset ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun y => N + y.val ∈ F

private lemma mem_namedRows {N : ℕ} {F : Finset ℕ} {x : Fin N} :
    x ∈ namedRows N F ↔ x.val ∈ F := by simp [namedRows]

private lemma mem_namedCols {N : ℕ} {F : Finset ℕ} {y : Fin N} :
    y ∈ namedCols N F ↔ N + y.val ∈ F := by simp [namedCols]

private lemma named_card (N : ℕ) (F : Finset ℕ) :
    (namedRows N F).card + (namedCols N F).card = (F.filter (· < N + N)).card := by
  let rowNames := (namedRows N F).image Fin.val
  let colNames := (namedCols N F).image fun y => N + y.val
  have hDisj : Disjoint rowNames colNames := by
    rw [Finset.disjoint_left]
    intro i hiR hiS
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hiR
    obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hiS
    have hlt := x.isLt
    omega
  have hUnion : rowNames ∪ colNames = F.filter (· < N + N) := by
    ext i
    rw [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (hi | hi)
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
        exact ⟨mem_namedRows.mp hx, by have := x.isLt; omega⟩
      · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hi
        exact ⟨mem_namedCols.mp hy, by have := y.isLt; omega⟩
    · rintro ⟨hi, hlt⟩
      by_cases h : i < N
      · exact Or.inl (Finset.mem_image.mpr ⟨⟨i, h⟩, mem_namedRows.mpr hi, rfl⟩)
      · have he : N + (i - N) = i := by omega
        exact Or.inr (Finset.mem_image.mpr
          ⟨⟨i - N, by omega⟩, mem_namedCols.mpr (he ▸ hi), he⟩)
  rw [← hUnion, Finset.card_union_of_disjoint hDisj]
  congr 1
  · exact (Finset.card_image_of_injective _ Fin.val_injective).symm
  · exact (Finset.card_image_of_injective _ (fun _ _ h => Fin.ext (Nat.add_left_cancel h))).symm

private lemma named_card_le (N : ℕ) (F : Finset ℕ) :
    (namedRows N F).card + (namedCols N F).card ≤ F.card := by
  rw [named_card]
  exact Finset.card_le_card (Finset.filter_subset _ _)

private lemma lt_of_named_card_eq {N : ℕ} {F : Finset ℕ}
    (h : F.card ≤ (namedRows N F).card + (namedCols N F).card) :
    ∀ i ∈ F, i < N + N := by
  rw [named_card] at h
  have he : F.filter (· < N + N) = F :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) h
  intro i hi
  have hmem : i ∈ F.filter (· < N + N) := he.symm ▸ hi
  exact (Finset.mem_filter.mp hmem).2

private lemma oneEach_append_len {N h : ℕ} (x y : Fin N) (w : Fin h → Bool) :
    (oneEach x y ++ List.ofFn w).length = N + N + h := by
  simp [oneEach]; omega

private lemma oneEach_append_getD {N h : ℕ} (x y : Fin N) (w : Fin h → Bool) (i : ℕ)
    (hi : i < N + N + h) :
    (oneEach x y ++ List.ofFn w).getD i false =
      if h1 : i < N then decide ((⟨i, h1⟩ : Fin N) = x)
      else if h2 : i < N + N then decide ((⟨i - N, by omega⟩ : Fin N) = y)
      else w ⟨i - (N + N), by omega⟩ := by
  simp only [oneEach, List.getD_eq_getElem?_getD]
  by_cases h1 : i < N
  · have hlt1 : i < (List.ofFn (fun j : Fin N => decide (j = x)) ++
        List.ofFn (fun j : Fin N => decide (j = y))).length := by simp; omega
    rw [List.getElem?_append_left hlt1, List.getElem?_append_left (by simp; omega)]
    simp [h1]
  · by_cases h2 : i < N + N
    · have hlt1 : i < (List.ofFn (fun j : Fin N => decide (j = x)) ++
          List.ofFn (fun j : Fin N => decide (j = y))).length := by simp; omega
      have hltN : i - N < N := by omega
      rw [List.getElem?_append_left hlt1, List.getElem?_append_right (by simp; omega)]
      simp [h1, h2, hltN]
    · have hlth : i - (N + N) < h := by omega
      rw [List.getElem?_append_right (by simp; omega)]
      simp [h1, h2, hlth]

private def gridZero (N : ℕ) {h : ℕ} (w : Fin h → Bool) : List Bool :=
  List.replicate (N + N) false ++ List.ofFn w

private lemma gridZero_len (N : ℕ) {h : ℕ} (w : Fin h → Bool) :
    (gridZero N w).length = N + N + h := by simp [gridZero]

private lemma gridZero_getD {N h : ℕ} (w : Fin h → Bool) (i : ℕ) (hi : i < N + N + h) :
    (gridZero N w).getD i false =
      if hGrid : i < N + N then false else w ⟨i - (N + N), by omega⟩ := by
  by_cases hGrid : i < N + N
  · rw [dite_eq_left hGrid, gridZero, List.getD_append _ _ _ _ (by simpa using hGrid)]
    exact List.getD_replicate _ hGrid
  · have hs : i - (N + N) < h := by omega
    rw [dite_eq_right hGrid, gridZero, List.getD_append_right _ _ _ _ (by simp; omega)]
    simp [hs]

private lemma gridZero_agrees {N h : ℕ} {F : Finset ℕ} (x y : Fin N) (w : Fin h → Bool)
    (hx : x ∉ namedRows N F) (hy : y ∉ namedCols N F)
    (i : ℕ) (hiF : i ∈ F) (hi : i < N + N + h) :
    (oneEach x y ++ List.ofFn w).getD i false = (gridZero N w).getD i false := by
  rw [oneEach_append_getD _ _ _ _ hi, gridZero_getD _ _ hi]
  by_cases hRow : i < N
  · have hGrid : i < N + N := by omega
    have hne : i ≠ x.val := fun he => hx (mem_namedRows.mpr (he ▸ hiF))
    simp [hRow, hGrid, Fin.ext_iff, hne]
  · by_cases hGrid : i < N + N
    · have hne : i - N ≠ y.val := by
        intro h
        have he : i = N + y.val := by omega
        exact hy (mem_namedCols.mpr (he ▸ hiF))
      simp [hRow, hGrid, Fin.ext_iff, hne]
    · simp [hRow, hGrid]

private lemma gridInput_true_iff {N h : ℕ} (x y : Fin N) (w : Fin h → Bool)
    (i : ℕ) (hi : i < N + N + h) (hGridSeed : i < N + N ∨ ∀ j, w j = false) :
    (oneEach x y ++ List.ofFn w).getD i false = true ↔ i = x.val ∨ i = N + y.val := by
  rw [oneEach_append_getD _ _ _ _ hi]
  by_cases hRow : i < N
  · simp [hRow, Fin.ext_iff]
    omega
  · by_cases hGrid : i < N + N
    · have hx := x.isLt
      simp [hRow, hGrid, Fin.ext_iff]
      omega
    · have hs := hGridSeed.resolve_left hGrid
      have hx := x.isLt
      have hy := y.isLt
      simp [hRow, hGrid, hs]
      omega

private lemma gridInput_true_exists_iff {N h : ℕ} {F : Finset ℕ} (x y : Fin N)
    (w : Fin h → Bool) (hInput : ∀ i ∈ F, i < N + N + h)
    (hGridSeed : (∀ i ∈ F, i < N + N) ∨ ∀ j, w j = false) :
    (∃ i ∈ F, (oneEach x y ++ List.ofFn w).getD i false = true) ↔
      x ∈ namedRows N F ∨ y ∈ namedCols N F := by
  have hBit : ∀ i ∈ F, (oneEach x y ++ List.ofFn w).getD i false = true ↔
      i = x.val ∨ i = N + y.val := by
    intro i hi
    exact gridInput_true_iff x y w i (hInput i hi) (hGridSeed.imp (fun h => h i hi) id)
  constructor
  · rintro ⟨i, hi, hTrue⟩
    rcases (hBit i hi).mp hTrue with rfl | rfl
    · exact Or.inl (mem_namedRows.mpr hi)
    · exact Or.inr (mem_namedCols.mpr hi)
  · rintro (hx | hy)
    · have hi := mem_namedRows.mp hx
      exact ⟨x.val, hi, (hBit _ hi).mpr (Or.inl rfl)⟩
    · have hi := mem_namedCols.mp hy
      exact ⟨N + y.val, hi, (hBit _ hi).mpr (Or.inr rfl)⟩

private def cellArea {N : ℕ} (H : Fin N → Fin N → Bool) : ℕ :=
  ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => H z.1 z.2 = true)).card

private theorem cellArea_le_lines {N g : ℕ} (H : Fin N → Fin N → Bool)
    (R S : Finset (Fin N)) (hc : R.card + S.card ≤ g)
    (hcover : ∀ x y, H x y = true → x ∈ R ∨ y ∈ S) :
    cellArea H ≤ g * N := by
  let rowCells := R ×ˢ (Finset.univ : Finset (Fin N))
  let colCells := (Finset.univ : Finset (Fin N)) ×ˢ S
  have hs : (Finset.univ.filter (fun z : Fin N × Fin N => H z.1 z.2 = true)) ⊆
      rowCells ∪ colCells := by
    intro z hz
    rcases hcover z.1 z.2 (Finset.mem_filter.mp hz).2 with hR | hS
    · exact Finset.mem_union_left _ (Finset.mem_product.mpr ⟨hR, Finset.mem_univ _⟩)
    · exact Finset.mem_union_right _ (Finset.mem_product.mpr ⟨Finset.mem_univ _, hS⟩)
  calc
    cellArea H ≤ (rowCells ∪ colCells).card := Finset.card_le_card hs
    _ ≤ rowCells.card + colCells.card := Finset.card_union_le _ _
    _ = (R.card + S.card) * N := by
      simp only [rowCells, colCells, Finset.card_product, Finset.card_univ, Fintype.card_fin]
      rw [Nat.add_mul, Nat.mul_comm N S.card]
    _ ≤ g * N := Nat.mul_le_mul_right _ hc

private theorem cellArea_le_of_unnamed_false {N g : ℕ} (H : Fin N → Fin N → Bool)
    (R S : Finset (Fin N)) (hc : R.card + S.card ≤ g)
    (h : ∀ x y, x ∉ R → y ∉ S → H x y = false) : cellArea H ≤ g * N := by
  apply cellArea_le_lines H R S hc
  intro x y hxy
  by_cases hx : x ∈ R
  · exact Or.inl hx
  · right
    by_contra hy
    exact Bool.noConfusion (hxy.symm.trans (h x y hx hy))

private theorem cellArea_ge_of_unnamed_true {N g : ℕ} (H : Fin N → Fin N → Bool)
    (R S : Finset (Fin N)) (hc : R.card + S.card ≤ g)
    (h : ∀ x y, x ∉ R → y ∉ S → H x y = true) : N * (N - g) ≤ cellArea H := by
  let rejected : Finset (Fin N × Fin N) :=
    Finset.univ.filter fun z => (!H z.1 z.2) = true
  have hreject : rejected.card ≤ g * N :=
    cellArea_le_of_unnamed_false (fun x y => !H x y) R S hc (by
      intro x y hx hy
      rw [h x y hx hy]
      rfl)
  have haccept : cellArea H = rejectedᶜ.card := by
    unfold cellArea
    congr 1
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl, rejected]
    cases H z.1 z.2 <;> simp
  rw [haccept, Finset.card_compl, Fintype.card_prod, Fintype.card_fin,
    Nat.mul_sub_left_distrib, Nat.mul_comm N g]
  exact Nat.sub_le_sub_left hreject _

private theorem cellArea_lines_gt {N g : ℕ} (H : Fin N → Fin N → Bool)
    (R S : Finset (Fin N)) (b : Bool)
    (hConst : ∀ x y, x ∉ R → y ∉ S → H x y = b)
    (hLower : g * N < cellArea H) (hUpper : cellArea H < N * (N - g)) :
    g < R.card + S.card := by
  by_contra! hc
  cases b
  · exact (not_le_of_gt hLower) (cellArea_le_of_unnamed_false H R S hc hConst)
  · exact (not_le_of_gt hUpper) (cellArea_ge_of_unnamed_true H R S hc hConst)

private lemma eval_seed_eq {N h : ℕ} (C : Circuit)
    (hBack : ReadsBack (N + N + h) C) (hOut : C.output < N + N + h + C.size)
    (hData : ∀ i ∈ inputsUsed (N + N + h) C, i < N + N)
    (w w' : Fin h → Bool) (x y : Fin N) :
    C.eval (oneEach x y ++ List.ofFn w) = C.eval (oneEach x y ++ List.ofFn w') := by
  apply eval_eq_of_eq_on_frontier C hBack hOut (oneEach_append_len x y w)
    (oneEach_append_len x y w')
  intro i hi
  have hd := hData i hi
  apply Bool.eq_iff_iff.mpr
  rw [gridInput_true_iff x y w i (by omega) (Or.inl hd),
      gridInput_true_iff x y w' i (by omega) (Or.inl hd)]

private theorem saturate {N g h : ℕ} (C : Circuit)
    (hBack : ReadsBack (N + N + h) C) (hOut : C.output < N + N + h + C.size)
    (hGates : ∀ a ∈ C.gates, a.inputs.length ≤ 2 ∧
      (a.op = .and ∨ a.op = .or ∨ (a.op = .not ∧ a.inputs.length = 1)))
    (hSize : C.size ≤ g) (w : Fin h → Bool)
    (hLower : g * N < cellArea (fun x y : Fin N => C.eval (oneEach x y ++ List.ofFn w)))
    (hUpper : cellArea (fun x y : Fin N => C.eval (oneEach x y ++ List.ofFn w)) < N * (N-g)) :
    let F := inputsUsed (N+N+h) C
    (namedRows N F).card + (namedCols N F).card = g + 1 ∧
      (∀ i ∈ F, i < N+N) ∧
      (∀ a ∈ C.gates, a.inputs.length = 2 ∧ (a.op = .and ∨ a.op = .or)) := by
  dsimp only
  let F := inputsUsed (N+N+h) C
  let R := namedRows N F
  let S := namedCols N F
  let baseline := gridZero N w
  have hNames : g < R.card + S.card := by
    apply cellArea_lines_gt _ R S (C.eval baseline) _ hLower hUpper
    intro x y hx hy
    apply eval_eq_of_eq_on_frontier C hBack hOut (oneEach_append_len x y w) (gridZero_len N w)
    intro i hi
    exact gridZero_agrees x y w hx hy i hi (input_used_lt C hBack hOut i hi)
  have hFan : ∀ a ∈ C.gates, a.inputs.length ≤ 2 := fun a ha => (hGates a ha).1
  have hSizeF : F.card ≤ C.size + 1 := inputsUsed_card C hFan
  have hBound : R.card + S.card ≤ F.card := named_card_le N F
  have hExact : R.card + S.card = g + 1 := by omega
  have hData : ∀ i ∈ F, i < N+N := lt_of_named_card_eq (by
    change F.card ≤ R.card + S.card
    omega)
  refine ⟨hExact, hData, fun a ha => ?_⟩
  have hBinary : a.inputs.length = 2 := by
    by_contra hne
    have hle : a.inputs.length ≤ 1 := by have := hFan a ha; omega
    have hSave : F.card ≤ C.size := inputsUsed_card_small C hFan ⟨a, ha, hle⟩
    omega
  refine ⟨hBinary, ?_⟩
  rcases (hGates a ha).2 with hop | hop | ⟨_, hlen⟩
  · exact Or.inl hop
  · exact Or.inr hop
  · omega

private def pruneGate (a : Gate) : Gate :=
  match a.op with
  | .and => ⟨.or, a.inputs.take 1⟩
  | _ => a

private theorem pruneGate_inputs_subset (a : Gate) : (pruneGate a).inputs ⊆ a.inputs := by
  cases h : a.op <;> simp [pruneGate, h, List.take_subset]

private theorem prune_readsBack {n o : ℕ} {gs : List Gate}
    (h : ReadsBack n (⟨gs, o⟩ : Circuit)) :
    ReadsBack n (⟨gs.map pruneGate, o⟩ : Circuit) := by
  intro j hj i hi
  change j < (gs.map pruneGate).length at hj
  have hj' : j < gs.length := by simpa using hj
  change i ∈ ((gs.map pruneGate).getD j ⟨.or, []⟩).inputs at hi
  rw [List.getD_eq_getElem _ _ hj, List.getElem_map] at hi
  have hi' := pruneGate_inputs_subset gs[j] hi
  apply h j hj' i
  change i ∈ (gs.getD j ⟨.or, []⟩).inputs
  rwa [List.getD_eq_getElem _ _ hj']

private theorem prune_gate_bounds (a : Gate) (hInputs : a.inputs.length ≤ 2)
    (hOp : a.op = .and ∨ a.op = .or) :
    (pruneGate a).op = .or ∧ (pruneGate a).inputs.length ≤ 2 := by
  rcases hOp with h | h
  · simp [pruneGate, h, List.length_take]
  · simpa [pruneGate, h] using hInputs

private theorem prune_gate_unary (a : Gate) (hOp : a.op = .and) :
    (pruneGate a).inputs.length ≤ 1 := by
  simp [pruneGate, hOp, List.length_take]

private theorem prune_small_gate {gs : List Gate} (h : ∃ a ∈ gs, a.op = .and) :
    ∃ b ∈ gs.map pruneGate, b.inputs.length ≤ 1 := by
  obtain ⟨a, ha, hOp⟩ := h
  exact ⟨pruneGate a, List.mem_map.mpr ⟨a, ha, rfl⟩, prune_gate_unary a hOp⟩

private def pruneGateValue (xs : List Bool) (a : Gate) : Bool :=
  a.op.eval (a.inputs.map fun i => xs.getD i false)

private theorem prune_eval_compare_aux (f : Gate → Gate) (gs : List Gate)
    (hGate : ∀ a ∈ gs, ∀ xs ys : List Bool,
      (∀ i, xs.getD i false ≤ ys.getD i false) →
      pruneGateValue xs a ≤ pruneGateValue ys (f a))
    (xs ys : List Bool) (hLen : xs.length = ys.length)
    (hVal : ∀ i, xs.getD i false ≤ ys.getD i false) (o : ℕ) :
    (⟨gs, o⟩ : Circuit).eval xs ≤ (⟨gs.map f, o⟩ : Circuit).eval ys := by
  induction gs generalizing xs ys with
  | nil => exact hVal o
  | cons a gs ih =>
    change (⟨gs, o⟩ : Circuit).eval (xs ++ [pruneGateValue xs a]) ≤
      (⟨gs.map f, o⟩ : Circuit).eval (ys ++ [pruneGateValue ys (f a)])
    apply ih (fun b hb => hGate b (List.mem_cons_of_mem _ hb))
    · simpa using hLen
    · intro i
      by_cases hi : i < xs.length
      · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (hLen ▸ hi)]
        exact hVal i
      · have hLe : xs.length ≤ i := Nat.le_of_not_gt hi
        rw [List.getD_append_right _ _ _ _ hLe,
          List.getD_append_right _ _ _ _ (hLen ▸ hLe), hLen]
        cases i - ys.length with
        | zero => exact hGate a (by simp) xs ys hVal
        | succ j => simp

private theorem gateValue_mono_and_or (a : Gate) (hOp : a.op = .and ∨ a.op = .or)
    (xs ys : List Bool) (hVal : ∀ i, xs.getD i false ≤ ys.getD i false) :
    pruneGateValue xs a ≤ pruneGateValue ys a := by
  apply Bool.le_iff_imp.mpr
  rcases hOp with h | h
  · simp only [pruneGateValue, h, GateOp.eval, List.all_map, List.all_eq_true,
      Function.comp_apply, id_eq]
    exact fun hAll i hi => Bool.le_iff_imp.mp (hVal i) (hAll i hi)
  · simp only [pruneGateValue, h, GateOp.eval, List.any_map, List.any_eq_true,
      Function.comp_apply, id_eq]
    rintro ⟨i, hi, hb⟩
    exact ⟨i, hi, Bool.le_iff_imp.mp (hVal i) hb⟩

private theorem prune_eval (gs : List Gate)
    (hOp : ∀ a ∈ gs, a.op = .and ∨ a.op = .or)
    (hNonempty : ∀ a ∈ gs, a.op = .and → a.inputs ≠ [])
    (xs : List Bool) (o : ℕ) :
    (⟨gs, o⟩ : Circuit).eval xs ≤ (⟨gs.map pruneGate, o⟩ : Circuit).eval xs := by
  apply prune_eval_compare_aux pruneGate gs _ xs xs rfl (fun _ => le_rfl) o
  intro a ha us vs hVal
  refine (gateValue_mono_and_or a (hOp a ha) us vs hVal).trans ?_
  rcases hOp a ha with h | h
  · cases hInputs : a.inputs with
    | nil => exact (hNonempty a ha h hInputs).elim
    | cons i is =>
      apply Bool.le_iff_imp.mpr
      simp only [pruneGateValue, pruneGate, h, hInputs, GateOp.eval, List.all_map,
        List.all_eq_true, Function.comp_apply, id_eq]
      exact fun hAll => by simpa using hAll i (by simp)
  · simp [pruneGate, h]

private theorem prune_eval_binary (gs : List Gate)
    (hOp : ∀ a ∈ gs, a.op = .and ∨ a.op = .or)
    (hBinary : ∀ a ∈ gs, a.inputs.length = 2)
    (xs : List Bool) (o : ℕ) :
    (⟨gs, o⟩ : Circuit).eval xs ≤ (⟨gs.map pruneGate, o⟩ : Circuit).eval xs := by
  apply prune_eval gs hOp _ xs o
  intro a ha _ hEmpty
  simpa [hEmpty] using hBinary a ha

private lemma eval_or_lines {N h : ℕ} (C : Circuit)
    (hBack : ReadsBack (N+N+h) C) (hOut : C.output < N+N+h+C.size)
    (hOr : ∀ a ∈ C.gates, a.op = .or) (w : Fin h → Bool)
    (hData : (∀ i ∈ inputsUsed (N+N+h) C, i < N+N) ∨ ∀ i, w i = false)
    (x y : Fin N) :
    C.eval (oneEach x y ++ List.ofFn w) =
      decide (x ∈ namedRows N (inputsUsed (N+N+h) C) ∨
        y ∈ namedCols N (inputsUsed (N+N+h) C)) := by
  apply Bool.eq_iff_iff.mpr
  rw [eval_or_iff C hBack hOut hOr (oneEach_append_len x y w), decide_eq_true_eq]
  exact gridInput_true_exists_iff x y w (input_used_lt C hBack hOut) hData

private theorem whole_lines {N g h : ℕ} (C : Circuit)
    (hBack : ReadsBack (N+N+h) C) (hOut : C.output < N+N+h+C.size)
    (hGates : ∀ a ∈ C.gates, a.inputs.length ≤ 2 ∧
      (a.op = .and ∨ a.op = .or ∨ (a.op = .not ∧ a.inputs.length = 1)))
    (hSize : C.size ≤ g) (w : Fin h → Bool)
    (hLower : g * N < cellArea (fun x y : Fin N => C.eval (oneEach x y ++ List.ofFn w)))
    (hUpper : cellArea (fun x y : Fin N => C.eval (oneEach x y ++ List.ofFn w)) < N * (N-g)) :
    ∃ R S : Finset (Fin N), R.card + S.card = g+1 ∧
      ∀ (w' : Fin h → Bool) (x y : Fin N),
        C.eval (oneEach x y ++ List.ofFn w') = decide (x ∈ R ∨ y ∈ S) := by
  obtain ⟨hNames, hData, hBinary⟩ := saturate C hBack hOut hGates hSize w hLower hUpper
  let n := N+N+h
  let F := inputsUsed n C
  have hOr : ∀ a ∈ C.gates, a.op = .or := by
    intro a ha
    rcases (hBinary a ha).2 with hAnd | hIsOr
    · exfalso
      let D : Circuit := ⟨C.gates.map pruneGate, C.output⟩
      let I := inputsUsed n D
      let R := namedRows N I
      let S := namedCols N I
      let z : Fin h → Bool := fun _ => false
      have hDb : ReadsBack n D := prune_readsBack hBack
      have hDs : D.size = C.size := by simp [D, Circuit.size]
      have hDo : D.output < n + D.size := by
        rw [hDs]
        exact hOut
      have hDops : ∀ b ∈ D.gates, b.op = .or ∧ b.inputs.length ≤ 2 := by
        intro b hb
        rcases List.mem_map.mp hb with ⟨c, hc, rfl⟩
        exact prune_gate_bounds c (hGates c hc).1 (hBinary c hc).2
      have hDsmall : ∃ b ∈ D.gates, b.inputs.length ≤ 1 := prune_small_gate ⟨a, ha, hAnd⟩
      have hI : I.card ≤ D.size := inputsUsed_card_small D (fun b hb => (hDops b hb).2) hDsmall
      have hRS : R.card + S.card ≤ g := calc
        R.card + S.card = (I.filter fun i => i < N+N).card := named_card N I
        _ ≤ I.card := Finset.card_filter_le _ _
        _ ≤ D.size := hI
        _ ≤ g := hDs ▸ hSize
      have hCover : ∀ x y : Fin N, C.eval (oneEach x y ++ List.ofFn w) = true → x ∈ R ∨ y ∈ S := by
        intro x y hv
        have hv' : C.eval (oneEach x y ++ List.ofFn z) = true :=
          (eval_seed_eq C hBack hOut hData w z x y).symm.trans hv
        have hLe : C.eval (oneEach x y ++ List.ofFn z) ≤ D.eval (oneEach x y ++ List.ofFn z) :=
          prune_eval_binary C.gates (fun b hb => (hBinary b hb).2)
            (fun b hb => (hBinary b hb).1) _ C.output
        have hTrue := Bool.le_iff_imp.mp hLe hv'
        rw [eval_or_lines D hDb hDo (fun b hb => (hDops b hb).1) z (Or.inr fun _ => rfl) x y,
          decide_eq_true_eq] at hTrue
        exact hTrue
      exact (not_le_of_gt hLower) (cellArea_le_lines _ R S hRS hCover)
    · exact hIsOr
  refine ⟨namedRows N F, namedCols N F, hNames, fun w' x y => ?_⟩
  exact eval_or_lines C hBack hOut hOr w' (Or.inl hData) x y


private def orChainAux (n : ℕ) : ℕ → List ℕ → List Gate → Circuit
  | acc, [], gs => ⟨gs, acc⟩
  | acc, w :: ws, gs => orChainAux n (n + gs.length) ws (gs ++ [⟨.or, [acc, w]⟩])

private lemma orChainAux_size (n acc : ℕ) (ws : List ℕ) (gs : List Gate) :
    (orChainAux n acc ws gs).size = gs.length + ws.length := by
  induction ws generalizing acc gs with
  | nil => simp [orChainAux, Circuit.size]
  | cons w ws ih =>
    simp only [orChainAux, ih, List.length_append, List.length_cons, List.length_nil]
    omega

private lemma orChainAux_output (n acc : ℕ) (ws : List ℕ) (gs : List Gate)
    (hacc : acc < n + gs.length) :
    (orChainAux n acc ws gs).output < n + (orChainAux n acc ws gs).size := by
  induction ws generalizing acc gs with
  | nil => simpa [orChainAux, Circuit.size] using hacc
  | cons w ws ih =>
    simp only [orChainAux]
    apply ih
    simp only [List.length_append, List.length_singleton]
    omega

private lemma orChainAux_gates (n acc : ℕ) (ws : List ℕ) (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.inputs.length ≤ 2 ∧ g.op = .or) :
    ∀ g ∈ (orChainAux n acc ws gs).gates, g.inputs.length ≤ 2 ∧ g.op = .or := by
  induction ws generalizing acc gs with
  | nil => exact hgs
  | cons w ws ih =>
    apply ih
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hgs g hg
    · simp only [List.mem_singleton] at hg
      subst hg
      simp

private lemma orChainAux_readsBack (n acc : ℕ) (ws : List ℕ) (gs : List Gate)
    (hgs : ReadsBack n ⟨gs, acc⟩) (hacc : acc < n + gs.length) (hws : ∀ w ∈ ws, w < n) :
    ReadsBack n (orChainAux n acc ws gs) := by
  induction ws generalizing acc gs with
  | nil => exact hgs
  | cons w ws ih =>
    apply ih
    · intro j hj i hi
      change j < (gs ++ [Gate.mk .or [acc, w]]).length at hj
      rw [gateAt_eq_getElem _ _ hj] at hi
      change i ∈ (gs ++ [Gate.mk .or [acc, w]])[j].inputs at hi
      by_cases hlt : j < gs.length
      · rw [List.getElem_append_left hlt] at hi
        apply hgs j hlt i
        rwa [gateAt_eq_getElem _ _ hlt]
      · have heq : j = gs.length := by simp at hj; omega
        subst heq
        rw [List.getElem_append_right (le_refl _)] at hi
        simp only [Nat.sub_self, List.getElem_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact hacc
        · have hw := hws i (by simp)
          omega
    · simp only [List.length_append, List.length_singleton]; omega
    · intro u hu; exact hws u (List.mem_cons_of_mem _ hu)

private lemma wires_append_one (gs : List Gate) (g : Gate) (x : List Bool) :
    (Circuit.mk (gs ++ [g]) 0).wires x =
      let w := (Circuit.mk gs 0).wires x
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := by
  simp [Circuit.wires, List.foldl_append]

private lemma wires_length_eq (gs : List Gate) (x : List Bool) :
    ((Circuit.mk gs 0).wires x).length = x.length + gs.length := by
  have h := reverseWires_length x gs.reverse
  rw [reverseWires_eq, List.reverse_reverse, List.length_reverse] at h
  exact h

private lemma wires_getD_lt (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    ((Circuit.mk gs 0).wires x).getD i false = x.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [wires_append_one]
    dsimp only
    have hlen := wires_length_eq gs x
    rw [List.getD_append _ _ _ _ (by omega)]
    exact ih

private lemma orChainAux_eval (n acc : ℕ) (ws : List ℕ) (gs : List Gate)
    (x : List Bool) (hx : x.length = n) (hws : ∀ w ∈ ws, w < n) :
    (orChainAux n acc ws gs).eval x =
      ((Circuit.mk gs acc).eval x || ws.any (fun w => x.getD w false)) := by
  induction ws generalizing acc gs with
  | nil => simp [orChainAux]
  | cons w ws ih =>
    simp only [orChainAux]
    rw [ih _ _ (fun u hu => hws u (List.mem_cons_of_mem _ hu))]
    have hstep : (Circuit.mk (gs ++ [⟨.or, [acc, w]⟩]) (n + gs.length)).eval x =
        ((Circuit.mk gs acc).eval x || x.getD w false) := by
      have hlen : ((Circuit.mk gs 0).wires x).length = n + gs.length := by
        rw [wires_length_eq, hx]
      change ((Circuit.mk (gs ++ [⟨.or, [acc, w]⟩]) 0).wires x).getD (n + gs.length) false = _
      rw [wires_append_one]
      dsimp only
      rw [← hlen, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
      have hw : ((Circuit.mk gs 0).wires x).getD w false = x.getD w false :=
        wires_getD_lt gs x w (hx ▸ hws w (by simp))
      simp only [List.getD_cons_zero, GateOp.eval, List.map_cons, List.map_nil,
        List.any_cons, List.any_nil, Bool.or_false, id_eq, hw]
      rfl
    rw [hstep, List.any_cons, Bool.or_assoc]

private lemma exists_lineUnion_circuit {N : ℕ} (r s : ℕ) (hr : r < N) (hs : s < N)
    (hne : 0 < r + s) :
    ∃ D : Circuit,
      ReadsBack (N + N + 0) D ∧
      D.output < N + N + 0 + D.size ∧
      (∀ a ∈ D.gates, a.inputs.length ≤ 2 ∧
        (a.op = .and ∨ a.op = .or ∨ (a.op = .not ∧ a.inputs.length = 1))) ∧
      D.size = r + s - 1 ∧
      ∀ (w : Fin 0 → Bool) (x y : Fin N),
        D.eval (oneEach x y ++ List.ofFn w) = decide (x.val < r ∨ y.val < s) := by
  let ws : List ℕ := (List.finRange r).map Fin.val ++ (List.finRange s).map (fun j => N + j.val)
  have hlen : ws.length = r + s := by simp [ws]
  have hlt : ∀ u ∈ ws, u < N + N + 0 := by
    intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · rcases List.mem_map.mp hu with ⟨i, _, rfl⟩
      have := i.isLt
      omega
    · rcases List.mem_map.mp hu with ⟨j, _, rfl⟩
      have := j.isLt
      omega
  cases hws : ws with
  | nil =>
    rw [hws] at hlen
    simp at hlen
    omega
  | cons w0 rest =>
    have hw0 : w0 < N + N + 0 := hlt w0 (hws ▸ by simp)
    have hrest : ∀ u ∈ rest, u < N + N + 0 := fun u hu => hlt u (hws ▸ List.mem_cons_of_mem _ hu)
    let D := orChainAux (N + N + 0) w0 rest []
    have hrb0 : ReadsBack (N + N + 0) ⟨[], w0⟩ := by
      intro j hj
      simp at hj
    have hD_rb : ReadsBack (N + N + 0) D :=
      orChainAux_readsBack (N + N + 0) w0 rest [] hrb0 (by simpa using hw0) hrest
    have hD_out : D.output < N + N + 0 + D.size :=
      orChainAux_output (N + N + 0) w0 rest [] (by simpa using hw0)
    have hD_gates : ∀ a ∈ D.gates, a.inputs.length ≤ 2 ∧
        (a.op = .and ∨ a.op = .or ∨ (a.op = .not ∧ a.inputs.length = 1)) := by
      intro a ha
      have h := orChainAux_gates (N + N + 0) w0 rest [] (by intro g hg; simp at hg) a ha
      exact ⟨h.1, Or.inr (Or.inl h.2)⟩
    have hD_size : D.size = r + s - 1 := by
      have h1 := orChainAux_size (N + N + 0) w0 rest []
      rw [hws] at hlen
      simp only [List.length_cons, List.length_nil, zero_add] at h1 hlen
      dsimp only [D]
      omega
    refine ⟨D, hD_rb, hD_out, hD_gates, hD_size, fun w x y => ?_⟩
    have hev := orChainAux_eval (N + N + 0) w0 rest [] (oneEach x y ++ List.ofFn w)
      (oneEach_append_len x y w) hrest
    have h0 : (Circuit.mk [] w0).eval (oneEach x y ++ List.ofFn w) =
        (oneEach x y ++ List.ofFn w).getD w0 false := rfl
    have hany : ((oneEach x y ++ List.ofFn w).getD w0 false ||
        rest.any (fun u => (oneEach x y ++ List.ofFn w).getD u false)) =
        (w0 :: rest).any (fun u => (oneEach x y ++ List.ofFn w).getD u false) := rfl
    rw [hev, h0, hany, ← hws]
    apply Bool.eq_iff_iff.mpr
    rw [List.any_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨u, hu, htrue⟩
      rw [oneEach_append_getD x y w u (hlt u hu)] at htrue
      rcases List.mem_append.mp hu with hu | hu
      · rcases List.mem_map.mp hu with ⟨i, _, rfl⟩
        have hiN : i.val < N := by have := i.isLt; omega
        simp only [hiN, ↓reduceDIte, decide_eq_true_eq, Fin.ext_iff] at htrue
        exact Or.inl (htrue ▸ i.isLt)
      · rcases List.mem_map.mp hu with ⟨j, _, rfl⟩
        have hj1 : ¬ N + j.val < N := by omega
        have hj2 : N + j.val < N + N := by have := j.isLt; omega
        simp only [hj1, hj2, ↓reduceDIte, Nat.add_sub_cancel_left, decide_eq_true_eq, Fin.ext_iff] at htrue
        exact Or.inr (htrue ▸ j.isLt)
    · rintro (hx | hy)
      · refine ⟨x.val, List.mem_append_left _ (List.mem_map.mpr ⟨⟨x.val, hx⟩, List.mem_finRange _, rfl⟩), ?_⟩
        rw [oneEach_append_getD x y w x.val (by have := x.isLt; omega)]
        simp [x.isLt]
      · refine ⟨N + y.val, List.mem_append_right _ (List.mem_map.mpr ⟨⟨y.val, hy⟩, List.mem_finRange _, rfl⟩), ?_⟩
        rw [oneEach_append_getD x y w (N + y.val) (by have := y.isLt; omega)]
        have h1 : ¬ N + y.val < N := by omega
        have h2 : N + y.val < N + N := by have := y.isLt; omega
        simp [h1, h2]

private def lossOf {N : ℕ} (color : Fin N → Fin N → Fin N) (H : Fin N → Fin N → Bool)
    (U : Finset (Fin N)) : ℕ :=
  ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => H z.1 z.2 ≠ decide (color z.1 z.2 ∈ U))).card

private def hitOf {N : ℕ} (color : Fin N → Fin N → Fin N) (H : Fin N → Fin N → Bool)
    (U : Finset (Fin N)) : ℕ :=
  ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => H z.1 z.2 = true ∧ color z.1 z.2 ∈ U)).card

private def overlapHit {N : ℕ} (color : Fin N → Fin N → Fin N) (R S U : Finset (Fin N)) : ℕ :=
  ((R ×ˢ S).filter (fun z => color z.1 z.2 ∈ U)).card

private lemma row_color_card {N : ℕ} (color : Fin N → Fin N → Fin N)
    (hRow : ∀ x, Function.Bijective (color x)) (x : Fin N) (U : Finset (Fin N)) :
    ((Finset.univ : Finset (Fin N)).filter (fun y => color x y ∈ U)).card = U.card := by
  refine Finset.card_bij (fun y _ => color x y) ?_ ?_ ?_
  · intro y hy; exact (Finset.mem_filter.mp hy).2
  · intro y1 _ y2 _ h; exact (hRow x).1 h
  · intro c hc
    obtain ⟨y, hy⟩ := (hRow x).2 c
    exact ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy.symm ▸ hc⟩, hy⟩

private lemma col_color_card {N : ℕ} (color : Fin N → Fin N → Fin N)
    (hCol : ∀ y, Function.Bijective (fun x => color x y)) (y : Fin N) (U : Finset (Fin N)) :
    ((Finset.univ : Finset (Fin N)).filter (fun x => color x y ∈ U)).card = U.card := by
  refine Finset.card_bij (fun x _ => color x y) ?_ ?_ ?_
  · intro x hx; exact (Finset.mem_filter.mp hx).2
  · intro x1 _ x2 _ h; exact (hCol y).1 h
  · intro c hc
    obtain ⟨x, hx⟩ := (hCol y).2 c
    dsimp only at hx
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx.symm ▸ hc⟩, hx⟩

private lemma grid_color_card {N : ℕ} (color : Fin N → Fin N → Fin N)
    (hRow : ∀ x, Function.Bijective (color x)) (U : Finset (Fin N)) :
    ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => color z.1 z.2 ∈ U)).card = N * U.card := by
  rw [Finset.card_filter, Fintype.sum_prod_type]
  have h : ∀ x : Fin N, (∑ y : Fin N, if color x y ∈ U then 1 else 0) = U.card := by
    intro x
    rw [← Finset.card_filter]
    exact row_color_card color hRow x U
  simp_rw [h]
  simp

private lemma loss_add_two_hit {N : ℕ} (color : Fin N → Fin N → Fin N)
    (hRow : ∀ x, Function.Bijective (color x)) (H : Fin N → Fin N → Bool) (U : Finset (Fin N)) :
    lossOf color H U + 2 * hitOf color H U = N * U.card + cellArea H := by
  rw [← grid_color_card color hRow U]
  unfold lossOf hitOf cellArea
  simp_rw [Finset.card_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hc : color z.1 z.2 ∈ U <;> cases h : H z.1 z.2 <;> simp [hc, h]

private lemma lineUnion_area {N : ℕ} (R S : Finset (Fin N)) :
    cellArea (fun x y => decide (x ∈ R ∨ y ∈ S)) + R.card * S.card = (R.card + S.card) * N := by
  have h1 : cellArea (fun x y => decide (x ∈ R ∨ y ∈ S)) + (R ×ˢ S).card =
      ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => z.1 ∈ R)).card +
      ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => z.2 ∈ S)).card := by
    have hRS : (R ×ˢ S).card =
        ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => z.1 ∈ R ∧ z.2 ∈ S)).card := by
      congr 1
      ext z
      simp
    rw [hRS]
    unfold cellArea
    simp_rw [Finset.card_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases hx : z.1 ∈ R <;> by_cases hy : z.2 ∈ S <;> simp [hx, hy]
  have hR : ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => z.1 ∈ R)).card = R.card * N := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    have : ∀ x : Fin N, (∑ _y : Fin N, if x ∈ R then 1 else 0) = if x ∈ R then N else 0 := by
      intro x; by_cases hx : x ∈ R <;> simp [hx]
    simp_rw [this]
    simp [Finset.sum_ite_mem]
  have hS : ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => z.2 ∈ S)).card = N * S.card := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    have hrow : (∑ y : Fin N, if y ∈ S then 1 else 0) = S.card := by
      rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
    simp_rw [hrow]
    simp
  rw [Finset.card_product, hR, hS] at h1
  linarith

private lemma lineUnion_hit {N : ℕ} (color : Fin N → Fin N → Fin N)
    (hRow : ∀ x, Function.Bijective (color x))
    (hCol : ∀ y, Function.Bijective (fun x => color x y))
    (R S U : Finset (Fin N)) :
    hitOf color (fun x y => decide (x ∈ R ∨ y ∈ S)) U + overlapHit color R S U =
      (R.card + S.card) * U.card := by
  have hOv : overlapHit color R S U =
      ((Finset.univ : Finset (Fin N × Fin N)).filter
        (fun z => z.1 ∈ R ∧ z.2 ∈ S ∧ color z.1 z.2 ∈ U)).card := by
    unfold overlapHit
    congr 1
    ext z
    simp [and_assoc]
  have h1 : hitOf color (fun x y => decide (x ∈ R ∨ y ∈ S)) U + overlapHit color R S U =
      ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => z.1 ∈ R ∧ color z.1 z.2 ∈ U)).card +
      ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => z.2 ∈ S ∧ color z.1 z.2 ∈ U)).card := by
    rw [hOv]
    unfold hitOf
    simp_rw [Finset.card_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases hx : z.1 ∈ R <;> by_cases hy : z.2 ∈ S <;> by_cases hc : color z.1 z.2 ∈ U <;> simp [hx, hy, hc]
  have hR : ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => z.1 ∈ R ∧ color z.1 z.2 ∈ U)).card =
      R.card * U.card := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    have : ∀ x : Fin N, (∑ y : Fin N, if x ∈ R ∧ color x y ∈ U then 1 else 0) =
        if x ∈ R then U.card else 0 := by
      intro x
      by_cases hx : x ∈ R
      · simp only [hx, true_and, ↓reduceIte]
        rw [← Finset.card_filter]
        exact row_color_card color hRow x U
      · simp [hx]
    simp_rw [this]
    simp [Finset.sum_ite_mem]
  have hS : ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => z.2 ∈ S ∧ color z.1 z.2 ∈ U)).card =
      S.card * U.card := by
    rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
    have : ∀ y : Fin N, (∑ x : Fin N, if y ∈ S ∧ color x y ∈ U then 1 else 0) =
        if y ∈ S then U.card else 0 := by
      intro y
      by_cases hy : y ∈ S
      · simp only [hy, true_and, ↓reduceIte]
        rw [← Finset.card_filter]
        exact col_color_card color hCol y U
      · simp [hy]
    simp_rw [this]
    simp [Finset.sum_ite_mem]
  rw [hR, hS] at h1
  linarith

private lemma lineUnion_loss_eq {N t : ℕ} (color : Fin N → Fin N → Fin N)
    (hRow : ∀ x, Function.Bijective (color x))
    (hCol : ∀ y, Function.Bijective (fun x => color x y))
    (htN : N < 2 * t) (R S U : Finset (Fin N)) (hU : U.card = t) :
    lossOf color (fun x y => decide (x ∈ R ∨ y ∈ S)) U + (R.card + S.card) * (2 * t - N) + R.card * S.card =
      N * t + 2 * overlapHit color R S U := by
  have h1 := loss_add_two_hit color hRow (fun x y => decide (x ∈ R ∨ y ∈ S)) U
  have h2 := lineUnion_area R S
  have h3 := lineUnion_hit color hRow hCol R S U
  rw [hU] at h1 h3
  have h2t : 2 * t = N + (2 * t - N) := by omega
  have h4 : (R.card + S.card) * (2 * t) = (R.card + S.card) * N + (R.card + S.card) * (2 * t - N) := by
    calc (R.card + S.card) * (2 * t)
        = (R.card + S.card) * (N + (2 * t - N)) := congrArg ((R.card + S.card) * ·) h2t
      _ = (R.card + S.card) * N + (R.card + S.card) * (2 * t - N) := Nat.mul_add _ _ _
  linarith

private lemma color_mem_powersetCard_eq {N t : ℕ} (c1 c2 : Fin N) :
    ((Finset.powersetCard t (Finset.univ : Finset (Fin N))).filter (fun U => c1 ∈ U)).card =
    ((Finset.powersetCard t (Finset.univ : Finset (Fin N))).filter (fun U => c2 ∈ U)).card := by
  let e := Equiv.swap c1 c2
  refine Finset.card_bij (fun U _ => U.map e.toEmbedding) ?_ ?_ ?_
  · intro U hU
    obtain ⟨hUp, hc1⟩ := Finset.mem_filter.mp hU
    rw [Finset.mem_powersetCard_univ] at hUp
    rw [Finset.mem_filter, Finset.mem_powersetCard_univ]
    refine ⟨by simp [hUp], Finset.mem_map.mpr ⟨c1, hc1, by simp [e]⟩⟩
  · intro U1 _ U2 _ h
    exact Finset.map_injective e.toEmbedding h
  · intro V hV
    obtain ⟨hVp, hc2⟩ := Finset.mem_filter.mp hV
    rw [Finset.mem_powersetCard_univ] at hVp
    refine ⟨V.map e.toEmbedding, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_powersetCard_univ]
      refine ⟨by simp [hVp], Finset.mem_map.mpr ⟨c2, hc2, by simp [e]⟩⟩
    · ext x
      simp only [Finset.mem_map, Equiv.coe_toEmbedding]
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        simpa [e] using hz
      · intro hx
        exact ⟨e x, ⟨x, hx, rfl⟩, by simp [e]⟩

private lemma color_mem_powersetCard_count {N : ℕ} (t : ℕ) (c : Fin N) :
    N * ((Finset.powersetCard t (Finset.univ : Finset (Fin N))).filter (fun U => c ∈ U)).card =
      (Finset.powersetCard t (Finset.univ : Finset (Fin N))).card * t := by
  let S := Finset.powersetCard t (Finset.univ : Finset (Fin N))
  have h1 : ∑ U ∈ S, U.card = S.card * t := by
    have hcard : ∀ U ∈ S, U.card = t := fun U hU => (Finset.mem_powersetCard_univ.mp hU)
    rw [Finset.sum_congr rfl hcard, Finset.sum_const, smul_eq_mul]
  have h2 : ∑ U ∈ S, U.card = ∑ x : Fin N, (S.filter (fun U => x ∈ U)).card := by
    have hcard : ∀ U ∈ S, U.card = ∑ x : Fin N, if x ∈ U then 1 else 0 := by
      intro U _; simp [Finset.sum_ite_mem]
    rw [Finset.sum_congr rfl hcard, Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.card_filter]
  have h3 : ∑ x : Fin N, (S.filter (fun U => x ∈ U)).card =
      N * (S.filter (fun U => c ∈ U)).card := by
    have heq : ∀ x : Fin N, (S.filter (fun U => x ∈ U)).card = (S.filter (fun U => c ∈ U)).card :=
      fun x => color_mem_powersetCard_eq x c
    simp_rw [heq]
    simp
  rw [← h3, ← h2, h1]

private lemma sum_filter_powersetCard {N : ℕ} (t : ℕ) (color : Fin N → Fin N → Fin N)
    (A : Finset (Fin N × Fin N)) :
    N * ∑ U ∈ Finset.powersetCard t (Finset.univ : Finset (Fin N)),
        (A.filter (fun z => color z.1 z.2 ∈ U)).card =
      (Finset.powersetCard t (Finset.univ : Finset (Fin N))).card * (A.card * t) := by
  let S := Finset.powersetCard t (Finset.univ : Finset (Fin N))
  have hswap : ∑ U ∈ S, (A.filter (fun z => color z.1 z.2 ∈ U)).card =
      ∑ z ∈ A, (S.filter (fun U => color z.1 z.2 ∈ U)).card := by
    simp_rw [Finset.card_filter]
    exact Finset.sum_comm
  rw [hswap, Finset.mul_sum]
  calc
    ∑ z ∈ A, N * (S.filter (fun U => color z.1 z.2 ∈ U)).card
        = ∑ _z ∈ A, S.card * t :=
          Finset.sum_congr rfl fun z _ => color_mem_powersetCard_count t (color z.1 z.2)
    _ = A.card * (S.card * t) := by simp
    _ = S.card * (A.card * t) := by ring

private lemma sum_loss_ge_of_area_le {N g t : ℕ} (color : Fin N → Fin N → Fin N)
    (hRow : ∀ x, Function.Bijective (color x))
    (hN : 0 < N) (htN : N < 2 * t)
    (H : Fin N → Fin N → Bool) (hArea : cellArea H ≤ g * N) :
    let S := Finset.powersetCard t (Finset.univ : Finset (Fin N))
    S.card * (N * t) ≤ (∑ U ∈ S, lossOf color H U) + S.card * ((2 * t - N) * g) := by
  intro S
  have hsum : (∑ U ∈ S, lossOf color H U) + 2 * ∑ U ∈ S, hitOf color H U =
      S.card * (N * t + cellArea H) := by
    have hpt : ∀ U ∈ S, lossOf color H U + 2 * hitOf color H U = N * t + cellArea H := by
      intro U hU
      have hcard := Finset.mem_powersetCard_univ.mp hU
      simpa [hcard] using loss_add_two_hit color hRow H U
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_congr rfl hpt]
    simp
  have hhit : N * ∑ U ∈ S, hitOf color H U = S.card * (cellArea H * t) := by
    let A := (Finset.univ : Finset (Fin N × Fin N)).filter (fun z => H z.1 z.2 = true)
    have hhitEq : ∀ U ∈ S, hitOf color H U = (A.filter (fun z => color z.1 z.2 ∈ U)).card := by
      intro U _
      unfold hitOf
      congr 1
      ext z
      simp [A]
    rw [Finset.sum_congr rfl hhitEq]
    exact sum_filter_powersetCard t color A
  have hmulN : N * (∑ U ∈ S, lossOf color H U) + 2 * (N * ∑ U ∈ S, hitOf color H U) =
      N * (S.card * (N * t + cellArea H)) := by
    linarith [congrArg (fun z => N * z) hsum]
  rw [hhit] at hmulN
  have h2t : 2 * t = N + (2 * t - N) := by omega
  have hclean : N * (∑ U ∈ S, lossOf color H U) + S.card * (cellArea H * (2 * t - N)) =
      N * (S.card * (N * t)) := by
    have hsplit : 2 * (S.card * (cellArea H * t)) =
        S.card * (cellArea H * N) + S.card * (cellArea H * (2 * t - N)) := by
      calc 2 * (S.card * (cellArea H * t))
          = S.card * (cellArea H * (2 * t)) := by ring
        _ = S.card * (cellArea H * (N + (2 * t - N))) :=
            congrArg (fun z => S.card * (cellArea H * z)) h2t
        _ = S.card * (cellArea H * N) + S.card * (cellArea H * (2 * t - N)) := by ring
    nlinarith
  have hle : S.card * (cellArea H * (2 * t - N)) ≤ N * (S.card * ((2 * t - N) * g)) := by
    have : cellArea H * (2 * t - N) ≤ (g * N) * (2 * t - N) := Nat.mul_le_mul_right _ hArea
    nlinarith
  have hfin : N * (S.card * (N * t)) ≤
      N * ((∑ U ∈ S, lossOf color H U) + S.card * ((2 * t - N) * g)) := by
    nlinarith
  exact Nat.le_of_mul_le_mul_left hfin hN

private lemma exists_superset_card {N t : ℕ} (htle : t ≤ N) (A : Finset (Fin N))
    (hA : A.card ≤ t) :
    ∃ U : Finset (Fin N), A ⊆ U ∧ U.card = t := by
  have hcompl : t - A.card ≤ (Finset.univ \ A).card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨V, hVsub, hVcard⟩ := Finset.exists_subset_card_eq hcompl
  have hdisj : Disjoint A V :=
    Finset.disjoint_left.mpr fun x hxA hxV => (Finset.mem_sdiff.mp (hVsub hxV)).2 hxA
  refine ⟨A ∪ V, Finset.subset_union_left, ?_⟩
  rw [Finset.card_union_of_disjoint hdisj, hVcard]
  omega

private lemma exists_overlapHit_large {N t : ℕ} (color : Fin N → Fin N → Fin N)
    (hN : 0 < N) (htN : N < 2 * t) (htle : t ≤ N) (R S : Finset (Fin N)) :
    let p := R.card * S.card
    let a := 2 * t - N
    (p < a → ∃ U : Finset (Fin N), U.card = t ∧ overlapHit color R S U = p) ∧
    (a ≤ p → p ≤ N → ∃ U : Finset (Fin N), U.card = t ∧ a + p ≤ 2 * overlapHit color R S U) ∧
    (N < p → ∃ U : Finset (Fin N), U.card = t ∧ a + p < 2 * overlapHit color R S U) := by
  intro p a
  let supp : Finset (Fin N) := (R ×ˢ S).image (fun z => color z.1 z.2)
  have hsupp_le : supp.card ≤ p := by
    calc supp.card ≤ (R ×ˢ S).card := Finset.card_image_le
      _ = p := Finset.card_product R S
  have hov_eq_of_sup : ∀ U : Finset (Fin N), supp ⊆ U → overlapHit color R S U = p := by
    intro U hsub
    unfold overlapHit
    have hflt : (R ×ˢ S).filter (fun z => color z.1 z.2 ∈ U) = R ×ˢ S := by
      rw [Finset.filter_eq_self]
      intro z hz
      exact hsub (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
    rw [hflt, Finset.card_product]
  have hov_ge_of_sub : ∀ U : Finset (Fin N), U ⊆ supp → U.card ≤ overlapHit color R S U := by
    intro U hsub
    have himg : U ⊆ ((R ×ˢ S).filter (fun z => color z.1 z.2 ∈ U)).image (fun z => color z.1 z.2) := by
      intro c hc
      obtain ⟨z, hz, hzc⟩ := Finset.mem_image.mp (hsub hc)
      exact Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨hz, hzc.symm ▸ hc⟩, hzc⟩
    calc U.card ≤ (((R ×ˢ S).filter (fun z => color z.1 z.2 ∈ U)).image (fun z => color z.1 z.2)).card :=
          Finset.card_le_card himg
      _ ≤ overlapHit color R S U := Finset.card_image_le
  refine ⟨?_, ?_, ?_⟩
  · intro hpa
    have hsuppt : supp.card ≤ t := by omega
    obtain ⟨U, hsub, hU⟩ := exists_superset_card htle supp hsuppt
    exact ⟨U, hU, hov_eq_of_sup U hsub⟩
  · intro hap hpN
    by_cases hsuppt : supp.card ≤ t
    · obtain ⟨U, hsub, hU⟩ := exists_superset_card htle supp hsuppt
      refine ⟨U, hU, ?_⟩
      rw [hov_eq_of_sup U hsub]
      omega
    · have htlt : t ≤ supp.card := by omega
      obtain ⟨U, hsub, hU⟩ := Finset.exists_subset_card_eq htlt
      have hge := hov_ge_of_sub U hsub
      rw [hU] at hge
      refine ⟨U, hU, ?_⟩
      omega
  · intro hNp
    let St := Finset.powersetCard t (Finset.univ : Finset (Fin N))
    have hSt_pos : 0 < St.card := by
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
      exact Nat.choose_pos htle
    have havg : N * ∑ U ∈ St, overlapHit color R S U = St.card * (p * t) := by
      have h := sum_filter_powersetCard t color (R ×ˢ S)
      rwa [Finset.card_product] at h
    have hex : ∃ U ∈ St, p * t ≤ N * overlapHit color R S U := by
      by_contra hall
      push_neg at hall
      have hlt_sum : ∑ U ∈ St, (N * overlapHit color R S U + 1) ≤ ∑ _U ∈ St, (p * t) :=
        Finset.sum_le_sum fun U hU => hall U hU
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.sum_const,
        smul_eq_mul, smul_eq_mul, mul_one, havg] at hlt_sum
      omega
    obtain ⟨U, hUmem, hUge⟩ := hex
    have hUcard := Finset.mem_powersetCard_univ.mp hUmem
    refine ⟨U, hUcard, ?_⟩
    have ha_pos : 0 < a := by omega
    have h2t : 2 * t = N + a := by omega
    have hstrict : N * (a + p) < N * (2 * overlapHit color R S U) := by
      nlinarith
    exact Nat.lt_of_mul_lt_mul_left hstrict

private lemma card_filter_val_lt {N k : ℕ} (hk : k ≤ N) :
    ((Finset.univ : Finset (Fin N)).filter (fun x : Fin N => x.val < k)).card = k := by
  have h : ((Finset.univ : Finset (Fin N)).filter (fun x : Fin N => x.val < k)).card =
      (Finset.univ : Finset (Fin k)).card := by
    refine Finset.card_bij (fun x hx => (⟨x.val, (Finset.mem_filter.mp hx).2⟩ : Fin k)) ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro x1 _ x2 _ h
      exact Fin.ext (congrArg (@Fin.val k) h)
    · intro i _
      exact ⟨⟨i.val, by have := i.isLt; omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.isLt⟩, Fin.ext rfl⟩
  simpa using h

private lemma value_add_eq {N g d t : ℕ} (hNg : 2 * g + 1 < N) (htle : t ≤ N) :
    let b := g + 1
    let lineGain := 2 * t - N
    let bonus := (Finset.range (b + 1)).sup (fun r => if d ≤ r * (b - r) then lineGain - r * (b - r) else 0)
    let value := N * t - lineGain * g - bonus
    value + lineGain * g + bonus = N * t := by
  intro b lineGain bonus value
  have hbonus_le : bonus ≤ lineGain := by
    refine Finset.sup_le fun r _ => ?_
    split_ifs
    · exact Nat.sub_le _ _
    · exact Nat.zero_le _
  have hlg_le_t : lineGain ≤ t := by omega
  have hbound : lineGain * g + bonus ≤ N * t := by
    have h1 : lineGain * g + bonus ≤ lineGain * (g + 1) := by nlinarith
    have h2 : lineGain * (g + 1) ≤ t * (g + 1) := Nat.mul_le_mul_right _ hlg_le_t
    have h3 : t * (g + 1) ≤ t * N := Nat.mul_le_mul_left _ (by omega)
    nlinarith
  have hv : value = N * t - (lineGain * g + bonus) := Nat.sub_sub _ _ _
  omega

private lemma main_32061_part1 {N g d t : ℕ} (hg : 0 < g) (hNg : 2 * g + 1 < N)
    (hd0 : 0 < d) (hdN : d < N) (htN : N < 2 * t) (htle : t ≤ N)
    (color : Fin N → Fin N → Fin N)
    (hRow : ∀ x, Function.Bijective (color x))
    (hCol : ∀ y, Function.Bijective (fun x => color x y)) :
    let b := g + 1
    let lineGain := 2 * t - N
    let cap := b * N - d
    let bonus := (Finset.range (b + 1)).sup (fun r => if d ≤ r * (b - r) then lineGain - r * (b - r) else 0)
    let value := N * t - lineGain * g - bonus
    ∃ D : Circuit,
      (ReadsBack (N + N + 0) D ∧ D.output < N + N + 0 + D.size ∧
        ∀ gate ∈ D.gates, gate.inputs.length ≤ 2 ∧
          (gate.op = .and ∨ gate.op = .or ∨ (gate.op = .not ∧ gate.inputs.length = 1))) ∧
      D.size ≤ g ∧
      (∀ w : Fin 0 → Bool, cellArea (fun x y : Fin N => D.eval (oneEach x y ++ List.ofFn w)) ≤ cap) ∧
      ∀ (w : Fin 0 → Bool) (U : Finset (Fin N)),
        U.card = t → lossOf color (fun x y : Fin N => D.eval (oneEach x y ++ List.ofFn w)) U ≤ value := by
  intro b lineGain cap bonus value
  have hN : 0 < N := by omega
  have hval_sum : value + lineGain * g + bonus = N * t := value_add_eq hNg htle
  by_cases hbon : bonus = 0
  · obtain ⟨D, hrb, hout, hgates, hsize, heval⟩ :=
      exists_lineUnion_circuit (N := N) g 0 (by omega) hN (by omega)
    let R : Finset (Fin N) := Finset.univ.filter (fun x : Fin N => x.val < g)
    have hRcard : R.card = g := card_filter_val_lt (by omega)
    have htab : ∀ w : Fin 0 → Bool,
        (fun x y : Fin N => D.eval (oneEach x y ++ List.ofFn w)) =
        (fun x y => decide (x ∈ R ∨ y ∈ (∅ : Finset (Fin N)))) := by
      intro w; funext x y; rw [heval w x y]; simp [R]
    refine ⟨D, ⟨hrb, hout, hgates⟩, by omega, fun w => ?_, fun w U hU => ?_⟩
    · rw [htab w]
      have hA := lineUnion_area R ∅
      rw [hRcard, Finset.card_empty] at hA
      simp only [Nat.add_zero, Nat.mul_zero] at hA
      have h1 : g * N + d ≤ b * N := by dsimp only [b]; nlinarith
      dsimp only [cap]
      omega
    · rw [htab w]
      have hL := lineUnion_loss_eq color hRow hCol htN R ∅ U hU
      have hov0 : overlapHit color R ∅ U = 0 := by simp [overlapHit]
      rw [hRcard, Finset.card_empty, hov0] at hL
      have hmul : (g + 0) * (2 * t - N) = lineGain * g := by dsimp only [lineGain]; ring
      omega
  · have hbon_pos : 0 < bonus := Nat.pos_of_ne_zero hbon
    obtain ⟨r, hrMem, hrEq⟩ :=
      Finset.exists_mem_eq_sup (Finset.range (b + 1)) ⟨0, Finset.mem_range.mpr (Nat.succ_pos b)⟩
        (fun r => if d ≤ r * (b - r) then lineGain - r * (b - r) else 0)
    have hrLe : r ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hrMem)
    have hfeas : d ≤ r * (b - r) := by
      by_contra hnot
      simp only [hnot, ↓reduceIte] at hrEq
      have : bonus = 0 := hrEq
      omega
    simp only [hfeas, ↓reduceIte] at hrEq
    have hbon_eq : bonus = lineGain - r * (b - r) := hrEq
    have hbon_add : bonus + r * (b - r) = lineGain := by omega
    have hrN : r < N := by omega
    have hsN : b - r < N := by omega
    have hsum_rs : r + (b - r) = b := Nat.add_sub_of_le hrLe
    obtain ⟨D, hrb, hout, hgates, hsize, heval⟩ :=
      exists_lineUnion_circuit (N := N) r (b - r) hrN hsN (by omega)
    let R : Finset (Fin N) := Finset.univ.filter (fun x : Fin N => x.val < r)
    let S : Finset (Fin N) := Finset.univ.filter (fun y : Fin N => y.val < b - r)
    have hRcard : R.card = r := card_filter_val_lt (by omega)
    have hScard : S.card = b - r := card_filter_val_lt (by omega)
    have htab : ∀ w : Fin 0 → Bool,
        (fun x y : Fin N => D.eval (oneEach x y ++ List.ofFn w)) =
        (fun x y => decide (x ∈ R ∨ y ∈ S)) := by
      intro w; funext x y; rw [heval w x y]; simp [R, S]
    refine ⟨D, ⟨hrb, hout, hgates⟩, by omega, fun w => ?_, fun w U hU => ?_⟩
    · rw [htab w]
      have hA := lineUnion_area R S
      rw [hRcard, hScard, hsum_rs] at hA
      have hle_bN : d ≤ b * N := by nlinarith
      dsimp only [cap]
      omega
    · rw [htab w]
      have hL := lineUnion_loss_eq color hRow hCol htN R S U hU
      have hov_le : overlapHit color R S U ≤ R.card * S.card := by
        calc overlapHit color R S U ≤ (R ×ˢ S).card := Finset.card_filter_le _ _
          _ = R.card * S.card := Finset.card_product R S
      rw [hRcard, hScard, hsum_rs] at hL
      rw [hRcard, hScard] at hov_le
      have hb_lg : b * (2 * t - N) = lineGain * g + lineGain := by dsimp only [b, lineGain]; ring
      rw [hb_lg] at hL
      omega

private lemma main_32061_part2 {N g d t h : ℕ} (hg : 0 < g) (hNg : 2 * g + 1 < N)
    (hd0 : 0 < d) (hdN : d < N) (htN : N < 2 * t) (htle : t ≤ N)
    (color : Fin N → Fin N → Fin N)
    (hRow : ∀ x, Function.Bijective (color x))
    (hCol : ∀ y, Function.Bijective (fun x => color x y))
    (C : Circuit) (P : (Fin h → Bool) → ℝ)
    (hBack : ReadsBack (N + N + h) C) (hOut : C.output < N + N + h + C.size)
    (hGates : ∀ gate ∈ C.gates, gate.inputs.length ≤ 2 ∧
      (gate.op = .and ∨ gate.op = .or ∨ (gate.op = .not ∧ gate.inputs.length = 1)))
    (hSize : C.size ≤ g)
    (hCap : ∀ w : Fin h → Bool, cellArea (fun x y : Fin N => C.eval (oneEach x y ++ List.ofFn w)) ≤ (g + 1) * N - d)
    (hP_nonneg : ∀ w, 0 ≤ P w) (hP_sum : (∑ w, P w) = 1) :
    let b := g + 1
    let lineGain := 2 * t - N
    let bonus := (Finset.range (b + 1)).sup (fun r => if d ≤ r * (b - r) then lineGain - r * (b - r) else 0)
    let value := N * t - lineGain * g - bonus
    let risk := fun (U : Finset (Fin N)) =>
      ∑ w : Fin h → Bool, P w * (lossOf color (fun x y => C.eval (oneEach x y ++ List.ofFn w)) U : ℝ)
    (∃ U : Finset (Fin N), U.card = t ∧ (value : ℝ) ≤ risk U) ∧
    (0 < bonus → (∀ U : Finset (Fin N), U.card = t → risk U ≤ (value : ℝ)) →
      ∃ R S : Finset (Fin N), R.card + S.card = b ∧
        d ≤ R.card * S.card ∧ bonus + R.card * S.card = lineGain ∧
        ∀ (w : Fin h → Bool) (x y : Fin N),
          C.eval (oneEach x y ++ List.ofFn w) = decide (x ∈ R ∨ y ∈ S)) := by
  intro b lineGain bonus value risk
  have hN : 0 < N := by omega
  have hval_sum : value + lineGain * g + bonus = N * t := value_add_eq hNg htle
  by_cases hBig : ∃ w0 : Fin h → Bool,
      g * N < cellArea (fun x y : Fin N => C.eval (oneEach x y ++ List.ofFn w0))
  · obtain ⟨w0, hLow⟩ := hBig
    have hHigh : cellArea (fun x y : Fin N => C.eval (oneEach x y ++ List.ofFn w0)) < N * (N - g) := by
      have h1 := hCap w0
      have h2 : (g + 1) * N - d < b * N := by
        have : d ≤ b * N := by dsimp only [b]; nlinarith
        dsimp only [b]
        omega
      have h3 : b * N < N * (N - g) := by
        have : b < N - g := by omega
        nlinarith
      omega
    obtain ⟨R, S, hRScard, hLU⟩ := whole_lines C hBack hOut hGates hSize w0 hLow hHigh
    have hfun : ∀ w : Fin h → Bool,
        (fun x y : Fin N => C.eval (oneEach x y ++ List.ofFn w)) =
        (fun x y => decide (x ∈ R ∨ y ∈ S)) := fun w => funext fun x => funext fun y => hLU w x y
    have hrisk_eq : ∀ U : Finset (Fin N),
        risk U = (lossOf color (fun x y => decide (x ∈ R ∨ y ∈ S)) U : ℝ) := by
      intro U
      dsimp only [risk]
      simp_rw [hfun]
      rw [← Finset.sum_mul, hP_sum, one_mul]
    have hd_le_p : d ≤ R.card * S.card := by
      have hA := lineUnion_area R S
      have hcap0 : cellArea (fun x y => decide (x ∈ R ∨ y ∈ S)) ≤ (g + 1) * N - d := by
        rw [← hfun w0]
        exact hCap w0
      rw [hRScard] at hA
      have hdbN : d ≤ (g + 1) * N := by nlinarith
      omega
    have hbon_ge : lineGain - R.card * S.card ≤ bonus := by
      have hrMem : R.card ∈ Finset.range (b + 1) := Finset.mem_range.mpr (by omega)
      have hsEq : b - R.card = S.card := by omega
      have hsup := Finset.le_sup (f := fun r => if d ≤ r * (b - r) then lineGain - r * (b - r) else 0) hrMem
      simpa [hsEq, hd_le_p] using hsup
    obtain ⟨hSmall, hMid, hLarge⟩ := exists_overlapHit_large color hN htN htle R S
    have hloss_ge_iff : ∀ U : Finset (Fin N), U.card = t →
        (value ≤ lossOf color (fun x y => decide (x ∈ R ∨ y ∈ S)) U ↔
          lineGain + R.card * S.card ≤ 2 * overlapHit color R S U + bonus) ∧
        (value < lossOf color (fun x y => decide (x ∈ R ∨ y ∈ S)) U ↔
          lineGain + R.card * S.card < 2 * overlapHit color R S U + bonus) := by
      intro U hU
      have hL := lineUnion_loss_eq color hRow hCol htN R S U hU
      rw [hRScard] at hL
      have hb_eq : b * (2 * t - N) = lineGain * g + lineGain := by dsimp only [b, lineGain]; ring
      rw [hb_eq] at hL
      constructor <;> omega
    constructor
    · by_cases h1 : R.card * S.card < lineGain
      · obtain ⟨U, hU, hov⟩ := hSmall h1
        clear hSmall hMid hLarge
        refine ⟨U, hU, ?_⟩
        rw [hrisk_eq U]
        have hstep : lineGain + R.card * S.card ≤ 2 * overlapHit color R S U + bonus := by
          rw [hov]; omega
        exact_mod_cast (hloss_ge_iff U hU).1.mpr hstep
      · by_cases h2 : R.card * S.card ≤ N
        · obtain ⟨U, hU, hov⟩ := hMid (by omega) h2
          clear hSmall hMid hLarge
          refine ⟨U, hU, ?_⟩
          rw [hrisk_eq U]
          exact_mod_cast (hloss_ge_iff U hU).1.mpr (by omega)
        · obtain ⟨U, hU, hov⟩ := hLarge (by omega)
          clear hSmall hMid hLarge
          refine ⟨U, hU, ?_⟩
          rw [hrisk_eq U]
          exact_mod_cast (hloss_ge_iff U hU).1.mpr (by omega)
    · intro hbon_pos hall_le
      refine ⟨R, S, hRScard, hd_le_p, ?_, hLU⟩
      by_cases h1 : R.card * S.card < lineGain
      · obtain ⟨U, hU, hov⟩ := hSmall h1
        clear hSmall hMid hLarge
        have hle_real : (lossOf color (fun x y => decide (x ∈ R ∨ y ∈ S)) U : ℝ) ≤ (value : ℝ) := by
          rw [← hrisk_eq U]
          exact hall_le U hU
        have hle_nat : lossOf color (fun x y => decide (x ∈ R ∨ y ∈ S)) U ≤ value := by
          exact_mod_cast hle_real
        have hnot_gt : ¬ (value < lossOf color (fun x y => decide (x ∈ R ∨ y ∈ S)) U) := by omega
        have hnot2 : ¬ (lineGain + R.card * S.card < 2 * overlapHit color R S U + bonus) :=
          mt (hloss_ge_iff U hU).2.mpr hnot_gt
        rw [hov] at hnot2
        omega
      · exfalso
        by_cases h2 : R.card * S.card ≤ N
        · obtain ⟨U, hU, hov⟩ := hMid (by omega) h2
          have hle_real : (lossOf color (fun x y => decide (x ∈ R ∨ y ∈ S)) U : ℝ) ≤ (value : ℝ) := by
            rw [← hrisk_eq U]
            exact hall_le U hU
          have hle_nat : lossOf color (fun x y => decide (x ∈ R ∨ y ∈ S)) U ≤ value := by
            exact_mod_cast hle_real
          have hgt : value < lossOf color (fun x y => decide (x ∈ R ∨ y ∈ S)) U :=
            (hloss_ge_iff U hU).2.mpr (by omega)
          omega
        · obtain ⟨U, hU, hov⟩ := hLarge (by omega)
          have hle_real : (lossOf color (fun x y => decide (x ∈ R ∨ y ∈ S)) U : ℝ) ≤ (value : ℝ) := by
            rw [← hrisk_eq U]
            exact hall_le U hU
          have hle_nat : lossOf color (fun x y => decide (x ∈ R ∨ y ∈ S)) U ≤ value := by
            exact_mod_cast hle_real
          have hgt : value < lossOf color (fun x y => decide (x ∈ R ∨ y ∈ S)) U :=
            (hloss_ge_iff U hU).2.mpr (by omega)
          omega
  · push Not at hBig
    let St := Finset.powersetCard t (Finset.univ : Finset (Fin N))
    have hSt_pos : 0 < St.card := by
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
      exact Nat.choose_pos htle
    have hSt_real : (0 : ℝ) < (St.card : ℝ) := Nat.cast_pos.mpr hSt_pos
    have hsum_risk_ge : (St.card : ℝ) * ((value : ℝ) + (bonus : ℝ)) ≤ ∑ U ∈ St, risk U := by
      dsimp only [risk]
      rw [Finset.sum_comm]
      have hper_w : ∀ w : Fin h → Bool,
          P w * ((St.card : ℝ) * ((value : ℝ) + (bonus : ℝ))) ≤
            ∑ U ∈ St, P w * (lossOf color (fun x y => C.eval (oneEach x y ++ List.ofFn w)) U : ℝ) := by
        intro w
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ (hP_nonneg w)
        have hnat := sum_loss_ge_of_area_le color hRow hN htN
          (fun x y => C.eval (oneEach x y ++ List.ofFn w)) (hBig w)
        change St.card * (N * t) ≤
            (∑ U ∈ St, lossOf color (fun x y => C.eval (oneEach x y ++ List.ofFn w)) U) +
              St.card * (lineGain * g) at hnat
        have hnat' : St.card * (value + bonus) ≤
            ∑ U ∈ St, lossOf color (fun x y => C.eval (oneEach x y ++ List.ofFn w)) U := by
          have h1 : St.card * (value + bonus) + St.card * (lineGain * g) = St.card * (N * t) := by
            calc St.card * (value + bonus) + St.card * (lineGain * g)
                = St.card * (value + lineGain * g + bonus) := by ring
              _ = St.card * (N * t) := congrArg (St.card * ·) hval_sum
          omega
        have hreal : ((St.card * (value + bonus) : ℕ) : ℝ) ≤
            ((∑ U ∈ St, lossOf color (fun x y => C.eval (oneEach x y ++ List.ofFn w)) U : ℕ) : ℝ) :=
          Nat.cast_le.mpr hnat'
        simpa [Nat.cast_mul, Nat.cast_add, Nat.cast_sum] using hreal
      calc
        (St.card : ℝ) * ((value : ℝ) + (bonus : ℝ))
            = (∑ w : Fin h → Bool, P w) * ((St.card : ℝ) * ((value : ℝ) + (bonus : ℝ))) := by
              rw [hP_sum, one_mul]
        _ = ∑ w : Fin h → Bool, P w * ((St.card : ℝ) * ((value : ℝ) + (bonus : ℝ))) := by
              rw [Finset.sum_mul]
        _ ≤ ∑ w : Fin h → Bool, ∑ U ∈ St,
              P w * (lossOf color (fun x y => C.eval (oneEach x y ++ List.ofFn w)) U : ℝ) :=
              Finset.sum_le_sum fun w _ => hper_w w
    constructor
    · by_contra hall
      push Not at hall
      have hlt_sum : ∑ U ∈ St, risk U < ∑ _U ∈ St, (value : ℝ) :=
        Finset.sum_lt_sum_of_nonempty (Finset.card_pos.mp hSt_pos) fun U hU =>
          hall U (Finset.mem_powersetCard_univ.mp hU)
      rw [Finset.sum_const, nsmul_eq_mul] at hlt_sum
      have hbon_nonneg : (0 : ℝ) ≤ (bonus : ℝ) := Nat.cast_nonneg bonus
      nlinarith
    · intro hbon_pos hall_le
      exfalso
      have hle_sum : ∑ U ∈ St, risk U ≤ ∑ _U ∈ St, (value : ℝ) :=
        Finset.sum_le_sum fun U hU => hall_le U (Finset.mem_powersetCard_univ.mp hU)
      rw [Finset.sum_const, nsmul_eq_mul] at hle_sum
      have hbon_real : (0 : ℝ) < (bonus : ℝ) := Nat.cast_pos.mpr hbon_pos
      nlinarith

theorem main_32061 : ∀ (N g d t : ℕ), 0 < g → 2*g+1 < N → 0 < d → d < N → N < 2*t → t ≤ N →
  let X := Fin N
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let legal := fun (h : ℕ) (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N+h) C ∧ C.output < N+N+h+C.size ∧
    ∀ gate ∈ C.gates, gate.inputs.length ≤ 2 ∧
      (gate.op = .and ∨ gate.op = .or ∨ (gate.op = .not ∧ gate.inputs.length = 1))
  let table := fun (h : ℕ) (C : Circ) (w : Fin h → Bool) (x y : X) =>
    C.eval (PEqualNP.Represents.oneEach x y ++ List.ofFn w)
  let area := fun (H : X → X → Bool) =>
    ((Finset.univ : Finset (X × X)).filter (fun z => H z.1 z.2 = true)).card
  let lineUnion := fun (h : ℕ) (C : Circ) (R S : Finset X) =>
    ∀ (w : Fin h → Bool) (x y : X), table h C w x y = decide (x ∈ R ∨ y ∈ S)
  ∀ color : X → X → X,
    (∀ x, Function.Bijective (color x)) → (∀ y, Function.Bijective (fun x => color x y)) →
    let b := g+1
    let lineGain := 2*t-N
    let cap := b*N-d
    let bonus := (Finset.range (b+1)).sup (fun r => if d ≤ r*(b-r) then lineGain-r*(b-r) else 0)
    let value := N*t - lineGain*g - bonus
    let loss := fun (H : X → X → Bool) (U : Finset X) =>
      ((Finset.univ : Finset (X × X)).filter (fun z =>
        H z.1 z.2 ≠ decide (color z.1 z.2 ∈ U))).card
    let fits := fun (h : ℕ) (C : Circ) =>
      legal h C ∧ C.size ≤ g ∧ ∀ w : Fin h → Bool, area (table h C w) ≤ cap
    let risk := fun (h : ℕ) (C : Circ) (P : (Fin h → Bool) → ℝ) (U : Finset X) =>
      ∑ w, P w * (loss (table h C w) U : ℝ)
    (∃ D : Circ, fits 0 D ∧ ∀ (w : Fin 0 → Bool) (U : Finset X),
      U.card = t → loss (table 0 D w) U ≤ value) ∧
    ∀ (h : ℕ) (C : Circ) (P : (Fin h → Bool) → ℝ), fits h C →
      (∀ w, 0 ≤ P w) → (∑ w, P w) = 1 →
      (∃ U : Finset X, U.card = t ∧ (value : ℝ) ≤ risk h C P U) ∧
      (0 < bonus → (∀ U : Finset X, U.card = t → risk h C P U ≤ (value : ℝ)) →
        ∃ R S : Finset X, R.card+S.card = b ∧
          d ≤ R.card*S.card ∧ bonus + R.card*S.card = lineGain ∧ lineUnion h C R S) := by
  intro N g d t hg hNg hd0 hdN htN htle
  dsimp only
  intro color hRow hCol
  constructor
  · obtain ⟨D, hleg, hsz, hcap, hloss⟩ := main_32061_part1 hg hNg hd0 hdN htN htle color hRow hCol
    exact ⟨D, ⟨hleg, hsz, hcap⟩, hloss⟩
  · intro h C P ⟨⟨hBack, hOut, hGates⟩, hSize, hCap⟩ hP_nonneg hP_sum
    exact main_32061_part2 hg hNg hd0 hdN htN htle color hRow hCol C P
      hBack hOut hGates hSize hCap hP_nonneg hP_sum

end PEqualNP.Outside.L_meta_32061_aux

theorem PEqualNP.Outside.L_meta_32061 : ∀ (N g d t : ℕ), 0 < g → 2*g+1 < N → 0 < d → d < N → N < 2*t → t ≤ N →
  let X := Fin N
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let legal := fun (h : ℕ) (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N+h) C ∧ C.output < N+N+h+C.size ∧
    ∀ gate ∈ C.gates, gate.inputs.length ≤ 2 ∧
      (gate.op = .and ∨ gate.op = .or ∨ (gate.op = .not ∧ gate.inputs.length = 1))
  let table := fun (h : ℕ) (C : Circ) (w : Fin h → Bool) (x y : X) =>
    C.eval (PEqualNP.Represents.oneEach x y ++ List.ofFn w)
  let area := fun (H : X → X → Bool) =>
    ((Finset.univ : Finset (X × X)).filter (fun z => H z.1 z.2 = true)).card
  let lineUnion := fun (h : ℕ) (C : Circ) (R S : Finset X) =>
    ∀ (w : Fin h → Bool) (x y : X), table h C w x y = decide (x ∈ R ∨ y ∈ S)
  ∀ color : X → X → X,
    (∀ x, Function.Bijective (color x)) → (∀ y, Function.Bijective (fun x => color x y)) →
    let b := g+1
    let lineGain := 2*t-N
    let cap := b*N-d
    let bonus := (Finset.range (b+1)).sup (fun r => if d ≤ r*(b-r) then lineGain-r*(b-r) else 0)
    let value := N*t - lineGain*g - bonus
    let loss := fun (H : X → X → Bool) (U : Finset X) =>
      ((Finset.univ : Finset (X × X)).filter (fun z =>
        H z.1 z.2 ≠ decide (color z.1 z.2 ∈ U))).card
    let fits := fun (h : ℕ) (C : Circ) =>
      legal h C ∧ C.size ≤ g ∧ ∀ w : Fin h → Bool, area (table h C w) ≤ cap
    let risk := fun (h : ℕ) (C : Circ) (P : (Fin h → Bool) → ℝ) (U : Finset X) =>
      ∑ w, P w * (loss (table h C w) U : ℝ)
    (∃ D : Circ, fits 0 D ∧ ∀ (w : Fin 0 → Bool) (U : Finset X),
      U.card = t → loss (table 0 D w) U ≤ value) ∧
    ∀ (h : ℕ) (C : Circ) (P : (Fin h → Bool) → ℝ), fits h C →
      (∀ w, 0 ≤ P w) → (∑ w, P w) = 1 →
      (∃ U : Finset X, U.card = t ∧ (value : ℝ) ≤ risk h C P U) ∧
      (0 < bonus → (∀ U : Finset X, U.card = t → risk h C P U ≤ (value : ℝ)) →
        ∃ R S : Finset X, R.card+S.card = b ∧
          d ≤ R.card*S.card ∧ bonus + R.card*S.card = lineGain ∧ lineUnion h C R S) :=
  PEqualNP.Outside.L_meta_32061_aux.main_32061
