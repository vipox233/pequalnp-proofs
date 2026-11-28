import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_32573_aux

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

section Bal
open Finset

def F (N s j : ℕ) : ℕ := j * s / N

def Sset (N s : ℕ) : Finset (Fin N) :=
  (univ : Finset (Fin N)).filter (fun y => F N s y.val < F N s (y.val + 1))

def sig (N t k : ℕ) : ℕ := (k % (N / Nat.gcd t N)) * t + k / (N / Nat.gcd t N)

theorem F_mono (N s : ℕ) : Monotone (F N s) := fun _ _ h =>
  Nat.div_le_div_right (Nat.mul_le_mul_right s h)

theorem F_shift {N : ℕ} (s : ℕ) (hN : 0 < N) (j m : ℕ) : F N s (j + N * m) = F N s j + s * m := by
  unfold F
  rw [show (j + N * m) * s = j * s + (s * m) * N by ring, Nat.add_mul_div_right _ _ hN]

theorem F_step {N s : ℕ} (hs : s ≤ N) (hN : 0 < N) (j : ℕ) : F N s (j + 1) ≤ F N s j + 1 := by
  unfold F
  calc (j + 1) * s / N ≤ (j * s + 1 * N) / N := Nat.div_le_div_right (by nlinarith)
    _ = j * s / N + 1 := Nat.add_mul_div_right _ _ hN

theorem memS {N : ℕ} (s : ℕ) (hN : 0 < N) (j : ℕ) :
    (⟨j % N, Nat.mod_lt _ hN⟩ : Fin N) ∈ Sset N s ↔ F N s j < F N s (j + 1) := by
  simp only [Sset, Finset.mem_filter, Finset.mem_univ, true_and]
  have h1 := F_shift s hN (j % N) (j / N)
  have h2 := F_shift s hN (j % N + 1) (j / N)
  have hd := Nat.mod_add_div j N
  rw [hd] at h1
  rw [show j % N + 1 + N * (j / N) = j + 1 by omega] at h2
  rw [h1, h2]
  omega

theorem back {N : ℕ} (x u y : Fin N) :
    (x.val + u.val + (y.val + N - x.val + N - u.val) % N) % N = y.val := by
  rw [Nat.add_mod_mod, show x.val + u.val + (y.val + N - x.val + N - u.val) = y.val + N * 2 by omega,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt y.isLt]

theorem injmod {N a i j : ℕ} (hi : i < N) (hj : j < N) (h : (a + i) % N = (a + j) % N) : i = j := by
  have h2 : i ≡ j [MOD N] := Nat.ModEq.add_left_cancel' a h
  unfold Nat.ModEq at h2
  rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h2

theorem tele {N s : ℕ} (hs : s ≤ N) (hN : 0 < N) (a t : ℕ) :
    ((range t).filter (fun i => F N s (a + i) < F N s (a + i + 1))).card = F N s (a + t) - F N s a := by
  rw [Finset.card_filter]
  have h : ∀ i ∈ range t, (if F N s (a + i) < F N s (a + i + 1) then 1 else 0) =
      (fun i => F N s (a + i)) (i + 1) - (fun i => F N s (a + i)) i := by
    intro i _
    have := F_step hs hN (a + i)
    have := F_mono N s (Nat.le_succ (a + i))
    simp only [← add_assoc]
    split_ifs <;> omega
  rw [Finset.sum_congr rfl h, Finset.sum_range_tsub (fun i j hij => F_mono N s (by omega))]
  simp

theorem cnt {N s : ℕ} (hs : s ≤ N) (hN : 0 < N) (x u : Fin N) (t : ℕ) (ht : t ≤ N) :
    ((univ : Finset (Fin N)).filter (fun y => y ∈ Sset N s ∧
      (y.val + N - x.val + N - u.val) % N < t)).card =
      F N s (x.val + u.val + t) - F N s (x.val + u.val) := by
  rw [← tele hs hN]
  symm
  apply Finset.card_bij (fun i _ => (⟨(x.val + u.val + i) % N, Nat.mod_lt _ hN⟩ : Fin N))
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨(memS s hN _).2 hi.2, ?_⟩
    have hb := back x u ⟨(x.val + u.val + i) % N, Nat.mod_lt _ hN⟩
    have h3 := injmod (Nat.mod_lt _ hN) (show i < N by omega) hb
    dsimp only at h3 ⊢
    omega
  · intro i hi j hj h
    simp only [Finset.mem_filter, Finset.mem_range] at hi hj
    exact injmod (show i < N by omega) (show j < N by omega) (Fin.mk.inj_iff.mp h)
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    have hb := back x u y
    have hy' : (⟨(x.val + u.val + (y.val + N - x.val + N - u.val) % N) % N, Nat.mod_lt _ hN⟩ : Fin N) = y :=
      Fin.ext hb
    refine ⟨(y.val + N - x.val + N - u.val) % N, ?_, hy'⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨hy.2, ?_⟩
    rw [← memS s hN, hy']
    exact hy.1

theorem L_pos {N : ℕ} (hN : 0 < N) (t : ℕ) : 0 < N / Nat.gcd t N :=
  Nat.div_pos (Nat.le_of_dvd hN (Nat.gcd_dvd_right t N)) (Nat.gcd_pos_of_pos_right t hN)

theorem NLg (N t : ℕ) : N = N / Nat.gcd t N * Nat.gcd t N :=
  (Nat.div_mul_cancel (Nat.gcd_dvd_right t N)).symm

theorem sig_inj {N : ℕ} (hN : 0 < N) (t : ℕ) (k k' : ℕ) (hk : k < N) (hk' : k' < N)
    (h : sig N t k % N = sig N t k' % N) : k = k' := by
  unfold sig at h
  have hL := L_pos hN t
  have hNL := NLg N t
  have hg : 0 < Nat.gcd t N := Nat.gcd_pos_of_pos_right t hN
  set L := N / Nat.gcd t N with hLd
  have hc : k / L < Nat.gcd t N := Nat.div_lt_of_lt_mul (by rw [← hNL]; exact hk)
  have hc' : k' / L < Nat.gcd t N := Nat.div_lt_of_lt_mul (by rw [← hNL]; exact hk')
  have hgN : (k % L) * t + k / L ≡ (k' % L) * t + k' / L [MOD Nat.gcd t N] :=
    Nat.ModEq.of_dvd (Nat.gcd_dvd_right t N) h
  have ht0 : t % Nat.gcd t N = 0 := Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_left t N)
  have e1 : ∀ m, (m % L) * t + m / L ≡ m / L [MOD Nat.gcd t N] := by
    intro m
    unfold Nat.ModEq
    rw [Nat.add_mod, Nat.mul_mod, ht0, mul_zero, Nat.zero_mod, zero_add, Nat.mod_mod]
  have hcc : k / L = k' / L := by
    have h2 := ((e1 k).symm.trans hgN).trans (e1 k')
    unfold Nat.ModEq at h2
    rwa [Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hc'] at h2
  rw [hcc] at h
  have h3 : (k % L) * t ≡ (k' % L) * t [MOD N] := Nat.ModEq.add_right_cancel' (k' / L) h
  have h4 : k % L ≡ k' % L [MOD L] := by
    have := Nat.ModEq.cancel_right_div_gcd hN h3
    rwa [Nat.gcd_comm] at this
  unfold Nat.ModEq at h4
  rw [Nat.mod_mod, Nat.mod_mod] at h4
  rw [← Nat.div_add_mod k L, ← Nat.div_add_mod k' L, hcc, h4]

theorem Lt_eq {N : ℕ} (hN : 0 < N) (t : ℕ) : N / Nat.gcd t N * t = N * (t / Nat.gcd t N) := by
  have hg : 0 < Nat.gcd t N := Nat.gcd_pos_of_pos_right t hN
  obtain ⟨L, hL⟩ := Nat.gcd_dvd_right t N
  obtain ⟨t', ht'⟩ := Nat.gcd_dvd_left t N
  generalize Nat.gcd t N = g at *
  subst hL ht'
  rw [Nat.mul_div_cancel_left _ hg, Nat.mul_div_cancel_left _ hg]
  ring

def ordF {N : ℕ} (hN : 0 < N) (t : ℕ) : Fin N → Fin N := fun k => ⟨sig N t k.val % N, Nat.mod_lt _ hN⟩

theorem ordF_inj {N : ℕ} (hN : 0 < N) (t : ℕ) : Function.Injective (ordF hN t) := by
  intro k k' h
  exact Fin.ext (sig_inj hN t k k' k.isLt k'.isLt (Fin.mk.inj_iff.mp h))

noncomputable def order {N : ℕ} (hN : 0 < N) (t : ℕ) : Equiv.Perm (Fin N) :=
  Equiv.ofBijective (ordF hN t) (Finite.injective_iff_bijective.mp (ordF_inj hN t))

def G (N s t u k : ℕ) : ℕ := F N s (sig N t k + u + t) - F N s (sig N t k + u)

theorem block {N s : ℕ} (hN : 0 < N) (t u q j : ℕ) (hj : j ≤ N / Nat.gcd t N) :
    ∑ i ∈ range j, G N s t u (N / Nat.gcd t N * q + i) = F N s (q + j * t + u) - F N s (q + u) := by
  have hL := L_pos hN t
  have hs : ∀ i ∈ range j, G N s t u (N / Nat.gcd t N * q + i) =
      (fun i => F N s (q + i * t + u)) (i + 1) - (fun i => F N s (q + i * t + u)) i := by
    intro i hi
    rw [Finset.mem_range] at hi
    unfold G sig
    have e1 : (N / Nat.gcd t N * q + i) % (N / Nat.gcd t N) = i := by
      rw [add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    have e2 : (N / Nat.gcd t N * q + i) / (N / Nat.gcd t N) = q := by
      rw [add_comm, Nat.add_mul_div_left _ _ hL, Nat.div_eq_of_lt (by omega), zero_add]
    rw [e1, e2]
    dsimp only
    rw [show i * t + q + u + t = q + (i + 1) * t + u by ring, show i * t + q + u = q + i * t + u by ring]
  rw [Finset.sum_congr rfl hs, Finset.sum_range_tsub (f := fun i => F N s (q + i * t + u))
    (fun a b hab => F_mono N s (by nlinarith))]
  simp

theorem full {N s : ℕ} (hN : 0 < N) (t u q : ℕ) :
    ∑ k ∈ range (N / Nat.gcd t N * q), G N s t u k = q * (s * (t / Nat.gcd t N)) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show N / Nat.gcd t N * (q + 1) = N / Nat.gcd t N * q + N / Nat.gcd t N by ring,
      Finset.sum_range_add, ih, block hN t u q _ le_rfl]
    have hLt := Lt_eq hN t
    rw [show q + N / Nat.gcd t N * t + u = q + u + N * (t / Nat.gcd t N) by rw [hLt]; ring,
      F_shift s hN]
    rw [Nat.add_sub_cancel_left]
    ring

theorem total {N s : ℕ} (hN : 0 < N) (t u r : ℕ) :
    ∑ k ∈ range r, G N s t u k = r / (N / Nat.gcd t N) * (s * (t / Nat.gcd t N)) +
      (F N s (r / (N / Nat.gcd t N) + r % (N / Nat.gcd t N) * t + u) - F N s (r / (N / Nat.gcd t N) + u)) := by
  have hL := L_pos hN t
  conv_lhs => rw [← Nat.div_add_mod r (N / Nat.gcd t N)]
  rw [Finset.sum_range_add, full hN, block hN t u _ _ (Nat.mod_lt _ hL).le]

theorem hits_eq {N s : ℕ} (hs : s ≤ N) (hN : 0 < N) (t : ℕ) (ht : t ≤ N) (r : ℕ) (hr : r ≤ N)
    (u : Fin N) :
    ((univ : Finset (Fin N × Fin N)).filter (fun z => ((order hN t).symm z.1).val < r ∧
      z.2 ∈ Sset N s ∧ (z.2.val + N - z.1.val + N - u.val) % N < t)).card =
      ∑ k ∈ range r, G N s t u.val k := by
  rw [Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product]
  have h1 : ∀ x : Fin N, (∑ y : Fin N, if (((order hN t).symm x).val < r ∧ y ∈ Sset N s ∧
      (y.val + N - x.val + N - u.val) % N < t) then 1 else 0) =
      if ((order hN t).symm x).val < r then F N s (x.val + u.val + t) - F N s (x.val + u.val)
      else 0 := by
    intro x
    split_ifs with hA
    · rw [← cnt hs hN x u t ht, Finset.card_filter]
      simp [hA]
    · simp [hA]
  rw [Finset.sum_congr rfl (fun x _ => h1 x), ← Equiv.sum_comp (order hN t)]
  simp only [Equiv.symm_apply_apply]
  have h2 : ∀ k : Fin N, (if k.val < r then F N s ((order hN t k).val + u.val + t) -
      F N s ((order hN t k).val + u.val) else 0) =
      (fun k => if k < r then G N s t u.val k else 0) k.val := by
    intro k
    have ho : (order hN t k).val = sig N t k.val % N := rfl
    have e := Nat.mod_add_div (sig N t k.val) N
    dsimp only
    split_ifs
    · rw [ho]
      unfold G
      rw [show sig N t k.val + u.val + t = sig N t k.val % N + u.val + t + N * (sig N t k.val / N) by
          linarith,
        show sig N t k.val + u.val = sig N t k.val % N + u.val + N * (sig N t k.val / N) by linarith,
        F_shift s hN, F_shift s hN]
      omega
    · rfl
  rw [Finset.sum_congr rfl (fun k _ => h2 k),
    Fin.sum_univ_eq_sum_range (fun k => if k < r then G N s t u.val k else 0) N, ← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem updiv {N : ℕ} (hN : 0 < N) (x y : ℕ) : (x + y) / N ≤ x / N + (y + N - 1) / N := by
  apply Nat.lt_succ_iff.mp
  rw [Nat.div_lt_iff_lt_mul hN]
  have h1 := Nat.div_add_mod x N
  have h2 := Nat.div_add_mod (y + N - 1) N
  have h3 := Nat.mod_lt x hN
  have h4 : y + N - 1 + 1 = y + N := by omega
  have h5 := Nat.mod_lt (y + N - 1) hN
  rw [Nat.succ_mul, add_mul]
  nlinarith

theorem bounds {N s : ℕ} (hN : 0 < N) (t r u : ℕ) :
    r * s * t / N ≤ ∑ k ∈ range r, G N s t u k ∧
      ∑ k ∈ range r, G N s t u k ≤ (r * s * t + N - 1) / N := by
  rw [total hN]
  have hLt := Lt_eq hN t
  have hr' := Nat.div_add_mod r (N / Nat.gcd t N)
  generalize r / (N / Nat.gcd t N) = q at *
  generalize r % (N / Nat.gcd t N) = j at *
  generalize t / Nat.gcd t N = t' at *
  generalize N / Nat.gcd t N = L at *
  have key : r * s * t = j * t * s + N * (q * (s * t')) := by
    have : (r : ℤ) * s * t = j * t * s + N * (q * (s * t')) := by
      have a1 : ((L : ℤ) * t) = N * t' := by exact_mod_cast hLt
      have a2 : ((L : ℤ) * q + j) = r := by exact_mod_cast hr'
      linear_combination (↑q * ↑s) * a1 - (↑s * ↑t) * a2
    exact_mod_cast this
  have hF : F N s (q + j * t + u) = ((q + u) * s + j * t * s) / N := by
    unfold F
    rw [show (q + j * t + u) * s = (q + u) * s + j * t * s by ring]
  have hF0 : F N s (q + u) = (q + u) * s / N := rfl
  have lo : (q + u) * s / N + j * t * s / N ≤ ((q + u) * s + j * t * s) / N := Nat.div_add_div_le_add_div
  have hi := updiv hN ((q + u) * s) (j * t * s)
  rw [hF, hF0, key, Nat.add_mul_div_left _ _ hN,
    show j * t * s + N * (q * (s * t')) + N - 1 = j * t * s + N - 1 + N * (q * (s * t')) by omega,
    Nat.add_mul_div_left _ _ hN]
  generalize ((q + u) * s + j * t * s) / N = D at *
  generalize (q + u) * s / N = A at *
  generalize j * t * s / N = B at *
  generalize (j * t * s + N - 1) / N = C at *
  omega

theorem lib945 (N : ℕ) (hN : 0 < N) (s : ℕ) (hs : s ≤ N) : ∃ S : Finset (Fin N), S.card = s ∧
    ∀ t : ℕ, t ≤ N → ∃ ord : Equiv.Perm (Fin N), ∀ r : ℕ, r ≤ N → ∀ u : Fin N,
      ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z =>
        (ord.symm z.1).val < r ∧ z.2 ∈ S ∧ (z.2.val + N - z.1.val + N - u.val) % N < t)).card ≤
          (r*s*t + N - 1)/N := by
  have hcard : (Sset N s).card = s := by
    have h := cnt hs hN ⟨0, hN⟩ ⟨0, hN⟩ N le_rfl
    have hfe : ((Finset.univ : Finset (Fin N)).filter (fun y => y ∈ Sset N s ∧
        (y.val + N - (⟨0, hN⟩ : Fin N).val + N - (⟨0, hN⟩ : Fin N).val) % N < N)) = Sset N s := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_left_iff_imp]
      intro _
      exact Nat.mod_lt _ hN
    rw [hfe] at h
    rw [h]
    simp only [zero_add]
    unfold F
    rw [Nat.mul_div_cancel_left _ hN]
    simp
  refine ⟨Sset N s, hcard, ?_⟩
  intro t ht
  refine ⟨order hN t, ?_⟩
  intro r hr u
  rw [hits_eq hs hN t ht r hr u]
  exact (bounds hN t r u.val).2

end Bal

private lemma exists_lineUnion_circuit' {N : ℕ} (R S : Finset (Fin N))
    (hne : 0 < R.card + S.card) :
    ∃ D : Circuit,
      ReadsBack (N + N + 0) D ∧
      D.output < N + N + 0 + D.size ∧
      (∀ a ∈ D.gates, a.inputs.length ≤ 2 ∧
        (a.op = .and ∨ a.op = .or ∨ (a.op = .not ∧ a.inputs.length = 1))) ∧
      D.size = R.card + S.card - 1 ∧
      ∀ (w : Fin 0 → Bool) (x y : Fin N),
        D.eval (oneEach x y ++ List.ofFn w) = decide (x ∈ R ∨ y ∈ S) := by
  let ws : List ℕ := R.toList.map Fin.val ++ S.toList.map (fun j => N + j.val)
  have hlen : ws.length = R.card + S.card := by simp [ws]
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
    have hD_size : D.size = R.card + S.card - 1 := by
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
      · rcases List.mem_map.mp hu with ⟨i, hi, rfl⟩
        have hiN : i.val < N := i.isLt
        simp only [hiN, ↓reduceDIte, decide_eq_true_eq, Fin.ext_iff] at htrue
        have hxi : i = x := Fin.ext htrue
        exact Or.inl (hxi ▸ Finset.mem_toList.mp hi)
      · rcases List.mem_map.mp hu with ⟨j, hj, rfl⟩
        have hj1 : ¬ N + j.val < N := by omega
        have hj2 : N + j.val < N + N := by have := j.isLt; omega
        simp only [hj1, hj2, ↓reduceDIte, Nat.add_sub_cancel_left, decide_eq_true_eq, Fin.ext_iff] at htrue
        have hyj : j = y := Fin.ext htrue
        exact Or.inr (hyj ▸ Finset.mem_toList.mp hj)
    · rintro (hx | hy)
      · refine ⟨x.val, List.mem_append_left _ (List.mem_map.mpr ⟨x, Finset.mem_toList.mpr hx, rfl⟩), ?_⟩
        rw [oneEach_append_getD x y w x.val (by have := x.isLt; omega)]
        simp [x.isLt]
      · refine ⟨N + y.val, List.mem_append_right _ (List.mem_map.mpr ⟨y, Finset.mem_toList.mpr hy, rfl⟩), ?_⟩
        rw [oneEach_append_getD x y w (N + y.val) (by have := y.isLt; omega)]
        have h1 : ¬ N + y.val < N := by omega
        have h2 : N + y.val < N + N := by have := y.isLt; omega
        simp [h1, h2]

private def wcolor (N : ℕ) (x y : Fin N) : Fin N :=
  ⟨(y.val + N - x.val) % N, Nat.mod_lt _ (Fin.pos x)⟩

private def win (N t : ℕ) (u : Fin N) : Finset (Fin N) :=
  (Finset.univ : Finset (Fin N)).filter (fun c : Fin N => (c.val + N - u.val) % N < t)

private lemma inside_iff {N t : ℕ} (x y u : Fin N) :
    (y.val + N - x.val + N - u.val) % N < t ↔ wcolor N x y ∈ win N t u := by
  have hx := x.isLt
  have hu := u.isLt
  have h1 : y.val + N - x.val + N - u.val = (y.val + N - x.val) + (N - u.val) := by omega
  have h2 : (y.val + N - x.val) % N + N - u.val = (y.val + N - x.val) % N + (N - u.val) := by omega
  have key : (y.val + N - x.val + N - u.val) % N = ((wcolor N x y).val + N - u.val) % N := by
    show _ = ((y.val + N - x.val) % N + N - u.val) % N
    rw [h1, h2]
    conv_rhs => rw [Nat.add_mod, Nat.mod_mod]
    exact Nat.add_mod _ _ _
  simp only [win, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [key]

private lemma wcolor_row {N : ℕ} (x : Fin N) : Function.Bijective (wcolor N x) := by
  refine Finite.injective_iff_bijective.mp ?_
  intro y1 y2 h
  have h' : (y1.val + N - x.val) % N = (y2.val + N - x.val) % N := congrArg Fin.val h
  have hx := x.isLt
  have e1 : y1.val + N - x.val = (N - x.val) + y1.val := by omega
  have e2 : y2.val + N - x.val = (N - x.val) + y2.val := by omega
  rw [e1, e2] at h'
  exact Fin.ext (injmod y1.isLt y2.isLt h')

private lemma wcolor_col {N : ℕ} (y : Fin N) : Function.Bijective (fun x => wcolor N x y) := by
  refine Finite.injective_iff_bijective.mp ?_
  intro x1 x2 h
  have h' : (y.val + N - x1.val) % N = (y.val + N - x2.val) % N := congrArg Fin.val h
  have h1 := x1.isLt
  have h2 := x2.isLt
  have hm : Nat.ModEq N (y.val + N - x1.val) (y.val + N - x2.val) := h'
  have e : (y.val + N - x1.val + (x1.val + x2.val)) % N = (y.val + N - x2.val + (x1.val + x2.val)) % N :=
    hm.add_right _
  have e1 : y.val + N - x1.val + (x1.val + x2.val) = (y.val + N) + x2.val := by omega
  have e2 : y.val + N - x2.val + (x1.val + x2.val) = (y.val + N) + x1.val := by omega
  rw [e1, e2] at e
  exact Fin.ext (injmod x2.isLt x1.isLt e).symm

private lemma card_filter_bij {N t : ℕ} (f : Fin N → Fin N) (hf : Function.Bijective f) (ht : t ≤ N) :
    ((Finset.univ : Finset (Fin N)).filter (fun z : Fin N => (f z).val < t)).card = t :=
  (Finset.card_bijective f hf (fun i => by simp)).trans (card_filter_val_lt ht)

private lemma win_card {N t : ℕ} (ht : t ≤ N) (u : Fin N) : (win N t u).card = t :=
  card_filter_bij (wcolor N u) (wcolor_row u) ht

private lemma mem_win_count {N t : ℕ} (ht : t ≤ N) (c : Fin N) :
    ((Finset.univ : Finset (Fin N)).filter (fun u : Fin N => c ∈ win N t u)).card = t := by
  have h : ((Finset.univ : Finset (Fin N)).filter (fun u : Fin N => c ∈ win N t u)) =
      (Finset.univ : Finset (Fin N)).filter (fun u : Fin N => (wcolor N u c).val < t) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, win]
    exact Iff.rfl
  rw [h]
  exact card_filter_bij (fun u => wcolor N u c) (wcolor_col c) ht

private lemma sum_filter_win {N t : ℕ} (ht : t ≤ N) (A : Finset (Fin N × Fin N)) :
    ∑ u : Fin N, (A.filter (fun z => wcolor N z.1 z.2 ∈ win N t u)).card = A.card * t := by
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  have hz : ∀ z ∈ A, (∑ u : Fin N, if wcolor N z.1 z.2 ∈ win N t u then 1 else 0) = t := by
    intro z _
    rw [← Finset.card_filter]
    exact mem_win_count ht (wcolor N z.1 z.2)
  rw [Finset.sum_congr rfl hz, Finset.sum_const, smul_eq_mul]

private lemma sum_loss_win_ge {N g t : ℕ} (htN : N < 2 * t) (htle : t ≤ N)
    (H : Fin N → Fin N → Bool) (hArea : cellArea H ≤ g * N) :
    N * (N * t) ≤ (∑ u : Fin N, lossOf (wcolor N) H (win N t u)) + N * ((2 * t - N) * g) := by
  have hpt : ∀ u : Fin N,
      lossOf (wcolor N) H (win N t u) + 2 * hitOf (wcolor N) H (win N t u) = N * t + cellArea H := by
    intro u
    have h := loss_add_two_hit (wcolor N) (fun x => wcolor_row x) H (win N t u)
    rwa [win_card htle u] at h
  have hsum : (∑ u : Fin N, lossOf (wcolor N) H (win N t u)) +
      2 * ∑ u : Fin N, hitOf (wcolor N) H (win N t u) = N * (N * t + cellArea H) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_congr rfl (fun u _ => hpt u)]
    simp
  have hhit : ∑ u : Fin N, hitOf (wcolor N) H (win N t u) = cellArea H * t := by
    have hA := sum_filter_win htle
      ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => H z.1 z.2 = true))
    have hEq : ∀ u : Fin N, hitOf (wcolor N) H (win N t u) =
        (((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => H z.1 z.2 = true)).filter
          (fun z => wcolor N z.1 z.2 ∈ win N t u)).card := by
      intro u
      unfold hitOf
      rw [Finset.filter_filter]
    rw [Finset.sum_congr rfl (fun u _ => hEq u)]
    exact hA
  rw [hhit] at hsum
  obtain ⟨a, ha⟩ : ∃ a, 2 * t = N + a := ⟨2 * t - N, by omega⟩
  have ha' : 2 * t - N = a := by omega
  rw [ha']
  have h1 : cellArea H * a ≤ g * N * a := Nat.mul_le_mul_right _ hArea
  have h2 : 2 * (cellArea H * t) = cellArea H * N + cellArea H * a := by
    calc 2 * (cellArea H * t) = cellArea H * (2 * t) := by ring
      _ = cellArea H * (N + a) := by rw [ha]
      _ = cellArea H * N + cellArea H * a := by ring
  nlinarith [h1, h2, hsum]

private lemma exists_overlap_ceil {N t : ℕ} (hN : 0 < N) (htle : t ≤ N) (R S : Finset (Fin N)) :
    ∃ u : Fin N, (R.card * S.card * t + N - 1) / N ≤ overlapHit (wcolor N) R S (win N t u) := by
  by_contra hall
  have hall' : ∀ u : Fin N,
      overlapHit (wcolor N) R S (win N t u) + 1 ≤ (R.card * S.card * t + N - 1) / N := by
    intro u
    by_contra hu
    exact hall ⟨u, by omega⟩
  have hsum : ∑ u : Fin N, overlapHit (wcolor N) R S (win N t u) = R.card * S.card * t := by
    have h := sum_filter_win htle (R ×ˢ S)
    rw [Finset.card_product] at h
    exact h
  have hc_le : N * ((R.card * S.card * t + N - 1) / N) ≤ R.card * S.card * t + N - 1 :=
    Nat.mul_div_le _ _
  have hstep : ∀ u : Fin N,
      N * overlapHit (wcolor N) R S (win N t u) + 1 ≤ R.card * S.card * t := by
    intro u
    have h2 : N * (overlapHit (wcolor N) R S (win N t u) + 1) ≤
        N * ((R.card * S.card * t + N - 1) / N) := Nat.mul_le_mul_left _ (hall' u)
    rw [Nat.mul_add, Nat.mul_one] at h2
    omega
  have hs := Finset.sum_le_sum (fun u (_ : u ∈ (Finset.univ : Finset (Fin N))) => hstep u)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum, Finset.sum_const, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, smul_eq_mul, mul_one] at hs
  omega

private lemma balanced {N : ℕ} (hN : 0 < N) (r s t : ℕ) (hr : r ≤ N) (hs : s ≤ N) (ht : t ≤ N) :
    ∃ R S : Finset (Fin N), R.card = r ∧ S.card = s ∧
      ∀ u : Fin N, overlapHit (wcolor N) R S (win N t u) ≤ (r * s * t + N - 1) / N := by
  obtain ⟨S, hS, hbal⟩ := lib945 N hN s hs
  obtain ⟨ord, hord⟩ := hbal t ht
  refine ⟨(Finset.univ : Finset (Fin N)).filter (fun x : Fin N => (ord.symm x).val < r), S, ?_, hS,
    fun u => ?_⟩
  · exact card_filter_bij (fun x => ord.symm x) ord.symm.bijective hr
  · have h := hord r hr u
    have hEq : overlapHit (wcolor N)
        ((Finset.univ : Finset (Fin N)).filter (fun x : Fin N => (ord.symm x).val < r)) S (win N t u) =
        ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z =>
          (ord.symm z.1).val < r ∧ z.2 ∈ S ∧ (z.2.val + N - z.1.val + N - u.val) % N < t)).card := by
      unfold overlapHit
      congr 1
      ext z
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and, inside_iff, and_assoc]
    rw [hEq]
    exact h

private def wloss (N t : ℕ) (H : Fin N → Fin N → Bool) (u : Fin N) : ℕ :=
  ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z =>
    H z.1 z.2 ≠ decide ((z.2.val + N - z.1.val + N - u.val) % N < t))).card

private lemma wloss_eq {N t : ℕ} (H : Fin N → Fin N → Bool) (u : Fin N) :
    wloss N t H u = lossOf (wcolor N) H (win N t u) := by
  unfold wloss lossOf
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, inside_iff]

private lemma overlap_eq {N t : ℕ} (R S : Finset (Fin N)) (u : Fin N) :
    ((R ×ˢ S).filter (fun z => (z.2.val + N - z.1.val + N - u.val) % N < t)).card =
      overlapHit (wcolor N) R S (win N t u) := by
  unfold overlapHit
  exact congrArg Finset.card (Finset.filter_congr fun z _ => inside_iff z.1 z.2 u)

private lemma ceil_ge {N t p : ℕ} (hN : 0 < N) (htN : N < 2 * t) :
    p ≤ 2 * ((p * t + N - 1) / N) := by
  have h1 : p * t ≤ N * ((p * t + N - 1) / N) := by
    have h := Nat.div_add_mod (p * t + N - 1) N
    have hr := Nat.mod_lt (p * t + N - 1) hN
    omega
  by_contra hlt
  have hlt' : 2 * ((p * t + N - 1) / N) + 1 ≤ p := by omega
  have h2 : N * (2 * ((p * t + N - 1) / N) + 1) ≤ N * p := Nat.mul_le_mul_left _ hlt'
  have h4 : p * N ≤ p * (2 * t) := Nat.mul_le_mul_left _ (le_of_lt htN)
  nlinarith [h1, h2, h4, hN]

private lemma value_add_eq' {N g d t : ℕ} (hNg : 2 * g + 1 < N) (htN : N < 2 * t) (htle : t ≤ N) :
    let b := g + 1
    let a := 2 * t - N
    let bonus := (Finset.range (b + 1)).sup (fun r =>
      if d ≤ r * (b - r) then a + r * (b - r) - 2 * ((r * (b - r) * t + N - 1) / N) else 0)
    let value := N * t - a * g - bonus
    value + a * g + bonus = N * t := by
  intro b a bonus value
  have hN : 0 < N := by omega
  have hbonus_le : bonus ≤ a := by
    refine Finset.sup_le fun r _ => ?_
    split_ifs
    · have hc := ceil_ge (p := r * (b - r)) hN htN
      omega
    · exact Nat.zero_le _
  have ha_le_t : a ≤ t := by omega
  have hbound : a * g + bonus ≤ N * t := by
    have h1 : a * g + bonus ≤ a * (g + 1) := by nlinarith
    have h2 : a * (g + 1) ≤ t * (g + 1) := Nat.mul_le_mul_right _ ha_le_t
    have h3 : t * (g + 1) ≤ t * N := Nat.mul_le_mul_left _ (by omega)
    nlinarith
  have hv : value = N * t - (a * g + bonus) := Nat.sub_sub _ _ _
  omega

private lemma main_part1 {N g d t : ℕ} (hg : 0 < g) (hNg : 2 * g + 1 < N)
    (hd0 : 0 < d) (hdN : d < N) (htN : N < 2 * t) (htle : t ≤ N) :
    let b := g + 1
    let a := 2 * t - N
    let cap := b * N - d
    let bonus := (Finset.range (b + 1)).sup (fun r =>
      if d ≤ r * (b - r) then a + r * (b - r) - 2 * ((r * (b - r) * t + N - 1) / N) else 0)
    let value := N * t - a * g - bonus
    ∃ D : Circuit,
      (ReadsBack (N + N + 0) D ∧ D.output < N + N + 0 + D.size ∧
        ∀ gate ∈ D.gates, gate.inputs.length ≤ 2 ∧
          (gate.op = .and ∨ gate.op = .or ∨ (gate.op = .not ∧ gate.inputs.length = 1))) ∧
      D.size ≤ g ∧
      (∀ w : Fin 0 → Bool, cellArea (fun x y : Fin N => D.eval (oneEach x y ++ List.ofFn w)) ≤ cap) ∧
      ∀ (w : Fin 0 → Bool) (u : Fin N),
        wloss N t (fun x y : Fin N => D.eval (oneEach x y ++ List.ofFn w)) u ≤ value := by
  intro b a cap bonus value
  have hN : 0 < N := by omega
  have hval_sum : value + a * g + bonus = N * t := value_add_eq' hNg htN htle
  by_cases hbon : bonus = 0
  · obtain ⟨D, hrb, hout, hgates, hsize, heval⟩ :=
      exists_lineUnion_circuit (N := N) g 0 (by omega) hN (by omega)
    let R : Finset (Fin N) := Finset.univ.filter (fun x : Fin N => x.val < g)
    have hRcard : R.card = g := card_filter_val_lt (by omega)
    have htab : ∀ w : Fin 0 → Bool,
        (fun x y : Fin N => D.eval (oneEach x y ++ List.ofFn w)) =
        (fun x y => decide (x ∈ R ∨ y ∈ (∅ : Finset (Fin N)))) := by
      intro w; funext x y; rw [heval w x y]; simp [R]
    refine ⟨D, ⟨hrb, hout, hgates⟩, by omega, fun w => ?_, fun w u => ?_⟩
    · rw [htab w]
      have hA := lineUnion_area R ∅
      rw [hRcard, Finset.card_empty] at hA
      simp only [Nat.add_zero, Nat.mul_zero] at hA
      have h1 : g * N + d ≤ b * N := by dsimp only [b]; nlinarith
      dsimp only [cap]
      omega
    · rw [htab w, wloss_eq]
      have hL := lineUnion_loss_eq (wcolor N) (fun x => wcolor_row x) (fun y => wcolor_col y) htN R ∅
        (win N t u) (win_card htle u)
      have hov0 : overlapHit (wcolor N) R ∅ (win N t u) = 0 := by simp [overlapHit]
      rw [hRcard, Finset.card_empty, hov0] at hL
      have hmul : (g + 0) * (2 * t - N) = a * g := by dsimp only [a]; ring
      omega
  · have hbon_pos : 0 < bonus := Nat.pos_of_ne_zero hbon
    obtain ⟨r, hrMem, hrEq⟩ :=
      Finset.exists_mem_eq_sup (Finset.range (b + 1)) ⟨0, Finset.mem_range.mpr (Nat.succ_pos b)⟩
        (fun r => if d ≤ r * (b - r) then a + r * (b - r) - 2 * ((r * (b - r) * t + N - 1) / N) else 0)
    have hrLe : r ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hrMem)
    have hfeas : d ≤ r * (b - r) := by
      by_contra hnot
      simp only [hnot, ↓reduceIte] at hrEq
      have : bonus = 0 := hrEq
      omega
    simp only [hfeas, ↓reduceIte] at hrEq
    have hbon_eq : bonus = a + r * (b - r) - 2 * ((r * (b - r) * t + N - 1) / N) := hrEq
    have hsum_rs : r + (b - r) = b := Nat.add_sub_of_le hrLe
    obtain ⟨R, S, hRcard, hScard, hov⟩ := balanced hN r (b - r) t (by omega) (by omega) htle
    have hpos : 0 < R.card + S.card := by rw [hRcard, hScard]; omega
    obtain ⟨D, hrb, hout, hgates, hsize, heval⟩ := exists_lineUnion_circuit' R S hpos
    have htab : ∀ w : Fin 0 → Bool,
        (fun x y : Fin N => D.eval (oneEach x y ++ List.ofFn w)) =
        (fun x y => decide (x ∈ R ∨ y ∈ S)) := by
      intro w; funext x y; exact heval w x y
    refine ⟨D, ⟨hrb, hout, hgates⟩, by rw [hsize, hRcard, hScard]; omega, fun w => ?_, fun w u => ?_⟩
    · rw [htab w]
      have hA := lineUnion_area R S
      rw [hRcard, hScard, hsum_rs] at hA
      have hle_bN : d ≤ b * N := by nlinarith
      dsimp only [cap]
      omega
    · rw [htab w, wloss_eq]
      have hL := lineUnion_loss_eq (wcolor N) (fun x => wcolor_row x) (fun y => wcolor_col y) htN R S
        (win N t u) (win_card htle u)
      have hov_le := hov u
      rw [hRcard, hScard, hsum_rs] at hL
      have hb_lg : b * (2 * t - N) = a * g + a := by dsimp only [b, a]; ring
      rw [hb_lg] at hL
      omega

private lemma main_part2 {N g d t h : ℕ} (hg : 0 < g) (hNg : 2 * g + 1 < N)
    (hd0 : 0 < d) (hdN : d < N) (htN : N < 2 * t) (htle : t ≤ N)
    (C : Circuit) (P : (Fin h → Bool) → ℝ)
    (hBack : ReadsBack (N + N + h) C) (hOut : C.output < N + N + h + C.size)
    (hGates : ∀ gate ∈ C.gates, gate.inputs.length ≤ 2 ∧
      (gate.op = .and ∨ gate.op = .or ∨ (gate.op = .not ∧ gate.inputs.length = 1)))
    (hSize : C.size ≤ g)
    (hCap : ∀ w : Fin h → Bool,
      cellArea (fun x y : Fin N => C.eval (oneEach x y ++ List.ofFn w)) ≤ (g + 1) * N - d)
    (hP_nonneg : ∀ w, 0 ≤ P w) (hP_sum : (∑ w, P w) = 1) :
    let b := g + 1
    let a := 2 * t - N
    let bonus := (Finset.range (b + 1)).sup (fun r =>
      if d ≤ r * (b - r) then a + r * (b - r) - 2 * ((r * (b - r) * t + N - 1) / N) else 0)
    let value := N * t - a * g - bonus
    let risk := fun (u : Fin N) =>
      ∑ w : Fin h → Bool, P w * (wloss N t (fun x y => C.eval (oneEach x y ++ List.ofFn w)) u : ℝ)
    (∃ u : Fin N, (value : ℝ) ≤ risk u) ∧
    (0 < bonus → (∀ u : Fin N, risk u ≤ (value : ℝ)) →
      ∃ R S : Finset (Fin N), R.card + S.card = b ∧
        d ≤ R.card * S.card ∧
        bonus + 2 * ((R.card * S.card * t + N - 1) / N) = a + R.card * S.card ∧
        (Finset.univ.sup (fun u : Fin N =>
          ((R ×ˢ S).filter (fun z => (z.2.val + N - z.1.val + N - u.val) % N < t)).card)) =
            (R.card * S.card * t + N - 1) / N ∧
        ∀ (w : Fin h → Bool) (x y : Fin N),
          C.eval (oneEach x y ++ List.ofFn w) = decide (x ∈ R ∨ y ∈ S)) := by
  intro b a bonus value risk
  have hN : 0 < N := by omega
  have hval_sum : value + a * g + bonus = N * t := value_add_eq' hNg htN htle
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
    have hrisk_eq : ∀ u : Fin N,
        risk u = (lossOf (wcolor N) (fun x y => decide (x ∈ R ∨ y ∈ S)) (win N t u) : ℝ) := by
      intro u
      dsimp only [risk]
      simp_rw [hfun, wloss_eq]
      rw [← Finset.sum_mul, hP_sum, one_mul]
    have hd_le_p : d ≤ R.card * S.card := by
      have hA := lineUnion_area R S
      have hcap0 : cellArea (fun x y => decide (x ∈ R ∨ y ∈ S)) ≤ (g + 1) * N - d := by
        rw [← hfun w0]
        exact hCap w0
      rw [hRScard] at hA
      have hdbN : d ≤ (g + 1) * N := by nlinarith
      omega
    have hbon_ge : a + R.card * S.card - 2 * ((R.card * S.card * t + N - 1) / N) ≤ bonus := by
      have hrMem : R.card ∈ Finset.range (b + 1) := Finset.mem_range.mpr (by omega)
      have hsEq : b - R.card = S.card := by omega
      have hsup := Finset.le_sup (f := fun r =>
        if d ≤ r * (b - r) then a + r * (b - r) - 2 * ((r * (b - r) * t + N - 1) / N) else 0) hrMem
      simpa [hsEq, hd_le_p] using hsup
    have hloss : ∀ u : Fin N,
        lossOf (wcolor N) (fun x y => decide (x ∈ R ∨ y ∈ S)) (win N t u) + (a * g + a) +
          R.card * S.card = N * t + 2 * overlapHit (wcolor N) R S (win N t u) := by
      intro u
      have hL := lineUnion_loss_eq (wcolor N) (fun x => wcolor_row x) (fun y => wcolor_col y) htN R S
        (win N t u) (win_card htle u)
      rw [hRScard] at hL
      have hb_eq : b * (2 * t - N) = a * g + a := by dsimp only [b, a]; ring
      rw [hb_eq] at hL
      exact hL
    obtain ⟨u0, hu0⟩ := exists_overlap_ceil hN htle R S
    constructor
    · refine ⟨u0, ?_⟩
      rw [hrisk_eq u0]
      have h1 := hloss u0
      have hge : value ≤ lossOf (wcolor N) (fun x y => decide (x ∈ R ∨ y ∈ S)) (win N t u0) := by
        omega
      exact_mod_cast hge
    · intro hbon_pos hall_le
      have hnat : ∀ u : Fin N,
          lossOf (wcolor N) (fun x y => decide (x ∈ R ∨ y ∈ S)) (win N t u) ≤ value := by
        intro u
        have hle_real : (lossOf (wcolor N) (fun x y => decide (x ∈ R ∨ y ∈ S)) (win N t u) : ℝ) ≤
            (value : ℝ) := by
          rw [← hrisk_eq u]
          exact hall_le u
        exact_mod_cast hle_real
      have h3 := hloss u0
      have h4 := hnat u0
      have hbon_eq : bonus + 2 * ((R.card * S.card * t + N - 1) / N) = a + R.card * S.card := by
        omega
      have hov_le : ∀ u : Fin N,
          overlapHit (wcolor N) R S (win N t u) ≤ (R.card * S.card * t + N - 1) / N := by
        intro u
        have h1 := hloss u
        have h2 := hnat u
        omega
      refine ⟨R, S, hRScard, hd_le_p, hbon_eq, ?_, hLU⟩
      apply le_antisymm
      · refine Finset.sup_le fun u _ => ?_
        rw [overlap_eq]
        exact hov_le u
      · have hle := Finset.le_sup (f := fun u : Fin N =>
          ((R ×ˢ S).filter (fun z => (z.2.val + N - z.1.val + N - u.val) % N < t)).card)
          (Finset.mem_univ u0)
        have hle' : overlapHit (wcolor N) R S (win N t u0) ≤ Finset.univ.sup (fun u : Fin N =>
            ((R ×ˢ S).filter (fun z => (z.2.val + N - z.1.val + N - u.val) % N < t)).card) := by
          rw [← overlap_eq]
          exact hle
        exact le_trans hu0 hle'
  · push Not at hBig
    have hsum_risk_ge : (N : ℝ) * ((value : ℝ) + (bonus : ℝ)) ≤ ∑ u : Fin N, risk u := by
      dsimp only [risk]
      rw [Finset.sum_comm]
      have hper_w : ∀ w : Fin h → Bool,
          P w * ((N : ℝ) * ((value : ℝ) + (bonus : ℝ))) ≤
            ∑ u : Fin N, P w * (wloss N t (fun x y => C.eval (oneEach x y ++ List.ofFn w)) u : ℝ) := by
        intro w
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ (hP_nonneg w)
        have hnat := sum_loss_win_ge htN htle
          (fun x y => C.eval (oneEach x y ++ List.ofFn w)) (hBig w)
        change N * (N * t) ≤
            (∑ u : Fin N, lossOf (wcolor N) (fun x y => C.eval (oneEach x y ++ List.ofFn w)) (win N t u)) +
              N * (a * g) at hnat
        have hnat' : N * (value + bonus) ≤
            ∑ u : Fin N, wloss N t (fun x y => C.eval (oneEach x y ++ List.ofFn w)) u := by
          simp_rw [wloss_eq]
          have h1 : N * (value + bonus) + N * (a * g) = N * (N * t) := by
            calc N * (value + bonus) + N * (a * g)
                = N * (value + a * g + bonus) := by ring
              _ = N * (N * t) := congrArg (N * ·) hval_sum
          omega
        have hreal : ((N * (value + bonus) : ℕ) : ℝ) ≤
            ((∑ u : Fin N, wloss N t (fun x y => C.eval (oneEach x y ++ List.ofFn w)) u : ℕ) : ℝ) :=
          Nat.cast_le.mpr hnat'
        simpa [Nat.cast_mul, Nat.cast_add, Nat.cast_sum] using hreal
      calc
        (N : ℝ) * ((value : ℝ) + (bonus : ℝ))
            = (∑ w : Fin h → Bool, P w) * ((N : ℝ) * ((value : ℝ) + (bonus : ℝ))) := by
              rw [hP_sum, one_mul]
        _ = ∑ w : Fin h → Bool, P w * ((N : ℝ) * ((value : ℝ) + (bonus : ℝ))) := by
              rw [Finset.sum_mul]
        _ ≤ ∑ w : Fin h → Bool, ∑ u : Fin N,
              P w * (wloss N t (fun x y => C.eval (oneEach x y ++ List.ofFn w)) u : ℝ) :=
              Finset.sum_le_sum fun w _ => hper_w w
    have hNr : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
    have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0, hN⟩, Finset.mem_univ _⟩
    constructor
    · by_contra hall
      push Not at hall
      have hlt_sum : ∑ u : Fin N, risk u < ∑ _u : Fin N, (value : ℝ) :=
        Finset.sum_lt_sum_of_nonempty hne fun u _ => hall u
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin] at hlt_sum
      have hbon_nonneg : (0 : ℝ) ≤ (bonus : ℝ) := Nat.cast_nonneg bonus
      nlinarith
    · intro hbon_pos hall_le
      exfalso
      have hle_sum : ∑ u : Fin N, risk u ≤ ∑ _u : Fin N, (value : ℝ) :=
        Finset.sum_le_sum fun u _ => hall_le u
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin] at hle_sum
      have hbon_real : (0 : ℝ) < (bonus : ℝ) := Nat.cast_pos.mpr hbon_pos
      nlinarith

theorem main_32573 : (∀ (N g d t : ℕ), 0 < g → 2*g+1 < N → 0 < d → d < N → N < 2*t → t ≤ N →
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
  let b := g+1
  let a := 2*t-N
  let cap := b*N-d
  let ceiling := fun (p : ℕ) => (p*t+N-1)/N
  let bonus := (Finset.range (b+1)).sup (fun r =>
    let p := r*(b-r)
    if d ≤ p then a+p-2*ceiling p else 0)
  let value := N*t-a*g-bonus
  let inside := fun (x y u : X) => (y.val + N - x.val + N - u.val) % N < t
  let overlaps := fun (R S : Finset X) (u : X) =>
    ((R ×ˢ S).filter (fun z => inside z.1 z.2 u)).card
  let loss := fun (H : X → X → Bool) (u : X) =>
    ((Finset.univ : Finset (X × X)).filter (fun z =>
      H z.1 z.2 ≠ decide (inside z.1 z.2 u))).card
  let fits := fun (h : ℕ) (C : Circ) =>
    legal h C ∧ C.size ≤ g ∧ ∀ w : Fin h → Bool, area (table h C w) ≤ cap
  let risk := fun (h : ℕ) (C : Circ) (P : (Fin h → Bool) → ℝ) (u : X) =>
    ∑ w, P w * (loss (table h C w) u : ℝ)
  (∃ D : Circ, fits 0 D ∧ ∀ (w : Fin 0 → Bool) (u : X), loss (table 0 D w) u ≤ value) ∧
  ∀ (h : ℕ) (C : Circ) (P : (Fin h → Bool) → ℝ), fits h C →
    (∀ w, 0 ≤ P w) → (∑ w, P w) = 1 →
    (∃ u : X, (value : ℝ) ≤ risk h C P u) ∧
    (0 < bonus → (∀ u : X, risk h C P u ≤ (value : ℝ)) →
      ∃ R S : Finset X, R.card+S.card = b ∧ d ≤ R.card*S.card ∧
        bonus + 2*ceiling (R.card*S.card) = a + R.card*S.card ∧
        (Finset.univ.sup (overlaps R S)) = ceiling (R.card*S.card) ∧ lineUnion h C R S)) := by
  intro N g d t hg hNg hd0 hdN htN htle
  dsimp only
  constructor
  · obtain ⟨D, hleg, hsz, hcap, hloss⟩ := main_part1 hg hNg hd0 hdN htN htle
    exact ⟨D, ⟨hleg, hsz, hcap⟩, hloss⟩
  · intro h C P ⟨⟨hBack, hOut, hGates⟩, hSize, hCap⟩ hP_nonneg hP_sum
    exact main_part2 hg hNg hd0 hdN htN htle C P hBack hOut hGates hSize hCap hP_nonneg hP_sum

end PEqualNP.Outside.L_meta_32573_aux

theorem PEqualNP.Outside.L_meta_32573 : (∀ (N g d t : ℕ), 0 < g → 2*g+1 < N → 0 < d → d < N → N < 2*t → t ≤ N →
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
  let b := g+1
  let a := 2*t-N
  let cap := b*N-d
  let ceiling := fun (p : ℕ) => (p*t+N-1)/N
  let bonus := (Finset.range (b+1)).sup (fun r =>
    let p := r*(b-r)
    if d ≤ p then a+p-2*ceiling p else 0)
  let value := N*t-a*g-bonus
  let inside := fun (x y u : X) => (y.val + N - x.val + N - u.val) % N < t
  let overlaps := fun (R S : Finset X) (u : X) =>
    ((R ×ˢ S).filter (fun z => inside z.1 z.2 u)).card
  let loss := fun (H : X → X → Bool) (u : X) =>
    ((Finset.univ : Finset (X × X)).filter (fun z =>
      H z.1 z.2 ≠ decide (inside z.1 z.2 u))).card
  let fits := fun (h : ℕ) (C : Circ) =>
    legal h C ∧ C.size ≤ g ∧ ∀ w : Fin h → Bool, area (table h C w) ≤ cap
  let risk := fun (h : ℕ) (C : Circ) (P : (Fin h → Bool) → ℝ) (u : X) =>
    ∑ w, P w * (loss (table h C w) u : ℝ)
  (∃ D : Circ, fits 0 D ∧ ∀ (w : Fin 0 → Bool) (u : X), loss (table 0 D w) u ≤ value) ∧
  ∀ (h : ℕ) (C : Circ) (P : (Fin h → Bool) → ℝ), fits h C →
    (∀ w, 0 ≤ P w) → (∑ w, P w) = 1 →
    (∃ u : X, (value : ℝ) ≤ risk h C P u) ∧
    (0 < bonus → (∀ u : X, risk h C P u ≤ (value : ℝ)) →
      ∃ R S : Finset X, R.card+S.card = b ∧ d ≤ R.card*S.card ∧
        bonus + 2*ceiling (R.card*S.card) = a + R.card*S.card ∧
        (Finset.univ.sup (overlaps R S)) = ceiling (R.card*S.card) ∧ lineUnion h C R S)) := by
  exact PEqualNP.Outside.L_meta_32573_aux.main_32573
