import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_32059_aux

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

-- The gate accessor bridge is from L-meta-32013 (#43375).
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

-- Input length and bit lookup from L-meta-32013 (#43375).
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

end PEqualNP.Outside.L_meta_32059_aux

open PEqualNP.Outside.L_meta_32059_aux

theorem PEqualNP.Outside.L_meta_32059 : ∀ (N g : ℕ), g+1 < N →
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
  ∀ (h : ℕ) (C : Circ), legal h C → C.size ≤ g →
    (∃ w : Fin h → Bool, g*N < area (table h C w) ∧ area (table h C w) < N*(N-g)) →
    ∃ R S : Finset X, R.card + S.card = g+1 ∧ lineUnion h C R S := by
  intro N g _
  dsimp only
  intro h C hLegal hSize hArea
  obtain ⟨hBack, hOut, hGates⟩ := hLegal
  obtain ⟨w, hLow, hHigh⟩ := hArea
  exact whole_lines C hBack hOut hGates hSize w hLow hHigh
