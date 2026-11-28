import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1333

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket

open Classical

def rawFn (k d : ℕ) (s : Fin k) (x : Fin d → Bool) : List Bool :=
  (List.ofFn (fun i : Fin k => decide (i ≤ s) :: List.ofFn (fun z : Fin d =>
    decide (i < s) || (decide (i = s) && x z)))).flatten ++ [false, true]

lemma rawFn_length (k d : ℕ) (s : Fin k) (x : Fin d → Bool) :
    (rawFn k d s x).length = k * (d + 1) + 2 := by
  simp [rawFn, List.length_flatten, List.map_ofFn]
  simp [List.sum_ofFn, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.mul_comm]

lemma flatten_getD_eq {α : Type*} (d : ℕ) (a0 : α) :
    ∀ (L : List (List α)), (∀ a ∈ L, a.length = d + 1) →
      ∀ (i j : ℕ), i < L.length → j < d + 1 →
        L.flatten.getD (i * (d + 1) + j) a0 = (L.getD i []).getD j a0
  | [], _, i, _, hi, _ => by simp at hi
  | a :: L, hL, 0, j, _, hj => by
    have ha : a.length = d + 1 := hL a (by simp)
    have hj' : j < a.length := by rw [ha]; exact hj
    simp [List.flatten_cons, List.getD_eq_getElem?_getD, List.getElem?_append_left hj']
  | a :: L, hL, i + 1, j, hi, hj => by
    have ha : a.length = d + 1 := hL a (by simp)
    have ih := flatten_getD_eq d a0 L (fun b hb => hL b (by simp [hb])) i j (by simpa using hi) hj
    have hidx : (i + 1) * (d + 1) + j = a.length + (i * (d + 1) + j) := by
      rw [ha, Nat.succ_mul]; omega
    simp only [List.flatten_cons, List.getD_eq_getElem?_getD] at ih ⊢
    rw [hidx, List.getElem?_append_right (by omega)]
    simpa [Nat.add_sub_cancel_left] using ih

lemma rawFn_getD_lt (k d : ℕ) (s : Fin k) (x : Fin d → Bool) (i : Fin k) (j : ℕ) (hj : j < d + 1) :
    (rawFn k d s x).getD (i.val * (d + 1) + j) false =
      if hj0 : j = 0 then decide (i ≤ s)
      else decide (i < s) || (decide (i = s) && x ⟨j - 1, by omega⟩) := by
  let f : Fin k → List Bool := fun t => decide (t ≤ s) :: List.ofFn (fun z : Fin d =>
    decide (t < s) || (decide (t = s) && x z))
  have hf : ∀ a ∈ List.ofFn f, a.length = d + 1 := by
    intro a ha
    rcases List.mem_ofFn.mp ha with ⟨t, rfl⟩
    simp [f]
  have hlen_flat : (List.ofFn f).flatten.length = k * (d + 1) := by
    simp [List.length_flatten, List.map_ofFn, f, List.sum_ofFn, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, Nat.mul_comm]
  have hlt : i.val * (d + 1) + j < (List.ofFn f).flatten.length := by
    rw [hlen_flat]
    calc i.val * (d + 1) + j < i.val * (d + 1) + (d + 1) := by omega
      _ = (i.val + 1) * (d + 1) := by rw [Nat.succ_mul]
      _ ≤ k * (d + 1) := Nat.mul_le_mul_right _ i.isLt
  have happ : (rawFn k d s x).getD (i.val * (d + 1) + j) false =
      (List.ofFn f).flatten.getD (i.val * (d + 1) + j) false := by
    simp only [rawFn, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hlt]
  rw [happ, flatten_getD_eq d false (List.ofFn f) hf i.val j (by simpa using i.isLt) hj]
  have hget : (List.ofFn f).getD i.val [] = f i := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt]
  rw [hget]
  rcases j with _ | j'
  · simp [f]
  · simp [f, dif_pos (by omega : j' < d)]

lemma rawFn_getD_N (k d : ℕ) (s : Fin k) (x : Fin d → Bool) :
    (rawFn k d s x).getD (k * (d + 1)) false = false := by
  have hlen_flat : (List.ofFn (fun i : Fin k => decide (i ≤ s) :: List.ofFn (fun z : Fin d =>
      decide (i < s) || (decide (i = s) && x z)))).flatten.length = k * (d + 1) := by
    simp [List.length_flatten, List.map_ofFn, List.sum_ofFn, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, Nat.mul_comm]
  simp only [rawFn, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega), hlen_flat, Nat.sub_self]
  rfl

lemma rawFn_getD_N1 (k d : ℕ) (s : Fin k) (x : Fin d → Bool) :
    (rawFn k d s x).getD (k * (d + 1) + 1) false = true := by
  have hlen_flat : (List.ofFn (fun i : Fin k => decide (i ≤ s) :: List.ofFn (fun z : Fin d =>
      decide (i < s) || (decide (i = s) && x z)))).flatten.length = k * (d + 1) := by
    simp [List.length_flatten, List.map_ofFn, List.sum_ofFn, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, Nat.mul_comm]
  simp only [rawFn, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega), hlen_flat, Nat.add_sub_cancel_left]
  rfl

def wiresStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wiresPrefix (C : Circuit) (x : List Bool) (m : ℕ) : List Bool :=
  (C.gates.take m).foldl wiresStep x

lemma wiresPrefix_length (C : Circuit) (x : List Bool) (m : ℕ) :
    (wiresPrefix C x m).length = x.length + min m C.gates.length := by
  have hgen : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl wiresStep w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      simp [List.foldl_cons, ih, wiresStep]; omega
  simpa [wiresPrefix, List.length_take] using hgen (C.gates.take m) x

lemma wiresPrefix_all (C : Circuit) (x : List Bool) :
    wiresPrefix C x C.gates.length = C.wires x := by
  simp [wiresPrefix, Circuit.wires]
  rfl

lemma foldl_wiresStep_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl wiresStep w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlen : i < (wiresStep w g).length := by simp [wiresStep]; omega
    rw [ih (wiresStep w g) hlen]
    simp only [wiresStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma wires_getD_prefix (C : Circuit) (x : List Bool) (m i : ℕ) (hi : i < x.length + min m C.gates.length) :
    (C.wires x).getD i false = (wiresPrefix C x m).getD i false := by
  have hsplit : C.gates = C.gates.take m ++ C.gates.drop m := (List.take_append_drop m C.gates).symm
  have hfold : C.wires x = (C.gates.drop m).foldl wiresStep (wiresPrefix C x m) := by
    conv_lhs => rw [Circuit.wires, hsplit, List.foldl_append]
    rfl
  rw [hfold]
  apply foldl_wiresStep_getD_lt
  rw [wiresPrefix_length]
  exact hi

lemma wires_getD_gate {M : ℕ} {C : Circuit} (hRB : ReadsBack M C) {x : List Bool} (hx : x.length = M)
    {j : ℕ} (hj : j < C.gates.length) :
    (C.wires x).getD (M + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (C.wires x).getD i false) := by
  have h1 : (C.wires x).getD (M + j) false = (wiresPrefix C x (j + 1)).getD (M + j) false := by
    apply wires_getD_prefix
    rw [hx, min_eq_left (by omega)]
    omega
  have hpref : wiresPrefix C x (j + 1) = wiresStep (wiresPrefix C x j) (gateAt C j) := by
    simp only [wiresPrefix, List.take_succ_eq_append_getElem hj, List.foldl_append, List.foldl_cons,
      List.foldl_nil]
    have hget : C.gates[j] = gateAt C j := by simp [gateAt, List.getD_eq_getElem?_getD, hj]
    rw [hget]
  rw [h1, hpref, wiresStep]
  have hlenj : (wiresPrefix C x j).length = M + j := by
    rw [wiresPrefix_length, hx, min_eq_left (by omega)]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by rw [hlenj]), hlenj, Nat.sub_self]
  simp only [List.getElem?_singleton, ↓reduceIte, Option.getD_some]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hilt : i < M + j := hRB j hj i hi
  symm
  apply wires_getD_prefix
  rw [hx, min_eq_left (by omega)]
  exact hilt

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  rw [← wiresPrefix_all, wiresPrefix_length, min_self]

lemma list_length_filter_add_not {α : Type*} (l : List α) (p : α → Bool) :
    (l.filter p).length + (l.filter (fun x => !p x)).length = l.length := by
  induction l with
  | nil => simp
  | cons a l ih => cases hpa : p a <;> simp [hpa] <;> omega

lemma finset_range_filter_card (n : ℕ) (p : ℕ → Bool) :
    ((Finset.range n).filter (fun j => p j = true)).card = ((List.range n).filter p).length := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.range_add_one, Finset.filter_insert, List.range_succ, List.filter_append, List.length_append]
    by_cases hp : p n = true
    · simp [hp, ih, Finset.notMem_range_self]
    · have hpf : p n = false := Bool.eq_false_iff.mpr hp
      simp [hp, hpf, ih]

lemma notCount_plus_pos (C : Circuit) :
    notCount C + ((List.range C.gates.length).filter
      (fun j => decide ((gateAt C j).op ≠ GateOp.not))).length = C.size := by
  have hnot : notCount C = ((List.range C.gates.length).filter
      (fun j => decide ((gateAt C j).op = GateOp.not))).length := by
    simp only [notCount]
    have hmap : C.gates = (List.range C.gates.length).map (fun j => gateAt C j) := by
      apply List.ext_getElem
      · simp
      · intro i hi1 hi2
        simp [gateAt, List.getD_eq_getElem?_getD, hi1]
    conv_lhs => rw [hmap, List.filter_map]
    simp only [List.length_map, Function.comp_def]
    congr 1; apply List.filter_congr
    intro j _
    by_cases h : (gateAt C j).op = GateOp.not <;> simp [h]
  rw [hnot]
  have hsum := list_length_filter_add_not (List.range C.gates.length) (fun j => decide ((gateAt C j).op = GateOp.not))
  have hcongr : (List.range C.gates.length).filter (fun x => !decide ((gateAt C x).op = GateOp.not)) =
      (List.range C.gates.length).filter (fun j => decide ((gateAt C j).op ≠ GateOp.not)) := by
    apply List.filter_congr
    intro j _
    simp
  rw [hcongr] at hsum
  have hlen_range : (List.range C.gates.length).length = C.size := by simp [Circuit.size]
  rw [hlen_range] at hsum
  exact hsum

noncomputable def traceNot (M : ℕ) (C : Circuit) (hRB : ReadsBack M C) (w : ℕ) : ℕ :=
  if hw : w < M then w
  else
    let j := w - M
    if hj : j < C.gates.length then
      if (gateAt C j).op = GateOp.not then
        if h_in : (gateAt C j).inputs = [] then w
        else
          have hi : (gateAt C j).inputs.head h_in < w := by
            have := hRB j hj _ (List.head_mem h_in)
            omega
          traceNot M C hRB ((gateAt C j).inputs.head h_in)
      else w
    else w
termination_by w

lemma traceNot_lt {M : ℕ} {C : Circuit} {hRB : ReadsBack M C} {w : ℕ} (hw : w < M) :
    traceNot M C hRB w = w := by
  conv_lhs => unfold traceNot; simp [hw]

lemma traceNot_ge_len {M : ℕ} {C : Circuit} {hRB : ReadsBack M C} {w : ℕ}
    (hw : ¬w < M) (hj : ¬w - M < C.gates.length) :
    traceNot M C hRB w = w := by
  conv_lhs => unfold traceNot; dsimp only; simp [hw, hj]

lemma traceNot_pos {M : ℕ} {C : Circuit} {hRB : ReadsBack M C} {w : ℕ}
    (hw : ¬w < M) (hj : w - M < C.gates.length) (hop : (gateAt C (w - M)).op ≠ GateOp.not) :
    traceNot M C hRB w = w := by
  conv_lhs => unfold traceNot; dsimp only; simp [hw, hj, hop]

lemma traceNot_nil {M : ℕ} {C : Circuit} {hRB : ReadsBack M C} {w : ℕ}
    (hw : ¬w < M) (hj : w - M < C.gates.length) (hop : (gateAt C (w - M)).op = GateOp.not)
    (h_in : (gateAt C (w - M)).inputs = []) :
    traceNot M C hRB w = w := by
  conv_lhs => unfold traceNot; dsimp only; simp [hw, hj, hop, h_in]

lemma traceNot_cons {M : ℕ} {C : Circuit} {hRB : ReadsBack M C} {w i : ℕ} {is : List ℕ}
    (hw : ¬w < M) (hj : w - M < C.gates.length) (hop : (gateAt C (w - M)).op = GateOp.not)
    (h_in : (gateAt C (w - M)).inputs = i :: is) :
    traceNot M C hRB w = traceNot M C hRB i := by
  conv_lhs => unfold traceNot; dsimp only; simp [hw, hj, hop, h_in]

lemma traceNot_le (M : ℕ) (C : Circuit) (hRB : ReadsBack M C) (w : ℕ) :
    traceNot M C hRB w ≤ w := by
  by_cases hw : w < M
  · rw [traceNot_lt hw]
  · by_cases hj : w - M < C.gates.length
    · by_cases hop : (gateAt C (w - M)).op = GateOp.not
      · cases h_in : (gateAt C (w - M)).inputs with
        | nil => rw [traceNot_nil hw hj hop h_in]
        | cons i is =>
          rw [traceNot_cons hw hj hop h_in]
          have hi : i < w := by have := hRB (w - M) hj i (by simp [h_in]); omega
          exact le_trans (traceNot_le M C hRB i) (Nat.le_of_lt hi)
      · rw [traceNot_pos hw hj hop]
    · rw [traceNot_ge_len hw hj]
termination_by w

lemma traceNot_lt_or_pos (M : ℕ) (C : Circuit) (hRB : ReadsBack M C) (w : ℕ) :
    traceNot M C hRB w < M ∨
      (∃ j < C.gates.length, traceNot M C hRB w = M + j ∧
        ((gateAt C j).op ≠ GateOp.not ∨ (gateAt C j).inputs = [])) ∨
      traceNot M C hRB w ≥ M + C.gates.length := by
  by_cases hw : w < M
  · left; rw [traceNot_lt hw]; exact hw
  · by_cases hj : w - M < C.gates.length
    · by_cases hop : (gateAt C (w - M)).op = GateOp.not
      · cases h_in : (gateAt C (w - M)).inputs with
        | nil =>
          right; left
          rw [traceNot_nil hw hj hop h_in]
          exact ⟨w - M, hj, by omega, Or.inr h_in⟩
        | cons i is =>
          rw [traceNot_cons hw hj hop h_in]
          have hi : i < w := by have := hRB (w - M) hj i (by simp [h_in]); omega
          exact traceNot_lt_or_pos M C hRB i
      · right; left
        rw [traceNot_pos hw hj hop]
        exact ⟨w - M, hj, by omega, Or.inl hop⟩
    · right; right
      rw [traceNot_ge_len hw hj]; omega
termination_by w

lemma traceNot_diff {M : ℕ} {C : Circuit} (hRB : ReadsBack M C)
    {x₁ x₂ : List Bool} (hx₁ : x₁.length = M) (hx₂ : x₂.length = M)
    {w : ℕ} (hdiff : (C.wires x₁).getD w false ≠ (C.wires x₂).getD w false) :
    (C.wires x₁).getD (traceNot M C hRB w) false ≠ (C.wires x₂).getD (traceNot M C hRB w) false ∧
    (traceNot M C hRB w < M ∨
      ∃ j < C.gates.length, traceNot M C hRB w = M + j ∧ (gateAt C j).op ≠ GateOp.not) := by
  by_cases hw : w < M
  · rw [traceNot_lt hw]; exact ⟨hdiff, Or.inl hw⟩
  · by_cases hj : w - M < C.gates.length
    · by_cases hop : (gateAt C (w - M)).op = GateOp.not
      · cases h_in : (gateAt C (w - M)).inputs with
        | nil =>
          exfalso
          have hw1 := wires_getD_gate hRB hx₁ hj
          have hw2 := wires_getD_gate hRB hx₂ hj
          have hw_eq : M + (w - M) = w := by omega
          rw [hw_eq] at hw1 hw2
          rw [hw1, hw2, hop, h_in] at hdiff
          exact hdiff rfl
        | cons i is =>
          have hw1 := wires_getD_gate hRB hx₁ hj
          have hw2 := wires_getD_gate hRB hx₂ hj
          have hw_eq : M + (w - M) = w := by omega
          rw [hw_eq] at hw1 hw2
          have hidiff : (C.wires x₁).getD i false ≠ (C.wires x₂).getD i false := by
            intro heq
            apply hdiff
            rw [hw1, hw2, hop, h_in]
            simp only [GateOp.eval, List.map_cons, List.headD_cons, heq]
          have hi : i < w := by have := hRB (w - M) hj i (by simp [h_in]); omega
          rw [traceNot_cons hw hj hop h_in]
          exact traceNot_diff hRB hx₁ hx₂ hidiff
      · rw [traceNot_pos hw hj hop]; exact ⟨hdiff, Or.inr ⟨w - M, hj, by omega, hop⟩⟩
    · exfalso
      have h1 : (C.wires x₁).length ≤ w := by rw [wires_length, hx₁]; omega
      have h2 : (C.wires x₂).length ≤ w := by rw [wires_length, hx₂]; omega
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none h1, List.getElem?_eq_none h2] at hdiff
      exact hdiff rfl
termination_by w

lemma traceNot_eval_eq_of_lt {M : ℕ} {C : Circuit} (hRB : ReadsBack M C)
    {x₁ x₂ : List Bool} (hx₁ : x₁.length = M) (hx₂ : x₂.length = M)
    (w : ℕ) (ht : traceNot M C hRB w < M)
    (h_eq : x₁.getD (traceNot M C hRB w) false = x₂.getD (traceNot M C hRB w) false) :
    (C.wires x₁).getD w false = (C.wires x₂).getD w false := by
  by_contra hdiff
  have hd := (traceNot_diff hRB hx₁ hx₂ hdiff).1
  rw [wires_getD_prefix C x₁ 0 _ (by rw [hx₁]; omega), wires_getD_prefix C x₂ 0 _ (by rw [hx₂]; omega)] at hd
  simp only [wiresPrefix, List.take_zero, List.foldl_nil] at hd
  exact hd h_eq

lemma traceNot_diff_of_lt {M : ℕ} {C : Circuit} (hRB : ReadsBack M C)
    {x₁ x₂ : List Bool} (hx₁ : x₁.length = M) (hx₂ : x₂.length = M)
    (w : ℕ) (ht : traceNot M C hRB w < M)
    (hdiff : x₁.getD (traceNot M C hRB w) false ≠ x₂.getD (traceNot M C hRB w) false) :
    (C.wires x₁).getD w false ≠ (C.wires x₂).getD w false := by
  by_cases hw : w < M
  · rw [traceNot_lt hw] at hdiff
    rw [wires_getD_prefix C x₁ 0 _ (by rw [hx₁]; exact hw),
      wires_getD_prefix C x₂ 0 _ (by rw [hx₂]; exact hw)]
    simpa [wiresPrefix] using hdiff
  · by_cases hj : w - M < C.gates.length
    · by_cases hop : (gateAt C (w - M)).op = GateOp.not
      · cases h_in : (gateAt C (w - M)).inputs with
        | nil => rw [traceNot_nil hw hj hop h_in] at ht; omega
        | cons i is =>
          rw [traceNot_cons hw hj hop h_in] at ht hdiff
          have hi : i < w := by have := hRB (w - M) hj i (by simp [h_in]); omega
          have hidiff := traceNot_diff_of_lt hRB hx₁ hx₂ i ht hdiff
          have hw1 := wires_getD_gate hRB hx₁ hj
          have hw2 := wires_getD_gate hRB hx₂ hj
          have hw_eq : M + (w - M) = w := by omega
          rw [hw_eq] at hw1 hw2
          rw [hw1, hw2, hop, h_in]
          simp only [GateOp.eval, List.map_cons, List.headD_cons]
          intro heq
          apply hidiff
          exact Bool.not_inj heq
      · rw [traceNot_pos hw hj hop] at ht; omega
    · rw [traceNot_ge_len hw hj] at ht; omega
termination_by w

lemma rawFn_flip_diff (k d : ℕ) (s : Fin k) (x₁ x₂ : Fin d → Bool) (v : Fin d)
    (hdiff : ∀ u : Fin d, u ≠ v → x₁ u = x₂ u) (w : ℕ) (hw : w < k * (d + 1) + 2)
    (hne : w ≠ s.val * (d + 1) + 1 + v.val) :
    (rawFn k d s x₁).getD w false = (rawFn k d s x₂).getD w false := by
  by_cases hwN : w < k * (d + 1)
  · have hdiv : w / (d + 1) < k := Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hwN)
    have hmod : w % (d + 1) < d + 1 := Nat.mod_lt _ (Nat.succ_pos d)
    let i : Fin k := ⟨w / (d + 1), hdiv⟩
    let j : ℕ := w % (d + 1)
    have hj_lt : j < d + 1 := hmod
    have hw_eq : i.val * (d + 1) + j = w := by
      simpa [i, j, Nat.mul_comm] using Nat.div_add_mod w (d + 1)
    rw [← hw_eq, rawFn_getD_lt k d s x₁ i j hj_lt, rawFn_getD_lt k d s x₂ i j hj_lt]
    rcases j with _ | j'
    · rfl
    · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceDIte]
      by_cases his : i = s
      · subst his
        have hjv : (⟨j', by omega⟩ : Fin d) ≠ v := by
          intro heq
          apply hne
          have h1 : j' = v.val := congrArg Fin.val heq
          omega
        simp only [Nat.add_sub_cancel]
        rw [hdiff ⟨j', by omega⟩ hjv]
      · simp [his]
  · have hcases : w = k * (d + 1) ∨ w = k * (d + 1) + 1 := by omega
    rcases hcases with rfl | rfl
    · rw [rawFn_getD_N, rawFn_getD_N]
    · rw [rawFn_getD_N1, rawFn_getD_N1]

lemma lower_bound_kd (k d : ℕ) (E : Finset (Fin d × Fin d)) (hk : 0 < k) (hd : 2 ≤ d)
    (hE_lt : ∀ z ∈ E, z.1 < z.2) (hE_cov : ∀ v : Fin d, ∃ z ∈ E, z.1 = v ∨ z.2 = v)
    (C : Circuit) (tap : Fin k → {z : Fin d × Fin d // z ∈ E} → ℕ)
    (hFan : FanInTwo C) (hRB : ReadsBack (k * (d + 1) + 2) C)
    (htap : ∀ s x z, (C.wires (rawFn k d s x)).getD (tap s z) false = (x z.val.1 && x z.val.2)) :
    k * d ≤ 2 * (C.size - notCount C) := by
  let N := k * (d + 1)
  let M := N + 2
  let posGates : Finset ℕ := (Finset.range C.gates.length).filter (fun j => decide ((gateAt C j).op ≠ GateOp.not) = true)
  have hpos_mem : ∀ {j}, j ∈ posGates ↔ j < C.gates.length ∧ (gateAt C j).op ≠ GateOp.not := by
    intro j
    simp [posGates]
  have hpos_card : posGates.card = C.size - notCount C := by
    have h1 := notCount_plus_pos C
    have h2 : posGates.card = ((List.range C.gates.length).filter
        (fun j => decide ((gateAt C j).op ≠ GateOp.not))).length := by
      simpa [posGates] using finset_range_filter_card C.gates.length (fun j => decide ((gateAt C j).op ≠ GateOp.not))
    omega
  rw [← hpos_card]
  have hkey : ∀ p : Fin k × Fin d, ∃ gp ∈ posGates.product (Finset.univ : Finset (Fin 2)),
      traceNot M C hRB ((gateAt C gp.1).inputs.getD gp.2.val 0) = p.1.val * (d + 1) + 1 + p.2.val := by
    rintro ⟨s, v⟩
    rcases hE_cov v with ⟨z, hzE, hz⟩
    let u : Fin d := if z.1 = v then z.2 else z.1
    have huv : u ≠ v := by
      have hlt := hE_lt z hzE
      dsimp [u]
      split_ifs with h
      · intro heq; rw [h, heq] at hlt; exact lt_irrefl v hlt
      · exact h
    let x₀ : Fin d → Bool := fun w => decide (w = u)
    let x₁ : Fin d → Bool := fun w => decide (w = u ∨ w = v)
    let xF : Fin d → Bool := fun _ => false
    let xV : Fin d → Bool := fun w => decide (w = v)
    have hlen0 : (rawFn k d s x₀).length = M := rawFn_length k d s x₀
    have hlen1 : (rawFn k d s x₁).length = M := rawFn_length k d s x₁
    have hlenF : (rawFn k d s xF).length = M := rawFn_length k d s xF
    have hlenV : (rawFn k d s xV).length = M := rawFn_length k d s xV
    have htap0 : (C.wires (rawFn k d s x₀)).getD (tap s ⟨z, hzE⟩) false = false := by
      rw [htap]
      have hlt := hE_lt z hzE
      rcases hz with h | h
      · have hne : v ≠ z.2 := ne_of_lt (by rwa [← h])
        simp [x₀, u, h, hne]
      · have hne1 : z.1 ≠ v := ne_of_lt (by rwa [← h])
        have hne2 : v ≠ z.1 := hne1.symm
        simp [x₀, u, h, hne1, hne2]
    have htap1 : (C.wires (rawFn k d s x₁)).getD (tap s ⟨z, hzE⟩) false = true := by
      rw [htap]
      rcases hz with h | h <;> simp [x₁, u, h]
    have htap_diff : (C.wires (rawFn k d s x₀)).getD (tap s ⟨z, hzE⟩) false ≠
        (C.wires (rawFn k d s x₁)).getD (tap s ⟨z, hzE⟩) false := by
      rw [htap0, htap1]; decide
    have htapF : (C.wires (rawFn k d s xF)).getD (tap s ⟨z, hzE⟩) false = false := by
      rw [htap]; simp [xF]
    have htapV : (C.wires (rawFn k d s xV)).getD (tap s ⟨z, hzE⟩) false = false := by
      rw [htap]
      rcases hz with h | h
      · have hlt := hE_lt z hzE
        have hne : z.2 ≠ v := by rw [← h]; exact ne_of_gt hlt
        simp [xV, hne]
      · have hlt := hE_lt z hzE
        have hne : z.1 ≠ v := by rw [← h]; exact ne_of_lt hlt
        simp [xV, hne]
    have hex_pos : ∃ j ∈ posGates,
        (C.wires (rawFn k d s x₀)).getD (M + j) false ≠
        (C.wires (rawFn k d s x₁)).getD (M + j) false := by
      rcases traceNot_diff hRB hlen0 hlen1 htap_diff with ⟨hd_tr, hlt | ⟨j, hj, htr_eq, hnot⟩⟩
      · exfalso
        have hidx_eq : traceNot M C hRB (tap s ⟨z, hzE⟩) = s.val * (d + 1) + 1 + v.val := by
          by_contra hne
          exact hd_tr (by
            rw [wires_getD_prefix C _ 0 _ (by rw [hlen0]; exact hlt),
              wires_getD_prefix C _ 0 _ (by rw [hlen1]; exact hlt)]
            simp only [wiresPrefix, List.take_zero, List.foldl_nil]
            exact rawFn_flip_diff k d s x₀ x₁ v (fun w hw => by simp [x₀, x₁, hw]) _ hlt hne)
        have heqFV : (C.wires (rawFn k d s xF)).getD (tap s ⟨z, hzE⟩) false ≠
            (C.wires (rawFn k d s xV)).getD (tap s ⟨z, hzE⟩) false := by
          apply traceNot_diff_of_lt hRB hlenF hlenV _ hlt
          rw [hidx_eq]
          have hidx_form : s.val * (d + 1) + 1 + v.val = s.val * (d + 1) + (v.val + 1) := by omega
          rw [hidx_form, rawFn_getD_lt k d s xF s (v.val + 1) (by omega),
            rawFn_getD_lt k d s xV s (v.val + 1) (by omega)]
          simp [xF, xV, Fin.ext_iff]
        rw [htapF, htapV] at heqFV
        exact heqFV rfl
      · refine ⟨j, hpos_mem.mpr ⟨hj, hnot⟩, ?_⟩
        rwa [← htr_eq]

    have hnonempty : (posGates.filter (fun j =>
        (C.wires (rawFn k d s x₀)).getD (M + j) false ≠
        (C.wires (rawFn k d s x₁)).getD (M + j) false)).Nonempty := by
      rcases hex_pos with ⟨j, hj, hdj⟩
      exact ⟨j, Finset.mem_filter.mpr ⟨hj, hdj⟩⟩
    let j_min := (posGates.filter (fun j =>
      (C.wires (rawFn k d s x₀)).getD (M + j) false ≠
      (C.wires (rawFn k d s x₁)).getD (M + j) false)).min' hnonempty
    have hj_min_mem : j_min ∈ posGates := (Finset.mem_filter.mp (Finset.min'_mem _ hnonempty)).1
    have hj_min_diff : (C.wires (rawFn k d s x₀)).getD (M + j_min) false ≠
        (C.wires (rawFn k d s x₁)).getD (M + j_min) false :=
      (Finset.mem_filter.mp (Finset.min'_mem _ hnonempty)).2
    have hj_min_lt : j_min < C.gates.length := (hpos_mem.mp hj_min_mem).1
    have hfan_j : (gateAt C j_min).inputs.length ≤ 2 := by
      have hmem : gateAt C j_min ∈ C.gates := by
        simp [gateAt, List.getD_eq_getElem?_getD, hj_min_lt, List.getElem_mem]
      exact (hFan _ hmem).2
    have hex_op : ∃ pos : Fin 2, pos.val < (gateAt C j_min).inputs.length ∧
        (C.wires (rawFn k d s x₀)).getD ((gateAt C j_min).inputs.getD pos.val 0) false ≠
        (C.wires (rawFn k d s x₁)).getD ((gateAt C j_min).inputs.getD pos.val 0) false := by
      by_contra hno
      push_neg at hno
      have hw0 := wires_getD_gate hRB hlen0 hj_min_lt
      have hw1 := wires_getD_gate hRB hlen1 hj_min_lt
      apply hj_min_diff
      rw [hw0, hw1]
      congr 1
      apply List.ext_getElem
      · simp
      · intro idx hi1 hi2
        simp only [List.length_map] at hi1 hi2
        have hidx2 : idx < 2 := lt_of_lt_of_le hi1 hfan_j
        have heq := hno ⟨idx, hidx2⟩ hi1
        simp only [List.getElem_map]
        simpa [List.getD_eq_getElem?_getD, hi1] using heq
    rcases hex_op with ⟨pos, hpos_lt, hw_op_diff⟩
    let w_op := (gateAt C j_min).inputs.getD pos.val 0
    have hw_op_lt : w_op < M + j_min := by
      apply hRB j_min hj_min_lt
      simp only [w_op, List.getD_eq_getElem?_getD, hpos_lt, List.getElem?_eq_getElem, Option.getD_some]
      exact List.getElem_mem hpos_lt
    rcases traceNot_diff hRB hlen0 hlen1 hw_op_diff with ⟨hd_tr, hlt | ⟨j', hj', htr_eq, hnot'⟩⟩
    · refine ⟨⟨j_min, pos⟩, Finset.mem_product.mpr ⟨hj_min_mem, Finset.mem_univ _⟩, ?_⟩
      by_contra hne
      apply hd_tr
      rw [wires_getD_prefix C _ 0 _ (by rw [hlen0]; exact hlt),
        wires_getD_prefix C _ 0 _ (by rw [hlen1]; exact hlt)]
      simp only [wiresPrefix, List.take_zero, List.foldl_nil]
      exact rawFn_flip_diff k d s x₀ x₁ v (fun w hw => by simp [x₀, x₁, hw]) _ hlt hne
    · exfalso
      have hj'_lt : j' < j_min := by
        have hle := traceNot_le M C hRB w_op
        rw [htr_eq] at hle
        omega
      have hj'_mem : j' ∈ posGates.filter (fun j =>
          (C.wires (rawFn k d s x₀)).getD (M + j) false ≠
          (C.wires (rawFn k d s x₁)).getD (M + j) false) := by
        refine Finset.mem_filter.mpr ⟨hpos_mem.mpr ⟨hj', hnot'⟩, ?_⟩
        rwa [← htr_eq]
      exact not_lt_of_ge (Finset.min'_le _ _ hj'_mem) hj'_lt

  have hcard : (Finset.univ : Finset (Fin k × Fin d)).card ≤
      (posGates.product (Finset.univ : Finset (Fin 2))).card := by
    let f : Fin k × Fin d → ℕ × Fin 2 := fun p => Classical.choose (hkey p)
    apply Finset.card_le_card_of_injOn f
    · intro p _
      exact (Classical.choose_spec (hkey p)).1
    · intro p₁ _ p₂ _ heq
      have h1 := (Classical.choose_spec (hkey p₁)).2
      have h2 := (Classical.choose_spec (hkey p₂)).2
      have heq' : Classical.choose (hkey p₁) = Classical.choose (hkey p₂) := heq
      rw [heq'] at h1
      have hidx : p₁.1.val * (d + 1) + 1 + p₁.2.val = p₂.1.val * (d + 1) + 1 + p₂.2.val :=
        h1.symm.trans h2
      have hp1 : 1 + p₁.2.val < d + 1 := by omega
      have hp2 : 1 + p₂.2.val < d + 1 := by omega
      have hv : p₁.2 = p₂.2 := by
        ext
        have hmod := congrArg (· % (d + 1)) hidx
        simp only [Nat.add_assoc, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hp1,
          Nat.mod_eq_of_lt hp2] at hmod
        omega
      have hs : p₁.1 = p₂.1 := by
        ext
        have : p₁.1.val * (d + 1) = p₂.1.val * (d + 1) := by
          have hv_val : p₁.2.val = p₂.2.val := congrArg Fin.val hv
          have h1 : p₁.1.val * (d + 1) + (1 + p₁.2.val) = p₂.1.val * (d + 1) + (1 + p₂.2.val) := by
            simpa [Nat.add_assoc] using hidx
          rw [hv_val] at h1
          exact Nat.add_right_cancel h1
        exact Nat.eq_of_mul_eq_mul_right (Nat.succ_pos d) this
      exact Prod.ext hs hv
  simpa [Finset.card_product, Fintype.card_fin, Nat.mul_comm] using hcard

def chainInp (k d : ℕ) (hk : 0 < k) (t : ℕ) : List Bool :=
  if ht : t < 2 * k then
    if t % 2 = 0 then rawFn k d ⟨t / 2, by omega⟩ (fun _ => false)
    else rawFn k d ⟨t / 2, by omega⟩ (fun _ => true)
  else
    rawFn k d ⟨0, hk⟩ (fun _ => false)

lemma chainInp_length (k d : ℕ) (hk : 0 < k) (t : ℕ) :
    (chainInp k d hk t).length = k * (d + 1) + 2 := by
  dsimp [chainInp]
  split_ifs <;> exact rawFn_length k d _ _

lemma chainInp_mono (k d : ℕ) (hk : 0 < k) {t₁ t₂ : ℕ} (ht : t₁ ≤ t₂) (ht₂ : t₂ < 2 * k) :
    ∀ w : ℕ, (chainInp k d hk t₁).getD w false = true → (chainInp k d hk t₂).getD w false = true := by
  intro w hw
  have ht₁ : t₁ < 2 * k := lt_of_le_of_lt ht ht₂
  by_cases hwN : w < k * (d + 1)
  · have hdiv : w / (d + 1) < k := Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hwN)
    have hmod : w % (d + 1) < d + 1 := Nat.mod_lt _ (Nat.succ_pos d)
    let i : Fin k := ⟨w / (d + 1), hdiv⟩
    have hw_eq : i.val * (d + 1) + w % (d + 1) = w := by
      simpa [i, Nat.mul_comm] using Nat.div_add_mod w (d + 1)
    have hbit : ∀ t (ht_lt : t < 2 * k),
        (chainInp k d hk t).getD (i.val * (d + 1) + w % (d + 1)) false =
          if w % (d + 1) = 0 then decide (i.val ≤ t / 2) else decide (2 * i.val + 1 ≤ t) := by
      intro t ht_lt
      simp only [chainInp, ht_lt, ↓reduceDIte]
      by_cases hj0 : w % (d + 1) = 0
      · rw [hj0]
        simp only [↓reduceIte]
        split_ifs <;> rw [rawFn_getD_lt k d _ _ i 0 (Nat.succ_pos d)] <;> simp [Fin.le_def]
      · obtain ⟨j', hj'_eq⟩ := Nat.exists_eq_succ_of_ne_zero hj0
        have hmod' : j' + 1 < d + 1 := by omega
        simp only [hj0, ↓reduceIte]
        rw [hj'_eq]
        split_ifs
        · rw [rawFn_getD_lt k d _ _ i (j' + 1) hmod']
          simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceDIte, Bool.and_false,
            Bool.or_false, decide_eq_decide, Fin.lt_def]
          omega
        · rw [rawFn_getD_lt k d _ _ i (j' + 1) hmod']
          simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceDIte, Bool.and_true]
          rw [← Bool.decide_or]
          simp only [decide_eq_decide, Fin.lt_def, Fin.ext_iff]
          omega
    rw [← hw_eq, hbit t₁ ht₁] at hw
    rw [← hw_eq, hbit t₂ ht₂]
    split_ifs at hw ⊢ with hj0
    · simp only [decide_eq_true_eq] at hw ⊢
      exact le_trans hw (Nat.div_le_div_right ht)
    · simp only [decide_eq_true_eq] at hw ⊢
      exact le_trans hw ht
  · have hcases : w = k * (d + 1) ∨ w = k * (d + 1) + 1 ∨ k * (d + 1) + 2 ≤ w := by omega
    rcases hcases with rfl | rfl | hwge
    · simp only [chainInp, ht₁, ht₂, ↓reduceDIte] at hw ⊢
      split_ifs at hw <;> rw [rawFn_getD_N] at hw <;> contradiction
    · simp only [chainInp, ht₁, ht₂, ↓reduceDIte]
      split_ifs <;> rw [rawFn_getD_N1]
    · have hlen1 : (chainInp k d hk t₁).length ≤ w := by rw [chainInp_length]; omega
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen1] at hw
      contradiction

lemma wires_mono_up_to {k d : ℕ} (hk : 0 < k) {C : Circuit}
    (hFan : FanInTwo C) (hRB : ReadsBack (k * (d + 1) + 2) C)
    (a b m : ℕ) (hb : b ≤ 2 * k)
    (hnot_const : ∀ j < m, (gateAt C j).op = GateOp.not →
      ∀ t₁ t₂, a ≤ t₁ → t₁ < b → a ≤ t₂ → t₂ < b →
        (C.wires (chainInp k d hk t₁)).getD (k * (d + 1) + 2 + j) false =
        (C.wires (chainInp k d hk t₂)).getD (k * (d + 1) + 2 + j) false) :
    ∀ w < k * (d + 1) + 2 + m,
      ∀ t₁ t₂, a ≤ t₁ → t₁ ≤ t₂ → t₂ < b →
        (C.wires (chainInp k d hk t₁)).getD w false = true →
        (C.wires (chainInp k d hk t₂)).getD w false = true := by
  let M := k * (d + 1) + 2
  intro w hw
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro t₁ t₂ ha ht₁₂ htb h1
    have ht₁b : t₁ < b := lt_of_le_of_lt ht₁₂ htb
    have hlen1 : (chainInp k d hk t₁).length = M := chainInp_length k d hk t₁
    have hlen2 : (chainInp k d hk t₂).length = M := chainInp_length k d hk t₂
    by_cases hwM : w < M
    · rw [wires_getD_prefix C _ 0 w (by rw [hlen1]; exact hwM)] at h1
      rw [wires_getD_prefix C _ 0 w (by rw [hlen2]; exact hwM)]
      simp only [wiresPrefix, List.take_zero, List.foldl_nil] at h1 ⊢
      exact chainInp_mono k d hk ht₁₂ (lt_of_lt_of_le htb hb) w h1
    · let j := w - M
      have hj_lt_m : j < m := by omega
      have hw_eq : M + j = w := by omega
      by_cases hj : j < C.gates.length
      · have hgate1 := wires_getD_gate hRB hlen1 hj
        have hgate2 := wires_getD_gate hRB hlen2 hj
        rw [hw_eq] at hgate1 hgate2
        have hmem : gateAt C j ∈ C.gates := by
          simp [gateAt, List.getD_eq_getElem?_getD, hj, List.getElem_mem]
        rcases (hFan _ hmem).1 with hop | hop | hop
        ·
          rw [hgate1, hop] at h1
          rw [hgate2, hop]
          simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index,
            and_imp, forall_apply_eq_imp_iff₂] at h1 ⊢
          intro i hi
          have hilt : i < w := by rw [← hw_eq]; exact hRB j hj i hi
          exact ih i hilt (lt_trans hilt hw) t₁ t₂ ha ht₁₂ htb (h1 i hi)
        ·
          rw [hgate1, hop] at h1
          rw [hgate2, hop]
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at h1 ⊢
          rcases h1 with ⟨_, ⟨i, hi, rfl⟩, hi_true⟩
          have hilt : i < w := by rw [← hw_eq]; exact hRB j hj i hi
          exact ⟨true, ⟨i, hi, ih i hilt (lt_trans hilt hw) t₁ t₂ ha ht₁₂ htb hi_true⟩, rfl⟩
        ·
          have hop_not : (gateAt C j).op = GateOp.not := Set.mem_singleton_iff.mp hop
          have heq := hnot_const j hj_lt_m hop_not t₁ t₂ ha ht₁b (le_trans ha ht₁₂) htb
          rw [← hw_eq, ← heq, hw_eq]
          exact h1
      · have hlenw1 : (C.wires (chainInp k d hk t₁)).length ≤ w := by rw [wires_length, hlen1]; omega
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlenw1] at h1
        contradiction

lemma split_interval_not {k d : ℕ} (hk : 0 < k) {C : Circuit}
    (hFan : FanInTwo C) (hRB : ReadsBack (k * (d + 1) + 2) C)
    (a b j : ℕ) (hab : a < b) (hb : b ≤ 2 * k) (hj : j < C.gates.length)
    (hnot : (gateAt C j).op = GateOp.not)
    (hnot_const : ∀ j' < j, (gateAt C j').op = GateOp.not →
      ∀ t₁ t₂, a ≤ t₁ → t₁ < b → a ≤ t₂ → t₂ < b →
        (C.wires (chainInp k d hk t₁)).getD (k * (d + 1) + 2 + j') false =
        (C.wires (chainInp k d hk t₂)).getD (k * (d + 1) + 2 + j') false) :
    ∃ t_split, a ≤ t_split ∧ t_split ≤ b ∧
      (∀ t, a ≤ t → t < t_split → (C.wires (chainInp k d hk t)).getD (k * (d + 1) + 2 + j) false = true) ∧
      (∀ t, t_split ≤ t → t < b → (C.wires (chainInp k d hk t)).getD (k * (d + 1) + 2 + j) false = false) := by
  let M := k * (d + 1) + 2
  have hdec : ∀ t₁ t₂, a ≤ t₁ → t₁ ≤ t₂ → t₂ < b →
      (C.wires (chainInp k d hk t₂)).getD (M + j) false = true →
      (C.wires (chainInp k d hk t₁)).getD (M + j) false = true := by
    intro t₁ t₂ ha ht₁₂ htb h2
    have hlen1 := chainInp_length k d hk t₁
    have hlen2 := chainInp_length k d hk t₂
    have hg1 := wires_getD_gate hRB hlen1 hj
    have hg2 := wires_getD_gate hRB hlen2 hj
    cases h_in : (gateAt C j).inputs with
    | nil =>
      rw [hg1, hnot, h_in]; rfl
    | cons i is =>
      rw [hg1, hnot, h_in]
      rw [hg2, hnot, h_in] at h2
      simp only [GateOp.eval, List.map_cons, List.headD_cons, Bool.not_eq_true'] at h2 ⊢
      by_contra h1true
      have h1_eq : (C.wires (chainInp k d hk t₁)).getD i false = true := by
        cases hval : (C.wires (chainInp k d hk t₁)).getD i false <;> simp_all
      have hilt : i < M + j := hRB j hj i (by simp [h_in])
      have h2_eq := wires_mono_up_to hk hFan hRB a b j hb hnot_const i hilt t₁ t₂ ha ht₁₂ htb h1_eq
      rw [h2] at h2_eq
      contradiction
  by_cases hex : ∃ t, a ≤ t ∧ t < b ∧ (C.wires (chainInp k d hk t)).getD (M + j) false = false
  · let S := (Finset.Ico a b).filter (fun t => (C.wires (chainInp k d hk t)).getD (M + j) false = false)
    have hS : S.Nonempty := by
      rcases hex with ⟨t, hat, htb, htval⟩
      exact ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hat, htb⟩, htval⟩⟩
    let t_split := S.min' hS
    have hmem := Finset.mem_filter.mp (Finset.min'_mem S hS)
    have ha_sp : a ≤ t_split := (Finset.mem_Ico.mp hmem.1).1
    have hsp_b : t_split < b := (Finset.mem_Ico.mp hmem.1).2
    refine ⟨t_split, ha_sp, le_of_lt hsp_b, ?_, ?_⟩
    · intro t hat hlt
      by_contra hfalse
      have hval : (C.wires (chainInp k d hk t)).getD (M + j) false = false := Bool.eq_false_iff.mpr hfalse
      have htmem : t ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hat, lt_trans hlt hsp_b⟩, hval⟩
      exact not_lt_of_ge (Finset.min'_le S t htmem) hlt
    · intro t hle htb
      by_contra hnotf
      have hval : (C.wires (chainInp k d hk t)).getD (M + j) false = true :=
        Bool.eq_true_of_not_eq_false (by intro hf; apply hnotf; exact hf)
      have hsp_true := hdec t_split t ha_sp hle htb hval
      rw [hmem.2] at hsp_true
      contradiction
  · push_neg at hex
    refine ⟨b, le_of_lt hab, le_rfl, ?_, ?_⟩
    · intro t hat htb
      have hne := hex t hat htb
      cases hv : (C.wires (chainInp k d hk t)).getD (M + j) false <;> simp_all
    · intro t hbt htb; omega

lemma exists_interval_partition {k d : ℕ} (hk : 0 < k) {C : Circuit}
    (hFan : FanInTwo C) (hRB : ReadsBack (k * (d + 1) + 2) C) (m : ℕ) (hm : m ≤ C.gates.length) :
    ∃ L : List (ℕ × ℕ),
      1 ≤ L.length ∧
      L.length ≤ 2 ^ ((Finset.range m).filter (fun j => (gateAt C j).op = GateOp.not)).card ∧
      (∀ p ∈ L, p.1 < p.2 ∧ p.2 ≤ 2 * k) ∧
      (∀ p ∈ L, ∀ j < m, (gateAt C j).op = GateOp.not →
        ∀ t₁ t₂, p.1 ≤ t₁ → t₁ < p.2 → p.1 ≤ t₂ → t₂ < p.2 →
          (C.wires (chainInp k d hk t₁)).getD (k * (d + 1) + 2 + j) false =
          (C.wires (chainInp k d hk t₂)).getD (k * (d + 1) + 2 + j) false) ∧
      k ≤ ((Finset.univ : Finset (Fin k)).filter
            (fun s => ∃ p ∈ L, p.1 ≤ 2 * s.val ∧ 2 * s.val + 1 < p.2)).card + (L.length - 1) := by
  induction m with
  | zero =>
    refine ⟨[(0, 2 * k)], by simp, by simp, by intro p hp; simp at hp; subst hp; omega, ?_, ?_⟩
    · intro p _ j hj; omega
    · have hcard : ((Finset.univ : Finset (Fin k)).filter
          (fun s => ∃ p ∈ [(0, 2 * k)], p.1 ≤ 2 * s.val ∧ 2 * s.val + 1 < p.2)).card = k := by
        rw [Finset.filter_eq_self.mpr]
        · simp
        · intro s _; exact ⟨(0, 2 * k), by simp, by omega, by omega⟩
      rw [hcard]; omega
  | succ m ih =>
    rcases ih (Nat.le_of_succ_le hm) with ⟨L, hLpos, hLlen, hLbounds, hLnot, hLcov⟩
    by_cases hm_not : (gateAt C m).op = GateOp.not
    · have hrefine : ∀ (L0 : List (ℕ × ℕ)),
          (∀ p ∈ L0, p.1 < p.2 ∧ p.2 ≤ 2 * k) →
          (∀ p ∈ L0, ∀ j' < m, (gateAt C j').op = GateOp.not →
            ∀ t₁ t₂, p.1 ≤ t₁ → t₁ < p.2 → p.1 ≤ t₂ → t₂ < p.2 →
              (C.wires (chainInp k d hk t₁)).getD (k * (d + 1) + 2 + j') false =
              (C.wires (chainInp k d hk t₂)).getD (k * (d + 1) + 2 + j') false) →
          ∃ L' : List (ℕ × ℕ),
            L0.length ≤ L'.length ∧ L'.length ≤ 2 * L0.length ∧
            (∀ q' ∈ L', ∃ q ∈ L0, q.1 ≤ q'.1 ∧ q'.2 ≤ q.2) ∧
            (∀ p ∈ L', p.1 < p.2 ∧ p.2 ≤ 2 * k) ∧
            (∀ p ∈ L', ∀ j < m + 1, (gateAt C j).op = GateOp.not →
              ∀ t₁ t₂, p.1 ≤ t₁ → t₁ < p.2 → p.1 ≤ t₂ → t₂ < p.2 →
                (C.wires (chainInp k d hk t₁)).getD (k * (d + 1) + 2 + j) false =
                (C.wires (chainInp k d hk t₂)).getD (k * (d + 1) + 2 + j) false) ∧
            ((Finset.univ : Finset (Fin k)).filter
              (fun s => ∃ p ∈ L0, p.1 ≤ 2 * s.val ∧ 2 * s.val + 1 < p.2)).card ≤
            ((Finset.univ : Finset (Fin k)).filter
              (fun s => ∃ p ∈ L', p.1 ≤ 2 * s.val ∧ 2 * s.val + 1 < p.2)).card + (L'.length - L0.length) := by
        intro L0
        induction L0 with
        | nil =>
          intro _ _
          exact ⟨[], le_rfl, le_rfl, by simp, by simp, by simp, by simp⟩
        | cons p rest ihL =>
          intro hp_bounds hp_not
          rcases ihL (fun q hq => hp_bounds q (by simp [hq]))
            (fun q hq => hp_not q (by simp [hq])) with
            ⟨rest', hlen1, hlen2, hsub_rest, hrb, hrn, hcov_rest⟩
          have hp_b := hp_bounds p (by simp)
          rcases split_interval_not hk hFan hRB p.1 p.2 m hp_b.1 hp_b.2 hm hm_not
            (fun j' hj' hnot' => hp_not p (by simp) j' hj' hnot') with
            ⟨t_sp, ha_sp, hsp_b, ht_true, ht_false⟩
          by_cases hsplit : p.1 < t_sp ∧ t_sp < p.2
          · let L' := (p.1, t_sp) :: (t_sp, p.2) :: rest'
            refine ⟨L', by simp [L']; omega, by simp [L']; omega, ?_, ?_, ?_, ?_⟩
            · intro q' hq'
              simp only [L', List.mem_cons] at hq'
              rcases hq' with rfl | rfl | hq'
              · exact ⟨p, by simp, le_rfl, le_of_lt hsplit.2⟩
              · exact ⟨p, by simp, le_of_lt hsplit.1, le_rfl⟩
              · rcases hsub_rest q' hq' with ⟨q, hq, h1, h2⟩
                exact ⟨q, by simp [hq], h1, h2⟩
            · intro q hq
              simp only [L', List.mem_cons] at hq
              rcases hq with rfl | rfl | hq
              · exact ⟨hsplit.1, le_trans (le_of_lt hsplit.2) hp_b.2⟩
              · exact ⟨hsplit.2, hp_b.2⟩
              · exact hrb q hq
            · intro q hq j hj hnot t₁ t₂ h1a h1b h2a h2b
              simp only [L', List.mem_cons] at hq
              rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjm | rfl
              · rcases hq with rfl | rfl | hq
                · exact hp_not p (by simp) j hjm hnot t₁ t₂ h1a (lt_trans h1b hsplit.2) h2a (lt_trans h2b hsplit.2)
                · exact hp_not p (by simp) j hjm hnot t₁ t₂ (le_trans (le_of_lt hsplit.1) h1a) h1b (le_trans (le_of_lt hsplit.1) h2a) h2b
                · exact hrn q hq j (Nat.lt_succ_of_lt hjm) hnot t₁ t₂ h1a h1b h2a h2b
              · rcases hq with rfl | rfl | hq
                · rw [ht_true t₁ h1a h1b, ht_true t₂ h2a h2b]
                · rw [ht_false t₁ h1a h1b, ht_false t₂ h2a h2b]
                · exact hrn q hq _ hj hnot t₁ t₂ h1a h1b h2a h2b
            · let S0 := (Finset.univ : Finset (Fin k)).filter (fun s => ∃ q ∈ p :: rest, q.1 ≤ 2 * s.val ∧ 2 * s.val + 1 < q.2)
              let S' := (Finset.univ : Finset (Fin k)).filter (fun s => ∃ q ∈ L', q.1 ≤ 2 * s.val ∧ 2 * s.val + 1 < q.2)
              let S_rest := (Finset.univ : Finset (Fin k)).filter (fun s => ∃ q ∈ rest, q.1 ≤ 2 * s.val ∧ 2 * s.val + 1 < q.2)
              let S_rest' := (Finset.univ : Finset (Fin k)).filter (fun s => ∃ q ∈ rest', q.1 ≤ 2 * s.val ∧ 2 * s.val + 1 < q.2)

              have hsub : S0 ⊆ S' ∪ (S_rest \ S_rest') ∪
                  ((Finset.univ : Finset (Fin k)).filter (fun s => 2 * s.val + 1 = t_sp)) := by
                intro s hs
                simp only [S0, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_cons] at hs
                simp only [Finset.mem_union]
                rcases hs with ⟨q, hq_mem, hs1, hs2⟩
                rcases hq_mem with hqp | hq
                · rw [hqp] at hs1 hs2
                  by_cases hlt1 : 2 * s.val + 1 < t_sp
                  · left; left; simp only [S', L', Finset.mem_filter, Finset.mem_univ, true_and, List.mem_cons]
                    exact ⟨(p.1, t_sp), Or.inl rfl, hs1, hlt1⟩
                  · by_cases hge2 : t_sp ≤ 2 * s.val
                    · left; left; simp only [S', L', Finset.mem_filter, Finset.mem_univ, true_and, List.mem_cons]
                      exact ⟨(t_sp, p.2), Or.inr (Or.inl rfl), hge2, hs2⟩
                    · right
                      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                      omega
                · by_cases hs' : s ∈ S_rest'
                  · left; left
                    simp only [S_rest', Finset.mem_filter, Finset.mem_univ, true_and] at hs'
                    rcases hs' with ⟨q', hq', h1, h2⟩
                    simp only [S', L', Finset.mem_filter, Finset.mem_univ, true_and, List.mem_cons]
                    exact ⟨q', Or.inr (Or.inr hq'), h1, h2⟩
                  · left; right
                    refine Finset.mem_sdiff.mpr ⟨?_, hs'⟩
                    simp only [S_rest, Finset.mem_filter, Finset.mem_univ, true_and]
                    exact ⟨q, hq, hs1, hs2⟩
              have hcard_cut : ((Finset.univ : Finset (Fin k)).filter (fun s => 2 * s.val + 1 = t_sp)).card ≤ 1 := by
                rw [Finset.card_le_one]
                intro a ha b hb
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
                ext; omega
              have hdiff_rest : (S_rest \ S_rest').card ≤ rest'.length - rest.length := by
                have hsub_s : S_rest' ⊆ S_rest := by
                  intro s hs
                  simp only [S_rest', Finset.mem_filter, Finset.mem_univ, true_and] at hs
                  rcases hs with ⟨q', hq', hs1, hs2⟩
                  rcases hsub_rest q' hq' with ⟨q, hq, h1, h2⟩
                  simp only [S_rest, Finset.mem_filter, Finset.mem_univ, true_and]
                  exact ⟨q, hq, le_trans h1 hs1, lt_of_lt_of_le hs2 h2⟩
                have h1 : (S_rest \ S_rest').card + S_rest'.card = S_rest.card :=
                  Finset.card_sdiff_add_card_eq_card hsub_s
                have hcov_r : S_rest.card ≤ S_rest'.card + (rest'.length - rest.length) := hcov_rest
                omega
              have hc1 := Finset.card_le_card hsub
              have hc2 := le_trans hc1 (Finset.card_union_le _ _)
              have hc3 := le_trans hc2 (Nat.add_le_add_right (Finset.card_union_le _ _) _)
              have hlen_eq : L'.length - (p :: rest).length = (rest'.length - rest.length) + 1 := by
                simp only [L', List.length_cons]; omega
              change S0.card ≤ S'.card + (L'.length - (p :: rest).length)
              omega
          · let L' := p :: rest'
            refine ⟨L', by simp [L']; omega, by simp [L']; omega, ?_, ?_, ?_, ?_⟩
            · intro q' hq'
              simp only [L', List.mem_cons] at hq'
              rcases hq' with hqp | hq'
              · rw [hqp]; exact ⟨p, by simp, le_rfl, le_rfl⟩
              · rcases hsub_rest q' hq' with ⟨q, hq, h1, h2⟩
                exact ⟨q, by simp [hq], h1, h2⟩
            · intro q hq
              simp only [L', List.mem_cons] at hq
              rcases hq with hqp | hq
              · rw [hqp]; exact hp_b
              · exact hrb q hq
            · intro q hq j hj hnot t₁ t₂ h1a h1b h2a h2b
              simp only [L', List.mem_cons] at hq
              rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjm | rfl
              · rcases hq with hqp | hq
                · rw [hqp] at h1a h1b h2a h2b; exact hp_not p (by simp) j hjm hnot t₁ t₂ h1a h1b h2a h2b
                · exact hrn q hq j (Nat.lt_succ_of_lt hjm) hnot t₁ t₂ h1a h1b h2a h2b
              · rcases hq with hqp | hq
                · rw [hqp] at h1a h1b h2a h2b
                  have hcases : t_sp = p.1 ∨ t_sp = p.2 := by omega
                  rcases hcases with rfl | rfl
                  · rw [ht_false t₁ h1a h1b, ht_false t₂ h2a h2b]
                  · rw [ht_true t₁ h1a h1b, ht_true t₂ h2a h2b]
                · exact hrn q hq _ hj hnot t₁ t₂ h1a h1b h2a h2b
            · let S0 := (Finset.univ : Finset (Fin k)).filter (fun s => ∃ q ∈ p :: rest, q.1 ≤ 2 * s.val ∧ 2 * s.val + 1 < q.2)
              let S' := (Finset.univ : Finset (Fin k)).filter (fun s => ∃ q ∈ L', q.1 ≤ 2 * s.val ∧ 2 * s.val + 1 < q.2)
              let S_rest := (Finset.univ : Finset (Fin k)).filter (fun s => ∃ q ∈ rest, q.1 ≤ 2 * s.val ∧ 2 * s.val + 1 < q.2)
              let S_rest' := (Finset.univ : Finset (Fin k)).filter (fun s => ∃ q ∈ rest', q.1 ≤ 2 * s.val ∧ 2 * s.val + 1 < q.2)
              have hsub : S0 ⊆ S' ∪ (S_rest \ S_rest') := by
                intro s hs
                simp only [S0, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_cons] at hs
                simp only [Finset.mem_union]
                rcases hs with ⟨q, hq_mem, hs1, hs2⟩
                rcases hq_mem with hqp | hq
                · rw [hqp] at hs1 hs2
                  left; simp only [S', L', Finset.mem_filter, Finset.mem_univ, true_and, List.mem_cons]
                  exact ⟨p, Or.inl rfl, hs1, hs2⟩
                · by_cases hs' : s ∈ S_rest'
                  · left
                    simp only [S_rest', Finset.mem_filter, Finset.mem_univ, true_and] at hs'
                    rcases hs' with ⟨q', hq', h1, h2⟩
                    simp only [S', L', Finset.mem_filter, Finset.mem_univ, true_and, List.mem_cons]
                    exact ⟨q', Or.inr hq', h1, h2⟩
                  · right
                    refine Finset.mem_sdiff.mpr ⟨?_, hs'⟩
                    simp only [S_rest, Finset.mem_filter, Finset.mem_univ, true_and]
                    exact ⟨q, hq, hs1, hs2⟩
              have hdiff_rest : (S_rest \ S_rest').card ≤ rest'.length - rest.length := by
                have hsub_s : S_rest' ⊆ S_rest := by
                  intro s hs
                  simp only [S_rest', Finset.mem_filter, Finset.mem_univ, true_and] at hs
                  rcases hs with ⟨q', hq', hs1, hs2⟩
                  rcases hsub_rest q' hq' with ⟨q, hq, h1, h2⟩
                  simp only [S_rest, Finset.mem_filter, Finset.mem_univ, true_and]
                  exact ⟨q, hq, le_trans h1 hs1, lt_of_lt_of_le hs2 h2⟩
                have h1 : (S_rest \ S_rest').card + S_rest'.card = S_rest.card :=
                  Finset.card_sdiff_add_card_eq_card hsub_s
                have hcov_r : S_rest.card ≤ S_rest'.card + (rest'.length - rest.length) := hcov_rest
                omega
              have hc1 := Finset.card_le_card hsub
              have hc2 := le_trans hc1 (Finset.card_union_le _ _)
              have hlen_eq : L'.length - (p :: rest).length = rest'.length - rest.length := by
                simp only [L', List.length_cons]; omega
              change S0.card ≤ S'.card + (L'.length - (p :: rest).length)
              omega
      rcases hrefine L hLbounds hLnot with ⟨L', hlen_ge, hlen_le, _, hL'b, hL'n, hL'cov⟩
      have hcard_succ : ((Finset.range (m + 1)).filter (fun j => (gateAt C j).op = GateOp.not)).card =
          ((Finset.range m).filter (fun j => (gateAt C j).op = GateOp.not)).card + 1 := by
        rw [Finset.range_add_one, Finset.filter_insert]
        simp [hm_not]
      refine ⟨L', le_trans hLpos hlen_ge, ?_, hL'b, hL'n, ?_⟩
      · rw [hcard_succ, pow_succ']
        exact le_trans hlen_le (Nat.mul_le_mul_left 2 hLlen)
      · omega
    · have hcard_eq : ((Finset.range (m + 1)).filter (fun j => (gateAt C j).op = GateOp.not)).card =
          ((Finset.range m).filter (fun j => (gateAt C j).op = GateOp.not)).card := by
        rw [Finset.range_add_one, Finset.filter_insert]
        simp [hm_not]
      refine ⟨L, hLpos, ?_, hLbounds, ?_, hLcov⟩
      · rwa [hcard_eq]
      · intro p hp j hj hnot
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjm | rfl
        · exact hLnot p hp j hjm hnot
        · exact absurd hnot hm_not

noncomputable def notParity (M : ℕ) (C : Circuit) (hRB : ReadsBack M C) (w : ℕ) : Bool :=
  if hw : w < M then false
  else
    let j := w - M
    if hj : j < C.gates.length then
      if (gateAt C j).op = GateOp.not then
        if h_in : (gateAt C j).inputs = [] then false
        else
          have hi : (gateAt C j).inputs.head h_in < w := by
            have := hRB j hj _ (List.head_mem h_in)
            omega
          !(notParity M C hRB ((gateAt C j).inputs.head h_in))
      else false
    else false
termination_by w

lemma notParity_pos {M : ℕ} {C : Circuit} {hRB : ReadsBack M C} {w : ℕ}
    (hw : ¬w < M) (hj : w - M < C.gates.length) (hop : (gateAt C (w - M)).op ≠ GateOp.not) :
    notParity M C hRB w = false := by
  conv_lhs => unfold notParity; dsimp only; simp [hw, hj, hop]

lemma notParity_ge_len {M : ℕ} {C : Circuit} {hRB : ReadsBack M C} {w : ℕ}
    (hw : ¬w < M) (hj : ¬w - M < C.gates.length) :
    notParity M C hRB w = false := by
  conv_lhs => unfold notParity; dsimp only; simp [hw, hj]

lemma notParity_cons {M : ℕ} {C : Circuit} {hRB : ReadsBack M C} {w i : ℕ} {is : List ℕ}
    (hw : ¬w < M) (hj : w - M < C.gates.length) (hop : (gateAt C (w - M)).op = GateOp.not)
    (h_in : (gateAt C (w - M)).inputs = i :: is) :
    notParity M C hRB w = !(notParity M C hRB i) := by
  conv_lhs => unfold notParity; dsimp only; simp [hw, hj, hop, h_in]

lemma wires_eq_xor_traceNot {M : ℕ} {C : Circuit} (hRB : ReadsBack M C)
    {x : List Bool} (hx : x.length = M) (w : ℕ)
    (htr_pos : ∃ g < C.gates.length, traceNot M C hRB w = M + g ∧ (gateAt C g).op ≠ GateOp.not) :
    (C.wires x).getD w false = xor (notParity M C hRB w) ((C.wires x).getD (traceNot M C hRB w) false) := by
  by_cases hw : w < M
  · rcases htr_pos with ⟨g, _, htr_eq, _⟩
    have hle := traceNot_le M C hRB w
    omega
  · by_cases hj : w - M < C.gates.length
    · by_cases hop : (gateAt C (w - M)).op = GateOp.not
      · cases h_in : (gateAt C (w - M)).inputs with
        | nil =>
          exfalso
          rcases htr_pos with ⟨g, _, htr_eq, hnot⟩
          rw [traceNot_nil hw hj hop h_in] at htr_eq
          have hgw : g = w - M := by omega
          rw [hgw] at hnot
          exact hnot hop
        | cons i is =>
          have hi : i < w := by have := hRB (w - M) hj i (by simp [h_in]); omega
          have htr_step := traceNot_cons (hRB := hRB) hw hj hop h_in
          have hnp_step := notParity_cons (hRB := hRB) hw hj hop h_in
          have htr_pos_i : ∃ g < C.gates.length, traceNot M C hRB i = M + g ∧ (gateAt C g).op ≠ GateOp.not := by
            rwa [← htr_step]
          have ih := wires_eq_xor_traceNot hRB hx i htr_pos_i
          have hgate := wires_getD_gate hRB hx hj
          have hw_eq : M + (w - M) = w := by omega
          rw [hw_eq] at hgate
          rw [hgate, hop, h_in, htr_step, hnp_step]
          simp only [GateOp.eval, List.map_cons, List.headD_cons]
          rw [ih]
          cases notParity M C hRB i <;> cases (C.wires x).getD (traceNot M C hRB i) false <;> rfl
      · rw [traceNot_pos hw hj hop, notParity_pos hw hj hop]; simp
    · rw [traceNot_ge_len hw hj, notParity_ge_len hw hj]; simp
termination_by w

lemma lower_bound_edges (k d r : ℕ) (E : Finset (Fin d × Fin d)) (hk : 0 < k)
    (hE_lt : ∀ z ∈ E, z.1 < z.2)
    (C : Circuit) (tap : Fin k → {z : Fin d × Fin d // z ∈ E} → ℕ)
    (hFan : FanInTwo C) (hRB : ReadsBack (k * (d + 1) + 2) C)
    (hb : notCount C ≤ r)
    (htap : ∀ s x z, (C.wires (rawFn k d s x)).getD (tap s z) false = (x z.val.1 && x z.val.2)) :
    max 1 (k / 2 ^ r) * E.card ≤ C.size - notCount C := by
  let M := k * (d + 1) + 2
  let posGates : Finset ℕ := (Finset.range C.gates.length).filter (fun j => decide ((gateAt C j).op ≠ GateOp.not) = true)
  have hpos_mem : ∀ {j}, j ∈ posGates ↔ j < C.gates.length ∧ (gateAt C j).op ≠ GateOp.not := by
    intro j; simp [posGates]
  have hpos_card : posGates.card = C.size - notCount C := by
    have h1 := notCount_plus_pos C
    have h2 : posGates.card = ((List.range C.gates.length).filter
        (fun j => decide ((gateAt C j).op ≠ GateOp.not))).length := by
      simpa [posGates] using finset_range_filter_card C.gates.length (fun j => decide ((gateAt C j).op ≠ GateOp.not))
    omega
  rw [← hpos_card]
  have htrace_pos : ∀ (s : Fin k) (z : {z : Fin d × Fin d // z ∈ E}),
      ∃ g ∈ posGates, traceNot M C hRB (tap s z) = M + g := by
    intro s z
    let xF : Fin d → Bool := fun _ => false
    let xZ : Fin d → Bool := fun v => decide (v = z.1.1 ∨ v = z.1.2)
    let x1 : Fin d → Bool := fun v => decide (v = z.1.1)
    let x2 : Fin d → Bool := fun v => decide (v = z.1.2)
    have hlenF : (rawFn k d s xF).length = M := rawFn_length k d s xF
    have hlenZ : (rawFn k d s xZ).length = M := rawFn_length k d s xZ
    have hlen1 : (rawFn k d s x1).length = M := rawFn_length k d s x1
    have hlen2 : (rawFn k d s x2).length = M := rawFn_length k d s x2
    have hF : (C.wires (rawFn k d s xF)).getD (tap s z) false = false := by rw [htap]; simp [xF]
    have hZ : (C.wires (rawFn k d s xZ)).getD (tap s z) false = true := by rw [htap]; simp [xZ]
    have hne12 : z.1.1 ≠ z.1.2 := ne_of_lt (hE_lt z.1 z.2)
    have h1 : (C.wires (rawFn k d s x1)).getD (tap s z) false = false := by
      rw [htap]; simp [x1, hne12.symm]
    have h2 : (C.wires (rawFn k d s x2)).getD (tap s z) false = false := by
      rw [htap]; simp [x2, hne12]
    have hdiffFZ : (C.wires (rawFn k d s xF)).getD (tap s z) false ≠
        (C.wires (rawFn k d s xZ)).getD (tap s z) false := by rw [hF, hZ]; decide
    rcases traceNot_diff hRB hlenF hlenZ hdiffFZ with ⟨hd_tr, hlt | ⟨g, hg, htr, hnot⟩⟩
    · exfalso
      let w := traceNot M C hRB (tap s z)
      have hw_diff : (rawFn k d s xF).getD w false ≠ (rawFn k d s xZ).getD w false := by
        rwa [wires_getD_prefix C _ 0 w (by rw [hlenF]; exact hlt),
          wires_getD_prefix C _ 0 w (by rw [hlenZ]; exact hlt)] at hd_tr
      have hw_cases : w = s.val * (d + 1) + 1 + z.1.1.val ∨ w = s.val * (d + 1) + 1 + z.1.2.val := by
        by_contra hno
        push_neg at hno
        apply hw_diff
        by_cases hwN : w < k * (d + 1)
        · have hdiv : w / (d + 1) < k := Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hwN)
          have hmod : w % (d + 1) < d + 1 := Nat.mod_lt _ (Nat.succ_pos d)
          let i : Fin k := ⟨w / (d + 1), hdiv⟩
          cases hj : w % (d + 1) with
          | zero =>
            have hw_eq : i.val * (d + 1) + 0 = w := by
              simpa [i, hj, Nat.mul_comm] using Nat.div_add_mod w (d + 1)
            rw [← hw_eq, rawFn_getD_lt k d s xF i 0 (Nat.succ_pos d), rawFn_getD_lt k d s xZ i 0 (Nat.succ_pos d)]
            rfl
          | succ j' =>
            have hw_eq : i.val * (d + 1) + (j' + 1) = w := by
              simpa [i, hj, Nat.mul_comm] using Nat.div_add_mod w (d + 1)
            rw [← hw_eq, rawFn_getD_lt k d s xF i (j' + 1) (by omega), rawFn_getD_lt k d s xZ i (j' + 1) (by omega)]
            simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceDIte]
            by_cases his : i = s
            · rw [his] at hw_eq
              have hj'_lt : j' < d := by omega
              have hne1 : (⟨j', hj'_lt⟩ : Fin d) ≠ z.1.1 := by
                intro heq; apply hno.1
                have hval : j' = z.1.1.val := congrArg Fin.val heq
                omega
              have hne2 : (⟨j', hj'_lt⟩ : Fin d) ≠ z.1.2 := by
                intro heq; apply hno.2
                have hval : j' = z.1.2.val := congrArg Fin.val heq
                omega
              simp only [his, lt_self_iff_false, decide_false, Bool.false_or, decide_true,
                Bool.true_and, Nat.add_sub_cancel, xF, xZ, decide_eq_true_eq, Bool.or_eq_true]
              simp [hne1, hne2]
            · simp [his]
        · have hlt' : w < k * (d + 1) + 2 := hlt
          have hcases : w = k * (d + 1) ∨ w = k * (d + 1) + 1 := by omega
          rcases hcases with hw0 | hw1
          · rw [hw0, rawFn_getD_N, rawFn_getD_N]
          · rw [hw1, rawFn_getD_N1, rawFn_getD_N1]
      rcases hw_cases with hw1 | hw2
      · have heq := traceNot_eval_eq_of_lt hRB hlen1 hlenZ (tap s z) hlt (by
          rw [show traceNot M C hRB (tap s z) = w from rfl, hw1]
          have hform : s.val * (d + 1) + 1 + z.1.1.val = s.val * (d + 1) + (z.1.1.val + 1) := by omega
          rw [hform, rawFn_getD_lt k d s x1 s _ (by omega), rawFn_getD_lt k d s xZ s _ (by omega)]
          simp [x1, xZ, Fin.ext_iff])
        rw [h1, hZ] at heq; contradiction
      · have heq := traceNot_eval_eq_of_lt hRB hlen2 hlenZ (tap s z) hlt (by
          rw [show traceNot M C hRB (tap s z) = w from rfl, hw2]
          have hform : s.val * (d + 1) + 1 + z.1.2.val = s.val * (d + 1) + (z.1.2.val + 1) := by omega
          rw [hform, rawFn_getD_lt k d s x2 s _ (by omega), rawFn_getD_lt k d s xZ s _ (by omega)]
          simp [x2, xZ, Fin.ext_iff])
        rw [h2, hZ] at heq; contradiction
    · exact ⟨g, hpos_mem.mpr ⟨hg, hnot⟩, htr⟩

  have h1_le : E.card ≤ posGates.card := by
    let s₀ : Fin k := ⟨0, hk⟩
    let fE : {z : Fin d × Fin d // z ∈ E} → ℕ := fun z => Classical.choose (htrace_pos s₀ z)
    have hfE_mem : ∀ z, fE z ∈ posGates := fun z => (Classical.choose_spec (htrace_pos s₀ z)).1
    have hfE_inj : ∀ z₁ z₂, fE z₁ = fE z₂ → z₁ = z₂ := by
      intro z₁ z₂ heq
      have htr1 := (Classical.choose_spec (htrace_pos s₀ z₁)).2
      have htr2 := (Classical.choose_spec (htrace_pos s₀ z₂)).2
      have htr_eq : traceNot M C hRB (tap s₀ z₁) = traceNot M C hRB (tap s₀ z₂) := by
        have heq' : Classical.choose (htrace_pos s₀ z₁) = Classical.choose (htrace_pos s₀ z₂) := heq
        rw [htr1, htr2, heq']
      by_contra hne
      let xF : Fin d → Bool := fun _ => false
      let xZ₁ : Fin d → Bool := fun v => decide (v = z₁.1.1 ∨ v = z₁.1.2)
      have hlenF : (rawFn k d s₀ xF).length = M := rawFn_length k d s₀ xF
      have hlenZ₁ : (rawFn k d s₀ xZ₁).length = M := rawFn_length k d s₀ xZ₁
      have hpos1 : ∃ g < C.gates.length, traceNot M C hRB (tap s₀ z₁) = M + g ∧ (gateAt C g).op ≠ GateOp.not :=
        ⟨fE z₁, (hpos_mem.mp (hfE_mem z₁)).1, htr1, (hpos_mem.mp (hfE_mem z₁)).2⟩
      have hpos2 : ∃ g < C.gates.length, traceNot M C hRB (tap s₀ z₂) = M + g ∧ (gateAt C g).op ≠ GateOp.not :=
        ⟨fE z₂, (hpos_mem.mp (hfE_mem z₂)).1, htr2, (hpos_mem.mp (hfE_mem z₂)).2⟩
      have hF1 := wires_eq_xor_traceNot hRB hlenF (tap s₀ z₁) hpos1
      have hF2 := wires_eq_xor_traceNot hRB hlenF (tap s₀ z₂) hpos2
      have hpar_eq : notParity M C hRB (tap s₀ z₁) = notParity M C hRB (tap s₀ z₂) := by
        have hv1 : (C.wires (rawFn k d s₀ xF)).getD (tap s₀ z₁) false = false := by rw [htap]; simp [xF]
        have hv2 : (C.wires (rawFn k d s₀ xF)).getD (tap s₀ z₂) false = false := by rw [htap]; simp [xF]
        have he1 : xor (notParity M C hRB (tap s₀ z₁))
            ((C.wires (rawFn k d s₀ xF)).getD (traceNot M C hRB (tap s₀ z₁)) false) = false :=
          hF1.symm.trans hv1
        have he2 : xor (notParity M C hRB (tap s₀ z₂))
            ((C.wires (rawFn k d s₀ xF)).getD (traceNot M C hRB (tap s₀ z₁)) false) = false := by
          have he2' : xor (notParity M C hRB (tap s₀ z₂))
              ((C.wires (rawFn k d s₀ xF)).getD (traceNot M C hRB (tap s₀ z₂)) false) = false :=
            hF2.symm.trans hv2
          rwa [htr_eq]
        have h1' : notParity M C hRB (tap s₀ z₁) =
            (C.wires (rawFn k d s₀ xF)).getD (traceNot M C hRB (tap s₀ z₁)) false := by
          cases hnp1 : notParity M C hRB (tap s₀ z₁) <;>
          cases hg : (C.wires (rawFn k d s₀ xF)).getD (traceNot M C hRB (tap s₀ z₁)) false <;>
          simp only [hnp1, hg, Bool.false_xor, Bool.true_xor] at he1 <;>
          first | rfl | exact absurd he1 (by decide)
        have h2' : notParity M C hRB (tap s₀ z₂) =
            (C.wires (rawFn k d s₀ xF)).getD (traceNot M C hRB (tap s₀ z₁)) false := by
          cases hnp2 : notParity M C hRB (tap s₀ z₂) <;>
          cases hg : (C.wires (rawFn k d s₀ xF)).getD (traceNot M C hRB (tap s₀ z₁)) false <;>
          simp only [hnp2, hg, Bool.false_xor, Bool.true_xor] at he2 <;>
          first | rfl | exact absurd he2 (by decide)
        exact h1'.trans h2'.symm
      have hZ1 := wires_eq_xor_traceNot hRB hlenZ₁ (tap s₀ z₁) hpos1
      have hZ2 := wires_eq_xor_traceNot hRB hlenZ₁ (tap s₀ z₂) hpos2
      have htap_eq : (C.wires (rawFn k d s₀ xZ₁)).getD (tap s₀ z₁) false =
          (C.wires (rawFn k d s₀ xZ₁)).getD (tap s₀ z₂) false := by
        rw [hZ1, hZ2, hpar_eq, htr_eq]
      rw [htap, htap] at htap_eq
      have hv1 : (xZ₁ z₁.1.1 && xZ₁ z₁.1.2) = true := by simp [xZ₁]
      have hv2 : (xZ₁ z₂.1.1 && xZ₁ z₂.1.2) = false := by
        by_contra htrue
        simp only [Bool.not_eq_false, Bool.and_eq_true, xZ₁, decide_eq_true_eq] at htrue
        rcases htrue with ⟨h21, h22⟩
        rcases h21 with h | h <;> rcases h22 with h' | h'
        · have := hE_lt z₂.1 z₂.2; rw [h, h'] at this; exact lt_irrefl _ this
        · apply hne; ext <;> simp [h, h']
        · have hlt1 := hE_lt z₁.1 z₁.2; have hlt2 := hE_lt z₂.1 z₂.2
          rw [h, h'] at hlt2; exact absurd (lt_trans hlt1 hlt2) (lt_irrefl _)
        · have := hE_lt z₂.1 z₂.2; rw [h, h'] at this; exact lt_irrefl _ this
      rw [hv1, hv2] at htap_eq
      contradiction
    have hcard_attach : E.attach.card ≤ posGates.card := by
      apply Finset.card_le_card_of_injOn fE (fun z _ => hfE_mem z) (fun z₁ _ z₂ _ h => hfE_inj z₁ z₂ h)
    simpa [Finset.card_attach] using hcard_attach
  by_cases hkq : k / 2 ^ r = 0
  · simp [hkq, max_eq_left (Nat.zero_le _), h1_le]
  · have hkq_pos : 1 ≤ k / 2 ^ r := Nat.pos_of_ne_zero hkq
    rw [max_eq_right hkq_pos]
    rcases exists_interval_partition hk hFan hRB C.gates.length le_rfl with
      ⟨L, hLpos, hLlen, hLbounds, hLnot, hLcov⟩
    have hnot_eq : ((Finset.range C.gates.length).filter (fun j => (gateAt C j).op = GateOp.not)).card =
        notCount C := by
      have h1 := notCount_plus_pos C
      have hsum : ((Finset.range C.gates.length).filter (fun j => (gateAt C j).op = GateOp.not)).card +
          posGates.card = C.gates.length := by
        have hdisj : Disjoint
            ((Finset.range C.gates.length).filter (fun j => (gateAt C j).op = GateOp.not))
            posGates := by
          rw [Finset.disjoint_filter]
          intro j _ h1' h2'
          simp only [decide_eq_true_eq] at h2'
          exact h2' h1'
        rw [← Finset.card_union_of_disjoint hdisj]
        have hunion : ((Finset.range C.gates.length).filter (fun j => (gateAt C j).op = GateOp.not)) ∪
            posGates = Finset.range C.gates.length := by
          ext j
          dsimp only [posGates]
          simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, decide_eq_true_eq]
          constructor
          · rintro (⟨h1, _⟩ | ⟨h1, _⟩) <;> exact h1
          · intro h1
            by_cases h : (gateAt C j).op = GateOp.not
            · left; exact ⟨h1, h⟩
            · right; exact ⟨h1, h⟩
        rw [hunion, Finset.card_range]
      have hsz_eq : C.size = C.gates.length := rfl
      omega
    have hLlen_q : L.length ≤ 2 ^ r := by
      rw [hnot_eq] at hLlen
      exact le_trans hLlen (Nat.pow_le_pow_right (by norm_num) hb)
    let goodS : ℕ × ℕ → Finset (Fin k) := fun p =>
      (Finset.univ : Finset (Fin k)).filter (fun s => p.1 ≤ 2 * s.val ∧ 2 * s.val + 1 < p.2)
    have hex_p : ∃ p ∈ L, k / 2 ^ r ≤ (goodS p).card := by
      by_contra hno
      push_neg at hno
      have hsum_le : (L.map (fun p => (goodS p).card)).sum ≤ L.length * (k / 2 ^ r - 1) := by
        have h1 : ∀ c ∈ L.map (fun p => (goodS p).card), c ≤ k / 2 ^ r - 1 := by
          intro c hc
          rcases List.mem_map.mp hc with ⟨p, hp, rfl⟩
          exact Nat.le_pred_of_lt (hno p hp)
        calc (L.map (fun p => (goodS p).card)).sum
            ≤ (L.map (fun p => (goodS p).card)).length * (k / 2 ^ r - 1) := List.sum_le_card_nsmul _ _ (fun x hx => h1 x hx)
          _ = L.length * (k / 2 ^ r - 1) := by simp
      have hcov_le : ((Finset.univ : Finset (Fin k)).filter
          (fun s => ∃ p ∈ L, p.1 ≤ 2 * s.val ∧ 2 * s.val + 1 < p.2)).card ≤
          (L.map (fun p => (goodS p).card)).sum := by
        clear hno hsum_le hLcov hLlen_q hLlen hLpos
        induction L with
        | nil => simp
        | cons q rest ih =>
          have hsub : (Finset.univ : Finset (Fin k)).filter
              (fun s => ∃ p ∈ q :: rest, p.1 ≤ 2 * s.val ∧ 2 * s.val + 1 < p.2) ⊆
              goodS q ∪ (Finset.univ : Finset (Fin k)).filter
              (fun s => ∃ p ∈ rest, p.1 ≤ 2 * s.val ∧ 2 * s.val + 1 < p.2) := by
            intro s hs
            simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_cons, goodS] at hs ⊢
            rcases hs with ⟨p, hp_mem, h1, h2⟩
            rcases hp_mem with rfl | hp
            · left; exact ⟨h1, h2⟩
            · right; exact ⟨p, hp, h1, h2⟩
          have hc := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
          simp only [List.map_cons, List.sum_cons]
          have ih' := ih (fun p hp => hLbounds p (by simp [hp])) (fun p hp => hLnot p (by simp [hp]))
          exact le_trans hc (Nat.add_le_add_left ih' _)
      have hmul : L.length * (k / 2 ^ r - 1) ≤ 2 ^ r * (k / 2 ^ r) - L.length := by
        have : L.length * (k / 2 ^ r - 1) + L.length = L.length * (k / 2 ^ r) := by
          rw [← Nat.mul_add_one, Nat.sub_add_cancel hkq_pos]
        have hle2 : L.length * (k / 2 ^ r) ≤ 2 ^ r * (k / 2 ^ r) :=
          Nat.mul_le_mul_right _ hLlen_q
        omega
      have hdiv_mul : 2 ^ r * (k / 2 ^ r) ≤ k := Nat.mul_div_le k (2 ^ r)
      have hle_prod : L.length ≤ 2 ^ r * (k / 2 ^ r) :=
        le_trans hLlen_q (Nat.le_mul_of_pos_right _ hkq_pos)
      omega
    rcases hex_p with ⟨p, hpL, hgood_card⟩
    have hp_b := hLbounds p hpL
    have htap_in_pos : ∀ s ∈ goodS p, ∀ z : {z : Fin d × Fin d // z ∈ E},
        ∃ g ∈ posGates, tap s z = M + g := by
      intro s hs z
      simp only [goodS, Finset.mem_filter, Finset.mem_univ, true_and] at hs
      rcases htrace_pos s z with ⟨g, hg, htr⟩
      have hchainF : chainInp k d hk (2 * s.val) = rawFn k d s (fun _ => false) := by
        simp [chainInp, show 2 * s.val < 2 * k by omega, Nat.mul_div_right _ (by norm_num : 0 < 2)]
      have hchainT : chainInp k d hk (2 * s.val + 1) = rawFn k d s (fun _ => true) := by
        simp [chainInp, show 2 * s.val + 1 < 2 * k by omega, show (2 * s.val + 1) % 2 = 1 by omega,
          show (2 * s.val + 1) / 2 = s.val by omega]
      have htapF : (C.wires (chainInp k d hk (2 * s.val))).getD (tap s z) false = false := by
        rw [hchainF, htap]; simp
      have htapT : (C.wires (chainInp k d hk (2 * s.val + 1))).getD (tap s z) false = true := by
        rw [hchainT, htap]; simp
      have hw_ge : M ≤ tap s z := by
        have := traceNot_le M C hRB (tap s z)
        omega
      have hj_lt : tap s z - M < C.gates.length := by
        by_contra hge
        push_neg at hge
        have hlenF : (C.wires (chainInp k d hk (2 * s.val))).length ≤ tap s z := by
          rw [wires_length, chainInp_length]; omega
        have hvalF : (C.wires (chainInp k d hk (2 * s.val))).getD (tap s z) false = false := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlenF]
        have hlenT : (C.wires (chainInp k d hk (2 * s.val + 1))).length ≤ tap s z := by
          rw [wires_length, chainInp_length]; omega
        have hvalT : (C.wires (chainInp k d hk (2 * s.val + 1))).getD (tap s z) false = false := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlenT]
        rw [hvalT] at htapT
        contradiction
      have hnot_op : (gateAt C (tap s z - M)).op ≠ GateOp.not := by
        intro hop
        have heq := hLnot p hpL (tap s z - M) hj_lt hop (2 * s.val) (2 * s.val + 1)
          hs.1 (by omega) (by omega) hs.2
        have hweq : M + (tap s z - M) = tap s z := by omega
        rw [hweq, htapF, htapT] at heq
        contradiction
      have htr_self : traceNot M C hRB (tap s z) = tap s z := by
        rw [traceNot]
        simp [show ¬(tap s z < M) by omega, hj_lt, hnot_op]
      refine ⟨tap s z - M, hpos_mem.mpr ⟨hj_lt, hnot_op⟩, by omega⟩
    let fSZ : Fin k × {z : Fin d × Fin d // z ∈ E} → ℕ := fun sz => tap sz.1 sz.2 - M
    have hfSZ_mem : ∀ sz ∈ (goodS p).product (E.attach), fSZ sz ∈ posGates := by
      intro sz hsz
      rcases Finset.mem_product.mp hsz with ⟨hs, _⟩
      rcases htap_in_pos sz.1 hs sz.2 with ⟨g, hg, htap_eq⟩
      have : fSZ sz = g := by dsimp [fSZ]; omega
      rwa [this]
    have hfSZ_inj : Set.InjOn fSZ ((goodS p).product (E.attach) : Set (Fin k × {z : Fin d × Fin d // z ∈ E})) := by
      intro ⟨s₁, z₁⟩ h1 ⟨s₂, z₂⟩ h2 heq
      rcases Finset.mem_product.mp h1 with ⟨hs1, _⟩
      rcases Finset.mem_product.mp h2 with ⟨hs2, _⟩
      rcases htap_in_pos s₁ hs1 z₁ with ⟨g₁, hg1, htap1⟩
      rcases htap_in_pos s₂ hs2 z₂ with ⟨g₂, hg2, htap2⟩
      have hg1_lt : g₁ < C.gates.length := (hpos_mem.mp hg1).1
      have hg2_lt : g₂ < C.gates.length := (hpos_mem.mp hg2).1
      have htap_eq : tap s₁ z₁ = tap s₂ z₂ := by
        dsimp [fSZ] at heq; omega
      have hs1_b := (Finset.mem_filter.mp hs1).2
      have hs2_b := (Finset.mem_filter.mp hs2).2
      dsimp [goodS] at hs1_b hs2_b
      rcases hs1_b with ⟨hs1_1, hs1_2⟩
      rcases hs2_b with ⟨hs2_1, hs2_2⟩
      have hs1_lt : s₁.val < k := s₁.isLt
      have hs2_lt : s₂.val < k := s₂.isLt
      have hs_eq : s₁ = s₂ := by
        by_contra hs_ne
        rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hs_ne) with hlt | hlt
        · have hmono := wires_mono_up_to hk hFan hRB p.1 p.2 C.gates.length hp_b.2 (hLnot p hpL)
            (tap s₁ z₁) (by omega) (2 * s₁.val + 1) (2 * s₂.val) (by omega) (by omega) (by omega)
          have hchainT1 : chainInp k d hk (2 * s₁.val + 1) = rawFn k d s₁ (fun _ => true) := by
            simp [chainInp, show 2 * s₁.val + 1 < 2 * k by omega, show (2 * s₁.val + 1) % 2 = 1 by omega,
              show (2 * s₁.val + 1) / 2 = s₁.val by omega]
          have hchainF2 : chainInp k d hk (2 * s₂.val) = rawFn k d s₂ (fun _ => false) := by
            simp [chainInp, show 2 * s₂.val < 2 * k by omega, Nat.mul_div_right _ (by norm_num : 0 < 2)]
          have hvT : (C.wires (chainInp k d hk (2 * s₁.val + 1))).getD (tap s₁ z₁) false = true := by
            rw [hchainT1, htap]; simp
          have hvF : (C.wires (chainInp k d hk (2 * s₂.val))).getD (tap s₁ z₁) false = false := by
            rw [hchainF2, htap_eq, htap]; simp
          have := hmono hvT
          rw [hvF] at this; contradiction
        · have hmono := wires_mono_up_to hk hFan hRB p.1 p.2 C.gates.length hp_b.2 (hLnot p hpL)
            (tap s₂ z₂) (by omega) (2 * s₂.val + 1) (2 * s₁.val) (by omega) (by omega) (by omega)
          have hchainT2 : chainInp k d hk (2 * s₂.val + 1) = rawFn k d s₂ (fun _ => true) := by
            simp [chainInp, show 2 * s₂.val + 1 < 2 * k by omega, show (2 * s₂.val + 1) % 2 = 1 by omega,
              show (2 * s₂.val + 1) / 2 = s₂.val by omega]
          have hchainF1 : chainInp k d hk (2 * s₁.val) = rawFn k d s₁ (fun _ => false) := by
            simp [chainInp, show 2 * s₁.val < 2 * k by omega, Nat.mul_div_right _ (by norm_num : 0 < 2)]
          have hvT : (C.wires (chainInp k d hk (2 * s₂.val + 1))).getD (tap s₂ z₂) false = true := by
            rw [hchainT2, htap]; simp
          have hvF : (C.wires (chainInp k d hk (2 * s₁.val))).getD (tap s₂ z₂) false = false := by
            rw [hchainF1, ← htap_eq, htap]; simp
          have := hmono hvT
          rw [hvF] at this; contradiction
      subst hs_eq
      have hz_eq : z₁ = z₂ := by
        by_contra hzne
        let xZ₁ : Fin d → Bool := fun v => decide (v = z₁.1.1 ∨ v = z₁.1.2)
        have h1' : (C.wires (rawFn k d s₁ xZ₁)).getD (tap s₁ z₁) false = true := by
          rw [htap]; simp [xZ₁]
        have h2' : (C.wires (rawFn k d s₁ xZ₁)).getD (tap s₁ z₁) false = false := by
          rw [htap_eq, htap]
          by_contra htrue
          simp only [Bool.not_eq_false, Bool.and_eq_true, xZ₁, decide_eq_true_eq] at htrue
          rcases htrue with ⟨h21, h22⟩
          rcases h21 with h | h <;> rcases h22 with h' | h'
          · have := hE_lt z₂.1 z₂.2; rw [h, h'] at this; exact lt_irrefl _ this
          · apply hzne; ext <;> simp [h, h']
          · have hlt1 := hE_lt z₁.1 z₁.2; have hlt2 := hE_lt z₂.1 z₂.2
            rw [h, h'] at hlt2; exact absurd (lt_trans hlt1 hlt2) (lt_irrefl _)
          · have := hE_lt z₂.1 z₂.2; rw [h, h'] at this; exact lt_irrefl _ this
        rw [h1'] at h2'; contradiction
      exact Prod.ext rfl hz_eq
    have hcard_prod := Finset.card_le_card_of_injOn fSZ hfSZ_mem hfSZ_inj
    simp only [Finset.product_eq_sprod, Finset.card_product, Finset.card_attach] at hcard_prod
    exact le_trans (Nat.mul_le_mul_right E.card hgood_card) hcard_prod

lemma wires_append_eq {M : ℕ} (gs1 gs2 : List Gate) (out1 out2 : ℕ)
    {x : List Bool} (hx : x.length = M) {w : ℕ} (hw : w < M + gs1.length) :
    (({ gates := gs1 ++ gs2, output := out2 } : Circuit).wires x).getD w false =
    (({ gates := gs1, output := out1 } : Circuit).wires x).getD w false := by
  have h1 := wires_getD_prefix ({ gates := gs1 ++ gs2, output := out2 } : Circuit) x gs1.length w (by
    rw [hx, List.length_append]; omega)
  have h2 := wires_getD_prefix ({ gates := gs1, output := out1 } : Circuit) x gs1.length w (by
    rw [hx, min_self]; exact hw)
  rw [h1, h2]
  simp [wiresPrefix, List.take_left]

lemma notCount_append (gs1 gs2 : List Gate) (out1 out2 : ℕ) :
    notCount { gates := gs1 ++ gs2, output := out2 } =
    notCount { gates := gs1, output := out1 } +
    notCount { gates := gs2, output := out1 } := by
  simp [notCount, List.filter_append]

lemma notCount_singleton_and (ins : List ℕ) :
    notCount { gates := [⟨GateOp.and, ins⟩], output := 0 } = 0 := by
  simp [notCount]

lemma notCount_singleton_or (ins : List ℕ) :
    notCount { gates := [⟨GateOp.or, ins⟩], output := 0 } = 0 := by
  simp [notCount]

lemma notCount_singleton_not (ins : List ℕ) :
    notCount { gates := [⟨GateOp.not, ins⟩], output := 0 } = 1 := by
  simp [notCount]

def emitGate (M : ℕ) (gs : List Gate) (op : GateOp) (ins : List ℕ) : List Gate × ℕ :=
  (gs ++ [⟨op, ins⟩], M + gs.length)

def emitOrList (M constFalse : ℕ) (gs : List Gate) : List ℕ → List Gate × ℕ
  | [] => (gs, constFalse)
  | [w] => (gs, w)
  | w :: ws =>
    let res := emitOrList M constFalse gs ws
    emitGate M res.1 GateOp.or [w, res.2]

def CircuitInv (M : ℕ) (gs : List Gate) : Prop :=
  FanInTwo { gates := gs, output := 0 } ∧ ReadsBack M { gates := gs, output := 0 }

lemma emitGate_inv {M : ℕ} {gs : List Gate} (hInv : CircuitInv M gs)
    {op : GateOp} (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    {ins : List ℕ} (hins_len : ins.length ≤ 2) (hins_lt : ∀ i ∈ ins, i < M + gs.length) :
    CircuitInv M (emitGate M gs op ins).1 ∧
    (emitGate M gs op ins).2 < M + (emitGate M gs op ins).1.length ∧
    (emitGate M gs op ins).1.length = gs.length + 1 := by
  refine ⟨⟨?_, ?_⟩, ?_, by simp [emitGate]⟩
  · intro g hg
    simp only [emitGate, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hInv.1 g hg
    · exact ⟨hop, hins_len⟩
  · intro j hj i hi
    dsimp only [emitGate] at hj hi
    simp only [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjm | rfl
    · have hget : gateAt { gates := gs ++ [⟨op, ins⟩], output := 0 } j =
          gateAt { gates := gs, output := 0 } j := by
        simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_append_left hjm]
      rw [hget] at hi
      exact hInv.2 j hjm i hi
    · have hget : gateAt { gates := gs ++ [⟨op, ins⟩], output := 0 } gs.length = ⟨op, ins⟩ := by
        simp [gateAt, List.getD_eq_getElem?_getD]
      rw [hget] at hi
      exact hins_lt i hi
  · simp [emitGate]

lemma emitGate_eval {M : ℕ} {gs : List Gate} (hInv : CircuitInv M gs)
    {op : GateOp} (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    {ins : List ℕ} (hins_len : ins.length ≤ 2) (hins_lt : ∀ i ∈ ins, i < M + gs.length)
    {x : List Bool} (hx : x.length = M) :
    (({ gates := (emitGate M gs op ins).1, output := 0 } : Circuit).wires x).getD
      (emitGate M gs op ins).2 false =
    op.eval (ins.map fun i => (({ gates := gs, output := 0 } : Circuit).wires x).getD i false) := by
  have hInv' := emitGate_inv hInv hop hins_len hins_lt
  have hj_lt : gs.length < (emitGate M gs op ins).1.length := by rw [hInv'.2.2]; omega
  have hw := wires_getD_gate hInv'.1.2 hx hj_lt
  have hget : gateAt { gates := (emitGate M gs op ins).1, output := 0 } gs.length = ⟨op, ins⟩ := by
    simp [emitGate, gateAt, List.getD_eq_getElem?_getD]
  change (({ gates := (emitGate M gs op ins).1, output := 0 } : Circuit).wires x).getD (M + gs.length) false = _
  rw [hw, hget]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact wires_append_eq gs [⟨op, ins⟩] 0 0 hx (hins_lt i hi)

lemma emitOrList_spec {M constFalse : ℕ} (hcf : constFalse < M)
    {gs : List Gate} (hInv : CircuitInv M gs)
    (ws : List ℕ) (hws : ∀ w ∈ ws, w < M + gs.length) :
    ∃ gs_ext : List Gate,
      (emitOrList M constFalse gs ws).1 = gs ++ gs_ext ∧
      CircuitInv M (emitOrList M constFalse gs ws).1 ∧
      (emitOrList M constFalse gs ws).2 < M + (emitOrList M constFalse gs ws).1.length ∧
      gs_ext.length ≤ ws.length ∧
      notCount { gates := gs_ext, output := 0 } = 0 ∧
      ∀ {x : List Bool}, x.length = M → x.getD constFalse false = false →
        (({ gates := (emitOrList M constFalse gs ws).1, output := 0 } : Circuit).wires x).getD
          (emitOrList M constFalse gs ws).2 false =
        ws.any (fun w => (({ gates := gs, output := 0 } : Circuit).wires x).getD w false) := by
  induction ws generalizing gs with
  | nil =>
    refine ⟨[], by simp [emitOrList], hInv, by simp [emitOrList]; omega, by simp, rfl, ?_⟩
    intro x hx hcf_val
    simp only [emitOrList, List.any_nil]
    rw [wires_getD_prefix _ x 0 constFalse (by rw [hx]; exact hcf)]
    simpa [wiresPrefix] using hcf_val
  | cons w ws ih =>
    cases ws with
    | nil =>
      refine ⟨[], by simp [emitOrList], hInv, ?_, by simp, rfl, ?_⟩
      · simp [emitOrList]; exact hws w (by simp)
      · intro x hx _; simp [emitOrList]
    | cons w2 ws2 =>
      rcases ih hInv (fun u hu => hws u (by simp [hu])) with
        ⟨ext1, heq1, hInv1, hr_lt, hlen1, hnot1, heval1⟩
      let res := emitOrList M constFalse gs (w2 :: ws2)
      have hw_lt : w < M + res.1.length := by
        have : gs.length ≤ res.1.length := by rw [heq1, List.length_append]; omega
        have := hws w (by simp)
        omega
      have hgate_inv := emitGate_inv hInv1 (op := GateOp.or) (ins := [w, res.2]) (by simp)
        (by simp only [List.length_cons, List.length_nil]; omega)
        (fun i hi => by
          cases hi with
          | head => exact hw_lt
          | tail _ hi2 => cases hi2 with
            | head => exact hr_lt
            | tail _ hi3 => cases hi3)
      refine ⟨ext1 ++ [⟨GateOp.or, [w, res.2]⟩], ?_, hgate_inv.1, hgate_inv.2.1, ?_, ?_, ?_⟩
      · simp only [emitOrList, emitGate, res] at heq1 ⊢
        rw [heq1, List.append_assoc]
      · simp only [List.length_append, List.length_singleton]
        simp only [List.length_cons] at hlen1 ⊢
        omega
      · rw [notCount_append _ _ 0 0, notCount_singleton_or, hnot1]
      · intro x hx hcf_val
        simp only [emitOrList]
        change (({ gates := (emitGate M res.1 GateOp.or [w, res.2]).1, output := 0 } : Circuit).wires x).getD
          (emitGate M res.1 GateOp.or [w, res.2]).2 false = _
        rw [emitGate_eval hInv1 (by simp) (by simp only [List.length_cons, List.length_nil]; omega) (fun i hi => by simp at hi; rcases hi with rfl | rfl <;> assumption) hx]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
        have hw_eq : (({ gates := res.1, output := 0 } : Circuit).wires x).getD w false =
            (({ gates := gs, output := 0 } : Circuit).wires x).getD w false := by
          change (({ gates := res.1, output := 0 } : Circuit).wires x).getD w false = _
          rw [heq1]
          exact wires_append_eq gs ext1 0 0 hx (hws w (by simp))
        rw [hw_eq, heval1 hx hcf_val]
        simp

def emitTerms (M h j : ℕ) (headWire : ℕ → ℕ) (gs : List Gate) (p0 : ℕ) :
    List ℕ → List Gate × List ℕ
  | [] => (gs, [])
  | w :: ws =>
    let res := emitGate M gs GateOp.and [w, headWire (((2 * p0 + 1) * 2 ^ j) * h)]
    let rest := emitTerms M h j headWire res.1 (p0 + 1) ws
    (rest.1, res.2 :: rest.2)

def emitNextPrefs (M nbit bit : ℕ) (gs : List Gate) : List ℕ → List Gate × List ℕ
  | [] => (gs, [])
  | w :: ws =>
    let r0 := emitGate M gs GateOp.and [w, nbit]
    let r1 := emitGate M r0.1 GateOp.and [w, bit]
    let rest := emitNextPrefs M nbit bit r1.1 ws
    (rest.1, r0.2 :: r1.2 :: rest.2)

def buildPrefixStep (M constFalse h j : ℕ) (headWire : ℕ → ℕ) (gs : List Gate) (prefs : List ℕ) :
    List Gate × List ℕ :=
  let tRes := emitTerms M h j headWire gs 0 prefs
  let orRes := emitOrList M constFalse tRes.1 tRes.2
  let notRes := emitGate M orRes.1 GateOp.not [orRes.2]
  emitNextPrefs M notRes.2 orRes.2 notRes.1 prefs

def buildPrefixes (M constFalse constTrue h m : ℕ) (headWire : ℕ → ℕ) :
    ℕ → List Gate × List ℕ
  | 0 => ([], [constTrue])
  | a + 1 =>
    let prev := buildPrefixes M constFalse constTrue h m headWire a
    buildPrefixStep M constFalse h (m - 1 - a) headWire prev.1 prev.2

lemma emitTerms_spec {M h j : ℕ} {headWire : ℕ → ℕ} (hhw : ∀ t, headWire t < M)
    {gs : List Gate} (hInv : CircuitInv M gs) (p0 : ℕ) (ws : List ℕ)
    (hws : ∀ w ∈ ws, w < M + gs.length) :
    ∃ ext : List Gate,
      (emitTerms M h j headWire gs p0 ws).1 = gs ++ ext ∧
      CircuitInv M (emitTerms M h j headWire gs p0 ws).1 ∧
      (emitTerms M h j headWire gs p0 ws).2.length = ws.length ∧
      (∀ t ∈ (emitTerms M h j headWire gs p0 ws).2,
        t < M + (emitTerms M h j headWire gs p0 ws).1.length) ∧
      ext.length = ws.length ∧
      notCount { gates := ext, output := 0 } = 0 ∧
      ∀ {x : List Bool} (hx : x.length = M) (idx : ℕ) (hidx : idx < ws.length),
        (({ gates := (emitTerms M h j headWire gs p0 ws).1, output := 0 } : Circuit).wires x).getD
          ((emitTerms M h j headWire gs p0 ws).2.getD idx 0) false =
        ((({ gates := gs, output := 0 } : Circuit).wires x).getD (ws.getD idx 0) false &&
          x.getD (headWire (((2 * (p0 + idx) + 1) * 2 ^ j) * h)) false) := by
  induction ws generalizing gs p0 with
  | nil =>
    refine ⟨[], by simp [emitTerms], hInv, by simp [emitTerms], by simp [emitTerms],
      by simp [emitTerms], rfl, ?_⟩
    intro x hx idx hidx; simp at hidx
  | cons w ws ih =>
    let res := emitGate M gs GateOp.and [w, headWire (((2 * p0 + 1) * 2 ^ j) * h)]
    have hw_lt : w < M + gs.length := hws w (by simp)
    have hhw_lt : headWire (((2 * p0 + 1) * 2 ^ j) * h) < M + gs.length := by
      have := hhw (((2 * p0 + 1) * 2 ^ j) * h); omega
    have hres_inv := emitGate_inv hInv (op := GateOp.and) (ins := [w, headWire (((2 * p0 + 1) * 2 ^ j) * h)]) (by simp) (by simp only [List.length_cons, List.length_nil]; omega)
      (fun i hi => by cases hi with | head => exact hw_lt | tail _ hi2 => cases hi2 with | head => exact hhw_lt | tail _ hi3 => cases hi3)
    rcases ih hres_inv.1 (p0 + 1) (fun u hu => by
        have := hws u (by simp [hu]); rw [hres_inv.2.2]; omega) with
      ⟨ext1, heq1, hInv1, hlen_t, ht_lt, hext1_len, hnot1, heval1⟩
    refine ⟨[⟨GateOp.and, [w, headWire (((2 * p0 + 1) * 2 ^ j) * h)]⟩] ++ ext1, ?_, hInv1,
      by dsimp only [emitTerms]; simp [hlen_t], ?_, by simp [hext1_len],
      by rw [notCount_append _ _ 0 0, notCount_singleton_and, hnot1], ?_⟩
    · simp only [emitTerms, res] at heq1 ⊢
      rw [heq1, List.singleton_append, emitGate, List.append_assoc]
      rfl
    · intro t ht
      simp only [emitTerms, List.mem_cons] at ht
      rcases ht with rfl | ht
      · have hlen : gs.length < (emitTerms M h j headWire res.1 (p0 + 1) ws).1.length := by
          rw [heq1, List.length_append, hres_inv.2.2]; omega
        dsimp only [res] at hlen
        change (emitGate M gs GateOp.and [w, headWire (((2 * p0 + 1) * 2 ^ j) * h)]).2 <
          M + (emitTerms M h j headWire (emitGate M gs GateOp.and [w, headWire (((2 * p0 + 1) * 2 ^ j) * h)]).1 (p0 + 1) ws).1.length
        dsimp only [emitGate] at hlen ⊢; omega
      · exact ht_lt t ht
    · intro x hx idx hidx
      simp only [emitTerms]
      cases idx with
      | zero =>
        simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some]
        change (({ gates := (emitTerms M h j headWire res.1 (p0 + 1) ws).1, output := 0 } : Circuit).wires x).getD
          res.2 false = _
        rw [heq1, wires_append_eq res.1 ext1 0 0 hx hres_inv.2.1]
        rw [emitGate_eval hInv (ins := [w, headWire (((2 * p0 + 1) * 2 ^ j) * h)]) (by simp) (by simp only [List.length_cons, List.length_nil]; omega)
          (fun i hi => by cases hi with | head => exact hw_lt | tail _ hi2 => cases hi2 with | head => exact hhw_lt | tail _ hi3 => cases hi3) hx]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
        rw [wires_getD_prefix _ x 0 (headWire _) (by rw [hx]; exact hhw _)]
        simp [wiresPrefix, Nat.add_zero]
      | succ idx' =>
        simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ]
        have hidx' : idx' < ws.length := by simpa using hidx
        have hev := heval1 hx idx' hidx'
        simp only [List.getD_eq_getElem?_getD] at hev
        rw [hev]
        have hw_eq : (({ gates := res.1, output := 0 } : Circuit).wires x).getD ((ws[idx']?).getD 0) false =
            (({ gates := gs, output := 0 } : Circuit).wires x).getD ((ws[idx']?).getD 0) false := by
          change (({ gates := (emitGate M gs GateOp.and _).1, output := 0 } : Circuit).wires x).getD _ false = _
          simp only [emitGate]
          apply wires_append_eq gs _ 0 0 hx
          have hmem : (ws[idx']?).getD 0 ∈ ws := by
            simp [hidx', List.getElem_mem]
          exact hws _ (List.mem_cons_of_mem w hmem)
        simp only [List.getD_eq_getElem?_getD] at hw_eq
        rw [hw_eq, show p0 + 1 + idx' = p0 + (idx' + 1) by omega]

lemma emitNextPrefs_spec {M nbit bit : ℕ} {gs : List Gate} (hInv : CircuitInv M gs)
    (hnbit : nbit < M + gs.length) (hbit : bit < M + gs.length)
    (ws : List ℕ) (hws : ∀ w ∈ ws, w < M + gs.length) :
    ∃ ext : List Gate,
      (emitNextPrefs M nbit bit gs ws).1 = gs ++ ext ∧
      CircuitInv M (emitNextPrefs M nbit bit gs ws).1 ∧
      (emitNextPrefs M nbit bit gs ws).2.length = 2 * ws.length ∧
      (∀ u ∈ (emitNextPrefs M nbit bit gs ws).2,
        u < M + (emitNextPrefs M nbit bit gs ws).1.length) ∧
      ext.length = 2 * ws.length ∧
      notCount { gates := ext, output := 0 } = 0 ∧
      ∀ {x : List Bool} (hx : x.length = M) (idx : ℕ) (hidx : idx < ws.length),
        (({ gates := (emitNextPrefs M nbit bit gs ws).1, output := 0 } : Circuit).wires x).getD
          ((emitNextPrefs M nbit bit gs ws).2.getD (2 * idx) 0) false =
          ((({ gates := gs, output := 0 } : Circuit).wires x).getD (ws.getD idx 0) false &&
           (({ gates := gs, output := 0 } : Circuit).wires x).getD nbit false) ∧
        (({ gates := (emitNextPrefs M nbit bit gs ws).1, output := 0 } : Circuit).wires x).getD
          ((emitNextPrefs M nbit bit gs ws).2.getD (2 * idx + 1) 0) false =
          ((({ gates := gs, output := 0 } : Circuit).wires x).getD (ws.getD idx 0) false &&
           (({ gates := gs, output := 0 } : Circuit).wires x).getD bit false) := by
  induction ws generalizing gs with
  | nil =>
    refine ⟨[], by simp [emitNextPrefs], hInv, rfl, by simp [emitNextPrefs],
      rfl, rfl, ?_⟩
    intro x hx idx hidx; simp at hidx
  | cons w ws ih =>
    let r0 := emitGate M gs GateOp.and [w, nbit]
    have hw_lt : w < M + gs.length := hws w (by simp)
    have hr0_inv := emitGate_inv hInv (op := GateOp.and) (ins := [w, nbit]) (by simp) (by simp only [List.length_cons, List.length_nil]; omega)
      (fun i hi => by cases hi with | head => exact hw_lt | tail _ hi2 => cases hi2 with | head => exact hnbit | tail _ hi3 => cases hi3)
    let r1 := emitGate M r0.1 GateOp.and [w, bit]
    have hr1_inv := emitGate_inv hr0_inv.1 (op := GateOp.and) (ins := [w, bit]) (by simp) (by simp only [List.length_cons, List.length_nil]; omega)
      (fun i hi => by
        cases hi with
        | head => rw [hr0_inv.2.2]; omega
        | tail _ hi2 => cases hi2 with
          | head => rw [hr0_inv.2.2]; omega
          | tail _ hi3 => cases hi3)
    rcases ih hr1_inv.1 (by rw [hr1_inv.2.2, hr0_inv.2.2]; omega)
      (by rw [hr1_inv.2.2, hr0_inv.2.2]; omega)
      (fun u hu => by have := hws u (by simp [hu]); rw [hr1_inv.2.2, hr0_inv.2.2]; omega) with
      ⟨ext1, heq1, hInv1, hlen_u, hu_lt, hext1_len, hnot1, heval1⟩
    refine ⟨[⟨GateOp.and, [w, nbit]⟩, ⟨GateOp.and, [w, bit]⟩] ++ ext1, ?_, hInv1,
      by simp [emitNextPrefs, hlen_u]; omega, ?_, by simp [hext1_len]; omega,
      by
        have h2 : ([⟨GateOp.and, [w, nbit]⟩, ⟨GateOp.and, [w, bit]⟩] : List Gate) =
            [⟨GateOp.and, [w, nbit]⟩] ++ [⟨GateOp.and, [w, bit]⟩] := rfl
        rw [notCount_append _ ext1 0 0, h2, notCount_append _ _ 0 0, notCount_singleton_and, notCount_singleton_and, hnot1], ?_⟩
    · simp only [emitNextPrefs, r0, r1] at heq1 ⊢
      rw [heq1, emitGate, emitGate, List.append_assoc, List.append_assoc]
      rfl
    · intro u hu
      simp only [emitNextPrefs, List.mem_cons] at hu
      rcases hu with rfl | rfl | hu
      · have hle1 : (emitGate M r0.1 GateOp.and [w, bit]).1.length ≤ (emitNextPrefs M nbit bit r1.1 ws).1.length := by
          rw [heq1, List.length_append]; exact Nat.le_add_right _ _
        have hle0 : r0.1.length ≤ (emitNextPrefs M nbit bit r1.1 ws).1.length := by
          have hsucc : r0.1.length ≤ (emitGate M r0.1 GateOp.and [w, bit]).1.length := by
            rw [hr1_inv.2.2]; exact Nat.le_succ _
          exact le_trans hsucc hle1
        exact lt_of_lt_of_le hr0_inv.2.1 (Nat.add_le_add_left hle0 M)
      · have hle1 : r1.1.length ≤ (emitNextPrefs M nbit bit r1.1 ws).1.length := by
          change (emitGate M r0.1 GateOp.and [w, bit]).1.length ≤ _
          rw [heq1, List.length_append]; exact Nat.le_add_right _ _
        exact lt_of_lt_of_le hr1_inv.2.1 (Nat.add_le_add_left hle1 M)
      · exact hu_lt u hu
    · intro x hx idx hidx
      simp only [emitNextPrefs]
      cases idx with
      | zero =>
        simp only [Nat.mul_zero, Nat.zero_add, List.getD_eq_getElem?_getD,
          List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
        constructor
        · change (({ gates := (emitNextPrefs M nbit bit r1.1 ws).1, output := 0 } : Circuit).wires x).getD r0.2 false = _
          rw [heq1, wires_append_eq r1.1 ext1 0 0 hx (by rw [hr1_inv.2.2]; exact lt_of_lt_of_le hr0_inv.2.1 (by omega))]
          change (({ gates := (emitGate M r0.1 GateOp.and [w, bit]).1, output := 0 } : Circuit).wires x).getD r0.2 false = _
          rw [emitGate, wires_append_eq r0.1 _ 0 0 hx hr0_inv.2.1]
          rw [emitGate_eval hInv (ins := [w, nbit]) (by simp) (by simp only [List.length_cons, List.length_nil]; omega)
            (fun i hi => by cases hi with | head => exact hw_lt | tail _ hi2 => cases hi2 with | head => exact hnbit | tail _ hi3 => cases hi3) hx]
          simp [GateOp.eval, List.getD_eq_getElem?_getD]
        · change (({ gates := (emitNextPrefs M nbit bit r1.1 ws).1, output := 0 } : Circuit).wires x).getD r1.2 false = _
          rw [heq1, wires_append_eq r1.1 ext1 0 0 hx hr1_inv.2.1]
          rw [emitGate_eval hr0_inv.1 (ins := [w, bit]) (by simp) (by simp only [List.length_cons, List.length_nil]; omega) (fun i hi => by
            cases hi with
            | head => rw [hr0_inv.2.2]; omega
            | tail _ hi2 => cases hi2 with
              | head => rw [hr0_inv.2.2]; omega
              | tail _ hi3 => cases hi3) hx]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          simp only [r0, emitGate]
          rw [wires_append_eq gs _ 0 0 hx hw_lt, wires_append_eq gs _ 0 0 hx hbit]
          simp only [List.getD_eq_getElem?_getD]
      | succ idx' =>
        simp only [show 2 * (idx' + 1) = 2 * idx' + 2 by omega,
          show 2 * (idx' + 1) + 1 = 2 * idx' + 2 + 1 by omega,
          List.getD_eq_getElem?_getD, List.getElem?_cons_succ]
        have hidx' : idx' < ws.length := by simpa using hidx
        have hev := heval1 hx idx' hidx'
        simp only [List.getD_eq_getElem?_getD] at hev
        have hws_mem : (ws[idx']?).getD 0 ∈ ws := by simp [hidx', List.getElem_mem]
        have h1 : (({ gates := r1.1, output := 0 } : Circuit).wires x).getD ((ws[idx']?).getD 0) false =
            (({ gates := gs, output := 0 } : Circuit).wires x).getD ((ws[idx']?).getD 0) false := by
          simp only [r1, r0, emitGate, List.append_assoc]
          exact wires_append_eq gs _ 0 0 hx (hws _ (List.mem_cons_of_mem w hws_mem))
        have h2 : (({ gates := r1.1, output := 0 } : Circuit).wires x).getD nbit false =
            (({ gates := gs, output := 0 } : Circuit).wires x).getD nbit false := by
          simp only [r1, r0, emitGate, List.append_assoc]
          exact wires_append_eq gs _ 0 0 hx hnbit
        have h3 : (({ gates := r1.1, output := 0 } : Circuit).wires x).getD bit false =
            (({ gates := gs, output := 0 } : Circuit).wires x).getD bit false := by
          simp only [r1, r0, emitGate, List.append_assoc]
          exact wires_append_eq gs _ 0 0 hx hbit
        dsimp only [r1, r0] at hev h1 h2 h3
        simp only [List.getD_eq_getElem?_getD] at h1 h2 h3
        rw [hev.1, hev.2, h1, h2, h3]
        exact ⟨rfl, rfl⟩

lemma buildPrefixes_spec (k d m h : ℕ) (hk : 0 < k) (hh : 0 < h)
    (a : ℕ) (ha : a ≤ m) :
    let M := k * (d + 1) + 2
    let constFalse := k * (d + 1)
    let constTrue := k * (d + 1) + 1
    let headWire : ℕ → ℕ := fun t => if t < k then t * (d + 1) else constFalse
    let res := buildPrefixes M constFalse constTrue h m headWire a
    CircuitInv M res.1 ∧
    res.2.length = 2 ^ a ∧
    (∀ w ∈ res.2, w < M + res.1.length) ∧
    res.1.length ≤ 4 * (2 ^ a - 1) + a ∧
    notCount { gates := res.1, output := 0 } = a ∧
    ∀ (s : Fin k) (x : Fin d → Bool) (p : ℕ) (hp : p < 2 ^ a),
      s.val / h < 2 ^ m →
      (({ gates := res.1, output := 0 } : Circuit).wires (rawFn k d s x)).getD (res.2.getD p 0) false =
        decide ((s.val / h) / 2 ^ (m - a) = p) := by
  induction a with
  | zero =>
    intro M constFalse constTrue headWire res
    refine ⟨⟨by intro g hg; simp [res, buildPrefixes] at hg, by intro j hj; simp [res, buildPrefixes] at hj⟩,
      by simp [res, buildPrefixes], by intro w hw; simp [res, buildPrefixes] at hw; subst hw; omega,
      by simp [res, buildPrefixes], by simp [res, buildPrefixes, notCount], ?_⟩
    intro s x p hp hu
    have hp0 : p = 0 := by simpa using hp
    subst hp0
    change (({ gates := [], output := 0 } : Circuit).wires (rawFn k d s x)).getD constTrue false = _
    rw [wires_getD_prefix _ _ 0 constTrue (by rw [rawFn_length]; omega)]
    simp only [wiresPrefix, List.take_zero, List.foldl_nil, constTrue, rawFn_getD_N1]
    have hdiv0 : (s.val / h) / 2 ^ m = 0 := Nat.div_eq_of_lt hu
    simp [hdiv0]
  | succ a ih =>
    intro M constFalse constTrue headWire res
    rcases ih (Nat.le_of_succ_le ha) with ⟨hInv0, hlen0, hw0, hsz0, hnot0, heval0⟩
    let prev := buildPrefixes M constFalse constTrue h m headWire a
    have hcf_lt : constFalse < M := by omega
    have hhw_lt : ∀ t, headWire t < M := by
      intro t; dsimp [headWire]; split_ifs with ht
      · calc t * (d + 1) < k * (d + 1) := Nat.mul_lt_mul_of_pos_right ht (Nat.succ_pos d)
          _ < M := by omega
      · omega
    let j := m - 1 - a
    let tRes := emitTerms M h j headWire prev.1 0 prev.2
    rcases emitTerms_spec hhw_lt hInv0 0 prev.2 hw0 with
      ⟨extT, heqT, hInvT, hlenT, ht_lt, hextT_len, hnotT, hevalT⟩
    let orRes := emitOrList M constFalse tRes.1 tRes.2
    rcases emitOrList_spec hcf_lt hInvT tRes.2 ht_lt with
      ⟨extO, heqO, hInvO, hor_lt, hextO_len, hnotO, hevalO⟩
    let notRes := emitGate M orRes.1 GateOp.not [orRes.2]
    have hnotRes_inv := emitGate_inv hInvO (op := GateOp.not) (ins := [orRes.2]) (by simp) (by simp only [List.length_cons, List.length_nil]; omega)
      (fun i hi => by cases hi with | head => exact hor_lt | tail _ hi2 => cases hi2)
    have hor_lt_not : orRes.2 < M + notRes.1.length := by
      dsimp [notRes]; rw [hnotRes_inv.2.2]
      exact Nat.lt_succ_of_lt hor_lt
    have hle_not : prev.1.length ≤ notRes.1.length := by
      have h1 : notRes.1.length = orRes.1.length + 1 := hnotRes_inv.2.2
      have h2 : orRes.1.length = tRes.1.length + extO.length := by rw [heqO, List.length_append]
      have h3 : tRes.1.length = prev.1.length + extT.length := by rw [heqT, List.length_append]
      omega
    have hprev_lt_not : ∀ w ∈ prev.2, w < M + notRes.1.length :=
      fun w hw => lt_of_lt_of_le (hw0 w hw) (Nat.add_le_add_left hle_not M)
    rcases emitNextPrefs_spec hnotRes_inv.1 hnotRes_inv.2.1 hor_lt_not prev.2 hprev_lt_not with
      ⟨extP, heqP, hInvP, hlenP, hp_lt, hextP_len, hnotP, hevalP⟩
    have hres_eq : res = emitNextPrefs M notRes.2 orRes.2 notRes.1 prev.2 := rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hres_eq]; exact hInvP
    · rw [hres_eq, hlenP, hlen0, pow_succ']
    · rw [hres_eq]; exact hp_lt
    · rw [hres_eq, heqP, List.length_append, hextP_len, hnotRes_inv.2.2, heqO, List.length_append,
        heqT, List.length_append, hextT_len, hlen0]
      have h1 : 1 ≤ 2 ^ a := Nat.one_le_pow _ _ (by norm_num)
      have h2 : 2 ^ (a + 1) = 2 * 2 ^ a := pow_succ' 2 a
      rw [hlenT, hlen0] at hextO_len
      have hpow1 : 2 ^ (a + 1) - 1 = 2 * (2 ^ a - 1) + 1 := by omega
      have hpow0 : 2 ^ a = (2 ^ a - 1) + 1 := (Nat.sub_add_cancel h1).symm
      rw [hpow1, hpow0] at *
      omega
    · rw [hres_eq, heqP, notCount_append _ extP 0 0, hnotP, Nat.add_zero]
      change notCount { gates := notRes.1, output := 0 } = a + 1
      simp only [notRes, emitGate, notCount_append _ _ 0 0, notCount_singleton_not]
      rw [heqO, notCount_append tRes.1 extO 0 0, hnotO, Nat.add_zero]
      rw [heqT, notCount_append prev.1 extT 0 0, hnotT, Nat.add_zero]
      rw [hnot0]
    · intro s x p hp hu
      have hlen_raw : (rawFn k d s x).length = M := rawFn_length k d s x
      have hcf_raw : (rawFn k d s x).getD constFalse false = false := rawFn_getD_N k d s x

      have hbit_eval : (({ gates := orRes.1, output := 0 } : Circuit).wires (rawFn k d s x)).getD
          orRes.2 false = decide ((s.val / h / 2 ^ j) % 2 = 1) := by
        rw [hevalO hlen_raw hcf_raw]
        have h_any : tRes.2.any (fun w => (({ gates := tRes.1, output := 0 } : Circuit).wires (rawFn k d s x)).getD w false) =
            decide ((s.val / h / 2 ^ j) % 2 = 1) := by
          rw [Bool.eq_iff_iff, List.any_eq_true]
          have hj_succ : m - a = j + 1 := by omega
          let u := s.val / h
          let p0 := u / 2 ^ (j + 1)
          have hp0_lt : p0 < 2 ^ a := by
            dsimp [p0, u]
            rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show a + (j + 1) = m by omega]
            exact hu
          have heval_idx : ∀ idx (hidx : idx < tRes.2.length),
              (({ gates := tRes.1, output := 0 } : Circuit).wires (rawFn k d s x)).getD (tRes.2.getD idx 0) false =
                (decide (p0 = idx) && decide (((2 * idx + 1) * 2 ^ j) * h ≤ s.val)) := by
            intro idx hidx
            rw [hlenT] at hidx
            have ht := hevalT hlen_raw idx hidx
            have hp_prev := heval0 s x idx (by rwa [← hlen0]) hu
            rw [hj_succ] at hp_prev
            rw [ht, hp_prev]
            congr 1
            simp only [Nat.zero_add, headWire]
            split_ifs with hlt_k
            · have hraw := rawFn_getD_lt k d s x ⟨_, hlt_k⟩ 0 (Nat.succ_pos d)
              simp only [Nat.add_zero] at hraw
              rw [hraw]
              simp [Fin.le_def]
            · rw [rawFn_getD_N]
              symm; simp only [decide_eq_false_iff_not, not_le]
              exact lt_of_lt_of_le s.isLt (not_lt.mp hlt_k)
          constructor
          · rintro ⟨w, hw_mem, hw_true⟩
            rcases List.mem_iff_getElem.mp hw_mem with ⟨idx, hidx, rfl⟩
            have h1 := heval_idx idx hidx
            simp only [List.getD_eq_getElem?_getD, hidx, List.getElem?_eq_getElem, Option.getD_some] at h1
            simp only [List.getD_eq_getElem?_getD] at hw_true
            rw [h1] at hw_true
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hw_true
            rcases hw_true with ⟨rfl, hle⟩
            have hle_u : (2 * p0 + 1) * 2 ^ j ≤ u := (Nat.le_div_iff_mul_le hh).mpr hle
            have hdiv_j : u / 2 ^ j = 2 * p0 + (u / 2 ^ j) % 2 := by
              have := Nat.div_add_mod (u / 2 ^ j) 2
              rw [Nat.div_div_eq_div_mul, ← pow_succ] at this
              dsimp only [p0]
              omega
            have hlt_pow : (2 * p0 + 1) * 2 ^ j ≤ u → 2 * p0 + 1 ≤ u / 2 ^ j := by
              intro hle'; exact (Nat.le_div_iff_mul_le (by positivity)).mpr hle'
            have h1' := hlt_pow hle_u
            simp only [decide_eq_true_eq]
            have hmod2 : (u / 2 ^ j) % 2 < 2 := Nat.mod_lt _ (by norm_num)
            have hadd : 2 * p0 + 1 ≤ 2 * p0 + (u / 2 ^ j) % 2 := by
              rw [← hdiv_j]; exact h1'
            exact Nat.le_antisymm (Nat.le_pred_of_lt hmod2) (Nat.le_of_add_le_add_left hadd)
          · intro hbit1
            simp only [decide_eq_true_eq] at hbit1
            refine ⟨tRes.2.getD p0 0, ?_, ?_⟩
            · have hp0_t : p0 < tRes.2.length := by rw [hlenT, hlen0]; exact hp0_lt
              simp [List.getD_eq_getElem?_getD, hp0_t, List.getElem_mem]
            · have h1 := heval_idx p0 (by rw [hlenT, hlen0]; exact hp0_lt)
              rw [h1]
              have hdiv_j : u / 2 ^ j = 2 * p0 + (u / 2 ^ j) % 2 := by
                have := Nat.div_add_mod (u / 2 ^ j) 2
                rw [Nat.div_div_eq_div_mul, ← pow_succ] at this
                dsimp only [p0]
                omega
              have hle_u : (2 * p0 + 1) * 2 ^ j ≤ u := by
                rw [← Nat.le_div_iff_mul_le (by positivity), hdiv_j, hbit1]
              have hle_s : ((2 * p0 + 1) * 2 ^ j) * h ≤ s.val := (Nat.le_div_iff_mul_le hh).mp hle_u
              simp [hle_s]
        exact h_any
      have hnot_eval : (({ gates := notRes.1, output := 0 } : Circuit).wires (rawFn k d s x)).getD
          notRes.2 false = decide ((s.val / h / 2 ^ j) % 2 = 0) := by
        simp only [notRes]
        rw [emitGate_eval hInvO (ins := [orRes.2]) (by simp) (by simp only [List.length_cons, List.length_nil]; omega)
          (fun i hi => by cases hi with | head => exact hor_lt | tail _ hi2 => cases hi2) hlen_raw]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons]
        rw [hbit_eval]
        have hmod2 : (s.val / h / 2 ^ j) % 2 = 0 ∨ (s.val / h / 2 ^ j) % 2 = 1 := by omega
        rcases hmod2 with h0 | h1
        · simp [h0]
        · simp [h1]
      have hbit_eval_not : (({ gates := notRes.1, output := 0 } : Circuit).wires (rawFn k d s x)).getD
          orRes.2 false = decide ((s.val / h / 2 ^ j) % 2 = 1) := by
        simp only [notRes, emitGate]
        rw [wires_append_eq orRes.1 _ 0 0 hlen_raw hor_lt, hbit_eval]
      have hprev_eval_not : ∀ idx (hidx : idx < prev.2.length),
          (({ gates := notRes.1, output := 0 } : Circuit).wires (rawFn k d s x)).getD
            (prev.2.getD idx 0) false = decide ((s.val / h) / 2 ^ (m - a) = idx) := by
        intro idx hidx
        have hw_mem : prev.2.getD idx 0 ∈ prev.2 := by
          simp [List.getD_eq_getElem?_getD, hidx, List.getElem_mem]
        have hw_lt0 := hw0 _ hw_mem
        have heq_not : notRes.1 = prev.1 ++ (extT ++ extO ++ [⟨GateOp.not, [orRes.2]⟩]) := by
          simp only [notRes, emitGate]
          rw [heqO, heqT]
          simp only [List.append_assoc]
          rfl
        rw [heq_not, wires_append_eq prev.1 _ 0 0 hlen_raw hw_lt0]
        exact heval0 s x idx (by rwa [← hlen0]) hu
      rw [hres_eq]
      let idx := p / 2
      have hidx : idx < prev.2.length := by rw [hlen0]; omega
      have hev := hevalP hlen_raw idx hidx
      have hmod2 : p = 2 * idx ∨ p = 2 * idx + 1 := by omega
      have hj_eq : m - (a + 1) = j := by omega
      have hj_succ : m - a = j + 1 := by omega
      have hdiv_step : (s.val / h) / 2 ^ (m - a) = ((s.val / h) / 2 ^ j) / 2 := by
        rw [hj_succ, pow_succ, ← Nat.div_div_eq_div_mul]
      rw [hj_eq]
      rcases hmod2 with hp_even | hp_odd
      · rw [hp_even, hev.1, hprev_eval_not idx hidx, hnot_eval, hdiv_step]
        have : ((s.val / h) / 2 ^ j) = 2 * ((s.val / h / 2 ^ j) / 2) + (s.val / h / 2 ^ j) % 2 := by
          omega
        by_cases h0 : (s.val / h / 2 ^ j) % 2 = 0 <;>
        by_cases h1 : (s.val / h / 2 ^ j) / 2 = idx <;>
        simp [h0, h1] <;> omega
      · rw [hp_odd, hev.2, hprev_eval_not idx hidx, hbit_eval_not, hdiv_step]
        by_cases h0 : (s.val / h / 2 ^ j) % 2 = 1 <;>
        by_cases h1 : (s.val / h / 2 ^ j) / 2 = idx <;>
        simp [h0, h1] <;> omega

def emitMuxTerms (M k d h r_idx v : ℕ) (prefs : List ℕ) (gs : List Gate) :
    List ℕ → List Gate × List ℕ
  | [] => (gs, [])
  | u :: us =>
    let xw := (u * h + r_idx) * (d + 1) + 1 + v
    let res := emitGate M gs GateOp.and [prefs.getD u 0, xw]
    let rest := emitMuxTerms M k d h r_idx v prefs res.1 us
    (rest.1, res.2 :: rest.2)

lemma emitMuxTerms_spec (k d h r_idx v : ℕ) (hv : v < d) (prefs : List ℕ)
    {gs : List Gate} (hInv : CircuitInv (k * (d + 1) + 2) gs)
    (hp_lt : ∀ w ∈ prefs, w < k * (d + 1) + 2 + gs.length)
    (us : List ℕ) (hus : ∀ u ∈ us, u < prefs.length ∧ u * h + r_idx < k) :
    let M := k * (d + 1) + 2
    ∃ ext : List Gate,
      (emitMuxTerms M k d h r_idx v prefs gs us).1 = gs ++ ext ∧
      CircuitInv M (emitMuxTerms M k d h r_idx v prefs gs us).1 ∧
      (emitMuxTerms M k d h r_idx v prefs gs us).2.length = us.length ∧
      (∀ t ∈ (emitMuxTerms M k d h r_idx v prefs gs us).2,
        t < M + (emitMuxTerms M k d h r_idx v prefs gs us).1.length) ∧
      ext.length = us.length ∧
      notCount { gates := ext, output := 0 } = 0 ∧
      ∀ (s : Fin k) (x : Fin d → Bool),
        ((emitMuxTerms M k d h r_idx v prefs gs us).2.any (fun w =>
          (({ gates := (emitMuxTerms M k d h r_idx v prefs gs us).1, output := 0 } : Circuit).wires
            (rawFn k d s x)).getD w false)) =
        (us.any (fun u =>
          ((({ gates := gs, output := 0 } : Circuit).wires (rawFn k d s x)).getD (prefs.getD u 0) false) &&
          ((rawFn k d s x).getD ((u * h + r_idx) * (d + 1) + 1 + v) false))) := by
  intro M
  induction us generalizing gs with
  | nil =>
    refine ⟨[], by simp [emitMuxTerms], hInv, by simp [emitMuxTerms], by simp [emitMuxTerms],
      by simp [emitMuxTerms], rfl, ?_⟩
    intro s x; simp [emitMuxTerms]
  | cons u us ih =>
    have hu := hus u (by simp)
    have hpu_mem : prefs.getD u 0 ∈ prefs := by simp [List.getD_eq_getElem?_getD, hu.1, List.getElem_mem]
    have hpu_lt : prefs.getD u 0 < M + gs.length := hp_lt _ hpu_mem
    let xw := (u * h + r_idx) * (d + 1) + 1 + v
    have hxw_k : xw < k * (d + 1) := by
      calc (u * h + r_idx) * (d + 1) + 1 + v
          < (u * h + r_idx) * (d + 1) + (d + 1) := by omega
        _ = (u * h + r_idx + 1) * (d + 1) := by rw [Nat.succ_mul]
        _ ≤ k * (d + 1) := Nat.mul_le_mul_right _ hu.2
    have hxw_lt : xw < M + gs.length := by omega
    let res := emitGate M gs GateOp.and [prefs.getD u 0, xw]
    have hres_inv := emitGate_inv hInv (op := GateOp.and) (ins := [prefs.getD u 0, xw]) (by simp) (by simp only [List.length_cons, List.length_nil]; omega)
      (fun i hi => by cases hi with | head => exact hpu_lt | tail _ hi2 => cases hi2 with | head => exact hxw_lt | tail _ hi3 => cases hi3)
    rcases ih hres_inv.1 (fun w hw => by have := hp_lt w hw; rw [hres_inv.2.2]; omega)
      (fun u' hu' => hus u' (List.mem_cons_of_mem u hu')) with
      ⟨ext1, heq1, hInv1, hlen_t, ht_lt, hext1_len, hnot1, heval1⟩
    refine ⟨[⟨GateOp.and, [prefs.getD u 0, xw]⟩] ++ ext1, ?_, hInv1,
      by dsimp only [emitMuxTerms]; rw [List.length_cons, hlen_t]; rfl, ?_, by rw [List.singleton_append, List.length_cons, hext1_len]; rfl,
      by rw [notCount_append _ ext1 0 0, notCount_singleton_and, hnot1], ?_⟩
    · simp only [emitMuxTerms, res] at heq1 ⊢
      rw [heq1, List.singleton_append, emitGate, List.append_assoc]; rfl
    · intro t ht
      simp only [emitMuxTerms, List.mem_cons] at ht
      rcases ht with rfl | ht
      · have hlen : gs.length < (emitMuxTerms M k d h r_idx v prefs res.1 us).1.length := by
          rw [heq1, List.length_append, hres_inv.2.2]; omega
        dsimp only [res] at hlen
        change (emitGate M gs GateOp.and [prefs.getD u 0, xw]).2 <
          M + (emitMuxTerms M k d h r_idx v prefs (emitGate M gs GateOp.and [prefs.getD u 0, xw]).1 us).1.length
        dsimp only [emitGate] at hlen ⊢; omega
      · exact ht_lt t ht
    · intro s x
      have hlen_raw : (rawFn k d s x).length = M := rawFn_length k d s x
      simp only [emitMuxTerms, List.any_cons]
      have hhead : (({ gates := (emitMuxTerms M k d h r_idx v prefs res.1 us).1, output := 0 } : Circuit).wires
          (rawFn k d s x)).getD res.2 false =
          ((({ gates := gs, output := 0 } : Circuit).wires (rawFn k d s x)).getD (prefs.getD u 0) false &&
          (rawFn k d s x).getD xw false) := by
        change (({ gates := (emitMuxTerms M k d h r_idx v prefs res.1 us).1, output := 0 } : Circuit).wires
          (rawFn k d s x)).getD res.2 false = _
        rw [heq1, wires_append_eq res.1 ext1 0 0 hlen_raw hres_inv.2.1]
        rw [emitGate_eval hInv (ins := [prefs.getD u 0, xw]) (by simp) (by simp only [List.length_cons, List.length_nil]; omega)
          (fun i hi => by cases hi with | head => exact hpu_lt | tail _ hi2 => cases hi2 with | head => exact hxw_lt | tail _ hi3 => cases hi3) hlen_raw]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
        congr 1
        rw [wires_getD_prefix _ _ 0 xw (by rw [hlen_raw]; omega)]
        simp [wiresPrefix]
      have htail := heval1 s x
      rw [hhead, htail]
      congr 1
      rw [Bool.eq_iff_iff]
      simp only [List.any_eq_true]
      constructor
      · rintro ⟨u', hu', hval⟩
        have hu'' := hus u' (List.mem_cons_of_mem u hu')
        have hpu' : prefs.getD u' 0 ∈ prefs := by
          simp [List.getD_eq_getElem?_getD, hu''.1, List.getElem_mem]
        simp only [res, emitGate] at hval
        rw [wires_append_eq gs _ 0 0 hlen_raw (hp_lt _ hpu')] at hval
        exact ⟨u', hu', hval⟩
      · rintro ⟨u', hu', hval⟩
        have hu'' := hus u' (List.mem_cons_of_mem u hu')
        have hpu' : prefs.getD u' 0 ∈ prefs := by
          simp [List.getD_eq_getElem?_getD, hu''.1, List.getElem_mem]
        refine ⟨u', hu', ?_⟩
        simp only [res, emitGate]
        rwa [wires_append_eq gs _ 0 0 hlen_raw (hp_lt _ hpu')]

def emitAllMux (M k d Q h : ℕ) (prefs : List ℕ) (gs : List Gate) (muxMap : ℕ × ℕ → ℕ) :
    List (ℕ × ℕ) → List Gate × (ℕ × ℕ → ℕ)
  | [] => (gs, muxMap)
  | (r_idx, v) :: rest =>
    let us := (List.range Q).filter (fun u => u * h + r_idx < k)
    let tRes := emitMuxTerms M k d h r_idx v prefs gs us
    let oRes := emitOrList M (k * (d + 1)) tRes.1 tRes.2
    let muxMap' : ℕ × ℕ → ℕ := fun p => if p = (r_idx, v) then oRes.2 else muxMap p
    emitAllMux M k d Q h prefs oRes.1 muxMap' rest

def emitAllEdges (M : ℕ) (muxMap : ℕ × ℕ → ℕ) (gs : List Gate) (tapMap : ℕ × (Fin d × Fin d) → ℕ) :
    List (ℕ × (Fin d × Fin d)) → List Gate × (ℕ × (Fin d × Fin d) → ℕ)
  | [] => (gs, tapMap)
  | (r_idx, z) :: rest =>
    let res := emitGate M gs GateOp.and [muxMap (r_idx, z.1.val), muxMap (r_idx, z.2.val)]
    let tapMap' : ℕ × (Fin d × Fin d) → ℕ := fun p => if p = (r_idx, z) then res.2 else tapMap p
    emitAllEdges M muxMap res.1 tapMap' rest

lemma upper_bound_exists (k d r : ℕ) (E : Finset (Fin d × Fin d)) (hk : 0 < k) (hd : 2 ≤ d) :
    let N := k * (d + 1)
    let q := 2 ^ r
    ∃ (C : Circuit) (tap : Fin k → {z : Fin d × Fin d // z ∈ E} → ℕ),
      FanInTwo C ∧ ReadsBack (N + 2) C ∧ C.output < N + 2 + C.size ∧
      (∀ s z, tap s z < N + 2 + C.size) ∧
      (∀ s x z, (C.wires (rawFn k d s x)).getD (tap s z) false = (x z.val.1 && x z.val.2)) ∧
      notCount C ≤ r ∧
      C.size - notCount C ≤ ((k + q - 1) / q) * E.card + 8 * k * d := by
  intro N q
  let M := N + 2
  let m := min r (Nat.clog 2 k)
  let Q := 2 ^ m
  let h := (k + Q - 1) / Q
  have hm_r : m ≤ r := min_le_left r _
  have hQ_pos : 0 < Q := by positivity
  have hh_pos : 0 < h := Nat.div_pos (by omega) hQ_pos
  have hk_le_Qh : k ≤ Q * h := by
    have hdiv := Nat.div_add_mod (k + Q - 1) Q
    change Q * h + (k + Q - 1) % Q = k + Q - 1 at hdiv
    have hmod : (k + Q - 1) % Q < Q := Nat.mod_lt _ hQ_pos
    omega
  have hQh_le_2k : Q * h ≤ 2 * k := by
    by_cases hr : r < Nat.clog 2 k
    · have hm_eq : m = r := min_eq_left (le_of_lt hr)
      have hQk : Q < k := by
        rw [show Q = 2 ^ m from rfl, hm_eq]
        exact Nat.pow_lt_of_lt_clog hr
      have hle : Q * h ≤ k + Q - 1 := Nat.mul_div_le (k + Q - 1) Q
      omega
    · have hclog : Nat.clog 2 k ≤ r := not_lt.mp hr
      have hm_eq : m = Nat.clog 2 k := min_eq_right hclog
      have hkQ : k ≤ Q := by
        rw [show Q = 2 ^ m from rfl, hm_eq]
        exact Nat.le_pow_clog (by norm_num) k
      have hh1 : h = 1 := by
        dsimp [h]
        have h1 : 1 * Q ≤ k + Q - 1 := by omega
        have h2 : k + Q - 1 < 2 * Q := by omega
        exact Nat.div_eq_of_lt_le h1 (by simpa [Nat.mul_comm] using h2)
      rw [hh1, Nat.mul_one]
      by_cases hk1 : k = 1
      · subst hk1; simp [Q, hm_eq]
      · have hm_pos : 0 < m := by
          rw [hm_eq]; exact Nat.clog_pos (by norm_num) (by omega)
        have hhalf : 2 ^ (m - 1) < k := by
          apply Nat.pow_lt_of_lt_clog
          rw [← hm_eq]; omega
        have hQ2 : Q = 2 * 2 ^ (m - 1) := by
          rw [show Q = 2 ^ m from rfl, ← pow_succ', Nat.sub_add_cancel hm_pos]
        omega
  have hh_eq : h = (k + q - 1) / q := by
    by_cases hr : r < Nat.clog 2 k
    · simp [h, Q, m, min_eq_left (le_of_lt hr), q]
    · have hclog : Nat.clog 2 k ≤ r := not_lt.mp hr
      have hkQ : k ≤ Q := by
        dsimp [Q, m]; rw [min_eq_right hclog]
        exact Nat.le_pow_clog (by norm_num) k
      have hkq : k ≤ q := le_trans hkQ (Nat.pow_le_pow_right (by norm_num) hm_r)
      have h1 : h = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
      have h2 : (k + q - 1) / q = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
      rw [h1, h2]

  let constFalse := N
  let constTrue := N + 1
  let headWire : ℕ → ℕ := fun t => if t < k then t * (d + 1) else constFalse
  let prefRes := buildPrefixes M constFalse constTrue h m headWire m
  have hpref_spec := buildPrefixes_spec k d m h hk hh_pos m le_rfl
  dsimp only at hpref_spec
  rcases hpref_spec with ⟨hInvP, hlenP, hwP, hszP, hnotP, hevalP⟩

  let pairsRV := (List.range h).flatMap (fun r_idx => (List.range d).map (fun v => (r_idx, v)))
  have hpairs_nodup : pairsRV.Nodup := by
    rw [List.nodup_flatMap]
    refine ⟨?_, ?_⟩
    · intro r_idx _
      exact List.Nodup.map (fun v1 v2 heq => by simpa using heq) List.nodup_range
    · exact List.nodup_range.imp (fun {r1 r2} hne => by
        simp only [List.disjoint_left, List.mem_map]
        rintro ⟨a, b⟩ ⟨v1, _, h1⟩ ⟨v2, _, h2⟩
        rcases Prod.mk.inj h1 with ⟨rfl, _⟩
        rcases Prod.mk.inj h2 with ⟨h_eq, _⟩
        exact hne h_eq.symm)
  have hpairs_mem : ∀ r_idx v, (r_idx, v) ∈ pairsRV ↔ r_idx < h ∧ v < d := by
    intro r_idx v
    simp [pairsRV, eq_comm]
  have hmux_lemma : ∀ (L : List (ℕ × ℕ)), L.Nodup → (∀ p ∈ L, p.1 < h ∧ p.2 < d) →
      ∀ (gs : List Gate) (muxMap : ℕ × ℕ → ℕ),
        CircuitInv M gs →
        (∀ w ∈ prefRes.2, w < M + gs.length) →
        (∀ (s : Fin k) (x : Fin d → Bool) (u : ℕ), u < prefRes.2.length →
          (({ gates := gs, output := 0 } : Circuit).wires (rawFn k d s x)).getD
            (prefRes.2.getD u 0) false = decide (u = s.val / h)) →
        ∃ ext : List Gate,
          (emitAllMux M k d Q h prefRes.2 gs muxMap L).1 = gs ++ ext ∧
          CircuitInv M (emitAllMux M k d Q h prefRes.2 gs muxMap L).1 ∧
          notCount { gates := ext, output := 0 } = 0 ∧
          ext.length ≤ 2 * (L.map (fun p => ((List.range Q).filter (fun u => u * h + p.1 < k)).length)).sum ∧
          (∀ p ∈ L, (emitAllMux M k d Q h prefRes.2 gs muxMap L).2 p <
            M + (emitAllMux M k d Q h prefRes.2 gs muxMap L).1.length) ∧
          (∀ p ∉ L, (emitAllMux M k d Q h prefRes.2 gs muxMap L).2 p = muxMap p) ∧
          (∀ (s : Fin k) (x : Fin d → Bool) (v : Fin d), (s.val % h, v.val) ∈ L →
            (({ gates := (emitAllMux M k d Q h prefRes.2 gs muxMap L).1, output := 0 } : Circuit).wires
              (rawFn k d s x)).getD
              ((emitAllMux M k d Q h prefRes.2 gs muxMap L).2 (s.val % h, v.val)) false = x v) := by
    intro L hnodup hmemL
    induction L with
    | nil =>
      intro gs muxMap hInv hpw hpe
      refine ⟨[], by simp [emitAllMux], hInv, rfl, by simp,
        by simp, by simp [emitAllMux], by simp⟩
    | cons p rest ih =>
      intro gs muxMap hInv hpw hpe
      have hp_b := hmemL p (by simp)
      have hnodup_rest := (List.nodup_cons.mp hnodup).2
      have hp_notin : p ∉ rest := (List.nodup_cons.mp hnodup).1
      let us := (List.range Q).filter (fun u => u * h + p.1 < k)
      let tRes := emitMuxTerms M k d h p.1 p.2 prefRes.2 gs us
      have hus : ∀ u ∈ us, u < prefRes.2.length ∧ u * h + p.1 < k := by
        intro u hu
        simp only [us, List.mem_filter, List.mem_range, decide_eq_true_eq] at hu
        rw [hlenP]; exact hu
      rcases emitMuxTerms_spec k d h p.1 p.2 hp_b.2 prefRes.2 hInv hpw us hus with
        ⟨extT, heqT, hInvT, hlenT, ht_lt, hextT_len, hnotT, hevalT⟩
      let oRes := emitOrList M constFalse tRes.1 tRes.2
      rcases emitOrList_spec (by omega : constFalse < M) hInvT tRes.2 ht_lt with
        ⟨extO, heqO, hInvO, hor_lt, hextO_len, hnotO, hevalO⟩
      let muxMap' : ℕ × ℕ → ℕ := fun q' => if q' = p then oRes.2 else muxMap q'
      have hpw_O : ∀ w ∈ prefRes.2, w < M + oRes.1.length := by
        intro w hw
        have := hpw w hw
        have : gs.length ≤ oRes.1.length := by rw [heqO, List.length_append, heqT, List.length_append]; omega
        omega
      have hpe_O : ∀ (s : Fin k) (x : Fin d → Bool) (u : ℕ), u < prefRes.2.length →
          (({ gates := oRes.1, output := 0 } : Circuit).wires (rawFn k d s x)).getD
            (prefRes.2.getD u 0) false = decide (u = s.val / h) := by
        intro s x u hu
        have hmem_u : prefRes.2.getD u 0 ∈ prefRes.2 := by
          simp [List.getD_eq_getElem?_getD, hu, List.getElem_mem]
        have heq_o : oRes.1 = gs ++ (extT ++ extO) := by rw [heqO, heqT, List.append_assoc]
        rw [heq_o, wires_append_eq gs _ 0 0 (rawFn_length k d s x) (hpw _ hmem_u)]
        exact hpe s x u hu
      rcases ih hnodup_rest (fun q' hq' => hmemL q' (by simp [hq'])) oRes.1 muxMap' hInvO hpw_O hpe_O with
        ⟨extR, heqR, hInvR, hnotR, hlenR, hltR, hsameR, hevalR⟩
      have hstep_eq : emitAllMux M k d Q h prefRes.2 gs muxMap (p :: rest) =
          emitAllMux M k d Q h prefRes.2 oRes.1 muxMap' rest := rfl
      refine ⟨extT ++ extO ++ extR, ?_, hInvR, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hstep_eq, heqR, heqO, heqT]; simp only [List.append_assoc]
      · rw [notCount_append, notCount_append, hnotT, hnotO, hnotR]
      · rw [List.length_append, List.length_append, hextT_len]
        simp only [List.map_cons, List.sum_cons]
        rw [hlenT] at hextO_len
        change extO.length ≤ us.length at hextO_len
        have hus_eq : us.length = (List.filter (fun u => decide (u * h + p.1 < k)) (List.range Q)).length := rfl
        rw [hus_eq] at hextO_len
        have hT_eq : ((List.range Q).filter (fun u => u * h + p.1 < k)).length =
            (List.filter (fun u => decide (u * h + p.1 < k)) (List.range Q)).length := rfl
        rw [hT_eq]
        omega
      · intro q' hq'
        simp only [List.mem_cons] at hq'
        rcases hq' with hqp | hq'
        · rw [hqp, hstep_eq, hsameR p hp_notin]
          dsimp [muxMap']; simp only [↓reduceIte]
          have hle_R : oRes.1.length ≤ (emitAllMux M k d Q h prefRes.2 oRes.1 muxMap' rest).1.length := by
            rw [heqR, List.length_append]; omega
          exact lt_of_lt_of_le hor_lt (Nat.add_le_add_left hle_R M)
        · exact hltR q' hq'
      · intro q' hq'
        simp only [List.mem_cons, not_or] at hq'
        rw [hstep_eq, hsameR q' hq'.2]
        dsimp [muxMap']; simp [hq'.1]
      · intro s x v hsv
        simp only [List.mem_cons] at hsv
        rcases hsv with heq_sv | hsv_rest
        · rw [hstep_eq, hsameR _ (by rwa [← heq_sv] at hp_notin)]
          have hmux_val : muxMap' (s.val % h, v.val) = oRes.2 := by
            dsimp [muxMap']; simp [heq_sv]
          rw [hmux_val]
          have hlen_raw : (rawFn k d s x).length = M := rawFn_length k d s x
          have hcf_raw : (rawFn k d s x).getD constFalse false = false := rawFn_getD_N k d s x
          have heq_full : (emitAllMux M k d Q h prefRes.2 oRes.1 muxMap' rest).1 = oRes.1 ++ extR := heqR
          rw [heq_full, wires_append_eq oRes.1 extR 0 0 hlen_raw hor_lt]
          rw [hevalO hlen_raw hcf_raw, hevalT s x]
          have hu_s : s.val / h < Q := (Nat.div_lt_iff_lt_mul hh_pos).mpr (lt_of_lt_of_le s.isLt hk_le_Qh)
          have hr_eq : p.1 = s.val % h := (congrArg Prod.fst heq_sv).symm
          have hv_eq : p.2 = v.val := (congrArg Prod.snd heq_sv).symm
          have hus_mem : s.val / h ∈ us := by
            simp only [us, List.mem_filter, List.mem_range, decide_eq_true_eq]
            refine ⟨hu_s, ?_⟩
            rw [hr_eq, Nat.mul_comm (s.val / h) h]
            exact lt_of_eq_of_lt (Nat.div_add_mod s.val h) s.isLt
          have h_any : us.any (fun u =>
              ((({ gates := gs, output := 0 } : Circuit).wires (rawFn k d s x)).getD (prefRes.2.getD u 0) false) &&
              ((rawFn k d s x).getD ((u * h + p.1) * (d + 1) + 1 + p.2) false)) = x v := by
            have heq_s : (s.val / h) * h + p.1 = s.val := by
              rw [hr_eq, Nat.mul_comm (s.val / h) h]; exact Nat.div_add_mod s.val h
            have hx_val : (rawFn k d s x).getD ((s.val / h * h + p.1) * (d + 1) + 1 + p.2) false = x v := by
              rw [heq_s, hv_eq, show s.val * (d + 1) + 1 + v.val = s.val * (d + 1) + (v.val + 1) by omega]
              rw [rawFn_getD_lt k d s x s (v.val + 1) (by omega)]
              simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceDIte, lt_self_iff_false,
                decide_false, Bool.false_or, decide_true, Bool.true_and, Nat.add_sub_cancel]
            cases hv_val : x v
            · simp only [List.any_eq_false, Bool.and_eq_true, not_and]
              intro u hu hpref_true
              have hu_len : u < prefRes.2.length := (hus u hu).1
              rw [hpe s x u hu_len] at hpref_true
              simp only [decide_eq_true_eq] at hpref_true
              subst hpref_true
              rw [hx_val, hv_val]
              decide
            · simp only [List.any_eq_true]
              refine ⟨s.val / h, hus_mem, ?_⟩
              have hu_len : s.val / h < prefRes.2.length := (hus _ hus_mem).1
              rw [hpe s x (s.val / h) hu_len, hx_val, hv_val]
              simp
          exact h_any
        · exact hevalR s x v hsv_rest
  have hpe_init : ∀ (s : Fin k) (x : Fin d → Bool) (u : ℕ), u < prefRes.2.length →
      (({ gates := prefRes.1, output := 0 } : Circuit).wires (rawFn k d s x)).getD
        (prefRes.2.getD u 0) false = decide (u = s.val / h) := by
    intro s x u hu
    rw [hlenP] at hu
    have hu_s : s.val / h < 2 ^ m := (Nat.div_lt_iff_lt_mul hh_pos).mpr (lt_of_lt_of_le s.isLt hk_le_Qh)
    rw [hevalP s x u hu hu_s, Nat.sub_self, pow_zero, Nat.div_one]
    simp [eq_comm]
  rcases hmux_lemma pairsRV hpairs_nodup (fun p hp => (hpairs_mem p.1 p.2).mp hp)
    prefRes.1 (fun _ => 0) hInvP hwP hpe_init with
    ⟨extM, heqM, hInvM, hnotM, hlenM, hmux_lt, _, hevalM⟩
  let muxRes := emitAllMux M k d Q h prefRes.2 prefRes.1 (fun _ => 0) pairsRV

  have hsum_us : (pairsRV.map (fun p => ((List.range Q).filter (fun u => u * h + p.1 < k)).length)).sum ≤ k * d := by
    have hflat : (pairsRV.map (fun p => ((List.range Q).filter (fun u => u * h + p.1 < k)).length)).sum =
        d * ((List.range h).map (fun r_idx => ((List.range Q).filter (fun u => u * h + r_idx < k)).length)).sum := by
      dsimp [pairsRV]
      have hsum_flat : ∀ (L : List ℕ) (f : ℕ → List ℕ), (L.flatMap f).sum = (L.map (fun a => (f a).sum)).sum := by
        intro L f; induction L with | nil => rfl | cons a as ih => simp [List.flatMap_cons, List.sum_append, ih]
      rw [List.map_flatMap, hsum_flat]
      have hconst : ∀ r_idx ∈ List.range h,
          ((List.range d).map (fun v => ((List.range Q).filter (fun u => u * h + r_idx < k)).length)).sum =
          d * ((List.range Q).filter (fun u => u * h + r_idx < k)).length := by
        intro r_idx _
        simp [List.map_const', List.sum_replicate, smul_eq_mul]
      conv_lhs =>
        arg 1
        simp only [List.map_map, Function.comp_def]
        rw [List.map_congr_left hconst]
      rw [← List.sum_map_mul_left]
    have hsum_h : ((List.range h).map (fun r_idx => ((List.range Q).filter (fun u => u * h + r_idx < k)).length)).sum ≤ k := by
      have hgen : ∀ (R : List ℕ), R.Nodup → (∀ r_idx ∈ R, r_idx < h) →
          (R.map (fun r_idx => ((List.range Q).filter (fun u => u * h + r_idx < k)).length)).sum ≤
          ((Finset.range k).filter (fun s => s % h ∈ R)).card := by
        intro R
        induction R with
        | nil => intro _ _; simp
        | cons r_idx rest ih =>
          intro hnodup hr_lt
          have hnodup_rest := (List.nodup_cons.mp hnodup).2
          have hr_notin : r_idx ∉ rest := (List.nodup_cons.mp hnodup).1
          have hr_h := hr_lt r_idx (by simp)
          have ih_rest := ih hnodup_rest (fun r' hr' => hr_lt r' (by simp [hr']))
          let A := (Finset.range k).filter (fun s => s % h = r_idx)
          let B := (Finset.range k).filter (fun s => s % h ∈ rest)
          have hdisj : Disjoint A B := by
            rw [Finset.disjoint_filter]
            intro s _ ha hb
            rw [ha] at hb
            exact hr_notin hb
          have hsub : A ∪ B ⊆ (Finset.range k).filter (fun s => s % h ∈ r_idx :: rest) := by
            intro s hs
            simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_range, List.mem_cons] at hs ⊢
            rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact ⟨h1, Or.inl h2⟩
            · exact ⟨h1, Or.inr h2⟩
          have hcard_r : ((List.range Q).filter (fun u => u * h + r_idx < k)).length ≤ A.card := by
            have hfin_len : ((List.range Q).filter (fun u => u * h + r_idx < k)).length =
                ((Finset.range Q).filter (fun u => u * h + r_idx < k)).card := by
              simpa using (finset_range_filter_card Q (fun u => decide (u * h + r_idx < k))).symm
            rw [hfin_len]
            apply Finset.card_le_card_of_injOn (fun u => u * h + r_idx)
            · intro u hu
              simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hu
              simp only [A, Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
              exact ⟨hu.2, by rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hr_h]⟩
            · intro u₁ _ u₂ _ heq
              dsimp only at heq
              exact Nat.eq_of_mul_eq_mul_right hh_pos (Nat.add_right_cancel heq)
          simp only [List.map_cons, List.sum_cons]
          have hcard_ab := Finset.card_le_card hsub
          rw [Finset.card_union_of_disjoint hdisj] at hcard_ab
          change _ ≤ B.card at ih_rest
          omega
      exact le_trans (hgen (List.range h) List.nodup_range (fun r_idx hr => List.mem_range.mp hr))
        (le_trans (Finset.card_filter_le _ _) (by simp))
    rw [hflat, Nat.mul_comm]
    exact Nat.mul_le_mul_right d hsum_h

  let pairsRE := (List.range h).flatMap (fun r_idx => E.toList.map (fun z => (r_idx, z)))
  have hpairsRE_nodup : pairsRE.Nodup := by
    rw [List.nodup_flatMap]
    refine ⟨?_, ?_⟩
    · intro r_idx _
      exact List.Nodup.map (fun z1 z2 heq => by simpa using heq) (Finset.nodup_toList E)
    · exact List.nodup_range.imp (fun {r1 r2} hne => by
        simp only [List.disjoint_left, List.mem_map]
        rintro ⟨a, b⟩ ⟨z1, _, h1⟩ ⟨z2, _, h2⟩
        rcases Prod.mk.inj h1 with ⟨rfl, _⟩
        rcases Prod.mk.inj h2 with ⟨h_eq, _⟩
        exact hne h_eq.symm)
  have hpairsRE_mem : ∀ r_idx z, (r_idx, z) ∈ pairsRE ↔ r_idx < h ∧ z ∈ E := by
    intro r_idx z
    simp [pairsRE, Finset.mem_toList, eq_comm]
  have hpairsRE_len : pairsRE.length = h * E.card := by
    simp [pairsRE, List.length_flatMap, List.map_const', List.sum_replicate, smul_eq_mul,
      Finset.length_toList]
  have hedges_lemma : ∀ (L : List (ℕ × (Fin d × Fin d))), L.Nodup → (∀ p ∈ L, p.1 < h) →
      ∀ (gs : List Gate) (tapMap : ℕ × (Fin d × Fin d) → ℕ),
        CircuitInv M gs →
        (∀ r_idx v, r_idx < h → v < d → muxRes.2 (r_idx, v) < M + gs.length) →
        (∀ (s : Fin k) (x : Fin d → Bool) (v : Fin d),
          (({ gates := gs, output := 0 } : Circuit).wires (rawFn k d s x)).getD
            (muxRes.2 (s.val % h, v.val)) false = x v) →
        ∃ ext : List Gate,
          (emitAllEdges M muxRes.2 gs tapMap L).1 = gs ++ ext ∧
          CircuitInv M (emitAllEdges M muxRes.2 gs tapMap L).1 ∧
          notCount { gates := ext, output := 0 } = 0 ∧
          ext.length = L.length ∧
          (∀ p ∈ L, (emitAllEdges M muxRes.2 gs tapMap L).2 p <
            M + (emitAllEdges M muxRes.2 gs tapMap L).1.length) ∧
          (∀ p ∉ L, (emitAllEdges M muxRes.2 gs tapMap L).2 p = tapMap p) ∧
          (∀ (s : Fin k) (x : Fin d → Bool) (z : Fin d × Fin d),
            (s.val % h, z) ∈ L →
            (({ gates := (emitAllEdges M muxRes.2 gs tapMap L).1, output := 0 } : Circuit).wires
              (rawFn k d s x)).getD
              ((emitAllEdges M muxRes.2 gs tapMap L).2 (s.val % h, z)) false = (x z.1 && x z.2)) := by
    intro L hnodup hmemL
    induction L with
    | nil =>
      intro gs tapMap hInv _ _
      refine ⟨[], by simp [emitAllEdges], hInv, rfl, by simp,
        by simp, by simp [emitAllEdges], by simp [emitAllEdges]⟩
    | cons p rest ih =>
      intro gs tapMap hInv hmux_b hmux_ev
      have hp_b := hmemL p (by simp)
      have hnodup_rest := (List.nodup_cons.mp hnodup).2
      have hp_notin : p ∉ rest := (List.nodup_cons.mp hnodup).1
      let res := emitGate M gs GateOp.and [muxRes.2 (p.1, p.2.1.val), muxRes.2 (p.1, p.2.2.val)]
      have hres_inv := emitGate_inv hInv (op := GateOp.and)
        (ins := [muxRes.2 (p.1, p.2.1.val), muxRes.2 (p.1, p.2.2.val)])
        (by simp) (by simp only [List.length_cons, List.length_nil]; omega)
        (fun i hi => by
          cases hi with
          | head => exact hmux_b p.1 p.2.1.val hp_b p.2.1.isLt
          | tail _ hi2 => cases hi2 with
            | head => exact hmux_b p.1 p.2.2.val hp_b p.2.2.isLt
            | tail _ hi3 => cases hi3)
      let tapMap' : ℕ × (Fin d × Fin d) → ℕ := fun q' => if q' = p then res.2 else tapMap q'
      have hmux_b' : ∀ r_idx v, r_idx < h → v < d → muxRes.2 (r_idx, v) < M + res.1.length := by
        intro r_idx v hr hv; rw [hres_inv.2.2]; have := hmux_b r_idx v hr hv; omega
      have hmux_ev' : ∀ (s : Fin k) (x : Fin d → Bool) (v : Fin d),
          (({ gates := res.1, output := 0 } : Circuit).wires (rawFn k d s x)).getD
            (muxRes.2 (s.val % h, v.val)) false = x v := by
        intro s x v
        simp only [res, emitGate]
        rw [wires_append_eq gs _ 0 0 (rawFn_length k d s x) (hmux_b _ _ (Nat.mod_lt _ hh_pos) v.isLt)]
        exact hmux_ev s x v
      rcases ih hnodup_rest (fun q' hq' => hmemL q' (by simp [hq'])) res.1 tapMap'
        hres_inv.1 hmux_b' hmux_ev' with
        ⟨extR, heqR, hInvR, hnotR, hlenR, hltR, hsameR, hevalR⟩
      have hstep_eq : emitAllEdges M muxRes.2 gs tapMap (p :: rest) =
          emitAllEdges M muxRes.2 res.1 tapMap' rest := rfl
      refine ⟨[⟨GateOp.and, [muxRes.2 (p.1, p.2.1.val), muxRes.2 (p.1, p.2.2.val)]⟩] ++ extR,
        ?_, hInvR, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hstep_eq, heqR]; simp [res, emitGate, List.append_assoc]
      · rw [notCount_append _ _ 0 0, notCount_singleton_and, hnotR]
      · simp [hlenR]
      · intro q' hq'
        simp only [List.mem_cons] at hq'
        rcases hq' with hqp | hq'
        · rw [hqp, hstep_eq, hsameR p hp_notin]
          have h1 : tapMap' p = res.2 := by dsimp [tapMap']; simp
          have h2 : res.2 < M + res.1.length := hres_inv.2.1
          have h3 : res.1.length ≤ (emitAllEdges M muxRes.2 res.1 tapMap' rest).1.length := by
            rw [heqR, List.length_append]; omega
          rw [h1]
          exact lt_of_lt_of_le h2 (Nat.add_le_add_left h3 M)
        · exact hltR q' hq'
      · intro q' hq'
        simp only [List.mem_cons, not_or] at hq'
        rw [hstep_eq, hsameR q' hq'.2]
        dsimp [tapMap']; simp [hq'.1]
      · intro s x z hz
        simp only [List.mem_cons] at hz
        rcases hz with heq_sz | hz_rest
        · rw [hstep_eq, hsameR _ (by rwa [← heq_sz] at hp_notin)]
          have htap_val : tapMap' (s.val % h, z) = res.2 := by dsimp [tapMap']; simp [heq_sz]
          rw [htap_val]
          have hlen_raw : (rawFn k d s x).length = M := rawFn_length k d s x
          rw [heqR, wires_append_eq res.1 extR 0 0 hlen_raw hres_inv.2.1]
          rw [emitGate_eval hInv (by simp) (by simp only [List.length_cons, List.length_nil]; omega) (fun i hi => by
            simp at hi; rcases hi with rfl | rfl
            · exact hmux_b p.1 p.2.1.val hp_b p.2.1.isLt
            · exact hmux_b p.1 p.2.2.val hp_b p.2.2.isLt) hlen_raw]
          have hp1 : p.1 = s.val % h := (congrArg Prod.fst heq_sz).symm
          have hp2 : p.2 = z := (congrArg Prod.snd heq_sz).symm
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          rw [hp1, hp2, hmux_ev s x z.1, hmux_ev s x z.2]
        · exact hevalR s x z hz_rest
  rcases hedges_lemma pairsRE hpairsRE_nodup (fun p hp => (hpairsRE_mem p.1 p.2).mp hp |>.1)
    muxRes.1 (fun _ => 0) hInvM
    (fun r_idx v hr hv => hmux_lt (r_idx, v) ((hpairs_mem r_idx v).mpr ⟨hr, hv⟩))
    (fun s x v => hevalM s x v ((hpairs_mem _ _).mpr ⟨Nat.mod_lt _ hh_pos, v.isLt⟩)) with
    ⟨extE, heqE, hInvE, hnotE, hlenE, hltE, _, hevalE⟩
  let finalRes := emitAllEdges M muxRes.2 muxRes.1 (fun _ => 0) pairsRE
  let C_final : Circuit := { gates := finalRes.1, output := constFalse }
  let tap_final : Fin k → {z : Fin d × Fin d // z ∈ E} → ℕ := fun s z => finalRes.2 (s.val % h, z.1)
  refine ⟨C_final, tap_final, hInvE.1, hInvE.2, by simp [C_final]; omega, ?_, ?_, ?_, ?_⟩
  · intro s z
    exact hltE _ ((hpairsRE_mem _ _).mpr ⟨Nat.mod_lt _ hh_pos, z.2⟩)
  · intro s x z
    exact hevalE s x z.1 ((hpairsRE_mem _ _).mpr ⟨Nat.mod_lt _ hh_pos, z.2⟩)
  · change notCount { gates := finalRes.1, output := constFalse } ≤ r
    have hnot_eq : notCount { gates := finalRes.1, output := constFalse } =
        notCount { gates := finalRes.1, output := 0 } := rfl
    rw [hnot_eq, heqE, notCount_append _ extE 0 0, hnotE, Nat.add_zero]
    change notCount { gates := muxRes.1, output := 0 } ≤ r
    rw [heqM, notCount_append _ extM 0 0, hnotM, Nat.add_zero, hnotP]
    exact hm_r
  · have hnot_eq : notCount C_final = m := by
      have h1 : notCount C_final = notCount { gates := finalRes.1, output := 0 } := by simp [C_final, notCount]
      rw [h1, heqE, notCount_append _ extE 0 0, hnotE, Nat.add_zero]
      change notCount { gates := muxRes.1, output := 0 } = m
      rw [heqM, notCount_append _ extM 0 0, hnotM, Nat.add_zero, hnotP]
    have hsz_eq : C_final.size = finalRes.1.length := rfl
    rw [hsz_eq, hnot_eq, heqE, List.length_append, hlenE, hpairsRE_len]
    change (muxRes.1.length + h * E.card) - m ≤ ((k + q - 1) / q) * E.card + 8 * k * d
    rw [heqM, List.length_append, ← hh_eq]
    have hM_2kd : extM.length ≤ 2 * (k * d) := le_trans hlenM (Nat.mul_le_mul_left 2 hsum_us)
    have hpref_sub : prefRes.1.length - m ≤ 4 * Q := by
      have hsz' : prefRes.1.length ≤ 4 * (2 ^ m - 1) + m := hszP
      have h4Q : 4 * (2 ^ m - 1) ≤ 4 * Q := by dsimp [Q]; omega
      omega
    have hm_le_pref : m ≤ prefRes.1.length := by
      rw [← hnotP]
      exact List.length_filter_le _ _
    have h8k : 4 * Q + 2 * (k * d) ≤ 8 * k * d := by
      have hQ_le_2k : Q ≤ 2 * k := by
        have h1 : Q ≤ Q * h := Nat.le_mul_of_pos_right Q hh_pos
        exact le_trans h1 hQh_le_2k
      have hkd : 4 * Q ≤ 4 * (2 * k) := Nat.mul_le_mul_left 4 hQ_le_2k
      have h8k_kd : 8 * k ≤ 4 * k * d := by
        calc 8 * k = 4 * k * 2 := by ring
          _ ≤ 4 * k * d := Nat.mul_le_mul_left (4 * k) hd
      calc 4 * Q + 2 * (k * d)
          ≤ 4 * (2 * k) + 2 * (k * d) := Nat.add_le_add_right hkd _
        _ = 8 * k + 2 * (k * d) := by ring
        _ ≤ 4 * k * d + 2 * (k * d) := Nat.add_le_add_right h8k_kd _
        _ = 6 * k * d := by ring
        _ ≤ 8 * k * d := by
          have : 6 * (k * d) ≤ 8 * (k * d) := Nat.mul_le_mul_right (k * d) (by norm_num)
          simpa [Nat.mul_assoc] using this
    have h_split : (prefRes.1.length + extM.length + h * E.card) - m =
        (prefRes.1.length - m) + (extM.length + h * E.card) := by
      have h1 : (prefRes.1.length - m) + m = prefRes.1.length := Nat.sub_add_cancel hm_le_pref
      omega
    rw [h_split]
    calc (prefRes.1.length - m) + (extM.length + h * E.card)
        ≤ 4 * Q + (2 * (k * d) + h * E.card) := Nat.add_le_add hpref_sub (Nat.add_le_add_right hM_2kd _)
      _ = (4 * Q + 2 * (k * d)) + h * E.card := by omega
      _ ≤ 8 * k * d + h * E.card := Nat.add_le_add_right h8k _
      _ = h * E.card + 8 * k * d := Nat.add_comm _ _

end PEqualNP.Outside.L_lib_1333

theorem PEqualNP.Outside.L_lib_1333 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (k d r : Nat) (E : Finset (Fin d × Fin d)), 0 < k → 2 ≤ d →
  (∀ z ∈ E, z.1 < z.2) → (∀ v : Fin d, ∃ z ∈ E, z.1 = v ∨ z.2 = v) →
  let N := k*(d+1)
  let raw := fun (s : Fin k) (x : Fin d → Bool) =>
    (List.ofFn (fun i : Fin k => decide (i ≤ s) :: List.ofFn (fun z : Fin d =>
      decide (i < s) || (decide (i=s) && x z)))).flatten ++ [false,true]
  let fits := fun (C : PEqualNP.CircuitLowerBounds.Circuit)
      (tap : Fin k → {z : Fin d × Fin d // z ∈ E} → Nat) =>
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+2) C ∧
    C.output < N+2+C.size ∧ (∀ s z, tap s z < N+2+C.size) ∧
    ∀ s x z, (C.wires (raw s x)).getD (tap s z) false = (x z.val.1 && x z.val.2)
  let b := PEqualNP.NotBracket.notCount
  let q := 2^r
  (∀ C tap, fits C tap → b C ≤ r →
    let p := C.size - b C
    k*d ≤ 2*p ∧ max 1 (k/q)*E.card ≤ p) ∧
  ∃ C tap, fits C tap ∧ b C ≤ r ∧
    C.size - b C ≤ ((k+q-1)/q)*E.card + 8*k*d) := by
  intro k d r E hk hd hE_lt hE_cov N raw fits b q
  have hraw_eq : ∀ s x, raw s x = PEqualNP.Outside.L_lib_1333.rawFn k d s x := by
    intro s x
    dsimp [raw, PEqualNP.Outside.L_lib_1333.rawFn]
    convert rfl
  constructor
  · intro C tap hfits hb p
    rcases hfits with ⟨hFan, hRB, _, _, htap⟩
    have htap' : ∀ s x z, (C.wires (PEqualNP.Outside.L_lib_1333.rawFn k d s x)).getD (tap s z) false =
        (x z.val.1 && x z.val.2) := by
      intro s x z; rw [← hraw_eq]; exact htap s x z
    refine ⟨?_, ?_⟩
    · exact PEqualNP.Outside.L_lib_1333.lower_bound_kd k d E hk hd hE_lt hE_cov C tap hFan hRB htap'
    · exact PEqualNP.Outside.L_lib_1333.lower_bound_edges k d r E hk hE_lt C tap hFan hRB hb htap'
  · rcases PEqualNP.Outside.L_lib_1333.upper_bound_exists k d r E hk hd with
      ⟨C, tap, hFan, hRB, hout, htap_lt, htap, hb_le, hsz_le⟩
    refine ⟨C, tap, ⟨hFan, hRB, hout, htap_lt, ?_⟩, hb_le, hsz_le⟩
    intro s x z; rw [hraw_eq]; exact htap s x z
