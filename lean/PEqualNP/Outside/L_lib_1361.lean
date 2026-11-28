import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1361_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket
open Classical

-- =========================================================================
-- Part 1: Circuit wire semantics, NOT-aware tap frontier, and retiming
-- =========================================================================

private lemma wires_foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w).length =
      w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, List.length_append, List.length_singleton]
    omega

private lemma wires_foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]) w).getD i false =
      w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]).length := by
      rw [List.length_append, List.length_singleton]; omega
    rw [ih _ hlt]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma wires_getD_gate (C : Circuit) (inp : List Bool) (j : ℕ)
    (hj : j < C.gates.length) (hrb : ReadsBack inp.length C) :
    (C.wires inp).getD (inp.length + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (C.wires inp).getD i false) := by
  let step : List Bool → Gate → List Bool :=
    fun acc g => acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [← h2]; exact h1.symm
  have hg : gateAt C j = C.gates[j] := by
    simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  set w0 := (C.gates.take j).foldl step inp
  have hw0_len : w0.length = inp.length + j := by
    dsimp only [w0]; rw [wires_foldl_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hwires_eq : C.wires inp =
      (C.gates.drop (j + 1)).foldl step (step w0 C.gates[j]) := by
    unfold Circuit.wires
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hval_at : (C.wires inp).getD (inp.length + j) false =
      C.gates[j].op.eval (C.gates[j].inputs.map fun k => w0.getD k false) := by
    rw [hwires_eq]
    have hlt : inp.length + j < (step w0 C.gates[j]).length := by
      dsimp only [step]; rw [List.length_append, List.length_singleton, hw0_len]; omega
    rw [wires_foldl_getD_lt _ _ _ hlt]
    dsimp only [step]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : w0.length ≤ inp.length + j),
      hw0_len, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rw [hval_at, hg]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hilt : i < inp.length + j := hrb j hj i (hg.symm ▸ hi)
  have hilt0 : i < w0.length := by omega
  rw [hwires_eq]
  have hlt1 : i < (step w0 C.gates[j]).length := by
    dsimp only [step]; rw [List.length_append, List.length_singleton]; omega
  rw [wires_foldl_getD_lt _ _ _ hlt1]
  dsimp only [step]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hilt0]

private def isNotOp : GateOp → Bool
  | GateOp.not => true
  | _ => false

private lemma isNotOp_eq_true (op : GateOp) : isNotOp op = true ↔ op = GateOp.not := by
  cases op <;> simp [isNotOp]

private lemma notCount_eq_filter_isNotOp (C : Circuit) :
    notCount C = (C.gates.filter (fun g => isNotOp g.op)).length := by
  unfold notCount
  congr 1
  apply List.filter_congr
  intro g _
  cases g with
  | mk op ins => cases op <;> rfl

private def monoCount (gs : List Gate) : ℕ :=
  (gs.filter (fun g => !(isNotOp g.op))).length

private lemma gates_len_eq_nots_add_monos (gs : List Gate) :
    gs.length = (gs.filter (fun g => isNotOp g.op)).length + monoCount gs := by
  unfold monoCount
  induction gs with
  | nil => simp
  | cons g gs ih =>
    simp only [List.length_cons, List.filter_cons]
    cases isNotOp g.op <;> simp <;> omega

private lemma monoCount_eq_size_sub_notCount (C : Circuit) :
    monoCount C.gates = C.size - notCount C := by
  have h1 := gates_len_eq_nots_add_monos C.gates
  have h2 := notCount_eq_filter_isNotOp C
  unfold Circuit.size
  omega

private def effInputs (g : Gate) : List ℕ :=
  if isNotOp g.op = true then g.inputs.take 1 else g.inputs

private lemma effInputs_subset (g : Gate) {i : ℕ} (hi : i ∈ effInputs g) : i ∈ g.inputs := by
  unfold effInputs at hi
  split_ifs at hi
  · exact List.mem_of_mem_take hi
  · exact hi

private lemma gateOp_eval_congr_eff (g : Gate) (w1 w2 : ℕ → Bool)
    (hagree : ∀ i ∈ effInputs g, w1 i = w2 i) :
    g.op.eval (g.inputs.map w1) = g.op.eval (g.inputs.map w2) := by
  unfold effInputs at hagree
  by_cases hnot : isNotOp g.op = true
  · simp only [hnot, ↓reduceIte] at hagree
    have hop : g.op = GateOp.not := (isNotOp_eq_true g.op).mp hnot
    rw [hop]
    cases hins : g.inputs with
    | nil => rfl
    | cons u rest =>
      simp only [List.map_cons, GateOp.eval, List.headD_cons]
      have hu : u ∈ (u :: rest).take 1 := by simp
      rw [hins] at hagree
      rw [hagree u hu]
  · simp only [hnot, ↓reduceIte] at hagree
    congr 1
    exact List.map_congr_left hagree

private lemma exists_tap_frontier {N a : ℕ} (C : Circuit) (tap : Fin a → ℕ)
    (hfan : FanInTwo C) (hrb : ReadsBack N C) (htap : ∀ i, tap i < N + C.size) :
    ∃ F : Finset ℕ,
      (∀ w ∈ F, w < N) ∧ F.card ≤ a + (C.size - notCount C) ∧
      ∀ inp1 inp2 : List Bool, inp1.length = N → inp2.length = N →
        (∀ i ∈ F, inp1.getD i false = inp2.getD i false) →
        ∀ i : Fin a, (C.wires inp1).getD (tap i) false = (C.wires inp2).getD (tap i) false := by
  suffices hstep : ∀ (m : ℕ), m ≤ C.gates.length →
      ∀ F : Finset ℕ, (∀ w ∈ F, w < N + m) →
        ∃ F0 : Finset ℕ,
          (∀ w ∈ F0, w < N) ∧ F0.card ≤ F.card + monoCount (C.gates.take m) ∧
          ∀ inp1 inp2 : List Bool, inp1.length = N → inp2.length = N →
            (∀ i ∈ F0, inp1.getD i false = inp2.getD i false) →
            ∀ w ∈ F, (C.wires inp1).getD w false = (C.wires inp2).getD w false by
    set Ft : Finset ℕ := Finset.univ.image tap
    have hFt_lt : ∀ w ∈ Ft, w < N + C.gates.length := by
      intro w hw
      rcases Finset.mem_image.mp hw with ⟨i, _, rfl⟩
      exact htap i
    rcases hstep C.gates.length (le_refl _) Ft hFt_lt with ⟨F0, hF0_lt, hF0_card, hF0_eq⟩
    have hFt_card : Ft.card ≤ a := by
      calc Ft.card ≤ (Finset.univ : Finset (Fin a)).card := Finset.card_image_le
        _ = a := by simp
    rw [List.take_length, monoCount_eq_size_sub_notCount] at hF0_card
    refine ⟨F0, hF0_lt, by omega, ?_⟩
    intro inp1 inp2 hl1 hl2 hagree i
    exact hF0_eq inp1 inp2 hl1 hl2 hagree (tap i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  intro m
  induction m with
  | zero =>
    intro _ F hF
    refine ⟨F, fun w hw => by have := hF w hw; omega, by simp [monoCount], ?_⟩
    intro inp1 inp2 hl1 hl2 hagree w hw
    have hwN : w < N := by have := hF w hw; omega
    unfold Circuit.wires
    rw [wires_foldl_getD_lt C.gates inp1 w (by omega),
        wires_foldl_getD_lt C.gates inp2 w (by omega)]
    exact hagree w hw
  | succ m ih =>
    intro hm F hF
    have hm_lt : m < C.gates.length := by omega
    have hgm_eq : gateAt C m = C.gates[m] := by
      simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm_lt, Option.getD_some]
    have htake : C.gates.take (m + 1) = C.gates.take m ++ [gateAt C m] := by
      rw [hgm_eq, List.take_succ_eq_append_getElem hm_lt]
    have hmono_succ : monoCount (C.gates.take (m + 1)) =
        monoCount (C.gates.take m) + if isNotOp (gateAt C m).op = true then 0 else 1 := by
      unfold monoCount
      rw [htake, List.filter_append, List.length_append, List.filter_cons, List.filter_nil]
      cases isNotOp (gateAt C m).op <;> simp
    by_cases hmem : N + m ∈ F
    · set F' : Finset ℕ := F.erase (N + m) ∪ (effInputs (gateAt C m)).toFinset
      have hF'_lt : ∀ w ∈ F', w < N + m := by
        intro w hw
        rcases Finset.mem_union.mp hw with h1 | h2
        · rcases Finset.mem_erase.mp h1 with ⟨hne, hwF⟩
          have := hF w hwF; omega
        · exact hrb m hm_lt w (effInputs_subset _ (List.mem_toFinset.mp h2))
      have hgm_mem : gateAt C m ∈ C.gates := hgm_eq ▸ List.getElem_mem hm_lt
      have hcard_F' : F'.card + monoCount (C.gates.take m) ≤ F.card + monoCount (C.gates.take (m + 1)) := by
        have h1 : F'.card ≤ (F.erase (N + m)).card + (effInputs (gateAt C m)).toFinset.card :=
          Finset.card_union_le _ _
        have h2 : (F.erase (N + m)).card + 1 = F.card := Finset.card_erase_add_one hmem
        have h3 : (effInputs (gateAt C m)).toFinset.card ≤ (effInputs (gateAt C m)).length :=
          List.toFinset_card_le _
        by_cases hnot : isNotOp (gateAt C m).op = true
        · have hlen1 : (effInputs (gateAt C m)).length ≤ 1 := by
            unfold effInputs; simp [hnot]
          rw [hmono_succ, if_pos hnot]; omega
        · have hlen2 : (effInputs (gateAt C m)).length ≤ 2 := by
            unfold effInputs; rw [if_neg hnot]; exact (hfan _ hgm_mem).2
          rw [hmono_succ, if_neg hnot]; omega
      rcases ih (by omega) F' hF'_lt with ⟨F0, hF0_lt, hF0_card, hF0_eq⟩
      refine ⟨F0, hF0_lt, by omega, ?_⟩
      intro inp1 inp2 hl1 hl2 hagree w hw
      by_cases hwm : w = N + m
      · subst hwm
        have h1 := wires_getD_gate C inp1 m hm_lt (by rw [hl1]; exact hrb)
        have h2 := wires_getD_gate C inp2 m hm_lt (by rw [hl2]; exact hrb)
        rw [hl1] at h1; rw [hl2] at h2
        rw [h1, h2]
        apply gateOp_eval_congr_eff
        intro i hi
        exact hF0_eq inp1 inp2 hl1 hl2 hagree i
          (Finset.mem_union_right _ (List.mem_toFinset.mpr hi))
      · exact hF0_eq inp1 inp2 hl1 hl2 hagree w
          (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwm, hw⟩))
    · have hF_lt : ∀ w ∈ F, w < N + m := by
        intro w hw
        have h1 := hF w hw
        have hne : w ≠ N + m := fun h => hmem (h ▸ hw)
        omega
      rcases ih (by omega) F hF_lt with ⟨F0, hF0_lt, hF0_card, hF0_eq⟩
      exact ⟨F0, hF0_lt, by rw [hmono_succ]; omega, hF0_eq⟩

-- =========================================================================
-- Part 2: Prefix vector prefVec and monotone retiming
-- =========================================================================

private noncomputable def prefVec (n : ℕ) (t : Fin (n + 1)) : List Bool :=
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  List.ofFn (fun j : Fin n => decide (j.val < t.val)) ++ [false, true]

private lemma prefVec_len (n : ℕ) (t : Fin (n + 1)) : (prefVec n t).length = n + 2 := by
  unfold prefVec; simp

private lemma prefVec_getD_lt (n : ℕ) (t : Fin (n + 1)) (j : ℕ) (hj : j < n) :
    (prefVec n t).getD j false = decide (j < t.val) := by
  unfold prefVec
  have hlt : j < (List.ofFn (fun k : Fin n => @decide (k.val < t.val) (Classical.propDecidable _))).length := by
    simp [hj]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt,
    List.getElem?_eq_getElem hlt, List.getElem_ofFn, Option.getD_some]
  by_cases h : j < t.val <;> simp [h]

private lemma prefVec_getD_false (n : ℕ) (t : Fin (n + 1)) :
    (prefVec n t).getD n false = false := by
  unfold prefVec
  have hlen : (List.ofFn (fun k : Fin n => @decide (k.val < t.val) (Classical.propDecidable _))).length = n := by
    simp
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hlen] : _ ≤ n),
    hlen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]

private lemma prefVec_getD_true (n : ℕ) (t : Fin (n + 1)) :
    (prefVec n t).getD (n + 1) false = true := by
  unfold prefVec
  have hlen : (List.ofFn (fun k : Fin n => @decide (k.val < t.val) (Classical.propDecidable _))).length = n := by
    simp
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hlen]; omega : _ ≤ n + 1), hlen]
  have hsub : n + 1 - n = 1 := by omega
  rw [hsub]; rfl

private noncomputable def retimeWire {n : ℕ} (g : Fin (n + 1) → Fin (n + 1)) (w : ℕ) : ℕ :=
  if w < n then
    let S := Finset.univ.filter (fun t : Fin (n + 1) => w < (g t).val)
    if h : S.Nonempty then
      let t0 := S.min' h
      if t0.val = 0 then n + 1 else t0.val - 1
    else n
  else w

private lemma retimeWire_lt {n : ℕ} (g : Fin (n + 1) → Fin (n + 1)) {w : ℕ} (hw : w < n + 2) :
    retimeWire g w < n + 2 := by
  unfold retimeWire
  by_cases h1 : w < n
  · simp only [h1, ↓reduceIte]
    set S := Finset.univ.filter (fun t : Fin (n + 1) => w < (g t).val)
    by_cases h2 : S.Nonempty
    · simp only [h2, ↓reduceDIte]
      have ht := (S.min' h2).isLt
      split_ifs <;> omega
    · simp only [h2, ↓reduceDIte]; omega
  · simp only [h1, ↓reduceIte]; exact hw

private lemma retimeWire_ge {n : ℕ} (g : Fin (n + 1) → Fin (n + 1)) {w : ℕ} (hw : n + 2 ≤ w) :
    retimeWire g w = w := by
  unfold retimeWire
  have hnot : ¬(w < n) := by omega
  simp [hnot]

private lemma retimeWire_prefVec {n : ℕ} (g : Fin (n + 1) → Fin (n + 1))
    (hg : ∀ t1 t2 : Fin (n + 1), t1.val ≤ t2.val → (g t1).val ≤ (g t2).val)
    (t : Fin (n + 1)) (w : ℕ) (hw : w < n + 2) :
    (prefVec n t).getD (retimeWire g w) false = (prefVec n (g t)).getD w false := by
  by_cases hwn : w < n
  · rw [prefVec_getD_lt n (g t) w hwn]
    unfold retimeWire
    simp only [hwn, ↓reduceIte]
    set S := Finset.univ.filter (fun u : Fin (n + 1) => w < (g u).val)
    by_cases hne : S.Nonempty
    · simp only [hne, ↓reduceDIte]
      set t0 := S.min' hne
      have ht0_mem : w < (g t0).val := (Finset.mem_filter.mp (Finset.min'_mem S hne)).2
      have ht0_le : ∀ u : Fin (n + 1), w < (g u).val → t0.val ≤ u.val := by
        intro u hu
        exact Finset.min'_le S u (Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu⟩)
      by_cases h0 : t0.val = 0
      · simp only [h0, ↓reduceIte]
        rw [prefVec_getD_true]
        have hgt : w < (g t).val := lt_of_lt_of_le ht0_mem (hg t0 t (by omega))
        simp [hgt]
      · simp only [h0, ↓reduceIte]
        have hlt_n : t0.val - 1 < n := by have := t0.isLt; omega
        rw [prefVec_getD_lt n t (t0.val - 1) hlt_n]
        have hiff : t0.val - 1 < t.val ↔ w < (g t).val := by
          constructor
          · intro hlt
            exact lt_of_lt_of_le ht0_mem (hg t0 t (by omega))
          · intro hgt
            have := ht0_le t hgt
            omega
        by_cases hp : w < (g t).val <;> simp [hp, hiff]
    · simp only [hne, ↓reduceDIte]
      rw [prefVec_getD_false]
      have hnot : ¬(w < (g t).val) := by
        intro hgt
        exact hne ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ t, hgt⟩⟩
      simp [hnot]
  · have hrew : retimeWire g w = w := by unfold retimeWire; simp [hwn]
    rw [hrew]
    by_cases hf : w = n
    · subst hf; rw [prefVec_getD_false, prefVec_getD_false]
    · have ht : w = n + 1 := by omega
      subst ht; rw [prefVec_getD_true, prefVec_getD_true]

private lemma retime_circuit {n a : ℕ} (C : Circuit) (tap : Fin a → ℕ)
    (hfan : FanInTwo C) (hrb : ReadsBack (n + 2) C)
    (hout : C.output < n + 2 + C.size) (htap : ∀ i, tap i < n + 2 + C.size)
    (g : Fin (n + 1) → Fin (n + 1))
    (hg : ∀ t1 t2 : Fin (n + 1), t1.val ≤ t2.val → (g t1).val ≤ (g t2).val) :
    ∃ (C' : Circuit) (tap' : Fin a → ℕ),
      FanInTwo C' ∧ ReadsBack (n + 2) C' ∧
      C'.size = C.size ∧ notCount C' = notCount C ∧
      C'.output < n + 2 + C'.size ∧ (∀ i, tap' i < n + 2 + C'.size) ∧
      ∀ (t : Fin (n + 1)) (i : Fin a),
        (C'.wires (prefVec n t)).getD (tap' i) false =
          (C.wires (prefVec n (g t))).getD (tap i) false := by
  let C' : Circuit := ⟨C.gates.map (fun gate => ⟨gate.op, gate.inputs.map (retimeWire g)⟩), retimeWire g C.output⟩
  let tap' : Fin a → ℕ := fun i => retimeWire g (tap i)
  have hsz : C'.size = C.size := by simp [C', Circuit.size]
  have hnot : notCount C' = notCount C := by
    rw [notCount_eq_filter_isNotOp, notCount_eq_filter_isNotOp]
    dsimp only [C']
    rw [List.filter_map, List.length_map]
    rfl
  have hfan' : FanInTwo C' := by
    intro gate hgate
    rcases List.mem_map.mp hgate with ⟨g0, hg0, rfl⟩
    have h0 := hfan g0 hg0
    exact ⟨h0.1, by simp [h0.2]⟩
  have hrb' : ReadsBack (n + 2) C' := by
    intro j hj i hi
    have hj' : j < C.gates.length := by simpa [C'] using hj
    have hgate : gateAt C' j = ⟨(gateAt C j).op, (gateAt C j).inputs.map (retimeWire g)⟩ := by
      simp only [gateAt, C', List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hj', Option.map_some, Option.getD_some]
    rw [hgate] at hi
    rcases List.mem_map.mp hi with ⟨u, hu, rfl⟩
    have hu_lt : u < n + 2 + j := hrb j hj' u hu
    by_cases hlt : u < n + 2
    · have := retimeWire_lt g hlt; omega
    · rw [retimeWire_ge g (by omega)]; exact hu_lt
  have hrm_bound : ∀ w < n + 2 + C.size, retimeWire g w < n + 2 + C'.size := by
    intro w hw
    by_cases hlt : w < n + 2
    · have := retimeWire_lt g hlt; omega
    · rw [retimeWire_ge g (by omega), hsz]; exact hw
  have hwires : ∀ (t : Fin (n + 1)) (w : ℕ), w < n + 2 + C.size →
      (C'.wires (prefVec n t)).getD (retimeWire g w) false = (C.wires (prefVec n (g t))).getD w false := by
    intro t w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases hlt : w < n + 2
      · have hrm_lt : retimeWire g w < n + 2 := retimeWire_lt g hlt
        unfold Circuit.wires
        rw [wires_foldl_getD_lt C'.gates (prefVec n t) (retimeWire g w) (by rw [prefVec_len]; exact hrm_lt),
            wires_foldl_getD_lt C.gates (prefVec n (g t)) w (by rw [prefVec_len]; exact hlt)]
        exact retimeWire_prefVec g hg t w hlt
      · set j := w - (n + 2)
        have hj : j < C.gates.length := by unfold Circuit.size at hw; omega
        have hj' : j < C'.gates.length := by simpa [C'] using hj
        have hw_eq : w = n + 2 + j := by omega
        rw [retimeWire_ge g (by omega), hw_eq]
        have h1 := wires_getD_gate C' (prefVec n t) j hj' (by rw [prefVec_len]; exact hrb')
        have h2 := wires_getD_gate C (prefVec n (g t)) j hj (by rw [prefVec_len]; exact hrb)
        rw [prefVec_len] at h1 h2
        rw [h1, h2]
        have hgate : gateAt C' j = ⟨(gateAt C j).op, (gateAt C j).inputs.map (retimeWire g)⟩ := by
          simp only [gateAt, C', List.getD_eq_getElem?_getD, List.getElem?_map,
            List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some]
        rw [hgate, List.map_map]
        congr 1
        apply List.map_congr_left
        intro u hu
        have hu_lt : u < n + 2 + j := hrb j hj u hu
        exact ih u (by omega) (by unfold Circuit.size; omega)
  exact ⟨C', tap', hfan', hrb', hsz, hnot, hrm_bound C.output hout, fun i => hrm_bound (tap i) (htap i),
    fun t i => hwires t (tap i) (htap i)⟩

-- =========================================================================
-- Part 3: Stutter-free word sequences (SFVec, Node) and compression
-- =========================================================================

private abbrev Word (a : ℕ) := Fin a → Bool

private abbrev SFVec (a j : ℕ) :=
  { f : Fin (j + 1) → Word a // ∀ i : Fin j, f i.castSucc ≠ f i.succ }

private abbrev Node (a M : ℕ) := Σ j : Fin (M + 1), SFVec a j.val

private lemma card_sfvec (a : ℕ) : ∀ j : ℕ, Fintype.card (SFVec a j) = 2 ^ a * (2 ^ a - 1) ^ j
  | 0 => by
    let e : SFVec a 0 ≃ Word a :=
      { toFun := fun s => s.1 0
        invFun := fun w => ⟨fun _ => w, fun i => Fin.elim0 i⟩
        left_inv := fun s => by
          apply Subtype.ext; funext i
          have : i = 0 := Fin.ext (by omega)
          rw [this]
        right_inv := fun _ => rfl }
    rw [Fintype.card_congr e]
    simp [Word]
  | j + 1 => by
    let e : SFVec a (j + 1) ≃ Σ s : SFVec a j, { w : Word a // s.1 (Fin.last j) ≠ w } :=
      { toFun := fun s =>
          ⟨⟨fun i => s.1 i.castSucc, fun i => s.2 i.castSucc⟩,
           ⟨s.1 (Fin.last (j + 1)), by
             have h := s.2 (Fin.last j)
             simpa [Fin.succ_last] using h⟩⟩
        invFun := fun ⟨s, w⟩ =>
          ⟨Fin.snoc s.1 w.1, fun i => by
            cases i using Fin.lastCases with
            | last =>
              simpa [Fin.snoc_castSucc, Fin.snoc_last, Fin.succ_last] using w.2
            | cast i' =>
              have hsc : i'.castSucc.succ = i'.succ.castSucc := by ext; simp
              rw [hsc]
              simp only [Fin.snoc_castSucc]
              exact s.2 i'⟩
        left_inv := fun s => by
          apply Subtype.ext
          funext i
          cases i using Fin.lastCases with
          | last => simp [Fin.snoc_last]
          | cast i' => simp [Fin.snoc_castSucc]
        right_inv := fun ⟨s, w⟩ => by
          apply Sigma.ext
          · apply Subtype.ext; funext i; simp [Fin.snoc_castSucc]
          · apply (Subtype.heq_iff_coe_eq (fun x => by simp [Fin.snoc_castSucc])).mpr
            simp [Fin.snoc_last] }
    rw [Fintype.card_congr e, Fintype.card_sigma]
    have hfib : ∀ s : SFVec a j, Fintype.card { w : Word a // s.1 (Fin.last j) ≠ w } = 2 ^ a - 1 := by
      intro s
      have heq : (Finset.univ.filter (fun w : Word a => s.1 (Fin.last j) ≠ w)) =
          Finset.univ.erase (s.1 (Fin.last j)) := by
        ext w; simp [ne_comm]
      rw [Fintype.card_subtype, heq, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
      simp [Word]
    simp_rw [hfib]
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, card_sfvec a j, pow_succ]
    ring

private lemma card_node (a M : ℕ) :
    Fintype.card (Node a M) = (Finset.range (M + 1)).sum (fun j => 2 ^ a * (2 ^ a - 1) ^ j) := by
  rw [Fintype.card_sigma]
  simp_rw [card_sfvec]
  rw [Fin.sum_univ_eq_sum_range (fun j => 2 ^ a * (2 ^ a - 1) ^ j) (M + 1)]

private def nodeTake {a M : ℕ} (v : Node a M) (q : Fin (v.1.val + 1)) : Node a M :=
  ⟨⟨q.val, lt_of_le_of_lt (Nat.le_of_lt_succ q.isLt) v.1.isLt⟩,
   ⟨fun i => v.2.1 ⟨i.val, lt_of_lt_of_le i.isLt q.isLt⟩,
    fun i => v.2.2 ⟨i.val, lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ q.isLt)⟩⟩⟩

private lemma nodeTake_last {a M : ℕ} (v : Node a M) :
    nodeTake v (Fin.last v.1.val) = v := by
  rcases v with ⟨j, ⟨f, hf⟩⟩
  apply Sigma.ext
  · exact Fin.ext rfl
  · apply heq_of_eq
    apply Subtype.ext
    funext i
    rfl

private lemma nodeTake_take {a M : ℕ} (v : Node a M) (q : Fin (v.1.val + 1))
    (r : Fin (q.val + 1)) :
    nodeTake (nodeTake v q) r = nodeTake v ⟨r.val, lt_of_lt_of_le r.isLt q.isLt⟩ := by
  apply Sigma.ext
  · exact Fin.ext rfl
  · apply heq_of_eq
    apply Subtype.ext
    funext i
    rfl

private lemma compress_word_seq {a : ℕ} :
    ∀ (k : ℕ) (f : Fin (k + 1) → Word a),
      let ch := (Finset.univ.filter (fun i : Fin k => f i.castSucc ≠ f i.succ)).card
      ∃ (s : SFVec a ch) (u : Fin (ch + 1) → Fin (k + 1)) (ψ : Fin (k + 1) → Fin (ch + 1)),
        (∀ q1 q2 : Fin (ch + 1), q1.val ≤ q2.val → (u q1).val ≤ (u q2).val) ∧
        (∀ t1 t2 : Fin (k + 1), t1.val ≤ t2.val → (ψ t1).val ≤ (ψ t2).val) ∧
        (∀ q : Fin (ch + 1), f (u q) = s.1 q) ∧
        (∀ t : Fin (k + 1), f t = s.1 (ψ t)) ∧
        ψ (Fin.last k) = Fin.last ch := by
  intro k
  induction k with
  | zero =>
    intro f
    have hch : (Finset.univ.filter (fun i : Fin 0 => f i.castSucc ≠ f i.succ)).card = 0 := by simp
    dsimp only
    rw [hch]
    refine ⟨⟨fun _ => f 0, fun i => Fin.elim0 i⟩, fun _ => 0, fun _ => 0,
      fun _ _ _ => le_refl _, fun _ _ _ => le_refl _, fun _ => rfl,
      fun t => by have : t = 0 := Fin.ext (by omega); rw [this], rfl⟩
  | succ k ih =>
    intro f
    let f' : Fin (k + 1) → Word a := fun i => f i.castSucc
    set ch' := (Finset.univ.filter (fun i : Fin k => f' i.castSucc ≠ f' i.succ)).card
    set ch := (Finset.univ.filter (fun i : Fin (k + 1) => f i.castSucc ≠ f i.succ)).card
    rcases ih f' with ⟨s', u', ψ', hu'_mono, hψ'_mono, hfu', hfψ', hψ'_last⟩
    have hch_split : ch = ch' + if f (Fin.last k).castSucc ≠ f (Fin.last (k + 1)) then 1 else 0 := by
      dsimp [ch, ch', f']
      rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
      simp only [Fin.succ_last]
    by_cases hdiff : f (Fin.last k).castSucc = f (Fin.last (k + 1))
    · have hch_eq : ch = ch' := by rw [hch_split]; simp [hdiff]
      dsimp only
      rw [hch_eq]
      refine ⟨s', fun q => (u' q).castSucc,
        Fin.snoc ψ' (Fin.last ch'),
        fun q1 q2 hq => hu'_mono q1 q2 hq,
        ?_, fun q => hfu' q, ?_, by simp [Fin.snoc_last]⟩
      · intro t1 t2 ht
        cases t1 using Fin.lastCases with
        | last =>
          cases t2 using Fin.lastCases with
          | last => exact le_refl _
          | cast t2' => have := t2'.isLt; simp at ht; omega
        | cast t1' =>
          cases t2 using Fin.lastCases with
          | last =>
            simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_last]
            exact Nat.le_of_lt_succ (ψ' t1').isLt
          | cast t2' =>
            simp only [Fin.snoc_castSucc]
            exact hψ'_mono t1' t2' ht
      · intro t
        cases t using Fin.lastCases with
        | last =>
          simp only [Fin.snoc_last]
          rw [← hdiff, ← hψ'_last]
          exact hfψ' (Fin.last k)
        | cast t' =>
          simp only [Fin.snoc_castSucc]
          exact hfψ' t'
    · have hch_eq : ch = ch' + 1 := by rw [hch_split]; simp [hdiff]
      dsimp only
      rw [hch_eq]
      have hlast_ne : s'.1 (Fin.last ch') ≠ f (Fin.last (k + 1)) := by
        rw [← hψ'_last, ← hfψ' (Fin.last k)]
        exact hdiff
      let s : SFVec a (ch' + 1) :=
        ⟨Fin.snoc s'.1 (f (Fin.last (k + 1))), fun i => by
          cases i using Fin.lastCases with
          | last => simpa [Fin.snoc_castSucc, Fin.snoc_last, Fin.succ_last] using hlast_ne
          | cast i' =>
            have hsc : i'.castSucc.succ = i'.succ.castSucc := by ext; simp
            rw [hsc]
            simp only [Fin.snoc_castSucc]
            exact s'.2 i'⟩
      let u : Fin (ch' + 2) → Fin (k + 2) :=
        Fin.snoc (fun q => (u' q).castSucc) (Fin.last (k + 1))
      let ψ : Fin (k + 2) → Fin (ch' + 2) :=
        Fin.snoc (fun t => (ψ' t).castSucc) (Fin.last (ch' + 1))
      refine ⟨s, u, ψ, ?_, ?_, ?_, ?_, by simp [ψ, Fin.snoc_last]⟩
      · intro q1 q2 hq
        cases q1 using Fin.lastCases with
        | last =>
          cases q2 using Fin.lastCases with
          | last => exact le_refl _
          | cast q2' => have := q2'.isLt; simp at hq; omega
        | cast q1' =>
          cases q2 using Fin.lastCases with
          | last =>
            simp only [u, Fin.snoc_castSucc, Fin.snoc_last, Fin.val_last, Fin.val_castSucc]
            exact Nat.le_of_lt (u' q1').isLt
          | cast q2' =>
            simp only [u, Fin.snoc_castSucc]
            exact hu'_mono q1' q2' hq
      · intro t1 t2 ht
        cases t1 using Fin.lastCases with
        | last =>
          cases t2 using Fin.lastCases with
          | last => exact le_refl _
          | cast t2' => have := t2'.isLt; simp at ht; omega
        | cast t1' =>
          cases t2 using Fin.lastCases with
          | last =>
            simp only [ψ, Fin.snoc_castSucc, Fin.snoc_last, Fin.val_last, Fin.val_castSucc]
            exact Nat.le_of_lt (ψ' t1').isLt
          | cast t2' =>
            simp only [ψ, Fin.snoc_castSucc]
            exact hψ'_mono t1' t2' ht
      · intro q
        cases q using Fin.lastCases with
        | last => simp [s, u, Fin.snoc_last]
        | cast q' => simp [s, u, Fin.snoc_castSucc]; exact hfu' q'
      · intro t
        cases t using Fin.lastCases with
        | last => simp [s, ψ, Fin.snoc_last]
        | cast t' => simp [s, ψ, Fin.snoc_castSucc]; exact hfψ' t'

-- =========================================================================
-- Part 4: Clipped DP over Node and core equivalence theorem
-- =========================================================================

private noncomputable def dpRec {n a M : ℕ} (E : ℕ)
    (c : Fin (n + 1) → Word a → ℕ) : ∀ (m : ℕ), m ≤ n + 1 → Node a M → ℕ
  | 0, _, _ => 0
  | m + 1, hm, v =>
    min (E + 1)
      ((Finset.univ : Finset (Fin (v.1.val + 1))).inf' Finset.univ_nonempty
        (fun q => dpRec E c m (Nat.le_of_succ_le hm) (nodeTake v q) + c ⟨m, hm⟩ (v.2.1 q)))

private lemma dpRec_le_succ_E {n a M : ℕ} (E : ℕ) (c : Fin (n + 1) → Word a → ℕ) :
    ∀ (m : ℕ) (hm : m ≤ n + 1) (v : Node a M), dpRec E c m hm v ≤ E + 1
  | 0, _, _ => Nat.zero_le _
  | _ + 1, _, _ => min_le_left _ _

private lemma dpRec_le_take {n a M : ℕ} (E : ℕ) (c : Fin (n + 1) → Word a → ℕ) :
    ∀ (m : ℕ) (hm : m ≤ n + 1) (v : Node a M) (q : Fin (v.1.val + 1)),
      dpRec E c m hm v ≤ dpRec E c m hm (nodeTake v q)
  | 0, _, _, _ => le_refl 0
  | m + 1, hm, v, q => by
    unfold dpRec
    apply min_le_min_left
    apply Finset.le_inf'
    intro r _
    have hle := Finset.inf'_le (f := fun q' : Fin (v.1.val + 1) =>
      dpRec E c m (Nat.le_of_succ_le hm) (nodeTake v q') + c ⟨m, hm⟩ (v.2.1 q'))
      (Finset.mem_univ (⟨r.val, lt_of_lt_of_le r.isLt q.isLt⟩ : Fin (v.1.val + 1)))
    have htake : nodeTake (nodeTake v q) r = nodeTake v ⟨r.val, lt_of_lt_of_le r.isLt q.isLt⟩ :=
      nodeTake_take v q r
    rw [htake]
    exact hle

private lemma dpRec_mono_m {n a M : ℕ} (E : ℕ) (c : Fin (n + 1) → Word a → ℕ)
    (m : ℕ) (hm : m + 1 ≤ n + 1) (v : Node a M) :
    dpRec E c m (Nat.le_of_succ_le hm) v ≤ dpRec E c (m + 1) hm v := by
  conv_rhs => unfold dpRec
  apply le_min (dpRec_le_succ_E E c m (Nat.le_of_succ_le hm) v)
  apply Finset.le_inf'
  intro q _
  exact le_trans (dpRec_le_take E c m (Nat.le_of_succ_le hm) v q) (Nat.le_add_right _ _)

private lemma dpRec_le_of_monotone {n a M : ℕ} (E : ℕ) (c : Fin (n + 1) → Word a → ℕ) :
    ∀ (m : ℕ) (hm : m ≤ n + 1) (v : Node a M) (φ : Fin m → Fin (v.1.val + 1)),
      (∀ t1 t2 : Fin m, t1.val ≤ t2.val → (φ t1).val ≤ (φ t2).val) →
      dpRec E c m hm v ≤ Finset.univ.sum (fun t : Fin m => c ⟨t.val, lt_of_lt_of_le t.isLt hm⟩ (v.2.1 (φ t)))
  | 0, _, _, _, _ => by simp [dpRec]
  | m + 1, hm, v, φ, hφ => by
    unfold dpRec
    refine le_trans (min_le_right _ _) ?_
    set q := φ (Fin.last m)
    refine le_trans (Finset.inf'_le _ (Finset.mem_univ q)) ?_
    let φ' : Fin m → Fin (q.val + 1) := fun t =>
      ⟨(φ t.castSucc).val, Nat.lt_succ_of_le (hφ t.castSucc (Fin.last m) (Nat.le_of_lt t.isLt))⟩
    have hih := dpRec_le_of_monotone E c m (Nat.le_of_succ_le hm) (nodeTake v q) φ'
      (fun t1 t2 ht => hφ t1.castSucc t2.castSucc ht)
    rw [Fin.sum_univ_castSucc]
    apply Nat.add_le_add_right
    refine le_trans hih (le_of_eq ?_)
    apply Finset.sum_congr rfl
    intro t _
    rfl

private lemma dpRec_achieved {n a M : ℕ} (E : ℕ) (c : Fin (n + 1) → Word a → ℕ) :
    ∀ (m : ℕ) (hm : m ≤ n + 1) (v : Node a M),
      dpRec E c m hm v ≤ E →
      ∃ φ : Fin m → Fin (v.1.val + 1),
        (∀ t1 t2 : Fin m, t1.val ≤ t2.val → (φ t1).val ≤ (φ t2).val) ∧
        Finset.univ.sum (fun t : Fin m => c ⟨t.val, lt_of_lt_of_le t.isLt hm⟩ (v.2.1 (φ t))) ≤
          dpRec E c m hm v
  | 0, _, _, _ => ⟨Fin.elim0, fun t => Fin.elim0 t, by simp [dpRec]⟩
  | m + 1, hm, v, hleE => by
    set infVal := (Finset.univ : Finset (Fin (v.1.val + 1))).inf' Finset.univ_nonempty
      (fun q => dpRec E c m (Nat.le_of_succ_le hm) (nodeTake v q) + c ⟨m, hm⟩ (v.2.1 q))
    have hdp_eq : dpRec E c (m + 1) hm v = min (E + 1) infVal := rfl
    have hinf_eq : infVal = dpRec E c (m + 1) hm v := by
      rw [hdp_eq] at hleE ⊢
      have : infVal ≤ E := by omega
      exact (min_eq_right (by omega)).symm
    rcases Finset.exists_mem_eq_inf' Finset.univ_nonempty
        (fun q : Fin (v.1.val + 1) =>
          dpRec E c m (Nat.le_of_succ_le hm) (nodeTake v q) + c ⟨m, hm⟩ (v.2.1 q)) with
      ⟨q, _, hq_eq⟩
    have hprev_le : dpRec E c m (Nat.le_of_succ_le hm) (nodeTake v q) ≤ E := by omega
    rcases dpRec_achieved E c m (Nat.le_of_succ_le hm) (nodeTake v q) hprev_le with
      ⟨φ', hφ'_mono, hφ'_sum⟩
    let φ : Fin (m + 1) → Fin (v.1.val + 1) :=
      Fin.snoc (fun t : Fin m => ⟨(φ' t).val, lt_of_lt_of_le (φ' t).isLt q.isLt⟩) q
    refine ⟨φ, ?_, ?_⟩
    · intro t1 t2 ht
      cases t1 using Fin.lastCases with
      | last =>
        cases t2 using Fin.lastCases with
        | last => exact le_refl _
        | cast t2' => have := t2'.isLt; simp at ht; omega
      | cast t1' =>
        cases t2 using Fin.lastCases with
        | last =>
          simp only [φ, Fin.snoc_castSucc, Fin.snoc_last]
          exact Nat.le_of_lt_succ (φ' t1').isLt
        | cast t2' =>
          simp only [φ, Fin.snoc_castSucc]
          exact hφ'_mono t1' t2' ht
    · rw [Fin.sum_univ_castSucc]
      have hcast_sum : (∑ t : Fin m, c ⟨t.castSucc.val, lt_of_lt_of_le t.castSucc.isLt hm⟩ (v.2.1 (φ t.castSucc))) =
          ∑ t : Fin m, c ⟨t.val, lt_of_lt_of_le t.isLt (Nat.le_of_succ_le hm)⟩ ((nodeTake v q).2.1 (φ' t)) := by
        apply Finset.sum_congr rfl
        intro t _
        simp [φ, Fin.snoc_castSucc, nodeTake]
      have hlast_term : c ⟨(Fin.last m).val, lt_of_lt_of_le (Fin.last m).isLt hm⟩ (v.2.1 (φ (Fin.last m))) =
          c ⟨m, hm⟩ (v.2.1 q) := by
        simp [φ, Fin.snoc_last]
      rw [hcast_sum, hlast_term]
      omega

private lemma dpRec_step_rises_card {n a M : ℕ} (E : ℕ) (c : Fin (n + 1) → Word a → ℕ) (v : Node a M) :
    ∀ (m : ℕ) (hm : m ≤ n + 1),
      (Finset.univ.filter (fun t : Fin m =>
        dpRec E c t.val (Nat.le_of_lt (lt_of_lt_of_le t.isLt hm)) v <
        dpRec E c (t.val + 1) (lt_of_lt_of_le t.isLt hm) v)).card ≤ dpRec E c m hm v
  | 0, _ => by simp [dpRec]
  | m + 1, hm => by
    rw [Finset.card_filter, Fin.sum_univ_castSucc]
    have hih := dpRec_step_rises_card E c v m (Nat.le_of_succ_le hm)
    rw [Finset.card_filter] at hih
    have hmono := dpRec_mono_m E c m hm v
    by_cases hlt : dpRec E c m (Nat.le_of_succ_le hm) v < dpRec E c (m + 1) hm v
    · simp only [Fin.val_castSucc, Fin.val_last, hlt, ↓reduceIte]
      omega
    · simp only [Fin.val_castSucc, Fin.val_last, hlt, ↓reduceIte]
      omega

private lemma dpRec_eq_restricted {n a M : ℕ} (E : ℕ) (c : Fin (n + 1) → Word a → ℕ) :
    let S : Finset (Fin (n + 1)) := Finset.univ.filter (fun t : Fin (n + 1) =>
      ∃ v : Node a M, dpRec E c t.val (Nat.le_of_lt t.isLt) v < dpRec E c (t.val + 1) t.isLt v)
    let cS : Fin (n + 1) → Word a → ℕ := fun t w => if t ∈ S then c t w else 0
    ∀ (m : ℕ) (hm : m ≤ n + 1) (v : Node a M), dpRec E cS m hm v = dpRec E c m hm v := by
  intro S cS m
  induction m with
  | zero => intro _ _; rfl
  | succ m ih =>
    intro hm v
    set t : Fin (n + 1) := ⟨m, hm⟩
    by_cases htS : t ∈ S
    · unfold dpRec
      congr 1
      apply Finset.inf'_congr Finset.univ_nonempty rfl
      intro q _
      rw [ih (Nat.le_of_succ_le hm) (nodeTake v q)]
      simp only [cS, t, htS, ↓reduceIte]
    · have hno_rise : dpRec E c (m + 1) hm v = dpRec E c m (Nat.le_of_succ_le hm) v := by
        have hmono := dpRec_mono_m E c m hm v
        have hnotlt : ¬(dpRec E c m (Nat.le_of_succ_le hm) v < dpRec E c (m + 1) hm v) := by
          intro hlt
          exact htS (Finset.mem_filter.mpr ⟨Finset.mem_univ t, ⟨v, hlt⟩⟩)
        omega
      rw [hno_rise]
      conv_lhs => unfold dpRec
      have hcS0 : ∀ q : Fin (v.1.val + 1),
          dpRec E cS m (Nat.le_of_succ_le hm) (nodeTake v q) + cS t (v.2.1 q) =
          dpRec E c m (Nat.le_of_succ_le hm) (nodeTake v q) := by
        intro q
        rw [ih (Nat.le_of_succ_le hm) (nodeTake v q)]
        simp [cS, htS]
      have hinf_eq : (Finset.univ : Finset (Fin (v.1.val + 1))).inf' Finset.univ_nonempty
          (fun q => dpRec E cS m (Nat.le_of_succ_le hm) (nodeTake v q) + cS ⟨m, hm⟩ (v.2.1 q)) =
          dpRec E c m (Nat.le_of_succ_le hm) v := by
        apply le_antisymm
        · have hle := Finset.inf'_le (f := fun q : Fin (v.1.val + 1) =>
            dpRec E cS m (Nat.le_of_succ_le hm) (nodeTake v q) + cS ⟨m, hm⟩ (v.2.1 q))
            (Finset.mem_univ (Fin.last v.1.val))
          refine le_trans hle ?_
          have := hcS0 (Fin.last v.1.val)
          rw [nodeTake_last] at this
          exact le_of_eq this
        · apply Finset.le_inf'
          intro q _
          have := hcS0 q
          change dpRec E c m (Nat.le_of_succ_le hm) v ≤
            dpRec E cS m (Nat.le_of_succ_le hm) (nodeTake v q) + cS t (v.2.1 q)
          rw [this]
          exact dpRec_le_take E c m (Nat.le_of_succ_le hm) v q
      rw [hinf_eq]
      exact min_eq_right (dpRec_le_succ_E E c m (Nat.le_of_succ_le hm) v)

private def fitProp (a n p b s e : ℕ) (cost : Fin (n + 1) → Word a → ℕ)
    (S : Finset (Fin (n + 1))) : Prop :=
  ∃ (C : Circuit) (tap : Fin a → ℕ),
    FanInTwo C ∧ ReadsBack (n + 2) C ∧
    C.size - notCount C ≤ p ∧ notCount C ≤ b ∧ C.size ≤ s ∧
    C.output < n + 2 + C.size ∧ (∀ i, tap i < n + 2 + C.size) ∧
    S.sum (fun t => cost t (fun i => (C.wires (prefVec n t)).getD (tap i) false)) ≤ e

private lemma core_theorem (n a P E : ℕ) (cost : Fin (n + 1) → Word a → ℕ) :
    let K := 2 ^ a
    let nodes := (Finset.range (P + a + 1)).sum (fun j => K * (K - 1) ^ j)
    ∃ S : Finset (Fin (n + 1)), S.card ≤ (E + 1) * nodes ∧
      ∀ p ≤ P, ∀ b s : ℕ, ∀ e ≤ E,
        fitProp a n p b s e cost Finset.univ ↔ fitProp a n p b s e cost S := by
  dsimp only
  set M := P + a
  set S : Finset (Fin (n + 1)) := Finset.univ.filter (fun t : Fin (n + 1) =>
    ∃ v : Node a M, dpRec E cost t.val (Nat.le_of_lt t.isLt) v < dpRec E cost (t.val + 1) t.isLt v)
  refine ⟨S, ?_, ?_⟩
  · -- S.card ≤ (E + 1) * nodes
    have hsub : S ⊆ (Finset.univ : Finset (Node a M)).biUnion (fun v =>
        Finset.univ.filter (fun t : Fin (n + 1) =>
          dpRec E cost t.val (Nat.le_of_lt t.isLt) v < dpRec E cost (t.val + 1) t.isLt v)) := by
      intro t ht
      rcases (Finset.mem_filter.mp ht).2 with ⟨v, hv⟩
      exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ v, Finset.mem_filter.mpr ⟨Finset.mem_univ t, hv⟩⟩
    calc S.card
        ≤ ((Finset.univ : Finset (Node a M)).biUnion (fun v =>
            Finset.univ.filter (fun t : Fin (n + 1) =>
              dpRec E cost t.val (Nat.le_of_lt t.isLt) v < dpRec E cost (t.val + 1) t.isLt v))).card :=
          Finset.card_le_card hsub
      _ ≤ (Finset.univ : Finset (Node a M)).sum (fun v =>
            (Finset.univ.filter (fun t : Fin (n + 1) =>
              dpRec E cost t.val (Nat.le_of_lt t.isLt) v < dpRec E cost (t.val + 1) t.isLt v)).card) :=
          Finset.card_biUnion_le
      _ ≤ (Finset.univ : Finset (Node a M)).sum (fun _ => E + 1) := by
          apply Finset.sum_le_sum
          intro v _
          exact le_trans (dpRec_step_rises_card E cost v (n + 1) (le_refl _))
            (dpRec_le_succ_E E cost (n + 1) (le_refl _) v)
      _ = Fintype.card (Node a M) * (E + 1) := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      _ = (E + 1) * (Finset.range (P + a + 1)).sum (fun j => 2 ^ a * (2 ^ a - 1) ^ j) := by
          rw [mul_comm, card_node]
  · intro p hp b s e he
    constructor
    · rintro ⟨C, tap, hfan, hrb, hpC, hbC, hsC, hout, htap, hsum⟩
      refine ⟨C, tap, hfan, hrb, hpC, hbC, hsC, hout, htap, ?_⟩
      exact le_trans (Finset.sum_le_sum_of_subset (Finset.subset_univ S)) hsum
    · rintro ⟨C, tap, hfan, hrb, hpC, hbC, hsC, hout, htap, hsumS⟩
      let f : Fin (n + 1) → Word a := fun t i => (C.wires (prefVec n t)).getD (tap i) false
      rcases exists_tap_frontier C tap hfan hrb htap with ⟨F, hF_lt, hF_card, hF_eq⟩
      set R : Finset ℕ := F.filter (· < n)
      have hR_card : R.card ≤ M := by
        have h1 : R.card ≤ F.card := Finset.card_filter_le F _
        omega
      set ch := (Finset.univ.filter (fun i : Fin n => f i.castSucc ≠ f i.succ)).card
      have hch_le : ch ≤ M := by
        have hsub : (Finset.univ.filter (fun i : Fin n => f i.castSucc ≠ f i.succ)).image Fin.val ⊆ R := by
          intro x hx
          rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
          have hne : f i.castSucc ≠ f i.succ := (Finset.mem_filter.mp hi).2
          rw [Finset.mem_filter]
          refine ⟨?_, i.isLt⟩
          by_contra hiF
          apply hne
          funext idx
          apply hF_eq _ _ (prefVec_len n i.castSucc) (prefVec_len n i.succ)
          intro w hwF
          have hw_lt : w < n + 2 := hF_lt w hwF
          by_cases hwn : w < n
          · rw [prefVec_getD_lt n i.castSucc w hwn, prefVec_getD_lt n i.succ w hwn]
            have hne_w : w ≠ i.val := fun h => hiF (h ▸ hwF)
            have h1 : (i.castSucc : Fin (n + 1)).val = i.val := rfl
            have h2 : (i.succ : Fin (n + 1)).val = i.val + 1 := rfl
            rw [h1, h2]
            by_cases hlt : w < i.val
            · have hlt2 : w < i.val + 1 := by omega
              simp [hlt, hlt2]
            · have hlt2 : ¬(w < i.val + 1) := by omega
              simp [hlt, hlt2]
          · by_cases hf0 : w = n
            · subst hf0; rw [prefVec_getD_false, prefVec_getD_false]
            · have ht1 : w = n + 1 := by omega
              subst ht1; rw [prefVec_getD_true, prefVec_getD_true]
        calc ch = ((Finset.univ.filter (fun i : Fin n => f i.castSucc ≠ f i.succ)).image Fin.val).card :=
              (Finset.card_image_of_injective _ Fin.val_injective).symm
          _ ≤ R.card := Finset.card_le_card hsub
          _ ≤ M := hR_card
      rcases compress_word_seq n f with ⟨sVec, u, ψ, hu_mono, hψ_mono, hfu, hfψ, _⟩
      let v0 : Node a M := ⟨⟨ch, Nat.lt_succ_of_le hch_le⟩, sVec⟩
      let cS : Fin (n + 1) → Word a → ℕ := fun t w => if t ∈ S then cost t w else 0
      have hdpS_le : dpRec E cS (n + 1) (le_refl _) v0 ≤ e := by
        have h1 := dpRec_le_of_monotone E cS (n + 1) (le_refl _) v0 ψ hψ_mono
        refine le_trans h1 ?_
        have hsum_eq : Finset.univ.sum (fun t : Fin (n + 1) => cS t (v0.2.1 (ψ t))) =
            S.sum (fun t => cost t (f t)) := by
          dsimp [cS, v0]
          rw [← Finset.sum_filter]
          have hfilt : Finset.univ.filter (fun t : Fin (n + 1) => t ∈ S) = S := by ext t; simp
          rw [hfilt]
          apply Finset.sum_congr rfl
          intro t _
          rw [hfψ t]
        rw [hsum_eq]
        exact hsumS
      have hdp_le : dpRec E cost (n + 1) (le_refl _) v0 ≤ e := by
        rw [← dpRec_eq_restricted (M := M) E cost (n + 1) (le_refl _) v0]
        exact hdpS_le
      rcases dpRec_achieved E cost (n + 1) (le_refl _) v0 (le_trans hdp_le he) with ⟨φ, hφ_mono, hφ_sum⟩
      let g : Fin (n + 1) → Fin (n + 1) := fun t => u (φ t)
      have hg_mono : ∀ t1 t2 : Fin (n + 1), t1.val ≤ t2.val → (g t1).val ≤ (g t2).val :=
        fun t1 t2 ht => hu_mono (φ t1) (φ t2) (hφ_mono t1 t2 ht)
      rcases retime_circuit C tap hfan hrb hout htap g hg_mono with
        ⟨C', tap', hfan', hrb', hsz', hnot', hout', htap', hev'⟩
      refine ⟨C', tap', hfan', hrb', by omega, by omega, by omega, hout', htap', ?_⟩
      have hsum_eq : Finset.univ.sum (fun t : Fin (n + 1) =>
            cost t (fun i => (C'.wires (prefVec n t)).getD (tap' i) false)) =
          Finset.univ.sum (fun t : Fin (n + 1) => cost t (v0.2.1 (φ t))) := by
        apply Finset.sum_congr rfl
        intro t _
        have hw : (fun i => (C'.wires (prefVec n t)).getD (tap' i) false) = v0.2.1 (φ t) := by
          funext i
          rw [hev' t i]
          exact congrFun (hfu (φ t)) i
        rw [hw]
      rw [hsum_eq]
      exact le_trans hφ_sum hdp_le

-- =========================================================================
-- Part 5: Main assembly (zero omega under letI)
-- =========================================================================

private theorem main_aux :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    let fit := fun (a n p b s e : Nat) (cost : Fin (n+1) → (Fin a → Bool) → Nat)
        (S : Finset (Fin (n+1))) =>
      ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin a → Nat),
        PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
        C.size - PEqualNP.NotBracket.notCount C ≤ p ∧ PEqualNP.NotBracket.notCount C ≤ b ∧ C.size ≤ s ∧
        C.output < n+2+C.size ∧ (∀ i, tap i < n+2+C.size) ∧
        S.sum (fun t => cost t (fun i => (C.wires
          (List.ofFn (fun j : Fin n => decide (j.val < t.val)) ++ [false,true])).getD (tap i) false)) ≤ e
    ∀ (n a P E : Nat) (cost : Fin (n+1) → (Fin a → Bool) → Nat),
      let K := 2^a
      let nodes := (Finset.range (P+a+1)).sum (fun j => K*(K-1)^j)
      ∃ S : Finset (Fin (n+1)), S.card ≤ (E+1)*nodes ∧
        ∀ p ≤ P, ∀ b s : Nat, ∀ e ≤ E,
          fit a n p b s e cost Finset.univ ↔ fit a n p b s e cost S := by
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  dsimp only
  intro n a P E cost
  exact core_theorem n a P E cost

end PEqualNP.Outside.L_lib_1361_aux

theorem PEqualNP.Outside.L_lib_1361 :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    let fit := fun (a n p b s e : Nat) (cost : Fin (n+1) → (Fin a → Bool) → Nat)
        (S : Finset (Fin (n+1))) =>
      ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin a → Nat),
        PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
        C.size - PEqualNP.NotBracket.notCount C ≤ p ∧ PEqualNP.NotBracket.notCount C ≤ b ∧ C.size ≤ s ∧
        C.output < n+2+C.size ∧ (∀ i, tap i < n+2+C.size) ∧
        S.sum (fun t => cost t (fun i => (C.wires
          (List.ofFn (fun j : Fin n => decide (j.val < t.val)) ++ [false,true])).getD (tap i) false)) ≤ e
    ∀ (n a P E : Nat) (cost : Fin (n+1) → (Fin a → Bool) → Nat),
      let K := 2^a
      let nodes := (Finset.range (P+a+1)).sum (fun j => K*(K-1)^j)
      ∃ S : Finset (Fin (n+1)), S.card ≤ (E+1)*nodes ∧
        ∀ p ≤ P, ∀ b s : Nat, ∀ e ≤ E,
          fit a n p b s e cost Finset.univ ↔ fit a n p b s e cost S := by
  exact PEqualNP.Outside.L_lib_1361_aux.main_aux
