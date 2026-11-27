import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Choose
import PEqualNP.Outside.L_meta_25491
import PEqualNP.MetaComplexity.Helpers.RepPath

namespace PEqualNP.Outside.L_meta_25529_aux

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.RepReads

private def val (C : Circuit) (x : List Bool) (k : ℕ) : Bool :=
  (wiresFrom C.gates x).getD k false

private def WellFormed (L : ℕ) (C : Circuit) : Prop :=
  (∀ j (hj : j < C.gates.length), ∀ i ∈ (C.gates[j]).inputs, i < L + j) ∧
  C.output < L + C.gates.length

private def rowInput {m : ℕ} (base : Fin m → List Bool) (r : ℕ) (c : Fin m) : List Bool :=
  (base c).set r true

private theorem length_rowInput {m : ℕ} (base : Fin m → List Bool) (r : ℕ) (c : Fin m) :
    (rowInput base r c).length = (base c).length := by
  simp [rowInput]

private theorem getD_set_true (l : List Bool) (r i : ℕ) (hr : r < l.length) :
    (l.set r true).getD i false = if i = r then true else l.getD i false := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h : i = r
  · subst h
    simp [hr]
  · rw [List.getElem?_set_ne (Ne.symm h)]
    simp [h]

private theorem rowInput_getD {m L : ℕ} (base : Fin m → List Bool)
    (hlen : ∀ c, (base c).length = L) (r : ℕ) (hr : r < L) (c : Fin m) (i : ℕ) :
    (rowInput base r c).getD i false = if i = r then true else (base c).getD i false :=
  getD_set_true (base c) r i (by rw [hlen c]; exact hr)

private theorem val_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    val C x i = x.getD i false :=
  getD_wiresFrom C.gates x i hi

private theorem val_eq_eval (C : Circuit) (x : List Bool) :
    val C x C.output = C.eval x := rfl

private theorem val_out_of_bounds (C : Circuit) (x : List Bool) (k : ℕ)
    (hk : x.length + C.gates.length ≤ k) :
    val C x k = false := by
  unfold val
  exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; exact hk)

private theorem val_gate_take (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    val C x (x.length + j) =
      (C.gates[j]).op.eval
        ((C.gates[j]).inputs.map fun i => (wiresFrom (C.gates.take j) x).getD i false) := by
  unfold val
  have hsplit : C.gates = (C.gates.take j ++ [C.gates[j]]) ++ C.gates.drop (j + 1) := by
    rw [List.take_append_getElem, List.take_append_drop]
  conv_lhs => rw [hsplit, wiresFrom_append]
  have hlen1 : (wiresFrom (C.gates.take j ++ [C.gates[j]]) x).length = x.length + j + 1 := by
    rw [length_wiresFrom, List.length_append, List.length_take_of_le (Nat.le_of_lt hj),
      List.length_singleton]
    omega
  rw [getD_wiresFrom _ _ _ (by omega), wiresFrom_snoc, getD_snoc, length_wiresFrom,
    List.length_take_of_le (Nat.le_of_lt hj)]
  simp

private theorem val_take_eq (C : Circuit) (x : List Bool) (j i : ℕ) (hj : j ≤ C.gates.length)
    (hi : i < x.length + j) :
    (wiresFrom (C.gates.take j) x).getD i false = val C x i := by
  unfold val
  have hlen : (wiresFrom (C.gates.take j) x).length = x.length + j := by
    rw [length_wiresFrom, List.length_take_of_le hj]
  conv_rhs =>
    rw [← List.take_append_drop j C.gates, wiresFrom_append, getD_wiresFrom _ _ _ (by omega)]

private theorem val_gate_wf {L : ℕ} (C : Circuit) (hW : WellFormed L C)
    (x : List Bool) (hx : x.length = L) (j : ℕ) (hj : j < C.gates.length) :
    val C x (L + j) = (C.gates[j]).op.eval ((C.gates[j]).inputs.map (val C x)) := by
  rw [← hx, val_gate_take C x j hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hilt : i < x.length + j := by rw [hx]; exact hW.1 j hj i hi
  exact val_take_eq C x j i (Nat.le_of_lt hj) hilt

private theorem op_mono_mem (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (S T : ℕ → Bool) (h : ∀ i ∈ g.inputs, S i = true → T i = true)
    (he : g.op.eval (g.inputs.map S) = true) : g.op.eval (g.inputs.map T) = true := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hop | hop <;> rw [hop] at he ⊢
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id] at he ⊢
    exact fun i hi => h i hi (he i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id] at he ⊢
    obtain ⟨i, hi, hv⟩ := he
    exact ⟨i, hi, h i hi hv⟩

private theorem val_le_of_exceptions (L : ℕ) (C : Circuit) (hM : Monotone2 C) (hW : WellFormed L C)
    (x y : List Bool) (hx : x.length = L) (hy : y.length = L)
    (E : Set ℕ)
    (hIn : ∀ i < L, i ∉ E → x.getD i false = true → y.getD i false = true)
    (hGate : ∀ j (hj : j < C.gates.length), L + j ∉ E →
      (val C x (L + j) = true → val C y (L + j) = true) ∨
      (∀ i ∈ (C.gates[j]).inputs, i ∉ E)) :
    ∀ k, k ∉ E → val C x k = true → val C y k = true := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hkE hval
    by_cases hkL : k < L
    · rw [val_input C x k (by omega)] at hval
      rw [val_input C y k (by omega)]
      exact hIn k hkL hkE hval
    · by_cases hkB : k < L + C.gates.length
      · set j := k - L
        have hj : j < C.gates.length := by omega
        have hkj : k = L + j := by omega
        rw [hkj] at hkE hval ⊢
        rcases hGate j hj hkE with hdir | hclean
        · exact hdir hval
        · rw [val_gate_wf C hW x hx j hj] at hval
          rw [val_gate_wf C hW y hy j hj]
          have hmem : C.gates[j] ∈ C.gates := List.getElem_mem hj
          refine op_mono_mem (C.gates[j]) (hM _ hmem).1 (val C x) (val C y) ?_ hval
          intro i hi hxi
          have hilt : i < k := by
            have := hW.1 j hj i hi
            omega
          exact ih i hilt (hclean i hi) hxi
      · have hfalse := val_out_of_bounds C x k (by omega)
        rw [hfalse] at hval
        exact Bool.noConfusion hval

private theorem sum_count_le_length (l : List ℕ) (S : Finset ℕ) (f : ℕ → ℕ)
    (hinj : Set.InjOn f S) :
    ∑ v ∈ S, l.count (f v) ≤ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hsplit : ∀ v, (a :: l).count (f v) = (if f v = a then 1 else 0) + l.count (f v) := by
      intro v
      rw [List.count_cons]
      by_cases h : f v = a
      · simp [h]; omega
      · simp [h, Ne.symm h]
    simp_rw [hsplit, Finset.sum_add_distrib]
    have h1 : ∑ v ∈ S, (if f v = a then 1 else 0) ≤ 1 := by
      rw [Finset.sum_boole]
      have hcard : (S.filter fun v => f v = a).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro x hx y hy
        simp only [Finset.mem_filter] at hx hy
        exact hinj hx.1 hy.1 (hx.2.trans hy.2.symm)
      simpa using hcard
    simp only [List.length_cons]
    omega

private theorem val_gate_or_true {L : ℕ} (C : Circuit) (hW : WellFormed L C)
    (x : List Bool) (hx : x.length = L) (j : ℕ) (hj : j < C.gates.length)
    (hop : (C.gates[j]).op = GateOp.or) (i : ℕ) (hi : i ∈ (C.gates[j]).inputs)
    (hvi : val C x i = true) :
    val C x (L + j) = true := by
  rw [val_gate_wf C hW x hx j hj, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
  exact ⟨i, hi, hvi⟩

private theorem val_gate_and_false {L : ℕ} (C : Circuit) (hW : WellFormed L C)
    (x : List Bool) (hx : x.length = L) (j : ℕ) (hj : j < C.gates.length)
    (hop : (C.gates[j]).op = GateOp.and) (i : ℕ) (hi : i ∈ (C.gates[j]).inputs)
    (hvi : val C x i = false) :
    val C x (L + j) = false := by
  rw [val_gate_wf C hW x hx j hj, hop]
  simp only [GateOp.eval, List.all_map]
  rw [Bool.eq_false_iff]
  intro hall
  rw [List.all_eq_true] at hall
  have h1 : val C x i = true := by simpa using hall i hi
  rw [hvi] at h1
  exact Bool.noConfusion h1

private theorem exists_ne_in (R : Finset ℕ) (h : 2 ≤ R.card) (r : ℕ) :
    ∃ r' ∈ R, r' ≠ r := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < R.card)
  by_cases h1 : a = r
  · exact ⟨b, hb, fun h2 => hab (h1.trans h2.symm)⟩
  · exact ⟨a, ha, h1⟩

private theorem no_row_output {m L : ℕ} (base : Fin m → List Bool)
    (hlen : ∀ c, (base c).length = L) (R : Finset ℕ) (hRL : ∀ r ∈ R, r < L)
    (G : ℕ → Fin m → Bool) (hcard : 2 ≤ R.card)
    (hPair : ∀ u ∈ R, ∀ v ∈ R, u ≠ v → ∃ c : Fin m, G u c = true ∧ G v c = false)
    (C : Circuit) (hEval : ∀ u ∈ R, ∀ c : Fin m, C.eval (rowInput base u c) = G u c)
    (r : ℕ) (hr : r ∈ R) :
    C.output ≠ r := by
  intro heq
  obtain ⟨r', hr', hne⟩ := exists_ne_in R hcard r
  obtain ⟨c, _, hGr⟩ := hPair r' hr' r hr hne
  have hv := hEval r hr c
  rw [← val_eq_eval, heq, val_input C _ r (by rw [length_rowInput, hlen]; exact hRL r hr),
    rowInput_getD base hlen r (hRL r hr) c r, ite_eq_left rfl] at hv
  rw [hGr] at hv
  exact Bool.noConfusion hv

private theorem no_gate_output_reads_row {m L : ℕ} (base : Fin m → List Bool)
    (hlen : ∀ c, (base c).length = L) (R : Finset ℕ)
    (hRL : ∀ r ∈ R, r < L) (hR0 : ∀ r ∈ R, ∀ c, (base c).getD r false = false)
    (G : ℕ → Fin m → Bool) (hcard : 2 ≤ R.card)
    (hPair : ∀ u ∈ R, ∀ v ∈ R, u ≠ v → ∃ c : Fin m, G u c = true ∧ G v c = false)
    (C : Circuit) (hM : Monotone2 C) (hW : WellFormed L C)
    (hEval : ∀ u ∈ R, ∀ c : Fin m, C.eval (rowInput base u c) = G u c)
    (r : ℕ) (hr : r ∈ R) (j : ℕ) (hj : j < C.gates.length)
    (hout : C.output = L + j) :
    r ∉ (C.gates[j]).inputs := by
  intro hmem
  obtain ⟨r', hr', hne⟩ := exists_ne_in R hcard r
  have hop := (hM (C.gates[j]) (List.getElem_mem hj)).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hop | hop
  · obtain ⟨c, hGr', _⟩ := hPair r' hr' r hr hne
    have hvr : val C (rowInput base r' c) r = false := by
      rw [val_input C _ r (by rw [length_rowInput, hlen]; exact hRL r hr),
        rowInput_getD base hlen r' (hRL r' hr') c r, ite_eq_right (Ne.symm hne), hR0 r hr c]
    have hgf := val_gate_and_false C hW (rowInput base r' c) (by rw [length_rowInput, hlen])
      j hj hop r hmem hvr
    have hev := hEval r' hr' c
    rw [← val_eq_eval, hout, hgf, hGr'] at hev
    exact Bool.noConfusion hev
  · obtain ⟨c, _, hGr⟩ := hPair r' hr' r hr hne
    have hvr : val C (rowInput base r c) r = true := by
      rw [val_input C _ r (by rw [length_rowInput, hlen]; exact hRL r hr),
        rowInput_getD base hlen r (hRL r hr) c r, ite_eq_left rfl]
    have hgt := val_gate_or_true C hW (rowInput base r c) (by rw [length_rowInput, hlen])
      j hj hop r hmem hvr
    have hev := hEval r hr c
    rw [← val_eq_eval, hout, hgt, hGr] at hev
    exact Bool.noConfusion hev

private theorem case_private_row_ors {m L : ℕ} (base : Fin m → List Bool)
    (hlen : ∀ c, (base c).length = L) (R : Finset ℕ)
    (hRL : ∀ r ∈ R, r < L) (hR0 : ∀ r ∈ R, ∀ c, (base c).getD r false = false)
    (G : ℕ → Fin m → Bool) (hcard3 : 3 ≤ R.card)
    (hPair : ∀ u ∈ R, ∀ v ∈ R, u ≠ v → ∃ c : Fin m, G u c = true ∧ G v c = false)
    (hTriple : ∀ u ∈ R, ∀ v ∈ R, ∀ w ∈ R, u ≠ v → u ≠ w → v ≠ w →
      ∃ c : Fin m, G u c = true ∧ G v c = true ∧ G w c = false)
    (C : Circuit) (hM : Monotone2 C) (hW : WellFormed L C)
    (hEval : ∀ u ∈ R, ∀ c : Fin m, C.eval (rowInput base u c) = G u c)
    (g : ℕ → ℕ)
    (hg_lt : ∀ r ∈ R, g r < C.gates.length)
    (hg_read : ∀ r (hr : r ∈ R), r ∈ (C.gates[g r]'(hg_lt r hr)).inputs)
    (hg_sole : ∀ r ∈ R, ∀ j (hj : j < C.gates.length), r ∈ (C.gates[j]).inputs → j = g r)
    (hg_or : ∀ r (hr : r ∈ R), (C.gates[g r]'(hg_lt r hr)).op = GateOp.or) :
    2 * R.card ≤ C.size := by
  have hcard2 : 2 ≤ R.card := by omega
  have hval_gu : ∀ r (hr : r ∈ R) (c : Fin m), val C (rowInput base r c) (L + g r) = true := by
    intro r hr c
    have hvr : val C (rowInput base r c) r = true := by
      rw [val_input C _ r (by rw [length_rowInput, hlen]; exact hRL r hr),
        rowInput_getD base hlen r (hRL r hr) c r, ite_eq_left rfl]
    exact val_gate_or_true C hW (rowInput base r c) (by rw [length_rowInput, hlen])
      (g r) (hg_lt r hr) (hg_or r hr) r (hg_read r hr) hvr
  have hg_not_out : ∀ r ∈ R, C.output ≠ L + g r := by
    intro r hr hout
    exact no_gate_output_reads_row base hlen R hRL hR0 G hcard2 hPair C hM hW hEval
      r hr (g r) (hg_lt r hr) hout (hg_read r hr)
  have hg_inj : Set.InjOn g R := by
    intro u hu v hv heq
    by_contra hne
    obtain ⟨c, hGu, hGv⟩ := hPair u hu v hv hne
    have hle := val_le_of_exceptions L C hM hW (rowInput base u c) (rowInput base v c)
      (by rw [length_rowInput, hlen]) (by rw [length_rowInput, hlen]) {u, v}
      (by
        intro i _ hi hx
        have hiu : i ≠ u := fun h => hi (Or.inl h)
        have hiv : i ≠ v := fun h => hi (Or.inr h)
        rw [rowInput_getD base hlen u (hRL u hu) c i, ite_eq_right hiu] at hx
        rw [rowInput_getD base hlen v (hRL v hv) c i, ite_eq_right hiv]
        exact hx)
      (by
        intro j hj _
        by_cases hjg : j = g u
        · left
          intro _
          rw [hjg, heq]
          exact hval_gu v hv c
        · right
          intro i hi hmem
          rcases hmem with h | h
          · rw [h] at hi; exact hjg (hg_sole u hu j hj hi)
          · simp only [Set.mem_singleton_iff] at h
            rw [h] at hi; exact hjg ((hg_sole v hv j hj hi).trans heq.symm))
    have houtE : C.output ∉ ({u, v} : Set ℕ) := by
      intro h
      rcases h with h | h
      · exact no_row_output base hlen R hRL G hcard2 hPair C hEval u hu h
      · exact no_row_output base hlen R hRL G hcard2 hPair C hEval v hv h
    have hres := hle C.output houtE (by rw [val_eq_eval, hEval u hu c, hGu])
    rw [val_eq_eval, hEval v hv c, hGv] at hres
    exact Bool.noConfusion hres
  have hg_no_feed_U : ∀ u (hu : u ∈ R) v (hv : v ∈ R),
      L + g u ∉ (C.gates[g v]'(hg_lt v hv)).inputs := by
    intro u hu v hv hmem
    by_cases huv : u = v
    · subst huv
      have h1 := hW.1 (g u) (hg_lt u hu) (L + g u) hmem
      omega
    · obtain ⟨c, hGv, hGu⟩ := hPair v hv u hu (Ne.symm huv)
      have hle := val_le_of_exceptions L C hM hW (rowInput base v c) (rowInput base u c)
        (by rw [length_rowInput, hlen]) (by rw [length_rowInput, hlen]) {v}
        (by
          intro i _ hi hx
          have hiv : i ≠ v := by simpa using hi
          rw [rowInput_getD base hlen v (hRL v hv) c i, ite_eq_right hiv] at hx
          rw [rowInput_getD base hlen u (hRL u hu) c i]
          split_ifs
          · rfl
          · exact hx)
        (by
          intro j hj _
          by_cases hjv : j = g v
          · left
            intro _
            rw [hjv]
            exact val_gate_or_true C hW (rowInput base u c) (by rw [length_rowInput, hlen])
              (g v) (hg_lt v hv) (hg_or v hv) (L + g u) hmem (hval_gu u hu c)
          · right
            intro i hi hmv
            have hiv : i = v := by simpa using hmv
            rw [hiv] at hi
            exact hjv (hg_sole v hv j hj hi))
      have houtE : C.output ∉ ({v} : Set ℕ) := by
        simpa using no_row_output base hlen R hRL G hcard2 hPair C hEval v hv
      have hres := hle C.output houtE (by rw [val_eq_eval, hEval v hv c, hGv])
      rw [val_eq_eval, hEval u hu c, hGu] at hres
      exact Bool.noConfusion hres
  have hg_has_reader : ∀ u ∈ R, ∃ j : ℕ, ∃ _ : j < C.gates.length, L + g u ∈ (C.gates[j]).inputs := by
    intro u hu
    by_contra hnone
    push Not at hnone
    obtain ⟨v, hv, hne⟩ := exists_ne_in R hcard2 u
    obtain ⟨c, hGu, hGv⟩ := hPair u hu v hv (Ne.symm hne)
    have hle := val_le_of_exceptions L C hM hW (rowInput base u c) (rowInput base v c)
      (by rw [length_rowInput, hlen]) (by rw [length_rowInput, hlen]) {u, L + g u}
      (by
        intro i hiL hiE hx
        have hiu : i ≠ u := fun h => hiE (Or.inl h)
        rw [rowInput_getD base hlen u (hRL u hu) c i, ite_eq_right hiu] at hx
        rw [rowInput_getD base hlen v (hRL v hv) c i]
        split_ifs
        · rfl
        · exact hx)
      (by
        intro j hj hjE
        have hjg : j ≠ g u := fun h => hjE (Set.mem_insert_of_mem _ (by simp [h]))
        right
        intro i hi hmem
        rcases hmem with h | h
        · rw [h] at hi; exact hjg (hg_sole u hu j hj hi)
        · simp only [Set.mem_singleton_iff] at h
          rw [h] at hi
          exact hnone j hj hi)
    have houtE : C.output ∉ ({u, L + g u} : Set ℕ) := by
      intro h
      rcases h with h | h
      · exact no_row_output base hlen R hRL G hcard2 hPair C hEval u hu h
      · exact hg_not_out u hu h
    have hres := hle C.output houtE (by rw [val_eq_eval, hEval u hu c, hGu])
    rw [val_eq_eval, hEval v hv c, hGv] at hres
    exact Bool.noConfusion hres
  have hmiracle : ∀ u ∈ R, ∀ v ∈ R, u ≠ v → ∀ q (hq : q < C.gates.length),
      (∀ j (hj : j < C.gates.length), L + g u ∈ (C.gates[j]).inputs → j = q) →
      L + g v ∉ (C.gates[q]).inputs := by
    intro u hu v hv huv q hq hq_sole hgv_in
    have hq_op := (hM (C.gates[q]) (List.getElem_mem hq)).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq_op
    rcases hq_op with hq_and | hq_or
    · have hcard_er : 0 < ((R.erase u).erase v).card := by
        have h1 : (R.erase u).card = R.card - 1 := Finset.card_erase_of_mem hu
        have hv1 : v ∈ R.erase u := Finset.mem_erase.2 ⟨Ne.symm huv, hv⟩
        have h2 : ((R.erase u).erase v).card = (R.erase u).card - 1 := Finset.card_erase_of_mem hv1
        omega
      obtain ⟨w, hw_er⟩ := Finset.card_pos.1 hcard_er
      have hwv : w ≠ v := (Finset.mem_erase.1 hw_er).1
      have hw_er1 := (Finset.mem_erase.1 hw_er).2
      have hwu : w ≠ u := (Finset.mem_erase.1 hw_er1).1
      have hw : w ∈ R := (Finset.mem_erase.1 hw_er1).2
      obtain ⟨c, hGu, hGv, hGw⟩ := hTriple u hu v hv w hw huv (Ne.symm hwu) (Ne.symm hwv)
      have hwgv : val C (rowInput base w c) (L + g v) = true := by
        by_contra hfalse
        have hwgvF : val C (rowInput base w c) (L + g v) = false := Bool.eq_false_iff.2 hfalse
        have hle1 := val_le_of_exceptions L C hM hW (rowInput base u c) (rowInput base w c)
          (by rw [length_rowInput, hlen]) (by rw [length_rowInput, hlen])
          ({u, L + g u} ∪ {k : ℕ | L + q ≤ k})
          (by
            intro i hiL hiE hx
            have hiu : i ≠ u := fun h => hiE (Or.inl (Or.inl h))
            rw [rowInput_getD base hlen u (hRL u hu) c i, ite_eq_right hiu] at hx
            rw [rowInput_getD base hlen w (hRL w hw) c i]
            split_ifs
            · rfl
            · exact hx)
          (by
            intro j hj hjE
            have hjg : j ≠ g u := fun h => hjE (Or.inl (Set.mem_insert_of_mem _ (by simp [h])))
            have hjq : j < q := by
              have hnotge : ¬ (L + q ≤ L + j) := fun h => hjE (Or.inr h)
              omega
            right
            intro i hi hmem
            rcases hmem with (h | h) | hge
            · rw [h] at hi; exact hjg (hg_sole u hu j hj hi)
            · simp only [Set.mem_singleton_iff] at h
              rw [h] at hi
              exact (Nat.ne_of_lt hjq) (hq_sole j hj hi)
            · have hilt := hW.1 j hj i hi
              change L + q ≤ i at hge
              omega)
        have hgv_lt_q : L + g v < L + q := hW.1 q hq (L + g v) hgv_in
        have hgv_notE : L + g v ∉ ({u, L + g u} ∪ {k : ℕ | L + q ≤ k} : Set ℕ) := by
          intro h
          rcases h with (h | h) | h
          · have := hRL u hu; omega
          · simp only [Set.mem_singleton_iff] at h
            exact huv (hg_inj hu hv (by omega))
          · exact Nat.not_le_of_lt hgv_lt_q h
        have hugvF : val C (rowInput base u c) (L + g v) = false := by
          by_contra hnt
          have ht : val C (rowInput base u c) (L + g v) = true := Bool.eq_true_of_not_eq_false hnt
          have := hle1 (L + g v) hgv_notE ht
          rw [hwgvF] at this
          exact Bool.noConfusion this
        have huqF : val C (rowInput base u c) (L + q) = false :=
          val_gate_and_false C hW (rowInput base u c) (by rw [length_rowInput, hlen])
            q hq hq_and (L + g v) hgv_in hugvF
        have hle2 := val_le_of_exceptions L C hM hW (rowInput base u c) (rowInput base w c)
          (by rw [length_rowInput, hlen]) (by rw [length_rowInput, hlen]) {u, L + g u}
          (by
            intro i _ hiE hx
            have hiu : i ≠ u := fun h => hiE (Or.inl h)
            rw [rowInput_getD base hlen u (hRL u hu) c i, ite_eq_right hiu] at hx
            rw [rowInput_getD base hlen w (hRL w hw) c i]
            split_ifs
            · rfl
            · exact hx)
          (by
            intro j hj hjE
            have hjg : j ≠ g u := fun h => hjE (Set.mem_insert_of_mem _ (by simp [h]))
            by_cases hjq : j = q
            · left
              intro hqT
              rw [hjq, huqF] at hqT
              exact Bool.noConfusion hqT
            · right
              intro i hi hmem
              rcases hmem with h | h
              · rw [h] at hi; exact hjg (hg_sole u hu j hj hi)
              · simp only [Set.mem_singleton_iff] at h
                rw [h] at hi
                exact hjq (hq_sole j hj hi))
        have houtE : C.output ∉ ({u, L + g u} : Set ℕ) := by
          intro h
          rcases h with h | h
          · exact no_row_output base hlen R hRL G hcard2 hPair C hEval u hu h
          · exact hg_not_out u hu h
        have hres := hle2 C.output houtE (by rw [val_eq_eval, hEval u hu c, hGu])
        rw [val_eq_eval, hEval w hw c, hGw] at hres
        exact Bool.noConfusion hres
      have hle3 := val_le_of_exceptions L C hM hW (rowInput base v c) (rowInput base w c)
        (by rw [length_rowInput, hlen]) (by rw [length_rowInput, hlen]) {v}
        (by
          intro i _ hiE hx
          have hiv : i ≠ v := by simpa using hiE
          rw [rowInput_getD base hlen v (hRL v hv) c i, ite_eq_right hiv] at hx
          rw [rowInput_getD base hlen w (hRL w hw) c i]
          split_ifs
          · rfl
          · exact hx)
        (by
          intro j hj _
          by_cases hjv : j = g v
          · left
            intro _
            rw [hjv]
            exact hwgv
          · right
            intro i hi hmem
            have hiv : i = v := by simpa using hmem
            rw [hiv] at hi
            exact hjv (hg_sole v hv j hj hi))
      have houtE : C.output ∉ ({v} : Set ℕ) := by
        simpa using no_row_output base hlen R hRL G hcard2 hPair C hEval v hv
      have hres := hle3 C.output houtE (by rw [val_eq_eval, hEval v hv c, hGv])
      rw [val_eq_eval, hEval w hw c, hGw] at hres
      exact Bool.noConfusion hres
    · obtain ⟨c, hGu, hGv⟩ := hPair u hu v hv huv
      have hle := val_le_of_exceptions L C hM hW (rowInput base u c) (rowInput base v c)
        (by rw [length_rowInput, hlen]) (by rw [length_rowInput, hlen]) {u, L + g u}
        (by
          intro i _ hiE hx
          have hiu : i ≠ u := fun h => hiE (Or.inl h)
          rw [rowInput_getD base hlen u (hRL u hu) c i, ite_eq_right hiu] at hx
          rw [rowInput_getD base hlen v (hRL v hv) c i]
          split_ifs
          · rfl
          · exact hx)
        (by
          intro j hj hjE
          have hjg : j ≠ g u := fun h => hjE (Set.mem_insert_of_mem _ (by simp [h]))
          by_cases hjq : j = q
          · left
            intro _
            rw [hjq]
            exact val_gate_or_true C hW (rowInput base v c) (by rw [length_rowInput, hlen])
              q hq hq_or (L + g v) hgv_in (hval_gu v hv c)
          · right
            intro i hi hmem
            rcases hmem with h | h
            · rw [h] at hi; exact hjg (hg_sole u hu j hj hi)
            · simp only [Set.mem_singleton_iff] at h
              rw [h] at hi
              exact hjq (hq_sole j hj hi))
      have houtE : C.output ∉ ({u, L + g u} : Set ℕ) := by
        intro h
        rcases h with h | h
        · exact no_row_output base hlen R hRL G hcard2 hPair C hEval u hu h
        · exact hg_not_out u hu h
      have hres := hle C.output houtE (by rw [val_eq_eval, hEval u hu c, hGu])
      rw [val_eq_eval, hEval v hv c, hGv] at hres
      exact Bool.noConfusion hres
  set U : Finset ℕ := R.image g
  have hU_sub : U ⊆ Finset.range C.gates.length := by
    intro j hj
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hj
    exact Finset.mem_range.2 (hg_lt r hr)
  have hU_card : U.card = R.card := Finset.card_image_of_injOn hg_inj
  set Q : Finset ℕ := Finset.range C.gates.length \ U
  have hQ_card : Q.card + U.card = C.gates.length := by
    have := Finset.card_sdiff_add_card_eq_card hU_sub
    simpa [Q] using this
  let inputsOf : ℕ → List ℕ := fun j => (C.gates.getD j ⟨GateOp.or, []⟩).inputs
  have hinputsOf : ∀ j (hj : j < C.gates.length), inputsOf j = (C.gates[j]).inputs := by
    intro j hj
    simp [inputsOf, List.getD_eq_getElem?_getD, hj]
  let slotCount : ℕ → ℕ := fun r => ∑ j ∈ Q, (inputsOf j).count (L + g r)
  have hslot_pos : ∀ r ∈ R, 1 ≤ slotCount r := by
    intro r hr
    obtain ⟨j, hj, hmem⟩ := hg_has_reader r hr
    have hjQ : j ∈ Q := by
      rw [Finset.mem_sdiff, Finset.mem_range]
      refine ⟨hj, ?_⟩
      intro hjU
      obtain ⟨v, hv, hgv⟩ := Finset.mem_image.1 hjU
      subst hgv
      exact hg_no_feed_U r hr v hv hmem
    have hcnt : 1 ≤ (inputsOf j).count (L + g r) := by
      rw [hinputsOf j hj]
      exact List.count_pos_iff.2 hmem
    exact le_trans hcnt
      (Finset.single_le_sum (f := fun k => (inputsOf k).count (L + g r)) (fun _ _ => Nat.zero_le _) hjQ)
  set B : Finset ℕ := R.filter fun r => slotCount r = 1
  set A : Finset ℕ := R.filter fun r => 2 ≤ slotCount r
  have hAB_disj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro r hA hB
    simp only [A, B, Finset.mem_filter] at hA hB
    omega
  have hAB_union : A ∪ B = R := by
    ext r
    simp only [Finset.mem_union, A, B, Finset.mem_filter]
    constructor
    · rintro (⟨hr, _⟩ | ⟨hr, _⟩) <;> exact hr
    · intro hr
      have hpos := hslot_pos r hr
      by_cases h1 : slotCount r = 1
      · exact Or.inr ⟨hr, h1⟩
      · exact Or.inl ⟨hr, by omega⟩
  have hAB_card : A.card + B.card = R.card := by
    rw [← Finset.card_union_of_disjoint hAB_disj, hAB_union]
  have hB_exists : ∀ r ∈ B, ∃ q ∈ Q, (inputsOf q).count (L + g r) = 1 ∧
      ∀ j ∈ Q, j ≠ q → (inputsOf j).count (L + g r) = 0 := by
    intro r hr
    have hsc : ∑ j ∈ Q, (inputsOf j).count (L + g r) = 1 := (Finset.mem_filter.1 hr).2
    have hpos : 0 < ∑ j ∈ Q, (inputsOf j).count (L + g r) := by omega
    obtain ⟨q, hqQ, hqpos⟩ := Finset.exists_ne_zero_of_sum_ne_zero (Nat.ne_of_gt hpos)
    have hq_le : (inputsOf q).count (L + g r) ≤ 1 := by
      have := Finset.single_le_sum (f := fun k => (inputsOf k).count (L + g r))
        (fun _ _ => Nat.zero_le _) hqQ
      exact le_trans this (le_of_eq hsc)
    have hq1 : (inputsOf q).count (L + g r) = 1 := by omega
    refine ⟨q, hqQ, hq1, ?_⟩
    intro j hjQ hjne
    have hsum2 := Finset.add_sum_erase Q (fun k => (inputsOf k).count (L + g r)) hqQ
    have hrest0 : ∑ k ∈ Q.erase q, (inputsOf k).count (L + g r) = 0 := by omega
    have hj_er : j ∈ Q.erase q := Finset.mem_erase.2 ⟨hjne, hjQ⟩
    have := Finset.single_le_sum (f := fun k => (inputsOf k).count (L + g r))
      (fun _ _ => Nat.zero_le _) hj_er
    omega
  classical
  let qOf : ℕ → ℕ := fun r => if hr : r ∈ B then Classical.choose (hB_exists r hr) else 0
  have hqOf_mem : ∀ r ∈ B, qOf r ∈ Q := by
    intro r hr
    simp only [qOf, dite_eq_left hr]
    exact (Classical.choose_spec (hB_exists r hr)).1
  have hqOf_lt : ∀ r ∈ B, qOf r < C.gates.length := by
    intro r hr
    exact Finset.mem_range.1 (Finset.mem_sdiff.1 (hqOf_mem r hr)).1
  have hqOf_in : ∀ r (hr : r ∈ B), L + g r ∈ (C.gates[qOf r]'(hqOf_lt r hr)).inputs := by
    intro r hr
    have h1 : (inputsOf (qOf r)).count (L + g r) = 1 := by
      simp only [qOf, dite_eq_left hr]
      exact (Classical.choose_spec (hB_exists r hr)).2.1
    rw [hinputsOf (qOf r) (hqOf_lt r hr)] at h1
    exact List.count_pos_iff.1 (by omega)
  have hqOf_sole : ∀ r ∈ B, ∀ j (hj : j < C.gates.length),
      L + g r ∈ (C.gates[j]).inputs → j = qOf r := by
    intro r hr j hj hmem
    have hrR : r ∈ R := (Finset.mem_filter.1 hr).1
    have hjQ : j ∈ Q := by
      rw [Finset.mem_sdiff, Finset.mem_range]
      refine ⟨hj, ?_⟩
      intro hjU
      obtain ⟨v, hv, hgv⟩ := Finset.mem_image.1 hjU
      subst hgv
      exact hg_no_feed_U r hrR v hv hmem
    by_contra hjne
    have h0 : (inputsOf j).count (L + g r) = 0 := by
      have hspec := Classical.choose_spec (hB_exists r hr)
      have hqeq : qOf r = Classical.choose (hB_exists r hr) := by simp [qOf, dite_eq_left hr]
      rw [hqeq] at hjne
      exact hspec.2.2 j hjQ hjne
    rw [hinputsOf j hj] at h0
    have hpos := List.count_pos_iff.2 hmem
    omega
  have hqOf_no_other : ∀ r (hr : r ∈ B) v (hv : v ∈ R), r ≠ v →
      L + g v ∉ (C.gates[qOf r]'(hqOf_lt r hr)).inputs := by
    intro r hr v hv hrv
    exact hmiracle r (Finset.mem_filter.1 hr).1 v hv hrv (qOf r) (hqOf_lt r hr) (hqOf_sole r hr)
  have hqOf_inj : Set.InjOn qOf B := by
    intro u hu v hv heq
    by_contra hne
    have hv_in := hqOf_in v hv
    have hvR : v ∈ R := (Finset.mem_filter.1 hv).1
    have hno := hqOf_no_other u hu v hvR hne
    have hv_in' : L + g v ∈ (C.gates[qOf u]'(hqOf_lt u hu)).inputs := by
      simpa [heq] using hv_in
    exact hno hv_in'
  set QB : Finset ℕ := B.image qOf
  have hQB_sub : QB ⊆ Q := by
    intro j hj
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hj
    exact hqOf_mem r hr
  have hQB_card : QB.card = B.card := Finset.card_image_of_injOn hqOf_inj
  set QA : Finset ℕ := Q \ QB
  have hQA_card : QA.card + B.card = Q.card := by
    have := Finset.card_sdiff_add_card_eq_card hQB_sub
    rw [hQB_card] at this
    exact this
  have hA_in_QA : ∀ v ∈ A, 2 ≤ ∑ j ∈ QA, (inputsOf j).count (L + g v) := by
    intro v hvA
    have hvR : v ∈ R := (Finset.mem_filter.1 hvA).1
    have hsc : 2 ≤ slotCount v := (Finset.mem_filter.1 hvA).2
    have hzero : ∀ j ∈ QB, (inputsOf j).count (L + g v) = 0 := by
      intro j hjQB
      obtain ⟨r, hrB, rfl⟩ := Finset.mem_image.1 hjQB
      have hrv : r ≠ v := by
        intro heq
        subst heq
        exact Finset.disjoint_left.1 hAB_disj hvA hrB
      rw [hinputsOf (qOf r) (hqOf_lt r hrB)]
      exact List.count_eq_zero.2 (hqOf_no_other r hrB v hvR hrv)
    have hsplit : ∑ j ∈ QA, (inputsOf j).count (L + g v) +
        ∑ j ∈ QB, (inputsOf j).count (L + g v) = slotCount v := by
      simpa [QA, slotCount] using Finset.sum_sdiff hQB_sub (f := fun j => (inputsOf j).count (L + g v))
    have hsum0 : ∑ j ∈ QB, (inputsOf j).count (L + g v) = 0 :=
      Finset.sum_eq_zero hzero
    omega
  have hlow : 2 * A.card ≤ ∑ v ∈ A, ∑ j ∈ QA, (inputsOf j).count (L + g v) := by
    have h1 := Finset.sum_le_sum hA_in_QA
    simpa [mul_comm] using h1
  have hup : ∑ j ∈ QA, ∑ v ∈ A, (inputsOf j).count (L + g v) ≤ 2 * QA.card := by
    have h1 : ∀ j ∈ QA, ∑ v ∈ A, (inputsOf j).count (L + g v) ≤ 2 := by
      intro j hjQA
      have hjlt : j < C.gates.length :=
        Finset.mem_range.1 (Finset.mem_sdiff.1 (Finset.mem_sdiff.1 hjQA).1).1
      have hinjA : Set.InjOn (fun v => L + g v) A := by
        intro x hx y hy hxy
        dsimp only at hxy
        exact hg_inj (Finset.mem_filter.1 hx).1 (Finset.mem_filter.1 hy).1 (by omega)
      have hle := sum_count_le_length (inputsOf j) A (fun v => L + g v) hinjA
      have hlen2 : (inputsOf j).length ≤ 2 := by
        rw [hinputsOf j hjlt]
        exact (hM (C.gates[j]) (List.getElem_mem hjlt)).2
      exact le_trans hle hlen2
    have h2 := Finset.sum_le_sum h1
    simpa [mul_comm] using h2
  rw [Finset.sum_comm] at hlow
  have hleA : A.card ≤ QA.card := by omega
  change 2 * R.card ≤ C.gates.length
  omega

private theorem rowInput_eq_oneHot {n m p : ℕ} (code : Fin m → Fin p → Bool)
    (u : Fin n) (c : Fin m) :
    rowInput (fun c' => List.replicate n false ++ List.ofFn (code c')) u.val c =
      List.ofFn (fun i : Fin n => decide (i = u)) ++ List.ofFn (code c) := by
  apply List.ext_getElem
  · simp [rowInput]
  · intro i h1 h2
    have hl1 : (List.replicate n false ++ List.ofFn (code c)).length = n + p := by simp
    have hi : i < n + p := by simpa [rowInput] using h1
    have hget : (rowInput (fun c' => List.replicate n false ++ List.ofFn (code c')) u.val c)[i] =
        (rowInput (fun c' => List.replicate n false ++ List.ofFn (code c')) u.val c).getD i false := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]; rfl
    have hget2 : (List.ofFn (fun i : Fin n => decide (i = u)) ++ List.ofFn (code c))[i] =
        (List.ofFn (fun i : Fin n => decide (i = u)) ++ List.ofFn (code c)).getD i false := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]; rfl
    rw [hget, hget2, rowInput_getD (L := n + p) _ (fun _ => by simp) u.val (by omega) c i]
    by_cases hin : i < n
    · rw [List.getD_append _ _ _ _ (by simpa using hin),
        List.getD_append _ _ _ _ (by simpa using hin)]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate, hin, ↓reduceIte,
        Option.getD_some, List.getElem?_ofFn, Fin.ext_iff]
      by_cases hiu : i = u.val <;> simp [hiu]
    · have hiu : i ≠ u.val := by omega
      rw [ite_eq_right hiu, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by simp; omega),
        List.getElem?_append_right (by simp; omega)]
      simp only [List.length_replicate, List.length_ofFn]

private def Separates {n m} (G : Fin n→Fin m→Bool) :=
  ∀ u v w : Fin n, u≠v → u≠w → v≠w → ∃ c, G u c=true ∧ G v c=true ∧ G w c=false

private theorem incomparable {n m} {G : Fin n→Fin m→Bool} (hn : 3≤n) (sep : Separates G)
    (u v : Fin n) (uv : u≠v) : ∃ c,G u c=true ∧ G v c=false := by
  classical
  have third : ∃w : Fin n,w≠u ∧ w≠v := by
    by_contra! missing
    have sub : (Finset.univ : Finset (Fin n))⊆{u,v} := by
      intro w _
      by_cases eq : w=u
      · simp [eq]
      · simp [missing w eq]
    have nle:=Finset.card_le_card sub
    simp [uv] at nle
    omega
  obtain ⟨w,wu,wv⟩:=third
  obtain ⟨c,on,_,off⟩:=sep u w v wu.symm uv wv
  exact ⟨c,on,off⟩

private theorem three_rows {m s} (G : Fin 3→Fin m→Bool) (sep : Separates G)
    (rep : Represents.RepSizeAtMost G s) : 6≤s := by
  classical
  obtain ⟨a,a0,a1,a2⟩:=sep 0 1 2 (by decide) (by decide) (by decide)
  obtain ⟨b,b0,b2,b1⟩:=sep 0 2 1 (by decide) (by decide) (by decide)
  obtain ⟨c,c1,c2,c0⟩:=sep 1 2 0 (by decide) (by decide) (by decide)
  have ab : a≠b := fun h=>Bool.noConfusion ((h ▸ a1).symm.trans b1)
  have ac : a≠c := fun h=>Bool.noConfusion ((h ▸ a0).symm.trans c0)
  have bc : b≠c := fun h=>Bool.noConfusion ((h ▸ b0).symm.trans c0)
  let L:=Finset.univ.filter (fun i : Fin 3=>∃j,G i j=true ∧ ∃k,G k j=false)
  let R:=Finset.univ.filter (fun j : Fin m=>∃i,G i j=true ∧ ∃k,G i k=false)
  have rows : L=Finset.univ := by
    ext i
    simp only [L,Finset.mem_filter,Finset.mem_univ,true_and,iff_true]
    fin_cases i
    · exact ⟨a,a0,2,a2⟩
    · exact ⟨a,a1,2,a2⟩
    · exact ⟨b,b2,1,b1⟩
  have cols : ({a,b,c} : Finset (Fin m))⊆R := by
    intro j hj
    simp only [Finset.mem_insert,Finset.mem_singleton] at hj
    simp only [R,Finset.mem_filter,Finset.mem_univ,true_and]
    rcases hj with rfl|rfl|rfl
    · exact ⟨0,a0,c,c0⟩
    · exact ⟨0,b0,c,c0⟩
    · exact ⟨1,c1,b,b1⟩
  have colCount:=Finset.card_le_card cols
  simp [ab,ac,bc] at colCount
  have low : L.card+R.card≤s := RepPath.path 3 m s G 0 1 a b a0 b0 a1 b1 ⟨c,c0⟩ ⟨2,a2⟩ rep
  rw [rows,Finset.card_univ,Fintype.card_fin] at low
  omega

private theorem charge {n m} (G : Fin n→Fin m→Bool) (hn : 3≤n) (sep : Separates G)
    (C : Circuit) (hM : Monotone2 C) (hB : NestedCover.ReadsBack (n+m) C)
    (hEval : Represents.Represents G C)
    (data : ∀u : Fin n, NestedCover.readsIn C (Finset.range C.size) u.val=1 ∧
      ∃ (j : Fin C.gates.length) (w : ℕ), (C.gates.get j).op=GateOp.or ∧
      ((C.gates.get j).inputs=[u.val,w] ∨ (C.gates.get j).inputs=[w,u.val])) :
    2*n≤C.size := by
  classical
  have hPair:=incomparable hn sep
  have hTriple:=sep
  let p:=m
  let code (c b : Fin m):=decide (b=c)
  let base : Fin m → List Bool := fun c => List.replicate n false ++ List.ofFn (code c)
  have hlen : ∀ c, (base c).length = n + p := by intro c; simp [base,p]
  let R : Finset ℕ := Finset.range n
  have hRL : ∀ r ∈ R, r < n + p := by
    intro r hr
    have := Finset.mem_range.1 hr
    omega
  have hR0 : ∀ r ∈ R, ∀ c, (base c).getD r false = false := by
    intro r hr c
    have hlt : r < n := Finset.mem_range.1 hr
    simp only [base]
    rw [List.getD_append _ _ _ _ (by simpa using hlt)]
    simp [List.getD_eq_getElem?_getD, hlt]
  let G' : ℕ → Fin m → Bool := fun r c => if h : r < n then G ⟨r, h⟩ c else false
  have hPair' : ∀ u ∈ R, ∀ v ∈ R, u ≠ v → ∃ c : Fin m, G' u c = true ∧ G' v c = false := by
    intro u hu v hv huv
    have hun : u < n := Finset.mem_range.1 hu
    have hvn : v < n := Finset.mem_range.1 hv
    have hne : (⟨u, hun⟩ : Fin n) ≠ ⟨v, hvn⟩ := fun h => huv (congrArg Fin.val h)
    obtain ⟨c, h1, h2⟩ := hPair ⟨u, hun⟩ ⟨v, hvn⟩ hne
    exact ⟨c, by simp [G', hun, h1], by simp [G', hvn, h2]⟩
  have hTriple' : ∀ u ∈ R, ∀ v ∈ R, ∀ w ∈ R, u ≠ v → u ≠ w → v ≠ w →
      ∃ c : Fin m, G' u c = true ∧ G' v c = true ∧ G' w c = false := by
    intro u hu v hv w hw huv huw hvw
    have hun : u < n := Finset.mem_range.1 hu
    have hvn : v < n := Finset.mem_range.1 hv
    have hwn : w < n := Finset.mem_range.1 hw
    obtain ⟨c, h1, h2, h3⟩ := hTriple ⟨u, hun⟩ ⟨v, hvn⟩ ⟨w, hwn⟩
      (fun h => huv (congrArg Fin.val h))
      (fun h => huw (congrArg Fin.val h))
      (fun h => hvw (congrArg Fin.val h))
    exact ⟨c, by simp [G', hun, h1], by simp [G', hvn, h2], by simp [G', hwn, h3]⟩
  have hEval' : ∀ u ∈ R, ∀ c : Fin m,
      C.eval (rowInput base u c) = G' u c := by
    intro u hu c
    have hun : u < n := Finset.mem_range.1 hu
    simp only [G', dite_eq_left hun]
    rw [show rowInput base u c =
        rowInput base (⟨u, hun⟩ : Fin n).val c from rfl,
      rowInput_eq_oneHot code ⟨u, hun⟩ c]
    exact hEval ⟨u, hun⟩ c
  have ga (j : ℕ) (hj : j<C.gates.length) : NestedCover.gateAt C j=C.gates[j] := by
    exact List.getD_eq_getElem _ _ hj
  have hW : WellFormed (n+m) C := by
    refine ⟨fun j hj i hi=>hB j hj i (ga j hj ▸ hi),?_⟩
    by_contra! past
    let u : Fin n:=⟨0,by omega⟩
    let v : Fin n:=⟨1,by omega⟩
    obtain ⟨c,on,_⟩:=hPair u v (by simp [u,v,Fin.ext_iff])
    have blank:=val_out_of_bounds C (Represents.oneEach u c) C.output (by simpa [Represents.oneEach] using past)
    rw [val_eq_eval,hEval u c,on] at blank
    contradiction
  choose reader partner isOr shape using fun u=>(data u).2
  let g (r : ℕ):=if hr : r<n then (reader ⟨r,hr⟩).val else 0
  have ltg (r) (hr : r∈R) : g r<C.gates.length := by
    have hrn:=Finset.mem_range.mp hr
    simp [g,hrn]
  have hit (r) (hr : r∈R) : r∈(C.gates[g r]'(ltg r hr)).inputs := by
    have hrn:=Finset.mem_range.mp hr
    let u : Fin n:=⟨r,hrn⟩
    have h : r∈(C.gates.get (reader u)).inputs := by
      rcases shape u with a|a <;> rw [a] <;> simp [u]
    simpa [g,hrn,u] using h
  have unique (r) (hr : r∈R) (j) (hj : j<C.gates.length) (hm : r∈(C.gates[j]).inputs) :
      j=g r := by
    have hrn:=Finset.mem_range.mp hr
    exact PEqualNP.Outside.L_meta_25491_aux.only_reader C r j (g r) hj (ltg r hr)
      (data ⟨r,hrn⟩).1 (ga j hj ▸ hm) (ga _ (ltg r hr) ▸ hit r hr)
  have gateOr (r) (hr : r∈R) : (C.gates[g r]'(ltg r hr)).op=GateOp.or := by
    have hrn:=Finset.mem_range.mp hr
    simpa [g,hrn] using isOr ⟨r,hrn⟩
  have lower:=case_private_row_ors base hlen R hRL hR0 G' (by simpa [R] using hn)
    hPair' hTriple' C hM hW hEval' g ltg hit unique gateOr
  simpa [R] using lower

private theorem lower_rows (n : ℕ) : ∀m s (G : Fin n→Fin m→Bool),
    3≤n → Separates G → Represents.RepSizeAtMost G s → 2*n≤s := by
  induction n with
  | zero=>intro m s G hn;omega
  | succ n ih=>
    intro m s G hn sep rep
    by_cases base : n=2
    · subst n
      exact three_rows G sep rep
    · have small : 3≤n := by omega
      rcases PEqualNP.Outside.L_meta_25491 n m s G (by omega) (incomparable hn sep) rep with
        ⟨r,t,smaller,newRep⟩|⟨C,hM,size,hB,hEval,data⟩
      · have sub : Separates (fun a c=>G (r.succAbove a) c) := by
          intro u v w uv uw vw
          exact sep _ _ _ (Fin.succAbove_right_injective.ne uv) (Fin.succAbove_right_injective.ne uw)
            (Fin.succAbove_right_injective.ne vw)
        have rest:=ih m t _ small sub newRep
        omega
      · exact (charge G hn sep C hM hB hEval data).trans size

end PEqualNP.Outside.L_meta_25529_aux

theorem PEqualNP.Outside.L_meta_25529 : (∀ (n m s : ℕ) (G : Fin n → Fin m → Bool),
  3 ≤ n →
  (∀ u v w : Fin n, u ≠ v → u ≠ w → v ≠ w →
    ∃ c : Fin m, G u c = true ∧ G v c = true ∧ G w c = false) →
  PEqualNP.Represents.RepSizeAtMost G s →
  2 * n ≤ s) :=
  PEqualNP.Outside.L_meta_25529_aux.lower_rows
