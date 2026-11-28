import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1351_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open Classical

-- =========================================================================
-- Part 1: Circuit wire semantics, output-cone frontier, and OR-chain builder
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

private lemma exists_output_frontier {N : ℕ} (C : Circuit) (hfan : FanInTwo C)
    (hrb : ReadsBack N C) (hout : C.output < N + C.size) :
    ∃ F : Finset ℕ,
      (∀ w ∈ F, w < N) ∧ F.card ≤ C.size + 1 ∧
      ∀ inp1 inp2 : List Bool, inp1.length = N → inp2.length = N →
        (∀ i ∈ F, inp1.getD i false = inp2.getD i false) →
        C.eval inp1 = C.eval inp2 := by
  suffices hstep : ∀ (m : ℕ), m ≤ C.gates.length →
      ∀ F : Finset ℕ, (∀ w ∈ F, w < N + m) →
        ∃ F0 : Finset ℕ,
          (∀ w ∈ F0, w < N) ∧ F0.card ≤ F.card + m ∧
          ∀ inp1 inp2 : List Bool, inp1.length = N → inp2.length = N →
            (∀ i ∈ F0, inp1.getD i false = inp2.getD i false) →
            ∀ w ∈ F, (C.wires inp1).getD w false = (C.wires inp2).getD w false by
    rcases hstep C.gates.length (le_refl _) {C.output} (fun w hw => by
        simp only [Finset.mem_singleton] at hw; subst hw; exact hout) with
      ⟨F0, hF0_lt, hF0_card, hF0_eq⟩
    refine ⟨F0, hF0_lt, by simp only [Finset.card_singleton] at hF0_card; unfold Circuit.size; omega, ?_⟩
    intro inp1 inp2 hl1 hl2 hagree
    exact hF0_eq inp1 inp2 hl1 hl2 hagree C.output (Finset.mem_singleton_self _)
  intro m
  induction m with
  | zero =>
    intro _ F hF
    refine ⟨F, fun w hw => by have := hF w hw; omega, by omega, ?_⟩
    intro inp1 inp2 hl1 hl2 hagree w hw
    have hwN : w < N := by have := hF w hw; omega
    unfold Circuit.wires
    rw [wires_foldl_getD_lt C.gates inp1 w (by omega),
        wires_foldl_getD_lt C.gates inp2 w (by omega)]
    exact hagree w hw
  | succ m ih =>
    intro hm F hF
    by_cases hmem : N + m ∈ F
    · set F' : Finset ℕ := F.erase (N + m) ∪ (gateAt C m).inputs.toFinset
      have hF'_lt : ∀ w ∈ F', w < N + m := by
        intro w hw
        rcases Finset.mem_union.mp hw with h1 | h2
        · rcases Finset.mem_erase.mp h1 with ⟨hne, hwF⟩
          have := hF w hwF; omega
        · exact hrb m (by omega) w (List.mem_toFinset.mp h2)
      have hgm : gateAt C m ∈ C.gates := by
        have hm' : m < C.gates.length := by omega
        simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm', Option.getD_some]
        exact List.getElem_mem hm'
      have hin_card : (gateAt C m).inputs.toFinset.card ≤ 2 :=
        le_trans (List.toFinset_card_le _) (hfan _ hgm).2
      have hF'_card : F'.card ≤ F.card + 1 := by
        have h1 : F'.card ≤ (F.erase (N + m)).card + (gateAt C m).inputs.toFinset.card :=
          Finset.card_union_le _ _
        have h2 : (F.erase (N + m)).card + 1 = F.card := Finset.card_erase_add_one hmem
        omega
      rcases ih (by omega) F' hF'_lt with ⟨F0, hF0_lt, hF0_card, hF0_eq⟩
      refine ⟨F0, hF0_lt, by omega, ?_⟩
      intro inp1 inp2 hl1 hl2 hagree w hw
      by_cases hwm : w = N + m
      · subst hwm
        have h1 := wires_getD_gate C inp1 m (by omega) (by rw [hl1]; exact hrb)
        have h2 := wires_getD_gate C inp2 m (by omega) (by rw [hl2]; exact hrb)
        rw [hl1] at h1; rw [hl2] at h2
        rw [h1, h2]
        congr 1
        apply List.map_congr_left
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
      exact ⟨F0, hF0_lt, by omega, hF0_eq⟩

private lemma exists_or_chain {M : ℕ} (ws : List ℕ) (hws : ∀ v ∈ ws, v < M) :
    ∃ C : Circuit,
      FanInTwo C ∧ ReadsBack (M + 2) C ∧ C.output < (M + 2) + C.size ∧
      C.size = ws.length - 1 ∧
      (∀ g ∈ C.gates, g.op = GateOp.or) ∧
      (∀ v < M, (C.output = v ∨ ∃ g ∈ C.gates, v ∈ g.inputs) ↔ v ∈ ws) ∧
      ∀ inp : List Bool, inp.length = M + 2 → inp.getD M false = false →
        C.eval inp = ws.any (fun v => inp.getD v false) := by
  induction ws with
  | nil =>
    refine ⟨⟨[], M⟩, (fun _ h => by cases h), (fun _ h => by simp at h), by simp [Circuit.size],
      by simp [Circuit.size], (fun _ h => by cases h), ?_, ?_⟩
    · intro v hv
      simp only [List.not_mem_nil, iff_false, not_or, not_exists]
      exact ⟨by omega, fun _ h => h.1⟩
    · intro inp hinp hM0
      simp only [Circuit.eval, Circuit.wires, List.foldl_nil, List.any_nil]
      exact hM0
  | cons w rest ih =>
    cases rest with
    | nil =>
      have hw : w < M := hws w (List.mem_cons_self ..)
      refine ⟨⟨[], w⟩, (fun _ h => by cases h), (fun _ h => by simp at h), by simp [Circuit.size]; omega,
        by simp [Circuit.size], (fun _ h => by cases h), ?_, ?_⟩
      · intro v hv
        simp only [List.mem_singleton, List.not_mem_nil, false_and, exists_false, or_false]
        exact eq_comm
      · intro inp _ _
        simp [Circuit.eval, Circuit.wires]
    | cons w2 rest2 =>
      rcases ih (fun v hv => hws v (List.mem_cons_of_mem w hv)) with
        ⟨C1, hfan1, hrb1, hout1, hsz1, hop1, huse1, hev1⟩
      have hw : w < M := hws w (List.mem_cons_self ..)
      let gNew : Gate := ⟨GateOp.or, [w, C1.output]⟩
      let C2 : Circuit := ⟨C1.gates ++ [gNew], (M + 2) + C1.gates.length⟩
      have hC2_sz : C2.size = (w :: w2 :: rest2).length - 1 := by
        simp only [C2, Circuit.size, List.length_append, List.length_cons, List.length_nil] at hsz1 ⊢
        omega
      have hC2_fan : FanInTwo C2 := by
        intro g hg
        rcases List.mem_append.mp hg with h1 | h2
        · exact hfan1 g h1
        · simp only [List.mem_singleton] at h2; subst h2
          exact ⟨by simp [gNew], by simp [gNew]⟩
      have hC2_rb : ReadsBack (M + 2) C2 := by
        intro j hj i hi
        simp only [C2, List.length_append, List.length_singleton] at hj
        by_cases hlt : j < C1.gates.length
        · have hget : gateAt C2 j = gateAt C1 j := by
            simp only [gateAt, C2, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
          rw [hget] at hi
          exact hrb1 j hlt i hi
        · have heq : j = C1.gates.length := by omega
          subst heq
          have hget : gateAt C2 C1.gates.length = gNew := by
            simp only [gateAt, C2, List.getD_eq_getElem?_getD,
              List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
          rw [hget] at hi
          simp only [gNew, List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · omega
          · exact hout1
      have hC2_out : C2.output < (M + 2) + C2.size := by
        simp only [C2, Circuit.size, List.length_append, List.length_singleton]; omega
      have hC2_op : ∀ g ∈ C2.gates, g.op = GateOp.or := by
        intro g hg
        rcases List.mem_append.mp hg with h1 | h2
        · exact hop1 g h1
        · simp only [List.mem_singleton] at h2; subst h2; rfl
      have hC2_use : ∀ v < M, (C2.output = v ∨ ∃ g ∈ C2.gates, v ∈ g.inputs) ↔ v ∈ w :: w2 :: rest2 := by
        intro v hv
        have hne_out : C2.output ≠ v := by dsimp [C2]; omega
        rw [or_iff_right hne_out]
        constructor
        · rintro ⟨g, hg, hvg⟩
          rcases List.mem_append.mp hg with h1 | h2
          · exact List.mem_cons_of_mem w ((huse1 v hv).mp (Or.inr ⟨g, h1, hvg⟩))
          · simp only [List.mem_singleton] at h2; subst h2
            simp only [gNew, List.mem_cons, List.not_mem_nil, or_false] at hvg
            rcases hvg with hvw | hvout
            · subst hvw; exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem w ((huse1 v hv).mp (Or.inl hvout.symm))
        · intro hvmem
          rcases List.mem_cons.mp hvmem with rfl | hrest
          · exact ⟨gNew, List.mem_append_right _ (List.mem_singleton_self _), by simp [gNew]⟩
          · rcases (huse1 v hv).mpr hrest with hout_eq | ⟨g, hg, hvg⟩
            · exact ⟨gNew, List.mem_append_right _ (List.mem_singleton_self _), by simp [gNew, hout_eq]⟩
            · exact ⟨g, List.mem_append_left _ hg, hvg⟩
      have hC2_ev : ∀ inp : List Bool, inp.length = M + 2 → inp.getD M false = false →
          C2.eval inp = (w :: w2 :: rest2).any (fun v => inp.getD v false) := by
        intro inp hinp hM0
        have hwires2 : C2.wires inp = C1.wires inp ++ [gNew.op.eval (gNew.inputs.map fun i => (C1.wires inp).getD i false)] := by
          unfold Circuit.wires
          simp only [C2, List.foldl_append, List.foldl_cons, List.foldl_nil]
        have hw0_len : (C1.wires inp).length = (M + 2) + C1.gates.length := by
          unfold Circuit.wires; rw [wires_foldl_len, hinp]
        unfold Circuit.eval
        rw [hwires2]
        simp only [C2]
        rw [List.getD_eq_getElem?_getD,
          List.getElem?_append_right (by omega : (C1.wires inp).length ≤ (M + 2) + C1.gates.length),
          hw0_len, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        simp only [gNew, List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
          id_eq, Bool.or_false]
        have hw_val : (C1.wires inp).getD w false = inp.getD w false := by
          unfold Circuit.wires; exact wires_foldl_getD_lt C1.gates inp w (by omega)
        have hout_val : (C1.wires inp).getD C1.output false = (w2 :: rest2).any (fun v => inp.getD v false) :=
          hev1 inp hinp hM0
        rw [hw_val, hout_val, List.any_cons]
      exact ⟨C2, hC2_fan, hC2_rb, hC2_out, hC2_sz, hC2_op, hC2_use, hC2_ev⟩

-- =========================================================================
-- Part 2: Uniform-width bank flattening and rawVec indexing
-- =========================================================================

private lemma getD_append_left {α : Type*} (l1 l2 : List α) (i : ℕ) (d : α) (hi : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma getD_append_right {α : Type*} (l1 l2 : List α) (i : ℕ) (d : α) (hi : l1.length ≤ i) :
    (l1 ++ l2).getD i d = l2.getD (i - l1.length) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

private lemma getD_ofFn {α : Type*} {m : ℕ} (f : Fin m → α) (i : ℕ) (hi : i < m) (d : α) :
    (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
  have hlt : i < (List.ofFn f).length := by simp [hi]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, List.getElem_ofFn, Option.getD_some]

private lemma flatten_const_len {α : Type*} :
    ∀ {n d : ℕ} (x : Fin n → Fin d → α),
      (List.ofFn (fun a : Fin n => List.ofFn (x a))).flatten.length = n * d
  | 0, _, _ => by simp
  | n + 1, d, x => by
    rw [List.ofFn_succ, List.flatten_cons, List.length_append, List.length_ofFn,
      flatten_const_len (fun a : Fin n => x a.succ), Nat.succ_mul, add_comm]

private lemma flatten_const_getD {α : Type*} :
    ∀ {n d : ℕ} (x : Fin n → Fin d → α) (a : Fin n) (i : Fin d) (defVal : α),
      (List.ofFn (fun b : Fin n => List.ofFn (x b))).flatten.getD (a.val * d + i.val) defVal = x a i
  | 0, _, _, a, _, _ => Fin.elim0 a
  | n + 1, d, x, a, i, defVal => by
    rw [List.ofFn_succ, List.flatten_cons]
    cases a using Fin.cases with
    | zero =>
      simp only [Fin.val_zero, zero_mul, zero_add]
      rw [getD_append_left _ _ _ _ (by rw [List.length_ofFn]; exact i.isLt)]
      rw [getD_ofFn (x 0) i.val i.isLt]
    | succ a' =>
      rw [Fin.val_succ, Nat.succ_mul]
      have hge : (List.ofFn (x 0)).length ≤ a'.val * d + d + i.val := by
        rw [List.length_ofFn]; omega
      rw [getD_append_right _ _ _ _ hge]
      have hsub : a'.val * d + d + i.val - (List.ofFn (x 0)).length = a'.val * d + i.val := by
        rw [List.length_ofFn]; omega
      rw [hsub]
      exact flatten_const_getD (fun b : Fin n => x b.succ) a' i defVal

private def rawVec {n d : ℕ} (x : Fin n → Fin d → Bool) : List Bool :=
  (List.ofFn (fun a : Fin n => List.ofFn (x a))).flatten ++ [false, true]

private lemma rawVec_len {n d : ℕ} (x : Fin n → Fin d → Bool) :
    (rawVec x).length = n * d + 2 := by
  unfold rawVec
  rw [List.length_append, flatten_const_len]; simp

private lemma rawVec_getD_bank {n d : ℕ} (x : Fin n → Fin d → Bool) (a : Fin n) (i : Fin d) :
    (rawVec x).getD (a.val * d + i.val) false = x a i := by
  unfold rawVec
  have hlt : a.val * d + i.val < n * d := by
    calc a.val * d + i.val < a.val * d + d := Nat.add_lt_add_left i.isLt _
      _ = (a.val + 1) * d := by rw [Nat.succ_mul]
      _ ≤ n * d := Nat.mul_le_mul_right d a.isLt
  rw [getD_append_left _ _ _ _ (by rw [flatten_const_len]; exact hlt)]
  exact flatten_const_getD x a i false

private lemma rawVec_getD_false {n d : ℕ} (x : Fin n → Fin d → Bool) :
    (rawVec x).getD (n * d) false = false := by
  unfold rawVec
  rw [getD_append_right _ _ _ _ (by rw [flatten_const_len])]
  rw [flatten_const_len, Nat.sub_self]; rfl

private lemma rawVec_getD_true {n d : ℕ} (x : Fin n → Fin d → Bool) :
    (rawVec x).getD (n * d + 1) false = true := by
  unfold rawVec
  rw [getD_append_right _ _ _ _ (by rw [flatten_const_len]; omega)]
  have hsub : n * d + 1 - (List.ofFn (fun a : Fin n => List.ofFn (x a))).flatten.length = 1 := by
    rw [flatten_const_len]; omega
  rw [hsub]; rfl

private lemma bank_index_lt {n d : ℕ} (a : Fin n) (i : Fin d) : a.val * d + i.val < n * d := by
  calc a.val * d + i.val < a.val * d + d := Nat.add_lt_add_left i.isLt _
    _ = (a.val + 1) * d := by rw [Nat.succ_mul]
    _ ≤ n * d := Nat.mul_le_mul_right d a.isLt

private lemma bank_index_inj {n d : ℕ} {a1 a2 : Fin n} {i1 i2 : Fin d}
    (h : a1.val * d + i1.val = a2.val * d + i2.val) : a1 = a2 ∧ i1 = i2 := by
  have hd : 0 < d := lt_of_le_of_lt (Nat.zero_le _) i1.isLt
  have ha : a1.val = a2.val := by
    have h1 := congrArg (· / d) h
    rw [mul_comm a1.val d, mul_comm a2.val d, Nat.mul_add_div hd, Nat.mul_add_div hd,
      Nat.div_eq_of_lt i1.isLt, Nat.div_eq_of_lt i2.isLt] at h1
    omega
  have hi : i1.val = i2.val := by rw [ha] at h; omega
  exact ⟨Fin.ext ha, Fin.ext hi⟩

private lemma exists_bank_pair {n d : ℕ} (hd : 0 < d) {w : ℕ} (hw : w < n * d) :
    ∃ (a : Fin n) (i : Fin d), w = a.val * d + i.val := by
  refine ⟨⟨w / d, Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hw)⟩, ⟨w % d, Nat.mod_lt w hd⟩, ?_⟩
  have := Nat.div_add_mod w d
  rw [mul_comm] at this
  exact this.symm

-- =========================================================================
-- Part 3: Concave endpoint rounding for bank counts
-- =========================================================================

private def obj {n : ℕ} (d : ℕ) (E : Finset (Finset (Fin n))) (x : Fin n → ℕ) : ℕ :=
  E.sum (fun M => M.prod (fun a => d - x a))

private lemma obj_mono {n : ℕ} (d : ℕ) (E : Finset (Finset (Fin n))) {x y : Fin n → ℕ}
    (hxy : ∀ a, x a ≤ y a) : obj d E y ≤ obj d E x := by
  unfold obj
  apply Finset.sum_le_sum
  intro M _
  apply Finset.prod_le_prod'
  intro a _
  have := hxy a; omega

private lemma exists_filled {n : ℕ} (d : ℕ) (E : Finset (Finset (Fin n))) (L : ℕ) (hL : L ≤ n * d)
    (x : Fin n → ℕ) (hxb : ∀ a, x a ≤ d) (hxs : Finset.univ.sum x ≤ L) :
    ∃ y : Fin n → ℕ, (∀ a, y a ≤ d) ∧ Finset.univ.sum y = L ∧ obj d E y ≤ obj d E x := by
  suffices h : ∀ gap : ℕ, ∀ x : Fin n → ℕ,
      (∀ a, x a ≤ d) → Finset.univ.sum x + gap = L →
      ∃ y : Fin n → ℕ, (∀ a, y a ≤ d) ∧ Finset.univ.sum y = L ∧ obj d E y ≤ obj d E x from
    h (L - Finset.univ.sum x) x hxb (by omega)
  intro gap
  induction gap with
  | zero =>
    intro x hxb hsum
    exact ⟨x, hxb, by omega, le_refl _⟩
  | succ gap ih =>
    intro x hxb hsum
    have hex : ∃ a : Fin n, x a < d := by
      by_contra hall
      push Not at hall
      have hge : n * d ≤ Finset.univ.sum x := by
        calc n * d = Finset.univ.sum (fun _ : Fin n => d) := by simp
          _ ≤ Finset.univ.sum x := Finset.sum_le_sum (fun a _ => hall a)
      omega
    rcases hex with ⟨a0, ha0⟩
    let x' : Fin n → ℕ := fun a => if a = a0 then x a + 1 else x a
    have hx'b : ∀ a, x' a ≤ d := by
      intro a; dsimp [x']; split_ifs with h
      · subst h; omega
      · exact hxb a
    have hx's : Finset.univ.sum x' = Finset.univ.sum x + 1 := by
      have hrest : (Finset.univ.erase a0).sum x' = (Finset.univ.erase a0).sum x := by
        apply Finset.sum_congr rfl
        intro a ha
        have hne : a ≠ a0 := (Finset.mem_erase.mp ha).1
        simp [x', hne]
      calc Finset.univ.sum x' = x' a0 + (Finset.univ.erase a0).sum x' :=
            (Finset.add_sum_erase Finset.univ x' (Finset.mem_univ a0)).symm
        _ = (x a0 + 1) + (Finset.univ.erase a0).sum x := by rw [hrest]; simp [x']
        _ = (x a0 + (Finset.univ.erase a0).sum x) + 1 := by omega
        _ = Finset.univ.sum x + 1 := by rw [Finset.add_sum_erase Finset.univ x (Finset.mem_univ a0)]
    have hobj : obj d E x' ≤ obj d E x := by
      apply obj_mono
      intro a; dsimp [x']; split_ifs <;> omega
    rcases ih x' hx'b (by omega) with ⟨y, hyb, hys, hyobj⟩
    exact ⟨y, hyb, hys, le_trans hyobj hobj⟩

private lemma prod_concave_transfer {n : ℕ} (d : ℕ) (M : Finset (Fin n)) (x : Fin n → ℕ)
    {a b : Fin n} (hab : a ≠ b) {δ ε : ℕ}
    (ha_hi : x a + δ ≤ d) (hb_lo : δ ≤ x b) (ha_lo : ε ≤ x a) (hb_hi : x b + ε ≤ d) :
    let xp := fun c => if c = a then x a + δ else if c = b then x b - δ else x c
    let xm := fun c => if c = a then x a - ε else if c = b then x b + ε else x c
    ε * M.prod (fun c => d - xp c) + δ * M.prod (fun c => d - xm c) ≤
      (ε + δ) * M.prod (fun c => d - x c) := by
  intro xp xm
  by_cases haM : a ∈ M
  · by_cases hbM : b ∈ M
    · have hb_er : b ∈ M.erase a := Finset.mem_erase.mpr ⟨hab.symm, hbM⟩
      set R := ((M.erase a).erase b).prod (fun c => d - x c)
      have hR_xp : ((M.erase a).erase b).prod (fun c => d - xp c) = R := by
        apply Finset.prod_congr rfl
        intro c hc
        have hcb : c ≠ b := (Finset.mem_erase.mp hc).1
        have hca : c ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).1
        simp [xp, hca, hcb]
      have hR_xm : ((M.erase a).erase b).prod (fun c => d - xm c) = R := by
        apply Finset.prod_congr rfl
        intro c hc
        have hcb : c ≠ b := (Finset.mem_erase.mp hc).1
        have hca : c ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).1
        simp [xm, hca, hcb]
      have hp_x : M.prod (fun c => d - x c) = (d - x a) * ((d - x b) * R) := by
        rw [← Finset.mul_prod_erase M _ haM, ← Finset.mul_prod_erase (M.erase a) _ hb_er]
      have hp_xp : M.prod (fun c => d - xp c) = (d - (x a + δ)) * ((d - (x b - δ)) * R) := by
        rw [← Finset.mul_prod_erase M _ haM, ← Finset.mul_prod_erase (M.erase a) _ hb_er, hR_xp]
        simp [xp, hab.symm]
      have hp_xm : M.prod (fun c => d - xm c) = (d - (x a - ε)) * ((d - (x b + ε)) * R) := by
        rw [← Finset.mul_prod_erase M _ haM, ← Finset.mul_prod_erase (M.erase a) _ hb_er, hR_xm]
        simp [xm, hab.symm]
      rw [hp_x, hp_xp, hp_xm]
      set A := d - x a
      set B := d - x b
      have hA1 : d - (x a + δ) = A - δ := by omega
      have hB1 : d - (x b - δ) = B + δ := by omega
      have hA2 : d - (x a - ε) = A + ε := by omega
      have hB2 : d - (x b + ε) = B - ε := by omega
      rw [hA1, hB1, hA2, hB2]
      have hδA : δ ≤ A := by omega
      have hεB : ε ≤ B := by omega
      have hstep : ε * ((A - δ) * (B + δ)) + δ * ((A + ε) * (B - ε)) ≤ (ε + δ) * (A * B) := by
        zify [hδA, hεB]
        have hdiff : ((ε : ℤ) + δ) * (A * B) -
            (ε * ((A - δ) * (B + δ)) + δ * ((A + ε) * (B - ε))) = (ε : ℤ) * δ * (δ + ε) := by ring
        have hnn : (0 : ℤ) ≤ (ε : ℤ) * δ * (δ + ε) := by positivity
        linarith
      calc ε * ((A - δ) * ((B + δ) * R)) + δ * ((A + ε) * ((B - ε) * R))
          = (ε * ((A - δ) * (B + δ)) + δ * ((A + ε) * (B - ε))) * R := by ring
        _ ≤ ((ε + δ) * (A * B)) * R := Nat.mul_le_mul_right R hstep
        _ = (ε + δ) * (A * (B * R)) := by ring
    · set R := (M.erase a).prod (fun c => d - x c)
      have hR_xp : (M.erase a).prod (fun c => d - xp c) = R := by
        apply Finset.prod_congr rfl
        intro c hc
        have hca : c ≠ a := (Finset.mem_erase.mp hc).1
        have hcb : c ≠ b := fun h => hbM (h ▸ (Finset.mem_erase.mp hc).2)
        simp [xp, hca, hcb]
      have hR_xm : (M.erase a).prod (fun c => d - xm c) = R := by
        apply Finset.prod_congr rfl
        intro c hc
        have hca : c ≠ a := (Finset.mem_erase.mp hc).1
        have hcb : c ≠ b := fun h => hbM (h ▸ (Finset.mem_erase.mp hc).2)
        simp [xm, hca, hcb]
      have hp_x : M.prod (fun c => d - x c) = (d - x a) * R := by
        rw [← Finset.mul_prod_erase M _ haM]
      have hp_xp : M.prod (fun c => d - xp c) = (d - (x a + δ)) * R := by
        rw [← Finset.mul_prod_erase M _ haM, hR_xp]; simp [xp]
      have hp_xm : M.prod (fun c => d - xm c) = (d - (x a - ε)) * R := by
        rw [← Finset.mul_prod_erase M _ haM, hR_xm]; simp [xm]
      rw [hp_x, hp_xp, hp_xm]
      set A := d - x a
      have hA1 : d - (x a + δ) = A - δ := by omega
      have hA2 : d - (x a - ε) = A + ε := by omega
      have hδA : δ ≤ A := by omega
      rw [hA1, hA2]
      have hlin : ε * (A - δ) + δ * (A + ε) = (ε + δ) * A := by zify [hδA]; ring
      exact le_of_eq (calc ε * ((A - δ) * R) + δ * ((A + ε) * R)
          = (ε * (A - δ) + δ * (A + ε)) * R := by ring
        _ = (ε + δ) * (A * R) := by rw [hlin]; ring)
  · by_cases hbM : b ∈ M
    · set R := (M.erase b).prod (fun c => d - x c)
      have hR_xp : (M.erase b).prod (fun c => d - xp c) = R := by
        apply Finset.prod_congr rfl
        intro c hc
        have hcb : c ≠ b := (Finset.mem_erase.mp hc).1
        have hca : c ≠ a := fun h => haM (h ▸ (Finset.mem_erase.mp hc).2)
        simp [xp, hca, hcb]
      have hR_xm : (M.erase b).prod (fun c => d - xm c) = R := by
        apply Finset.prod_congr rfl
        intro c hc
        have hcb : c ≠ b := (Finset.mem_erase.mp hc).1
        have hca : c ≠ a := fun h => haM (h ▸ (Finset.mem_erase.mp hc).2)
        simp [xm, hca, hcb]
      have hp_x : M.prod (fun c => d - x c) = (d - x b) * R := by
        rw [← Finset.mul_prod_erase M _ hbM]
      have hp_xp : M.prod (fun c => d - xp c) = (d - (x b - δ)) * R := by
        rw [← Finset.mul_prod_erase M _ hbM, hR_xp]; simp [xp, hab.symm]
      have hp_xm : M.prod (fun c => d - xm c) = (d - (x b + ε)) * R := by
        rw [← Finset.mul_prod_erase M _ hbM, hR_xm]; simp [xm, hab.symm]
      rw [hp_x, hp_xp, hp_xm]
      set B := d - x b
      have hB1 : d - (x b - δ) = B + δ := by omega
      have hB2 : d - (x b + ε) = B - ε := by omega
      have hεB : ε ≤ B := by omega
      rw [hB1, hB2]
      have hlin : ε * (B + δ) + δ * (B - ε) = (ε + δ) * B := by zify [hεB]; ring
      exact le_of_eq (calc ε * ((B + δ) * R) + δ * ((B - ε) * R)
          = (ε * (B + δ) + δ * (B - ε)) * R := by ring
        _ = (ε + δ) * (B * R) := by rw [hlin]; ring)
    · have h1 : M.prod (fun c => d - xp c) = M.prod (fun c => d - x c) := by
        apply Finset.prod_congr rfl; intro c hc
        have hca : c ≠ a := fun h => haM (h ▸ hc)
        have hcb : c ≠ b := fun h => hbM (h ▸ hc)
        simp [xp, hca, hcb]
      have h2 : M.prod (fun c => d - xm c) = M.prod (fun c => d - x c) := by
        apply Finset.prod_congr rfl; intro c hc
        have hca : c ≠ a := fun h => haM (h ▸ hc)
        have hcb : c ≠ b := fun h => hbM (h ▸ hc)
        simp [xm, hca, hcb]
      rw [h1, h2]; ring_nf; exact le_refl _

private lemma exists_rounded {n : ℕ} (d : ℕ) (E : Finset (Finset (Fin n))) (L : ℕ) :
    ∀ p : ℕ, ∀ x : Fin n → ℕ,
      (∀ a, x a ≤ d) → Finset.univ.sum x = L →
      (Finset.univ.filter (fun c : Fin n => 0 < x c ∧ x c < d)).card ≤ p →
      ∃ y : Fin n → ℕ,
        (∀ a, y a ≤ d) ∧ Finset.univ.sum y = L ∧
        (Finset.univ.filter (fun c : Fin n => 0 < y c ∧ y c < d)).card ≤ 1 ∧
        obj d E y ≤ obj d E x := by
  intro p
  induction p with
  | zero =>
    intro x hxb hxs hpc
    exact ⟨x, hxb, hxs, by omega, le_refl _⟩
  | succ p ih =>
    intro x hxb hxs hpc
    set P := Finset.univ.filter (fun c : Fin n => 0 < x c ∧ x c < d)
    by_cases h1 : P.card ≤ 1
    · exact ⟨x, hxb, hxs, h1, le_refl _⟩
    · have h2 : 1 < P.card := by omega
      rcases Finset.one_lt_card.mp h2 with ⟨a, haP, b, hbP, hab⟩
      have ha_mid : 0 < x a ∧ x a < d := (Finset.mem_filter.mp haP).2
      have hb_mid : 0 < x b ∧ x b < d := (Finset.mem_filter.mp hbP).2
      set δ := min (d - x a) (x b)
      set ε := min (x a) (d - x b)
      have hδ_pos : 0 < δ := lt_min (by omega) hb_mid.1
      have hε_pos : 0 < ε := lt_min ha_mid.1 (by omega)
      have ha_hi : x a + δ ≤ d := by have := min_le_left (d - x a) (x b); omega
      have hb_lo : δ ≤ x b := min_le_right (d - x a) (x b)
      have ha_lo : ε ≤ x a := min_le_left (x a) (d - x b)
      have hb_hi : x b + ε ≤ d := by have := min_le_right (x a) (d - x b); omega
      let xp : Fin n → ℕ := fun c => if c = a then x a + δ else if c = b then x b - δ else x c
      let xm : Fin n → ℕ := fun c => if c = a then x a - ε else if c = b then x b + ε else x c
      have hconc : ε * obj d E xp + δ * obj d E xm ≤ (ε + δ) * obj d E x := by
        unfold obj
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro M _
        exact prod_concave_transfer d M x hab ha_hi hb_lo ha_lo hb_hi
      have hchoice : obj d E xp ≤ obj d E x ∨ obj d E xm ≤ obj d E x := by
        by_contra hboth
        push Not at hboth
        have h1' : obj d E x + 1 ≤ obj d E xp := hboth.1
        have h2' : obj d E x + 1 ≤ obj d E xm := hboth.2
        nlinarith
      rcases hchoice with hxp_le | hxm_le
      · have hxp_b : ∀ c, xp c ≤ d := by
          intro c; dsimp [xp]; split_ifs with h1' h2'
          · exact ha_hi
          · have := hxb b; omega
          · exact hxb c
        have hxp_s : Finset.univ.sum xp = L := by
          have hb_er : b ∈ Finset.univ.erase a := Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩
          have hrest : ((Finset.univ.erase a).erase b).sum xp = ((Finset.univ.erase a).erase b).sum x := by
            apply Finset.sum_congr rfl; intro c hc
            have hcb : c ≠ b := (Finset.mem_erase.mp hc).1
            have hca : c ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).1
            simp [xp, hca, hcb]
          calc Finset.univ.sum xp = xp a + (xp b + ((Finset.univ.erase a).erase b).sum xp) := by
                rw [Finset.add_sum_erase _ _ hb_er, Finset.add_sum_erase _ _ (Finset.mem_univ a)]
            _ = (x a + δ) + ((x b - δ) + ((Finset.univ.erase a).erase b).sum x) := by
                rw [hrest]; simp [xp, hab.symm]
            _ = x a + (x b + ((Finset.univ.erase a).erase b).sum x) := by omega
            _ = L := by rw [Finset.add_sum_erase _ _ hb_er, Finset.add_sum_erase _ _ (Finset.mem_univ a), hxs]
        have hxp_card : (Finset.univ.filter (fun c : Fin n => 0 < xp c ∧ xp c < d)).card ≤ p := by
          set P' := Finset.univ.filter (fun c : Fin n => 0 < xp c ∧ xp c < d)
          have hsub : P' ⊆ P := by
            intro c hc
            have hcm := (Finset.mem_filter.mp hc).2
            rw [Finset.mem_filter]
            refine ⟨Finset.mem_univ c, ?_⟩
            by_cases hca : c = a
            · subst hca; exact ha_mid
            · by_cases hcb : c = b
              · subst hcb; exact hb_mid
              · simp [xp, hca, hcb] at hcm; exact hcm
          have hstrict : P' ⊂ P := by
            rw [Finset.ssubset_iff_subset_ne]
            refine ⟨hsub, ?_⟩
            intro heq
            rcases min_cases (d - x a) (x b) with ⟨hδe, _⟩ | ⟨hδe, _⟩
            · have ha_in : a ∈ P' := heq.symm ▸ haP
              have hm := (Finset.mem_filter.mp ha_in).2
              simp only [xp, ↓reduceIte] at hm; omega
            · have hb_in : b ∈ P' := heq.symm ▸ hbP
              have hm := (Finset.mem_filter.mp hb_in).2
              simp only [xp, hab.symm, ↓reduceIte] at hm; omega
          have := Finset.card_lt_card hstrict
          omega
        rcases ih xp hxp_b hxp_s hxp_card with ⟨y, hyb, hys, hyp, hyobj⟩
        exact ⟨y, hyb, hys, hyp, le_trans hyobj hxp_le⟩
      · have hxm_b : ∀ c, xm c ≤ d := by
          intro c; dsimp [xm]; split_ifs with h1' h2'
          · have := hxb a; omega
          · exact hb_hi
          · exact hxb c
        have hxm_s : Finset.univ.sum xm = L := by
          have hb_er : b ∈ Finset.univ.erase a := Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩
          have hrest : ((Finset.univ.erase a).erase b).sum xm = ((Finset.univ.erase a).erase b).sum x := by
            apply Finset.sum_congr rfl; intro c hc
            have hcb : c ≠ b := (Finset.mem_erase.mp hc).1
            have hca : c ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).1
            simp [xm, hca, hcb]
          calc Finset.univ.sum xm = xm a + (xm b + ((Finset.univ.erase a).erase b).sum xm) := by
                rw [Finset.add_sum_erase _ _ hb_er, Finset.add_sum_erase _ _ (Finset.mem_univ a)]
            _ = (x a - ε) + ((x b + ε) + ((Finset.univ.erase a).erase b).sum x) := by
                rw [hrest]; simp [xm, hab.symm]
            _ = x a + (x b + ((Finset.univ.erase a).erase b).sum x) := by omega
            _ = L := by rw [Finset.add_sum_erase _ _ hb_er, Finset.add_sum_erase _ _ (Finset.mem_univ a), hxs]
        have hxm_card : (Finset.univ.filter (fun c : Fin n => 0 < xm c ∧ xm c < d)).card ≤ p := by
          set P' := Finset.univ.filter (fun c : Fin n => 0 < xm c ∧ xm c < d)
          have hsub : P' ⊆ P := by
            intro c hc
            have hcm := (Finset.mem_filter.mp hc).2
            rw [Finset.mem_filter]
            refine ⟨Finset.mem_univ c, ?_⟩
            by_cases hca : c = a
            · subst hca; exact ha_mid
            · by_cases hcb : c = b
              · subst hcb; exact hb_mid
              · simp [xm, hca, hcb] at hcm; exact hcm
          have hstrict : P' ⊂ P := by
            rw [Finset.ssubset_iff_subset_ne]
            refine ⟨hsub, ?_⟩
            intro heq
            rcases min_cases (x a) (d - x b) with ⟨hεe, _⟩ | ⟨hεe, _⟩
            · have ha_in : a ∈ P' := heq.symm ▸ haP
              have hm := (Finset.mem_filter.mp ha_in).2
              simp only [xm, ↓reduceIte] at hm; omega
            · have hb_in : b ∈ P' := heq.symm ▸ hbP
              have hm := (Finset.mem_filter.mp hb_in).2
              simp only [xm, hab.symm, ↓reduceIte] at hm; omega
          have := Finset.card_lt_card hstrict
          omega
        rcases ih xm hxm_b hxm_s hxm_card with ⟨y, hyb, hys, hyp, hyobj⟩
        exact ⟨y, hyb, hys, hyp, le_trans hyobj hxm_le⟩

-- =========================================================================
-- Part 4: Row sets, copies disjointness, loss counting, and body theorem
-- =========================================================================

private noncomputable def copyAssign {n d : ℕ} (M : Finset (Fin n))
    (f : {a : Fin n // a ∈ M} → Fin d) : Fin n → Fin d → Bool :=
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  fun a k => if h : a ∈ M then decide (f ⟨a, h⟩ = k) else false

private noncomputable def copiesSet {n d : ℕ} (M : Finset (Fin n)) : Finset (List Bool) :=
  Finset.univ.image (fun f : {a : Fin n // a ∈ M} → Fin d => rawVec (copyAssign M f))

private lemma copiesSet_injective {n d : ℕ} (M : Finset (Fin n)) :
    Function.Injective (fun f : {a : Fin n // a ∈ M} → Fin d => rawVec (copyAssign M f)) := by
  intro f1 f2 heq
  funext a
  set t := f1 a
  have hb := congrArg (fun l : List Bool => l.getD (a.val.val * d + t.val) false) heq
  rw [rawVec_getD_bank, rawVec_getD_bank] at hb
  unfold copyAssign at hb
  simp only [a.property, ↓reduceDIte, t, decide_true] at hb
  have hEq : f2 a = f1 a := by simpa using hb.symm
  exact hEq.symm

private lemma copiesSet_pairwise_disjoint {n d : ℕ} (hd : 0 < d) (E : Finset (Finset (Fin n))) :
    Set.PairwiseDisjoint (E : Set (Finset (Fin n))) (copiesSet (d := d)) := by
  intro M1 _ M2 _ hne
  dsimp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro v hv1 hv2
  rcases Finset.mem_image.mp hv1 with ⟨f1, _, rfl⟩
  rcases Finset.mem_image.mp hv2 with ⟨f2, _, heq⟩
  apply hne
  ext a
  constructor
  · intro ha1
    set t := f1 ⟨a, ha1⟩
    have hb := congrArg (fun l : List Bool => l.getD (a.val * d + t.val) false) heq
    rw [rawVec_getD_bank, rawVec_getD_bank] at hb
    unfold copyAssign at hb
    simp only [ha1, ↓reduceDIte, t, decide_true] at hb
    by_contra ha2
    simp [ha2] at hb
  · intro ha2
    set t := f2 ⟨a, ha2⟩
    have hb := congrArg (fun l : List Bool => l.getD (a.val * d + t.val) false) heq
    rw [rawVec_getD_bank, rawVec_getD_bank] at hb
    unfold copyAssign at hb
    simp only [ha2, ↓reduceDIte, t, decide_true] at hb
    by_contra ha1
    simp [ha1] at hb

private def scoreVal {n : ℕ} (d u : ℕ) (E : Finset (Finset (Fin n))) (S T : Finset (Fin n)) : ℕ :=
  (E.filter (fun M => Disjoint M S)).sum (fun M =>
    if Disjoint M T then d ^ M.card else (d - u) * d ^ (M.card - 1))

private lemma obj_eq_scoreVal {n : ℕ} (d : ℕ) (hd : 0 < d) (E : Finset (Finset (Fin n)))
    (L : ℕ) (y : Fin n → ℕ)
    (hyb : ∀ a, y a ≤ d) (hys : Finset.univ.sum y = L)
    (hyp : (Finset.univ.filter (fun c : Fin n => 0 < y c ∧ y c < d)).card ≤ 1) :
    let S := Finset.univ.filter (fun a : Fin n => y a = d)
    let T := Finset.univ.filter (fun a : Fin n => 0 < y a ∧ y a < d)
    let k := L / d
    let u := L % d
    (S.card = k ∧ T.card = (if u = 0 then 0 else 1) ∧ Disjoint S T) ∧
    scoreVal d u E S T = obj d E y := by
  set S := Finset.univ.filter (fun a : Fin n => y a = d)
  set T := Finset.univ.filter (fun a : Fin n => 0 < y a ∧ y a < d)
  set k := L / d
  set u := L % d
  have hdisjST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro a haS haT
    have h1 := (Finset.mem_filter.mp haS).2
    have h2 := (Finset.mem_filter.mp haT).2
    omega
  have hsum_ST : S.card * d + T.sum y = L := by
    rw [← hys]
    have hpart : Finset.univ.sum y = (S ∪ T).sum y := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro a _ ha
      simp only [Finset.mem_union, S, T, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at ha
      have := hyb a; omega
    rw [hpart, Finset.sum_union hdisjST]
    have hSsum : S.sum y = S.card * d := by
      have : S.sum y = S.sum (fun _ => d) := Finset.sum_congr rfl (fun a ha => (Finset.mem_filter.mp ha).2)
      rw [this, Finset.sum_const, smul_eq_mul]
    rw [hSsum]
  have hshape_and_val : S.card = k ∧ T.card = (if u = 0 then 0 else 1) ∧ ∀ a ∈ T, y a = u := by
    by_cases hT0 : T = ∅
    · have hL : S.card * d = L := by rw [hT0] at hsum_ST; simp at hsum_ST; exact hsum_ST
      have hk : S.card = k := by
        dsimp [k]; rw [← hL, Nat.mul_div_cancel _ hd]
      have hu : u = 0 := by
        dsimp [u]; rw [← hL, Nat.mul_mod_left]
      exact ⟨hk, by rw [hT0, hu]; simp, fun a ha => by rw [hT0] at ha; simp at ha⟩
    · have hTpos : 0 < T.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hT0)
      have hT1 : T.card = 1 := by omega
      rcases Finset.card_eq_one.mp hT1 with ⟨a0, ha0⟩
      have ha0_mem : a0 ∈ T := by rw [ha0]; exact Finset.mem_singleton_self a0
      have ha0_mid : 0 < y a0 ∧ y a0 < d := (Finset.mem_filter.mp ha0_mem).2
      have hL : S.card * d + y a0 = L := by rw [ha0, Finset.sum_singleton] at hsum_ST; exact hsum_ST
      have hk : S.card = k := by
        dsimp [k]; rw [← hL, add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt ha0_mid.2, zero_add]
      have hu : y a0 = u := by
        dsimp [u]; rw [← hL, add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha0_mid.2]
      refine ⟨hk, ?_, ?_⟩
      · have hne0 : u ≠ 0 := by omega
        rw [hT1]; simp [hne0]
      · intro a ha; rw [ha0, Finset.mem_singleton] at ha; subst ha; exact hu
  refine ⟨⟨hshape_and_val.1, hshape_and_val.2.1, hdisjST⟩, ?_⟩
  unfold scoreVal obj
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro M _
  by_cases hMS : Disjoint M S
  · simp only [hMS, ↓reduceIte]
    by_cases hMT : Disjoint M T
    · simp only [hMT, ↓reduceIte]
      have hprod : M.prod (fun a => d - y a) = M.prod (fun _ => d) := by
        apply Finset.prod_congr rfl
        intro a haM
        have haS : a ∉ S := Finset.disjoint_left.mp hMS haM
        have haT : a ∉ T := Finset.disjoint_left.mp hMT haM
        simp only [S, T, Finset.mem_filter, Finset.mem_univ, true_and] at haS haT
        have := hyb a
        have hy0 : y a = 0 := by omega
        rw [hy0, Nat.sub_zero]
      rw [hprod, Finset.prod_const]
    · simp only [hMT, ↓reduceIte]
      rw [Finset.not_disjoint_iff] at hMT
      rcases hMT with ⟨a0, ha0M, ha0T⟩
      have hT1 : T.card = 1 := by
        have hpos : 0 < T.card := Finset.card_pos.mpr ⟨a0, ha0T⟩
        omega
      have hTeq : T = {a0} := by
        rcases Finset.card_eq_one.mp hT1 with ⟨b, hb⟩
        have : a0 = b := by rw [hb, Finset.mem_singleton] at ha0T; exact ha0T
        subst this; exact hb
      rw [← Finset.mul_prod_erase M _ ha0M]
      have hya0 : y a0 = u := hshape_and_val.2.2 a0 ha0T
      rw [hya0]
      congr 1
      have hrest : (M.erase a0).prod (fun a => d - y a) = (M.erase a0).prod (fun _ => d) := by
        apply Finset.prod_congr rfl
        intro a ha
        rcases Finset.mem_erase.mp ha with ⟨hne, haM⟩
        have haS : a ∉ S := Finset.disjoint_left.mp hMS haM
        have haT : a ∉ T := by rw [hTeq, Finset.mem_singleton]; exact hne
        simp only [S, T, Finset.mem_filter, Finset.mem_univ, true_and] at haS haT
        have := hyb a
        have hy0 : y a = 0 := by omega
        rw [hy0, Nat.sub_zero]
      rw [hrest, Finset.prod_const, Finset.card_erase_of_mem ha0M]
  · simp only [hMS, ↓reduceIte]
    rw [Finset.not_disjoint_iff] at hMS
    rcases hMS with ⟨a0, ha0M, ha0S⟩
    have hya0 : y a0 = d := (Finset.mem_filter.mp ha0S).2
    symm
    apply Finset.prod_eq_zero ha0M
    rw [hya0, Nat.sub_self]

private lemma card_avoiding_funcs {n d : ℕ} (M : Finset (Fin n)) (bad : Fin n → Finset (Fin d)) :
    (Finset.univ.filter (fun f : {a : Fin n // a ∈ M} → Fin d => ∀ a, f a ∉ bad a.val)).card =
      M.prod (fun a => d - (bad a).card) := by
  let good : (a : {a : Fin n // a ∈ M}) → Finset (Fin d) := fun a => Finset.univ \ bad a.val
  have heq : Finset.univ.filter (fun f : {a : Fin n // a ∈ M} → Fin d => ∀ a, f a ∉ bad a.val) =
      Fintype.piFinset good := by
    ext f
    simp [Fintype.mem_piFinset, good]
  rw [heq, Fintype.card_piFinset]
  have hcard : ∀ a : {a : Fin n // a ∈ M}, (good a).card = d - (bad a.val).card := by
    intro a
    dsimp [good]
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
  simp_rw [hcard]
  exact Finset.prod_coe_sort M (fun a => d - (bad a).card)

private lemma build_for_STU {n d s : ℕ} (hd : 0 < d) (E : Finset (Finset (Fin n)))
    (S T : Finset (Fin n)) (U : Finset (Fin d))
    (hScard : S.card = min (s + 1) (n * d) / d)
    (hTcard : T.card = if min (s + 1) (n * d) % d = 0 then 0 else 1)
    (hST : Disjoint S T) (hUcard : U.card = min (s + 1) (n * d) % d) :
    let L := min (s + 1) (n * d)
    let u := L % d
    let chosen := fun (a : Fin n) (i : Fin d) => a ∈ S ∨ (a ∈ T ∧ i ∈ U)
    ∃ C : Circuit,
      FanInTwo C ∧ ReadsBack (n * d + 2) C ∧ C.output < (n * d + 2) + C.size ∧
      C.size ≤ s ∧ C.eval (rawVec (fun (_ : Fin n) (_ : Fin d) => false)) = false ∧
      (∀ g ∈ C.gates, g.op = GateOp.or) ∧
      (∀ (a : Fin n) (i : Fin d),
        (C.output = a.val * d + i.val ∨ ∃ g ∈ C.gates, a.val * d + i.val ∈ g.inputs) ↔ chosen a i) ∧
      (∀ x : Fin n → Fin d → Bool, C.eval (rawVec x) = decide (∃ a i, chosen a i ∧ x a i = true)) ∧
      ((E.biUnion (copiesSet (d := d))).filter (fun v => C.eval v = false)).card = scoreVal d u E S T := by
  set L := min (s + 1) (n * d)
  set k := L / d
  set u := L % d
  set chosen : Fin n → Fin d → Prop := fun a i => a ∈ S ∨ (a ∈ T ∧ i ∈ U)
  set pairs : Finset (Fin n × Fin d) := Finset.univ.filter (fun p => chosen p.1 p.2)
  have hpairs_eq : pairs = S ×ˢ (Finset.univ : Finset (Fin d)) ∪ T ×ˢ U := by
    ext ⟨a, i⟩
    simp [pairs, chosen]
  have hpairs_disj : Disjoint (S ×ˢ (Finset.univ : Finset (Fin d))) (T ×ˢ U) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    exact Finset.disjoint_left.mp hST (Finset.mem_product.mp hp1).1 (Finset.mem_product.mp hp2).1
  have hpairs_card : pairs.card = L := by
    rw [hpairs_eq, Finset.card_union_of_disjoint hpairs_disj, Finset.card_product, Finset.card_product,
      Finset.card_univ, Fintype.card_fin, hScard, hTcard, hUcard]
    have hdiv : k * d + u = L := by
      have := Nat.div_add_mod L d; rw [mul_comm] at this; exact this
    by_cases hu0 : u = 0
    · simp only [hu0, ↓reduceIte, zero_mul, add_zero]
      omega
    · simp only [hu0, ↓reduceIte, one_mul]
      exact hdiv
  let ws : List ℕ := pairs.toList.map (fun p => p.1.val * d + p.2.val)
  have hws_len : ws.length = L := by simp [ws, hpairs_card]
  have hws_lt : ∀ v ∈ ws, v < n * d := by
    intro v hv
    rcases List.mem_map.mp hv with ⟨⟨a, i⟩, _, rfl⟩
    exact bank_index_lt a i
  have hmem_ws : ∀ (a : Fin n) (i : Fin d), a.val * d + i.val ∈ ws ↔ chosen a i := by
    intro a i
    constructor
    · intro h
      rcases List.mem_map.mp h with ⟨⟨a', i'⟩, hp, heq⟩
      rcases bank_index_inj heq with ⟨rfl, rfl⟩
      exact (Finset.mem_filter.mp (Finset.mem_toList.mp hp)).2
    · intro h
      exact List.mem_map.mpr ⟨(a, i), Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩), rfl⟩
  rcases exists_or_chain ws hws_lt with ⟨C, hfan, hrb, hout, hsz, hop, huse, hev⟩
  have hsz_le : C.size ≤ s := by rw [hsz, hws_len]; omega
  have hev_all : ∀ x : Fin n → Fin d → Bool,
      C.eval (rawVec x) = decide (∃ a i, chosen a i ∧ x a i = true) := by
    intro x
    rw [hev (rawVec x) (rawVec_len x) (rawVec_getD_false x)]
    apply Bool.eq_iff_iff.mpr
    rw [List.any_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨v, hv, hxv⟩
      rcases List.mem_map.mp hv with ⟨⟨a, i⟩, hp, rfl⟩
      rw [rawVec_getD_bank] at hxv
      exact ⟨a, i, (Finset.mem_filter.mp (Finset.mem_toList.mp hp)).2, hxv⟩
    · rintro ⟨a, i, hch, hxa⟩
      refine ⟨a.val * d + i.val, (hmem_ws a i).mpr hch, ?_⟩
      rw [rawVec_getD_bank]; exact hxa
  have hzero : C.eval (rawVec (fun (_ : Fin n) (_ : Fin d) => false)) = false := by
    rw [hev_all]; simp
  have hloss : ((E.biUnion (copiesSet (d := d))).filter (fun v => C.eval v = false)).card = scoreVal d u E S T := by
    rw [Finset.filter_biUnion]
    have hdisj_f : Set.PairwiseDisjoint (E : Set (Finset (Fin n)))
        (fun M => (copiesSet (d := d) M).filter (fun v => C.eval v = false)) := by
      intro M1 hM1 M2 hM2 hne
      dsimp only [Function.onFun]
      exact Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
        (copiesSet_pairwise_disjoint hd E hM1 hM2 hne)
    rw [Finset.card_biUnion hdisj_f]
    unfold scoreVal
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro M _
    let bad : Fin n → Finset (Fin d) := fun a => Finset.univ.filter (fun i : Fin d => chosen a i)
    have hfilt_eq : ((copiesSet (d := d) M).filter (fun v => C.eval v = false)).card =
        (Finset.univ.filter (fun f : {a : Fin n // a ∈ M} → Fin d => ∀ a, f a ∉ bad a.val)).card := by
      have himg : (copiesSet (d := d) M).filter (fun v => C.eval v = false) =
          (Finset.univ.filter (fun f : {a : Fin n // a ∈ M} → Fin d => ∀ a, f a ∉ bad a.val)).image
            (fun f => rawVec (copyAssign M f)) := by
        ext v
        simp only [copiesSet, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨⟨f, rfl⟩, hcf⟩
          refine ⟨f, ?_, rfl⟩
          intro a hbad
          have hch : chosen a.val (f a) := (Finset.mem_filter.mp hbad).2
          rw [hev_all] at hcf
          have htrue : decide (∃ b i, chosen b i ∧ copyAssign M f b i = true) = true := by
            rw [decide_eq_true_eq]
            refine ⟨a.val, f a, hch, ?_⟩
            unfold copyAssign; simp [a.property]
          rw [htrue] at hcf; exact absurd hcf (by decide)
        · rintro ⟨f, hgood, rfl⟩
          refine ⟨⟨f, rfl⟩, ?_⟩
          rw [hev_all, decide_eq_false_iff_not]
          rintro ⟨a, i, hch, hca⟩
          unfold copyAssign at hca
          by_cases haM : a ∈ M
          · simp only [haM, ↓reduceDIte] at hca
            have hfi : f ⟨a, haM⟩ = i := by simpa using hca
            apply hgood ⟨a, haM⟩
            rw [hfi]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hch⟩
          · simp [haM] at hca
      rw [himg, Finset.card_image_of_injective _ (copiesSet_injective M)]
    rw [hfilt_eq, card_avoiding_funcs M bad]
    by_cases hMS : Disjoint M S
    · simp only [hMS, ↓reduceIte]
      by_cases hMT : Disjoint M T
      · simp only [hMT, ↓reduceIte]
        have hprod : M.prod (fun a => d - (bad a).card) = M.prod (fun _ => d) := by
          apply Finset.prod_congr rfl
          intro a haM
          have haS : a ∉ S := Finset.disjoint_left.mp hMS haM
          have haT : a ∉ T := Finset.disjoint_left.mp hMT haM
          have hbad0 : bad a = ∅ := by
            ext i; simp [bad, chosen, haS, haT]
          rw [hbad0, Finset.card_empty, Nat.sub_zero]
        rw [hprod, Finset.prod_const]
      · simp only [hMT, ↓reduceIte]
        rw [Finset.not_disjoint_iff] at hMT
        rcases hMT with ⟨a0, ha0M, ha0T⟩
        have hTpos : 0 < T.card := Finset.card_pos.mpr ⟨a0, ha0T⟩
        have hT1 : T.card = 1 := by
          by_cases hu0 : u = 0
          · simp only [hu0, ↓reduceIte] at hTcard; omega
          · simp only [hu0, ↓reduceIte] at hTcard; exact hTcard
        have hTeq : T = {a0} := by
          rcases Finset.card_eq_one.mp hT1 with ⟨b, hb⟩
          have : a0 = b := by rw [hb, Finset.mem_singleton] at ha0T; exact ha0T
          subst this; exact hb
        rw [← Finset.mul_prod_erase M _ ha0M]
        have hbad_a0 : bad a0 = U := by
          have ha0S : a0 ∉ S := Finset.disjoint_left.mp hMS ha0M
          ext i; simp [bad, chosen, ha0S, ha0T]
        rw [hbad_a0, hUcard]
        congr 1
        have hrest : (M.erase a0).prod (fun a => d - (bad a).card) = (M.erase a0).prod (fun _ => d) := by
          apply Finset.prod_congr rfl
          intro a ha
          rcases Finset.mem_erase.mp ha with ⟨hne, haM⟩
          have haS : a ∉ S := Finset.disjoint_left.mp hMS haM
          have haT : a ∉ T := by rw [hTeq, Finset.mem_singleton]; exact hne
          have hbad0 : bad a = ∅ := by ext i; simp [bad, chosen, haS, haT]
          rw [hbad0, Finset.card_empty, Nat.sub_zero]
        rw [hrest, Finset.prod_const, Finset.card_erase_of_mem ha0M]
    · simp only [hMS, ↓reduceIte]
      rw [Finset.not_disjoint_iff] at hMS
      rcases hMS with ⟨a0, ha0M, ha0S⟩
      have hbad_univ : bad a0 = Finset.univ := by ext i; simp [bad, chosen, ha0S]
      apply Finset.prod_eq_zero ha0M
      rw [hbad_univ, Finset.card_univ, Fintype.card_fin, Nat.sub_self]
  refine ⟨C, hfan, hrb, hout, hsz_le, hzero, hop, ?_, hev_all, hloss⟩
  intro a i
  exact (huse (a.val * d + i.val) (bank_index_lt a i)).trans (hmem_ws a i)

private lemma lower_bound_loss {n d s t : ℕ} (hd : 0 < d) (E : Finset (Finset (Fin n)))
    (C : Circuit) (hfan : FanInTwo C) (hrb : ReadsBack (n * d + 2) C)
    (hout : C.output < (n * d + 2) + C.size) (hsz : C.size ≤ s)
    (hzero : C.eval (rawVec (fun (_ : Fin n) (_ : Fin d) => false)) = false)
    (hloss : ((E.biUnion (copiesSet (d := d))).filter (fun v => C.eval v = false)).card ≤ t) :
    let L := min (s + 1) (n * d)
    ∃ S T : Finset (Fin n),
      (S.card = L / d ∧ T.card = (if L % d = 0 then 0 else 1) ∧ Disjoint S T) ∧
      scoreVal d (L % d) E S T ≤ t := by
  set L := min (s + 1) (n * d)
  rcases exists_output_frontier C hfan hrb hout with ⟨F, hF_lt, hF_card, hF_eq⟩
  let B : Fin n → Finset (Fin d) := fun a => Finset.univ.filter (fun i : Fin d => a.val * d + i.val ∈ F)
  let x : Fin n → ℕ := fun a => (B a).card
  have hxb : ∀ a, x a ≤ d := fun a => by
    calc (B a).card ≤ (Finset.univ : Finset (Fin d)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = d := by simp
  have hxs_nd : Finset.univ.sum x ≤ n * d := by
    calc Finset.univ.sum x ≤ Finset.univ.sum (fun _ : Fin n => d) := Finset.sum_le_sum (fun a _ => hxb a)
      _ = n * d := by simp
  have hxs_F : Finset.univ.sum x ≤ F.card := by
    let bank : Fin n → Finset ℕ := fun a => (B a).image (fun i : Fin d => a.val * d + i.val)
    have hcard_b : ∀ a : Fin n, (bank a).card = x a := by
      intro a
      rw [Finset.card_image_of_injective _ (fun i1 i2 h => (bank_index_inj h).2)]
    have hdisj_b : Set.PairwiseDisjoint ((Finset.univ : Finset (Fin n)) : Set (Fin n)) bank := by
      intro a _ b _ hab
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro u hua hub
      rcases Finset.mem_image.mp hua with ⟨i1, _, rfl⟩
      rcases Finset.mem_image.mp hub with ⟨i2, _, heq⟩
      exact hab (bank_index_inj heq).1.symm
    have hsub : Finset.univ.biUnion bank ⊆ F := by
      intro u hu
      rcases Finset.mem_biUnion.mp hu with ⟨a, _, hua⟩
      rcases Finset.mem_image.mp hua with ⟨i, hi, rfl⟩
      exact (Finset.mem_filter.mp hi).2
    calc Finset.univ.sum x = Finset.univ.sum (fun a => (bank a).card) :=
          Finset.sum_congr rfl (fun a _ => (hcard_b a).symm)
      _ = (Finset.univ.biUnion bank).card := (Finset.card_biUnion hdisj_b).symm
      _ ≤ F.card := Finset.card_le_card hsub
  have hxs_L : Finset.univ.sum x ≤ L := le_min (by omega) hxs_nd
  have hobj_le : obj d E x ≤ ((E.biUnion (copiesSet (d := d))).filter (fun v => C.eval v = false)).card := by
    rw [Finset.filter_biUnion]
    have hdisj_f : Set.PairwiseDisjoint (E : Set (Finset (Fin n)))
        (fun M => (copiesSet (d := d) M).filter (fun v => C.eval v = false)) := by
      intro M1 hM1 M2 hM2 hne
      dsimp only [Function.onFun]
      exact Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
        (copiesSet_pairwise_disjoint hd E hM1 hM2 hne)
    rw [Finset.card_biUnion hdisj_f]
    unfold obj
    apply Finset.sum_le_sum
    intro M _
    rw [← card_avoiding_funcs M B]
    have hsub_img : (Finset.univ.filter (fun f : {a : Fin n // a ∈ M} → Fin d => ∀ a, f a ∉ B a.val)).image
        (fun f => rawVec (copyAssign M f)) ⊆
        (copiesSet (d := d) M).filter (fun v => C.eval v = false) := by
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨f, hf, rfl⟩
      have hf_avoid : ∀ a : {a : Fin n // a ∈ M}, f a ∉ B a.val := (Finset.mem_filter.mp hf).2
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_image.mpr ⟨f, Finset.mem_univ f, rfl⟩, ?_⟩
      rw [← hzero]
      apply hF_eq _ _ (rawVec_len _) (rawVec_len _)
      intro w hwF
      have hwN : w < n * d + 2 := hF_lt w hwF
      by_cases h_bank : w < n * d
      · rcases exists_bank_pair hd h_bank with ⟨a, i, rfl⟩
        rw [rawVec_getD_bank, rawVec_getD_bank]
        unfold copyAssign
        by_cases haM : a ∈ M
        · simp only [haM, ↓reduceDIte]
          have hne : f ⟨a, haM⟩ ≠ i := by
            intro heq
            apply hf_avoid ⟨a, haM⟩
            rw [heq]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hwF⟩
          simp [hne]
        · simp [haM]
      · by_cases h_f : w = n * d
        · subst h_f; rw [rawVec_getD_false, rawVec_getD_false]
        · have h_t : w = n * d + 1 := by omega
          subst h_t; rw [rawVec_getD_true, rawVec_getD_true]
    calc (Finset.univ.filter (fun f : {a : Fin n // a ∈ M} → Fin d => ∀ a, f a ∉ B a.val)).card
        = ((Finset.univ.filter (fun f : {a : Fin n // a ∈ M} → Fin d => ∀ a, f a ∉ B a.val)).image
            (fun f => rawVec (copyAssign M f))).card :=
          (Finset.card_image_of_injective _ (copiesSet_injective M)).symm
      _ ≤ ((copiesSet (d := d) M).filter (fun v => C.eval v = false)).card :=
          Finset.card_le_card hsub_img
  rcases exists_filled d E L (min_le_right _ _) x hxb hxs_L with ⟨x1, hx1b, hx1s, hx1obj⟩
  have hx1p : (Finset.univ.filter (fun c : Fin n => 0 < x1 c ∧ x1 c < d)).card ≤ n := by
    calc (Finset.univ.filter (fun c : Fin n => 0 < x1 c ∧ x1 c < d)).card
        ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = n := by simp
  rcases exists_rounded d E L n x1 hx1b hx1s hx1p with ⟨y, hyb, hys, hyp, hyobj⟩
  rcases obj_eq_scoreVal d hd E L y hyb hys hyp with ⟨hshape, hsc⟩
  refine ⟨Finset.univ.filter (fun a : Fin n => y a = d),
    Finset.univ.filter (fun a : Fin n => 0 < y a ∧ y a < d), hshape, ?_⟩
  rw [hsc]
  exact le_trans hyobj (le_trans hx1obj (le_trans hobj_le hloss))

private lemma exists_subset_card_mod {d L : ℕ} (hd : 0 < d) :
    ∃ U : Finset (Fin d), U.card = L % d := by
  have hlt : L % d < d := Nat.mod_lt L hd
  refine ⟨Finset.univ.filter (fun i : Fin d => i.val < L % d), ?_⟩
  have himg : Finset.univ.filter (fun i : Fin d => i.val < L % d) =
      (Finset.range (L % d)).attach.image (fun x => ⟨x.val, lt_trans (Finset.mem_range.mp x.property) hlt⟩) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_attach]
    constructor
    · intro hi
      exact ⟨⟨i.val, Finset.mem_range.mpr hi⟩, Fin.ext rfl⟩
    · rintro ⟨⟨v, hv⟩, heq⟩
      have hval : i.val = v := congrArg Fin.val heq.symm
      rw [hval]; exact Finset.mem_range.mp hv
  rw [himg, Finset.card_image_of_injective]
  · simp
  · intro x y h; exact Subtype.ext (congrArg Fin.val h)

-- =========================================================================
-- Part 5: Main assembly (zero omega under letI)
-- =========================================================================

private noncomputable def lossVal {n d : ℕ} (E : Finset (Finset (Fin n))) (C : Circuit) : ℕ :=
  ((E.biUnion (copiesSet (d := d))).filter (fun v => C.eval v = false)).card

private theorem main_aux :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    ∀ (n d : Nat) (E : Finset (Finset (Fin n))), 0 < d →
      let raw := fun (x : Fin n → Fin d → Bool) =>
        (List.ofFn (fun a : Fin n => List.ofFn (x a))).flatten ++ [false,true]
      let copies := fun M : Finset (Fin n) =>
        Finset.univ.image (fun f : {a : Fin n // a ∈ M} → Fin d =>
          raw (fun a k => if h : a ∈ M then decide (f ⟨a,h⟩ = k) else false))
      let positive := E.biUnion copies
      let N := n*d+2
      let good := fun (s : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
        PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack N C ∧
        C.output < N+C.size ∧ C.size ≤ s ∧ C.eval (raw (fun _ _ => false)) = false
      let loss := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
        (positive.filter (fun x => C.eval x = false)).card
      ∀ s : Nat,
        let L := min (s+1) (n*d)
        let k := L / d
        let u := L % d
        let shape := fun S T : Finset (Fin n) =>
          S.card = k ∧ T.card = (if u = 0 then 0 else 1) ∧ Disjoint S T
        let score := fun S T : Finset (Fin n) =>
          (E.filter (fun M => Disjoint M S)).sum (fun M =>
            if Disjoint M T then d^M.card else (d-u)*d^(M.card-1))
        (∀ t : Nat, (∃ C, good s C ∧ loss C ≤ t) ↔
          ∃ S T, shape S T ∧ score S T ≤ t) ∧
        ∀ (S T : Finset (Fin n)) (U : Finset (Fin d)), shape S T → U.card = u →
          let chosen := fun (a : Fin n) (i : Fin d) => a ∈ S ∨ (a ∈ T ∧ i ∈ U)
          ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
            good s C ∧ (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
            (∀ (a : Fin n) (i : Fin d),
              (C.output = a.val*d+i.val ∨ ∃ g ∈ C.gates, a.val*d+i.val ∈ g.inputs) ↔ chosen a i) ∧
            (∀ x, C.eval (raw x) = decide (∃ a i, chosen a i ∧ x a i = true)) ∧
            loss C = score S T := by
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  intro n d E hd
  dsimp only
  intro s
  set L := min (s + 1) (n * d)
  set k := L / d
  set u := L % d
  have hloss_eq : ∀ C : Circuit,
      ((E.biUnion (fun M => Finset.univ.image (fun f : {a : Fin n // a ∈ M} → Fin d =>
          (List.ofFn (fun a : Fin n => List.ofFn (fun k : Fin d =>
            if h : a ∈ M then decide (f ⟨a, h⟩ = k) else false))).flatten ++ [false, true]))).filter
          (fun x => C.eval x = false)).card =
      lossVal (d := d) E C := by
    intro C
    unfold lossVal
    congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_biUnion, copiesSet, Finset.mem_image, Finset.mem_univ, true_and]
    rfl
  have hite_u : @ite ℕ (u = 0) (Classical.propDecidable _) 0 1 =
      @ite ℕ (u = 0) (instDecidableEqNat _ _) 0 1 := by
    by_cases h : u = 0 <;> simp [h]
  have hscore_eq : ∀ S T : Finset (Fin n),
      (E.filter (fun M => Disjoint M S)).sum (fun M =>
        if Disjoint M T then d ^ M.card else (d - u) * d ^ (M.card - 1)) =
      scoreVal d u E S T := by
    intro S T
    unfold scoreVal
    refine Finset.sum_congr (by ext M; simp) (fun M _ => ?_)
    by_cases h : Disjoint M T <;> simp [h]
  constructor
  · intro t
    constructor
    · rintro ⟨C, ⟨hfan, hrb, hout, hsz, hzero⟩, hloss⟩
      rw [hloss_eq C] at hloss
      rcases lower_bound_loss hd E C hfan hrb hout hsz hzero hloss with ⟨S, T, ⟨hS, hT, hST⟩, hsc⟩
      refine ⟨S, T, ⟨hS, ?_, hST⟩, ?_⟩
      · rw [hite_u]; exact hT
      · rw [hscore_eq S T]; exact hsc
    · rintro ⟨S, T, ⟨hS, hT, hST⟩, hsc⟩
      rw [hite_u] at hT
      rw [hscore_eq S T] at hsc
      rcases exists_subset_card_mod (L := L) hd with ⟨U, hU⟩
      rcases build_for_STU hd E S T U hS hT hST hU with
        ⟨C, hfan, hrb, hout, hsz, hzero, _, _, _, hloss⟩
      refine ⟨C, ⟨hfan, hrb, hout, hsz, hzero⟩, ?_⟩
      rw [hloss_eq C]
      exact hloss.trans_le hsc
  · intro S T U ⟨hS, hT, hST⟩ hU
    rw [hite_u] at hT
    rcases build_for_STU hd E S T U hS hT hST hU with
      ⟨C, hfan, hrb, hout, hsz, hzero, hop, huse, hev, hloss⟩
    refine ⟨C, ⟨hfan, hrb, hout, hsz, hzero⟩, hop, huse, ?_, ?_⟩
    · intro x
      change C.eval (rawVec x) = _
      rw [hev x]
      exact congrArg (fun dec => @decide _ dec) (Subsingleton.elim _ _)
    · rw [hloss_eq C]
      exact hloss.trans (hscore_eq S T).symm

end PEqualNP.Outside.L_lib_1351_aux

theorem PEqualNP.Outside.L_lib_1351 :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    ∀ (n d : Nat) (E : Finset (Finset (Fin n))), 0 < d →
      let raw := fun (x : Fin n → Fin d → Bool) =>
        (List.ofFn (fun a : Fin n => List.ofFn (x a))).flatten ++ [false,true]
      let copies := fun M : Finset (Fin n) =>
        Finset.univ.image (fun f : {a : Fin n // a ∈ M} → Fin d =>
          raw (fun a k => if h : a ∈ M then decide (f ⟨a,h⟩ = k) else false))
      let positive := E.biUnion copies
      let N := n*d+2
      let good := fun (s : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
        PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack N C ∧
        C.output < N+C.size ∧ C.size ≤ s ∧ C.eval (raw (fun _ _ => false)) = false
      let loss := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
        (positive.filter (fun x => C.eval x = false)).card
      ∀ s : Nat,
        let L := min (s+1) (n*d)
        let k := L / d
        let u := L % d
        let shape := fun S T : Finset (Fin n) =>
          S.card = k ∧ T.card = (if u = 0 then 0 else 1) ∧ Disjoint S T
        let score := fun S T : Finset (Fin n) =>
          (E.filter (fun M => Disjoint M S)).sum (fun M =>
            if Disjoint M T then d^M.card else (d-u)*d^(M.card-1))
        (∀ t : Nat, (∃ C, good s C ∧ loss C ≤ t) ↔
          ∃ S T, shape S T ∧ score S T ≤ t) ∧
        ∀ (S T : Finset (Fin n)) (U : Finset (Fin d)), shape S T → U.card = u →
          let chosen := fun (a : Fin n) (i : Fin d) => a ∈ S ∨ (a ∈ T ∧ i ∈ U)
          ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
            good s C ∧ (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
            (∀ (a : Fin n) (i : Fin d),
              (C.output = a.val*d+i.val ∨ ∃ g ∈ C.gates, a.val*d+i.val ∈ g.inputs) ↔ chosen a i) ∧
            (∀ x, C.eval (raw x) = decide (∃ a i, chosen a i ∧ x a i = true)) ∧
            loss C = score S T := by
  exact PEqualNP.Outside.L_lib_1351_aux.main_aux
