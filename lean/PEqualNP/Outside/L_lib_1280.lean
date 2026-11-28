import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1280_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket

local instance : DecidableEq GateOp := lineDegreeGateOpDecEq

lemma mem_of_mem_set {α : Type*} {l : List α} {i : ℕ} {a x : α} (h : x ∈ l.set i a) :
    x ∈ l ∨ x = a := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp h
  by_cases hki : k = i
  · right; subst hki; simp [List.getElem_set_self]
  · left; rw [List.getElem_set_ne (Ne.symm hki)]; exact List.getElem_mem (by simpa using hk)

lemma wires_step (gs : List Gate) (x : List Bool) :
    (Circuit.mk gs 0).wires x =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x := rfl

lemma foldl_wires_length (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length =
      w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp only [List.length_append, List.length_singleton]
    omega

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length :=
  foldl_wires_length C.gates x

lemma wires_append (gs1 gs2 : List Gate) (x : List Bool) (o : ℕ) :
    (Circuit.mk (gs1 ++ gs2) o).wires x =
      (Circuit.mk gs2 o).wires ((Circuit.mk gs1 0).wires x) := by
  simp only [Circuit.wires, List.foldl_append]

lemma foldl_wires_prefix (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) w).getD i false =
      w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]).length := by
      simp only [List.length_append, List.length_singleton]; omega
    rw [ih _ hlt]
    simp only [List.getD, List.getElem?_append_left hi]

lemma wires_prefix (gs1 gs2 : List Gate) (x : List Bool) (o : ℕ)
    (i : ℕ) (hi : i < x.length + gs1.length) :
    ((Circuit.mk (gs1 ++ gs2) o).wires x).getD i false =
      ((Circuit.mk gs1 0).wires x).getD i false := by
  rw [wires_append]
  apply foldl_wires_prefix
  rw [wires_length]
  exact hi

lemma wires_snoc (gs : List Gate) (g : Gate) (x : List Bool) (o : ℕ) :
    (Circuit.mk (gs ++ [g]) o).wires x =
      (Circuit.mk gs 0).wires x ++
        [g.op.eval (g.inputs.map fun i => ((Circuit.mk gs 0).wires x).getD i false)] := by
  rw [wires_append]
  simp only [Circuit.wires, List.foldl_cons, List.foldl_nil]

lemma wires_snoc_last (n0 : ℕ) (gs : List Gate) (g : Gate) (y : List Bool) (hy : y.length = n0) :
    ((Circuit.mk (gs ++ [g]) 0).wires y).getD (n0 + gs.length) false =
      g.op.eval (g.inputs.map fun i => ((Circuit.mk gs 0).wires y).getD i false) := by
  rw [wires_snoc]
  have hl : ((Circuit.mk gs 0).wires y).length = n0 + gs.length := by rw [wires_length, hy]
  simp only [List.getD, List.getElem?_append_right (Nat.le_of_eq hl), hl, Nat.sub_self,
    List.getElem?_cons_zero, Option.getD_some]

lemma wires_get_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false :=
  foldl_wires_prefix C.gates x i hi

lemma wires_get_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i =>
        ((Circuit.mk (C.gates.take j) 0).wires x).getD i false) := by
  have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
    have h1 := (List.take_append_drop j C.gates).symm
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simpa [List.append_assoc] using h1
  have hlen_take : (C.gates.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
  have hC : C.wires x = (Circuit.mk (C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1)) 0).wires x := by
    simp only [Circuit.wires, ← hsplit]
  rw [hC, wires_prefix (C.gates.take j ++ [C.gates[j]]) (C.gates.drop (j + 1)) x 0 (x.length + j)
    (by simp [hlen_take]; omega)]
  have hlen_eq : x.length + j = x.length + (C.gates.take j).length := by rw [hlen_take]
  rw [hlen_eq]
  exact wires_snoc_last x.length (C.gates.take j) C.gates[j] x rfl

lemma wires_get_gate_rb (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length)
    (hrb : ReadsBack x.length C) :
    (C.wires x).getD (x.length + j) false =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => (C.wires x).getD i false) := by
  rw [wires_get_gate C x j hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hlt : i < x.length + j := by
    have h1 := hrb j hj i
    simp only [gateAt, List.getD, List.getElem?_eq_getElem hj, Option.getD_some] at h1
    exact h1 hi
  have hsplit : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
  have hlen_take : (C.gates.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
  have hC : C.wires x = (Circuit.mk (C.gates.take j ++ C.gates.drop j) 0).wires x := by
    simp only [Circuit.wires, ← hsplit]
  rw [hC, wires_prefix (C.gates.take j) (C.gates.drop j) x 0 i (by omega)]

lemma wires_get_gate_rb_eq (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n)
    (j : ℕ) (hj : j < C.gates.length) (hrb : ReadsBack n C) :
    (C.wires x).getD (n + j) false =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => (C.wires x).getD i false) := by
  subst hx
  exact wires_get_gate_rb C x j hj hrb

lemma notCount_eq_gates (gs : List Gate) (o1 o2 : ℕ) :
    notCount ⟨gs, o1⟩ = notCount ⟨gs, o2⟩ := rfl

lemma notCount_append (gs1 gs2 : List Gate) (o : ℕ) :
    notCount ⟨gs1 ++ gs2, o⟩ = notCount ⟨gs1, 0⟩ + notCount ⟨gs2, 0⟩ := by
  simp only [notCount, List.filter_append, List.length_append]

lemma notCount_nil (o : ℕ) : notCount ⟨[], o⟩ = 0 := rfl

lemma notCount_singleton_and (ins : List ℕ) (o : ℕ) : notCount ⟨[⟨GateOp.and, ins⟩], o⟩ = 0 := rfl
lemma notCount_singleton_or (ins : List ℕ) (o : ℕ) : notCount ⟨[⟨GateOp.or, ins⟩], o⟩ = 0 := rfl
lemma notCount_singleton_not (ins : List ℕ) (o : ℕ) : notCount ⟨[⟨GateOp.not, ins⟩], o⟩ = 1 := rfl

lemma readsBack_append (n : ℕ) (gs1 gs2 : List Gate) (o : ℕ)
    (h1 : ReadsBack n ⟨gs1, 0⟩) (h2 : ReadsBack (n + gs1.length) ⟨gs2, 0⟩) :
    ReadsBack n ⟨gs1 ++ gs2, o⟩ := by
  intro j hj i hi
  simp only [gateAt, List.getD] at hi
  by_cases hlt : j < gs1.length
  · rw [List.getElem?_append_left hlt] at hi
    exact h1 j hlt i (by simpa [gateAt, List.getD] using hi)
  · have hge : gs1.length ≤ j := Nat.le_of_not_lt hlt
    rw [List.getElem?_append_right hge] at hi
    have hj2 : j - gs1.length < gs2.length := by simp at hj; omega
    have hres := h2 (j - gs1.length) hj2 i (by simpa [gateAt, List.getD] using hi)
    omega

lemma readsBack_snoc (n : ℕ) (gs : List Gate) (g : Gate) (o : ℕ)
    (h1 : ReadsBack n ⟨gs, 0⟩) (hg : ∀ i ∈ g.inputs, i < n + gs.length) :
    ReadsBack n ⟨gs ++ [g], o⟩ := by
  apply readsBack_append n gs [g] o h1
  intro j hj i hi
  have hj0 : j = 0 := by simp at hj; omega
  subst hj0
  simp only [gateAt, List.getD, List.getElem?_cons_zero, Option.getD_some] at hi
  have := hg i hi; omega

lemma fanInTwo_append (gs1 gs2 : List Gate) (o : ℕ)
    (h1 : FanInTwo ⟨gs1, 0⟩) (h2 : FanInTwo ⟨gs2, 0⟩) :
    FanInTwo ⟨gs1 ++ gs2, o⟩ := by
  intro g hg
  rcases List.mem_append.mp hg with h | h
  · exact h1 g h
  · exact h2 g h

lemma monotone2_append (gs1 gs2 : List Gate) (o : ℕ)
    (h1 : Monotone2 ⟨gs1, 0⟩) (h2 : Monotone2 ⟨gs2, 0⟩) :
    Monotone2 ⟨gs1 ++ gs2, o⟩ := by
  intro g hg
  rcases List.mem_append.mp hg with h | h
  · exact h1 g h
  · exact h2 g h

lemma monotone2_imp_fanInTwo (C : Circuit) (h : Monotone2 C) : FanInTwo C := by
  intro g hg
  have ⟨hop, hlen⟩ := h g hg
  refine ⟨?_, hlen⟩
  rcases hop with h1 | h2
  · left; exact h1
  · right; left; exact h2

lemma notCount_of_monotone2 (C : Circuit) (h : Monotone2 C) : notCount C = 0 := by
  unfold notCount
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro g hg
  have ⟨hop, _⟩ := h g hg
  rcases hop with h1 | h1
  · simp [h1]
  · simp only [Set.mem_singleton_iff] at h1; simp [h1]

def bitsToNat : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 2 ^ bs.length else 0) + bitsToNat bs

lemma bitsToNat_lt (bs : List Bool) : bitsToNat bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [bitsToNat]
  | cons b bs ih =>
    simp only [bitsToNat, List.length_cons, Nat.pow_succ]
    cases b <;> simp <;> omega

lemma bitsToNat_head_ge (b : Bool) (bs : List Bool) :
    2 ^ bs.length ≤ bitsToNat (b :: bs) ↔ b = true := by
  have hlt := bitsToNat_lt bs
  cases b <;> simp [bitsToNat] <;> omega

lemma bitsToNat_lt_of_first_diff : ∀ (bs1 bs2 : List Bool),
    bs1.length = bs2.length →
    (∃ i, i < bs1.length ∧ (∀ k < i, bs1[k]! = bs2[k]!) ∧ bs1[i]! = true ∧ bs2[i]! = false) →
    bitsToNat bs2 < bitsToNat bs1
  | [], [], _, ⟨i, hi, _⟩ => by simp at hi
  | a :: as, b :: bs, hlen, ⟨i, hi, hpre, h1, h2⟩ => by
    have hlen' : as.length = bs.length := by simpa using hlen
    cases i with
    | zero =>
      simp only [List.getElem!_cons_zero] at h1 h2
      subst h1; subst h2
      simp only [bitsToNat, ↓reduceIte, Bool.false_eq_true, zero_add, hlen']
      have hlt := bitsToNat_lt bs
      omega
    | succ i' =>
      have hab : a = b := by
        have := hpre 0 (Nat.zero_lt_succ i')
        simpa using this
      subst hab
      have hlt_tail : bitsToNat bs < bitsToNat as := by
        apply bitsToNat_lt_of_first_diff as bs hlen'
        refine ⟨i', by simp at hi; omega, ?_, ?_, ?_⟩
        · intro k hk
          have := hpre (k + 1) (Nat.succ_lt_succ hk)
          simpa using this
        · simpa using h1
        · simpa using h2
      simp only [bitsToNat, hlen']
      omega

def notIndices (gs : List Gate) : List ℕ :=
  (List.range gs.length).filter (fun j => decide ((gateAt ⟨gs, 0⟩ j).op = GateOp.not))

lemma notIndices_length (C : Circuit) : (notIndices C.gates).length = notCount C := by
  unfold notIndices notCount
  have haux : ∀ (gs : List Gate),
      ((List.range gs.length).filter (fun j => decide ((gateAt ⟨gs, 0⟩ j).op = GateOp.not))).length =
      (gs.filter (fun g => decide (g.op = GateOp.not))).length := by
    intro gs
    have hmap : gs = (List.range gs.length).map (fun j => gateAt ⟨gs, 0⟩ j) := by
      apply List.ext_getElem
      · simp
      · intro i hi1 hi2
        simp only [List.getElem_map, List.getElem_range, gateAt, List.getD,
          List.getElem?_eq_getElem hi1, Option.getD_some]
    conv_rhs => rw [hmap]
    rw [List.filter_map, List.length_map]
    rfl
  exact haux C.gates

lemma notIndices_mem (gs : List Gate) (j : ℕ) :
    j ∈ notIndices gs ↔ j < gs.length ∧ (gateAt ⟨gs, 0⟩ j).op = GateOp.not := by
  simp [notIndices]

lemma notIndices_pairwise_lt (gs : List Gate) : (notIndices gs).Pairwise (· < ·) :=
  List.Pairwise.filter _ List.pairwise_lt_range

lemma notIndices_get_lt (gs : List Gate) {a b : ℕ} (ha : a < (notIndices gs).length)
    (hb : b < (notIndices gs).length) (hab : a < b) :
    (notIndices gs)[a] < (notIndices gs)[b] :=
  List.pairwise_iff_getElem.mp (notIndices_pairwise_lt gs) a b ha hb hab

lemma gateOp_and_mono {l1 l2 : List Bool} (hlen : l1.length = l2.length)
    (hle : ∀ i < l1.length, l1[i]! ≤ l2[i]!) :
    GateOp.and.eval l1 ≤ GateOp.and.eval l2 := by
  simp only [GateOp.eval]
  cases h1 : l1.all id
  · exact Bool.false_le _
  · simp only [Bool.le_iff_imp, true_implies]
    rw [List.all_eq_true] at h1 ⊢
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb
    have hi1 : i < l1.length := by omega
    have hle_i := hle i hi1
    have h1i : l1[i]! = true := by
      have : l1[i] = true := h1 l1[i] (List.getElem_mem hi1)
      simpa [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi1] using this
    have h2i : l2[i]! = l2[i] := by
      simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    rw [h1i, h2i] at hle_i
    cases h : l2[i]
    · rw [h] at hle_i; exact absurd hle_i (by decide)
    · rfl

lemma gateOp_or_mono {l1 l2 : List Bool} (hlen : l1.length = l2.length)
    (hle : ∀ i < l1.length, l1[i]! ≤ l2[i]!) :
    GateOp.or.eval l1 ≤ GateOp.or.eval l2 := by
  simp only [GateOp.eval]
  cases h1 : l1.any id
  · exact Bool.false_le _
  · simp only [Bool.le_iff_imp, true_implies]
    rw [List.any_eq_true] at h1 ⊢
    obtain ⟨b, hb, rfl⟩ := h1
    obtain ⟨i, hi1, heq⟩ := List.mem_iff_getElem.mp hb
    have hi2 : i < l2.length := by omega
    refine ⟨l2[i], List.getElem_mem hi2, ?_⟩
    have hle_i := hle i hi1
    have h1i : l1[i]! = true := by
      simpa [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi1] using heq
    have h2i : l2[i]! = l2[i] := by
      simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi2]
    rw [h1i, h2i] at hle_i
    cases h : l2[i]
    · rw [h] at hle_i; exact absurd hle_i (by decide)
    · rfl

def notOutputs (n : ℕ) (C : Circuit) (y : List Bool) : List Bool :=
  (notIndices C.gates).map (fun j => (C.wires y).getD (n + j) false)

def notRank (n : ℕ) (C : Circuit) (y : List Bool) : ℕ :=
  bitsToNat (notOutputs n C y)

lemma notRank_lt (n : ℕ) (C : Circuit) (y : List Bool) :
    notRank n C y < 2 ^ notCount C := by
  unfold notRank notOutputs
  have hlen : ((notIndices C.gates).map (fun j => (C.wires y).getD (n + j) false)).length = notCount C := by
    rw [List.length_map, notIndices_length]
  rw [← hlen]
  exact bitsToNat_lt _

lemma wires_mono_up_to (n : ℕ) (C : Circuit) (y1 y2 : List Bool) (k : ℕ)
    (hfit : FanInTwo C) (hrb : ReadsBack n C)
    (hy1 : y1.length = n) (hy2 : y2.length = n)
    (hin : ∀ i < n, y1.getD i false ≤ y2.getD i false)
    (hnot : ∀ j < k, j < C.gates.length → (gateAt C j).op = GateOp.not →
      (C.wires y1).getD (n + j) false = (C.wires y2).getD (n + j) false) :
    ∀ w < n + k, w < n + C.gates.length → (C.wires y1).getD w false ≤ (C.wires y2).getD w false := by
  intro w hw hwb
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hwn : w < n
    · rw [wires_get_input C y1 w (by omega), wires_get_input C y2 w (by omega)]
      exact hin w hwn
    · let j := w - n
      have hj : j < C.gates.length := by omega
      have hjk : j < k := by omega
      have hw_eq : w = n + j := by omega
      rw [hw_eq]
      have hgat : gateAt C j = C.gates[j] := by
        simp [gateAt, List.getD, List.getElem?_eq_getElem hj]
      have ⟨hop, _⟩ := hfit C.gates[j] (List.getElem_mem hj)
      rcases hop with hand | hor | hnotop
      · rw [wires_get_gate_rb_eq n C y1 hy1 j hj hrb, wires_get_gate_rb_eq n C y2 hy2 j hj hrb, hand]
        apply gateOp_and_mono (by simp)
        intro idx hidx
        simp only [List.length_map] at hidx
        have h1 : ((C.gates[j]).inputs.map (fun i => (C.wires y1).getD i false))[idx]! =
            (C.wires y1).getD (C.gates[j]).inputs[idx] false := by
          simp [List.getElem!_eq_getElem?_getD, hidx]
        have h2 : ((C.gates[j]).inputs.map (fun i => (C.wires y2).getD i false))[idx]! =
            (C.wires y2).getD (C.gates[j]).inputs[idx] false := by
          simp [List.getElem!_eq_getElem?_getD, hidx]
        rw [h1, h2]
        have hlt_rb : (C.gates[j]).inputs[idx] < n + j := by
          have := hrb j hj (C.gates[j]).inputs[idx] (by rw [hgat]; exact List.getElem_mem hidx)
          exact this
        exact ih _ (by omega) (by omega) (by omega)
      · rw [wires_get_gate_rb_eq n C y1 hy1 j hj hrb, wires_get_gate_rb_eq n C y2 hy2 j hj hrb, hor]
        apply gateOp_or_mono (by simp)
        intro idx hidx
        simp only [List.length_map] at hidx
        have h1 : ((C.gates[j]).inputs.map (fun i => (C.wires y1).getD i false))[idx]! =
            (C.wires y1).getD (C.gates[j]).inputs[idx] false := by
          simp [List.getElem!_eq_getElem?_getD, hidx]
        have h2 : ((C.gates[j]).inputs.map (fun i => (C.wires y2).getD i false))[idx]! =
            (C.wires y2).getD (C.gates[j]).inputs[idx] false := by
          simp [List.getElem!_eq_getElem?_getD, hidx]
        rw [h1, h2]
        have hlt_rb : (C.gates[j]).inputs[idx] < n + j := by
          have := hrb j hj (C.gates[j]).inputs[idx] (by rw [hgat]; exact List.getElem_mem hidx)
          exact this
        exact ih _ (by omega) (by omega) (by omega)
      · have heq := hnot j hjk hj (by rw [hgat]; exact hnotop)
        rw [heq]

lemma markov_step (n : ℕ) (C : Circuit) (y1 y2 : List Bool)
    (hfit : FanInTwo C) (hrb : ReadsBack n C) (hout : C.output < n + C.size)
    (hy1 : y1.length = n) (hy2 : y2.length = n)
    (hin : ∀ i < n, y1.getD i false ≤ y2.getD i false) :
    notRank n C y2 ≤ notRank n C y1 ∧
    (notRank n C y2 = notRank n C y1 → C.eval y1 ≤ C.eval y2) := by
  let bs1 := notOutputs n C y1
  let bs2 := notOutputs n C y2
  have hlen : bs1.length = bs2.length := by simp [bs1, bs2, notOutputs]
  by_cases heq : bs1 = bs2
  · have hrk : notRank n C y2 = notRank n C y1 := congrArg bitsToNat heq.symm
    refine ⟨le_of_eq hrk, fun _ => ?_⟩
    have hnot : ∀ j < C.gates.length, j < C.gates.length → (gateAt C j).op = GateOp.not →
        (C.wires y1).getD (n + j) false = (C.wires y2).getD (n + j) false := by
      intro j hj _ hop
      have hmem : j ∈ notIndices C.gates := (notIndices_mem C.gates j).mpr ⟨hj, hop⟩
      obtain ⟨idx, hidx, hget⟩ := List.mem_iff_getElem.mp hmem
      have h1 : bs1[idx]'(by simp [bs1, notOutputs, hidx]) = (C.wires y1).getD (n + j) false := by
        simp [bs1, notOutputs, hget]
      have h2 : bs2[idx]'(by simp [bs2, notOutputs, hidx]) = (C.wires y2).getD (n + j) false := by
        simp [bs2, notOutputs, hget]
      rw [← h1, ← h2]
      simp [heq]
    exact wires_mono_up_to n C y1 y2 C.gates.length hfit hrb hy1 hy2 hin hnot C.output hout hout
  · have hex_diff : ∃ idx, idx < bs1.length ∧ bs1[idx]! ≠ bs2[idx]! := by
      by_contra hall
      push_neg at hall
      apply heq
      apply List.ext_getElem hlen
      intro idx h1 h2
      have := hall idx h1
      simpa [List.getElem!_eq_getElem?_getD, h1, h2] using this
    let idx := Nat.find hex_diff
    have hidx_spec : idx < bs1.length ∧ bs1[idx]! ≠ bs2[idx]! := Nat.find_spec hex_diff
    have hidx_lt : idx < (notIndices C.gates).length := by
      have h1 : idx < bs1.length := hidx_spec.1
      simpa only [bs1, notOutputs, List.length_map] using h1
    let j0 := (notIndices C.gates)[idx]
    have hj0_mem : j0 ∈ notIndices C.gates := List.getElem_mem hidx_lt
    have ⟨hj0_lt, hj0_op⟩ := (notIndices_mem C.gates j0).mp hj0_mem
    have hpre_eq : ∀ k < idx, bs1[k]! = bs2[k]! := by
      intro k hk
      by_contra hne
      have hk_lt : k < bs1.length := lt_trans hk hidx_spec.1
      exact Nat.find_min hex_diff hk ⟨hk_lt, hne⟩
    have hnot_pre : ∀ j < j0, j < C.gates.length → (gateAt C j).op = GateOp.not →
        (C.wires y1).getD (n + j) false = (C.wires y2).getD (n + j) false := by
      intro j hjj0 hjlt hop
      have hmem : j ∈ notIndices C.gates := (notIndices_mem C.gates j).mpr ⟨hjlt, hop⟩
      obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hmem
      have hk_lt_idx : k < idx := by
        by_contra hge
        have hle : idx ≤ k := Nat.le_of_not_lt hge
        rcases lt_or_eq_of_le hle with hlt | rfl
        · have := notIndices_get_lt C.gates hidx_lt hk hlt
          omega
        · omega
      have h1 := hpre_eq k hk_lt_idx
      simp only [bs1, bs2, notOutputs, List.getElem!_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hk, Option.map_some, Option.getD_some, hget] at h1
      exact h1
    have hmono_pre := wires_mono_up_to n C y1 y2 j0 hfit hrb hy1 hy2 hin hnot_pre
    have hgat : gateAt C j0 = C.gates[j0] := by
      simp [gateAt, List.getD, List.getElem?_eq_getElem hj0_lt]
    have hj0_not : (C.gates[j0]).op = GateOp.not := by rw [← hgat]; exact hj0_op
    have hj0_ge : (C.wires y2).getD (n + j0) false ≤ (C.wires y1).getD (n + j0) false := by
      rw [wires_get_gate_rb_eq n C y1 hy1 j0 hj0_lt hrb, wires_get_gate_rb_eq n C y2 hy2 j0 hj0_lt hrb, hj0_not]
      simp only [GateOp.eval]
      cases hins : (C.gates[j0]).inputs with
      | nil => simp
      | cons u us =>
        simp only [List.map_cons, List.headD_cons]
        have hu_lt : u < n + j0 := by
          have := hrb j0 hj0_lt u (by rw [hgat, hins]; simp)
          exact this
        have hle_u := hmono_pre u hu_lt (by omega)
        cases h1 : (C.wires y1).getD u false <;> cases h2 : (C.wires y2).getD u false
        · simp
        · simp
        · rw [h1, h2] at hle_u; exact absurd hle_u (by decide)
        · simp
    have h1_eq : bs1[idx]! = (C.wires y1).getD (n + j0) false := by
      simp [bs1, notOutputs, List.getElem!_eq_getElem?_getD, hidx_lt, j0]
    have h2_eq : bs2[idx]! = (C.wires y2).getD (n + j0) false := by
      simp [bs2, notOutputs, List.getElem!_eq_getElem?_getD, hidx_lt, j0]
    have htf : bs1[idx]! = true ∧ bs2[idx]! = false := by
      have hne := hidx_spec.2
      rw [h1_eq, h2_eq] at hne ⊢
      cases hv1 : (C.wires y1).getD (n + j0) false <;>
        cases hv2 : (C.wires y2).getD (n + j0) false
      · exact (hne (by rw [hv1, hv2])).elim
      · rw [hv1, hv2] at hj0_ge; exact absurd hj0_ge (by decide)
      · exact ⟨rfl, rfl⟩
      · exact (hne (by rw [hv1, hv2])).elim
    have hlt_rk : notRank n C y2 < notRank n C y1 :=
      bitsToNat_lt_of_first_diff bs1 bs2 hlen ⟨idx, hidx_spec.1, hpre_eq, htf.1, htf.2⟩
    exact ⟨Nat.le_of_lt hlt_rk, fun h => by omega⟩

def remapWire (n m : ℕ) (z : Finset (Fin m)) [DecidablePred (· ∈ z)] (w : ℕ) : ℕ :=
  if h0 : w < n then w
  else if h : w < n + m then (if (⟨w - n, by omega⟩ : Fin m) ∈ z then n + 1 else n)
  else if w = n + m then n
  else if w = n + m + 1 then n + 1
  else w - m

lemma remapWire_lt (n m : ℕ) (z : Finset (Fin m)) [DecidablePred (· ∈ z)]
    (j w : ℕ) (hw : w < n + m + 2 + j) :
    remapWire n m z w < n + 2 + j := by
  unfold remapWire
  split_ifs <;> omega

def remapGate (n m : ℕ) (z : Finset (Fin m)) [DecidablePred (· ∈ z)] (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (remapWire n m z)⟩

def hardwirePrefix (n m : ℕ) (z : Finset (Fin m)) [DecidablePred (· ∈ z)]
    (C : Circuit) (len out : ℕ) : Circuit :=
  ⟨(C.gates.take len).map (remapGate n m z), remapWire n m z out⟩

lemma hardwirePrefix_readsBack (n m : ℕ) (z : Finset (Fin m)) [DecidablePred (· ∈ z)]
    (C : Circuit) (len out : ℕ) (hrb : ReadsBack (n + m + 2) C) :
    ReadsBack (n + 2) (hardwirePrefix n m z C len out) := by
  intro j hj i hi
  simp only [hardwirePrefix, List.length_map, List.length_take] at hj
  have hj_lt : j < C.gates.length := by omega
  have hj_take : j < (C.gates.take len).length := by simp; omega
  simp only [hardwirePrefix, gateAt, List.getD, List.getElem?_map,
    List.getElem?_eq_getElem hj_take, Option.map_some, Option.getD_some,
    List.getElem_take, remapGate, List.mem_map] at hi
  obtain ⟨u, hu, rfl⟩ := hi
  have hu_lt : u < n + m + 2 + j := by
    have h1 := hrb j hj_lt u
    simp only [gateAt, List.getD, List.getElem?_eq_getElem hj_lt, Option.getD_some] at h1
    exact h1 hu
  exact remapWire_lt n m z j u hu_lt

lemma hardwirePrefix_fanInTwo (n m : ℕ) (z : Finset (Fin m)) [DecidablePred (· ∈ z)]
    (C : Circuit) (len out : ℕ) (hfit : FanInTwo C) :
    FanInTwo (hardwirePrefix n m z C len out) := by
  intro g hg
  simp only [hardwirePrefix, List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  have ⟨hop, hlen⟩ := hfit g0 (List.mem_of_mem_take hg0)
  exact ⟨hop, by simpa [remapGate] using hlen⟩

lemma hardwirePrefix_wires (n m : ℕ) (z : Finset (Fin m)) [DecidablePred (· ∈ z)]
    (C : Circuit) (len out : ℕ) (hlen : len ≤ C.gates.length)
    (hrb : ReadsBack (n + m + 2) C)
    (xBits : List Bool) (hx : xBits.length = n)
    (zBits : List Bool) (hz : zBits.length = m)
    (hz_get : ∀ i : Fin m, zBits.getD i.val false = decide (i ∈ z)) :
    let D := hardwirePrefix n m z C len out
    let yD := xBits ++ [false, true]
    let yC := xBits ++ zBits ++ [false, true]
    ∀ w < n + m + 2 + len,
      (D.wires yD).getD (remapWire n m z w) false = (C.wires yC).getD w false := by
  intro D yD yC w hw
  have hyD : yD.length = n + 2 := by simp [yD, hx]
  have hyC : yC.length = n + m + 2 := by simp [yC, hx, hz]; omega
  have hrbD : ReadsBack (n + 2) D := hardwirePrefix_readsBack n m z C len out hrb
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hwn : w < n
    · have hrm : remapWire n m z w = w := by simp [remapWire, hwn]
      rw [hrm, wires_get_input D yD w (by omega), wires_get_input C yC w (by omega)]
      simp only [yD, yC, List.getD, List.append_assoc, List.getElem?_append_left (by omega : w < xBits.length)]
    · by_cases hwm : w < n + m
      · have hrm : remapWire n m z w = if (⟨w - n, by omega⟩ : Fin m) ∈ z then n + 1 else n := by
          simp [remapWire, hwn, hwm]
        rw [hrm]
        rw [wires_get_input C yC w (by omega)]
        have hC_val : yC.getD w false = zBits.getD (w - n) false := by
          simp only [yC, List.getD]
          rw [List.getElem?_append_left (by simp [hx, hz]; omega)]
          rw [List.getElem?_append_right (by omega : xBits.length ≤ w)]
          rw [hx]
        rw [hC_val, hz_get ⟨w - n, by omega⟩]
        by_cases hmem : (⟨w - n, by omega⟩ : Fin m) ∈ z
        · simp only [hmem, ↓reduceIte, decide_true]
          rw [wires_get_input D yD (n + 1) (by omega)]
          simp only [yD, List.getD, List.getElem?_append_right (by omega : xBits.length ≤ n + 1), hx]
          have : n + 1 - n = 1 := by omega
          rw [this]; rfl
        · simp only [hmem, ↓reduceIte, decide_false]
          rw [wires_get_input D yD n (by omega)]
          simp only [yD, List.getD, List.getElem?_append_right (by omega : xBits.length ≤ n), hx, Nat.sub_self]
          rfl
      · by_cases hw0 : w = n + m
        · have hrm : remapWire n m z w = n := by simp [remapWire, hwn, hwm, hw0]
          rw [hrm, wires_get_input D yD n (by omega), wires_get_input C yC w (by omega)]
          simp only [yD, yC, List.getD, hw0]
          rw [List.getElem?_append_right (by omega : xBits.length ≤ n), hx, Nat.sub_self]
          rw [List.getElem?_append_right (by simp [hx, hz])]
          simp [hx, hz]
        · by_cases hw1 : w = n + m + 1
          · have hrm : remapWire n m z w = n + 1 := by
              rw [hw1]; unfold remapWire
              have h1 : ¬(n + m + 1 < n) := by omega
              have h2 : ¬(n + m + 1 < n + m) := by omega
              have h3 : n + m + 1 ≠ n + m := by omega
              simp [h1, h2, h3]
            rw [hrm, wires_get_input D yD (n + 1) (by omega), wires_get_input C yC w (by omega)]
            have hlen_xz : (xBits ++ zBits).length = n + m := by simp [hx, hz]
            simp only [yD, yC, List.getD, hw1]
            rw [List.getElem?_append_right (by omega : xBits.length ≤ n + 1), hx]
            rw [List.getElem?_append_right (by omega : (xBits ++ zBits).length ≤ n + m + 1), hlen_xz]
            have h1 : n + 1 - n = 1 := by omega
            have h2 : n + m + 1 - (n + m) = 1 := by omega
            rw [h1, h2]
          · let j := w - (n + m + 2)
            have hj_len : j < len := by omega
            have hj_C : j < C.gates.length := by omega
            have hj_D : j < D.gates.length := by
              simp [D, hardwirePrefix, hj_len, hj_C]
            have hrm : remapWire n m z w = (n + 2) + j := by
              simp [remapWire, hwn, hwm, hw0, hw1]; omega
            have hw_eq : w = (n + m + 2) + j := by omega
            rw [hrm, wires_get_gate_rb_eq (n + 2) D yD hyD j hj_D hrbD]
            rw [hw_eq, wires_get_gate_rb_eq (n + m + 2) C yC hyC j hj_C hrb]
            have hDj : D.gates[j] = remapGate n m z C.gates[j] := by
              simp [D, hardwirePrefix]
            rw [hDj]
            simp only [remapGate, List.map_map]
            congr 1
            apply List.map_congr_left
            intro u hu
            have hu_lt : u < n + m + 2 + j := by
              have h1 := hrb j hj_C u
              simp only [gateAt, List.getD, List.getElem?_eq_getElem hj_C, Option.getD_some] at h1
              exact h1 hu
            exact ih u (by omega) (by omega)

def IsBitonic (v : List Bool) : Prop :=
  (∃ a b c, v = List.replicate a true ++ List.replicate b false ++ List.replicate c true) ∨
  (∃ a b c, v = List.replicate a false ++ List.replicate b true ++ List.replicate c false)

def isSortedDesc (v : List Bool) : Prop :=
  v = List.replicate (v.count true) true ++ List.replicate (v.length - v.count true) false

def isSortedAsc (v : List Bool) : Prop :=
  v = List.replicate (v.length - v.count true) false ++ List.replicate (v.count true) true

lemma count_true_replicate (k : ℕ) (b : Bool) :
    (List.replicate k b).count true = if b then k else 0 := by
  cases b <;> simp [List.count_replicate]

lemma replicate_add_append {α : Type*} (a b : ℕ) (x : α) :
    List.replicate (a + b) x = List.replicate a x ++ List.replicate b x := by
  induction a with
  | zero => simp
  | succ a ih => rw [Nat.succ_add, List.replicate_succ, List.replicate_succ, ih]; rfl

lemma isSortedDesc_iff (v : List Bool) :
    isSortedDesc v ↔ ∃ a b, v = List.replicate a true ++ List.replicate b false := by
  constructor
  · intro h; exact ⟨_, _, h⟩
  · rintro ⟨a, b, rfl⟩
    unfold isSortedDesc
    simp only [List.count_append, count_true_replicate, ↓reduceIte, Bool.false_eq_true, add_zero,
      List.length_append, List.length_replicate, Nat.add_sub_cancel_left]

lemma isSortedAsc_iff (v : List Bool) :
    isSortedAsc v ↔ ∃ a b, v = List.replicate a false ++ List.replicate b true := by
  constructor
  · intro h; exact ⟨_, _, h⟩
  · rintro ⟨a, b, rfl⟩
    unfold isSortedAsc
    simp only [List.count_append, count_true_replicate, ↓reduceIte, Bool.false_eq_true,
      zero_add, List.length_append, List.length_replicate, Nat.add_sub_cancel]

lemma bitonic_of_desc_asc {u w : List Bool} (hu : isSortedDesc u) (hw : isSortedAsc w) :
    IsBitonic (u ++ w) := by
  obtain ⟨a, b, rfl⟩ := (isSortedDesc_iff u).mp hu
  obtain ⟨c, d, rfl⟩ := (isSortedAsc_iff w).mp hw
  left
  refine ⟨a, b + c, d, ?_⟩
  rw [replicate_add_append]; simp only [List.append_assoc]

lemma applyComp_len (v : List Bool) (i j : ℕ) :
    ((v.set i (v.getD i false || v.getD j false)).set j (v.getD i false && v.getD j false)).length = v.length := by
  simp

def applyComp (v : List Bool) (p : ℕ × ℕ) : List Bool :=
  let a := v.getD p.1 false
  let b := v.getD p.2 false
  (v.set p.1 (a || b)).set p.2 (a && b)

def applyComps (v : List Bool) (cs : List (ℕ × ℕ)) : List Bool :=
  cs.foldl applyComp v

lemma applyComps_append (v : List Bool) (c1 c2 : List (ℕ × ℕ)) :
    applyComps v (c1 ++ c2) = applyComps (applyComps v c1) c2 := by
  simp [applyComps, List.foldl_append]

lemma applyComps_length (v : List Bool) (cs : List (ℕ × ℕ)) :
    (applyComps v cs).length = v.length := by
  induction cs generalizing v with
  | nil => rfl
  | cons p cs ih =>
    change (applyComps (applyComp v p) cs).length = v.length
    rw [ih]
    simp [applyComp]

lemma applyComp_outside (v : List Bool) (p : ℕ × ℕ) (k : ℕ) (hk1 : k ≠ p.1) (hk2 : k ≠ p.2) :
    (applyComp v p).getD k false = v.getD k false := by
  simp only [applyComp, List.getD, List.getElem?_set_ne hk2.symm, List.getElem?_set_ne hk1.symm]

lemma applyComp_at (v : List Bool) (p : ℕ × ℕ) (hne : p.1 ≠ p.2)
    (h1 : p.1 < v.length) (h2 : p.2 < v.length) :
    (applyComp v p).getD p.1 false = (v.getD p.1 false || v.getD p.2 false) ∧
    (applyComp v p).getD p.2 false = (v.getD p.1 false && v.getD p.2 false) := by
  constructor
  · simp only [applyComp, List.getD, List.getElem?_set_ne hne.symm, List.getElem?_set_self h1, Option.getD_some]
  · simp only [applyComp, List.getD, List.getElem?_set_self (by simpa using h2 : p.2 < (v.set p.1 _).length), Option.getD_some]

def halfCleanComps (off s : ℕ) (dir : Bool) : List (ℕ × ℕ) :=
  (List.range s).map (fun i => if dir then (off + i, off + s + i) else (off + s + i, off + i))

def bitonicMergeComps (off : ℕ) (dir : Bool) : ℕ → List (ℕ × ℕ)
  | 0 => []
  | p + 1 =>
      halfCleanComps off (2 ^ p) dir ++
        bitonicMergeComps off dir p ++
        bitonicMergeComps (off + 2 ^ p) dir p

def bitonicSortComps (off : ℕ) (dir : Bool) : ℕ → List (ℕ × ℕ)
  | 0 => []
  | p + 1 =>
      bitonicSortComps off true p ++
        bitonicSortComps (off + 2 ^ p) false p ++
        bitonicMergeComps off dir (p + 1)

lemma halfCleanComps_length (off s : ℕ) (dir : Bool) :
    (halfCleanComps off s dir).length = s := by
  simp [halfCleanComps]

lemma bitonicMergeComps_length (off : ℕ) (dir : Bool) (p : ℕ) :
    2 * (bitonicMergeComps off dir p).length = p * 2 ^ p := by
  induction p generalizing off with
  | zero => simp [bitonicMergeComps]
  | succ p ih =>
    simp only [bitonicMergeComps, List.length_append, halfCleanComps_length]
    have h1 := ih off
    have h2 := ih (off + 2 ^ p)
    rw [Nat.pow_succ]
    linarith

lemma bitonicSortComps_length (off : ℕ) (dir : Bool) (p : ℕ) :
    4 * (bitonicSortComps off dir p).length = p * (p + 1) * 2 ^ p := by
  induction p generalizing off dir with
  | zero => simp [bitonicSortComps]
  | succ p ih =>
    simp only [bitonicSortComps, List.length_append]
    have h1 := ih off true
    have h2 := ih (off + 2 ^ p) false
    have hm := bitonicMergeComps_length off dir (p + 1)
    rw [Nat.pow_succ] at hm ⊢
    nlinarith

lemma halfCleanComps_valid (off s N : ℕ) (dir : Bool) (hN : off + 2 * s ≤ N) :
    ∀ p ∈ halfCleanComps off s dir, p.1 < N ∧ p.2 < N ∧ p.1 ≠ p.2 ∧
      off ≤ p.1 ∧ p.1 < off + 2 * s ∧ off ≤ p.2 ∧ p.2 < off + 2 * s := by
  intro p hp
  simp only [halfCleanComps, List.mem_map, List.mem_range] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  cases dir <;> simp <;> omega

lemma bitonicMergeComps_valid (off N : ℕ) (dir : Bool) (p : ℕ) (hN : off + 2 ^ p ≤ N) :
    ∀ q ∈ bitonicMergeComps off dir p, q.1 < N ∧ q.2 < N ∧ q.1 ≠ q.2 ∧
      off ≤ q.1 ∧ q.1 < off + 2 ^ p ∧ off ≤ q.2 ∧ q.2 < off + 2 ^ p := by
  induction p generalizing off with
  | zero => intro q hq; simp [bitonicMergeComps] at hq
  | succ p ih =>
    intro q hq
    simp only [bitonicMergeComps, List.mem_append] at hq
    have hp2 : 2 ^ (p + 1) = 2 * 2 ^ p := by rw [Nat.pow_succ]; ring
    rcases hq with (h1 | h2) | h3
    · have := halfCleanComps_valid off (2 ^ p) N dir (by omega) q h1
      omega
    · have := ih off (by omega) q h2
      omega
    · have := ih (off + 2 ^ p) (by omega) q h3
      omega

lemma bitonicSortComps_valid (off N : ℕ) (dir : Bool) (p : ℕ) (hN : off + 2 ^ p ≤ N) :
    ∀ q ∈ bitonicSortComps off dir p, q.1 < N ∧ q.2 < N ∧ q.1 ≠ q.2 ∧
      off ≤ q.1 ∧ q.1 < off + 2 ^ p ∧ off ≤ q.2 ∧ q.2 < off + 2 ^ p := by
  induction p generalizing off dir with
  | zero => intro q hq; simp [bitonicSortComps] at hq
  | succ p ih =>
    intro q hq
    simp only [bitonicSortComps, List.mem_append] at hq
    have hp2 : 2 ^ (p + 1) = 2 * 2 ^ p := by rw [Nat.pow_succ]; ring
    rcases hq with (h1 | h2) | h3
    · have := ih off true (by omega) q h1; omega
    · have := ih (off + 2 ^ p) false (by omega) q h2; omega
    · exact bitonicMergeComps_valid off N dir (p + 1) hN q h3

lemma applyComps_outside (v : List Bool) (cs : List (ℕ × ℕ)) (k : ℕ)
    (hout : ∀ q ∈ cs, k ≠ q.1 ∧ k ≠ q.2) :
    (applyComps v cs).getD k false = v.getD k false := by
  induction cs generalizing v with
  | nil => rfl
  | cons p cs ih =>
    change (applyComps (applyComp v p) cs).getD k false = v.getD k false
    have hp := hout p (List.mem_cons_self ..)
    rw [ih (applyComp v p) (fun q hq => hout q (List.mem_cons_of_mem p hq))]
    exact applyComp_outside v p k hp.1 hp.2

lemma applyComps_halfClean_get (v : List Bool) (off s : ℕ) (dir : Bool)
    (hN : off + 2 * s ≤ v.length) (k : ℕ) :
    (applyComps v (halfCleanComps off s dir)).getD k false =
      if off ≤ k ∧ k < off + s then
        if dir then (v.getD k false || v.getD (k + s) false)
        else (v.getD k false && v.getD (k + s) false)
      else if off + s ≤ k ∧ k < off + 2 * s then
        if dir then (v.getD (k - s) false && v.getD k false)
        else (v.getD (k - s) false || v.getD k false)
      else v.getD k false := by

  suffices ∀ r ≤ s,
      (applyComps v ((List.range r).map
        (fun i => if dir then (off + i, off + s + i) else (off + s + i, off + i)))).getD k false =
      if off ≤ k ∧ k < off + r then
        if dir then (v.getD k false || v.getD (k + s) false)
        else (v.getD k false && v.getD (k + s) false)
      else if off + s ≤ k ∧ k < off + s + r then
        if dir then (v.getD (k - s) false && v.getD k false)
        else (v.getD (k - s) false || v.getD k false)
      else v.getD k false by
    have h := this s le_rfl
    simpa [halfCleanComps, two_mul, Nat.add_assoc] using h
  intro r hr
  induction r with
  | zero =>
    simp only [List.range_zero, List.map_nil, applyComps, List.foldl_nil, Nat.add_zero]
    have h1 : ¬(off ≤ k ∧ k < off) := by omega
    have h2 : ¬(off + s ≤ k ∧ k < off + s) := by omega
    simp [h1, h2]
  | succ r ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, applyComps_append]
    let v' := applyComps v ((List.range r).map
      (fun i => if dir then (off + i, off + s + i) else (off + s + i, off + i)))
    have hv'_len : v'.length = v.length := applyComps_length _ _
    have hprev := ih (Nat.le_of_succ_le hr)
    let p := if dir then (off + r, off + s + r) else (off + s + r, off + r)
    have hne : p.1 ≠ p.2 := by cases dir <;> simp [p] <;> omega
    have h1 : p.1 < v'.length := by cases dir <;> simp [p, hv'_len] <;> omega
    have h2 : p.2 < v'.length := by cases dir <;> simp [p, hv'_len] <;> omega
    have hv'_r1 : v'.getD (off + r) false = v.getD (off + r) false := by
      apply applyComps_outside
      intro q hq; simp only [List.mem_map, List.mem_range] at hq
      obtain ⟨i, hi, rfl⟩ := hq; cases dir <;> simp <;> omega
    have hv'_r2 : v'.getD (off + s + r) false = v.getD (off + s + r) false := by
      apply applyComps_outside
      intro q hq; simp only [List.mem_map, List.mem_range] at hq
      obtain ⟨i, hi, rfl⟩ := hq; cases dir <;> simp <;> omega
    change (applyComp v' p).getD k false = _
    by_cases hk1 : k = off + r
    · subst hk1
      cases dir
      · have hres := (applyComp_at v' p hne h1 h2).2
        have hp_eq : p = (off + s + r, off + r) := rfl
        rw [hp_eq] at hres ⊢
        simp only [hv'_r1, hv'_r2] at hres
        rw [hres, Bool.and_comm]
        simp [show off + r + s = off + s + r by omega]
      · have hres := (applyComp_at v' p hne h1 h2).1
        have hp_eq : p = (off + r, off + s + r) := rfl
        rw [hp_eq] at hres ⊢
        simp only [hv'_r1, hv'_r2] at hres
        rw [hres]
        simp [show off + r + s = off + s + r by omega]
    · by_cases hk2 : k = off + s + r
      · subst hk2
        cases dir
        · have hres := (applyComp_at v' p hne h1 h2).1
          have hp_eq : p = (off + s + r, off + r) := rfl
          rw [hp_eq] at hres ⊢
          simp only [hv'_r1, hv'_r2] at hres
          rw [hres, Bool.or_comm]
          have hcond1 : ¬(off ≤ off + s + r ∧ off + s + r < off + (r + 1)) := by omega
          have hcond2 : off + s ≤ off + s + r ∧ off + s + r < off + s + (r + 1) := by omega
          have hsub : off + s + r - s = off + r := by omega
          simp [hcond1, hcond2, hsub]
        · have hres := (applyComp_at v' p hne h1 h2).2
          have hp_eq : p = (off + r, off + s + r) := rfl
          rw [hp_eq] at hres ⊢
          simp only [hv'_r1, hv'_r2] at hres
          rw [hres]
          have hcond1 : ¬(off ≤ off + s + r ∧ off + s + r < off + (r + 1)) := by omega
          have hcond2 : off + s ≤ off + s + r ∧ off + s + r < off + s + (r + 1) := by omega
          have hsub : off + s + r - s = off + r := by omega
          simp [hcond1, hcond2, hsub]
      · have hne1 : k ≠ p.1 := by cases dir <;> simp [p] <;> omega
        have hne2 : k ≠ p.2 := by cases dir <;> simp [p] <;> omega
        rw [applyComp_outside v' p k hne1 hne2, hprev]
        by_cases ha : off ≤ k ∧ k < off + r
        · have ha' : off ≤ k ∧ k < off + (r + 1) := by omega
          simp [ha, ha']
        · have ha' : ¬(off ≤ k ∧ k < off + (r + 1)) := by omega
          by_cases hb : off + s ≤ k ∧ k < off + s + r
          · have hb' : off + s ≤ k ∧ k < off + s + (r + 1) := by omega
            simp [ha, ha', hb, hb']
          · have hb' : ¬(off + s ≤ k ∧ k < off + s + (r + 1)) := by omega
            simp [ha, ha', hb, hb']

lemma halfClean_bitonic_lists (s : ℕ) (u w : List Bool)
    (hu : u.length = s) (hw : w.length = s) (hbit : IsBitonic (u ++ w)) :
    let top := List.ofFn (fun i : Fin s => u.getD i.val false || w.getD i.val false)
    let bot := List.ofFn (fun i : Fin s => u.getD i.val false && w.getD i.val false)
    IsBitonic top ∧ IsBitonic bot ∧
    (top = List.replicate s true ∨ bot = List.replicate s false) ∧
    top.count true + bot.count true = (u ++ w).count true := by
  intro top bot

  have hcount : top.count true + bot.count true = (u ++ w).count true := by
    have hcnt_fn : ∀ (t : ℕ) (g : Fin t → Bool),
        (List.ofFn g).count true = ∑ i : Fin t, if g i then 1 else 0 := by
      intro t
      induction t with
      | zero => intro g; simp
      | succ t ih =>
        intro g
        rw [List.ofFn_succ, List.count_cons, Fin.sum_univ_succ, ih (fun i : Fin t => g i.succ)]
        cases g 0 <;> simp <;> omega
    have hcnt : ∀ (l : List Bool) (hl : l.length = s),
        l.count true = ∑ i : Fin s, if l.getD i.val false then 1 else 0 := by
      intro l hl
      have hl_eq : l = List.ofFn (fun i : Fin s => l.getD i.val false) := by
        apply List.ext_getElem (by simp [hl])
        intro i h1 h2
        simp [List.getD, List.getElem?_eq_getElem h1]
      conv_lhs => rw [hl_eq]
      exact hcnt_fn s (fun i : Fin s => l.getD i.val false)
    rw [List.count_append, hcnt top (by simp [top]), hcnt bot (by simp [bot]),
      hcnt u hu, hcnt w hw, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have ht : top.getD i.val false = (u.getD i.val false || w.getD i.val false) := by
      simp [top, List.getD]
    have hb : bot.getD i.val false = (u.getD i.val false && w.getD i.val false) := by
      simp [bot, List.getD]
    rw [ht, hb]
    cases u.getD i.val false <;> cases w.getD i.val false <;> simp

  have hget_u : ∀ i : Fin s, u.getD i.val false = (u ++ w).getD i.val false := by
    intro i; simp [List.getD, List.getElem?_append_left (by omega : i.val < u.length)]
  have hget_w : ∀ i : Fin s, w.getD i.val false = (u ++ w).getD (s + i.val) false := by
    intro i
    simp [List.getD, List.getElem?_append_right (by omega : u.length ≤ s + i.val), hu]

  have hmk_010 : ∀ (l : List Bool) (hl : l.length = s) (lo hi : ℕ), lo ≤ hi → hi ≤ s →
      (∀ i : Fin s, l.getD i.val false = decide (lo ≤ i.val ∧ i.val < hi)) →
      l = List.replicate lo false ++ List.replicate (hi - lo) true ++ List.replicate (s - hi) false := by
    intro l hl lo hi h1 h2 hspec
    apply List.ext_getElem (by simp [hl]; omega)
    intro i hlt1 hlt2
    have hlt_s : i < s := by omega
    have hL : l[i] = decide (lo ≤ i ∧ i < hi) := by
      have := hspec ⟨i, hlt_s⟩
      simpa [List.getD, List.getElem?_eq_getElem hlt1] using this
    rw [hL]
    by_cases c1 : i < lo
    · have hfalse : ¬(lo ≤ i ∧ i < hi) := by omega
      simp [hfalse, List.getElem_append_left (by simp; omega : i < (List.replicate lo false ++ List.replicate (hi - lo) true).length),
        List.getElem_append_left (by simp; omega : i < (List.replicate lo false).length)]
    · by_cases c2 : i < hi
      · have htrue : lo ≤ i ∧ i < hi := by omega
        rw [decide_eq_true htrue]
        rw [List.getElem_append_left (by simp; omega)]
        rw [List.getElem_append_right (by simp; omega)]
        simp
      · have hfalse : ¬(lo ≤ i ∧ i < hi) := by omega
        rw [decide_eq_false hfalse]
        rw [List.getElem_append_right (by simp; omega)]
        simp
  have hmk_101 : ∀ (l : List Bool) (hl : l.length = s) (lo hi : ℕ), lo ≤ hi → hi ≤ s →
      (∀ i : Fin s, l.getD i.val false = decide (¬(lo ≤ i.val ∧ i.val < hi))) →
      l = List.replicate lo true ++ List.replicate (hi - lo) false ++ List.replicate (s - hi) true := by
    intro l hl lo hi h1 h2 hspec
    apply List.ext_getElem (by simp [hl]; omega)
    intro i hlt1 hlt2
    have hlt_s : i < s := by omega
    have hL : l[i] = decide (¬(lo ≤ i ∧ i < hi)) := by
      have := hspec ⟨i, hlt_s⟩
      simpa [List.getD, List.getElem?_eq_getElem hlt1] using this
    rw [hL]
    by_cases c1 : i < lo
    · have htrue : ¬(lo ≤ i ∧ i < hi) := by omega
      rw [decide_eq_true htrue]
      rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega)]
      simp
    · by_cases c2 : i < hi
      · have hfalse : ¬¬(lo ≤ i ∧ i < hi) := by omega
        rw [decide_eq_false hfalse]
        rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
        simp
      · have htrue : ¬(lo ≤ i ∧ i < hi) := by omega
        rw [decide_eq_true htrue]
        rw [List.getElem_append_right (by simp; omega)]
        simp
  have hmk_all : ∀ (l : List Bool) (hl : l.length = s) (b : Bool),
      (∀ i : Fin s, l.getD i.val false = b) → l = List.replicate s b := by
    intro l hl b hspec
    apply List.ext_getElem (by simp [hl])
    intro i h1 h2
    have := hspec ⟨i, by omega⟩
    simpa [List.getD, List.getElem?_eq_getElem h1] using this

  rcases hbit with ⟨a, b, c, hshape⟩ | ⟨a, b, c, hshape⟩
  ·
    have hsum : a + b + c = 2 * s := by
      have := congrArg List.length hshape; simp [hu, hw] at this; omega
    have hval : ∀ k < 2 * s, (u ++ w).getD k false = decide (¬(a ≤ k ∧ k < a + b)) := by
      intro k hk
      rw [hshape, List.getD]
      by_cases c1 : k < a
      · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega)]
        simp [c1, show ¬(a ≤ k ∧ k < a + b) by omega]
      · by_cases c2 : k < a + b
        · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by simp; omega)]
          simp [show a ≤ k ∧ k < a + b by omega, show k - a < b by omega]
        · rw [List.getElem?_append_right (by simp; omega)]
          simp [show ¬(a ≤ k ∧ k < a + b) by omega, show k - (a + b) < c by omega]
    have htop_get : ∀ i : Fin s, top.getD i.val false =
        decide (¬((a ≤ i.val ∧ i.val < a + b) ∧ (a ≤ s + i.val ∧ s + i.val < a + b))) := by
      intro i
      have ht : top.getD i.val false = (u.getD i.val false || w.getD i.val false) := by simp [top, List.getD]
      rw [ht, hget_u, hget_w, hval i.val (by omega), hval (s + i.val) (by omega)]
      by_cases p1 : a ≤ i.val ∧ i.val < a + b <;> by_cases p2 : a ≤ s + i.val ∧ s + i.val < a + b <;> simp [p1, p2]
    have hbot_get : ∀ i : Fin s, bot.getD i.val false =
        decide (¬((a ≤ i.val ∧ i.val < a + b) ∨ (a ≤ s + i.val ∧ s + i.val < a + b))) := by
      intro i
      have hb : bot.getD i.val false = (u.getD i.val false && w.getD i.val false) := by simp [bot, List.getD]
      rw [hb, hget_u, hget_w, hval i.val (by omega), hval (s + i.val) (by omega)]
      by_cases p1 : a ≤ i.val ∧ i.val < a + b <;> by_cases p2 : a ≤ s + i.val ∧ s + i.val < a + b <;> simp [p1, p2]
    by_cases hbs : b ≤ s
    ·
      have htop_all : top = List.replicate s true := by
        apply hmk_all top (by simp [top]) true
        intro i; rw [htop_get i]; simp; omega
      have htop_bit : IsBitonic top := Or.inl ⟨s, 0, 0, by simp [htop_all]⟩

      have hbot_bit : IsBitonic bot := by
        by_cases ha : a + b ≤ s
        · left
          refine ⟨a, b, s - (a + b), ?_⟩
          have h := hmk_101 bot (by simp [bot]) a (a + b) (by omega) ha (fun i => by
            rw [hbot_get i]; congr 1; exact propext (by omega))
          simpa using h
        · by_cases ha2 : s ≤ a
          · left
            refine ⟨a - s, b, s - (a + b - s), ?_⟩
            have h := hmk_101 bot (by simp [bot]) (a - s) (a + b - s) (by omega) (by omega) (fun i => by
              rw [hbot_get i]; congr 1; exact propext (by omega))
            simpa [show a + b - s - (a - s) = b by omega] using h
          ·
            right
            refine ⟨a + b - s, a - (a + b - s), s - a, ?_⟩
            exact hmk_010 bot (by simp [bot]) (a + b - s) a (by omega) (by omega) (fun i => by
              rw [hbot_get i]; congr 1; exact propext (by omega))
      exact ⟨htop_bit, hbot_bit, Or.inl htop_all, hcount⟩
    ·
      have hbot_all : bot = List.replicate s false := by
        apply hmk_all bot (by simp [bot]) false
        intro i; rw [hbot_get i]; simp; omega
      have hbot_bit : IsBitonic bot := Or.inr ⟨s, 0, 0, by simp [hbot_all]⟩

      have htop_bit : IsBitonic top := by
        left
        refine ⟨a, a + b - s - a, s - (a + b - s), ?_⟩
        exact hmk_101 top (by simp [top]) a (a + b - s) (by omega) (by omega) (fun i => by
          rw [htop_get i]; congr 1; exact propext (by omega))
      exact ⟨htop_bit, hbot_bit, Or.inr hbot_all, hcount⟩
  ·
    have hsum : a + b + c = 2 * s := by
      have := congrArg List.length hshape; simp [hu, hw] at this; omega
    have hval : ∀ k < 2 * s, (u ++ w).getD k false = decide (a ≤ k ∧ k < a + b) := by
      intro k hk
      rw [hshape, List.getD]
      by_cases c1 : k < a
      · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega)]
        simp [c1, show ¬(a ≤ k ∧ k < a + b) by omega]
      · by_cases c2 : k < a + b
        · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by simp; omega)]
          simp [show a ≤ k ∧ k < a + b by omega, show k - a < b by omega]
        · rw [List.getElem?_append_right (by simp; omega)]
          simp [show ¬(a ≤ k ∧ k < a + b) by omega, show k - (a + b) < c by omega]
    have htop_get : ∀ i : Fin s, top.getD i.val false =
        decide ((a ≤ i.val ∧ i.val < a + b) ∨ (a ≤ s + i.val ∧ s + i.val < a + b)) := by
      intro i
      have ht : top.getD i.val false = (u.getD i.val false || w.getD i.val false) := by simp [top, List.getD]
      rw [ht, hget_u, hget_w, hval i.val (by omega), hval (s + i.val) (by omega)]
      by_cases p1 : a ≤ i.val ∧ i.val < a + b <;> by_cases p2 : a ≤ s + i.val ∧ s + i.val < a + b <;> simp [p1, p2]
    have hbot_get : ∀ i : Fin s, bot.getD i.val false =
        decide ((a ≤ i.val ∧ i.val < a + b) ∧ (a ≤ s + i.val ∧ s + i.val < a + b)) := by
      intro i
      have hb : bot.getD i.val false = (u.getD i.val false && w.getD i.val false) := by simp [bot, List.getD]
      rw [hb, hget_u, hget_w, hval i.val (by omega), hval (s + i.val) (by omega)]
      by_cases p1 : a ≤ i.val ∧ i.val < a + b <;> by_cases p2 : a ≤ s + i.val ∧ s + i.val < a + b <;> simp [p1, p2]
    by_cases hbs : b ≤ s
    ·
      have hbot_all : bot = List.replicate s false := by
        apply hmk_all bot (by simp [bot]) false
        intro i; rw [hbot_get i]; simp; omega
      have hbot_bit : IsBitonic bot := Or.inr ⟨s, 0, 0, by simp [hbot_all]⟩
      have htop_bit : IsBitonic top := by
        by_cases ha : a + b ≤ s
        · right
          refine ⟨a, b, s - (a + b), ?_⟩
          have h := hmk_010 top (by simp [top]) a (a + b) (by omega) ha (fun i => by
            rw [htop_get i]; congr 1; exact propext (by omega))
          simpa using h
        · by_cases ha2 : s ≤ a
          · right
            refine ⟨a - s, b, s - (a + b - s), ?_⟩
            have h := hmk_010 top (by simp [top]) (a - s) (a + b - s) (by omega) (by omega) (fun i => by
              rw [htop_get i]; congr 1; exact propext (by omega))
            simpa [show a + b - s - (a - s) = b by omega] using h
          · left
            refine ⟨a + b - s, a - (a + b - s), s - a, ?_⟩
            exact hmk_101 top (by simp [top]) (a + b - s) a (by omega) (by omega) (fun i => by
              rw [htop_get i]; congr 1; exact propext (by omega))
      exact ⟨htop_bit, hbot_bit, Or.inr hbot_all, hcount⟩
    ·
      have htop_all : top = List.replicate s true := by
        apply hmk_all top (by simp [top]) true
        intro i; rw [htop_get i]; simp; omega
      have htop_bit : IsBitonic top := Or.inl ⟨s, 0, 0, by simp [htop_all]⟩
      have hbot_bit : IsBitonic bot := by
        right
        refine ⟨a, a + b - s - a, s - (a + b - s), ?_⟩
        exact hmk_010 bot (by simp [bot]) a (a + b - s) (by omega) (by omega) (fun i => by
          rw [hbot_get i]; congr 1; exact propext (by omega))
      exact ⟨htop_bit, hbot_bit, Or.inl htop_all, hcount⟩

def slice (v : List Bool) (off len : ℕ) : List Bool := (v.drop off).take len

lemma slice_length (v : List Bool) (off len : ℕ) (h : off + len ≤ v.length) :
    (slice v off len).length = len := by
  simp only [slice, List.length_take, List.length_drop]; omega

lemma slice_getD (v : List Bool) (off len i : ℕ) (hi : i < len) :
    (slice v off len).getD i false = v.getD (off + i) false := by
  simp only [slice, List.getD, List.getElem?_take_of_lt hi, List.getElem?_drop]

lemma slice_append_adjacent (v : List Bool) (off len1 len2 : ℕ) (h : off + len1 + len2 ≤ v.length) :
    slice v off len1 ++ slice v (off + len1) len2 = slice v off (len1 + len2) := by
  apply List.ext_getElem
  · simp [slice_length v off len1 (by omega), slice_length v (off + len1) len2 (by omega),
      slice_length v off (len1 + len2) (by omega)]
  · intro i h1 h2
    have hlt : i < len1 + len2 := by rw [slice_length v off (len1 + len2) (by omega)] at h2; exact h2
    by_cases hi1 : i < len1
    · have hl1 : i < (slice v off len1).length := by rw [slice_length v off len1 (by omega)]; exact hi1
      rw [List.getElem_append_left hl1]
      have g1 : (slice v off len1)[i] = (slice v off len1).getD i false := by
        simp [List.getD, List.getElem?_eq_getElem hl1]
      have g2 : (slice v off (len1 + len2))[i] = (slice v off (len1 + len2)).getD i false := by
        simp [List.getD, List.getElem?_eq_getElem h2]
      rw [g1, g2, slice_getD v off len1 i hi1, slice_getD v off (len1 + len2) i hlt]
    · have hl1 : (slice v off len1).length ≤ i := by rw [slice_length v off len1 (by omega)]; omega
      rw [List.getElem_append_right hl1]
      have hlen1 : (slice v off len1).length = len1 := slice_length v off len1 (by omega)
      have hlen2 : (slice v (off + len1) len2).length = len2 := slice_length v (off + len1) len2 (by omega)
      have g1 : (slice v (off + len1) len2)[i - (slice v off len1).length]'(by omega) =
          (slice v (off + len1) len2).getD (i - len1) false := by
        have hsub : i - (slice v off len1).length = i - len1 := by omega
        simp only [List.getD, List.getElem?_eq_getElem (by omega : i - len1 < (slice v (off + len1) len2).length),
          Option.getD_some, hsub]
      have g2 : (slice v off (len1 + len2))[i] = (slice v off (len1 + len2)).getD i false := by
        simp [List.getD, List.getElem?_eq_getElem h2]
      rw [g1, g2, slice_getD v (off + len1) len2 (i - len1) (by omega),
        slice_getD v off (len1 + len2) i hlt, show off + len1 + (i - len1) = off + i by omega]

lemma bitonicMerge_correct (p : ℕ) : ∀ (v : List Bool) (off : ℕ) (dir : Bool),
    off + 2 ^ p ≤ v.length →
    IsBitonic (slice v off (2 ^ p)) →
    let v' := applyComps v (bitonicMergeComps off dir p)
    (if dir then isSortedDesc (slice v' off (2 ^ p)) else isSortedAsc (slice v' off (2 ^ p))) ∧
    (slice v' off (2 ^ p)).count true = (slice v off (2 ^ p)).count true := by
  induction p with
  | zero =>
    intro v off dir hlen _
    simp only [bitonicMergeComps, applyComps, List.foldl_nil, Nat.pow_zero]
    have hsl : (slice v off 1).length = 1 := slice_length v off 1 hlen
    obtain ⟨b, hb⟩ : ∃ b, slice v off 1 = [b] := by
      cases hs : slice v off 1 with
      | nil => simp [hs] at hsl
      | cons b bs =>
        cases bs with
        | nil => exact ⟨b, rfl⟩
        | cons _ _ => simp [hs] at hsl
    refine ⟨?_, trivial⟩
    cases dir <;> cases b <;> (unfold isSortedDesc isSortedAsc; rw [hb]; decide)
  | succ p ih =>
    intro v off dir hlen hbit
    set s := 2 ^ p with hs_def
    have hs_pos : 1 ≤ s := Nat.one_le_two_pow
    have hp2 : 2 ^ (p + 1) = s + s := by rw [Nat.pow_succ, ← hs_def]; ring
    have hlen2 : off + (s + s) ≤ v.length := by rwa [← hp2]
    let v1 := applyComps v (halfCleanComps off s dir)
    let v2 := applyComps v1 (bitonicMergeComps off dir p)
    let v3 := applyComps v2 (bitonicMergeComps (off + s) dir p)
    have hv3_eq : applyComps v (bitonicMergeComps off dir (p + 1)) = v3 := by
      simp [v1, v2, v3, s, bitonicMergeComps, applyComps_append]
    rw [hv3_eq]
    have hv1_len : v1.length = v.length := applyComps_length _ _
    have hv2_len : v2.length = v.length := by rw [applyComps_length, hv1_len]
    have hv3_len : v3.length = v.length := by rw [applyComps_length, hv2_len]

    let u := slice v off s
    let w := slice v (off + s) s
    have huw : u ++ w = slice v off (2 ^ (p + 1)) := by
      rw [hp2]; exact slice_append_adjacent v off s s (by omega)
    have ⟨htop_bit, hbot_bit, hclean, hcnt⟩ :=
      halfClean_bitonic_lists s u w (slice_length v off s (by omega))
        (slice_length v (off + s) s (by omega)) (by rwa [huw])
    let top := List.ofFn (fun i : Fin s => u.getD i.val false || w.getD i.val false)
    let bot := List.ofFn (fun i : Fin s => u.getD i.val false && w.getD i.val false)
    have hslice_v1_L : slice v1 off s = if dir then top else bot := by
      apply List.ext_getElem
      · cases dir <;> simp [slice_length v1 off s (by omega), top, bot]
      · intro i h1 h2
        have hi : i < s := by rw [slice_length v1 off s (by omega)] at h1; exact h1
        have hL : (slice v1 off s)[i] = v1.getD (off + i) false := by
          have := slice_getD v1 off s i hi
          simpa [List.getD, List.getElem?_eq_getElem h1] using this
        rw [hL, show v1.getD (off + i) false = _ from applyComps_halfClean_get v off s dir (by omega) (off + i)]
        have hc1 : off ≤ off + i ∧ off + i < off + s := by omega
        simp only [hc1, and_self, ↓reduceIte]
        have hu_i : u.getD i false = v.getD (off + i) false := slice_getD v off s i hi
        have hw_i : w.getD i false = v.getD (off + i + s) false := by
          rw [slice_getD v (off + s) s i hi, show off + s + i = off + i + s by omega]
        rw [← hu_i, ← hw_i]; cases dir <;> simp [top, bot, hi]
    have hslice_v1_R : slice v1 (off + s) s = if dir then bot else top := by
      apply List.ext_getElem
      · cases dir <;> simp [slice_length v1 (off + s) s (by omega), top, bot]
      · intro i h1 h2
        have hi : i < s := by rw [slice_length v1 (off + s) s (by omega)] at h1; exact h1
        have hL : (slice v1 (off + s) s)[i] = v1.getD (off + s + i) false := by
          have := slice_getD v1 (off + s) s i hi
          simpa [List.getD, List.getElem?_eq_getElem h1] using this
        rw [hL, show v1.getD (off + s + i) false = _ from applyComps_halfClean_get v off s dir (by omega) (off + s + i)]
        have hc1 : ¬(off ≤ off + s + i ∧ off + s + i < off + s) := by omega
        have hc2 : off + s ≤ off + s + i ∧ off + s + i < off + 2 * s := by omega
        simp only [hc1, ↓reduceIte, hc2, and_self]
        have hu_i : u.getD i false = v.getD (off + s + i - s) false := by
          rw [slice_getD v off s i hi, show off + s + i - s = off + i by omega]
        have hw_i : w.getD i false = v.getD (off + s + i) false := slice_getD v (off + s) s i hi
        rw [← hu_i, ← hw_i]; cases dir <;> simp [top, bot, hi]

    have hbit_L : IsBitonic (slice v1 off s) := by rw [hslice_v1_L]; cases dir <;> simpa using ‹_›
    have ⟨hsort_L, hcnt_L⟩ := ih v1 off dir (by omega) hbit_L

    have hR_unch : slice v2 (off + s) s = slice v1 (off + s) s := by
      apply List.ext_getElem (by rw [slice_length v2 (off + s) s (by omega), slice_length v1 (off + s) s (by omega)])
      intro i h1 h2
      have hi : i < s := by rw [slice_length v2 (off + s) s (by omega)] at h1; exact h1
      have g1 : (slice v2 (off + s) s)[i] = v2.getD (off + s + i) false := by
        simpa [List.getD, List.getElem?_eq_getElem h1] using slice_getD v2 (off + s) s i hi
      have g2 : (slice v1 (off + s) s)[i] = v1.getD (off + s + i) false := by
        simpa [List.getD, List.getElem?_eq_getElem h2] using slice_getD v1 (off + s) s i hi
      rw [g1, g2]
      apply applyComps_outside
      intro q hq
      have := bitonicMergeComps_valid off v1.length dir p (by omega) q hq
      omega

    have hbit_R : IsBitonic (slice v2 (off + s) s) := by
      rw [hR_unch, hslice_v1_R]; cases dir <;> simpa using ‹_›
    have ⟨hsort_R, hcnt_R⟩ := ih v2 (off + s) dir (by omega) hbit_R

    have hL_unch : slice v3 off s = slice v2 off s := by
      apply List.ext_getElem (by rw [slice_length v3 off s (by omega), slice_length v2 off s (by omega)])
      intro i h1 h2
      have hi : i < s := by rw [slice_length v3 off s (by omega)] at h1; exact h1
      have g1 : (slice v3 off s)[i] = v3.getD (off + i) false := by
        simpa [List.getD, List.getElem?_eq_getElem h1] using slice_getD v3 off s i hi
      have g2 : (slice v2 off s)[i] = v2.getD (off + i) false := by
        simpa [List.getD, List.getElem?_eq_getElem h2] using slice_getD v2 off s i hi
      rw [g1, g2]
      apply applyComps_outside
      intro q hq
      have := bitonicMergeComps_valid (off + s) v2.length dir p (by omega) q hq
      omega
    have hsplit3 : slice v3 off (2 ^ (p + 1)) = slice v3 off s ++ slice v3 (off + s) s := by
      rw [hp2]; exact (slice_append_adjacent v3 off s s (by omega)).symm
    have hcnt_tot : (slice v3 off (2 ^ (p + 1))).count true = (slice v off (2 ^ (p + 1))).count true := by
      rw [hsplit3, List.count_append, hL_unch, hcnt_L, hcnt_R, hR_unch, hslice_v1_L, hslice_v1_R, ← huw]
      dsimp only [top, bot]
      cases dir <;> simp only [↓reduceIte, Bool.false_eq_true] <;> omega
    refine ⟨?_, hcnt_tot⟩
    rw [hsplit3, hL_unch]
    have hLlen : (slice v2 off s).length = s := slice_length v2 off s (by omega)
    have hRlen : (slice v3 (off + s) s).length = s := slice_length v3 (off + s) s (by omega)
    cases dir
    ·
      simp only [Bool.false_eq_true, ↓reduceIte] at hsort_L hsort_R hslice_v1_L hslice_v1_R ⊢
      rw [isSortedAsc_iff] at hsort_L hsort_R ⊢
      obtain ⟨a1, b1, hL_eq⟩ := hsort_L
      obtain ⟨a2, b2, hR_eq⟩ := hsort_R
      rcases hclean with htop_t | hbot_f
      ·
        have hcR : (slice v3 (off + s) s).count true = s := by
          rw [show (slice v3 (off + s) s).count true = (slice v2 (off + s) s).count true from hcnt_R, hR_unch, hslice_v1_R]
          dsimp only [top]; rw [htop_t]; simp [count_true_replicate]
        have hlenR : a2 + b2 = s := by have := congrArg List.length hR_eq; rw [hRlen] at this; simp at this; exact this.symm
        have hb2 : b2 = s := by rw [hR_eq, List.count_append, count_true_replicate, count_true_replicate] at hcR; simp at hcR; exact hcR
        have ha2 : a2 = 0 := by omega
        refine ⟨a1, b1 + b2, ?_⟩
        rw [hL_eq, hR_eq, ha2, replicate_add_append]
        simp only [List.replicate_zero, List.nil_append, List.append_nil, List.append_assoc]
      ·
        have hcL : (slice v2 off s).count true = 0 := by
          rw [show (slice v2 off s).count true = (slice v1 off s).count true from hcnt_L, hslice_v1_L]
          dsimp only [bot]; rw [hbot_f]; simp [count_true_replicate]
        have hlenL : a1 + b1 = s := by have := congrArg List.length hL_eq; rw [hLlen] at this; simp at this; exact this.symm
        have hb1 : b1 = 0 := by rw [hL_eq, List.count_append, count_true_replicate, count_true_replicate] at hcL; simp at hcL; exact hcL
        refine ⟨a1 + a2, b2, ?_⟩
        rw [hL_eq, hR_eq, hb1, replicate_add_append]
        simp only [List.replicate_zero, List.nil_append, List.append_nil, List.append_assoc]
    ·
      simp only [↓reduceIte] at hsort_L hsort_R hslice_v1_L hslice_v1_R ⊢
      rw [isSortedDesc_iff] at hsort_L hsort_R ⊢
      obtain ⟨a1, b1, hL_eq⟩ := hsort_L
      obtain ⟨a2, b2, hR_eq⟩ := hsort_R
      rcases hclean with htop_t | hbot_f
      ·
        have hcL : (slice v2 off s).count true = s := by
          rw [show (slice v2 off s).count true = (slice v1 off s).count true from hcnt_L, hslice_v1_L]
          dsimp only [top]; rw [htop_t]; simp [count_true_replicate]
        have hlenL : a1 + b1 = s := by have := congrArg List.length hL_eq; rw [hLlen] at this; simp at this; exact this.symm
        have ha1 : a1 = s := by rw [hL_eq, List.count_append, count_true_replicate, count_true_replicate] at hcL; simp at hcL; exact hcL
        have hb1 : b1 = 0 := by omega
        refine ⟨a1 + a2, b2, ?_⟩
        rw [hL_eq, hR_eq, hb1, replicate_add_append]
        simp only [List.replicate_zero, List.nil_append, List.append_nil, List.append_assoc]
      ·
        have hcR : (slice v3 (off + s) s).count true = 0 := by
          rw [show (slice v3 (off + s) s).count true = (slice v2 (off + s) s).count true from hcnt_R, hR_unch, hslice_v1_R]
          dsimp only [bot]; rw [hbot_f]; simp [count_true_replicate]
        have hlenR : a2 + b2 = s := by have := congrArg List.length hR_eq; rw [hRlen] at this; simp at this; exact this.symm
        have ha2 : a2 = 0 := by rw [hR_eq, List.count_append, count_true_replicate, count_true_replicate] at hcR; simp at hcR; exact hcR
        refine ⟨a1, b1 + b2, ?_⟩
        rw [hL_eq, hR_eq, ha2, replicate_add_append]
        simp only [List.replicate_zero, List.nil_append, List.append_nil, List.append_assoc]

lemma bitonicSort_correct (p : ℕ) : ∀ (v : List Bool) (off : ℕ) (dir : Bool),
    off + 2 ^ p ≤ v.length →
    let v' := applyComps v (bitonicSortComps off dir p)
    (if dir then isSortedDesc (slice v' off (2 ^ p)) else isSortedAsc (slice v' off (2 ^ p))) ∧
    (slice v' off (2 ^ p)).count true = (slice v off (2 ^ p)).count true := by
  induction p with
  | zero =>
    intro v off dir hlen
    simp only [bitonicSortComps, applyComps, List.foldl_nil, Nat.pow_zero]
    have hsl : (slice v off 1).length = 1 := slice_length v off 1 hlen
    obtain ⟨b, hb⟩ : ∃ b, slice v off 1 = [b] := by
      cases hs : slice v off 1 with
      | nil => simp [hs] at hsl
      | cons b bs =>
        cases bs with
        | nil => exact ⟨b, rfl⟩
        | cons _ _ => simp [hs] at hsl
    refine ⟨?_, trivial⟩
    cases dir <;> cases b <;> (unfold isSortedDesc isSortedAsc; rw [hb]; decide)
  | succ p ih =>
    intro v off dir hlen
    set s := 2 ^ p with hs_def
    have hs_pos : 1 ≤ s := Nat.one_le_two_pow
    have hp2 : 2 ^ (p + 1) = s + s := by rw [Nat.pow_succ, ← hs_def]; ring
    have hlen2 : off + (s + s) ≤ v.length := by rwa [← hp2]
    let v1 := applyComps v (bitonicSortComps off true p)
    let v2 := applyComps v1 (bitonicSortComps (off + s) false p)
    let v3 := applyComps v2 (bitonicMergeComps off dir (p + 1))
    have hv3_eq : applyComps v (bitonicSortComps off dir (p + 1)) = v3 := by
      simp [v1, v2, v3, s, bitonicSortComps, applyComps_append]
    rw [hv3_eq]
    have hv1_len : v1.length = v.length := applyComps_length _ _
    have hv2_len : v2.length = v.length := by rw [applyComps_length, hv1_len]
    have ⟨hsort_L, hcnt_L⟩ := ih v off true (by omega)
    simp only [↓reduceIte] at hsort_L
    have hR_unch : slice v1 (off + s) s = slice v (off + s) s := by
      apply List.ext_getElem (by rw [slice_length v1 (off + s) s (by omega), slice_length v (off + s) s (by omega)])
      intro i h1 h2
      have hi : i < s := by rw [slice_length v1 (off + s) s (by omega)] at h1; exact h1
      have g1 : (slice v1 (off + s) s)[i] = v1.getD (off + s + i) false := by
        simpa [List.getD, List.getElem?_eq_getElem h1] using slice_getD v1 (off + s) s i hi
      have g2 : (slice v (off + s) s)[i] = v.getD (off + s + i) false := by
        simpa [List.getD, List.getElem?_eq_getElem h2] using slice_getD v (off + s) s i hi
      rw [g1, g2]
      apply applyComps_outside
      intro q hq
      have := bitonicSortComps_valid off v.length true p (by omega) q hq
      omega
    have ⟨hsort_R, hcnt_R⟩ := ih v1 (off + s) false (by omega)
    simp only [Bool.false_eq_true, ↓reduceIte] at hsort_R
    have hL_unch : slice v2 off s = slice v1 off s := by
      apply List.ext_getElem (by rw [slice_length v2 off s (by omega), slice_length v1 off s (by omega)])
      intro i h1 h2
      have hi : i < s := by rw [slice_length v2 off s (by omega)] at h1; exact h1
      have g1 : (slice v2 off s)[i] = v2.getD (off + i) false := by
        simpa [List.getD, List.getElem?_eq_getElem h1] using slice_getD v2 off s i hi
      have g2 : (slice v1 off s)[i] = v1.getD (off + i) false := by
        simpa [List.getD, List.getElem?_eq_getElem h2] using slice_getD v1 off s i hi
      rw [g1, g2]
      apply applyComps_outside
      intro q hq
      have := bitonicSortComps_valid (off + s) v1.length false p (by omega) q hq
      omega
    have hsplit2 : slice v2 off (2 ^ (p + 1)) = slice v2 off s ++ slice v2 (off + s) s := by
      rw [hp2]; exact (slice_append_adjacent v2 off s s (by omega)).symm
    have hbit2 : IsBitonic (slice v2 off (2 ^ (p + 1))) := by
      rw [hsplit2, hL_unch]; exact bitonic_of_desc_asc hsort_L hsort_R
    have ⟨hsort3, hcnt3⟩ := bitonicMerge_correct (p + 1) v2 off dir (by omega) hbit2
    refine ⟨hsort3, ?_⟩
    rw [hcnt3, hsplit2, List.count_append, hL_unch, hcnt_L, hcnt_R, hR_unch]
    have hsplit0 : slice v off (2 ^ (p + 1)) = slice v off s ++ slice v (off + s) s := by
      rw [hp2]; exact (slice_append_adjacent v off s s (by omega)).symm
    rw [hsplit0, List.count_append]

def compileCompsFwd (n0 : ℕ) (gs : List Gate) (ws : List ℕ) :
    List (ℕ × ℕ) → List Gate × List ℕ × List (ℕ × ℕ × ℕ × ℕ)
  | [] => (gs, ws, [])
  | (i, j) :: cs =>
    let wa := ws.getD i 0
    let wb := ws.getD j 0
    let wMax := n0 + gs.length
    let wMin := n0 + gs.length + 1
    let gs1 := gs ++ [⟨GateOp.or, [wa, wb]⟩, ⟨GateOp.and, [wa, wb]⟩]
    let ws1 := (ws.set i wMax).set j wMin
    let res := compileCompsFwd n0 gs1 ws1 cs
    (res.1, res.2.1, (i, j, wa, wb) :: res.2.2)

lemma compileCompsFwd_spec (n0 : ℕ) (cs : List (ℕ × ℕ)) :
    ∀ (gs : List Gate) (ws : List ℕ),
    (∀ w ∈ ws, w < n0 + gs.length) →
    (∀ q ∈ cs, q.1 < ws.length ∧ q.2 < ws.length ∧ q.1 ≠ q.2) →
    let res := compileCompsFwd n0 gs ws cs
    (∃ extra, res.1 = gs ++ extra ∧ extra.length = 2 * cs.length ∧
      Monotone2 ⟨extra, 0⟩ ∧ ReadsBack (n0 + gs.length) ⟨extra, 0⟩) ∧
    res.2.1.length = ws.length ∧
    (∀ w ∈ res.2.1, w < n0 + res.1.length) ∧
    res.2.2.length = cs.length ∧
    (∀ y : List Bool, y.length = n0 →
      res.2.1.map (fun w => ((Circuit.mk res.1 0).wires y).getD w false) =
        applyComps (ws.map (fun w => ((Circuit.mk gs 0).wires y).getD w false)) cs) := by
  induction cs with
  | nil =>
    intro gs ws hws _
    refine ⟨⟨[], by simp [compileCompsFwd], rfl, fun _ h => by simp at h, fun j hj => by simp at hj⟩,
      rfl, hws, rfl, fun y _ => rfl⟩
  | cons p cs ih =>
    rcases p with ⟨i, j⟩
    intro gs ws hws hcs
    have hp := hcs (i, j) (List.mem_cons_self ..)
    have hcs' : ∀ q ∈ cs, q.1 < ws.length ∧ q.2 < ws.length ∧ q.1 ≠ q.2 :=
      fun q hq => hcs q (List.mem_cons_of_mem _ hq)
    let wa := ws.getD i 0
    let wb := ws.getD j 0
    have hwa : wa < n0 + gs.length := by
      have : wa = ws[i]'(hp.1) := by simp [wa, List.getD, List.getElem?_eq_getElem hp.1]
      rw [this]; exact hws _ (List.getElem_mem hp.1)
    have hwb : wb < n0 + gs.length := by
      have : wb = ws[j]'(hp.2.1) := by simp [wb, List.getD, List.getElem?_eq_getElem hp.2.1]
      rw [this]; exact hws _ (List.getElem_mem hp.2.1)
    let step : List Gate := [⟨GateOp.or, [wa, wb]⟩, ⟨GateOp.and, [wa, wb]⟩]
    let gs1 := gs ++ step
    let wMax := n0 + gs.length
    let wMin := n0 + gs.length + 1
    let ws1 := (ws.set i wMax).set j wMin
    have hws1_len : ws1.length = ws.length := by simp [ws1]
    have hws1_lt : ∀ w ∈ ws1, w < n0 + gs1.length := by
      intro w hw
      have hlen1 : gs1.length = gs.length + 2 := by simp [gs1, step]
      rcases mem_of_mem_set hw with h | rfl
      · rcases mem_of_mem_set h with h0 | rfl
        · have := hws w h0; omega
        · omega
      · omega
    have hih := ih gs1 ws1 hws1_lt (by simpa [hws1_len] using hcs')
    obtain ⟨⟨extra2, hgs2, hlen2, hmon2, hrb2⟩, hws2_len, hws2_lt, hlog2_len, hsem2⟩ := hih
    have hstep_mon : Monotone2 ⟨step, 0⟩ := by
      intro g hg; simp only [step, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl <;> simp
    have hstep_rb : ReadsBack (n0 + gs.length) ⟨step, 0⟩ := by
      intro idx hidx u hu
      have : idx = 0 ∨ idx = 1 := by simp [step] at hidx; omega
      rcases this with rfl | rfl <;>
        (simp only [step, gateAt, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.getD_some, List.mem_cons, List.not_mem_nil, or_false] at hu;
         rcases hu with rfl | rfl <;> omega)
    refine ⟨⟨step ++ extra2, ?_, ?_, ?_, ?_⟩, ?_, hws2_lt, ?_, ?_⟩
    · change (compileCompsFwd n0 gs1 ws1 cs).1 = gs ++ (step ++ extra2)
      rw [hgs2, ← List.append_assoc]
    · simp [step, hlen2]; omega
    · exact monotone2_append step extra2 0 hstep_mon hmon2
    · exact readsBack_append (n0 + gs.length) step extra2 0 hstep_rb (by simpa [gs1, Nat.add_assoc] using hrb2)
    · change (compileCompsFwd n0 gs1 ws1 cs).2.1.length = ws.length
      rw [hws2_len, hws1_len]
    · change ((i, j, wa, wb) :: (compileCompsFwd n0 gs1 ws1 cs).2.2).length = ((i, j) :: cs).length
      simp [hlog2_len]
    · intro y hy
      change (compileCompsFwd n0 gs1 ws1 cs).2.1.map (fun w => ((Circuit.mk (compileCompsFwd n0 gs1 ws1 cs).1 0).wires y).getD w false) =
        applyComps (applyComp (ws.map (fun w => ((Circuit.mk gs 0).wires y).getD w false)) (i, j)) cs
      rw [hsem2 y hy]
      congr 1
      have hpre : ∀ w < n0 + gs.length,
          ((Circuit.mk gs1 0).wires y).getD w false = ((Circuit.mk gs 0).wires y).getD w false := by
        intro w hw; exact wires_prefix gs step y 0 w (by omega)
      have h1 : gs1 = (gs ++ [⟨GateOp.or, [wa, wb]⟩]) ++ [⟨GateOp.and, [wa, wb]⟩] := by
        simp [gs1, step]
      have hmax_val : ((Circuit.mk gs1 0).wires y).getD wMax false =
          (((Circuit.mk gs 0).wires y).getD wa false || ((Circuit.mk gs 0).wires y).getD wb false) := by
        have hp1 := wires_prefix (gs ++ [Gate.mk GateOp.or [wa, wb]]) [Gate.mk GateOp.and [wa, wb]] y 0 wMax
          (by simp [wMax, hy])
        rw [h1, hp1]
        rw [show wMax = n0 + gs.length from rfl, wires_snoc_last n0 gs (Gate.mk GateOp.or [wa, wb]) y hy]
        simp [GateOp.eval]
      have hmin_val : ((Circuit.mk gs1 0).wires y).getD wMin false =
          (((Circuit.mk gs 0).wires y).getD wa false && ((Circuit.mk gs 0).wires y).getD wb false) := by
        rw [h1]
        have hm_eq : wMin = n0 + (gs ++ [Gate.mk GateOp.or [wa, wb]]).length := by simp [wMin]; omega
        rw [hm_eq, wires_snoc_last n0 (gs ++ [Gate.mk GateOp.or [wa, wb]]) (Gate.mk GateOp.and [wa, wb]) y hy]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
        rw [wires_prefix gs [Gate.mk GateOp.or [wa, wb]] y 0 wa (by omega),
          wires_prefix gs [Gate.mk GateOp.or [wa, wb]] y 0 wb (by omega)]
      apply List.ext_getElem (by simp [ws1, applyComp])
      intro k hk1 hk2
      have hk : k < ws.length := by simpa [ws1] using hk1
      have hR_a : (ws.map (fun w => ((Circuit.mk gs 0).wires y).getD w false)).getD i false =
          ((Circuit.mk gs 0).wires y).getD wa false := by
        simp [wa, List.getD, List.getElem?_eq_getElem hp.1]
      have hR_b : (ws.map (fun w => ((Circuit.mk gs 0).wires y).getD w false)).getD j false =
          ((Circuit.mk gs 0).wires y).getD wb false := by
        simp [wb, List.getD, List.getElem?_eq_getElem hp.2.1]
      by_cases hkj : k = j
      · subst hkj
        rw [List.getElem_map]
        have hL : ws1[k]'(by simpa [ws1] using hk) = wMin := by
          simp only [ws1, List.getElem_set_self]
        rw [hL, hmin_val]
        simp only [applyComp, List.getElem_set_self, hR_a, hR_b]
      · by_cases hki : k = i
        · subst hki
          rw [List.getElem_map]
          have hL : ws1[k]'(by simpa [ws1] using hk) = wMax := by
            simp only [ws1, List.getElem_set_ne (Ne.symm hkj), List.getElem_set_self]
          rw [hL, hmax_val]
          simp only [applyComp, List.getElem_set_ne (Ne.symm hkj), List.getElem_set_self, hR_a, hR_b]
        · rw [List.getElem_map]
          have hL : ws1[k]'(by simpa [ws1] using hk) = ws[k] := by
            simp only [ws1, List.getElem_set_ne (Ne.symm hkj), List.getElem_set_ne (Ne.symm hki)]
          have hw_k : ws[k] < n0 + gs.length := hws ws[k] (List.getElem_mem hk)
          rw [hL, hpre ws[k] hw_k]
          simp only [applyComp, List.getElem_set_ne (Ne.symm hkj), List.getElem_set_ne (Ne.symm hki), List.getElem_map]

def compileCompsBwd (n0 : ℕ) (gs : List Gate) (negWs : List ℕ) :
    List (ℕ × ℕ × ℕ × ℕ) → List Gate × List ℕ
  | [] => (gs, negWs)
  | (i, j, wa, wb) :: rest =>
    let nMax := negWs.getD i 0
    let nMin := negWs.getD j 0
    let t1 := n0 + gs.length
    let na := n0 + gs.length + 1
    let t2 := n0 + gs.length + 2
    let nb := n0 + gs.length + 3
    let step : List Gate :=
      [⟨GateOp.and, [wb, nMin]⟩, ⟨GateOp.or, [nMax, t1]⟩,
       ⟨GateOp.and, [wa, nMin]⟩, ⟨GateOp.or, [nMax, t2]⟩]
    let negWs1 := (negWs.set i na).set j nb
    compileCompsBwd n0 (gs ++ step) negWs1 rest

lemma bwd_comp_bool (a b : Bool) :
    ((!(a || b) || (b && !(a && b))) = !a) ∧
    ((!(a || b) || (a && !(a && b))) = !b) := by
  cases a <;> cases b <;> decide

lemma compileCompsBwd_spec (n0 : ℕ) (cs : List (ℕ × ℕ)) :
    ∀ (gs0 : List Gate) (ws0 : List ℕ) (gs1 : List Gate) (negWs : List ℕ),
    (∀ w ∈ ws0, w < n0 + gs0.length) →
    (∀ q ∈ cs, q.1 < ws0.length ∧ q.2 < ws0.length ∧ q.1 ≠ q.2) →
    let fwd := compileCompsFwd n0 gs0 ws0 cs
    (∃ mid, gs1 = fwd.1 ++ mid) →
    negWs.length = ws0.length →
    (∀ w ∈ negWs, w < n0 + gs1.length) →
    let bwd := compileCompsBwd n0 gs1 negWs fwd.2.2.reverse
    (∃ extra, bwd.1 = gs1 ++ extra ∧ extra.length = 4 * cs.length ∧
      Monotone2 ⟨extra, 0⟩ ∧ ReadsBack (n0 + gs1.length) ⟨extra, 0⟩) ∧
    bwd.2.length = ws0.length ∧
    (∀ w ∈ bwd.2, w < n0 + bwd.1.length) ∧
    (∀ y : List Bool, y.length = n0 →
      (∀ k < ws0.length,
        ((Circuit.mk gs1 0).wires y).getD (negWs.getD k 0) false =
          !(((Circuit.mk fwd.1 0).wires y).getD (fwd.2.1.getD k 0) false)) →
      ∀ k < ws0.length,
        ((Circuit.mk bwd.1 0).wires y).getD (bwd.2.getD k 0) false =
          !(((Circuit.mk gs0 0).wires y).getD (ws0.getD k 0) false)) := by
  induction cs with
  | nil =>
    intro gs0 ws0 gs1 negWs _ _ fwd ⟨mid, hgs1⟩ hneg_len hneg_lt
    dsimp only [fwd] at hgs1 ⊢
    refine ⟨⟨[], by simp [compileCompsFwd, compileCompsBwd], rfl,
      fun _ h => by simp at h, fun j hj => by simp at hj⟩,
      by simpa [compileCompsFwd, compileCompsBwd] using hneg_len,
      by simpa [compileCompsFwd, compileCompsBwd] using hneg_lt, ?_⟩
    intro y _ hneg k hk
    simpa [compileCompsFwd, compileCompsBwd] using hneg k hk
  | cons p cs ih =>
    rcases p with ⟨i, j⟩
    intro gs0 ws0 gs1 negWs hws0 hcs fwd ⟨mid, hgs1⟩ hneg_len hneg_lt
    have hp := hcs (i, j) (List.mem_cons_self ..)
    have hcs' : ∀ q ∈ cs, q.1 < ws0.length ∧ q.2 < ws0.length ∧ q.1 ≠ q.2 :=
      fun q hq => hcs q (List.mem_cons_of_mem _ hq)
    let wa := ws0.getD i 0
    let wb := ws0.getD j 0
    have hwa : wa < n0 + gs0.length := by
      have : wa = ws0[i]'(hp.1) := by simp [wa, List.getD, List.getElem?_eq_getElem hp.1]
      rw [this]; exact hws0 _ (List.getElem_mem hp.1)
    have hwb : wb < n0 + gs0.length := by
      have : wb = ws0[j]'(hp.2.1) := by simp [wb, List.getD, List.getElem?_eq_getElem hp.2.1]
      rw [this]; exact hws0 _ (List.getElem_mem hp.2.1)
    let stepFwd : List Gate := [⟨GateOp.or, [wa, wb]⟩, ⟨GateOp.and, [wa, wb]⟩]
    let gs01 := gs0 ++ stepFwd
    let wMax := n0 + gs0.length
    let wMin := n0 + gs0.length + 1
    let ws01 := (ws0.set i wMax).set j wMin
    have hws01_len : ws01.length = ws0.length := by simp [ws01]
    have hws01_lt : ∀ w ∈ ws01, w < n0 + gs01.length := by
      intro w hw
      have hlen1 : gs01.length = gs0.length + 2 := by simp [gs01, stepFwd]
      rcases mem_of_mem_set hw with h | rfl
      · rcases mem_of_mem_set h with h0 | rfl
        · have := hws0 w h0; omega
        · omega
      · omega
    let fwdTail := compileCompsFwd n0 gs01 ws01 cs
    have hfwd_eq : compileCompsFwd n0 gs0 ws0 ((i, j) :: cs) =
        (fwdTail.1, fwdTail.2.1, (i, j, wa, wb) :: fwdTail.2.2) := rfl
    have hih := ih gs01 ws01 gs1 negWs hws01_lt (by simpa [hws01_len] using hcs')
      ⟨mid, hgs1⟩ (by omega) hneg_lt
    obtain ⟨⟨extraTail, hgsTail, hlenTail, hmonTail, hrbTail⟩, hnegTail_len, hnegTail_lt, hsemTail⟩ := hih

    set bwdTail := compileCompsBwd n0 gs1 negWs fwdTail.2.2.reverse
    change bwdTail.1 = gs1 ++ extraTail at hgsTail
    change bwdTail.2.length = ws01.length at hnegTail_len
    change ∀ w ∈ bwdTail.2, w < n0 + bwdTail.1.length at hnegTail_lt
    have hbwd_eq : compileCompsBwd n0 gs1 negWs ((i, j, wa, wb) :: fwdTail.2.2).reverse =
        compileCompsBwd n0 bwdTail.1 bwdTail.2 [(i, j, wa, wb)] := by
      simp only [List.reverse_cons]
      have hfold : ∀ (l1 l2 : List (ℕ × ℕ × ℕ × ℕ)) (g : List Gate) (nw : List ℕ),
          compileCompsBwd n0 g nw (l1 ++ l2) =
            compileCompsBwd n0 (compileCompsBwd n0 g nw l1).1 (compileCompsBwd n0 g nw l1).2 l2 := by
        intro l1
        induction l1 with
        | nil => intro l2 g nw; rfl
        | cons e l1 ihl => intro l2 g nw; exact ihl l2 _ _
      exact hfold fwdTail.2.2.reverse [(i, j, wa, wb)] gs1 negWs
    let nMax := bwdTail.2.getD i 0
    let nMin := bwdTail.2.getD j 0
    have hnMax_lt : nMax < n0 + bwdTail.1.length := by
      have hi' : i < bwdTail.2.length := by omega
      have : nMax = bwdTail.2[i]'hi' := by simp [nMax, List.getD, List.getElem?_eq_getElem hi']
      rw [this]; exact hnegTail_lt _ (List.getElem_mem hi')
    have hnMin_lt : nMin < n0 + bwdTail.1.length := by
      have hj' : j < bwdTail.2.length := by omega
      have : nMin = bwdTail.2[j]'hj' := by simp [nMin, List.getD, List.getElem?_eq_getElem hj']
      rw [this]; exact hnegTail_lt _ (List.getElem_mem hj')
    have hgs0_le_tail : gs0.length + 2 ≤ bwdTail.1.length := by
      have ⟨exF, hexF, _, _, _⟩ := (compileCompsFwd_spec n0 cs gs01 ws01 hws01_lt (by simpa [hws01_len] using hcs')).1
      dsimp only [fwd] at hgs1
      rw [hgsTail, hgs1, show (compileCompsFwd n0 gs0 ws0 ((i, j) :: cs)).1 = fwdTail.1 from rfl, hexF]
      simp [gs01, stepFwd]
    have hwa_lt : wa < n0 + bwdTail.1.length := by omega
    have hwb_lt : wb < n0 + bwdTail.1.length := by omega
    let t1 := n0 + bwdTail.1.length
    let na := n0 + bwdTail.1.length + 1
    let t2 := n0 + bwdTail.1.length + 2
    let nb := n0 + bwdTail.1.length + 3
    let stepBwd : List Gate :=
      [⟨GateOp.and, [wb, nMin]⟩, ⟨GateOp.or, [nMax, t1]⟩,
       ⟨GateOp.and, [wa, nMin]⟩, ⟨GateOp.or, [nMax, t2]⟩]
    have hstep_mon : Monotone2 ⟨stepBwd, 0⟩ := by
      intro g hg
      simp only [stepBwd, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl <;> simp
    have hstep_rb : ReadsBack (n0 + bwdTail.1.length) ⟨stepBwd, 0⟩ := by
      intro idx hidx u hu
      have : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 := by simp [stepBwd] at hidx; omega
      rcases this with rfl | rfl | rfl | rfl <;>
        (simp only [stepBwd, gateAt, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.getD_some, List.mem_cons, List.not_mem_nil, or_false] at hu;
         rcases hu with rfl | rfl <;> omega)
    dsimp only [fwd]
    rw [hfwd_eq, hbwd_eq]
    simp only [compileCompsBwd]
    refine ⟨⟨extraTail ++ stepBwd, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · dsimp only [stepBwd, nMax, nMin, t1, t2]; rw [hgsTail, List.append_assoc]
    · simp [stepBwd, hlenTail]; omega
    · exact monotone2_append extraTail stepBwd 0 hmonTail hstep_mon
    · exact readsBack_append (n0 + gs1.length) extraTail stepBwd 0 hrbTail (by simpa [hgsTail, Nat.add_assoc] using hstep_rb)
    · simp [hnegTail_len, hws01_len]
    · intro w hw
      simp only [List.length_append, List.length_cons, List.length_nil]
      rcases mem_of_mem_set hw with h | rfl
      · rcases mem_of_mem_set h with h0 | rfl
        · have := hnegTail_lt w h0; omega
        · omega
      · omega
    · intro y hy hneg k hk
      have hsemT := hsemTail y hy (by simpa [hws01_len] using hneg)
      have hgs_pref : ∃ restAll, bwdTail.1 = gs0 ++ stepFwd ++ restAll := by
        have ⟨exF, hexF, _, _, _⟩ := (compileCompsFwd_spec n0 cs gs01 ws01 hws01_lt (by simpa [hws01_len] using hcs')).1
        dsimp only [fwd] at hgs1
        exact ⟨exF ++ mid ++ extraTail, by rw [hgsTail, hgs1, show (compileCompsFwd n0 gs0 ws0 ((i, j) :: cs)).1 = gs01 ++ exF from hexF]; simp [gs01, List.append_assoc]⟩
      obtain ⟨restAll, hrestAll⟩ := hgs_pref

      have hwa_val : ((Circuit.mk (bwdTail.1 ++ stepBwd) 0).wires y).getD wa false =
          ((Circuit.mk gs0 0).wires y).getD wa false := by
        rw [wires_prefix bwdTail.1 stepBwd y 0 wa (by omega), hrestAll, List.append_assoc,
          wires_prefix gs0 (stepFwd ++ restAll) y 0 wa (by omega)]
      have hwb_val : ((Circuit.mk (bwdTail.1 ++ stepBwd) 0).wires y).getD wb false =
          ((Circuit.mk gs0 0).wires y).getD wb false := by
        rw [wires_prefix bwdTail.1 stepBwd y 0 wb (by omega), hrestAll, List.append_assoc,
          wires_prefix gs0 (stepFwd ++ restAll) y 0 wb (by omega)]
      have hmax_gs01 : ((Circuit.mk gs01 0).wires y).getD wMax false =
          (((Circuit.mk gs0 0).wires y).getD wa false || ((Circuit.mk gs0 0).wires y).getD wb false) := by
        have h1 : gs01 = (gs0 ++ [Gate.mk GateOp.or [wa, wb]]) ++ [Gate.mk GateOp.and [wa, wb]] := by
          simp [gs01, stepFwd]
        have hp1 := wires_prefix (gs0 ++ [Gate.mk GateOp.or [wa, wb]]) [Gate.mk GateOp.and [wa, wb]] y 0 wMax
          (by simp [wMax, hy])
        rw [h1, hp1, show wMax = n0 + gs0.length from rfl, wires_snoc_last n0 gs0 (Gate.mk GateOp.or [wa, wb]) y hy]
        simp [GateOp.eval]
      have hmin_gs01 : ((Circuit.mk gs01 0).wires y).getD wMin false =
          (((Circuit.mk gs0 0).wires y).getD wa false && ((Circuit.mk gs0 0).wires y).getD wb false) := by
        have h1 : gs01 = (gs0 ++ [Gate.mk GateOp.or [wa, wb]]) ++ [Gate.mk GateOp.and [wa, wb]] := by
          simp [gs01, stepFwd]
        have hwm_eq : wMin = n0 + (gs0 ++ [Gate.mk GateOp.or [wa, wb]]).length := by simp [wMin]; omega
        rw [h1, hwm_eq, wires_snoc_last n0 (gs0 ++ [Gate.mk GateOp.or [wa, wb]]) (Gate.mk GateOp.and [wa, wb]) y hy]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
        rw [wires_prefix gs0 [Gate.mk GateOp.or [wa, wb]] y 0 wa (by omega),
          wires_prefix gs0 [Gate.mk GateOp.or [wa, wb]] y 0 wb (by omega)]
      have hnMax_val : ((Circuit.mk bwdTail.1 0).wires y).getD nMax false =
          !(((Circuit.mk gs0 0).wires y).getD wa false || ((Circuit.mk gs0 0).wires y).getD wb false) := by
        have := hsemT i (by omega)
        have hws01_i : ws01.getD i 0 = wMax := by
          have hi_l : i < ws01.length := by rw [hws01_len]; exact hp.1
          rw [List.getD, List.getElem?_eq_getElem hi_l, Option.getD_some]
          simp only [ws01, List.getElem_set_ne (Ne.symm hp.2.2), List.getElem_set_self]
        rw [hws01_i, hmax_gs01] at this
        exact this
      have hnMin_val : ((Circuit.mk bwdTail.1 0).wires y).getD nMin false =
          !(((Circuit.mk gs0 0).wires y).getD wa false && ((Circuit.mk gs0 0).wires y).getD wb false) := by
        have := hsemT j (by omega)
        have hws01_j : ws01.getD j 0 = wMin := by
          have hj_l : j < ws01.length := by rw [hws01_len]; exact hp.2.1
          rw [List.getD, List.getElem?_eq_getElem hj_l, Option.getD_some]
          simp only [ws01, List.getElem_set_self]
        rw [hws01_j, hmin_gs01] at this
        exact this
      have hEval4 :
          ((Circuit.mk (bwdTail.1 ++ stepBwd) 0).wires y).getD na false =
            !(((Circuit.mk gs0 0).wires y).getD wa false) ∧
          ((Circuit.mk (bwdTail.1 ++ stepBwd) 0).wires y).getD nb false =
            !(((Circuit.mk gs0 0).wires y).getD wb false) := by
        let G0 := bwdTail.1
        have hG0_len : G0.length = bwdTail.1.length := rfl
        let G1 := G0 ++ [Gate.mk GateOp.and [wb, nMin]]
        let G2 := G1 ++ [Gate.mk GateOp.or [nMax, t1]]
        let G3 := G2 ++ [Gate.mk GateOp.and [wa, nMin]]
        let G4 := G3 ++ [Gate.mk GateOp.or [nMax, t2]]
        have hG4 : bwdTail.1 ++ stepBwd = G4 := by simp [G0, G1, G2, G3, G4, stepBwd, List.append_assoc]
        have hG0_wa : ((Circuit.mk G0 0).wires y).getD wa false = ((Circuit.mk gs0 0).wires y).getD wa false := by
          rw [← hwa_val, wires_prefix bwdTail.1 stepBwd y 0 wa (by omega)]
        have hG0_wb : ((Circuit.mk G0 0).wires y).getD wb false = ((Circuit.mk gs0 0).wires y).getD wb false := by
          rw [← hwb_val, wires_prefix bwdTail.1 stepBwd y 0 wb (by omega)]
        have ht1_v : ((Circuit.mk G1 0).wires y).getD t1 false =
            (((Circuit.mk gs0 0).wires y).getD wb false &&
             !(((Circuit.mk gs0 0).wires y).getD wa false && ((Circuit.mk gs0 0).wires y).getD wb false)) := by
          rw [show G1 = G0 ++ [Gate.mk GateOp.and [wb, nMin]] from rfl,
            show t1 = n0 + G0.length from rfl, wires_snoc_last n0 G0 _ y hy]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          rw [hG0_wb, hnMin_val]
        have hna_v : ((Circuit.mk G2 0).wires y).getD na false =
            !(((Circuit.mk gs0 0).wires y).getD wa false) := by
          have hna_eq : na = n0 + G1.length := by simp [G1, G0, na]; omega
          rw [show G2 = G1 ++ [Gate.mk GateOp.or [nMax, t1]] from rfl, hna_eq, wires_snoc_last n0 G1 _ y hy]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          rw [wires_prefix G0 [Gate.mk GateOp.and [wb, nMin]] y 0 nMax (by omega), hnMax_val, ht1_v]
          exact (bwd_comp_bool _ _).1
        have ht2_v : ((Circuit.mk G3 0).wires y).getD t2 false =
            (((Circuit.mk gs0 0).wires y).getD wa false &&
             !(((Circuit.mk gs0 0).wires y).getD wa false && ((Circuit.mk gs0 0).wires y).getD wb false)) := by
          have ht2_eq : t2 = n0 + G2.length := by simp [G2, G1, G0, t2]; omega
          rw [show G3 = G2 ++ [Gate.mk GateOp.and [wa, nMin]] from rfl, ht2_eq, wires_snoc_last n0 G2 _ y hy]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          have hG2_eq : G2 = G0 ++ [Gate.mk GateOp.and [wb, nMin], Gate.mk GateOp.or [nMax, t1]] := by simp [G2, G1]
          rw [hG2_eq, wires_prefix G0 _ y 0 wa (by omega), wires_prefix G0 _ y 0 nMin (by omega),
            hG0_wa, hnMin_val]
        have hnb_v : ((Circuit.mk G4 0).wires y).getD nb false =
            !(((Circuit.mk gs0 0).wires y).getD wb false) := by
          have hnb_eq : nb = n0 + G3.length := by simp [G3, G2, G1, G0, nb]; omega
          rw [show G4 = G3 ++ [Gate.mk GateOp.or [nMax, t2]] from rfl, hnb_eq, wires_snoc_last n0 G3 _ y hy]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          have hG3_eq : G3 = G0 ++ [Gate.mk GateOp.and [wb, nMin], Gate.mk GateOp.or [nMax, t1], Gate.mk GateOp.and [wa, nMin]] := by
            simp [G3, G2, G1]
          rw [hG3_eq, wires_prefix G0 _ y 0 nMax (by omega), hnMax_val, ← hG3_eq, ht2_v]
          exact (bwd_comp_bool _ _).2
        rw [hG4]
        refine ⟨?_, hnb_v⟩
        have hG4_2 : G4 = G2 ++ [Gate.mk GateOp.and [wa, nMin], Gate.mk GateOp.or [nMax, t2]] := by simp [G4, G3]
        have hna_lt : na < y.length + G2.length := by simp [G2, G1, G0, na, hy]; omega
        rw [hG4_2, wires_prefix G2 _ y 0 na hna_lt, hna_v]
      by_cases hkj : k = j
      · rw [hkj]
        have hget_j : ((bwdTail.2.set i na).set j nb).getD j 0 = nb := by
          have hj_l : j < ((bwdTail.2.set i na).set j nb).length := by simp; omega
          rw [List.getD, List.getElem?_eq_getElem hj_l, Option.getD_some, List.getElem_set_self]
        rw [hget_j, hEval4.2]
      · by_cases hki : k = i
        · rw [hki]
          have hget_i : ((bwdTail.2.set i na).set j nb).getD i 0 = na := by
            have hi_l : i < ((bwdTail.2.set i na).set j nb).length := by simp; omega
            rw [List.getD, List.getElem?_eq_getElem hi_l, Option.getD_some,
              List.getElem_set_ne (Ne.symm hp.2.2), List.getElem_set_self]
          rw [hget_i, hEval4.1]
        · have hget_k : ((bwdTail.2.set i na).set j nb).getD k 0 = bwdTail.2.getD k 0 := by
            simp [List.getD, List.getElem?_set_ne (Ne.symm hkj), List.getElem?_set_ne (Ne.symm hki)]
          have hk_lt_bwd : k < bwdTail.2.length := by omega
          have hwk_lt : bwdTail.2.getD k 0 < n0 + bwdTail.1.length := by
            have : bwdTail.2.getD k 0 = bwdTail.2[k]'hk_lt_bwd := by
              simp [List.getD, List.getElem?_eq_getElem hk_lt_bwd]
            rw [this]; exact hnegTail_lt _ (List.getElem_mem hk_lt_bwd)
          rw [hget_k, wires_prefix bwdTail.1 stepBwd y 0 (bwdTail.2.getD k 0) (by omega)]
          have hsem_k := hsemT k (by omega)
          have hws01_k : ws01.getD k 0 = ws0.getD k 0 := by
            simp [ws01, List.getD, List.getElem?_set_ne (Ne.symm hkj), List.getElem?_set_ne (Ne.symm hki)]
          have hws0_k_lt : ws0.getD k 0 < n0 + gs0.length := by
            have : ws0.getD k 0 = ws0[k]'hk := by simp [List.getD, List.getElem?_eq_getElem hk]
            rw [this]; exact hws0 _ (List.getElem_mem hk)
          rw [hsem_k, hws01_k, wires_prefix gs0 stepFwd y 0 (ws0.getD k 0) (by omega)]

def compileInvSorted (n0 : ℕ) : (a : ℕ) → List Gate → List ℕ → List Gate × List ℕ
  | 0, gs, ws =>
    let w0 := ws.getD 0 0
    let nw0 := n0 + gs.length
    (gs ++ [⟨GateOp.not, [w0]⟩], [nw0])
  | a + 1, gs, ws =>
    let s := 2 ^ (a + 1) - 1
    let wm := ws.getD s 0
    let nwm := n0 + gs.length
    let gs1 := gs ++ [⟨GateOp.not, [wm]⟩]

    let foldCollapse := (List.range s).foldl
      (fun (acc : List Gate × List ℕ) j =>
        let g := acc.1
        let zs := acc.2
        let wL := ws.getD j 0
        let wR := ws.getD (s + 1 + j) 0
        let wAnd := n0 + g.length
        let wOr := n0 + g.length + 1
        (g ++ [⟨GateOp.and, [wL, nwm]⟩, ⟨GateOp.or, [wR, wAnd]⟩], zs ++ [wOr]))
      (gs1, [])
    let gs2 := foldCollapse.1
    let zs := foldCollapse.2
    let recRes := compileInvSorted n0 a gs2 zs
    let gs3 := recRes.1
    let nzs := recRes.2

    let foldRecon := (List.range s).foldl
      (fun (acc : List Gate × List ℕ × List ℕ) j =>
        let g := acc.1
        let lo := acc.2.1
        let hi := acc.2.2
        let nz := nzs.getD j 0
        let wLo := n0 + g.length
        let wHi := n0 + g.length + 1
        (g ++ [⟨GateOp.and, [nwm, nz]⟩, ⟨GateOp.or, [nwm, nz]⟩], lo ++ [wLo], hi ++ [wHi]))
      (gs3, [], [])
    (foldRecon.1, foldRecon.2.1 ++ [nwm] ++ foldRecon.2.2)

lemma compileInvSorted_spec (n0 : ℕ) (a : ℕ) :
    ∀ (gs : List Gate) (ws : List ℕ),
    ws.length = 2 ^ (a + 1) - 1 →
    (∀ w ∈ ws, w < n0 + gs.length) →
    let res := compileInvSorted n0 a gs ws
    (∃ extra, res.1 = gs ++ extra ∧
      extra.length ≤ 4 * 2 ^ (a + 1) ∧
      notCount ⟨extra, 0⟩ = a + 1 ∧
      FanInTwo ⟨extra, 0⟩ ∧
      ReadsBack (n0 + gs.length) ⟨extra, 0⟩) ∧
    res.2.length = 2 ^ (a + 1) - 1 ∧
    (∀ w ∈ res.2, w < n0 + res.1.length) ∧
    (∀ y : List Bool, y.length = n0 →
      (∀ i j, i ≤ j → j < ws.length →
        ((Circuit.mk gs 0).wires y).getD (ws.getD j 0) false ≤
          ((Circuit.mk gs 0).wires y).getD (ws.getD i 0) false) →
      ∀ i < ws.length,
        ((Circuit.mk res.1 0).wires y).getD (res.2.getD i 0) false =
          !(((Circuit.mk gs 0).wires y).getD (ws.getD i 0) false)) := by
  induction a with
  | zero =>
    intro gs ws hlen hws
    have h0 : 0 < ws.length := by omega
    have hw0 : ws.getD 0 0 < n0 + gs.length := by
      have : ws.getD 0 0 = ws[0]'h0 := by simp [List.getD, List.getElem?_eq_getElem h0]
      rw [this]; exact hws _ (List.getElem_mem h0)
    refine ⟨⟨[⟨GateOp.not, [ws.getD 0 0]⟩], rfl, by simp, rfl, ?_, ?_⟩, rfl, ?_, ?_⟩
    · intro g hg; simp only [List.mem_singleton] at hg; subst hg; simp
    · intro j hj u hu
      have hj0 : j = 0 := by simp at hj; omega
      subst hj0; simp only [gateAt, List.getD_cons_zero, List.mem_singleton] at hu
      subst hu; exact hw0
    · intro w hw; simp only [compileInvSorted, List.mem_singleton] at hw; subst hw
      change n0 + gs.length < n0 + (gs ++ [Gate.mk GateOp.not [ws.getD 0 0]]).length
      simp only [List.length_append, List.length_singleton]; omega
    · intro y hy _ i hi
      have hi0 : i = 0 := by omega
      subst hi0
      simp only [compileInvSorted, List.getD, List.getElem?_cons_zero, Option.getD_some]
      rw [wires_snoc]
      have hl : ((Circuit.mk gs 0).wires y).length = n0 + gs.length := by rw [wires_length, hy]
      simp only [List.getElem?_append_right (Nat.le_of_eq hl), hl, Nat.sub_self,
        List.getElem?_cons_zero, Option.getD_some, GateOp.eval, List.map_cons, List.map_nil, List.headD_cons]
      rfl
  | succ a ih =>
    intro gs ws hlen hws
    let s := 2 ^ (a + 1) - 1
    have hs_pos : 1 ≤ 2 ^ (a + 1) := Nat.one_le_two_pow
    have hlen_eq : 2 ^ (a + 2) - 1 = 2 * s + 1 := by rw [Nat.pow_succ]; omega
    have hs_lt : s < ws.length := by omega
    let wm := ws.getD s 0
    have hwm_lt : wm < n0 + gs.length := by
      have : wm = ws[s]'hs_lt := by simp [wm, List.getD, List.getElem?_eq_getElem hs_lt]
      rw [this]; exact hws _ (List.getElem_mem hs_lt)
    let nwm := n0 + gs.length
    let gs1 := gs ++ [⟨GateOp.not, [wm]⟩]
    have hgs1_len : gs1.length = gs.length + 1 := by simp [gs1]
    have hstep1_fit : FanInTwo ⟨[⟨GateOp.not, [wm]⟩], 0⟩ := by
      intro g hg; simp only [List.mem_singleton] at hg; subst hg; simp
    have hstep1_rb : ReadsBack (n0 + gs.length) ⟨[⟨GateOp.not, [wm]⟩], 0⟩ := by
      intro j hj u hu
      have hj0 : j = 0 := by simp at hj; omega
      subst hj0; simp only [gateAt, List.getD_cons_zero, List.mem_singleton] at hu
      subst hu; exact hwm_lt

    have hCol : ∀ r ≤ s,
        let fc := (List.range r).foldl
          (fun (acc : List Gate × List ℕ) j =>
            let g := acc.1; let zs := acc.2
            let wL := ws.getD j 0; let wR := ws.getD (s + 1 + j) 0
            (g ++ [⟨GateOp.and, [wL, nwm]⟩, ⟨GateOp.or, [wR, n0 + g.length]⟩], zs ++ [n0 + g.length + 1]))
          (gs1, [])
        (∃ ex, fc.1 = gs1 ++ ex ∧ ex.length = 2 * r ∧ Monotone2 ⟨ex, 0⟩ ∧
          ReadsBack (n0 + gs1.length) ⟨ex, 0⟩) ∧
        fc.2.length = r ∧
        (∀ w ∈ fc.2, w < n0 + fc.1.length) ∧
        (∀ y : List Bool, y.length = n0 → ∀ j < r,
          ((Circuit.mk fc.1 0).wires y).getD (fc.2.getD j 0) false =
            (((Circuit.mk gs 0).wires y).getD (ws.getD (s + 1 + j) 0) false ||
             (((Circuit.mk gs 0).wires y).getD (ws.getD j 0) false &&
              !(((Circuit.mk gs 0).wires y).getD wm false)))) := by
      intro r hr
      induction r with
      | zero =>
        refine ⟨⟨[], by simp, rfl, fun _ h => by simp at h, fun j hj => by simp at hj⟩,
          rfl, fun _ h => by simp at h, fun _ _ _ hj => by omega⟩
      | succ r ihr =>
        obtain ⟨⟨ex, hex, hlen_ex, hmon_ex, hrb_ex⟩, hzl, hzlt, hsem⟩ := ihr (Nat.le_of_succ_le hr)
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
        set fc := (List.range r).foldl
          (fun (acc : List Gate × List ℕ) j =>
            let g := acc.1; let zs := acc.2
            let wL := ws.getD j 0; let wR := ws.getD (s + 1 + j) 0
            (g ++ [⟨GateOp.and, [wL, nwm]⟩, ⟨GateOp.or, [wR, n0 + g.length]⟩], zs ++ [n0 + g.length + 1]))
          (gs1, [])
        have hwL : ws.getD r 0 < n0 + gs.length := by
          have hr' : r < ws.length := by omega
          have : ws.getD r 0 = ws[r]'hr' := by simp [List.getD, List.getElem?_eq_getElem hr']
          rw [this]; exact hws _ (List.getElem_mem hr')
        have hwR : ws.getD (s + 1 + r) 0 < n0 + gs.length := by
          have hr' : s + 1 + r < ws.length := by omega
          have : ws.getD (s + 1 + r) 0 = ws[s + 1 + r]'hr' := by simp [List.getD, List.getElem?_eq_getElem hr']
          rw [this]; exact hws _ (List.getElem_mem hr')
        have hlen_fc : fc.1.length = gs.length + 1 + 2 * r := by rw [hex, List.length_append, hgs1_len, hlen_ex]
        let st : List Gate := [⟨GateOp.and, [ws.getD r 0, nwm]⟩, ⟨GateOp.or, [ws.getD (s + 1 + r) 0, n0 + fc.1.length]⟩]
        have hst_mon : Monotone2 ⟨st, 0⟩ := by
          intro g hg; simp only [st, List.mem_cons, List.not_mem_nil, or_false] at hg
          rcases hg with rfl | rfl <;> simp
        have hst_rb : ReadsBack (n0 + fc.1.length) ⟨st, 0⟩ := by
          intro idx hidx u hu
          have : idx = 0 ∨ idx = 1 := by simp [st] at hidx; omega
          rcases this with rfl | rfl
          · simp only [st, gateAt, List.getD_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hu
            rcases hu with rfl | rfl
            · omega
            · dsimp only [nwm]; omega
          · simp only [st, gateAt, List.getD_cons_succ, List.getD_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hu
            rcases hu with rfl | rfl <;> omega
        refine ⟨⟨ex ++ st, by dsimp only [st]; rw [hex, List.append_assoc], by simp [st, hlen_ex]; omega,
          monotone2_append ex st 0 hmon_ex hst_mon,
          readsBack_append (n0 + gs1.length) ex st 0 hrb_ex (by simpa [hex, Nat.add_assoc] using hst_rb)⟩,
          by simp [hzl], ?_, ?_⟩
        · intro w hw
          rcases List.mem_append.mp hw with h | h
          · have := hzlt w h; simp [st]; omega
          · simp only [List.mem_singleton] at h; subst h; simp [st]; omega
        · intro y hy j hj
          by_cases hjr : j < r
          · have hget : (fc.2 ++ [n0 + fc.1.length + 1]).getD j 0 = fc.2.getD j 0 := by
              simp [List.getD, List.getElem?_append_left (by omega : j < fc.2.length)]
            have hlt_j : fc.2.getD j 0 < n0 + fc.1.length := by
              have : fc.2.getD j 0 = fc.2[j]'(by omega) := by
                simp [List.getD, List.getElem?_eq_getElem (by omega : j < fc.2.length)]
              rw [this]; exact hzlt _ (List.getElem_mem (by omega))
            rw [hget, wires_prefix fc.1 st y 0 _ (by omega)]
            exact hsem y hy j hjr
          · have hj_eq : j = r := by omega
            rw [hj_eq]
            have hget : (fc.2 ++ [n0 + fc.1.length + 1]).getD r 0 = n0 + fc.1.length + 1 := by
              rw [List.getD, List.getElem?_append_right (by omega : fc.2.length ≤ r), hzl, Nat.sub_self]
              rfl
            rw [hget]
            have hst_eq : fc.1 ++ st = (fc.1 ++ [Gate.mk GateOp.and [ws.getD r 0, nwm]]) ++
                [Gate.mk GateOp.or [ws.getD (s + 1 + r) 0, n0 + fc.1.length]] := by simp [st]
            have hidx_eq : n0 + fc.1.length + 1 = n0 + (fc.1 ++ [Gate.mk GateOp.and [ws.getD r 0, nwm]]).length := by simp; omega
            change ((Circuit.mk (fc.1 ++ st) 0).wires y).getD (n0 + fc.1.length + 1) false = _
            rw [hst_eq, hidx_eq, wires_snoc_last n0 (fc.1 ++ [Gate.mk GateOp.and [ws.getD r 0, nwm]]) _ y hy]
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
            have h_wR : ((Circuit.mk (fc.1 ++ [Gate.mk GateOp.and [ws.getD r 0, nwm]]) 0).wires y).getD
                (ws.getD (s + 1 + r) 0) false =
                ((Circuit.mk gs 0).wires y).getD (ws.getD (s + 1 + r) 0) false := by
              rw [hex]; dsimp only [gs1]
              rw [List.append_assoc, List.append_assoc, wires_prefix gs _ y 0 _ (by omega)]
            have h_and : ((Circuit.mk (fc.1 ++ [Gate.mk GateOp.and [ws.getD r 0, nwm]]) 0).wires y).getD
                (n0 + fc.1.length) false =
                (((Circuit.mk gs 0).wires y).getD (ws.getD r 0) false &&
                 !(((Circuit.mk gs 0).wires y).getD wm false)) := by
              rw [wires_snoc_last n0 fc.1 (Gate.mk GateOp.and [ws.getD r 0, nwm]) y hy]
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
              have h_wL : ((Circuit.mk fc.1 0).wires y).getD (ws.getD r 0) false =
                  ((Circuit.mk gs 0).wires y).getD (ws.getD r 0) false := by
                rw [hex]; dsimp only [gs1]
                rw [List.append_assoc, wires_prefix gs _ y 0 _ (by omega)]
              have h_nwm : ((Circuit.mk fc.1 0).wires y).getD nwm false =
                  !(((Circuit.mk gs 0).wires y).getD wm false) := by
                rw [hex, wires_prefix gs1 ex y 0 nwm (by simp [nwm, gs1, hy])]
                rw [show gs1 = gs ++ [Gate.mk GateOp.not [wm]] from rfl,
                  show nwm = n0 + gs.length from rfl, wires_snoc_last n0 gs _ y hy]
                simp [GateOp.eval]
              rw [h_wL, h_nwm]
            rw [h_wR, h_and]
    obtain ⟨⟨exCol, hgs2, hlen_col, hmon_col, hrb_col⟩, hzs_len, hzs_lt, hcol_sem⟩ := hCol s le_rfl
    set fc := (List.range s).foldl
      (fun (acc : List Gate × List ℕ) j =>
        let g := acc.1; let zs := acc.2
        let wL := ws.getD j 0; let wR := ws.getD (s + 1 + j) 0
        (g ++ [⟨GateOp.and, [wL, nwm]⟩, ⟨GateOp.or, [wR, n0 + g.length]⟩], zs ++ [n0 + g.length + 1]))
      (gs1, [])
    let gs2 := fc.1
    let zs := fc.2
    change gs2 = gs1 ++ exCol at hgs2
    change zs.length = s at hzs_len
    change ∀ w ∈ zs, w < n0 + gs2.length at hzs_lt

    have ⟨⟨exRec, hgs3, hlen_rec, hnot_rec, hfit_rec, hrb_rec⟩, hnzs_len, hnzs_lt, hrec_sem⟩ :=
      ih gs2 zs hzs_len hzs_lt
    let gs3 := (compileInvSorted n0 a gs2 zs).1
    let nzs := (compileInvSorted n0 a gs2 zs).2
    change gs3 = gs2 ++ exRec at hgs3
    change nzs.length = s at hnzs_len
    change ∀ w ∈ nzs, w < n0 + gs3.length at hnzs_lt

    have hRecon : ∀ r ≤ s,
        let fr := (List.range r).foldl
          (fun (acc : List Gate × List ℕ × List ℕ) j =>
            let g := acc.1; let lo := acc.2.1; let hi := acc.2.2
            let nz := nzs.getD j 0
            (g ++ [⟨GateOp.and, [nwm, nz]⟩, ⟨GateOp.or, [nwm, nz]⟩],
             lo ++ [n0 + g.length], hi ++ [n0 + g.length + 1]))
          (gs3, [], [])
        (∃ ex, fr.1 = gs3 ++ ex ∧ ex.length = 2 * r ∧ Monotone2 ⟨ex, 0⟩ ∧
          ReadsBack (n0 + gs3.length) ⟨ex, 0⟩) ∧
        fr.2.1.length = r ∧ fr.2.2.length = r ∧
        (∀ w ∈ fr.2.1, w < n0 + fr.1.length) ∧
        (∀ w ∈ fr.2.2, w < n0 + fr.1.length) ∧
        (∀ y : List Bool, y.length = n0 → ∀ j < r,
          ((Circuit.mk fr.1 0).wires y).getD (fr.2.1.getD j 0) false =
            (!(((Circuit.mk gs 0).wires y).getD wm false) &&
             ((Circuit.mk gs3 0).wires y).getD (nzs.getD j 0) false) ∧
          ((Circuit.mk fr.1 0).wires y).getD (fr.2.2.getD j 0) false =
            (!(((Circuit.mk gs 0).wires y).getD wm false) ||
             ((Circuit.mk gs3 0).wires y).getD (nzs.getD j 0) false)) := by
      intro r hr
      induction r with
      | zero =>
        refine ⟨⟨[], by simp, rfl, fun _ h => by simp at h, fun j hj => by simp at hj⟩,
          rfl, rfl, fun _ h => by simp at h, fun _ h => by simp at h, fun _ _ _ hj => by omega⟩
      | succ r ihr =>
        obtain ⟨⟨ex, hex, hlen_ex, hmon_ex, hrb_ex⟩, hlo_l, hhi_l, hlo_lt, hhi_lt, hsem⟩ :=
          ihr (Nat.le_of_succ_le hr)
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
        set fr := (List.range r).foldl
          (fun (acc : List Gate × List ℕ × List ℕ) j =>
            let g := acc.1; let lo := acc.2.1; let hi := acc.2.2
            let nz := nzs.getD j 0
            (g ++ [⟨GateOp.and, [nwm, nz]⟩, ⟨GateOp.or, [nwm, nz]⟩],
             lo ++ [n0 + g.length], hi ++ [n0 + g.length + 1]))
          (gs3, [], [])
        have hgs_le_gs3 : gs.length + 1 ≤ gs3.length := by
          rw [hgs3, hgs2, List.length_append, List.length_append, hgs1_len]; omega
        have hnwm_lt : nwm < n0 + fr.1.length := by rw [hex, List.length_append]; dsimp only [nwm]; omega
        have hnz_lt : nzs.getD r 0 < n0 + gs3.length := by
          have hr' : r < nzs.length := by omega
          have : nzs.getD r 0 = nzs[r]'hr' := by simp [List.getD, List.getElem?_eq_getElem hr']
          rw [this]; exact hnzs_lt _ (List.getElem_mem hr')
        have hnz_lt_fr : nzs.getD r 0 < n0 + fr.1.length := by rw [hex, List.length_append]; omega
        let st : List Gate := [⟨GateOp.and, [nwm, nzs.getD r 0]⟩, ⟨GateOp.or, [nwm, nzs.getD r 0]⟩]
        have hst_mon : Monotone2 ⟨st, 0⟩ := by
          intro g hg; simp only [st, List.mem_cons, List.not_mem_nil, or_false] at hg
          rcases hg with rfl | rfl <;> simp
        have hst_rb : ReadsBack (n0 + fr.1.length) ⟨st, 0⟩ := by
          intro idx hidx u hu
          have : idx = 0 ∨ idx = 1 := by simp [st] at hidx; omega
          rcases this with rfl | rfl
          · simp only [st, gateAt, List.getD_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hu
            rcases hu with rfl | rfl <;> omega
          · simp only [st, gateAt, List.getD_cons_succ, List.getD_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hu
            rcases hu with rfl | rfl <;> omega
        refine ⟨⟨ex ++ st, by dsimp only; rw [hex, List.append_assoc], by simp [st, hlen_ex]; omega,
          monotone2_append ex st 0 hmon_ex hst_mon,
          readsBack_append (n0 + gs3.length) ex st 0 hrb_ex (by simpa [hex, Nat.add_assoc] using hst_rb)⟩,
          by simp [hlo_l], by simp [hhi_l], ?_, ?_, ?_⟩
        · intro w hw
          rcases List.mem_append.mp hw with h | h
          · have := hlo_lt w h; simp [st]; omega
          · simp only [List.mem_singleton] at h; subst h; simp [st]
        · intro w hw
          rcases List.mem_append.mp hw with h | h
          · have := hhi_lt w h; simp [st]; omega
          · simp only [List.mem_singleton] at h; subst h; simp [st]; omega
        · intro y hy j hj
          by_cases hjr : j < r
          · have hg1 : (fr.2.1 ++ [n0 + fr.1.length]).getD j 0 = fr.2.1.getD j 0 := by
              simp [List.getD, List.getElem?_append_left (by omega : j < fr.2.1.length)]
            have hg2 : (fr.2.2 ++ [n0 + fr.1.length + 1]).getD j 0 = fr.2.2.getD j 0 := by
              simp [List.getD, List.getElem?_append_left (by omega : j < fr.2.2.length)]
            have hl1 : fr.2.1.getD j 0 < n0 + fr.1.length := by
              have : fr.2.1.getD j 0 = fr.2.1[j]'(by omega) := by
                simp [List.getD, List.getElem?_eq_getElem (by omega : j < fr.2.1.length)]
              rw [this]; exact hlo_lt _ (List.getElem_mem (by omega))
            have hl2 : fr.2.2.getD j 0 < n0 + fr.1.length := by
              have : fr.2.2.getD j 0 = fr.2.2[j]'(by omega) := by
                simp [List.getD, List.getElem?_eq_getElem (by omega : j < fr.2.2.length)]
              rw [this]; exact hhi_lt _ (List.getElem_mem (by omega))
            rw [hg1, hg2, wires_prefix fr.1 st y 0 _ (by omega), wires_prefix fr.1 st y 0 _ (by omega)]
            exact hsem y hy j hjr
          · have hj_eq : j = r := by omega
            rw [hj_eq]
            have hg1 : (fr.2.1 ++ [n0 + fr.1.length]).getD r 0 = n0 + fr.1.length := by
              rw [List.getD, List.getElem?_append_right (by omega : fr.2.1.length ≤ r), hlo_l, Nat.sub_self]; rfl
            have hg2 : (fr.2.2 ++ [n0 + fr.1.length + 1]).getD r 0 = n0 + fr.1.length + 1 := by
              rw [List.getD, List.getElem?_append_right (by omega : fr.2.2.length ≤ r), hhi_l, Nat.sub_self]; rfl
            have h_nwm_fr : ((Circuit.mk fr.1 0).wires y).getD nwm false =
                !(((Circuit.mk gs 0).wires y).getD wm false) := by
              rw [hex, hgs3, hgs2, List.append_assoc, List.append_assoc,
                wires_prefix gs1 _ y 0 nwm (by simp [nwm, gs1, hy])]
              rw [show gs1 = gs ++ [Gate.mk GateOp.not [wm]] from rfl,
                show nwm = n0 + gs.length from rfl, wires_snoc_last n0 gs _ y hy]
              simp [GateOp.eval]
            have h_nz_fr : ((Circuit.mk fr.1 0).wires y).getD (nzs.getD r 0) false =
                ((Circuit.mk gs3 0).wires y).getD (nzs.getD r 0) false := by
              rw [hex, wires_prefix gs3 ex y 0 _ (by omega)]
            rw [hg1, hg2]
            have hst_eq : fr.1 ++ st = (fr.1 ++ [Gate.mk GateOp.and [nwm, nzs.getD r 0]]) ++
                [Gate.mk GateOp.or [nwm, nzs.getD r 0]] := by simp [st]
            constructor
            · change ((Circuit.mk (fr.1 ++ st) 0).wires y).getD (n0 + fr.1.length) false = _
              have hp1 := wires_prefix (fr.1 ++ [Gate.mk GateOp.and [nwm, nzs.getD r 0]])
                [Gate.mk GateOp.or [nwm, nzs.getD r 0]] y 0 (n0 + fr.1.length) (by simp [hy])
              rw [hst_eq, hp1, wires_snoc_last n0 fr.1 _ y hy]
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
              rw [h_nwm_fr, h_nz_fr]
            · change ((Circuit.mk (fr.1 ++ st) 0).wires y).getD (n0 + fr.1.length + 1) false = _
              have hidx_eq : n0 + fr.1.length + 1 = n0 + (fr.1 ++ [Gate.mk GateOp.and [nwm, nzs.getD r 0]]).length := by simp; omega
              rw [hst_eq, hidx_eq, wires_snoc_last n0 (fr.1 ++ [Gate.mk GateOp.and [nwm, nzs.getD r 0]]) _ y hy]
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
              rw [wires_prefix fr.1 _ y 0 nwm (by omega), wires_prefix fr.1 _ y 0 (nzs.getD r 0) (by omega),
                h_nwm_fr, h_nz_fr]
    obtain ⟨⟨exRec2, hgs4, hlen_rec2, hmon_rec2, hrb_rec2⟩, hlo_l, hhi_l, hlo_lt, hhi_lt, hrec2_sem⟩ :=
      hRecon s le_rfl
    set fr := (List.range s).foldl
      (fun (acc : List Gate × List ℕ × List ℕ) j =>
        let g := acc.1; let lo := acc.2.1; let hi := acc.2.2
        let nz := nzs.getD j 0
        (g ++ [⟨GateOp.and, [nwm, nz]⟩, ⟨GateOp.or, [nwm, nz]⟩],
         lo ++ [n0 + g.length], hi ++ [n0 + g.length + 1]))
      (gs3, [], [])
    let exAll := [⟨GateOp.not, [wm]⟩] ++ exCol ++ exRec ++ exRec2
    have hgs_all : fr.1 = gs ++ exAll := by
      change fr.1 = gs3 ++ exRec2 at hgs4
      simp [exAll, hgs4, hgs3, hgs2, gs1, List.append_assoc]
    have hex_len : exAll.length ≤ 4 * 2 ^ (a + 2) := by
      simp only [exAll, List.length_append, List.length_singleton, hlen_col, hlen_rec2]
      rw [Nat.pow_succ]; omega
    have hex_not : notCount ⟨exAll, 0⟩ = a + 2 := by
      simp only [exAll, notCount_append, notCount_singleton_not,
        notCount_of_monotone2 ⟨exCol, 0⟩ hmon_col,
        notCount_of_monotone2 ⟨exRec2, 0⟩ hmon_rec2, hnot_rec]
      omega
    have hex_fit : FanInTwo ⟨exAll, 0⟩ := by
      apply fanInTwo_append _ exRec2 0 _ (monotone2_imp_fanInTwo _ hmon_rec2)
      apply fanInTwo_append _ exRec 0 _ hfit_rec
      exact fanInTwo_append _ exCol 0 hstep1_fit (monotone2_imp_fanInTwo _ hmon_col)
    have hex_rb : ReadsBack (n0 + gs.length) ⟨exAll, 0⟩ := by
      have h12 : ReadsBack (n0 + gs.length) ⟨[⟨GateOp.not, [wm]⟩] ++ exCol, 0⟩ :=
        readsBack_append (n0 + gs.length) [⟨GateOp.not, [wm]⟩] exCol 0 hstep1_rb
          (by simpa [gs1, Nat.add_assoc] using hrb_col)
      have h123 : ReadsBack (n0 + gs.length) ⟨[⟨GateOp.not, [wm]⟩] ++ exCol ++ exRec, 0⟩ :=
        readsBack_append (n0 + gs.length) _ exRec 0 h12
          (by
            have hlen12 : n0 + gs.length + ([Gate.mk GateOp.not [wm]] ++ exCol).length = n0 + gs2.length := by
              rw [hgs2]; dsimp only [gs1]; simp; omega
            rw [hlen12]; exact hrb_rec)
      exact readsBack_append (n0 + gs.length) _ exRec2 0 h123
        (by
          have hlen123 : n0 + gs.length + ([Gate.mk GateOp.not [wm]] ++ exCol ++ exRec).length = n0 + gs3.length := by
            rw [hgs3, hgs2]; dsimp only [gs1]; simp; omega
          rw [hlen123]; exact hrb_rec2)
    refine ⟨⟨exAll, hgs_all, hex_len, hex_not, hex_fit, hex_rb⟩, ?_, ?_, ?_⟩
    · simp only [compileInvSorted, List.length_append, List.length_singleton]
      change fr.2.1.length + 1 + fr.2.2.length = 2 ^ (a + 2) - 1
      omega
    · intro w hw
      change w ∈ fr.2.1 ++ [nwm] ++ fr.2.2 at hw
      simp only [List.mem_append, List.mem_singleton] at hw
      rcases hw with (h | rfl) | h
      · exact hlo_lt w h
      · change nwm < n0 + fr.1.length; rw [hgs_all]; simp [nwm, exAll]
      · exact hhi_lt w h
    · intro y hy hsort i hi

      have hzs_sort : ∀ j1 j2, j1 ≤ j2 → j2 < zs.length →
          ((Circuit.mk gs2 0).wires y).getD (zs.getD j2 0) false ≤
            ((Circuit.mk gs2 0).wires y).getD (zs.getD j1 0) false := by
        intro j1 j2 h12 hj2
        rw [hcol_sem y hy j1 (by omega), hcol_sem y hy j2 (by omega)]
        have hL := hsort j1 j2 h12 (by omega)
        have hR := hsort (s + 1 + j1) (s + 1 + j2) (by omega) (by omega)
        have hbool : ∀ (bm bL1 bL2 bR1 bR2 : Bool), bL2 ≤ bL1 → bR2 ≤ bR1 →
            (bR2 || (bL2 && !bm)) ≤ (bR1 || (bL1 && !bm)) := by
          intro bm bL1 bL2 bR1 bR2 h1 h2
          cases bm <;> cases bL1 <;> cases bL2 <;> cases bR1 <;> cases bR2 <;>
            first | decide | (exfalso; exact absurd h1 (by decide)) | (exfalso; exact absurd h2 (by decide))
        exact hbool _ _ _ _ _ hL hR
      have hnz_val : ∀ j < s, ((Circuit.mk gs3 0).wires y).getD (nzs.getD j 0) false =
          !(((Circuit.mk gs 0).wires y).getD (ws.getD (s + 1 + j) 0) false ||
            (((Circuit.mk gs 0).wires y).getD (ws.getD j 0) false &&
             !(((Circuit.mk gs 0).wires y).getD wm false))) := by
        intro j hj
        rw [hrec_sem y hy hzs_sort j (by omega), hcol_sem y hy j hj]
      change ((Circuit.mk fr.1 0).wires y).getD ((fr.2.1 ++ [nwm] ++ fr.2.2).getD i 0) false = _
      by_cases hi1 : i < s
      · have hget : (fr.2.1 ++ [nwm] ++ fr.2.2).getD i 0 = fr.2.1.getD i 0 := by
          have hl1 : i < (fr.2.1 ++ [nwm]).length := by simp [hlo_l]; omega
          have hl2 : i < fr.2.1.length := by rw [hlo_l]; exact hi1
          simp [List.getD, List.getElem?_append_left hl1, List.getElem?_append_left hl2]
        rw [hget, (hrec2_sem y hy i hi1).1, hnz_val i hi1]
        have hm_le : ((Circuit.mk gs 0).wires y).getD wm false ≤
            ((Circuit.mk gs 0).wires y).getD (ws.getD i 0) false := hsort i s (by omega) hs_lt
        have hR_le : ((Circuit.mk gs 0).wires y).getD (ws.getD (s + 1 + i) 0) false ≤
            ((Circuit.mk gs 0).wires y).getD wm false := hsort s (s + 1 + i) (by omega) (by omega)
        have hbool : ∀ (bm bL bR : Bool), bm ≤ bL → bR ≤ bm → (!bm && !(bR || (bL && !bm))) = !bL := by
          intro bm bL bR h1 h2
          cases bm <;> cases bL <;> cases bR <;>
            first | decide | (exfalso; exact absurd h1 (by decide)) | (exfalso; exact absurd h2 (by decide))
        exact hbool _ _ _ hm_le hR_le
      · by_cases hi2 : i = s
        · subst hi2
          have hget : (fr.2.1 ++ [nwm] ++ fr.2.2).getD s 0 = nwm := by
            have hl1 : s < (fr.2.1 ++ [nwm]).length := by simp [hlo_l]
            have hl2 : fr.2.1.length ≤ s := by omega
            rw [List.getD, List.getElem?_append_left hl1, List.getElem?_append_right hl2, hlo_l, Nat.sub_self]; rfl
          rw [hget, hgs4, hgs3, hgs2, List.append_assoc, List.append_assoc,
            wires_prefix gs1 _ y 0 nwm (by simp [nwm, gs1, hy])]
          rw [show gs1 = gs ++ [⟨GateOp.not, [wm]⟩] from rfl, wires_snoc]
          have hl0 : ((Circuit.mk gs 0).wires y).length = nwm := by rw [wires_length, hy]
          simp only [List.getD, List.getElem?_append_right (Nat.le_of_eq hl0), hl0, Nat.sub_self,
            List.getElem?_cons_zero, Option.getD_some, GateOp.eval, List.map_cons, List.map_nil,
            List.headD_cons]
          rfl
        · let j := i - (s + 1)
          have hj : j < s := by omega
          have hi_eq : i = s + 1 + j := by omega
          have hget : (fr.2.1 ++ [nwm] ++ fr.2.2).getD i 0 = fr.2.2.getD j 0 := by
            have hl1 : (fr.2.1 ++ [nwm]).length ≤ i := by simp [hlo_l]; omega
            rw [List.getD, List.getElem?_append_right hl1, List.length_append, List.length_singleton, hlo_l]
            rfl
          rw [hget, (hrec2_sem y hy j hj).2, hnz_val j hj, hi_eq]
          have hm_le : ((Circuit.mk gs 0).wires y).getD wm false ≤
              ((Circuit.mk gs 0).wires y).getD (ws.getD j 0) false := hsort j s (by omega) hs_lt
          have hR_le : ((Circuit.mk gs 0).wires y).getD (ws.getD (s + 1 + j) 0) false ≤
              ((Circuit.mk gs 0).wires y).getD wm false := hsort s (s + 1 + j) (by omega) (by omega)
          have hbool : ∀ (bm bL bR : Bool), bm ≤ bL → bR ≤ bm → (!bm || !(bR || (bL && !bm))) = !bR := by
            intro bm bL bR h1 h2
            cases bm <;> cases bL <;> cases bR <;>
              first | decide | (exfalso; exact absurd h1 (by decide)) | (exfalso; exact absurd h2 (by decide))
          exact hbool _ _ _ hm_le hR_le

def compileDualRail (n0 cFalse cTrue : ℕ) (gs : List Gate) (posW negW : List ℕ) :
    List Gate → List Gate × List ℕ × List ℕ
  | [] => (gs, posW, negW)
  | g :: rest =>
    match g.op with
    | GateOp.and =>
      let wPos := n0 + gs.length
      let wNeg := n0 + gs.length + 1
      let gPos : Gate := ⟨GateOp.and, g.inputs.map (fun u => posW.getD u cFalse)⟩
      let gNeg : Gate := ⟨GateOp.or, g.inputs.map (fun u => negW.getD u cTrue)⟩
      compileDualRail n0 cFalse cTrue (gs ++ [gPos, gNeg]) (posW ++ [wPos]) (negW ++ [wNeg]) rest
    | GateOp.or =>
      let wPos := n0 + gs.length
      let wNeg := n0 + gs.length + 1
      let gPos : Gate := ⟨GateOp.or, g.inputs.map (fun u => posW.getD u cFalse)⟩
      let gNeg : Gate := ⟨GateOp.and, g.inputs.map (fun u => negW.getD u cTrue)⟩
      compileDualRail n0 cFalse cTrue (gs ++ [gPos, gNeg]) (posW ++ [wPos]) (negW ++ [wNeg]) rest
    | GateOp.not =>
      match g.inputs with
      | [] => compileDualRail n0 cFalse cTrue gs (posW ++ [cTrue]) (negW ++ [cFalse]) rest
      | u :: _ =>
        compileDualRail n0 cFalse cTrue gs
          (posW ++ [negW.getD u cTrue]) (negW ++ [posW.getD u cFalse]) rest
    | _ => compileDualRail n0 cFalse cTrue gs (posW ++ [cFalse]) (negW ++ [cTrue]) rest

lemma any_not_eq_not_all (l : List ℕ) (f : ℕ → Bool) :
    (l.map (fun u => !(f u))).any id = !((l.map f).all id) := by
  induction l with
  | nil => rfl
  | cons u us ih => cases f u <;> simp [ih]

lemma all_not_eq_not_any (l : List ℕ) (f : ℕ → Bool) :
    (l.map (fun u => !(f u))).all id = !((l.map f).any id) := by
  induction l with
  | nil => rfl
  | cons u us ih => cases f u <;> simp [ih]

lemma compileDualRail_spec (n0 cFalse cTrue : ℕ) (dGates : List Gate) :
    ∀ (gs : List Gate) (posW negW : List ℕ),
    cFalse < n0 + gs.length → cTrue < n0 + gs.length →
    posW.length = negW.length →
    (∀ w ∈ posW, w < n0 + gs.length) →
    (∀ w ∈ negW, w < n0 + gs.length) →
    FanInTwo ⟨dGates, 0⟩ →
    ReadsBack posW.length ⟨dGates, 0⟩ →
    let res := compileDualRail n0 cFalse cTrue gs posW negW dGates
    (∃ ex, res.1 = gs ++ ex ∧ ex.length ≤ 2 * dGates.length ∧
      Monotone2 ⟨ex, 0⟩ ∧ ReadsBack (n0 + gs.length) ⟨ex, 0⟩) ∧
    res.2.1.length = posW.length + dGates.length ∧
    res.2.2.length = negW.length + dGates.length ∧
    (∀ w ∈ res.2.1, w < n0 + res.1.length) ∧
    (∀ w ∈ res.2.2, w < n0 + res.1.length) ∧
    (∀ (y : List Bool) (yD : List Bool),
      y.length = n0 → yD.length = posW.length →
      ((Circuit.mk gs 0).wires y).getD cFalse false = false →
      ((Circuit.mk gs 0).wires y).getD cTrue false = true →
      (∀ i < posW.length,
        ((Circuit.mk gs 0).wires y).getD (posW.getD i cFalse) false = yD.getD i false ∧
        ((Circuit.mk gs 0).wires y).getD (negW.getD i cTrue) false = !(yD.getD i false)) →
      ∀ i < posW.length + dGates.length,
        ((Circuit.mk res.1 0).wires y).getD (res.2.1.getD i cFalse) false =
          ((Circuit.mk dGates 0).wires yD).getD i false ∧
        ((Circuit.mk res.1 0).wires y).getD (res.2.2.getD i cTrue) false =
          !(((Circuit.mk dGates 0).wires yD).getD i false)) := by
  induction dGates with
  | nil =>
    intro gs posW negW _ _ hlen hpos hneg _ _
    refine ⟨⟨[], by simp [compileDualRail], by simp, fun _ h => by simp at h, fun j hj => by simp at hj⟩,
      by simp [compileDualRail], by simp [compileDualRail], hpos, hneg, ?_⟩
    intro y yD _ _ _ _ hin i hi
    simpa [compileDualRail, Circuit.wires] using hin i (by omega)
  | cons g rest ih =>
    intro gs posW negW hcf hct hlen hpos hneg hfit hrb
    have ⟨hg_op, hg_len⟩ := hfit g (List.mem_cons_self ..)
    have hfit_rest : FanInTwo ⟨rest, 0⟩ := fun g' hg' => hfit g' (List.mem_cons_of_mem g hg')
    have hg_rb : ∀ u ∈ g.inputs, u < posW.length := by
      intro u hu
      have := hrb 0 (by simp) u
      simpa [gateAt, List.getD, List.getElem?_cons_zero] using this hu
    have hrb_rest : ReadsBack (posW.length + 1) ⟨rest, 0⟩ := by
      intro j hj u hu
      have := hrb (j + 1) (by simp; omega) u (by simpa [gateAt, List.getD] using hu)
      omega
    have hpos_get : ∀ u < posW.length, posW.getD u cFalse < n0 + gs.length := by
      intro u hu
      have : posW.getD u cFalse = posW[u]'hu := by simp [List.getD, List.getElem?_eq_getElem hu]
      rw [this]; exact hpos _ (List.getElem_mem hu)
    have hneg_get : ∀ u < posW.length, negW.getD u cTrue < n0 + gs.length := by
      intro u hu
      have hu' : u < negW.length := by omega
      have : negW.getD u cTrue = negW[u]'hu' := by simp [List.getD, List.getElem?_eq_getElem hu']
      rw [this]; exact hneg _ (List.getElem_mem hu')
    rcases hg_op with hand | hor | hnot
    ·
      let wPos := n0 + gs.length
      let wNeg := n0 + gs.length + 1
      let gPos : Gate := ⟨GateOp.and, g.inputs.map (fun u => posW.getD u cFalse)⟩
      let gNeg : Gate := ⟨GateOp.or, g.inputs.map (fun u => negW.getD u cTrue)⟩
      let st : List Gate := [gPos, gNeg]
      have hst_mon : Monotone2 ⟨st, 0⟩ := by
        intro x hx; simp only [st, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> simp [gPos, gNeg, hg_len]
      have hst_rb : ReadsBack (n0 + gs.length) ⟨st, 0⟩ := by
        intro j hj u hu
        have : j = 0 ∨ j = 1 := by simp [st] at hj; omega
        rcases this with rfl | rfl
        · simp only [st, gateAt, List.getD_cons_zero, gPos, List.mem_map] at hu
          obtain ⟨v, hv, rfl⟩ := hu; have := hpos_get v (hg_rb v hv); omega
        · simp only [st, gateAt, List.getD_cons_succ, List.getD_cons_zero, gNeg, List.mem_map] at hu
          obtain ⟨v, hv, rfl⟩ := hu; have := hneg_get v (hg_rb v hv); omega
      have hpos1 : ∀ w ∈ posW ++ [wPos], w < n0 + (gs ++ st).length := by
        intro w hw; rcases List.mem_append.mp hw with h | h
        · have := hpos w h; simp [st]; omega
        · simp only [List.mem_singleton] at h; subst h; simp [st, wPos]
      have hneg1 : ∀ w ∈ negW ++ [wNeg], w < n0 + (gs ++ st).length := by
        intro w hw; rcases List.mem_append.mp hw with h | h
        · have := hneg w h; simp [st]; omega
        · simp only [List.mem_singleton] at h; subst h; simp [st, wNeg]; omega
      have hih := ih (gs ++ st) (posW ++ [wPos]) (negW ++ [wNeg])
        (by simp [st]; omega) (by simp [st]; omega) (by simp [hlen])
        hpos1 hneg1 hfit_rest (by simpa using hrb_rest)
      obtain ⟨⟨exR, hgsR, hlenR, hmonR, hrbR⟩, hpl, hnl, hplt, hnlt, hsemR⟩ := hih
      simp only [compileDualRail, hand]
      refine ⟨⟨st ++ exR, by rw [hgsR, List.append_assoc], by simp [st]; omega,
        monotone2_append st exR 0 hst_mon hmonR,
        readsBack_append (n0 + gs.length) st exR 0 hst_rb (by simpa [List.length_append, Nat.add_assoc] using hrbR)⟩,
        by dsimp only [st, gPos, gNeg, wPos, wNeg] at hpl; simp only [List.length_append, List.length_cons, List.length_nil] at hpl ⊢; omega,
        by dsimp only [st, gPos, gNeg, wPos, wNeg] at hnl; simp only [List.length_append, List.length_cons, List.length_nil] at hnl ⊢; omega, hplt, hnlt, ?_⟩
      intro y yD hy hyD hcfv hctv hin i hi
      let yD1 := yD ++ [g.op.eval (g.inputs.map fun u => yD.getD u false)]
      have hcf1 : ((Circuit.mk (gs ++ st) 0).wires y).getD cFalse false = false := by
        rw [wires_prefix gs st y 0 cFalse (by omega)]; exact hcfv
      have hct1 : ((Circuit.mk (gs ++ st) 0).wires y).getD cTrue false = true := by
        rw [wires_prefix gs st y 0 cTrue (by omega)]; exact hctv
      have hin1 : ∀ k < (posW ++ [wPos]).length,
          ((Circuit.mk (gs ++ st) 0).wires y).getD ((posW ++ [wPos]).getD k cFalse) false = yD1.getD k false ∧
          ((Circuit.mk (gs ++ st) 0).wires y).getD ((negW ++ [wNeg]).getD k cTrue) false = !(yD1.getD k false) := by
        intro k hk
        simp only [List.length_append, List.length_singleton] at hk
        by_cases hkp : k < posW.length
        · have hp_k : (posW ++ [wPos]).getD k cFalse = posW.getD k cFalse := by
            simp [List.getD, List.getElem?_append_left hkp]
          have hn_k : (negW ++ [wNeg]).getD k cTrue = negW.getD k cTrue := by
            simp [List.getD, List.getElem?_append_left (by omega : k < negW.length)]
          have hy_k : yD1.getD k false = yD.getD k false := by
            simp [yD1, List.getD, List.getElem?_append_left (by omega : k < yD.length)]
          rw [hp_k, hn_k, hy_k,
            wires_prefix gs st y 0 _ (by have := hpos_get k hkp; omega),
            wires_prefix gs st y 0 _ (by have := hneg_get k hkp; omega)]
          exact hin k hkp
        · have hk_eq : k = posW.length := by omega
          subst hk_eq
          have hp_k : (posW ++ [wPos]).getD posW.length cFalse = wPos := by
            simp [List.getD, List.getElem?_append_right le_rfl]
          have hn_k : (negW ++ [wNeg]).getD posW.length cTrue = wNeg := by
            simp [List.getD, hlen, List.getElem?_append_right le_rfl]
          have hy_k : yD1.getD posW.length false = g.op.eval (g.inputs.map fun u => yD.getD u false) := by
            simp [yD1, List.getD, ← hyD, List.getElem?_append_right le_rfl]
          rw [hp_k, hn_k, hy_k, hand]
          constructor
          · have hst' : gs ++ st = (gs ++ [gPos]) ++ [gNeg] := by simp [st]
            rw [hst', wires_prefix (gs ++ [gPos]) [gNeg] y 0 wPos (by simp [wPos, hy])]
            rw [wires_snoc]
            have hl : ((Circuit.mk gs 0).wires y).length = wPos := by rw [wires_length, hy]
            simp only [List.getD, List.getElem?_append_right (Nat.le_of_eq hl), hl, Nat.sub_self,
              List.getElem?_cons_zero, Option.getD_some, gPos, GateOp.eval, List.map_map]
            congr 1
            apply List.map_congr_left
            intro u hu; exact (hin u (hg_rb u hu)).1
          · have hst' : gs ++ st = (gs ++ [gPos]) ++ [gNeg] := by simp [st]
            have hwn_eq : wNeg = n0 + (gs ++ [gPos]).length := by simp [wNeg]; omega
            rw [hst', hwn_eq, wires_snoc_last n0 (gs ++ [gPos]) gNeg y hy]
            simp only [gNeg, GateOp.eval, List.map_map]
            have hmap : (g.inputs.map (((fun i => ((Circuit.mk (gs ++ [gPos]) 0).wires y).getD i false) ∘ fun u => negW.getD u cTrue))) =
                (g.inputs.map (fun u => !(yD.getD u false))) := by
              apply List.map_congr_left
              intro u hu
              simp only [Function.comp_apply]
              rw [wires_prefix gs [gPos] y 0 _ (by have := hneg_get u (hg_rb u hu); omega)]
              exact (hin u (hg_rb u hu)).2
            rw [hmap]
            exact any_not_eq_not_all g.inputs (fun u => yD.getD u false)
      have hi' : i < (posW ++ [wPos]).length + rest.length := by
        simp only [List.length_append, List.length_singleton, List.length_cons] at hi ⊢; omega
      have hres := hsemR y yD1 hy (by simp [yD1, hyD]) hcf1 hct1 hin1 i hi'
      dsimp only [st, gPos, gNeg, wPos, wNeg] at hres
      simpa [Circuit.wires, yD1, List.foldl_cons] using hres
    ·
      let wPos := n0 + gs.length
      let wNeg := n0 + gs.length + 1
      let gPos : Gate := ⟨GateOp.or, g.inputs.map (fun u => posW.getD u cFalse)⟩
      let gNeg : Gate := ⟨GateOp.and, g.inputs.map (fun u => negW.getD u cTrue)⟩
      let st : List Gate := [gPos, gNeg]
      have hst_mon : Monotone2 ⟨st, 0⟩ := by
        intro x hx; simp only [st, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> simp [gPos, gNeg, hg_len]
      have hst_rb : ReadsBack (n0 + gs.length) ⟨st, 0⟩ := by
        intro j hj u hu
        have : j = 0 ∨ j = 1 := by simp [st] at hj; omega
        rcases this with rfl | rfl
        · simp only [st, gateAt, List.getD_cons_zero, gPos, List.mem_map] at hu
          obtain ⟨v, hv, rfl⟩ := hu; have := hpos_get v (hg_rb v hv); omega
        · simp only [st, gateAt, List.getD_cons_succ, List.getD_cons_zero, gNeg, List.mem_map] at hu
          obtain ⟨v, hv, rfl⟩ := hu; have := hneg_get v (hg_rb v hv); omega
      have hpos1 : ∀ w ∈ posW ++ [wPos], w < n0 + (gs ++ st).length := by
        intro w hw; rcases List.mem_append.mp hw with h | h
        · have := hpos w h; simp [st]; omega
        · simp only [List.mem_singleton] at h; subst h; simp [st, wPos]
      have hneg1 : ∀ w ∈ negW ++ [wNeg], w < n0 + (gs ++ st).length := by
        intro w hw; rcases List.mem_append.mp hw with h | h
        · have := hneg w h; simp [st]; omega
        · simp only [List.mem_singleton] at h; subst h; simp [st, wNeg]; omega
      have hih := ih (gs ++ st) (posW ++ [wPos]) (negW ++ [wNeg])
        (by simp [st]; omega) (by simp [st]; omega) (by simp [hlen])
        hpos1 hneg1 hfit_rest (by simpa using hrb_rest)
      obtain ⟨⟨exR, hgsR, hlenR, hmonR, hrbR⟩, hpl, hnl, hplt, hnlt, hsemR⟩ := hih
      simp only [compileDualRail, hor]
      refine ⟨⟨st ++ exR, by rw [hgsR, List.append_assoc], by simp [st]; omega,
        monotone2_append st exR 0 hst_mon hmonR,
        readsBack_append (n0 + gs.length) st exR 0 hst_rb (by simpa [List.length_append, Nat.add_assoc] using hrbR)⟩,
        by dsimp only [st, gPos, gNeg, wPos, wNeg] at hpl; simp only [List.length_append, List.length_cons, List.length_nil] at hpl ⊢; omega,
        by dsimp only [st, gPos, gNeg, wPos, wNeg] at hnl; simp only [List.length_append, List.length_cons, List.length_nil] at hnl ⊢; omega, hplt, hnlt, ?_⟩
      intro y yD hy hyD hcfv hctv hin i hi
      let yD1 := yD ++ [g.op.eval (g.inputs.map fun u => yD.getD u false)]
      have hcf1 : ((Circuit.mk (gs ++ st) 0).wires y).getD cFalse false = false := by
        rw [wires_prefix gs st y 0 cFalse (by omega)]; exact hcfv
      have hct1 : ((Circuit.mk (gs ++ st) 0).wires y).getD cTrue false = true := by
        rw [wires_prefix gs st y 0 cTrue (by omega)]; exact hctv
      have hin1 : ∀ k < (posW ++ [wPos]).length,
          ((Circuit.mk (gs ++ st) 0).wires y).getD ((posW ++ [wPos]).getD k cFalse) false = yD1.getD k false ∧
          ((Circuit.mk (gs ++ st) 0).wires y).getD ((negW ++ [wNeg]).getD k cTrue) false = !(yD1.getD k false) := by
        intro k hk
        simp only [List.length_append, List.length_singleton] at hk
        by_cases hkp : k < posW.length
        · have hp_k : (posW ++ [wPos]).getD k cFalse = posW.getD k cFalse := by
            simp [List.getD, List.getElem?_append_left hkp]
          have hn_k : (negW ++ [wNeg]).getD k cTrue = negW.getD k cTrue := by
            simp [List.getD, List.getElem?_append_left (by omega : k < negW.length)]
          have hy_k : yD1.getD k false = yD.getD k false := by
            simp [yD1, List.getD, List.getElem?_append_left (by omega : k < yD.length)]
          rw [hp_k, hn_k, hy_k,
            wires_prefix gs st y 0 _ (by have := hpos_get k hkp; omega),
            wires_prefix gs st y 0 _ (by have := hneg_get k hkp; omega)]
          exact hin k hkp
        · have hk_eq : k = posW.length := by omega
          subst hk_eq
          have hp_k : (posW ++ [wPos]).getD posW.length cFalse = wPos := by
            simp [List.getD, List.getElem?_append_right le_rfl]
          have hn_k : (negW ++ [wNeg]).getD posW.length cTrue = wNeg := by
            simp [List.getD, hlen, List.getElem?_append_right le_rfl]
          have hy_k : yD1.getD posW.length false = g.op.eval (g.inputs.map fun u => yD.getD u false) := by
            simp [yD1, List.getD, ← hyD, List.getElem?_append_right le_rfl]
          rw [hp_k, hn_k, hy_k, hor]
          constructor
          · have hst' : gs ++ st = (gs ++ [gPos]) ++ [gNeg] := by simp [st]
            rw [hst', wires_prefix (gs ++ [gPos]) [gNeg] y 0 wPos (by simp [wPos, hy])]
            rw [wires_snoc]
            have hl : ((Circuit.mk gs 0).wires y).length = wPos := by rw [wires_length, hy]
            simp only [List.getD, List.getElem?_append_right (Nat.le_of_eq hl), hl, Nat.sub_self,
              List.getElem?_cons_zero, Option.getD_some, gPos, GateOp.eval, List.map_map]
            congr 1
            apply List.map_congr_left
            intro u hu; exact (hin u (hg_rb u hu)).1
          · have hst' : gs ++ st = (gs ++ [gPos]) ++ [gNeg] := by simp [st]
            have hwn_eq : wNeg = n0 + (gs ++ [gPos]).length := by simp [wNeg]; omega
            rw [hst', hwn_eq, wires_snoc_last n0 (gs ++ [gPos]) gNeg y hy]
            simp only [gNeg, GateOp.eval, List.map_map]
            have hmap : (g.inputs.map (((fun i => ((Circuit.mk (gs ++ [gPos]) 0).wires y).getD i false) ∘ fun u => negW.getD u cTrue))) =
                (g.inputs.map (fun u => !(yD.getD u false))) := by
              apply List.map_congr_left
              intro u hu
              simp only [Function.comp_apply]
              rw [wires_prefix gs [gPos] y 0 _ (by have := hneg_get u (hg_rb u hu); omega)]
              exact (hin u (hg_rb u hu)).2
            rw [hmap]
            exact all_not_eq_not_any g.inputs (fun u => yD.getD u false)
      have hi' : i < (posW ++ [wPos]).length + rest.length := by
        simp only [List.length_append, List.length_singleton, List.length_cons] at hi ⊢; omega
      have hres := hsemR y yD1 hy (by simp [yD1, hyD]) hcf1 hct1 hin1 i hi'
      dsimp only [st, gPos, gNeg, wPos, wNeg] at hres
      simpa [Circuit.wires, yD1, List.foldl_cons] using hres
    ·
      simp only [Set.mem_singleton_iff] at hnot
      cases hins : g.inputs with
      | nil =>
        have hpos1 : ∀ w ∈ posW ++ [cTrue], w < n0 + gs.length := by
          intro w hw; rcases List.mem_append.mp hw with h | h
          · exact hpos w h
          · simp only [List.mem_singleton] at h; subst h; exact hct
        have hneg1 : ∀ w ∈ negW ++ [cFalse], w < n0 + gs.length := by
          intro w hw; rcases List.mem_append.mp hw with h | h
          · exact hneg w h
          · simp only [List.mem_singleton] at h; subst h; exact hcf
        have hih := ih gs (posW ++ [cTrue]) (negW ++ [cFalse]) hcf hct (by simp [hlen])
          hpos1 hneg1 hfit_rest (by simpa using hrb_rest)
        obtain ⟨⟨exR, hgsR, hlenR, hmonR, hrbR⟩, hpl, hnl, hplt, hnlt, hsemR⟩ := hih
        simp only [compileDualRail, hnot, hins]
        refine ⟨⟨exR, hgsR, by simp only [List.length_cons]; omega, hmonR, hrbR⟩,
          by rw [hpl]; simp only [List.length_append, List.length_cons, List.length_nil]; omega,
          by rw [hnl]; simp only [List.length_append, List.length_cons, List.length_nil]; omega, hplt, hnlt, ?_⟩
        intro y yD hy hyD hcfv hctv hin i hi
        let yD1 := yD ++ [true]
        have hin1 : ∀ k < (posW ++ [cTrue]).length,
            ((Circuit.mk gs 0).wires y).getD ((posW ++ [cTrue]).getD k cFalse) false = yD1.getD k false ∧
            ((Circuit.mk gs 0).wires y).getD ((negW ++ [cFalse]).getD k cTrue) false = !(yD1.getD k false) := by
          intro k hk
          simp only [List.length_append, List.length_singleton] at hk
          by_cases hkp : k < posW.length
          · simp [List.getD, List.getElem?_append_left hkp, List.getElem?_append_left (by omega : k < negW.length),
              yD1, List.getElem?_append_left (by omega : k < yD.length)]
            exact hin k hkp
          · have hk_eq : k = posW.length := by omega
            subst hk_eq
            have hp1 : (posW ++ [cTrue]).getD posW.length cFalse = cTrue := by
              rw [List.getD, List.getElem?_append_right le_rfl, Nat.sub_self]; rfl
            have hn1 : (negW ++ [cFalse]).getD posW.length cTrue = cFalse := by
              rw [List.getD, hlen, List.getElem?_append_right le_rfl, Nat.sub_self]; rfl
            have hy1 : yD1.getD posW.length false = true := by
              rw [List.getD, show yD1 = yD ++ [true] from rfl, ← hyD, List.getElem?_append_right le_rfl, Nat.sub_self]; rfl
            rw [hp1, hn1, hy1, hctv, hcfv]; simp
        have hi' : i < (posW ++ [cTrue]).length + rest.length := by
          simp only [List.length_append, List.length_singleton, List.length_cons] at hi ⊢; omega
        have hres := hsemR y yD1 hy (by simp [yD1, hyD]) hcfv hctv hin1 i hi'
        simpa [Circuit.wires, yD1, List.foldl_cons, hnot, hins, GateOp.eval] using hres
      | cons u us =>
        have hu_lt : u < posW.length := hg_rb u (by rw [hins]; simp)
        have hpos1 : ∀ w ∈ posW ++ [negW.getD u cTrue], w < n0 + gs.length := by
          intro w hw; rcases List.mem_append.mp hw with h | h
          · exact hpos w h
          · simp only [List.mem_singleton] at h; subst h; exact hneg_get u hu_lt
        have hneg1 : ∀ w ∈ negW ++ [posW.getD u cFalse], w < n0 + gs.length := by
          intro w hw; rcases List.mem_append.mp hw with h | h
          · exact hneg w h
          · simp only [List.mem_singleton] at h; subst h; exact hpos_get u hu_lt
        have hih := ih gs (posW ++ [negW.getD u cTrue]) (negW ++ [posW.getD u cFalse]) hcf hct (by simp [hlen])
          hpos1 hneg1 hfit_rest (by simpa using hrb_rest)
        obtain ⟨⟨exR, hgsR, hlenR, hmonR, hrbR⟩, hpl, hnl, hplt, hnlt, hsemR⟩ := hih
        simp only [compileDualRail, hnot, hins]
        refine ⟨⟨exR, hgsR, by simp only [List.length_cons]; omega, hmonR, hrbR⟩,
          by rw [hpl]; simp only [List.length_append, List.length_cons, List.length_nil]; omega,
          by rw [hnl]; simp only [List.length_append, List.length_cons, List.length_nil]; omega, hplt, hnlt, ?_⟩
        intro y yD hy hyD hcfv hctv hin i hi
        let yD1 := yD ++ [!(yD.getD u false)]
        have hin1 : ∀ k < (posW ++ [negW.getD u cTrue]).length,
            ((Circuit.mk gs 0).wires y).getD ((posW ++ [negW.getD u cTrue]).getD k cFalse) false = yD1.getD k false ∧
            ((Circuit.mk gs 0).wires y).getD ((negW ++ [posW.getD u cFalse]).getD k cTrue) false = !(yD1.getD k false) := by
          intro k hk
          simp only [List.length_append, List.length_singleton] at hk
          by_cases hkp : k < posW.length
          · simp [List.getD, List.getElem?_append_left hkp, List.getElem?_append_left (by omega : k < negW.length),
              yD1, List.getElem?_append_left (by omega : k < yD.length)]
            exact hin k hkp
          · have hk_eq : k = posW.length := by omega
            subst hk_eq
            have ⟨hp_u, hn_u⟩ := hin u hu_lt
            have hp1 : (posW ++ [negW.getD u cTrue]).getD posW.length cFalse = negW.getD u cTrue := by
              rw [List.getD, List.getElem?_append_right le_rfl, Nat.sub_self]; rfl
            have hn1 : (negW ++ [posW.getD u cFalse]).getD posW.length cTrue = posW.getD u cFalse := by
              rw [List.getD, hlen, List.getElem?_append_right le_rfl, Nat.sub_self]; rfl
            have hy1 : yD1.getD posW.length false = !(yD.getD u false) := by
              rw [List.getD, show yD1 = yD ++ [!(yD.getD u false)] from rfl, ← hyD, List.getElem?_append_right le_rfl, Nat.sub_self]; rfl
            rw [hp1, hn1, hy1, hp_u, hn_u]; simp
        have hi' : i < (posW ++ [negW.getD u cTrue]).length + rest.length := by
          simp only [List.length_append, List.length_singleton, List.length_cons] at hi ⊢; omega
        have hres := hsemR y yD1 hy (by simp [yD1, hyD]) hcfv hctv hin1 i hi'
        simpa [Circuit.wires, yD1, List.foldl_cons, hnot, hins, GateOp.eval] using hres

def embedGate (n m : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (fun w => if w < n then w else w + m)⟩

def embedMono (n m : ℕ) (D : Circuit) : Circuit :=
  ⟨D.gates.map (embedGate n m), if D.output < n then D.output else D.output + m⟩

lemma embedMono_readsBack (n m : ℕ) (D : Circuit) (hrb : ReadsBack (n + 2) D) :
    ReadsBack (n + m + 2) (embedMono n m D) := by
  intro j hj i hi
  simp only [embedMono, List.length_map] at hj
  simp only [embedMono, gateAt, List.getD, List.getElem?_map, List.getElem?_eq_getElem hj,
    Option.map_some, Option.getD_some, embedGate, List.mem_map] at hi
  obtain ⟨u, hu, rfl⟩ := hi
  have := hrb j hj u (by simpa [gateAt, List.getD, List.getElem?_eq_getElem hj] using hu)
  split_ifs <;> omega

lemma embedMono_monotone2 (n m : ℕ) (D : Circuit) (hm : Monotone2 D) :
    Monotone2 (embedMono n m D) := by
  intro g hg
  simp only [embedMono, List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  have ⟨hop, hlen⟩ := hm g0 hg0
  exact ⟨hop, by simpa [embedGate] using hlen⟩

lemma embedMono_wires (n m : ℕ) (D : Circuit) (hrb : ReadsBack (n + 2) D)
    (xBits : List Bool) (hx : xBits.length = n) (zBits : List Bool) (hz : zBits.length = m) :
    ∀ w < n + 2 + D.gates.length,
      ((embedMono n m D).wires (xBits ++ zBits ++ [false, true])).getD
        (if w < n then w else w + m) false =
      (D.wires (xBits ++ [false, true])).getD w false := by
  intro w hw
  let yC := xBits ++ zBits ++ [false, true]
  let yD := xBits ++ [false, true]
  have hyC : yC.length = n + m + 2 := by simp [yC, hx, hz]; omega
  have hyD : yD.length = n + 2 := by simp [yD, hx]
  have hrbE : ReadsBack (n + m + 2) (embedMono n m D) := embedMono_readsBack n m D hrb
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hwn : w < n
    · simp only [hwn, ↓reduceIte]
      rw [wires_get_input _ yC w (by omega), wires_get_input _ yD w (by omega)]
      simp [yC, yD, List.getD, List.append_assoc, List.getElem?_append_left (by omega : w < xBits.length)]
    · simp only [hwn, ↓reduceIte]
      by_cases hw2 : w < n + 2
      · rw [wires_get_input _ yC (w + m) (by omega), wires_get_input _ yD w (by omega)]
        simp only [yC, yD, List.getD]
        rw [List.getElem?_append_right (by simp [hx, hz]; omega)]
        rw [List.getElem?_append_right (by omega : xBits.length ≤ w)]
        simp [hx, hz, show w + m - (n + m) = w - n by omega]
      · let j := w - (n + 2)
        have hj : j < D.gates.length := by omega
        have hw_eq : w = (n + 2) + j := by omega
        have hwm_eq : w + m = (n + m + 2) + j := by omega
        rw [hwm_eq, ← hyC, wires_get_gate_rb (embedMono n m D) yC j (by simpa [embedMono] using hj) (by rwa [hyC])]
        rw [hw_eq, ← hyD, wires_get_gate_rb D yD j hj (by rwa [hyD])]
        simp only [embedMono, List.getElem_map, embedGate, List.map_map]
        congr 1
        apply List.map_congr_left
        intro u hu
        have hu_lt : u < n + 2 + j := by
          have h1 := hrb j hj u
          simp only [gateAt, List.getD, List.getElem?_eq_getElem hj, Option.getD_some] at h1
          exact h1 hu
        exact ih u (by omega) (by omega)

def compileOrChain (n0 cFalse : ℕ) (gs : List Gate) : List ℕ → List Gate × ℕ
  | [] => (gs, cFalse)
  | [w] => (gs, w)
  | w :: ws =>
    let res1 := compileOrChain n0 cFalse gs ws
    let gs1 := res1.1
    let wRest := res1.2
    let wOut := n0 + gs1.length
    (gs1 ++ [⟨GateOp.or, [w, wRest]⟩], wOut)

lemma compileOrChain_spec (n0 cFalse : ℕ) (ws : List ℕ) :
    ∀ (gs : List Gate),
    cFalse < n0 + gs.length →
    (∀ w ∈ ws, w < n0 + gs.length) →
    let res := compileOrChain n0 cFalse gs ws
    (∃ ex, res.1 = gs ++ ex ∧ ex.length ≤ ws.length ∧
      Monotone2 ⟨ex, 0⟩ ∧ ReadsBack (n0 + gs.length) ⟨ex, 0⟩) ∧
    res.2 < n0 + res.1.length ∧
    (∀ y : List Bool, y.length = n0 →
      ((Circuit.mk gs 0).wires y).getD cFalse false = false →
      ((Circuit.mk res.1 0).wires y).getD res.2 false =
        ws.any (fun w => ((Circuit.mk gs 0).wires y).getD w false)) := by
  induction ws with
  | nil =>
    intro gs hcf _
    refine ⟨⟨[], by simp [compileOrChain], by simp, fun _ h => by simp at h, fun j hj => by simp at hj⟩,
      hcf, fun y _ hcfv => by simpa [compileOrChain] using hcfv⟩
  | cons w ws ih =>
    intro gs hcf hws
    cases ws with
    | nil =>
      refine ⟨⟨[], by simp [compileOrChain], by simp, fun _ h => by simp at h, fun j hj => by simp at hj⟩,
        hws w (List.mem_cons_self ..), fun y _ _ => by simp [compileOrChain]⟩
    | cons w2 ws' =>
      have hw : w < n0 + gs.length := hws w (List.mem_cons_self ..)
      have hws' : ∀ u ∈ w2 :: ws', u < n0 + gs.length := fun u hu => hws u (List.mem_cons_of_mem w hu)
      have ⟨⟨ex1, hgs1, hlen1, hmon1, hrb1⟩, hout1, hsem1⟩ := ih gs hcf hws'
      let res1 := compileOrChain n0 cFalse gs (w2 :: ws')
      have hw_lt1 : w < n0 + res1.1.length := by rw [hgs1]; simp; omega
      let gOr : Gate := ⟨GateOp.or, [w, res1.2]⟩
      have hgOr_mon : Monotone2 ⟨[gOr], 0⟩ := by
        intro x hx; simp only [List.mem_singleton] at hx; subst hx; simp [gOr]
      have hgOr_rb : ReadsBack (n0 + res1.1.length) ⟨[gOr], 0⟩ := by
        intro j hj u hu
        have hj0 : j = 0 := by simp at hj; omega
        subst hj0; simp only [gateAt, List.getD, List.getElem?_cons_zero, Option.getD_some, gOr,
          List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl <;> omega
      simp only [compileOrChain]
      refine ⟨⟨ex1 ++ [gOr], by rw [hgs1, List.append_assoc], by simp; omega,
        monotone2_append ex1 [gOr] 0 hmon1 hgOr_mon,
        readsBack_append (n0 + gs.length) ex1 [gOr] 0 hrb1 (by
          have : n0 + gs.length + ex1.length = n0 + res1.1.length := by rw [hgs1, List.length_append]; omega
          rw [this]; exact hgOr_rb)⟩,
        by simp, ?_⟩
      intro y hy hcfv
      change ((Circuit.mk (res1.1 ++ [gOr]) 0).wires y).getD (n0 + res1.1.length) false = _
      rw [wires_snoc_last n0 res1.1 gOr y hy]
      simp only [gOr, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
      rw [hgs1, wires_prefix gs ex1 y 0 w (by omega), ← hgs1, hsem1 y hy hcfv]
      simp only [List.any_cons]

end PEqualNP.Outside.L_lib_1280_aux

set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.L_lib_1280 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (a n : Nat),
  let h := 2^a
  let b := a+1
  let r := 2*h-1
  let k := 2*(h-1)
  let m := 2*k
  n ≤ 2*h → ∀ f : Finset (Fin n) → Bool, Monotone f →
    f ∅ = false → f Finset.univ = true →
  let bits := fun (l : Nat) (x : Finset (Fin l)) => List.ofFn (fun i : Fin l => decide (i ∈ x))
  let valid := fun (l : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (l+2) C ∧ C.output < l+2+C.size
  let source := fun (D : PEqualNP.CircuitLowerBounds.Circuit) =>
    valid n D ∧ ∀ x, D.eval (bits n x ++ [false,true]) = f x
  let target := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    valid (n+m) C ∧ ∀ x z,
      C.eval (bits n x ++ bits m z ++ [false,true]) =
        (if z.card < k then decide (z.card % 2 = 0)
         else if z.card = k then !(f x) else decide (z.card % 2 = 1))
  let K := 96*(n+m+2)*(Nat.log2 (n+m+2)+2)^2
  (∀ C, target C → b ≤ PEqualNP.NotBracket.notCount C ∧
    (∃ D, source D ∧ D.size ≤ C.size+1) ∧
    (PEqualNP.NotBracket.notCount C = b →
      ∃ D, source D ∧ PEqualNP.MetaComplexity.Monotone2 D ∧ D.size < C.size)) ∧
  ∀ D, source D →
    (PEqualNP.MetaComplexity.Monotone2 D → ∃ C, target C ∧
      PEqualNP.NotBracket.notCount C = b ∧ C.size ≤ D.size + K) ∧
    ∃ C, target C ∧ PEqualNP.NotBracket.notCount C = b+1 ∧ C.size ≤ 2*D.size + K) := by
  classical
  open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
    PEqualNP.NotBracket PEqualNP.Outside.L_lib_1280_aux in
  intro a n h b r k m hn f hf_mono hf0 hf1 bits valid source target K
  have hh_pos : 1 ≤ h := Nat.one_le_two_pow
  have hbits_len : ∀ l (x : Finset (Fin l)), (bits l x).length = l := by
    intro l x; simp [bits]
  have hbits_get : ∀ l (x : Finset (Fin l)) (i : ℕ) (hi : i < l),
      (bits l x).getD i false = @decide (⟨i, hi⟩ ∈ x) (Classical.propDecidable _) := by
    intro l x i hi
    simp [bits, List.getD, hi]
  have hbits_get_iff : ∀ l (x : Finset (Fin l)) (i : ℕ) (hi : i < l),
      (bits l x).getD i false = true ↔ (⟨i, hi⟩ : Fin l) ∈ x := by
    intro l x i hi
    rw [hbits_get l x i hi]
    exact @decide_eq_true_iff _ (Classical.propDecidable _)
  have hbits_mono : ∀ l {x y : Finset (Fin l)}, x ⊆ y →
      ∀ i < l, (bits l x).getD i false ≤ (bits l y).getD i false := by
    intro l x y hxy i hi
    cases hx : (bits l x).getD i false
    · exact Bool.false_le _
    · have hmem : (⟨i, hi⟩ : Fin l) ∈ x := (hbits_get_iff l x i hi).mp hx
      have hy : (bits l y).getD i false = true := (hbits_get_iff l y i hi).mpr (hxy hmem)
      rw [hy]
  have hbits_count : ∀ l (x : Finset (Fin l)), (bits l x).count true = x.card := by
    intro l x
    have h1 : (bits l x).count true =
        ((Finset.univ : Finset (Fin l)).filter (fun i : Fin l => i ∈ x)).card := by
      have haux : ∀ (l' : ℕ) (g : Fin l' → Bool),
          (List.ofFn g).count true = ((Finset.univ : Finset (Fin l')).filter (fun i => g i = true)).card := by
        intro l'
        induction l' with
        | zero => intro g; simp
        | succ l ih =>
          intro g
          rw [List.ofFn_succ, List.count_cons, ih (fun i => g i.succ)]
          have hcard : ((Finset.univ : Finset (Fin (l + 1))).filter (fun i => g i = true)).card =
              (if g 0 = true then 1 else 0) +
                ((Finset.univ : Finset (Fin l)).filter (fun i => g i.succ = true)).card := by
            let s0 : Finset (Fin (l + 1)) := if g 0 = true then {0} else ∅
            let s1 : Finset (Fin (l + 1)) :=
              ((Finset.univ : Finset (Fin l)).filter (fun i => g i.succ = true)).map
                ⟨Fin.succ, Fin.succ_injective l⟩
            have hu : (Finset.univ : Finset (Fin (l + 1))).filter (fun i => g i = true) = s0 ∪ s1 := by
              ext i; simp only [s0, s1, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
                Finset.mem_map, Function.Embedding.coeFn_mk]
              refine Fin.cases ?_ ?_ i
              · cases hg : g 0 <;> simp [hg]
              · intro j
                have hne : j.succ ≠ 0 := Fin.succ_ne_zero j
                cases hg : g 0 <;> simp [hg, hne]
            have hd : Disjoint s0 s1 := by
              rw [Finset.disjoint_left]; intro i hi1 hi2
              simp only [s1, Finset.mem_map, Function.Embedding.coeFn_mk] at hi2
              obtain ⟨j, _, rfl⟩ := hi2
              cases hg : g 0 <;> simp [s0, hg, Fin.succ_ne_zero] at hi1
            rw [hu, Finset.card_union_of_disjoint hd, Finset.card_map]
            cases hg : g 0 <;> simp [s0, hg]
          rw [hcard]; cases g 0 <;> simp <;> omega
      rw [show bits l x = List.ofFn (fun i : Fin l => @decide (i ∈ x) (Classical.propDecidable _)) from rfl, haux l]
      congr 1; ext i; simp [@decide_eq_true_iff _ (Classical.propDecidable _)]
    rw [h1]
    congr 1; ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hn_pos : 1 ≤ n := by
    by_contra h0
    have hn0 : n = 0 := by omega
    subst hn0
    have heq : (∅ : Finset (Fin 0)) = Finset.univ := by ext i; exact i.elim0
    rw [heq] at hf0
    rw [hf0] at hf1; exact Bool.false_ne_true hf1

  let zSet : ℕ → Finset (Fin m) := fun j => Finset.univ.filter (fun i : Fin m => i.val < j)
  have hzSet_card : ∀ j ≤ m, (zSet j).card = j := by
    intro j hj
    have hbij : (zSet j).card = (Finset.univ : Finset (Fin j)).card := by
      symm
      apply Finset.card_bij (fun i _ => (⟨i.val, by omega⟩ : Fin m))
      · intro i _; simp [zSet]
      · intro i1 _ i2 _ heq; exact Fin.ext (by simpa using congrArg Fin.val heq)
      · intro y hy
        simp only [zSet, Finset.mem_filter, Finset.mem_univ, true_and] at hy
        exact ⟨⟨y.val, hy⟩, Finset.mem_univ _, Fin.ext rfl⟩
    rw [hbij, Finset.card_fin]
  have hzSet_mono : ∀ {j1 j2 : ℕ}, j1 ≤ j2 → zSet j1 ⊆ zSet j2 := by
    intro j1 j2 h12 i hi
    simp only [zSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    omega
  constructor
  ·
    intro C ⟨⟨hfit, hrb, hout⟩, heval⟩
    let yOf : Finset (Fin n) → Finset (Fin m) → List Bool := fun x z =>
      bits n x ++ bits m z ++ [false, true]
    have hyOf_len : ∀ x z, (yOf x z).length = n + m + 2 := by
      intro x z; simp [yOf, hbits_len]; omega
    have hyOf_mono : ∀ {x1 x2 : Finset (Fin n)} {z1 z2 : Finset (Fin m)},
        x1 ⊆ x2 → z1 ⊆ z2 →
        ∀ i < n + m + 2, (yOf x1 z1).getD i false ≤ (yOf x2 z2).getD i false := by
      intro x1 x2 z1 z2 hx hz i hi
      by_cases h1 : i < n
      · have g1 : (yOf x1 z1).getD i false = (bits n x1).getD i false := by
          simp only [yOf, List.getD, List.append_assoc]
          rw [List.getElem?_append_left (by rw [hbits_len]; exact h1)]
        have g2 : (yOf x2 z2).getD i false = (bits n x2).getD i false := by
          simp only [yOf, List.getD, List.append_assoc]
          rw [List.getElem?_append_left (by rw [hbits_len]; exact h1)]
        rw [g1, g2]; exact hbits_mono n hx i h1
      · by_cases h2 : i < n + m
        · have g1 : (yOf x1 z1).getD i false = (bits m z1).getD (i - n) false := by
            simp only [yOf, List.getD]
            rw [List.getElem?_append_left (by simp [hbits_len]; omega)]
            rw [List.getElem?_append_right (by rw [hbits_len]; omega), hbits_len]
          have g2 : (yOf x2 z2).getD i false = (bits m z2).getD (i - n) false := by
            simp only [yOf, List.getD]
            rw [List.getElem?_append_left (by simp [hbits_len]; omega)]
            rw [List.getElem?_append_right (by rw [hbits_len]; omega), hbits_len]
          rw [g1, g2]; exact hbits_mono m hz (i - n) (by omega)
        · have g1 : (yOf x1 z1).getD i false = [false, true].getD (i - (n + m)) false := by
            simp only [yOf, List.getD]
            rw [List.getElem?_append_right (by simp [hbits_len]; omega)]
            simp [hbits_len]
          have g2 : (yOf x2 z2).getD i false = [false, true].getD (i - (n + m)) false := by
            simp only [yOf, List.getD]
            rw [List.getElem?_append_right (by simp [hbits_len]; omega)]
            simp [hbits_len]
          rw [g1, g2]
    have hrk_le : ∀ {x1 x2 : Finset (Fin n)} {z1 z2 : Finset (Fin m)},
        x1 ⊆ x2 → z1 ⊆ z2 →
        notRank (n + m + 2) C (yOf x2 z2) ≤ notRank (n + m + 2) C (yOf x1 z1) := by
      intro x1 x2 z1 z2 hx hz
      exact (markov_step (n + m + 2) C (yOf x1 z1) (yOf x2 z2) hfit hrb hout
        (hyOf_len x1 z1) (hyOf_len x2 z2) (hyOf_mono hx hz)).1
    have hrk_fall : ∀ {x1 x2 : Finset (Fin n)} {z1 z2 : Finset (Fin m)},
        x1 ⊆ x2 → z1 ⊆ z2 → C.eval (yOf x1 z1) = true → C.eval (yOf x2 z2) = false →
        notRank (n + m + 2) C (yOf x2 z2) + 1 ≤ notRank (n + m + 2) C (yOf x1 z1) := by
      intro x1 x2 z1 z2 hx hz h1 h2
      have hms := markov_step (n + m + 2) C (yOf x1 z1) (yOf x2 z2) hfit hrb hout
        (hyOf_len x1 z1) (hyOf_len x2 z2) (hyOf_mono hx hz)
      have hne : notRank (n + m + 2) C (yOf x2 z2) ≠ notRank (n + m + 2) C (yOf x1 z1) := by
        intro heq; have hle := hms.2 heq; rw [h1, h2] at hle; exact absurd hle (by decide)
      omega

    have hpre_drop : ∀ t ≤ h - 1,
        notRank (n + m + 2) C (yOf ∅ (zSet (2 * t))) + t ≤ 2 ^ notCount C - 1 := by
      intro t ht
      induction t with
      | zero =>
        have hlt := notRank_lt (n + m + 2) C (yOf ∅ (zSet 0))
        simp only [Nat.mul_zero, Nat.add_zero]
        omega
      | succ t ih =>
        have h1 := ih (by omega)
        have he1 : C.eval (yOf ∅ (zSet (2 * t))) = true := by
          rw [heval, hzSet_card (2 * t) (by omega)]
          have hlt : 2 * t < k := by omega
          simp [hlt]
        have he2 : C.eval (yOf ∅ (zSet (2 * t + 1))) = false := by
          rw [heval, hzSet_card (2 * t + 1) (by omega)]
          have hlt : 2 * t + 1 < k := by omega
          simp [hlt]
        have hfall := hrk_fall (Finset.Subset.refl ∅) (hzSet_mono (by omega : 2 * t ≤ 2 * t + 1)) he1 he2
        have hle := hrk_le (Finset.Subset.refl ∅) (hzSet_mono (by omega : 2 * t + 1 ≤ 2 * (t + 1)))
        omega

    have hpost_drop : ∀ t ≤ h - 1,
        t ≤ notRank (n + m + 2) C (yOf Finset.univ (zSet (m - 2 * t))) := by
      intro t ht
      induction t with
      | zero => exact Nat.zero_le _
      | succ t ih =>
        have h1 := ih (by omega)
        have he1 : C.eval (yOf Finset.univ (zSet (m - 2 * t - 1))) = true := by
          rw [heval, hzSet_card (m - 2 * t - 1) (by omega)]
          have hgt : ¬(m - 2 * t - 1 < k) := by omega
          have hne : m - 2 * t - 1 ≠ k := by omega
          simp [hgt, hne]; omega
        have he2 : C.eval (yOf Finset.univ (zSet (m - 2 * t))) = false := by
          rw [heval, hzSet_card (m - 2 * t) (by omega)]
          have hgt : ¬(m - 2 * t < k) := by omega
          have hne : m - 2 * t ≠ k := by omega
          simp [hgt, hne]; omega
        have hfall := hrk_fall (Finset.Subset.refl Finset.univ) (hzSet_mono (by omega : m - 2 * t - 1 ≤ m - 2 * t)) he1 he2
        have hle := hrk_le (Finset.Subset.refl Finset.univ) (hzSet_mono (by omega : m - 2 * (t + 1) ≤ m - 2 * t - 1))
        omega
    have hpre_k : notRank (n + m + 2) C (yOf ∅ (zSet k)) + (h - 1) ≤ 2 ^ notCount C - 1 := by
      have := hpre_drop (h - 1) le_rfl
      simpa [k] using this
    have hpost_k : h - 1 ≤ notRank (n + m + 2) C (yOf Finset.univ (zSet k)) := by
      have := hpost_drop (h - 1) le_rfl
      have hm_eq : m - 2 * (h - 1) = k := by omega
      simpa [hm_eq] using this
    have hmid_fall : notRank (n + m + 2) C (yOf Finset.univ (zSet k)) + 1 ≤
        notRank (n + m + 2) C (yOf ∅ (zSet k)) := by
      apply hrk_fall (Finset.empty_subset _) (Finset.Subset.refl _)
      · rw [heval, hzSet_card k (by omega)]; simp [hf0]
      · rw [heval, hzSet_card k (by omega)]; simp [hf1]
    have hpow_ge : 2 ^ b ≤ 2 ^ notCount C := by
      have h2b : 2 ^ b = 2 * h := by simp [b, h, Nat.pow_succ, mul_comm]
      have h1 : 1 ≤ 2 ^ notCount C := Nat.one_le_two_pow
      omega
    have hb_le : b ≤ notCount C := (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hpow_ge
    refine ⟨hb_le, ?_, ?_⟩
    ·
      let D0 := hardwirePrefix n m (zSet k) C C.size C.output
      let D : Circuit := ⟨D0.gates ++ [⟨GateOp.not, [D0.output]⟩], n + 2 + D0.size⟩
      have hD0_len : D0.size = C.size := by simp [D0, hardwirePrefix, Circuit.size]
      have hD0_out : D0.output < n + 2 + D0.size := by
        rw [hD0_len]; exact remapWire_lt n m (zSet k) C.size C.output hout
      refine ⟨D, ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩
      · apply fanInTwo_append D0.gates [⟨GateOp.not, [D0.output]⟩] _
          (hardwirePrefix_fanInTwo n m (zSet k) C C.size C.output hfit)
        intro g hg; simp only [List.mem_singleton] at hg; subst hg; simp
      · exact readsBack_snoc (n + 2) D0.gates ⟨GateOp.not, [D0.output]⟩ _
          (hardwirePrefix_readsBack n m (zSet k) C C.size C.output hrb)
          (fun i hi => by simp only [List.mem_singleton] at hi; subst hi; exact hD0_out)
      · simp [D, Circuit.size]
      · intro x
        have hyD_len : (bits n x ++ [false, true]).length = n + 2 := by simp [hbits_len]
        have hD_eval : D.eval (bits n x ++ [false, true]) =
            !((D0.wires (bits n x ++ [false, true])).getD D0.output false) := by
          change ((Circuit.mk (D0.gates ++ [Gate.mk GateOp.not [D0.output]]) 0).wires (bits n x ++ [false, true])).getD (n + 2 + D0.gates.length) false = _
          rw [wires_snoc_last (n + 2) D0.gates (Gate.mk GateOp.not [D0.output]) (bits n x ++ [false, true]) hyD_len]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons]; rfl
        rw [hD_eval]
        have hhw := hardwirePrefix_wires n m (zSet k) C C.size C.output le_rfl hrb
          (bits n x) (hbits_len n x) (bits m (zSet k)) (hbits_len m (zSet k))
          (fun i => by
            have hiff := hbits_get_iff m (zSet k) i.val i.isLt
            simp only [Fin.eta] at hiff
            cases hb : (bits m (zSet k)).getD i.val false
            · have hni : i ∉ zSet k := fun hmem => by have h1 := hiff.mpr hmem; rw [hb] at h1; exact Bool.false_ne_true h1
              exact (decide_eq_false hni).symm
            · have hi : i ∈ zSet k := hiff.mp hb
              exact (decide_eq_true hi).symm)
          C.output hout
        change (!((D0.wires (bits n x ++ [false, true])).getD (remapWire n m (zSet k) C.output) false)) = f x
        rw [hhw]
        change (!(C.eval (yOf x (zSet k)))) = f x
        rw [heval, hzSet_card k (by omega)]
        simp
      · simp only [D, Circuit.size, List.length_append, List.length_singleton]
        have : D0.gates.length = C.gates.length := hD0_len
        omega
    ·
      intro hnc
      have hni_len : (notIndices C.gates).length = b := by rw [notIndices_length, hnc]
      have hni_pos : 0 < (notIndices C.gates).length := by omega
      let j0 := (notIndices C.gates)[0]'hni_pos
      have hj0_mem : j0 ∈ notIndices C.gates := List.getElem_mem hni_pos
      have ⟨hj0_lt, hj0_op⟩ := (notIndices_mem C.gates j0).mp hj0_mem
      have hgat0 : gateAt C j0 = C.gates[j0] := by
        simp [gateAt, List.getD, List.getElem?_eq_getElem hj0_lt]
      have hj0_not : (C.gates[j0]).op = GateOp.not := by rw [← hgat0]; exact hj0_op

      have hpre_mon : ∀ g ∈ C.gates.take j0, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
        intro g hg
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
        have hj_lt_j0 : j < j0 := by rw [List.length_take_of_le (Nat.le_of_lt hj0_lt)] at hj; exact hj
        have hj_C : j < C.gates.length := lt_trans hj_lt_j0 hj0_lt
        rw [List.getElem_take]
        have ⟨hop, hlen⟩ := hfit C.gates[j] (List.getElem_mem hj_C)
        refine ⟨?_, hlen⟩
        rcases hop with h1 | h2 | h3
        · left; exact h1
        · right; exact h2
        · exfalso
          simp only [Set.mem_singleton_iff] at h3
          have hmem : j ∈ notIndices C.gates := (notIndices_mem C.gates j).mpr ⟨hj_C, by
            simp [gateAt, List.getD, List.getElem?_eq_getElem hj_C, h3]⟩
          obtain ⟨idx, hidx, hget⟩ := List.mem_iff_getElem.mp hmem
          cases idx with
          | zero => omega
          | succ idx' =>
            have := notIndices_get_lt C.gates hni_pos hidx (Nat.zero_lt_succ idx')
            omega

      have hj0_eval : ∀ x : Finset (Fin n),
          (C.wires (yOf x (zSet k))).getD (n + m + 2 + j0) false = !(f x) := by
        intro x
        have hhead : ∃ rest, notOutputs (n + m + 2) C (yOf x (zSet k)) =
            (C.wires (yOf x (zSet k))).getD (n + m + 2 + j0) false :: rest ∧ rest.length = a := by
          cases hni : notIndices C.gates with
          | nil => simp [hni] at hni_pos
          | cons j0' rest =>
            have hj_eq : j0' = j0 := by simp [j0, hni]
            subst hj_eq
            refine ⟨rest.map (fun j => (C.wires (yOf x (zSet k))).getD (n + m + 2 + j) false), ?_, ?_⟩
            · simp [notOutputs, hni]
            · simp only [List.length_map]
              have := congrArg List.length hni
              simp [hni_len, b] at this; omega
        obtain ⟨rest, hrest, hrest_len⟩ := hhead
        have hrk_iff : h ≤ notRank (n + m + 2) C (yOf x (zSet k)) ↔
            (C.wires (yOf x (zSet k))).getD (n + m + 2 + j0) false = true := by
          unfold notRank; rw [hrest]
          change 2 ^ a ≤ _ ↔ _
          rw [← hrest_len]
          exact bitsToNat_head_ge _ _
        cases hfx : f x
        ·
          have he1 : C.eval (yOf x (zSet k)) = true := by
            rw [heval, hzSet_card k (by omega)]; simp [hfx]
          have he2 : C.eval (yOf Finset.univ (zSet k)) = false := by
            rw [heval, hzSet_card k (by omega)]; simp [hf1]
          have hfall := hrk_fall (Finset.subset_univ x) (Finset.Subset.refl _) he1 he2
          have hge : h ≤ notRank (n + m + 2) C (yOf x (zSet k)) := by omega
          simpa using hrk_iff.mp hge
        ·
          have he1 : C.eval (yOf ∅ (zSet k)) = true := by
            rw [heval, hzSet_card k (by omega)]; simp [hf0]
          have he2 : C.eval (yOf x (zSet k)) = false := by
            rw [heval, hzSet_card k (by omega)]; simp [hfx]
          have hfall := hrk_fall (Finset.empty_subset x) (Finset.Subset.refl _) he1 he2
          have h2b : 2 ^ b = 2 * h := by simp [b, h, Nat.pow_succ, mul_comm]
          have hlt : ¬(h ≤ notRank (n + m + 2) C (yOf x (zSet k))) := by rw [hnc, h2b] at hpre_k; omega
          have hne : (C.wires (yOf x (zSet k))).getD (n + m + 2 + j0) false ≠ true := fun ht => hlt (hrk_iff.mpr ht)
          cases hv : (C.wires (yOf x (zSet k))).getD (n + m + 2 + j0) false <;> simp_all

      cases hins : (C.gates[j0]).inputs with
      | nil =>
        exfalso
        have h1 := hj0_eval Finset.univ
        rw [← hyOf_len Finset.univ (zSet k), wires_get_gate_rb C (yOf Finset.univ (zSet k)) j0 hj0_lt
          (by rw [hyOf_len]; exact hrb)] at h1
        simp [hj0_not, hins, GateOp.eval, hf1] at h1
      | cons u us =>
        have hu_lt : u < n + m + 2 + j0 := by
          have h1 := hrb j0 hj0_lt u
          rw [hgat0, hins] at h1
          exact h1 (List.mem_cons_self ..)
        let D := hardwirePrefix n m (zSet k) C j0 u
        refine ⟨D, ⟨⟨hardwirePrefix_fanInTwo n m (zSet k) C j0 u hfit,
          hardwirePrefix_readsBack n m (zSet k) C j0 u hrb, ?_⟩, ?_⟩, ?_, ?_⟩
        · have hD_len : D.size = j0 := by simp [D, hardwirePrefix, Circuit.size, Nat.le_of_lt hj0_lt]
          rw [hD_len]; exact remapWire_lt n m (zSet k) j0 u hu_lt
        · intro x
          have hhw := hardwirePrefix_wires n m (zSet k) C j0 u (Nat.le_of_lt hj0_lt) hrb
            (bits n x) (hbits_len n x) (bits m (zSet k)) (hbits_len m (zSet k))
            (fun i => by
              have hiff := hbits_get_iff m (zSet k) i.val i.isLt
              simp only [Fin.eta] at hiff
              cases hb : (bits m (zSet k)).getD i.val false
              · have hni : i ∉ zSet k := fun hmem => by have h1 := hiff.mpr hmem; rw [hb] at h1; exact Bool.false_ne_true h1
                exact (decide_eq_false hni).symm
              · have hi : i ∈ zSet k := hiff.mp hb
                exact (decide_eq_true hi).symm)
            u hu_lt
          change (D.wires (bits n x ++ [false, true])).getD (remapWire n m (zSet k) u) false = f x
          rw [hhw]
          have h1 := hj0_eval x
          rw [← hyOf_len x (zSet k), wires_get_gate_rb C (yOf x (zSet k)) j0 hj0_lt
            (by rw [hyOf_len]; exact hrb)] at h1
          simp only [hj0_not, hins, GateOp.eval, List.map_cons, List.headD_cons] at h1
          cases hv : (C.wires (yOf x (zSet k))).getD u false <;> cases hfx : f x <;> simp_all
        · intro g hg
          simp only [D, hardwirePrefix, List.mem_map] at hg
          obtain ⟨g0, hg0, rfl⟩ := hg
          have ⟨hop, hlen⟩ := hpre_mon g0 hg0
          exact ⟨hop, by simpa [remapGate] using hlen⟩
        · simp [D, hardwirePrefix, Circuit.size, List.length_take_of_le (Nat.le_of_lt hj0_lt), hj0_lt]
  ·
    intro D ⟨⟨hfitD, hrbD, houtD⟩, hevalD⟩
    let n0 := n + m + 2
    let cF := n + m
    let cT := n + m + 1
    let L := Nat.log2 n0 + 2
    have h2b_le_n0 : 2 ^ b ≤ n0 := by
      cases a with
      | zero => simp [b, n0]
      | succ a' =>
        have h2a : 2 ^ (a' + 1) = 2 * 2 ^ a' := by rw [Nat.pow_succ]; ring
        have h2b : 2 ^ b = 2 * h := by simp [b, h, Nat.pow_succ, mul_comm]
        have h1 : 1 ≤ 2 ^ a' := Nat.one_le_two_pow
        have hh2 : 2 ≤ h := by simp [h, h2a]; omega
        have hm_eq : m = 4 * h - 4 := by omega
        omega
    have hb_le_log : b ≤ Nat.log2 n0 :=
      (Nat.le_log2 (by omega : n0 ≠ 0)).mpr h2b_le_n0

    let p1 := if m ≤ 1 then 0 else Nat.log2 (m - 1) + 1
    have hp1_ge : m ≤ 2 ^ p1 := by
      by_cases hm1 : m ≤ 1
      · simp [p1, hm1]
      · simp only [p1, hm1, ↓reduceIte]
        have hlt := Nat.lt_log2_self (n := m - 1)
        omega
    have hp1_le_pow : 2 ^ p1 ≤ 2 * n0 := by
      by_cases hm1 : m ≤ 1
      · simp [p1, hm1]; omega
      · simp only [p1, hm1, ↓reduceIte, Nat.pow_succ]
        have hle : 2 ^ Nat.log2 (m - 1) ≤ m - 1 := (Nat.le_log2 (by omega : m - 1 ≠ 0)).mp le_rfl
        omega
    have hp1_le_L : p1 + 1 ≤ L := by
      by_cases hm1 : m ≤ 1
      · simp [p1, hm1, L]
      · simp only [p1, hm1, ↓reduceIte, L]
        have hle : Nat.log2 (m - 1) ≤ Nat.log2 n0 :=
          (Nat.le_log2 (by omega : n0 ≠ 0)).mpr (le_trans ((Nat.le_log2 (by omega : m - 1 ≠ 0)).mp le_rfl) (by omega))
        omega

    let zPadWires : List ℕ :=
      (List.range (2 ^ p1)).map (fun i => if i < m then n + i else cF)
    have hzPad_len : zPadWires.length = 2 ^ p1 := by simp [zPadWires]
    have hzPad_lt : ∀ gs0 : List Gate, ∀ w ∈ zPadWires, w < n0 + gs0.length := by
      intro gs0 w hw
      simp only [zPadWires, List.mem_map, List.mem_range] at hw
      obtain ⟨i, _, rfl⟩ := hw; split_ifs <;> omega
    have hsortZ_eval : ∀ (gs0 : List Gate) (x : Finset (Fin n)) (z : Finset (Fin m)),
        let y := bits n x ++ bits m z ++ [false, true]
        let sZ := compileCompsFwd n0 gs0 zPadWires (bitonicSortComps 0 true p1)
        ∀ j : ℕ,
          let wT := if j = 0 then cT else if j ≤ m then sZ.2.1.getD (j - 1) cF else cF
          ((Circuit.mk sZ.1 0).wires y).getD wT false = decide (j ≤ z.card) := by
      intro gs0 x z y sZ j
      have hy : y.length = n0 := by simp [y, n0, hbits_len]; omega
      have hspec := compileCompsFwd_spec n0 (bitonicSortComps 0 true p1) gs0 zPadWires
        (hzPad_lt gs0) (fun q hq => by
          have := bitonicSortComps_valid 0 (2 ^ p1) true p1 (by simp) q hq
          rw [hzPad_len]; exact ⟨this.1, this.2.1, this.2.2.1⟩)
      have hmap := hspec.2.2.2.2 y hy
      let v0 := zPadWires.map (fun w => ((Circuit.mk gs0 0).wires y).getD w false)
      have hv0_len : v0.length = 2 ^ p1 := by simp [v0, hzPad_len]
      have hsort := bitonicSort_correct p1 v0 0 true (by rw [hv0_len]; simp)
      have hslice_eq : ∀ (v : List Bool), v.length = 2 ^ p1 → slice v 0 (2 ^ p1) = v := by
        intro v hv; simp [slice, hv]
      have hcnt_v0 : v0.count true = z.card := by
        have hv0_eq : v0 = bits m z ++ List.replicate (2 ^ p1 - m) false := by
          apply List.ext_getElem (by simp [v0, hzPad_len, hbits_len]; omega)
          intro i h1 h2
          have hi : i < 2 ^ p1 := by simpa [v0, hzPad_len] using h1
          simp only [v0, zPadWires, List.getElem_map, List.getElem_range]
          by_cases him : i < m
          · simp only [him, ↓reduceIte]
            rw [wires_get_input _ y (n + i) (by omega)]
            have gy : y.getD (n + i) false = (bits m z).getD i false := by
              simp only [y, List.getD]
              rw [List.getElem?_append_left (by simp [hbits_len]; omega)]
              rw [List.getElem?_append_right (by rw [hbits_len]; omega), hbits_len]
              simp
            rw [gy, List.getElem_append_left (by rw [hbits_len m z]; exact him)]
            simp [List.getD, List.getElem?_eq_getElem (by rw [hbits_len m z]; exact him)]
          · simp only [him, ↓reduceIte]
            rw [wires_get_input _ y cF (by omega)]
            have gy : y.getD cF false = false := by
              simp only [y, cF, List.getD]
              rw [List.getElem?_append_right (by simp [hbits_len])]
              simp [hbits_len]
            rw [gy, List.getElem_append_right (by rw [hbits_len]; omega)]
            simp
        rw [hv0_eq, List.count_append, hbits_count, count_true_replicate]; simp
      have hsorted_eq : sZ.2.1.map (fun w => ((Circuit.mk sZ.1 0).wires y).getD w false) =
          List.replicate z.card true ++ List.replicate (2 ^ p1 - z.card) false := by
        rw [hmap]
        have hlen1 : (applyComps v0 (bitonicSortComps 0 true p1)).length = 2 ^ p1 := by
          rw [applyComps_length, hv0_len]
        have hs1 := hsort.1
        have hc1 := hsort.2
        simp only [↓reduceIte, hslice_eq _ hlen1, hslice_eq _ hv0_len, hcnt_v0] at hs1 hc1
        unfold isSortedDesc at hs1
        rw [hc1, hlen1] at hs1
        exact hs1
      by_cases hj0 : j = 0
      · subst hj0; simp only [↓reduceIte, Nat.zero_le, decide_true]
        rw [wires_get_input _ y cT (by omega)]
        simp only [y, cT, List.getD]
        rw [List.getElem?_append_right (by simp [hbits_len])]
        have : n + m + 1 - (bits n x ++ bits m z).length = 1 := by simp [hbits_len]
        rw [this]; rfl
      · by_cases hjm : j ≤ m
        · simp only [hj0, ↓reduceIte, hjm]
          have hj1 : j - 1 < 2 ^ p1 := by omega
          have hj1_s : j - 1 < sZ.2.1.length := by rw [hspec.2.1, hzPad_len]; exact hj1
          have hget : ((Circuit.mk sZ.1 0).wires y).getD (sZ.2.1.getD (j - 1) cF) false =
              (sZ.2.1.map (fun w => ((Circuit.mk sZ.1 0).wires y).getD w false)).getD (j - 1) false := by
            simp [List.getD, List.getElem?_eq_getElem hj1_s]
          rw [hget, hsorted_eq, List.getD]
          by_cases hjz : j ≤ z.card
          · rw [List.getElem?_append_left (by simp; omega)]
            simp [show j - 1 < z.card by omega, hjz]
          · rw [List.getElem?_append_right (by simp; omega)]
            have hzc : z.card ≤ m := by
              calc z.card ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_le_card (Finset.subset_univ _)
                _ = m := Finset.card_fin m
            simp [show j - 1 - z.card < 2 ^ p1 - z.card by omega, hjz]
        · simp only [hj0, ↓reduceIte, hjm]
          have hzc : z.card ≤ m := by
            calc z.card ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_le_card (Finset.subset_univ _)
              _ = m := Finset.card_fin m
          have hgt : ¬(j ≤ z.card) := by omega
          rw [decide_eq_false hgt, wires_get_input _ y cF (by omega)]
          simp only [y, cF, List.getD]
          rw [List.getElem?_append_right (by simp [hbits_len])]
          simp [hbits_len]

    let compileAndList : List Gate → List (ℕ × ℕ) → List Gate × List ℕ := fun gs pairs =>
      pairs.foldl
        (fun (acc : List Gate × List ℕ) pq =>
          (acc.1 ++ [⟨GateOp.and, [pq.1, pq.2]⟩], acc.2 ++ [n0 + acc.1.length]))
        (gs, [])
    have hAndList_spec : ∀ (pairs : List (ℕ × ℕ)) (gs : List Gate),
        (∀ pq ∈ pairs, pq.1 < n0 + gs.length ∧ pq.2 < n0 + gs.length) →
        let res := compileAndList gs pairs
        (∃ ex, res.1 = gs ++ ex ∧ ex.length = pairs.length ∧
          Monotone2 ⟨ex, 0⟩ ∧ ReadsBack (n0 + gs.length) ⟨ex, 0⟩) ∧
        res.2.length = pairs.length ∧
        (∀ w ∈ res.2, w < n0 + res.1.length) ∧
        (∀ y : List Bool, y.length = n0 → ∀ (i : ℕ) (hi : i < pairs.length),
          ((Circuit.mk res.1 0).wires y).getD (res.2.getD i 0) false =
            (((Circuit.mk gs 0).wires y).getD (pairs[i]'hi).1 false &&
             ((Circuit.mk gs 0).wires y).getD (pairs[i]'hi).2 false)) := by
      intro pairs
      induction pairs using List.reverseRecOn with
      | nil =>
        intro gs _
        refine ⟨⟨[], by simp [compileAndList], rfl, fun _ h => by simp at h, fun j hj => by simp at hj⟩,
          rfl, fun _ h => by simp [compileAndList] at h, fun _ _ _ hi => by simp at hi⟩
      | append_singleton pairs pq ih =>
        intro gs hlt
        have hlt_p : ∀ q ∈ pairs, q.1 < n0 + gs.length ∧ q.2 < n0 + gs.length :=
          fun q hq => hlt q (List.mem_append_left _ hq)
        have hlt_pq := hlt pq (List.mem_append_right _ (List.mem_singleton_self _))
        have ⟨⟨ex1, hgs1, hlen1, hmon1, hrb1⟩, hws1_l, hws1_lt, hsem1⟩ := ih gs hlt_p
        set r1 := compileAndList gs pairs
        have hr_eq : compileAndList gs (pairs ++ [pq]) =
            (r1.1 ++ [⟨GateOp.and, [pq.1, pq.2]⟩], r1.2 ++ [n0 + r1.1.length]) := by
          simp [compileAndList, r1, List.foldl_append]
        rw [hr_eq]
        have hlen_r1 : r1.1.length = gs.length + pairs.length := by rw [hgs1, List.length_append, hlen1]
        have hg_mon : Monotone2 ⟨[⟨GateOp.and, [pq.1, pq.2]⟩], 0⟩ := by
          intro g hg; simp only [List.mem_singleton] at hg; subst hg; simp
        have hg_rb : ReadsBack (n0 + r1.1.length) ⟨[⟨GateOp.and, [pq.1, pq.2]⟩], 0⟩ := by
          intro j hj u hu
          have hj0 : j = 0 := by simp at hj; omega
          subst hj0; simp only [gateAt, List.getD, List.getElem?_cons_zero, Option.getD_some,
            List.mem_cons, List.not_mem_nil, or_false] at hu
          rcases hu with rfl | rfl <;> omega
        refine ⟨⟨ex1 ++ [⟨GateOp.and, [pq.1, pq.2]⟩], by rw [hgs1, List.append_assoc], by simp [hlen1],
          monotone2_append ex1 _ 0 hmon1 hg_mon,
          readsBack_append (n0 + gs.length) ex1 _ 0 hrb1 (by simpa [hgs1, Nat.add_assoc] using hg_rb)⟩,
          by simp [hws1_l], ?_, ?_⟩
        · intro w hw; rcases List.mem_append.mp hw with h | h
          · have := hws1_lt w h; simp; omega
          · simp only [List.mem_singleton] at h; subst h; simp
        · intro y hy i hi
          simp only [List.length_append, List.length_singleton] at hi
          by_cases hip : i < pairs.length
          · have hg : (r1.2 ++ [n0 + r1.1.length]).getD i 0 = r1.2.getD i 0 := by
              simp [List.getD, List.getElem?_append_left (by omega : i < r1.2.length)]
            have hw_lt : r1.2.getD i 0 < n0 + r1.1.length := by
              have : r1.2.getD i 0 = r1.2[i]'(by omega) := by
                simp [List.getD, List.getElem?_eq_getElem (by omega : i < r1.2.length)]
              rw [this]; exact hws1_lt _ (List.getElem_mem (by omega))
            rw [hg, wires_prefix r1.1 _ y 0 _ (by omega), hsem1 y hy i hip]
            simp [List.getElem_append_left hip]
          · have hi_eq : i = pairs.length := by omega
            subst hi_eq
            have hg : (r1.2 ++ [n0 + r1.1.length]).getD pairs.length 0 = n0 + r1.1.length := by
              rw [List.getD, List.getElem?_append_right (by omega : r1.2.length ≤ pairs.length), hws1_l, Nat.sub_self]; rfl
            rw [hg, wires_snoc_last n0 r1.1 (Gate.mk GateOp.and [pq.1, pq.2]) y hy]
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
            rw [hgs1, wires_prefix gs ex1 y 0 pq.1 (by omega), wires_prefix gs ex1 y 0 pq.2 (by omega)]
            simp
    constructor
    ·
      intro hmonD
      let E := embedMono n m D
      have hE_mon : Monotone2 E := embedMono_monotone2 n m D hmonD
      have hE_rb : ReadsBack n0 E := embedMono_readsBack n m D hrbD
      have hE_out : E.output < n0 + E.gates.length := by
        have houtD' : D.output < n + 2 + D.gates.length := houtD
        simp only [E, embedMono, List.length_map]; split_ifs <;> omega

      let sZ := compileCompsFwd n0 E.gates zPadWires (bitonicSortComps 0 true p1)
      have hsZ_spec := compileCompsFwd_spec n0 (bitonicSortComps 0 true p1) E.gates zPadWires
        (hzPad_lt E.gates) (fun q hq => by
          have := bitonicSortComps_valid 0 (2 ^ p1) true p1 (by simp) q hq
          rw [hzPad_len]; exact ⟨this.1, this.2.1, this.2.2.1⟩)
      obtain ⟨⟨ex1, hgs1, hlen1, hmon1, hrb1⟩, hsZ_len, hsZ_lt, _, _⟩ := hsZ_spec
      let T : ℕ → ℕ := fun j => if j = 0 then cT else if j ≤ m then sZ.2.1.getD (j - 1) cF else cF
      have hT_lt : ∀ j, T j < n0 + sZ.1.length := by
        intro j; simp only [T]; split_ifs with h1 h2
        · omega
        · have hj1 : j - 1 < sZ.2.1.length := by rw [hsZ_len, hzPad_len]; omega
          have : sZ.2.1.getD (j - 1) cF = sZ.2.1[j - 1]'hj1 := by simp [List.getD, List.getElem?_eq_getElem hj1]
          rw [this]; exact hsZ_lt _ (List.getElem_mem hj1)
        · omega

      let wAnd := n0 + sZ.1.length
      let wMid := n0 + sZ.1.length + 1
      let stMid : List Gate := [⟨GateOp.and, [T k, E.output]⟩, ⟨GateOp.or, [T (k + 1), wAnd]⟩]
      let gs2 := sZ.1 ++ stMid
      have hstMid_mon : Monotone2 ⟨stMid, 0⟩ := by
        intro g hg; simp only [stMid, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl <;> simp
      have hstMid_rb : ReadsBack (n0 + sZ.1.length) ⟨stMid, 0⟩ := by
        intro j hj u hu
        have : j = 0 ∨ j = 1 := by simp [stMid] at hj; omega
        have hEo : E.output < n0 + sZ.1.length := by rw [hgs1]; simp; omega
        have hTk := hT_lt k; have hTk1 := hT_lt (k + 1)
        rcases this with rfl | rfl <;>
          (simp only [stMid, gateAt, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
            Option.getD_some, List.mem_cons, List.not_mem_nil, or_false] at hu;
           rcases hu with rfl | rfl <;> omega)

      let Y : List ℕ := (List.range r).map (fun i =>
        if i < h - 1 then T (2 * i + 1) else if i = h - 1 then wMid else T (2 * i))
      have hY_len : Y.length = 2 ^ (a + 1) - 1 := by
        simp [Y, r, h, Nat.pow_succ, mul_comm]
      have hY_lt : ∀ w ∈ Y, w < n0 + gs2.length := by
        intro w hw
        simp only [Y, List.mem_map, List.mem_range] at hw
        obtain ⟨i, _, rfl⟩ := hw
        have hgl : gs2.length = sZ.1.length + 2 := by simp [gs2, stMid]
        split_ifs
        · have := hT_lt (2 * i + 1); omega
        · omega
        · have := hT_lt (2 * i); omega
      let invRes := compileInvSorted n0 a gs2 Y
      have hinv_spec := compileInvSorted_spec n0 a gs2 Y hY_len hY_lt
      obtain ⟨⟨ex3, hgs3, hlen3, hnot3, hfit3, hrb3⟩, hny_len, hny_lt, hinv_sem⟩ := hinv_spec

      let pairs : List (ℕ × ℕ) := (List.range r).map (fun i =>
        let tLo := if i = 0 then cT else if i < h - 1 then T (2 * i)
          else if i = h - 1 then T k else T (2 * i - 1)
        (tLo, invRes.2.getD i 0))
      have hpairs_lt : ∀ pq ∈ pairs, pq.1 < n0 + invRes.1.length ∧ pq.2 < n0 + invRes.1.length := by
        intro pq hpq
        simp only [pairs, List.mem_map, List.mem_range] at hpq
        obtain ⟨i, hi, rfl⟩ := hpq
        have hi' : i < invRes.2.length := by rw [hny_len]; simpa [r, h, Nat.pow_succ, mul_comm] using hi
        have hle_len : sZ.1.length ≤ invRes.1.length := by rw [hgs3, List.length_append]; simp [gs2]; omega
        constructor
        · split_ifs
          · omega
          · have := hT_lt (2 * i); omega
          · have := hT_lt k; omega
          · have := hT_lt (2 * i - 1); omega
        · have : invRes.2.getD i 0 = invRes.2[i]'hi' := by simp [List.getD, List.getElem?_eq_getElem hi']
          rw [this]; exact hny_lt _ (List.getElem_mem hi')
      let andRes := compileAndList invRes.1 pairs
      have ⟨⟨ex4, hgs4, hlen4, hmon4, hrb4⟩, hterms_len, hterms_lt, hand_sem⟩ :=
        hAndList_spec pairs invRes.1 hpairs_lt
      let orRes := compileOrChain n0 cF andRes.1 andRes.2
      have ⟨⟨ex5, hgs5, hlen5, hmon5, hrb5⟩, hout_lt, hor_sem⟩ :=
        compileOrChain_spec n0 cF andRes.2 andRes.1 (by omega) hterms_lt
      let C : Circuit := ⟨orRes.1, orRes.2⟩
      have hC_gates : C.gates = E.gates ++ ex1 ++ stMid ++ ex3 ++ ex4 ++ ex5 := by
        change orRes.1 = _
        rw [hgs5, hgs4, hgs3]; dsimp only [gs2]; rw [hgs1]
      have hC_eq : C = ⟨E.gates ++ ex1 ++ stMid ++ ex3 ++ ex4 ++ ex5, C.output⟩ :=
        congrArg (fun g => Circuit.mk g orRes.2) hC_gates
      refine ⟨C, ⟨⟨?_, ?_, hout_lt⟩, ?_⟩, ?_, ?_⟩
      ·
        rw [hC_eq]
        apply fanInTwo_append _ ex5 _ _ (monotone2_imp_fanInTwo _ hmon5)
        apply fanInTwo_append _ ex4 _ _ (monotone2_imp_fanInTwo _ hmon4)
        apply fanInTwo_append _ ex3 _ _ hfit3
        apply fanInTwo_append _ stMid _ _ (monotone2_imp_fanInTwo _ hstMid_mon)
        exact fanInTwo_append E.gates ex1 _ (monotone2_imp_fanInTwo _ hE_mon) (monotone2_imp_fanInTwo _ hmon1)
      ·
        rw [hC_eq]
        have r1 := readsBack_append n0 E.gates ex1 0 hE_rb hrb1
        have r2 := readsBack_append n0 (E.gates ++ ex1) stMid 0 r1 (by
          have hl : n0 + (E.gates ++ ex1).length = n0 + sZ.1.length := by rw [hgs1]
          rw [hl]; exact hstMid_rb)
        have r3 := readsBack_append n0 (E.gates ++ ex1 ++ stMid) ex3 0 r2 (by
          have hl : n0 + (E.gates ++ ex1 ++ stMid).length = n0 + gs2.length := by dsimp only [gs2]; rw [hgs1]
          rw [hl]; exact hrb3)
        have r4 := readsBack_append n0 (E.gates ++ ex1 ++ stMid ++ ex3) ex4 0 r3 (by
          have hl : n0 + (E.gates ++ ex1 ++ stMid ++ ex3).length = n0 + invRes.1.length := by rw [hgs3]; dsimp only [gs2]; rw [hgs1]
          rw [hl]; exact hrb4)
        exact readsBack_append n0 _ ex5 C.output r4 (by
          have hl : n0 + (E.gates ++ ex1 ++ stMid ++ ex3 ++ ex4).length = n0 + andRes.1.length := by
            rw [hgs4, hgs3]; dsimp only [gs2]; rw [hgs1]
          rw [hl]; exact hrb5)
      ·
        intro x z
        let y := bits n x ++ bits m z ++ [false, true]
        have hy : y.length = n0 := by simp [y, n0, hbits_len]; omega
        have hT_val : ∀ j, ((Circuit.mk sZ.1 0).wires y).getD (T j) false = decide (j ≤ z.card) :=
          hsortZ_eval E.gates x z
        have hEf_val : ((Circuit.mk sZ.1 0).wires y).getD E.output false = f x := by
          rw [hgs1, wires_prefix E.gates ex1 y 0 E.output (by omega)]
          have hw := embedMono_wires n m D hrbD (bits n x) (hbits_len n x) (bits m z) (hbits_len m z)
            D.output houtD
          exact hw.trans (hevalD x)
        have hMid_val : ((Circuit.mk gs2 0).wires y).getD wMid false =
            (decide (k + 1 ≤ z.card) || (decide (k ≤ z.card) && f x)) := by
          have hgs2_eq : gs2 = (sZ.1 ++ [Gate.mk GateOp.and [T k, E.output]]) ++ [Gate.mk GateOp.or [T (k + 1), wAnd]] := by
            simp [gs2, stMid]
          have hwm_eq : wMid = n0 + (sZ.1 ++ [Gate.mk GateOp.and [T k, E.output]]).length := by simp [wMid]; omega
          rw [hgs2_eq, hwm_eq, wires_snoc_last n0 (sZ.1 ++ [Gate.mk GateOp.and [T k, E.output]]) _ y hy]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          rw [wires_prefix sZ.1 _ y 0 (T (k + 1)) (by have := hT_lt (k + 1); omega), hT_val (k + 1)]
          rw [show wAnd = n0 + sZ.1.length from rfl, wires_snoc_last n0 sZ.1 _ y hy]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          rw [hT_val k, hEf_val]
        have hY_val : ∀ i < r, ((Circuit.mk gs2 0).wires y).getD (Y.getD i 0) false =
            if i < h - 1 then decide (2 * i + 1 ≤ z.card)
            else if i = h - 1 then (decide (k + 1 ≤ z.card) || (decide (k ≤ z.card) && f x))
            else decide (2 * i ≤ z.card) := by
          intro i hi
          have hget : Y.getD i 0 = if i < h - 1 then T (2 * i + 1) else if i = h - 1 then wMid else T (2 * i) := by
            simp [Y, List.getD, hi]
          rw [hget]
          split_ifs with c1 c2
          · rw [show gs2 = sZ.1 ++ stMid from rfl, wires_prefix sZ.1 stMid y 0 _ (by have := hT_lt (2 * i + 1); omega), hT_val]
          · exact hMid_val
          · rw [show gs2 = sZ.1 ++ stMid from rfl, wires_prefix sZ.1 stMid y 0 _ (by have := hT_lt (2 * i); omega), hT_val]
        have hY_sorted : ∀ i j, i ≤ j → j < Y.length →
            ((Circuit.mk gs2 0).wires y).getD (Y.getD j 0) false ≤
              ((Circuit.mk gs2 0).wires y).getD (Y.getD i 0) false := by
          intro i j hij hj
          have hjr : j < r := by simpa [Y] using hj
          rw [hY_val i (by omega), hY_val j hjr]
          split_ifs <;>
            (cases hfx : f x <;> simp [Bool.le_iff_imp] <;> omega)
        have hnY_val : ∀ i < r, ((Circuit.mk invRes.1 0).wires y).getD (invRes.2.getD i 0) false =
            !(if i < h - 1 then decide (2 * i + 1 ≤ z.card)
              else if i = h - 1 then (decide (k + 1 ≤ z.card) || (decide (k ≤ z.card) && f x))
              else decide (2 * i ≤ z.card)) := by
          intro i hi
          rw [hinv_sem y hy hY_sorted i (by simpa [Y] using hi), hY_val i hi]
        have hcf_and : ((Circuit.mk andRes.1 0).wires y).getD cF false = false := by
          rw [wires_get_input _ y cF (by omega)]
          simp only [y, cF, List.getD]
          rw [List.getElem?_append_right (by simp [hbits_len])]
          simp [hbits_len]
        change ((Circuit.mk orRes.1 0).wires y).getD orRes.2 false = _
        rw [hor_sem y hy hcf_and]

        have hterm_val : ∀ i < r, ((Circuit.mk andRes.1 0).wires y).getD (andRes.2.getD i 0) false =
            if i < h - 1 then decide (z.card = 2 * i)
            else if i = h - 1 then (decide (z.card = k) && !(f x))
            else decide (z.card = 2 * i - 1) := by
          intro i hi
          rw [hand_sem y hy i (by simpa [pairs] using hi)]
          have hp_i : pairs[i]'(by simpa [pairs] using hi) =
              (if i = 0 then cT else if i < h - 1 then T (2 * i) else if i = h - 1 then T k else T (2 * i - 1),
               invRes.2.getD i 0) := by simp [pairs]
          rw [hp_i, hnY_val i hi]
          have hT_inv : ∀ t, ((Circuit.mk invRes.1 0).wires y).getD (T t) false = decide (t ≤ z.card) := by
            intro t
            rw [hgs3]; dsimp only [gs2]
            rw [List.append_assoc, wires_prefix sZ.1 _ y 0 (T t) (by have := hT_lt t; omega), hT_val t]
          have hcT_inv : ((Circuit.mk invRes.1 0).wires y).getD cT false = true := by
            rw [wires_get_input _ y cT (by omega)]
            simp only [y, cT, List.getD]
            rw [List.getElem?_append_right (by simp [hbits_len])]
            have : n + m + 1 - (bits n x ++ bits m z).length = 1 := by simp [hbits_len]
            rw [this]; rfl
          by_cases hi0 : i = 0
          · subst hi0; simp only [↓reduceIte, hcT_inv, Bool.true_and]
            by_cases hh1 : 0 < h - 1
            · simp only [hh1, ↓reduceIte, Nat.mul_zero, zero_add]
              by_cases hz0 : z.card = 0
              · simp [hz0]
              · have h1 : 1 ≤ z.card := by omega
                simp [hz0, h1]
            · have hk0 : k = 0 := by omega
              have hz0 : z.card = 0 := by
                have hle : z.card ≤ m := by
                  calc z.card ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_le_card (Finset.subset_univ _)
                    _ = m := Finset.card_fin m
                omega
              simp [show h - 1 = 0 by omega, hk0, hz0]
          · simp only [hi0, ↓reduceIte]
            by_cases c1 : i < h - 1
            · simp only [c1, ↓reduceIte, hT_inv]
              by_cases h1 : 2 * i ≤ z.card <;> by_cases h2 : 2 * i + 1 ≤ z.card <;>
                simp [h1, h2, show (z.card = 2 * i) ↔ (2 * i ≤ z.card ∧ ¬(2 * i + 1 ≤ z.card)) by omega]
            · by_cases c2 : i = h - 1
              · simp only [c1, c2, lt_irrefl, ↓reduceIte]
                rw [hT_inv k]
                by_cases h1 : k ≤ z.card <;> by_cases h2 : k + 1 ≤ z.card <;> cases hfx : f x <;>
                  simp [h1, h2, show (z.card = k) ↔ (k ≤ z.card ∧ ¬(k + 1 ≤ z.card)) by omega]
              · simp only [c1, c2, ↓reduceIte, hT_inv]
                by_cases h1 : 2 * i - 1 ≤ z.card <;> by_cases h2 : 2 * i ≤ z.card <;>
                  simp [h1, h2, show (z.card = 2 * i - 1) ↔ (2 * i - 1 ≤ z.card ∧ ¬(2 * i ≤ z.card)) by omega]
        apply Bool.eq_iff_iff.mpr
        rw [List.any_eq_true]
        constructor
        · rintro ⟨w, hw, hwt⟩
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hw
          have hir : i < r := by rw [hterms_len] at hi; simpa [pairs] using hi
          have hv := hterm_val i hir
          have hget : andRes.2.getD i 0 = andRes.2[i]'hi := by simp [List.getD, List.getElem?_eq_getElem hi]
          rw [hget, hwt] at hv
          split_ifs at hv with c1 c2
          · have hzc : z.card = 2 * i := decide_eq_true_eq.mp hv.symm
            have hlt : z.card < k := by omega
            rw [if_pos hlt, hzc]; exact @decide_eq_true _ (Classical.propDecidable _) (by omega)
          · have h1 : z.card = k ∧ !(f x) = true := by
              have hb := Bool.and_eq_true_iff.mp hv.symm
              exact ⟨decide_eq_true_eq.mp hb.1, hb.2⟩
            rw [h1.1, if_neg (lt_irrefl k), if_pos rfl]; exact h1.2
          · have hzc : z.card = 2 * i - 1 := decide_eq_true_eq.mp hv.symm
            have hgt : ¬(z.card < k) := by omega
            have hne : z.card ≠ k := by omega
            simp [hgt, hne]; omega
        · intro htarget
          have hzc_le : z.card ≤ m := by
            calc z.card ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_le_card (Finset.subset_univ _)
              _ = m := Finset.card_fin m
          by_cases c1 : z.card < k
          · simp only [c1, ↓reduceIte, decide_eq_true_eq] at htarget
            let i := z.card / 2
            have hir : i < r := by omega
            have hi_len : i < andRes.2.length := by rw [hterms_len]; simpa [pairs] using hir
            refine ⟨andRes.2[i]'hi_len, List.getElem_mem hi_len, ?_⟩
            have hget : andRes.2.getD i 0 = andRes.2[i]'hi_len := by simp [List.getD, List.getElem?_eq_getElem hi_len]
            rw [← hget, hterm_val i hir]
            have hi_lt : i < h - 1 := by omega
            simp [hi_lt]; omega
          · by_cases c2 : z.card = k
            · simp only [c1, c2, ↓reduceIte] at htarget
              let i := h - 1
              have hir : i < r := by omega
              have hi_len : i < andRes.2.length := by rw [hterms_len]; simpa [pairs] using hir
              refine ⟨andRes.2[i]'hi_len, List.getElem_mem hi_len, ?_⟩
              have hget : andRes.2.getD i 0 = andRes.2[i]'hi_len := by simp [List.getD, List.getElem?_eq_getElem hi_len]
              rw [← hget, hterm_val i hir]
              simp only [i, lt_irrefl, ↓reduceIte, c2, decide_true, Bool.true_and]
              simp only [lt_irrefl, ↓reduceIte] at htarget
              exact htarget
            · simp only [c1, c2, ↓reduceIte, decide_eq_true_eq] at htarget
              let i := (z.card + 1) / 2
              have hir : i < r := by omega
              have hi_len : i < andRes.2.length := by rw [hterms_len]; simpa [pairs] using hir
              refine ⟨andRes.2[i]'hi_len, List.getElem_mem hi_len, ?_⟩
              have hget : andRes.2.getD i 0 = andRes.2[i]'hi_len := by simp [List.getD, List.getElem?_eq_getElem hi_len]
              rw [← hget, hterm_val i hir]
              have hi_gt1 : ¬(i < h - 1) := by omega
              have hi_gt2 : i ≠ h - 1 := by omega
              simp [hi_gt1, hi_gt2]; omega
      ·
        rw [hC_eq]
        have hEn : notCount ⟨E.gates, 0⟩ = 0 := notCount_of_monotone2 ⟨E.gates, 0⟩ hE_mon
        simp only [notCount_append, hEn,
          notCount_of_monotone2 ⟨ex1, 0⟩ hmon1, notCount_of_monotone2 ⟨stMid, 0⟩ hstMid_mon,
          notCount_of_monotone2 ⟨ex4, 0⟩ hmon4, notCount_of_monotone2 ⟨ex5, 0⟩ hmon5, hnot3]
        omega
      ·
        have hC_sz : C.size = D.size + ex1.length + 2 + ex3.length + ex4.length + ex5.length := by
          simp [Circuit.size, hC_gates, E, embedMono, stMid]; omega
        have hcs1 := bitonicSortComps_length 0 true p1
        have h_ex1 : ex1.length ≤ n0 * L ^ 2 := by
          have h1 : 2 * ex1.length = p1 * (p1 + 1) * 2 ^ p1 := by omega
          have h2 : p1 * (p1 + 1) ≤ L ^ 2 := by rw [sq]; exact Nat.mul_le_mul (by omega) hp1_le_L
          have h3 : p1 * (p1 + 1) * 2 ^ p1 ≤ L ^ 2 * (2 * n0) := Nat.mul_le_mul h2 hp1_le_pow
          have h4 : L ^ 2 * (2 * n0) = 2 * (n0 * L ^ 2) := by ring
          omega
        have hL2 : 4 ≤ L ^ 2 := by
          have hL_ge2 : 2 ≤ L := by simp [L]
          rw [sq]; exact Nat.mul_le_mul hL_ge2 hL_ge2
        have h_ex3 : ex3.length ≤ 4 * n0 := by
          have : 2 ^ (a + 1) = 2 ^ b := rfl
          omega
        have h_ex4 : ex4.length ≤ n0 := by rw [hlen4]; simp [pairs]; omega
        have h_ex5 : ex5.length ≤ n0 := by
          have : andRes.2.length = r := by rw [hterms_len]; simp [pairs]
          omega
        have hn0_L : 4 * n0 ≤ n0 * L ^ 2 := by
          rw [mul_comm n0]; exact Nat.mul_le_mul_right n0 hL2
        have h96 : 96 * n0 * L ^ 2 = 96 * (n0 * L ^ 2) := by ring
        rw [hC_sz]
        change D.size + ex1.length + 2 + ex3.length + ex4.length + ex5.length ≤ D.size + 96 * n0 * L ^ 2
        omega
    ·

      let sZ := compileCompsFwd n0 [] zPadWires (bitonicSortComps 0 true p1)
      have hsZ_spec := compileCompsFwd_spec n0 (bitonicSortComps 0 true p1) [] zPadWires
        (hzPad_lt []) (fun q hq => by
          have := bitonicSortComps_valid 0 (2 ^ p1) true p1 (by simp) q hq
          rw [hzPad_len]; exact ⟨this.1, this.2.1, this.2.2.1⟩)
      obtain ⟨⟨ex1, hgs1, hlen1, hmon1, hrb1⟩, hsZ_len, hsZ_lt, _, _⟩ := hsZ_spec
      let T : ℕ → ℕ := fun j => if j = 0 then cT else if j ≤ m then sZ.2.1.getD (j - 1) cF else cF
      have hT_lt : ∀ j, T j < n0 + sZ.1.length := by
        intro j; simp only [T]; split_ifs with h1 h2
        · omega
        · have hj1 : j - 1 < sZ.2.1.length := by rw [hsZ_len, hzPad_len]; omega
          have : sZ.2.1.getD (j - 1) cF = sZ.2.1[j - 1]'hj1 := by simp [List.getD, List.getElem?_eq_getElem hj1]
          rw [this]; exact hsZ_lt _ (List.getElem_mem hj1)
        · omega

      let p2 := b + 1
      have hp2_eq : 2 ^ p2 = 4 * h := by simp [p2, b, h, Nat.pow_succ]; ring
      let W : List ℕ := (List.range (2 ^ p2)).map (fun idx =>
        if idx < n then idx
        else if idx < n + r then
          let i := idx - n
          if i < h - 1 then T (2 * i + 1)
          else if i = h - 1 then T (k + 1)
          else T (2 * i)
        else cF)
      have hW_len : W.length = 2 ^ p2 := by simp [W]
      have hW_lt : ∀ w ∈ W, w < n0 + sZ.1.length := by
        intro w hw; simp only [W, List.mem_map, List.mem_range] at hw
        obtain ⟨idx, _, rfl⟩ := hw
        split_ifs
        · omega
        · exact hT_lt _
        · exact hT_lt _
        · exact hT_lt _
        · omega

      have hfwdW_spec := compileCompsFwd_spec n0 (bitonicSortComps 0 true p2) sZ.1 W
        hW_lt (fun q hq => by
          have := bitonicSortComps_valid 0 (2 ^ p2) true p2 (by simp) q hq
          rw [hW_len]; exact ⟨this.1, this.2.1, this.2.2.1⟩)
      set fwdW := compileCompsFwd n0 sZ.1 W (bitonicSortComps 0 true p2)
      obtain ⟨⟨ex2, hgs2, hlen2, hmon2, hrb2⟩, hsW_len, hsW_lt, hlog_len, hfwdW_sem⟩ := hfwdW_spec

      let sWInit := fwdW.2.1.take (2 ^ p2 - 1)
      have hsWInit_len : sWInit.length = 2 ^ (a + 1 + 1) - 1 := by
        have hle : 2 ^ p2 - 1 ≤ fwdW.2.1.length := by rw [hsW_len, hW_len]; omega
        rw [show sWInit = fwdW.2.1.take (2 ^ p2 - 1) from rfl, List.length_take_of_le hle]
      have hsWInit_lt : ∀ w ∈ sWInit, w < n0 + fwdW.1.length :=
        fun w hw => hsW_lt w (List.mem_of_mem_take hw)
      have hinvW_spec := compileInvSorted_spec n0 (a + 1) fwdW.1 sWInit hsWInit_len hsWInit_lt
      set invW := compileInvSorted n0 (a + 1) fwdW.1 sWInit
      obtain ⟨⟨ex3, hgs3, hlen3, hnot3, hfit3, hrb3⟩, hnsW_len, hnsW_lt, hinvW_sem⟩ := hinvW_spec
      let negSW := invW.2 ++ [cT]
      have hnegSW_len : negSW.length = W.length := by
        have h1 : 1 ≤ 2 ^ p2 := Nat.one_le_two_pow
        have h2 : invW.2.length = 2 ^ p2 - 1 := hnsW_len
        simp only [negSW, List.length_append, List.length_singleton, h2, hW_len]; omega
      have hnegSW_lt : ∀ w ∈ negSW, w < n0 + invW.1.length := by
        intro w hw; rcases List.mem_append.mp hw with h | h
        · exact hnsW_lt w h
        · simp only [List.mem_singleton] at h; subst h; omega

      have hbwdW_spec := compileCompsBwd_spec n0 (bitonicSortComps 0 true p2) sZ.1 W invW.1 negSW
        hW_lt (fun q hq => by
          have := bitonicSortComps_valid 0 (2 ^ p2) true p2 (by simp) q hq
          rw [hW_len]; exact ⟨this.1, this.2.1, this.2.2.1⟩)
        ⟨ex3, hgs3⟩ hnegSW_len hnegSW_lt
      set bwdW := compileCompsBwd n0 invW.1 negSW fwdW.2.2.reverse
      obtain ⟨⟨ex4, hgs4, hlen4, hmon4, hrb4⟩, hnegW_len, hnegW_lt, hbwdW_sem⟩ := hbwdW_spec
      change ∀ y : List Bool, y.length = n0 →
        (∀ k < W.length,
          ((Circuit.mk invW.1 0).wires y).getD (negSW.getD k 0) false =
            !(((Circuit.mk fwdW.1 0).wires y).getD (fwdW.2.1.getD k 0) false)) →
        ∀ k < W.length,
          ((Circuit.mk bwdW.1 0).wires y).getD (bwdW.2.getD k 0) false =
            !(((Circuit.mk sZ.1 0).wires y).getD (W.getD k 0) false) at hbwdW_sem
      clear_value fwdW invW

      let posIn : List ℕ := List.range n ++ [cF, cT]
      let negIn : List ℕ := (List.range n).map (fun i => bwdW.2.getD i 0) ++ [cT, cF]
      have hposIn_len : posIn.length = n + 2 := by simp [posIn]
      have hnegIn_len : negIn.length = n + 2 := by simp [negIn]
      have hposIn_lt : ∀ w ∈ posIn, w < n0 + bwdW.1.length := by
        intro w hw; simp only [posIn, List.mem_append, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with h | rfl | rfl <;> omega
      have hnegIn_lt : ∀ w ∈ negIn, w < n0 + bwdW.1.length := by
        intro w hw; simp only [negIn, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with ⟨i, hi, rfl⟩ | rfl | rfl
        · have hi' : i < bwdW.2.length := by rw [hnegW_len, hW_len]; omega
          have : bwdW.2.getD i 0 = bwdW.2[i]'hi' := by simp [List.getD, List.getElem?_eq_getElem hi']
          rw [this]; exact hnegW_lt _ (List.getElem_mem hi')
        · omega
        · omega
      have hdr_spec := compileDualRail_spec n0 cF cT D.gates bwdW.1 posIn negIn
        (by omega) (by omega) (by rw [hposIn_len, hnegIn_len])
        hposIn_lt hnegIn_lt hfitD (by rw [hposIn_len]; exact hrbD)
      set drRes := compileDualRail n0 cF cT bwdW.1 posIn negIn D.gates
      obtain ⟨⟨ex5, hgs5, hlen5, hmon5, hrb5⟩, hposD_len, hnegD_len, _, hnegD_lt, hdr_sem⟩ := hdr_spec
      clear_value bwdW drRes
      let wNotF := drRes.2.2.getD D.output cT
      have hwNotF_lt : wNotF < n0 + drRes.1.length := by
        have ho' : D.output < drRes.2.2.length := by rw [hnegD_len, hnegIn_len]; exact houtD
        have : wNotF = drRes.2.2[D.output]'ho' := by simp [wNotF, List.getD, List.getElem?_eq_getElem ho']
        rw [this]; exact hnegD_lt _ (List.getElem_mem ho')

      let wNegMid := bwdW.2.getD (n + (h - 1)) 0
      have hwNegMid_lt : wNegMid < n0 + drRes.1.length := by
        have hm' : n + (h - 1) < bwdW.2.length := by rw [hnegW_len, hW_len]; omega
        have h1 : wNegMid = bwdW.2[n + (h - 1)]'hm' := by simp [wNegMid, List.getD, List.getElem?_eq_getElem hm']
        have h2 := hnegW_lt _ (h1 ▸ List.getElem_mem hm')
        rw [hgs5, List.length_append]; omega
      have hT_lt_dr : ∀ j, T j < n0 + drRes.1.length := by
        intro j; have := hT_lt j
        rw [hgs5, hgs4, hgs3, hgs2]; simp only [List.length_append]; omega
      let wSliceK := n0 + drRes.1.length
      let gSliceK : Gate := ⟨GateOp.and, [T k, wNegMid]⟩
      let gs6 := drRes.1 ++ [gSliceK]
      have hgSliceK_mon : Monotone2 ⟨[gSliceK], 0⟩ := by
        intro g hg; simp only [List.mem_singleton] at hg; subst hg; simp [gSliceK]
      have hgSliceK_rb : ReadsBack (n0 + drRes.1.length) ⟨[gSliceK], 0⟩ := by
        intro j hj u hu
        have hj0 : j = 0 := by simp at hj; omega
        subst hj0; simp only [gateAt, List.getD_cons_zero, gSliceK,
          List.mem_cons, List.not_mem_nil, or_false] at hu
        have := hT_lt_dr k
        rcases hu with rfl | rfl <;> omega
      let pairs : List (ℕ × ℕ) := (List.range r).map (fun i =>
        if i < h - 1 then
          (if i = 0 then cT else T (2 * i), bwdW.2.getD (n + i) 0)
        else if i = h - 1 then
          (wSliceK, wNotF)
        else
          (T (2 * i - 1), bwdW.2.getD (n + i) 0))
      have hpairs_lt : ∀ pq ∈ pairs, pq.1 < n0 + gs6.length ∧ pq.2 < n0 + gs6.length := by
        intro pq hpq
        simp only [pairs, List.mem_map, List.mem_range] at hpq
        obtain ⟨i, hi, rfl⟩ := hpq
        have hni_lt : n + i < bwdW.2.length := by rw [hnegW_len, hW_len]; omega
        have hbw_lt : bwdW.2.getD (n + i) 0 < n0 + gs6.length := by
          have : bwdW.2.getD (n + i) 0 = bwdW.2[n + i]'hni_lt := by simp [List.getD, List.getElem?_eq_getElem hni_lt]
          have h1 := hnegW_lt _ (this ▸ List.getElem_mem hni_lt)
          have hgl : gs6.length = drRes.1.length + 1 := by simp [gs6]
          rw [hgl, hgs5, List.length_append]; omega
        have hgl : gs6.length = drRes.1.length + 1 := by simp [gs6]
        split_ifs
        · exact ⟨by omega, hbw_lt⟩
        · have := hT_lt_dr (2 * i); exact ⟨by omega, hbw_lt⟩
        · exact ⟨by dsimp only [wSliceK]; omega, by omega⟩
        · have := hT_lt_dr (2 * i - 1); exact ⟨by omega, hbw_lt⟩
      have hAnd_spec := hAndList_spec pairs gs6 hpairs_lt
      set andRes := compileAndList gs6 pairs
      obtain ⟨⟨ex7, hgs7, hlen7, hmon7, hrb7⟩, hterms_len, hterms_lt, hand_sem⟩ := hAnd_spec
      have hOr_spec := compileOrChain_spec n0 cF andRes.2 andRes.1 (by omega) hterms_lt
      set orRes := compileOrChain n0 cF andRes.1 andRes.2
      obtain ⟨⟨ex8, hgs8, hlen8, hmon8, hrb8⟩, hout_lt, hor_sem⟩ := hOr_spec
      clear_value andRes orRes
      let C : Circuit := ⟨orRes.1, orRes.2⟩
      have hC_gates : C.gates = ex1 ++ ex2 ++ ex3 ++ ex4 ++ ex5 ++ [gSliceK] ++ ex7 ++ ex8 := by
        change orRes.1 = _
        rw [hgs8, hgs7]; dsimp only [gs6]; rw [hgs5, hgs4, hgs3, hgs2, hgs1]; simp only [List.nil_append, List.append_assoc]
      have hC_eq : C = ⟨ex1 ++ ex2 ++ ex3 ++ ex4 ++ ex5 ++ [gSliceK] ++ ex7 ++ ex8, C.output⟩ :=
        congrArg (fun g => Circuit.mk g orRes.2) hC_gates
      refine ⟨C, ⟨⟨?_, ?_, hout_lt⟩, ?_⟩, ?_, ?_⟩
      ·
        rw [hC_eq]
        apply fanInTwo_append _ ex8 _ _ (monotone2_imp_fanInTwo _ hmon8)
        apply fanInTwo_append _ ex7 _ _ (monotone2_imp_fanInTwo _ hmon7)
        apply fanInTwo_append _ [gSliceK] _ _ (monotone2_imp_fanInTwo _ hgSliceK_mon)
        apply fanInTwo_append _ ex5 _ _ (monotone2_imp_fanInTwo _ hmon5)
        apply fanInTwo_append _ ex4 _ _ (monotone2_imp_fanInTwo _ hmon4)
        apply fanInTwo_append _ ex3 _ _ hfit3
        exact fanInTwo_append ex1 ex2 _ (monotone2_imp_fanInTwo _ hmon1) (monotone2_imp_fanInTwo _ hmon2)
      ·
        rw [hC_eq]
        have r1 : ReadsBack n0 ⟨ex1, 0⟩ := by simpa using hrb1
        have r2 := readsBack_append n0 ex1 ex2 0 r1 (by
          have hl : n0 + ex1.length = n0 + sZ.1.length := by rw [hgs1]; simp
          rw [hl]; exact hrb2)
        have r3 := readsBack_append n0 (ex1 ++ ex2) ex3 0 r2 (by
          have hl : n0 + (ex1 ++ ex2).length = n0 + fwdW.1.length := by rw [hgs2, hgs1]; simp
          rw [hl]; exact hrb3)
        have r4 := readsBack_append n0 (ex1 ++ ex2 ++ ex3) ex4 0 r3 (by
          have hl : n0 + (ex1 ++ ex2 ++ ex3).length = n0 + invW.1.length := by rw [hgs3, hgs2, hgs1]; simp
          rw [hl]; exact hrb4)
        have r5 := readsBack_append n0 (ex1 ++ ex2 ++ ex3 ++ ex4) ex5 0 r4 (by
          have hl : n0 + (ex1 ++ ex2 ++ ex3 ++ ex4).length = n0 + bwdW.1.length := by rw [hgs4, hgs3, hgs2, hgs1]; simp
          rw [hl]; exact hrb5)
        have r6 := readsBack_append n0 (ex1 ++ ex2 ++ ex3 ++ ex4 ++ ex5) [gSliceK] 0 r5 (by
          have hl : n0 + (ex1 ++ ex2 ++ ex3 ++ ex4 ++ ex5).length = n0 + drRes.1.length := by rw [hgs5, hgs4, hgs3, hgs2, hgs1]; simp
          rw [hl]; exact hgSliceK_rb)
        have r7 := readsBack_append n0 (ex1 ++ ex2 ++ ex3 ++ ex4 ++ ex5 ++ [gSliceK]) ex7 0 r6 (by
          have hl : n0 + (ex1 ++ ex2 ++ ex3 ++ ex4 ++ ex5 ++ [gSliceK]).length = n0 + gs6.length := by
            dsimp only [gs6]; rw [hgs5, hgs4, hgs3, hgs2, hgs1]; simp
          rw [hl]; exact hrb7)
        exact readsBack_append n0 _ ex8 C.output r7 (by
          have hl : n0 + (ex1 ++ ex2 ++ ex3 ++ ex4 ++ ex5 ++ [gSliceK] ++ ex7).length = n0 + andRes.1.length := by
            rw [hgs7]; dsimp only [gs6]; rw [hgs5, hgs4, hgs3, hgs2, hgs1]; simp
          rw [hl]; exact hrb8)
      ·
        intro x z
        let y := bits n x ++ bits m z ++ [false, true]
        have hy : y.length = n0 := by simp [y, n0, hbits_len]; omega
        have hT_val : ∀ j, ((Circuit.mk sZ.1 0).wires y).getD (T j) false = decide (j ≤ z.card) :=
          hsortZ_eval [] x z
        have hcF_val : ∀ (gs : List Gate), ((Circuit.mk gs 0).wires y).getD cF false = false := by
          intro gs; rw [wires_get_input _ y cF (by omega)]
          simp only [y, cF, List.getD]
          rw [List.getElem?_append_right (by simp [hbits_len])]
          simp [hbits_len]
        have hcT_val : ∀ (gs : List Gate), ((Circuit.mk gs 0).wires y).getD cT false = true := by
          intro gs; rw [wires_get_input _ y cT (by omega)]
          simp only [y, cT, List.getD]
          rw [List.getElem?_append_right (by simp [hbits_len])]
          have : n + m + 1 - (bits n x ++ bits m z).length = 1 := by simp [hbits_len]
          rw [this]; rfl

        let vW0 := W.map (fun w => ((Circuit.mk sZ.1 0).wires y).getD w false)
        have hvW0_len : vW0.length = 2 ^ p2 := by simp [vW0, hW_len]
        have hsortW := bitonicSort_correct p2 vW0 0 true (by rw [hvW0_len]; simp)
        have hslice_eq : ∀ (v : List Bool), v.length = 2 ^ p2 → slice v 0 (2 ^ p2) = v := by
          intro v hv; simp [slice, hv]
        have hmapW := hfwdW_sem y hy
        have hsortedW : fwdW.2.1.map (fun w => ((Circuit.mk fwdW.1 0).wires y).getD w false) =
            List.replicate (vW0.count true) true ++ List.replicate (2 ^ p2 - vW0.count true) false := by
          rw [hmapW]
          have hlen1 : (applyComps vW0 (bitonicSortComps 0 true p2)).length = 2 ^ p2 := by
            rw [applyComps_length, hvW0_len]
          have hs1 := hsortW.1
          have hc1 := hsortW.2
          simp only [↓reduceIte, hslice_eq _ hlen1, hslice_eq _ hvW0_len] at hs1 hc1
          unfold isSortedDesc at hs1
          rw [hc1, hlen1] at hs1
          exact hs1
        have hlast_false : vW0.count true < 2 ^ p2 := by
          have hlast_idx : 2 ^ p2 - 1 < vW0.length := by rw [hvW0_len]; have := @Nat.one_le_two_pow p2; omega
          have hlast_v : vW0[2 ^ p2 - 1]'hlast_idx = false := by
            have hge : ¬(2 ^ p2 - 1 < n) := by omega
            have hge2 : ¬(2 ^ p2 - 1 < n + r) := by omega
            simp only [vW0, W, List.getElem_map, List.getElem_range, hge, hge2, ↓reduceIte]
            exact hcF_val sZ.1
          have hmem_f : false ∈ vW0 := hlast_v ▸ List.getElem_mem hlast_idx
          have hsum_cnt : vW0.count true + vW0.count false = vW0.length := by
            clear hlast_idx hlast_v hmem_f
            induction vW0 with
            | nil => simp
            | cons b bs ih => cases b <;> simp <;> omega
          have hcf_pos : 0 < vW0.count false := List.count_pos_iff.mpr hmem_f
          omega
        have hsW_get : ∀ idx < 2 ^ p2,
            ((Circuit.mk fwdW.1 0).wires y).getD (fwdW.2.1.getD idx 0) false = decide (idx < vW0.count true) := by
          intro idx hidx
          have hi' : idx < fwdW.2.1.length := by rw [hsW_len, hW_len]; exact hidx
          have hg : ((Circuit.mk fwdW.1 0).wires y).getD (fwdW.2.1.getD idx 0) false =
              (fwdW.2.1.map (fun w => ((Circuit.mk fwdW.1 0).wires y).getD w false)).getD idx false := by
            simp [List.getD, List.getElem?_eq_getElem hi']
          rw [hg, hsortedW, List.getD]
          by_cases hc : idx < vW0.count true
          · rw [List.getElem?_append_left (by simp; exact hc)]; simp [hc]
          · rw [List.getElem?_append_right (by simp; omega)]
            simp [show idx - vW0.count true < 2 ^ p2 - vW0.count true by omega, hc]
        have hsWInit_sort : ∀ i j, i ≤ j → j < sWInit.length →
            ((Circuit.mk fwdW.1 0).wires y).getD (sWInit.getD j 0) false ≤
              ((Circuit.mk fwdW.1 0).wires y).getD (sWInit.getD i 0) false := by
          intro i j hij hj
          have hj_lt : j < 2 ^ p2 - 1 := by rw [hsWInit_len] at hj; simp [p2, b] at hj ⊢; exact hj
          have hgi : sWInit.getD i 0 = fwdW.2.1.getD i 0 := by simp [sWInit, List.getD, List.getElem?_take_of_lt (by omega : i < 2 ^ p2 - 1)]
          have hgj : sWInit.getD j 0 = fwdW.2.1.getD j 0 := by simp [sWInit, List.getD, List.getElem?_take_of_lt hj_lt]
          rw [hgi, hgj, hsW_get i (by omega), hsW_get j (by omega)]
          simp [Bool.le_iff_imp]; omega
        have hnegSW_ok : ∀ idx < W.length,
            ((Circuit.mk invW.1 0).wires y).getD (negSW.getD idx 0) false =
              !(((Circuit.mk fwdW.1 0).wires y).getD (fwdW.2.1.getD idx 0) false) := by
          intro idx hidx
          rw [hW_len] at hidx
          by_cases hlt : idx < 2 ^ p2 - 1
          · have h1 : negSW.getD idx 0 = invW.2.getD idx 0 := by
              simp [negSW, List.getD, List.getElem?_append_left (by rw [hnsW_len]; simp [p2, b] at hlt ⊢; exact hlt)]
            have h2 : sWInit.getD idx 0 = fwdW.2.1.getD idx 0 := by
              simp [sWInit, List.getD, List.getElem?_take_of_lt hlt]
            rw [h1, hinvW_sem y hy hsWInit_sort idx (by rw [hsWInit_len]; simp [p2, b] at hlt ⊢; exact hlt), h2]
          · have heq : idx = 2 ^ p2 - 1 := by omega
            subst heq
            have h1 : negSW.getD (2 ^ p2 - 1) 0 = cT := by
              have hlen_inv : invW.2.length = 2 ^ p2 - 1 := hnsW_len
              rw [show negSW = invW.2 ++ [cT] from rfl, List.getD, List.getElem?_append_right (by omega), hlen_inv, Nat.sub_self]; rfl
            rw [h1, hcT_val, hsW_get (2 ^ p2 - 1) hidx]
            have hnf : ¬(2 ^ p2 - 1 < vW0.count true) := by omega
            simp [hnf]

        have hbwd_ok := hbwdW_sem y hy hnegSW_ok
        have hnegW_x : ∀ i < n, ((Circuit.mk bwdW.1 0).wires y).getD (bwdW.2.getD i 0) false = !((bits n x).getD i false) := by
          intro i hi
          rw [hbwd_ok i (by rw [hW_len]; omega)]
          have hWi : W.getD i 0 = i := by simp [W, List.getD, show i < 2 ^ p2 by omega, hi]
          rw [hWi, wires_get_input _ y i (by omega)]
          simp only [y, List.getD, List.append_assoc]
          rw [List.getElem?_append_left (by rw [hbits_len n x]; exact hi)]
        have hnegW_T : ∀ i < r, ((Circuit.mk bwdW.1 0).wires y).getD (bwdW.2.getD (n + i) 0) false =
            !(if i < h - 1 then decide (2 * i + 1 ≤ z.card)
              else if i = h - 1 then decide (k + 1 ≤ z.card)
              else decide (2 * i ≤ z.card)) := by
          intro i hi
          rw [hbwd_ok (n + i) (by rw [hW_len]; omega)]
          have hWi : W.getD (n + i) 0 =
              if i < h - 1 then T (2 * i + 1) else if i = h - 1 then T (k + 1) else T (2 * i) := by
            have h1 : n + i < 2 ^ p2 := by omega
            have h2 : ¬(n + i < n) := by omega
            have h3 : n + i < n + r := by omega
            simp [W, List.getD, h1, h2, h3]
          rw [hWi]
          split_ifs <;> rw [hT_val]

        have hwNotF_val : ((Circuit.mk drRes.1 0).wires y).getD wNotF false = !(f x) := by
          let yD := bits n x ++ [false, true]
          have hin_dr : ∀ i < posIn.length,
              ((Circuit.mk bwdW.1 0).wires y).getD (posIn.getD i cF) false = yD.getD i false ∧
              ((Circuit.mk bwdW.1 0).wires y).getD (negIn.getD i cT) false = !(yD.getD i false) := by
            intro i hi
            rw [hposIn_len] at hi
            by_cases hin : i < n
            · have hp : posIn.getD i cF = i := by
                simp only [posIn, List.getD]
                rw [List.getElem?_append_left (by simp; exact hin)]
                simp [hin]
              have hn' : negIn.getD i cT = bwdW.2.getD i 0 := by
                simp only [negIn, List.getD]
                rw [List.getElem?_append_left (by simp; exact hin)]
                simp [hin]
              have hyDi : yD.getD i false = (bits n x).getD i false := by
                simp only [yD, List.getD]
                rw [List.getElem?_append_left (by rw [hbits_len n x]; exact hin)]
              rw [hp, hn', hyDi, wires_get_input _ y i (by omega), hnegW_x i hin]
              constructor
              · simp only [y, List.getD, List.append_assoc]
                rw [List.getElem?_append_left (by rw [hbits_len n x]; exact hin)]
              · rfl
            · by_cases hi0 : i = n
              · rw [hi0]
                have hp : posIn.getD n cF = cF := by
                  simp only [posIn, List.getD]
                  rw [List.getElem?_append_right (by simp), List.length_range, Nat.sub_self]; rfl
                have hn' : negIn.getD n cT = cT := by
                  simp only [negIn, List.getD]
                  rw [List.getElem?_append_right (by simp), List.length_map, List.length_range, Nat.sub_self]; rfl
                have hyDi : yD.getD n false = false := by
                  simp only [yD, List.getD]
                  rw [List.getElem?_append_right (by rw [hbits_len n x]), hbits_len n x, Nat.sub_self]; rfl
                rw [hp, hn', hyDi, hcF_val, hcT_val]; simp
              · have hi1 : i = n + 1 := by omega
                rw [hi1]
                have hsub1 : n + 1 - n = 1 := by omega
                have hp : posIn.getD (n + 1) cF = cT := by
                  simp only [posIn, List.getD]
                  rw [List.getElem?_append_right (by simp), List.length_range, hsub1]; rfl
                have hn' : negIn.getD (n + 1) cT = cF := by
                  simp only [negIn, List.getD]
                  rw [List.getElem?_append_right (by simp), List.length_map, List.length_range, hsub1]; rfl
                have hyDi : yD.getD (n + 1) false = true := by
                  simp only [yD, List.getD]
                  rw [List.getElem?_append_right (by rw [hbits_len n x]; omega), hbits_len n x, hsub1]; rfl
                rw [hp, hn', hyDi, hcF_val, hcT_val]; simp
          have hres := (hdr_sem y yD hy (by simp [yD, hbits_len, hposIn_len]) (hcF_val bwdW.1) (hcT_val bwdW.1)
            hin_dr D.output (by rw [hposIn_len]; exact houtD)).2
          change ((Circuit.mk drRes.1 0).wires y).getD wNotF false = !(D.eval yD) at hres
          rw [hevalD x] at hres
          exact hres

        have hT_gs6 : ∀ j, ((Circuit.mk gs6 0).wires y).getD (T j) false = decide (j ≤ z.card) := by
          intro j
          have hpref : gs6 = sZ.1 ++ (ex2 ++ ex3 ++ ex4 ++ ex5 ++ [gSliceK]) := by
            simp [gs6, hgs5, hgs4, hgs3, hgs2, List.append_assoc]
          rw [hpref, wires_prefix sZ.1 _ y 0 (T j) (by have := hT_lt j; omega), hT_val j]
        have hnegW_gs6 : ∀ i < r, ((Circuit.mk gs6 0).wires y).getD (bwdW.2.getD (n + i) 0) false =
            !(if i < h - 1 then decide (2 * i + 1 ≤ z.card)
              else if i = h - 1 then decide (k + 1 ≤ z.card)
              else decide (2 * i ≤ z.card)) := by
          intro i hi
          have hni_lt : n + i < bwdW.2.length := by rw [hnegW_len, hW_len]; omega
          have hbw_lt : bwdW.2.getD (n + i) 0 < n0 + bwdW.1.length := by
            have : bwdW.2.getD (n + i) 0 = bwdW.2[n + i]'hni_lt := by simp [List.getD, List.getElem?_eq_getElem hni_lt]
            rw [this]; exact hnegW_lt _ (List.getElem_mem hni_lt)
          have hpref : gs6 = bwdW.1 ++ (ex5 ++ [gSliceK]) := by simp [gs6, hgs5, List.append_assoc]
          rw [hpref, wires_prefix bwdW.1 _ y 0 _ (by omega), hnegW_T i hi]
        have hwSliceK_val : ((Circuit.mk gs6 0).wires y).getD wSliceK false = decide (z.card = k) := by
          rw [show gs6 = drRes.1 ++ [gSliceK] from rfl, show wSliceK = n0 + drRes.1.length from rfl,
            wires_snoc_last n0 drRes.1 gSliceK y hy]
          simp only [gSliceK, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          have h1 : ((Circuit.mk drRes.1 0).wires y).getD (T k) false = decide (k ≤ z.card) := by
            have hpref : drRes.1 = sZ.1 ++ (ex2 ++ ex3 ++ ex4 ++ ex5) := by
              simp [hgs5, hgs4, hgs3, hgs2, List.append_assoc]
            rw [hpref, wires_prefix sZ.1 _ y 0 (T k) (by have := hT_lt k; omega), hT_val k]
          have h2 : ((Circuit.mk drRes.1 0).wires y).getD wNegMid false = !decide (k + 1 ≤ z.card) := by
            have hni_lt : n + (h - 1) < bwdW.2.length := by rw [hnegW_len, hW_len]; omega
            have hbw_lt : wNegMid < n0 + bwdW.1.length := by
              have : wNegMid = bwdW.2[n + (h - 1)]'hni_lt := by simp [wNegMid, List.getD, List.getElem?_eq_getElem hni_lt]
              rw [this]; exact hnegW_lt _ (List.getElem_mem hni_lt)
            rw [hgs5, wires_prefix bwdW.1 ex5 y 0 wNegMid (by omega), hnegW_T (h - 1) (by omega)]
            simp
          rw [h1, h2]
          by_cases hzc : z.card = k <;> simp [hzc] <;> omega
        have hwNotF_gs6 : ((Circuit.mk gs6 0).wires y).getD wNotF false = !(f x) := by
          rw [show gs6 = drRes.1 ++ [gSliceK] from rfl, wires_prefix drRes.1 [gSliceK] y 0 wNotF (by omega), hwNotF_val]
        have hterm_val : ∀ i < r, ((Circuit.mk andRes.1 0).wires y).getD (andRes.2.getD i 0) false =
            if i < h - 1 then decide (z.card = 2 * i)
            else if i = h - 1 then (decide (z.card = k) && !(f x))
            else decide (z.card = 2 * i - 1) := by
          intro i hi
          rw [hand_sem y hy i (by simpa [pairs] using hi)]
          have hp_i : pairs[i]'(by simpa [pairs] using hi) =
              if i < h - 1 then (if i = 0 then cT else T (2 * i), bwdW.2.getD (n + i) 0)
              else if i = h - 1 then (wSliceK, wNotF)
              else (T (2 * i - 1), bwdW.2.getD (n + i) 0) := by simp [pairs]
          rw [hp_i]
          by_cases c1 : i < h - 1
          · simp only [c1, ↓reduceIte, hnegW_gs6 i hi]
            by_cases hi0 : i = 0
            · subst hi0; simp only [↓reduceIte, hcT_val, Bool.true_and, Nat.mul_zero, zero_add]
              by_cases hzc : z.card = 0
              · simp [hzc]
              · have h1 : 1 ≤ z.card := by omega
                simp [hzc, h1]
            · simp only [hi0, ↓reduceIte, hT_gs6]
              by_cases h1 : 2 * i ≤ z.card <;> by_cases h2 : 2 * i + 1 ≤ z.card <;>
                simp [h1, h2, show (z.card = 2 * i) ↔ (2 * i ≤ z.card ∧ ¬(2 * i + 1 ≤ z.card)) by omega]
          · by_cases c2 : i = h - 1
            · simp only [c1, c2, lt_irrefl, ↓reduceIte]
              rw [hwSliceK_val, hwNotF_gs6]
            · simp only [c1, c2, ↓reduceIte, hT_gs6, hnegW_gs6 i hi]
              by_cases h1 : 2 * i - 1 ≤ z.card <;> by_cases h2 : 2 * i ≤ z.card <;>
                simp [h1, h2, show (z.card = 2 * i - 1) ↔ (2 * i - 1 ≤ z.card ∧ ¬(2 * i ≤ z.card)) by omega]
        change ((Circuit.mk orRes.1 0).wires y).getD orRes.2 false = _
        rw [hor_sem y hy (hcF_val andRes.1)]
        apply Bool.eq_iff_iff.mpr
        rw [List.any_eq_true]
        constructor
        · rintro ⟨w, hw, hwt⟩
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hw
          have hir : i < r := by rw [hterms_len] at hi; simpa [pairs] using hi
          have hv := hterm_val i hir
          have hget : andRes.2.getD i 0 = andRes.2[i]'hi := by simp [List.getD, List.getElem?_eq_getElem hi]
          rw [hget, hwt] at hv
          split_ifs at hv with c1 c2
          · have hzc : z.card = 2 * i := decide_eq_true_eq.mp hv.symm
            have hlt : z.card < k := by omega
            rw [if_pos hlt, hzc]; exact @decide_eq_true _ (Classical.propDecidable _) (by omega)
          · have h1 : z.card = k ∧ !(f x) = true := by
              have hb := Bool.and_eq_true_iff.mp hv.symm
              exact ⟨decide_eq_true_eq.mp hb.1, hb.2⟩
            rw [h1.1, if_neg (lt_irrefl k), if_pos rfl]; exact h1.2
          · have hzc : z.card = 2 * i - 1 := decide_eq_true_eq.mp hv.symm
            have hgt : ¬(z.card < k) := by omega
            have hne : z.card ≠ k := by omega
            simp [hgt, hne]; omega
        · intro htarget
          have hzc_le : z.card ≤ m := by
            calc z.card ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_le_card (Finset.subset_univ _)
              _ = m := Finset.card_fin m
          by_cases c1 : z.card < k
          · simp only [c1, ↓reduceIte, decide_eq_true_eq] at htarget
            let i := z.card / 2
            have hir : i < r := by omega
            have hi_len : i < andRes.2.length := by rw [hterms_len]; simpa [pairs] using hir
            refine ⟨andRes.2[i]'hi_len, List.getElem_mem hi_len, ?_⟩
            have hget : andRes.2.getD i 0 = andRes.2[i]'hi_len := by simp [List.getD, List.getElem?_eq_getElem hi_len]
            rw [← hget, hterm_val i hir]
            have hi_lt : i < h - 1 := by omega
            simp [hi_lt]; omega
          · by_cases c2 : z.card = k
            · simp only [c1, c2, ↓reduceIte] at htarget
              let i := h - 1
              have hir : i < r := by omega
              have hi_len : i < andRes.2.length := by rw [hterms_len]; simpa [pairs] using hir
              refine ⟨andRes.2[i]'hi_len, List.getElem_mem hi_len, ?_⟩
              have hget : andRes.2.getD i 0 = andRes.2[i]'hi_len := by simp [List.getD, List.getElem?_eq_getElem hi_len]
              rw [← hget, hterm_val i hir]
              simp only [i, lt_irrefl, ↓reduceIte, c2, decide_true, Bool.true_and]
              simp only [lt_irrefl, ↓reduceIte] at htarget
              exact htarget
            · simp only [c1, c2, ↓reduceIte, decide_eq_true_eq] at htarget
              let i := (z.card + 1) / 2
              have hir : i < r := by omega
              have hi_len : i < andRes.2.length := by rw [hterms_len]; simpa [pairs] using hir
              refine ⟨andRes.2[i]'hi_len, List.getElem_mem hi_len, ?_⟩
              have hget : andRes.2.getD i 0 = andRes.2[i]'hi_len := by simp [List.getD, List.getElem?_eq_getElem hi_len]
              rw [← hget, hterm_val i hir]
              have hi_gt1 : ¬(i < h - 1) := by omega
              have hi_gt2 : i ≠ h - 1 := by omega
              simp [hi_gt1, hi_gt2]; omega
      ·
        rw [hC_eq]
        simp only [notCount_append, notCount_of_monotone2 ⟨ex1, 0⟩ hmon1,
          notCount_of_monotone2 ⟨ex2, 0⟩ hmon2, notCount_of_monotone2 ⟨ex4, 0⟩ hmon4,
          notCount_of_monotone2 ⟨ex5, 0⟩ hmon5, notCount_of_monotone2 ⟨[gSliceK], 0⟩ hgSliceK_mon,
          notCount_of_monotone2 ⟨ex7, 0⟩ hmon7, notCount_of_monotone2 ⟨ex8, 0⟩ hmon8, hnot3]
        omega
      ·
        have hC_sz : C.size = ex1.length + ex2.length + ex3.length + ex4.length + ex5.length + 1 + ex7.length + ex8.length := by
          simp [Circuit.size, hC_gates]; omega
        have hcs1 := bitonicSortComps_length 0 true p1
        have h_ex1 : ex1.length ≤ n0 * L ^ 2 := by
          have h1 : 2 * ex1.length = p1 * (p1 + 1) * 2 ^ p1 := by omega
          have h2 : p1 * (p1 + 1) ≤ L ^ 2 := by rw [sq]; exact Nat.mul_le_mul (by omega) hp1_le_L
          have h3 : p1 * (p1 + 1) * 2 ^ p1 ≤ L ^ 2 * (2 * n0) := Nat.mul_le_mul h2 hp1_le_pow
          have h4 : L ^ 2 * (2 * n0) = 2 * (n0 * L ^ 2) := by ring
          omega
        have hcs2 := bitonicSortComps_length 0 true p2
        have hp2_le_pow : 2 ^ p2 ≤ 2 * n0 := by
          have : 2 ^ p2 = 2 * 2 ^ b := by simp [p2, Nat.pow_succ, mul_comm]
          omega
        have hp2_le_L : p2 + 1 ≤ L := by simp [p2, L]; omega
        have h_ex2 : ex2.length ≤ n0 * L ^ 2 := by
          have h1 : 2 * ex2.length = p2 * (p2 + 1) * 2 ^ p2 := by omega
          have h2 : p2 * (p2 + 1) ≤ L ^ 2 := by rw [sq]; exact Nat.mul_le_mul (by omega) hp2_le_L
          have h3 : p2 * (p2 + 1) * 2 ^ p2 ≤ L ^ 2 * (2 * n0) := Nat.mul_le_mul h2 hp2_le_pow
          have h4 : L ^ 2 * (2 * n0) = 2 * (n0 * L ^ 2) := by ring
          omega
        have h_ex4 : ex4.length ≤ 2 * (n0 * L ^ 2) := by omega
        have hL2 : 4 ≤ L ^ 2 := by
          have hL_ge2 : 2 ≤ L := by simp [L]
          rw [sq]; exact Nat.mul_le_mul hL_ge2 hL_ge2
        have h_ex3 : ex3.length ≤ 8 * n0 := by
          have : 2 ^ (a + 1 + 1) = 2 ^ p2 := by simp [p2, b]
          omega
        have h_ex5 : ex5.length ≤ 2 * D.size := hlen5
        have h_ex7 : ex7.length ≤ n0 := by rw [hlen7]; simp [pairs]; omega
        have h_ex8 : ex8.length ≤ n0 := by
          have : andRes.2.length = r := by rw [hterms_len]; simp [pairs]
          omega
        have hn0_L : 4 * n0 ≤ n0 * L ^ 2 := by
          rw [mul_comm n0]; exact Nat.mul_le_mul_right n0 hL2
        have h96 : 96 * n0 * L ^ 2 = 96 * (n0 * L ^ 2) := by ring
        rw [hC_sz]
        change ex1.length + ex2.length + ex3.length + ex4.length + ex5.length + 1 + ex7.length + ex8.length ≤
          2 * D.size + 96 * n0 * L ^ 2
        omega
