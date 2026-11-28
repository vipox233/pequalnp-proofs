import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1312_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket
open Classical

-- =========================================================================
-- Part 1: Circuit wire semantics, NOT-vector monotonicity, and Builder
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

private def bitsToNat : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat * 2 ^ bs.length + bitsToNat bs

private lemma bitsToNat_lt (bs : List Bool) : bitsToNat bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [bitsToNat]
  | cons b bs ih =>
    simp only [bitsToNat, List.length_cons, pow_succ]
    cases b <;> simp <;> omega

private lemma bitsToNat_lt_of_first_diff :
    ∀ (l1 l2 : List Bool), l1.length = l2.length →
      (∃ m, m < l1.length ∧ (∀ k < m, l1.getD k false = l2.getD k false) ∧
        l1.getD m false = false ∧ l2.getD m false = true) →
      bitsToNat l1 < bitsToNat l2
  | [], [], _, ⟨m, hm, _⟩ => by simp at hm
  | a :: t1, b :: t2, hlen, ⟨m, hm, hpref, hm1, hm2⟩ => by
    have htlen : t1.length = t2.length := by simp at hlen; omega
    cases m with
    | zero =>
      simp only [List.getD_cons_zero] at hm1 hm2
      subst hm1; subst hm2
      simp only [bitsToNat, Bool.toNat_false, Bool.toNat_true, zero_mul, zero_add, one_mul, htlen]
      have := bitsToNat_lt t1
      rw [htlen] at this
      omega
    | succ m' =>
      have hab : a = b := by simpa using hpref 0 (Nat.zero_lt_succ m')
      subst hab
      simp only [bitsToNat, htlen]
      have hsub : bitsToNat t1 < bitsToNat t2 :=
        bitsToNat_lt_of_first_diff t1 t2 htlen
          ⟨m', by simp at hm; omega,
           fun k hk => by simpa using hpref (k + 1) (Nat.succ_lt_succ hk),
           by simpa using hm1, by simpa using hm2⟩
      omega
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen

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

private def notIdxs (C : Circuit) : List ℕ :=
  (List.range C.gates.length).filter (fun j => isNotOp (gateAt C j).op)

private lemma notIdxs_length (C : Circuit) : (notIdxs C).length = notCount C := by
  unfold notIdxs
  rw [notCount_eq_filter_isNotOp]
  suffices ∀ (gs : List Gate),
      ((List.range gs.length).filter (fun j => isNotOp (gs.getD j ⟨GateOp.or, []⟩).op)).length =
        (gs.filter (fun g => isNotOp g.op)).length from this C.gates
  intro gs
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih =>
    rw [List.length_append, List.length_singleton, List.range_succ, List.filter_append,
      List.filter_append, List.length_append, List.length_append]
    congr 1
    · have hcongr : (List.range gs.length).filter
          (fun j => isNotOp ((gs ++ [g]).getD j ⟨GateOp.or, []⟩).op) =
          (List.range gs.length).filter
          (fun j => isNotOp (gs.getD j ⟨GateOp.or, []⟩).op) := by
        apply List.filter_congr
        intro j hj
        have hlt : j < gs.length := List.mem_range.mp hj
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
      rw [hcongr]; exact ih
    · simp only [List.filter_cons, List.filter_nil, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (le_refl gs.length), Nat.sub_self, List.getElem?_cons_zero,
        Option.getD_some]
      cases isNotOp g.op <;> rfl

private lemma notIdxs_pairwise (C : Circuit) : (notIdxs C).Pairwise (· < ·) :=
  List.pairwise_lt_range.filter _

private lemma mem_notIdxs_iff (C : Circuit) (j : ℕ) :
    j ∈ notIdxs C ↔ j < C.gates.length ∧ (gateAt C j).op = GateOp.not := by
  simp only [notIdxs, List.mem_filter, List.mem_range, isNotOp_eq_true]

private def notVec (n : ℕ) (C : Circuit) (inp : List Bool) : List Bool :=
  (notIdxs C).map (fun j => (C.wires inp).getD (n + 2 + j) false)

private def notVal (n : ℕ) (C : Circuit) (inp : List Bool) : ℕ :=
  bitsToNat (notVec n C inp)

private lemma notVal_lt (n : ℕ) (C : Circuit) (inp : List Bool) :
    notVal n C inp < 2 ^ notCount C := by
  have h1 := bitsToNat_lt (notVec n C inp)
  have hlen : (notVec n C inp).length = notCount C := by
    simp [notVec, notIdxs_length]
  rw [hlen] at h1
  exact h1

private lemma gateOp_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l1 l2 : List Bool) (hlen : l1.length = l2.length)
    (hle : ∀ k < l1.length, l1.getD k false = true → l2.getD k false = true) :
    op.eval l1 = true → op.eval l2 = true := by
  rcases hop with rfl | rfl
  · intro h1
    simp only [GateOp.eval, List.all_eq_true, id_eq] at h1 ⊢
    intro b hb
    rcases List.getElem_of_mem hb with ⟨k, hk, rfl⟩
    have hk1 : k < l1.length := by omega
    have h1k : l1.getD k false = true := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk1, Option.getD_some]
      exact h1 _ (List.getElem_mem hk1)
    have h2k := hle k hk1 h1k
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some] using h2k
  · intro h1
    simp only [GateOp.eval, List.any_eq_true, id_eq] at h1 ⊢
    rcases h1 with ⟨b, hb, rfl⟩
    rcases List.getElem_of_mem hb with ⟨k, hk1, hkval⟩
    have hk2 : k < l2.length := by omega
    have h1k : l1.getD k false = true := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk1, Option.getD_some]
      exact hkval
    have h2k := hle k hk1 h1k
    refine ⟨l2[k], List.getElem_mem hk2, ?_⟩
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk2, Option.getD_some] using h2k

private lemma wires_mono_upto {n : ℕ} (C : Circuit) (hfan : FanInTwo C) (hrb : ReadsBack (n + 2) C)
    (inp1 inp2 : List Bool) (hl1 : inp1.length = n + 2) (hl2 : inp2.length = n + 2)
    (hle : ∀ i < n + 2, inp1.getD i false = true → inp2.getD i false = true)
    (lim : ℕ) (hlim : lim ≤ C.gates.length)
    (hnot : ∀ j < lim, (gateAt C j).op = GateOp.not →
      (C.wires inp1).getD (n + 2 + j) false = (C.wires inp2).getD (n + 2 + j) false) :
    ∀ w < n + 2 + lim, (C.wires inp1).getD w false = true → (C.wires inp2).getD w false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw h1
    by_cases hlt : w < n + 2
    · unfold Circuit.wires at h1 ⊢
      rw [wires_foldl_getD_lt C.gates inp1 w (by omega)] at h1
      rw [wires_foldl_getD_lt C.gates inp2 w (by omega)]
      exact hle w hlt h1
    · set j := w - (n + 2)
      have hj_lt : j < lim := by omega
      have hj_len : j < C.gates.length := by omega
      have hw_eq : w = n + 2 + j := by omega
      rw [hw_eq] at h1 ⊢
      by_cases hnop : (gateAt C j).op = GateOp.not
      · rw [← hnot j hj_lt hnop]; exact h1
      · have hg_mem : gateAt C j ∈ C.gates := by
          simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj_len, Option.getD_some]
          exact List.getElem_mem hj_len
        have hop_mono : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
          rcases (hfan _ hg_mem).1 with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exact absurd h hnop
        have h1' := wires_getD_gate C inp1 j hj_len (by rw [hl1]; exact hrb)
        have h2' := wires_getD_gate C inp2 j hj_len (by rw [hl2]; exact hrb)
        rw [hl1] at h1'; rw [hl2] at h2'
        rw [h1'] at h1; rw [h2']
        apply gateOp_mono _ hop_mono _ _ (by simp) _ h1
        intro k hk hval
        simp only [List.length_map] at hk
        have hget1 : ((gateAt C j).inputs.map fun i => (C.wires inp1).getD i false).getD k false =
            (C.wires inp1).getD ((gateAt C j).inputs[k]'hk) false := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk,
            Option.map_some, Option.getD_some]
        have hget2 : ((gateAt C j).inputs.map fun i => (C.wires inp2).getD i false).getD k false =
            (C.wires inp2).getD ((gateAt C j).inputs[k]'hk) false := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk,
            Option.map_some, Option.getD_some]
        rw [hget1] at hval; rw [hget2]
        have hu_lt : (gateAt C j).inputs[k]'hk < n + 2 + j :=
          hrb j hj_len _ (List.getElem_mem hk)
        exact ih _ (by omega) (by omega) hval

private lemma notVal_anti {n : ℕ} (C : Circuit) (hfan : FanInTwo C) (hrb : ReadsBack (n + 2) C)
    (inp1 inp2 : List Bool) (hl1 : inp1.length = n + 2) (hl2 : inp2.length = n + 2)
    (hle : ∀ i < n + 2, inp1.getD i false = true → inp2.getD i false = true) :
    notVal n C inp2 < notVal n C inp1 ∨
    (notVal n C inp2 = notVal n C inp1 ∧
      ∀ w < n + 2 + C.size, (C.wires inp1).getD w false = true → (C.wires inp2).getD w false = true) := by
  by_cases heq : notVec n C inp1 = notVec n C inp2
  · right
    refine ⟨by unfold notVal; rw [heq], ?_⟩
    apply wires_mono_upto C hfan hrb inp1 inp2 hl1 hl2 hle C.gates.length le_rfl
    intro j hj hnop
    have hj_mem : j ∈ notIdxs C := (mem_notIdxs_iff C j).mpr ⟨hj, hnop⟩
    rcases List.getElem_of_mem hj_mem with ⟨p, hp, hjp⟩
    have h1 := congrArg (fun l => l.getD p false) heq
    simp only [notVec, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hp, Option.map_some, Option.getD_some, hjp] at h1
    exact h1
  · left
    have hlen_eq : (notVec n C inp1).length = (notVec n C inp2).length := by simp [notVec]
    have hex_diff : ∃ p, p < (notIdxs C).length ∧
        (notVec n C inp1).getD p false ≠ (notVec n C inp2).getD p false := by
      by_contra hno
      push_neg at hno
      apply heq
      apply List.ext_getElem hlen_eq
      intro p hp1 hp2
      have hp : p < (notIdxs C).length := by simpa [notVec] using hp1
      have h := hno p hp
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp1,
        List.getElem?_eq_getElem hp2, Option.getD_some] using h
    let p0 := Nat.find hex_diff
    have hp0_spec : p0 < (notIdxs C).length ∧
        (notVec n C inp1).getD p0 false ≠ (notVec n C inp2).getD p0 false :=
      Nat.find_spec hex_diff
    have hp0_min : ∀ k < p0, (notVec n C inp1).getD k false = (notVec n C inp2).getD k false := by
      intro k hk
      by_contra hne
      have := Nat.find_min hex_diff hk
      exact this ⟨by omega, hne⟩
    set j0 := (notIdxs C)[p0]'hp0_spec.1
    have hj0_mem : j0 ∈ notIdxs C := List.getElem_mem hp0_spec.1
    have hj0_spec := (mem_notIdxs_iff C j0).mp hj0_mem
    have hmono_lt : ∀ w < n + 2 + j0,
        (C.wires inp1).getD w false = true → (C.wires inp2).getD w false = true := by
      apply wires_mono_upto C hfan hrb inp1 inp2 hl1 hl2 hle j0 (le_of_lt hj0_spec.1)
      intro j hjl hnop
      have hj_mem : j ∈ notIdxs C := (mem_notIdxs_iff C j).mpr ⟨by omega, hnop⟩
      rcases List.getElem_of_mem hj_mem with ⟨q, hq, hjq⟩
      have hqp : q < p0 := by
        by_contra hge
        have hpq : p0 ≤ q := by omega
        rcases eq_or_lt_of_le hpq with rfl | hlt
        · omega
        · have := List.pairwise_iff_getElem.mp (notIdxs_pairwise C) p0 q hp0_spec.1 hq hlt
          omega
      have hmin := hp0_min q hqp
      simp only [notVec, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hq, Option.map_some, Option.getD_some, hjq] at hmin
      exact hmin
    have hv1 : (notVec n C inp1).getD p0 false = (C.wires inp1).getD (n + 2 + j0) false := by
      simp only [notVec, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hp0_spec.1, Option.map_some, Option.getD_some, j0]
    have hv2 : (notVec n C inp2).getD p0 false = (C.wires inp2).getD (n + 2 + j0) false := by
      simp only [notVec, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hp0_spec.1, Option.map_some, Option.getD_some, j0]
    have hg1 := wires_getD_gate C inp1 j0 hj0_spec.1 (by rw [hl1]; exact hrb)
    have hg2 := wires_getD_gate C inp2 j0 hj0_spec.1 (by rw [hl2]; exact hrb)
    rw [hl1] at hg1; rw [hl2] at hg2
    rw [hj0_spec.2] at hg1 hg2
    have hft : (notVec n C inp2).getD p0 false = false ∧ (notVec n C inp1).getD p0 false = true := by
      rw [hv1, hv2, hg1, hg2]
      have hne := hp0_spec.2
      rw [hv1, hv2, hg1, hg2] at hne
      cases hins : (gateAt C j0).inputs with
      | nil =>
        simp [hins, GateOp.eval] at hne
      | cons u rest =>
        simp only [hins, List.map_cons, GateOp.eval, List.headD_cons] at hne ⊢
        have hu_lt : u < n + 2 + j0 := hrb j0 hj0_spec.1 u (by rw [hins]; exact List.mem_cons_self ..)
        cases hu1 : (C.wires inp1).getD u false with
        | false =>
          cases hu2 : (C.wires inp2).getD u false with
          | false => rw [hu1, hu2] at hne; exact absurd rfl hne
          | true => simp
        | true =>
          have hu2 := hmono_lt u hu_lt hu1
          rw [hu1, hu2] at hne; exact absurd rfl hne
    unfold notVal
    exact bitsToNat_lt_of_first_diff (notVec n C inp2) (notVec n C inp1) hlen_eq.symm
      ⟨p0, by simp [notVec, hp0_spec.1], fun k hk => (hp0_min k hk).symm, hft.1, hft.2⟩

private structure Builder (n : ℕ) where
  gates : List Gate
  fan : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2
  rb : ∀ j < gates.length, ∀ i ∈ (gates.getD j ⟨GateOp.or, []⟩).inputs, i < n + 2 + j

private def Builder.toCircuit {n : ℕ} (B : Builder n) (out : ℕ := 0) : Circuit := ⟨B.gates, out⟩

private def Builder.eval {n : ℕ} (B : Builder n) (inp : List Bool) (w : ℕ) : Bool :=
  (B.toCircuit.wires inp).getD w false

private def Builder.nots {n : ℕ} (B : Builder n) : ℕ :=
  (B.gates.filter fun g => isNotOp g.op).length

private def Builder.monos {n : ℕ} (B : Builder n) : ℕ :=
  (B.gates.filter fun g => !(isNotOp g.op)).length

private lemma Builder.nots_eq_notCount {n : ℕ} (B : Builder n) (out : ℕ) :
    B.nots = notCount (B.toCircuit out) := (notCount_eq_filter_isNotOp (B.toCircuit out)).symm

private lemma Builder.gates_len_eq {n : ℕ} (B : Builder n) :
    B.gates.length = B.nots + B.monos := by
  unfold Builder.nots Builder.monos
  suffices ∀ gs : List Gate,
      gs.length = (gs.filter fun g => isNotOp g.op).length + (gs.filter fun g => !(isNotOp g.op)).length from
    this B.gates
  intro gs
  induction gs with
  | nil => simp
  | cons g gs ih =>
    simp only [List.length_cons, List.filter_cons]
    cases isNotOp g.op <;> simp <;> omega

private lemma Builder.toCircuit_fanInTwo {n : ℕ} (B : Builder n) (out : ℕ) :
    FanInTwo (B.toCircuit out) := by
  intro g hg
  rcases B.fan g hg with ⟨hop, hlen⟩
  exact ⟨by rcases hop with h | h | h <;> simp [h], hlen⟩

private def Builder.push {n : ℕ} (B : Builder n) (g : Gate)
    (hfan : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hins : ∀ i ∈ g.inputs, i < n + 2 + B.gates.length) : Builder n :=
  { gates := B.gates ++ [g]
    fan := by
      intro g' hg'
      rcases List.mem_append.mp hg' with h1 | h2
      · exact B.fan g' h1
      · simp only [List.mem_singleton] at h2; subst h2; exact hfan
    rb := by
      intro j hj i hi
      rw [List.length_append, List.length_singleton] at hj
      by_cases hlt : j < B.gates.length
      · have hget : (B.gates ++ [g]).getD j ⟨GateOp.or, []⟩ = B.gates.getD j ⟨GateOp.or, []⟩ := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
        rw [hget] at hi
        exact B.rb j hlt i hi
      · have heq : j = B.gates.length := by omega
        subst heq
        have hget : (B.gates ++ [g]).getD B.gates.length ⟨GateOp.or, []⟩ = g := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
            Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        rw [hget] at hi
        exact hins i hi }

private lemma Builder.eval_push_old {n : ℕ} (B : Builder n) (g : Gate)
    (hfan : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hins : ∀ i ∈ g.inputs, i < n + 2 + B.gates.length)
    (inp : List Bool) (hinp : inp.length = n + 2) (w : ℕ) (hw : w < n + 2 + B.gates.length) :
    (B.push g hfan hins).eval inp w = B.eval inp w := by
  unfold Builder.eval Builder.toCircuit Builder.push Circuit.wires
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  set w0 := B.gates.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) inp
  have hlen : w0.length = n + 2 + B.gates.length := by
    dsimp only [w0]; rw [wires_foldl_len, hinp]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]

private lemma Builder.eval_push_new {n : ℕ} (B : Builder n) (g : Gate)
    (hfan : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hins : ∀ i ∈ g.inputs, i < n + 2 + B.gates.length)
    (inp : List Bool) (hinp : inp.length = n + 2) :
    (B.push g hfan hins).eval inp (n + 2 + B.gates.length) =
      g.op.eval (g.inputs.map (B.eval inp)) := by
  unfold Builder.eval Builder.toCircuit Builder.push Circuit.wires
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  set w0 := B.gates.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) inp
  have hlen : w0.length = n + 2 + B.gates.length := by
    dsimp only [w0]; rw [wires_foldl_len, hinp]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : w0.length ≤ n + 2 + B.gates.length),
    hlen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]

private lemma Builder.push_nots {n : ℕ} (B : Builder n) (g : Gate) (hfan hins) :
    (B.push g hfan hins).nots = B.nots + if isNotOp g.op = true then 1 else 0 := by
  unfold Builder.nots Builder.push
  simp only [List.filter_append, List.length_append, List.filter_cons, List.filter_nil]
  cases isNotOp g.op <;> simp

private lemma Builder.push_monos {n : ℕ} (B : Builder n) (g : Gate) (hfan hins) :
    (B.push g hfan hins).monos = B.monos + if isNotOp g.op = true then 0 else 1 := by
  unfold Builder.monos Builder.push
  simp only [List.filter_append, List.length_append, List.filter_cons, List.filter_nil]
  cases isNotOp g.op <;> simp

private def Builder.empty (n : ℕ) : Builder n :=
  { gates := [], fan := (fun _ h => by cases h), rb := (fun _ h => by simp at h) }

private lemma Builder.eval_inp {n : ℕ} (B : Builder n) (inp : List Bool)
    (hinp : inp.length = n + 2) (w : ℕ) (hw : w < n + 2) :
    B.eval inp w = inp.getD w false := by
  unfold Builder.eval Builder.toCircuit Circuit.wires
  exact wires_foldl_getD_lt B.gates inp w (by omega)

private def Extends {n : ℕ} (B1 B2 : Builder n) : Prop :=
  B1.gates.length ≤ B2.gates.length ∧
    ∀ inp, inp.length = n + 2 → ∀ w < n + 2 + B1.gates.length, B2.eval inp w = B1.eval inp w

private lemma Extends.refl {n : ℕ} (B : Builder n) : Extends B B :=
  ⟨le_refl _, fun _ _ _ _ => rfl⟩

private lemma Extends.trans {n : ℕ} {B1 B2 B3 : Builder n}
    (h12 : Extends B1 B2) (h23 : Extends B2 B3) : Extends B1 B3 :=
  ⟨le_trans h12.1 h23.1, fun inp hinp w hw =>
    (h23.2 inp hinp w (by have := h12.1; omega)).trans (h12.2 inp hinp w hw)⟩

private lemma Extends.push {n : ℕ} (B : Builder n) (g : Gate) (hfan hins) :
    Extends B (B.push g hfan hins) :=
  ⟨by simp [Builder.push], fun inp hinp w hw => B.eval_push_old g hfan hins inp hinp w hw⟩

private def pushAnd {n : ℕ} (B : Builder n) (a b : ℕ)
    (ha : a < n + 2 + B.gates.length) (hb : b < n + 2 + B.gates.length) : Builder n × ℕ :=
  (B.push ⟨GateOp.and, [a, b]⟩ ⟨Or.inl rfl, by simp⟩
    (fun i hi => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with rfl | rfl <;> assumption),
   n + 2 + B.gates.length)

private lemma pushAnd_spec {n : ℕ} (B : Builder n) (a b : ℕ)
    (ha : a < n + 2 + B.gates.length) (hb : b < n + 2 + B.gates.length) :
    Extends B (pushAnd B a b ha hb).1 ∧
    (pushAnd B a b ha hb).2 < n + 2 + (pushAnd B a b ha hb).1.gates.length ∧
    (pushAnd B a b ha hb).1.nots = B.nots ∧
    (pushAnd B a b ha hb).1.monos = B.monos + 1 ∧
    ∀ inp, inp.length = n + 2 →
      (pushAnd B a b ha hb).1.eval inp (pushAnd B a b ha hb).2 = (B.eval inp a && B.eval inp b) := by
  dsimp only [pushAnd]
  refine ⟨Extends.push B _ _ _, by simp [Builder.push], by rw [Builder.push_nots]; rfl,
    by rw [Builder.push_monos]; rfl, fun inp hinp => ?_⟩
  rw [Builder.eval_push_new B _ _ _ inp hinp]
  simp [GateOp.eval]

private def pushOr {n : ℕ} (B : Builder n) (a b : ℕ)
    (ha : a < n + 2 + B.gates.length) (hb : b < n + 2 + B.gates.length) : Builder n × ℕ :=
  (B.push ⟨GateOp.or, [a, b]⟩ ⟨Or.inr (Or.inl rfl), by simp⟩
    (fun i hi => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with rfl | rfl <;> assumption),
   n + 2 + B.gates.length)

private lemma pushOr_spec {n : ℕ} (B : Builder n) (a b : ℕ)
    (ha : a < n + 2 + B.gates.length) (hb : b < n + 2 + B.gates.length) :
    Extends B (pushOr B a b ha hb).1 ∧
    (pushOr B a b ha hb).2 < n + 2 + (pushOr B a b ha hb).1.gates.length ∧
    (pushOr B a b ha hb).1.nots = B.nots ∧
    (pushOr B a b ha hb).1.monos = B.monos + 1 ∧
    ∀ inp, inp.length = n + 2 →
      (pushOr B a b ha hb).1.eval inp (pushOr B a b ha hb).2 = (B.eval inp a || B.eval inp b) := by
  dsimp only [pushOr]
  refine ⟨Extends.push B _ _ _, by simp [Builder.push], by rw [Builder.push_nots]; rfl,
    by rw [Builder.push_monos]; rfl, fun inp hinp => ?_⟩
  rw [Builder.eval_push_new B _ _ _ inp hinp]
  simp [GateOp.eval]

private def pushNot {n : ℕ} (B : Builder n) (a : ℕ) (ha : a < n + 2 + B.gates.length) :
    Builder n × ℕ :=
  (B.push ⟨GateOp.not, [a]⟩ ⟨Or.inr (Or.inr rfl), by simp⟩
    (fun i hi => by simp only [List.mem_singleton] at hi; subst hi; exact ha),
   n + 2 + B.gates.length)

private lemma pushNot_spec {n : ℕ} (B : Builder n) (a : ℕ) (ha : a < n + 2 + B.gates.length) :
    Extends B (pushNot B a ha).1 ∧
    (pushNot B a ha).2 < n + 2 + (pushNot B a ha).1.gates.length ∧
    (pushNot B a ha).1.nots = B.nots + 1 ∧
    (pushNot B a ha).1.monos = B.monos ∧
    ∀ inp, inp.length = n + 2 →
      (pushNot B a ha).1.eval inp (pushNot B a ha).2 = !(B.eval inp a) := by
  dsimp only [pushNot]
  refine ⟨Extends.push B _ _ _, by simp [Builder.push], by rw [Builder.push_nots]; rfl,
    by rw [Builder.push_monos]; rfl, fun inp hinp => ?_⟩
  rw [Builder.eval_push_new B _ _ _ inp hinp]; rfl

private lemma exists_or_list {n : ℕ} (ws : List ℕ) :
    ∀ (B : Builder n), (∀ w ∈ ws, w < n + 2 + B.gates.length) →
      ∃ (B' : Builder n) (out : ℕ),
        Extends B B' ∧ out < n + 2 + B'.gates.length ∧
        B'.nots = B.nots ∧ B'.monos ≤ B.monos + ws.length ∧
        ∀ inp, inp.length = n + 2 → inp.getD n false = false →
          B'.eval inp out = ws.any (B.eval inp) := by
  induction ws with
  | nil =>
    intro B _
    refine ⟨B, n, Extends.refl B, by omega, rfl, by simp, ?_⟩
    intro inp hinp hn0
    rw [B.eval_inp inp hinp n (by omega), hn0]; rfl
  | cons w rest ih =>
    intro B hws
    cases rest with
    | nil =>
      refine ⟨B, w, Extends.refl B, hws w (List.mem_cons_self ..), rfl, by simp, ?_⟩
      intro _ _ _; simp
    | cons w2 rest2 =>
      rcases ih B (fun u hu => hws u (List.mem_cons_of_mem w hu)) with
        ⟨B1, out1, hE1, hlt1, hn1, hm1, hev1⟩
      have hw1 : w < n + 2 + B1.gates.length := by
        have := hws w (List.mem_cons_self ..); have := hE1.1; omega
      set rO := pushOr B1 w out1 hw1 hlt1
      have hsO := pushOr_spec B1 w out1 hw1 hlt1
      refine ⟨rO.1, rO.2, hE1.trans hsO.1, hsO.2.1, by rw [hsO.2.2.1, hn1],
        by rw [hsO.2.2.2.1]; simp only [List.length_cons] at hm1 ⊢; omega, ?_⟩
      intro inp hinp hn0
      rw [hsO.2.2.2.2 inp hinp, hE1.2 inp hinp w (hws w (List.mem_cons_self ..)),
        hev1 inp hinp hn0]
      simp [List.any_cons]

private lemma exists_and_list {n : ℕ} (ws : List ℕ) :
    ∀ (B : Builder n), (∀ w ∈ ws, w < n + 2 + B.gates.length) →
      ∃ (B' : Builder n) (out : ℕ),
        Extends B B' ∧ out < n + 2 + B'.gates.length ∧
        B'.nots = B.nots ∧ B'.monos ≤ B.monos + ws.length ∧
        ∀ inp, inp.length = n + 2 → inp.getD (n + 1) false = true →
          B'.eval inp out = ws.all (B.eval inp) := by
  induction ws with
  | nil =>
    intro B _
    refine ⟨B, n + 1, Extends.refl B, by omega, rfl, by simp, ?_⟩
    intro inp hinp hn1
    rw [B.eval_inp inp hinp (n + 1) (by omega), hn1]; rfl
  | cons w rest ih =>
    intro B hws
    cases rest with
    | nil =>
      refine ⟨B, w, Extends.refl B, hws w (List.mem_cons_self ..), rfl, by simp, ?_⟩
      intro _ _ _; simp
    | cons w2 rest2 =>
      rcases ih B (fun u hu => hws u (List.mem_cons_of_mem w hu)) with
        ⟨B1, out1, hE1, hlt1, hn1, hm1, hev1⟩
      have hw1 : w < n + 2 + B1.gates.length := by
        have := hws w (List.mem_cons_self ..); have := hE1.1; omega
      set rA := pushAnd B1 w out1 hw1 hlt1
      have hsA := pushAnd_spec B1 w out1 hw1 hlt1
      refine ⟨rA.1, rA.2, hE1.trans hsA.1, hsA.2.1, by rw [hsA.2.2.1, hn1],
        by rw [hsA.2.2.2.1]; simp only [List.length_cons] at hm1 ⊢; omega, ?_⟩
      intro inp hinp hn1
      rw [hsA.2.2.2.2 inp hinp, hE1.2 inp hinp w (hws w (List.mem_cons_self ..)),
        hev1 inp hinp hn1]
      simp [List.all_cons]

-- =========================================================================
-- Part 2: Binary head-bit helpers
-- =========================================================================

private def bitAt (v s : ℕ) : Bool := decide ((v / 2 ^ s) % 2 = 1)

private lemma div_pow_succ_eq (v s : ℕ) :
    v / 2 ^ s = 2 * (v / 2 ^ (s + 1)) + (v / 2 ^ s) % 2 := by
  have hdiv : v / 2 ^ (s + 1) = (v / 2 ^ s) / 2 := by
    rw [pow_succ, Nat.div_div_eq_div_mul]
  rw [hdiv]
  omega

private lemma bitAt_mono_of_prefix {a b s : ℕ} (hab : a ≤ b)
    (hpref : a / 2 ^ (s + 1) = b / 2 ^ (s + 1)) (ha : bitAt a s = true) :
    bitAt b s = true := by
  have hle : a / 2 ^ s ≤ b / 2 ^ s := Nat.div_le_div_right hab
  have ha1 : (a / 2 ^ s) % 2 = 1 := by simpa [bitAt] using ha
  have h1 := div_pow_succ_eq a s
  have h2 := div_pow_succ_eq b s
  have hb1 : (b / 2 ^ s) % 2 = 1 := by omega
  simp [bitAt, hb1]

private lemma prefix_step_eq {a b s : ℕ} (hab : a ≤ b)
    (hpref : a / 2 ^ (s + 1) = b / 2 ^ (s + 1))
    (himp : bitAt a s = false → bitAt b s = false) :
    a / 2 ^ s = b / 2 ^ s := by
  have hle : a / 2 ^ s ≤ b / 2 ^ s := Nat.div_le_div_right hab
  have h1 := div_pow_succ_eq a s
  have h2 := div_pow_succ_eq b s
  by_cases ha : (a / 2 ^ s) % 2 = 1
  · omega
  · have ha0 : bitAt a s = false := by simp [bitAt, ha]
    have hb0 : bitAt b s = false := himp ha0
    have hbn : (b / 2 ^ s) % 2 ≠ 1 := by simpa [bitAt] using hb0
    omega

-- =========================================================================
-- Part 3: Greedy state construction and circuit realization
-- =========================================================================

private def beforeSt {t : ℕ} (a b : ℕ × Finset (Fin t)) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ⊆ b.2)

private lemma beforeSt_refl {t : ℕ} (a : ℕ × Finset (Fin t)) : beforeSt a a :=
  Or.inr ⟨rfl, Finset.Subset.refl _⟩

private lemma beforeSt_trans {t : ℕ} {a b c : ℕ × Finset (Fin t)}
    (hab : beforeSt a b) (hbc : beforeSt b c) : beforeSt a c := by
  rcases hab with h1 | ⟨h1, hs1⟩ <;> rcases hbc with h2 | ⟨h2, hs2⟩
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inr ⟨by omega, Finset.Subset.trans hs1 hs2⟩

private lemma beforeSt_antisymm {t : ℕ} {a b : ℕ × Finset (Fin t)}
    (hab : beforeSt a b) (hba : beforeSt b a) : a = b := by
  rcases a with ⟨a1, a2⟩; rcases b with ⟨b1, b2⟩
  rcases hab with h1 | ⟨h1, hs1⟩ <;> rcases hba with h2 | ⟨h2, hs2⟩
  · omega
  · omega
  · omega
  · exact Prod.ext h1 (Finset.Subset.antisymm hs1 hs2)

private lemma inf'_mem_of_inter_closed {t : ℕ} (Ai : Finset (Finset (Fin t)))
    (hinter : ∀ a b, a ∈ Ai → b ∈ Ai → a ∩ b ∈ Ai)
    (S : Finset (Finset (Fin t))) (hS : S.Nonempty) (hsub : S ⊆ Ai) :
    S.inf' hS id ∈ Ai := by
  induction hS using Finset.Nonempty.cons_induction with
  | singleton a =>
    simpa using hsub (Finset.mem_singleton_self a)
  | cons a s ha hs ih =>
    rw [Finset.inf'_cons]
    have ha_mem : a ∈ Ai := hsub (Finset.mem_cons_self a s)
    have hs_mem : s.inf' hs id ∈ Ai :=
      ih (fun u hu => hsub (Finset.mem_cons_of_mem hu))
    exact hinter a (s.inf' hs id) ha_mem hs_mem

private lemma strict_card_lt {n m : ℕ} {x : Fin m → Finset (Fin n)}
    (hx : Function.Injective x) {j i : Fin m} (hne : j ≠ i) (hsub : x j ⊆ x i) :
    (x j).card < (x i).card := by
  apply Finset.card_lt_card
  exact Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq => hne (hx heq)⟩

private lemma lib1301_core (n m t : ℕ) (x : Fin m → Finset (Fin n))
    (A : Fin m → Finset (Finset (Fin t)))
    (hx : Function.Injective x) (hAne : ∀ i, (A i).Nonempty)
    (hAinter : ∀ i a b, a ∈ A i → b ∈ A i → a ∩ b ∈ A i) :
    let st := ℕ × Finset (Fin t)
    let before := @beforeSt t
    let candidate := fun (g : Fin m → st) (i : Fin m) (b : st) =>
      b.2 ∈ A i ∧ ∀ j, j ≠ i → x j ⊆ x i → before (g j) b
    let greedy := fun (g : Fin m → st) => ∀ i,
      candidate g i (g i) ∧ ∀ b, candidate g i b → before (g i) b
    let fit := fun (r : ℕ) (C : Circuit) (tap : Fin t → ℕ) =>
      FanInTwo C ∧ ReadsBack (n + 2) C ∧
      C.output < n + 2 + C.size ∧ (∀ a, tap a < n + 2 + C.size) ∧ notCount C ≤ r ∧
      ∀ i, (Finset.univ.filter (fun a =>
        (C.wires (List.ofFn (fun j : Fin n => decide (j ∈ x i)) ++ [false, true])).getD (tap a) false = true)) ∈ A i
    (∃! g, greedy g) ∧ ∀ g, greedy g →
      (∀ i, (g i).1 ≤ (x i).card) ∧
      (∀ h, (∀ i, candidate h i (h i)) → ∀ i, before (g i) (h i)) ∧
      ∀ r, ((∃ C tap, fit r C tap) ↔ ∀ i, (g i).1 < 2 ^ r) ∧
        ((∀ i, (g i).1 < 2 ^ r) → ∃ C tap, fit r C tap ∧ C.size ≤ m * (n + 2 * r + t) + r ∧
          ∀ i a, (C.wires (List.ofFn (fun j : Fin n => decide (j ∈ x i)) ++ [false, true])).getD (tap a) false =
            decide (a ∈ (g i).2)) := by
  intro st before candidate greedy fit
  have huniq : ∀ g1 g2, greedy g1 → greedy g2 → g1 = g2 := by
    intro g1 g2 hg1 hg2
    funext i
    have hcard_ind : ∀ c (i : Fin m), (x i).card = c → g1 i = g2 i := by
      intro c
      induction c using Nat.strong_induction_on with
      | _ c ih =>
        intro i hci
        have hcand_iff : ∀ b, candidate g1 i b ↔ candidate g2 i b := by
          intro b
          refine and_congr_right fun _ => forall_congr' fun j => forall_congr' fun hne => forall_congr' fun hsub => ?_
          have hlt := strict_card_lt hx hne hsub
          rw [ih (x j).card (by omega) j rfl]
        have h12 : before (g1 i) (g2 i) := (hg1 i).2 (g2 i) ((hcand_iff (g2 i)).mpr (hg2 i).1)
        have h21 : before (g2 i) (g1 i) := (hg2 i).2 (g1 i) ((hcand_iff (g1 i)).mp (hg1 i).1)
        exact beforeSt_antisymm h12 h21
    exact hcard_ind (x i).card i rfl
  have hexist : ∃ g, greedy g := by
    have hstep : ∀ k, ∃ g : Fin m → st, ∀ i, (x i).card < k →
        candidate g i (g i) ∧ ∀ b, candidate g i b → before (g i) b := by
      intro k
      induction k with
      | zero =>
        exact ⟨fun _ => (0, ∅), fun i hi => by omega⟩
      | succ k ih =>
        rcases ih with ⟨g, hg⟩
        let nextVal : Fin m → st := fun i =>
          if (x i).card < k then g i
          else
            let P : Finset (Fin m) := Finset.univ.filter (fun j => j ≠ i ∧ x j ⊆ x i)
            if hP : P.Nonempty then
              let L := P.sup' hP (fun j => (g j).1)
              let U := (P.filter (fun j => (g j).1 = L)).biUnion (fun j => (g j).2)
              let S := (A i).filter (fun w => U ⊆ w)
              if hS : S.Nonempty then (L, S.inf' hS id)
              else (L + 1, (A i).inf' (hAne i) id)
            else (0, (A i).inf' (hAne i) id)
        have hnext_lt : ∀ j, (x j).card < k → nextVal j = g j := fun j hj => by
          simp only [nextVal, if_pos hj]
        refine ⟨nextVal, fun i hi => ?_⟩
        by_cases hik : (x i).card < k
        · have hcand_eq : ∀ b, candidate nextVal i b ↔ candidate g i b := by
            intro b
            refine and_congr_right fun _ => forall_congr' fun j => forall_congr' fun hne => forall_congr' fun hsub => ?_
            have hlt := strict_card_lt hx hne hsub
            rw [hnext_lt j (by omega)]
          rw [hnext_lt i hik]
          exact ⟨(hcand_eq _).mpr (hg i hik).1, fun b hb => (hg i hik).2 b ((hcand_eq b).mp hb)⟩
        · have hcard_eq : (x i).card = k := by omega
          have hpred_eq : ∀ j, j ≠ i → x j ⊆ x i → nextVal j = g j := by
            intro j hne hsub
            exact hnext_lt j (by have := strict_card_lt hx hne hsub; omega)
          let P : Finset (Fin m) := Finset.univ.filter (fun j => j ≠ i ∧ x j ⊆ x i)
          have hmemP : ∀ j, j ∈ P ↔ j ≠ i ∧ x j ⊆ x i := by simp [P]
          by_cases hP : P.Nonempty
          · set L := P.sup' hP (fun j => (g j).1)
            set U := (P.filter (fun j => (g j).1 = L)).biUnion (fun j => (g j).2)
            set S := (A i).filter (fun w => U ⊆ w)
            by_cases hS : S.Nonempty
            · have hni : nextVal i = (L, S.inf' hS id) := by
                simp only [nextVal, if_neg hik]
                dsimp only [P, L, U, S]
                rw [dif_pos hP, dif_pos hS]
              rw [hni]
              constructor
              · refine ⟨inf'_mem_of_inter_closed (A i) (hAinter i) S hS (Finset.filter_subset _ _), ?_⟩
                intro j hne hsub
                rw [hpred_eq j hne hsub]
                have hjP : j ∈ P := (hmemP j).mpr ⟨hne, hsub⟩
                have hjle : (g j).1 ≤ L := Finset.le_sup' (fun u => (g u).1) hjP
                rcases lt_or_eq_of_le hjle with hlt | heq
                · exact Or.inl hlt
                · right
                  refine ⟨heq, Finset.Subset.trans ?_ (Finset.le_inf' hS _ fun w hw => (Finset.mem_filter.mp hw).2)⟩
                  exact Finset.subset_biUnion_of_mem (fun u => (g u).2) (Finset.mem_filter.mpr ⟨hjP, heq⟩)
              · intro b ⟨hbA, hbpred⟩
                have hLle : L ≤ b.1 := by
                  apply Finset.sup'_le hP
                  intro j hjP
                  rcases (hmemP j).mp hjP with ⟨hne, hsub⟩
                  have hbj := hbpred j hne hsub
                  rw [hpred_eq j hne hsub] at hbj
                  rcases hbj with hlt | ⟨heq, _⟩ <;> omega
                rcases lt_or_eq_of_le hLle with hlt | heq
                · exact Or.inl hlt
                · right
                  refine ⟨heq, Finset.inf'_le id (Finset.mem_filter.mpr ⟨hbA, ?_⟩)⟩
                  rw [Finset.biUnion_subset]
                  intro j hjF
                  rcases Finset.mem_filter.mp hjF with ⟨hjP, hjL⟩
                  rcases (hmemP j).mp hjP with ⟨hne, hsub⟩
                  have hbj := hbpred j hne hsub
                  rw [hpred_eq j hne hsub] at hbj
                  rcases hbj with hlt | ⟨_, hsub2⟩
                  · omega
                  · exact hsub2
            · have hni : nextVal i = (L + 1, (A i).inf' (hAne i) id) := by
                simp only [nextVal, if_neg hik]
                dsimp only [P, L, U, S]
                rw [dif_pos hP, dif_neg hS]
              rw [hni]
              constructor
              · refine ⟨inf'_mem_of_inter_closed (A i) (hAinter i) (A i) (hAne i) (Finset.Subset.refl _), ?_⟩
                intro j hne hsub
                rw [hpred_eq j hne hsub]
                have hjP : j ∈ P := (hmemP j).mpr ⟨hne, hsub⟩
                have hjle : (g j).1 ≤ L := Finset.le_sup' (fun u => (g u).1) hjP
                exact Or.inl (by omega)
              · intro b ⟨hbA, hbpred⟩
                have hLle : L ≤ b.1 := by
                  apply Finset.sup'_le hP
                  intro j hjP
                  rcases (hmemP j).mp hjP with ⟨hne, hsub⟩
                  have hbj := hbpred j hne hsub
                  rw [hpred_eq j hne hsub] at hbj
                  rcases hbj with hlt | ⟨heq, _⟩ <;> omega
                have hbne : b.1 ≠ L := by
                  intro hbe
                  apply hS
                  refine ⟨b.2, Finset.mem_filter.mpr ⟨hbA, ?_⟩⟩
                  rw [Finset.biUnion_subset]
                  intro j hjF
                  rcases Finset.mem_filter.mp hjF with ⟨hjP, hjL⟩
                  rcases (hmemP j).mp hjP with ⟨hne, hsub⟩
                  have hbj := hbpred j hne hsub
                  rw [hpred_eq j hne hsub] at hbj
                  rcases hbj with hlt | ⟨_, hsub2⟩
                  · omega
                  · exact hsub2
                have hL1le : L + 1 ≤ b.1 := by omega
                rcases lt_or_eq_of_le hL1le with hlt | heq
                · exact Or.inl hlt
                · exact Or.inr ⟨heq, Finset.inf'_le id hbA⟩
          · have hni : nextVal i = (0, (A i).inf' (hAne i) id) := by
              simp only [nextVal, if_neg hik]
              rw [dif_neg hP]
            rw [hni]
            constructor
            · refine ⟨inf'_mem_of_inter_closed (A i) (hAinter i) (A i) (hAne i) (Finset.Subset.refl _), ?_⟩
              intro j hne hsub
              exact absurd ⟨j, (hmemP j).mpr ⟨hne, hsub⟩⟩ hP
            · intro b ⟨hbA, _⟩
              rcases Nat.eq_zero_or_pos b.1 with hb0 | hbpos
              · exact Or.inr ⟨hb0.symm, Finset.inf'_le id hbA⟩
              · exact Or.inl hbpos
    rcases hstep (n + 1) with ⟨g, hg⟩
    refine ⟨g, fun i => hg i ?_⟩
    have hle : (x i).card ≤ n := by
      have := Finset.card_le_univ (x i)
      simpa using this
    omega
  refine ⟨?_, ?_⟩
  · rcases hexist with ⟨g, hg⟩
    exact ⟨g, hg, fun g' hg' => huniq g' g hg' hg⟩
  · intro g hg
    have hcard_bound : ∀ i, (g i).1 ≤ (x i).card := by
      have hind : ∀ c (i : Fin m), (x i).card = c → (g i).1 ≤ c := by
        intro c
        induction c using Nat.strong_induction_on with
        | _ c ih =>
          intro i hci
          rcases hAne i with ⟨w0, hw0⟩
          have hcand : candidate g i (c, w0) := by
            refine ⟨hw0, fun j hne hsub => ?_⟩
            have hlt := strict_card_lt hx hne hsub
            have hjle := ih (x j).card (by omega) j rfl
            exact Or.inl (by omega)
          rcases (hg i).2 (c, w0) hcand with hlt | ⟨heq, _⟩ <;> omega
      exact fun i => hind (x i).card i rfl
    have hleast : ∀ h, (∀ i, candidate h i (h i)) → ∀ i, before (g i) (h i) := by
      intro h hh
      have hind : ∀ c (i : Fin m), (x i).card = c → before (g i) (h i) := by
        intro c
        induction c using Nat.strong_induction_on with
        | _ c ih =>
          intro i hci
          have hcand : candidate g i (h i) := by
            refine ⟨(hh i).1, fun j hne hsub => ?_⟩
            have hlt := strict_card_lt hx hne hsub
            exact beforeSt_trans (ih (x j).card (by omega) j rfl) ((hh i).2 j hne hsub)
          exact (hg i).2 (h i) hcand
      exact fun i => hind (x i).card i rfl
    have hrealize : ∀ r, (∀ i, (g i).1 < 2 ^ r) →
        ∃ C tap, fit r C tap ∧ C.size ≤ m * (n + 2 * r + t) + r ∧
          ∀ i a, (C.wires (List.ofFn (fun j : Fin n => decide (j ∈ x i)) ++ [false, true])).getD (tap a) false =
            decide (a ∈ (g i).2) := by
      intro r hlt_pow
      let inpOf : Fin m → List Bool := fun k => List.ofFn (fun j : Fin n => decide (j ∈ x k)) ++ [false, true]
      have hinp_spec : ∀ k : Fin m,
          (inpOf k).length = n + 2 ∧ (inpOf k).getD n false = false ∧
          (inpOf k).getD (n + 1) false = true ∧
          ∀ j : Fin n, (inpOf k).getD j.val false = decide (j ∈ x k) := by
        intro k
        refine ⟨by simp [inpOf], by simp [inpOf, List.getD_eq_getElem?_getD],
          by simp [inpOf, List.getD_eq_getElem?_getD], fun j => ?_⟩
        simp only [inpOf, List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by simp : j.val < (List.ofFn (fun j : Fin n => decide (j ∈ x k))).length),
          List.getElem?_ofFn, dite_eq_left j.isLt, Option.getD_some]
      have hmono_lvl : ∀ i k : Fin m, x i ⊆ x k → (g i).1 ≤ (g k).1 := by
        intro i k hsub
        by_cases hik : i = k
        · subst hik; exact le_rfl
        · rcases (hg k).1.2 i hik hsub with hlt | ⟨heq, _⟩ <;> omega
      -- Stage 0: mask indicators ind0 i computing decide (x i ⊆ x k)
      have hstage0 : ∀ (p : ℕ) (hp : p ≤ m),
          ∃ (Bp : Builder n) (ind0 : Fin p → ℕ),
            (∀ i, ind0 i < n + 2 + Bp.gates.length) ∧
            Bp.nots = 0 ∧ Bp.monos ≤ p * n ∧
            ∀ (k : Fin m) (i : Fin p),
              Bp.eval (inpOf k) (ind0 i) = decide (x ⟨i.val, by have := i.isLt; omega⟩ ⊆ x k) := by
        intro p
        induction p with
        | zero =>
          intro _
          exact ⟨Builder.empty n, fun i => Fin.elim0 i, fun i => Fin.elim0 i, rfl, by simp [Builder.empty, Builder.monos],
            fun _ i => Fin.elim0 i⟩
        | succ p ih =>
          intro hp
          rcases ih (by omega) with ⟨Bp, ind0, hlt0, hn0, hm0, hev0⟩
          let ip : Fin m := ⟨p, by omega⟩
          let ws : List ℕ := ((List.finRange n).filter (fun j => decide (j ∈ x ip))).map Fin.val
          have hws_len : ws.length ≤ n := by
            calc ws.length = ((List.finRange n).filter (fun j => decide (j ∈ x ip))).length := by simp [ws]
              _ ≤ (List.finRange n).length := List.length_filter_le _ _
              _ = n := List.length_finRange
          have hws_lt : ∀ w ∈ ws, w < n + 2 + Bp.gates.length := by
            intro w hw
            rcases List.mem_map.mp hw with ⟨j, _, rfl⟩
            omega
          rcases exists_and_list ws Bp hws_lt with ⟨Bp', outp, hEp, hltp, hnp, hmp, hevp⟩
          let ind' : Fin (p + 1) → ℕ := fun i => if hi : i.val < p then ind0 ⟨i.val, hi⟩ else outp
          refine ⟨Bp', ind', ?_, by rw [hnp, hn0], ?_, ?_⟩
          · intro i; dsimp only [ind']; split_ifs with hi
            · have := hlt0 ⟨i.val, hi⟩; have := hEp.1; omega
            · exact hltp
          · have hmul : (p + 1) * n = p * n + n := by ring
            omega
          · intro k i
            have hk := hinp_spec k
            dsimp only [ind']; split_ifs with hi
            · rw [hEp.2 (inpOf k) hk.1 _ (hlt0 ⟨i.val, hi⟩), hev0 k ⟨i.val, hi⟩]
            · have hip : (⟨i.val, by omega⟩ : Fin m) = ip := by ext; dsimp [ip]; omega
              rw [hip, hevp (inpOf k) hk.1 hk.2.2.1, Bool.eq_iff_iff, decide_eq_true_eq]
              simp only [ws, List.all_eq_true, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
                decide_eq_true_eq]
              constructor
              · intro hall j hj
                have hval := hall j.val ⟨j, hj, rfl⟩
                rw [Bp.eval_inp (inpOf k) hk.1 j.val (by omega), hk.2.2.2 j, decide_eq_true_eq] at hval
                exact hval
              · rintro hsub w ⟨j, hj, rfl⟩
                rw [Bp.eval_inp (inpOf k) hk.1 j.val (by omega), hk.2.2.2 j, decide_eq_true_eq]
                exact hsub hj
      rcases hstage0 m le_rfl with ⟨B0, ind0, hlt0, hn0, hm0, hev0⟩
      -- Stages d = 0 .. r: update indicators with 1 NOT per stage
      have hstages : ∀ d ≤ r,
          ∃ (Bd : Builder n) (ind : Fin m → ℕ),
            (∀ i, ind i < n + 2 + Bd.gates.length) ∧
            Bd.nots = d ∧ Bd.monos ≤ m * n + 2 * m * d ∧
            ∀ (k i : Fin m),
              Bd.eval (inpOf k) (ind i) = decide (x i ⊆ x k ∧ (g i).1 / 2 ^ (r - d) = (g k).1 / 2 ^ (r - d)) := by
        intro d
        induction d with
        | zero =>
          intro _
          refine ⟨B0, ind0, hlt0, hn0, by simpa using hm0, fun k i => ?_⟩
          rw [hev0 k i]
          have h1 : (g i).1 / 2 ^ r = 0 := Nat.div_eq_of_lt (hlt_pow i)
          have h2 : (g k).1 / 2 ^ r = 0 := Nat.div_eq_of_lt (hlt_pow k)
          simp [h1, h2]
        | succ d ih =>
          intro hd
          rcases ih (by omega) with ⟨Bd, ind, hltd, hnd, hmd, hevd⟩
          set s := r - 1 - d
          have hs1 : r - d = s + 1 := by omega
          have hs0 : r - (d + 1) = s := by omega
          let posList : List ℕ := ((List.finRange m).filter (fun i => bitAt (g i).1 s)).map ind
          have hpos_len : posList.length ≤ m := by
            calc posList.length = ((List.finRange m).filter (fun i => bitAt (g i).1 s)).length := by simp [posList]
              _ ≤ (List.finRange m).length := List.length_filter_le _ _
              _ = m := List.length_finRange
          have hpos_lt : ∀ w ∈ posList, w < n + 2 + Bd.gates.length := by
            intro w hw
            rcases List.mem_map.mp hw with ⟨i, _, rfl⟩
            exact hltd i
          rcases exists_or_list posList Bd hpos_lt with ⟨Bor, inW, hEor, hltIn, hnOr, hmOr, hevOr⟩
          have hinW_val : ∀ k : Fin m, Bor.eval (inpOf k) inW = bitAt (g k).1 s := by
            intro k
            have hk := hinp_spec k
            rw [hevOr (inpOf k) hk.1 hk.2.1, Bool.eq_iff_iff]
            simp only [posList, List.any_eq_true, List.mem_map, List.mem_filter, List.mem_finRange, true_and]
            constructor
            · rintro ⟨w, ⟨i, hbi, rfl⟩, hev⟩
              rw [hevd k i, decide_eq_true_eq, hs1] at hev
              exact bitAt_mono_of_prefix (hmono_lvl i k hev.1) hev.2 hbi
            · intro hbk
              refine ⟨ind k, ⟨k, hbk, rfl⟩, ?_⟩
              rw [hevd k k, decide_eq_true_eq]
              exact ⟨Finset.Subset.refl _, rfl⟩
          set rNot := pushNot Bor inW hltIn
          have hsNot := pushNot_spec Bor inW hltIn
          have hEnot : Extends Bd rNot.1 := hEor.trans hsNot.1
          have hnot_val : ∀ k : Fin m, rNot.1.eval (inpOf k) rNot.2 = !(bitAt (g k).1 s) := by
            intro k
            rw [hsNot.2.2.2.2 (inpOf k) (hinp_spec k).1, hinW_val k]
          -- Update each indicator: if bitAt (g i).1 s = false then AND(ind i, notW) else ind i
          have hupd : ∀ (p : ℕ) (hp : p ≤ m),
              ∃ (Bp : Builder n) (ind' : Fin p → ℕ),
                Extends rNot.1 Bp ∧ (∀ i, ind' i < n + 2 + Bp.gates.length) ∧
                Bp.nots = rNot.1.nots ∧ Bp.monos ≤ rNot.1.monos + p ∧
                ∀ (k : Fin m) (i : Fin p),
                  let im : Fin m := ⟨i.val, by have := i.isLt; omega⟩
                  Bp.eval (inpOf k) (ind' i) =
                    decide (x im ⊆ x k ∧ (g im).1 / 2 ^ s = (g k).1 / 2 ^ s) := by
            intro p
            induction p with
            | zero =>
              intro _
              exact ⟨rNot.1, fun i => Fin.elim0 i, Extends.refl _, fun i => Fin.elim0 i, rfl, by simp,
                fun _ i => Fin.elim0 i⟩
            | succ p ihp =>
              intro hp
              rcases ihp (by omega) with ⟨Bp, ind', hEp, hltp, hnp, hmp, hevp⟩
              let ip : Fin m := ⟨p, by omega⟩
              have hind_lt : ind ip < n + 2 + Bp.gates.length := by
                have := hltd ip; have := hEnot.1; have := hEp.1; omega
              have hnot_lt : rNot.2 < n + 2 + Bp.gates.length := by
                have h1 : rNot.2 < n + 2 + rNot.1.gates.length := hsNot.2.1
                have := hEp.1; omega
              by_cases hbit : bitAt (g ip).1 s = false
              · set rA := pushAnd Bp (ind ip) rNot.2 hind_lt hnot_lt
                have hsA := pushAnd_spec Bp (ind ip) rNot.2 hind_lt hnot_lt
                have hEA : Extends Bp rA.1 := hsA.1
                let ind'' : Fin (p + 1) → ℕ := fun i => if hi : i.val < p then ind' ⟨i.val, hi⟩ else rA.2
                refine ⟨rA.1, ind'', hEp.trans hEA, ?_, by rw [hsA.2.2.1, hnp],
                  by rw [hsA.2.2.2.1]; omega, ?_⟩
                · intro i; dsimp only [ind'']; split_ifs with hi
                  · have := hltp ⟨i.val, hi⟩; have := hEA.1; omega
                  · exact hsA.2.1
                · intro k i
                  have hk := hinp_spec k
                  dsimp only [ind'']; split_ifs with hi
                  · rw [hsA.1.2 (inpOf k) hk.1 _ (hltp ⟨i.val, hi⟩)]
                    exact hevp k ⟨i.val, hi⟩
                  · have hip : (⟨i.val, by omega⟩ : Fin m) = ip := by ext; dsimp [ip]; omega
                    rw [hip, hsA.2.2.2.2 (inpOf k) hk.1, (hEnot.trans hEp).2 (inpOf k) hk.1 _ (hltd ip),
                      hEp.2 (inpOf k) hk.1 _ hsNot.2.1, hevd k ip, hnot_val k, hs1, Bool.eq_iff_iff]
                    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
                    constructor
                    · rintro ⟨⟨hsub, hpref⟩, hbk0⟩
                      exact ⟨hsub, prefix_step_eq (hmono_lvl ip k hsub) hpref (fun _ => hbk0)⟩
                    · rintro ⟨hsub, hdiv⟩
                      have hpref : (g ip).1 / 2 ^ (s + 1) = (g k).1 / 2 ^ (s + 1) := by
                        rw [pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hdiv]
                      have hbk0 : bitAt (g k).1 s = false := by
                        unfold bitAt at hbit ⊢
                        rw [← hdiv]; exact hbit
                      exact ⟨⟨hsub, hpref⟩, hbk0⟩
              · have hbit1 : bitAt (g ip).1 s = true := Bool.eq_true_of_not_eq_false hbit
                let ind'' : Fin (p + 1) → ℕ := fun i => if hi : i.val < p then ind' ⟨i.val, hi⟩ else ind ip
                refine ⟨Bp, ind'', hEp, ?_, hnp, by omega, ?_⟩
                · intro i; dsimp only [ind'']; split_ifs with hi
                  · exact hltp ⟨i.val, hi⟩
                  · exact hind_lt
                · intro k i
                  have hk := hinp_spec k
                  dsimp only [ind'']; split_ifs with hi
                  · exact hevp k ⟨i.val, hi⟩
                  · have hip : (⟨i.val, by omega⟩ : Fin m) = ip := by ext; dsimp [ip]; omega
                    rw [hip, (hEnot.trans hEp).2 (inpOf k) hk.1 _ (hltd ip), hevd k ip, hs1, Bool.eq_iff_iff]
                    simp only [decide_eq_true_eq]
                    constructor
                    · rintro ⟨hsub, hpref⟩
                      exact ⟨hsub, prefix_step_eq (hmono_lvl ip k hsub) hpref (fun h => by rw [hbit1] at h; cases h)⟩
                    · rintro ⟨hsub, hdiv⟩
                      refine ⟨hsub, ?_⟩
                      rw [pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hdiv]
          rcases hupd m le_rfl with ⟨Bnext, indNext, hEnext, hltNext, hnNext, hmNext, hevNext⟩
          refine ⟨Bnext, indNext, hltNext, ?_, ?_, fun k i => ?_⟩
          · rw [hnNext, hsNot.2.2.1, hnOr, hnd]
          · have hm_not : rNot.1.monos = Bor.monos := hsNot.2.2.2.1
            have hmul : 2 * m * (d + 1) = 2 * m * d + m + m := by ring
            omega
          · rw [hs0]
            exact hevNext k i
      rcases hstages r le_rfl with ⟨Br, indR, hltr, hnr, hmr, hevr⟩
      -- Final stage: for each a : Fin t, tap a = OR of indR i for i with a ∈ (g i).2
      have htaps : ∀ (p : ℕ) (hp : p ≤ t),
          ∃ (Bp : Builder n) (tap : Fin p → ℕ),
            Extends Br Bp ∧ (∀ a, tap a < n + 2 + Bp.gates.length) ∧
            Bp.nots = Br.nots ∧ Bp.monos ≤ Br.monos + p * m ∧
            ∀ (k : Fin m) (a : Fin p),
              Bp.eval (inpOf k) (tap a) = decide ((⟨a.val, by have := a.isLt; omega⟩ : Fin t) ∈ (g k).2) := by
        intro p
        induction p with
        | zero =>
          intro _
          exact ⟨Br, fun a => Fin.elim0 a, Extends.refl Br, fun a => Fin.elim0 a, rfl, by simp,
            fun _ a => Fin.elim0 a⟩
        | succ p ih =>
          intro hp
          rcases ih (by omega) with ⟨Bp, tap, hEp, hltp, hnp, hmp, hevp⟩
          let ap : Fin t := ⟨p, by omega⟩
          let ws : List ℕ := ((List.finRange m).filter (fun i => decide (ap ∈ (g i).2))).map indR
          have hws_len : ws.length ≤ m := by
            calc ws.length = ((List.finRange m).filter (fun i => decide (ap ∈ (g i).2))).length := by simp [ws]
              _ ≤ (List.finRange m).length := List.length_filter_le _ _
              _ = m := List.length_finRange
          have hws_lt : ∀ w ∈ ws, w < n + 2 + Bp.gates.length := by
            intro w hw
            rcases List.mem_map.mp hw with ⟨i, _, rfl⟩
            have := hltr i; have := hEp.1; omega
          rcases exists_or_list ws Bp hws_lt with ⟨Bp', outp, hE1, hlt1, hn1, hm1, hev1⟩
          let tap' : Fin (p + 1) → ℕ := fun a => if ha : a.val < p then tap ⟨a.val, ha⟩ else outp
          refine ⟨Bp', tap', hEp.trans hE1, ?_, by rw [hn1, hnp], ?_, ?_⟩
          · intro a; dsimp only [tap']; split_ifs with ha
            · have := hltp ⟨a.val, ha⟩; have := hE1.1; omega
            · exact hlt1
          · have hmul : (p + 1) * m = p * m + m := by ring
            omega
          · intro k a
            have hk := hinp_spec k
            dsimp only [tap']; split_ifs with ha
            · rw [hE1.2 (inpOf k) hk.1 _ (hltp ⟨a.val, ha⟩)]
              exact hevp k ⟨a.val, ha⟩
            · have hap : (⟨a.val, by omega⟩ : Fin t) = ap := by ext; dsimp [ap]; omega
              rw [hap, hev1 (inpOf k) hk.1 hk.2.1, Bool.eq_iff_iff, decide_eq_true_eq]
              simp only [ws, List.any_eq_true, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
                decide_eq_true_eq]
              constructor
              · rintro ⟨w, ⟨i, hai, rfl⟩, hev⟩
                rw [hEp.2 (inpOf k) hk.1 _ (hltr i), hevr k i, Nat.sub_self, pow_zero, Nat.div_one,
                  Nat.div_one, decide_eq_true_eq] at hev
                by_cases hik : i = k
                · subst hik; exact hai
                · rcases (hg k).1.2 i hik hev.1 with hlt | ⟨_, hsub2⟩
                  · omega
                  · exact hsub2 hai
              · intro hak
                refine ⟨indR k, ⟨k, hak, rfl⟩, ?_⟩
                rw [hEp.2 (inpOf k) hk.1 _ (hltr k), hevr k k, decide_eq_true_eq]
                exact ⟨Finset.Subset.refl _, rfl⟩
      rcases htaps t le_rfl with ⟨Bfin, tap, hEfin, hltFin, hnFin, hmFin, hevFin⟩
      refine ⟨Bfin.toCircuit 0, tap, ?_, ?_, fun i a => hevFin i a⟩
      · refine ⟨Bfin.toCircuit_fanInTwo 0, Bfin.rb, by dsimp [Builder.toCircuit]; omega, hltFin,
          by rw [← Bfin.nots_eq_notCount 0, hnFin, hnr], fun i => ?_⟩
        have hfilt : Finset.univ.filter (fun a => ((Bfin.toCircuit 0).wires (inpOf i)).getD (tap a) false = true) =
            (g i).2 := by
          ext a
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          change Bfin.eval (inpOf i) (tap a) = true ↔ a ∈ (g i).2
          rw [hevFin i a, decide_eq_true_eq]
        rw [hfilt]
        exact (hg i).1.1
      · change Bfin.gates.length ≤ m * (n + 2 * r + t) + r
        rw [Bfin.gates_len_eq, hnFin, hnr]
        have hmul : m * (n + 2 * r + t) = m * n + 2 * m * r + t * m := by ring
        omega
    refine ⟨hcard_bound, hleast, fun r => ⟨?_, hrealize r⟩⟩
    constructor
    · rintro ⟨C, tap, hfan, hrb, hout, htap_lt, hnot_le, hA_ok⟩ i
      let inpOf : Fin m → List Bool := fun k => List.ofFn (fun j : Fin n => decide (j ∈ x k)) ++ [false, true]
      let h : Fin m → st := fun k =>
        (2 ^ notCount C - 1 - notVal n C (inpOf k),
         Finset.univ.filter (fun a => (C.wires (inpOf k)).getD (tap a) false = true))
      have hcand : ∀ k, candidate h k (h k) := by
        intro k
        refine ⟨hA_ok k, fun j hne hsub => ?_⟩
        have hle : ∀ u < n + 2, (inpOf j).getD u false = true → (inpOf k).getD u false = true := by
          intro u hu hv
          by_cases hun : u < n
          · have hjv : (inpOf j).getD u false = decide ((⟨u, hun⟩ : Fin n) ∈ x j) := by
              simp only [inpOf, List.getD_eq_getElem?_getD,
                List.getElem?_append_left (by simp; omega : u < (List.ofFn (fun l : Fin n => decide (l ∈ x j))).length),
                List.getElem?_ofFn, dite_eq_left hun, Option.getD_some]
            have hkv : (inpOf k).getD u false = decide ((⟨u, hun⟩ : Fin n) ∈ x k) := by
              simp only [inpOf, List.getD_eq_getElem?_getD,
                List.getElem?_append_left (by simp; omega : u < (List.ofFn (fun l : Fin n => decide (l ∈ x k))).length),
                List.getElem?_ofFn, dite_eq_left hun, Option.getD_some]
            rw [hjv, decide_eq_true_eq] at hv
            rw [hkv, decide_eq_true_eq]
            exact hsub hv
          · have hu1 : u = n ∨ u = n + 1 := by omega
            rcases hu1 with rfl | rfl <;> simpa [inpOf, List.getD_eq_getElem?_getD] using hv
        have hanti := notVal_anti C hfan hrb (inpOf j) (inpOf k) (by simp [inpOf]) (by simp [inpOf]) hle
        have hlt_j := notVal_lt n C (inpOf j)
        have hlt_k := notVal_lt n C (inpOf k)
        rcases hanti with hlt | ⟨heq, hmono⟩
        · exact Or.inl (by dsimp only [h]; omega)
        · right
          refine ⟨by dsimp only [h]; omega, fun a ha => ?_⟩
          simp only [h, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
          exact hmono (tap a) (htap_lt a) ha
      have hbi := hleast h hcand i
      have hlt_i := notVal_lt n C (inpOf i)
      have hpow_le : 2 ^ notCount C ≤ 2 ^ r := Nat.pow_le_pow_right (by omega) hnot_le
      have hpow_pos : 1 ≤ 2 ^ notCount C := Nat.one_le_pow _ _ (by omega)
      rcases hbi with hlt | ⟨heq, _⟩ <;> dsimp only [h] at * <;> omega
    · intro hlt_pow
      rcases hrealize r hlt_pow with ⟨C, tap, hfit, _, _⟩
      exact ⟨C, tap, hfit⟩

private lemma input_congr_dec {n : ℕ} (s : Finset (Fin n))
    (d1 d2 : ∀ j : Fin n, Decidable (j ∈ s)) :
    (List.ofFn (fun j : Fin n => @decide (j ∈ s) (d1 j)) ++ [false, true]) =
    (List.ofFn (fun j : Fin n => @decide (j ∈ s) (d2 j)) ++ [false, true]) := by
  have hd : d1 = d2 := funext fun j => Subsingleton.elim _ _
  rw [hd]

private lemma filter_congr_dec {α : Type*} (s : Finset α) (P : α → Prop)
    (d1 d2 : DecidablePred P) :
    @Finset.filter α P d1 s = @Finset.filter α P d2 s := by
  ext a; simp only [Finset.mem_filter]


-- =========================================================================
-- Part 4: Two-tap forcing witness bound 3*(2^h - 1) and compactness
-- =========================================================================

private lemma exists_min_card {n m : ℕ} (x : Fin m → Finset (Fin n))
    (P : Fin m → Prop) (hP : ∃ k, P k) :
    ∃ k, P k ∧ ∀ j, P j → (x k).card ≤ (x j).card := by
  let S : Finset (Fin m) := Finset.univ.filter P
  have hS : S.Nonempty := by
    rcases hP with ⟨k, hk⟩
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩⟩
  rcases Finset.exists_min_image S (fun k => (x k).card) hS with ⟨k, hkS, hkmin⟩
  refine ⟨k, (Finset.mem_filter.mp hkS).2, fun j hj => ?_⟩
  exact hkmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)

private lemma fin2_cases_eq (a : Fin 2) :
    ∃ b : Fin 2, b ≠ a ∧ ∀ c : Fin 2, c = a ∨ c = b := by
  refine ⟨⟨1 - a.val, by omega⟩, ?_, ?_⟩
  · intro h; have := congrArg Fin.val h; dsimp only at this; omega
  · intro c
    have ha := a.isLt; have hc := c.isLt
    by_cases h : c.val = a.val
    · left; exact Fin.ext h
    · right; exact Fin.ext (by dsimp only; omega)

private lemma main_core (n m : ℕ) (x : Fin m → Finset (Fin n))
    (A : Fin m → Finset (Finset (Fin 2)))
    (hx : Function.Injective x) (hAne : ∀ i, (A i).Nonempty)
    (hAinter : ∀ i u v, u ∈ A i → v ∈ A i → u ∩ v ∈ A i) :
    let st := ℕ × Finset (Fin 2)
    let coherent := fun (S : Finset (Fin m)) (g : Fin m → st) =>
      (∀ i ∈ S, (g i).2 ∈ A i) ∧ ∀ i ∈ S, ∀ j ∈ S, x i ⊆ x j →
        (g i).1 < (g j).1 ∨ ((g i).1 = (g j).1 ∧ (g i).2 ⊆ (g j).2)
    let forces := fun (S : Finset (Fin m)) (i : Fin m) (h : ℕ) =>
      h = 0 ∨ ∀ g, coherent S g → ∃ j ∈ S, x j ⊆ x i ∧ h ≤ (g j).1
    let fits := fun (S : Finset (Fin m)) (r : ℕ) =>
      ∃ (C : Circuit) (tap : Fin 2 → ℕ),
        FanInTwo C ∧ ReadsBack (n + 2) C ∧
        C.output < n + 2 + C.size ∧ (∀ a, tap a < n + 2 + C.size) ∧ notCount C ≤ r ∧
        ∀ i ∈ S, (Finset.univ.filter (fun a =>
          (C.wires (List.ofFn (fun j : Fin n => decide (j ∈ x i)) ++ [false, true])).getD (tap a) false = true)) ∈ A i
    (∀ i h, forces Finset.univ i h ↔ ∃ S, (∀ j ∈ S, x j ⊆ x i) ∧
      S.card ≤ 3 * (2 ^ h - 1) ∧ forces S i h) ∧
      ∀ r, fits Finset.univ r ↔ ∀ S, S.card ≤ 3 * (2 ^ (2 ^ r) - 1) → fits S r := by
  intro st coherent forces fits
  rcases lib1301_core n m 2 x A hx hAne hAinter with ⟨⟨g, hg, _⟩, hall⟩
  dsimp only at hg hall
  rcases hall g hg with ⟨_, hleast, hreal⟩
  have hcoh_g : coherent Finset.univ g := by
    refine ⟨fun i _ => (hg i).1.1, fun i _ j _ hsub => ?_⟩
    by_cases hij : i = j
    · subst hij; exact beforeSt_refl (g i)
    · exact (hg j).1.2 i hij hsub
  have hleast_coh : ∀ g', coherent Finset.univ g' → ∀ i, beforeSt (g i) (g' i) := by
    intro g' hg'
    exact hleast g' (fun i => ⟨hg'.1 i (Finset.mem_univ i),
      fun j _ hsub => hg'.2 j (Finset.mem_univ j) i (Finset.mem_univ i) hsub⟩)
  have hforces_univ_iff : ∀ i h, forces Finset.univ i h ↔ h ≤ (g i).1 := by
    intro i h
    by_cases h0 : h = 0
    · subst h0; simp [forces]
    · constructor
      · intro hf
        rcases hf with rfl | hf'
        · exact absurd rfl h0
        · rcases hf' g hcoh_g with ⟨j, _, hsub, hle⟩
          rcases hcoh_g.2 j (Finset.mem_univ j) i (Finset.mem_univ i) hsub with hlt | ⟨heq, _⟩ <;> omega
      · intro hle
        right
        intro g' hg'
        refine ⟨i, Finset.mem_univ i, Finset.Subset.refl _, ?_⟩
        rcases hleast_coh g' hg' i with hlt | ⟨heq, _⟩ <;> omega
  let minA : Fin m → Finset (Fin 2) := fun j => (A j).inf' (hAne j) id
  have hminA_sub : ∀ j w, w ∈ A j → minA j ⊆ w := fun j w hw => Finset.inf'_le id hw
  have hminA_mem : ∀ j, minA j ∈ A j := fun j =>
    inf'_mem_of_inter_closed (A j) (hAinter j) (A j) (hAne j) (Finset.Subset.refl _)
  have hcoh_mono : ∀ S1 S2 g', S1 ⊆ S2 → coherent S2 g' → coherent S1 g' := by
    intro S1 S2 g' hsub ⟨h1, h2⟩
    exact ⟨fun i hi => h1 i (hsub hi), fun i hi j hj => h2 i (hsub hi) j (hsub hj)⟩
  have hforce_ge : ∀ S S' j h g', S' ⊆ S → j ∈ S → coherent S g' → forces S' j h → h ≤ (g' j).1 := by
    intro S S' j h g' hsub hjS hcoh hf
    rcases hf with rfl | hf'
    · omega
    · rcases hf' g' (hcoh_mono S' S g' hsub hcoh) with ⟨k, hkS', hkx, hkle⟩
      rcases hcoh.2 k (hsub hkS') j hjS hkx with hlt | ⟨heq, _⟩ <;> omega
  -- Main inductive witness construction: h <= (g i).1 -> exists S of card <= 3*(2^h - 1) forcing (i, h)
  have hbuild : ∀ h i, h ≤ (g i).1 →
      ∃ S : Finset (Fin m), (∀ j ∈ S, x j ⊆ x i) ∧ S.card ≤ 3 * (2 ^ h - 1) ∧ forces S i h := by
    intro h
    induction h with
    | zero =>
      intro i _
      exact ⟨∅, fun j hj => by simp at hj, by simp, Or.inl rfl⟩
    | succ h ih =>
      intro i hgi
      -- Pick minimal i0 with x i0 <= x i and h + 1 <= (g i0).1
      rcases exists_min_card x (fun k => x k ⊆ x i ∧ h + 1 ≤ (g k).1) ⟨i, Finset.Subset.refl _, hgi⟩ with
        ⟨i0, ⟨hi0_sub, hi0_ge⟩, hi0_min⟩
      have hpred_le : ∀ j, j ≠ i0 → x j ⊆ x i0 → (g j).1 ≤ h := by
        intro j hne hsub
        by_contra hgt
        have hlt := strict_card_lt hx hne hsub
        have hle := hi0_min j ⟨Finset.Subset.trans hsub hi0_sub, by omega⟩
        omega
      let Q : Finset (Fin m) := Finset.univ.filter (fun j => j ≠ i0 ∧ x j ⊆ x i0 ∧ (g j).1 = h)
      let U : Finset (Fin 2) := Q.biUnion (fun j => (g j).2)
      -- Claim A: no w in A i0 contains U
      have hno_sup : ∀ w ∈ A i0, ¬ U ⊆ w := by
        intro w hw hUw
        have hcand : (w ∈ A i0 ∧ ∀ j, j ≠ i0 → x j ⊆ x i0 → beforeSt (g j) (h, w)) := by
          refine ⟨hw, fun j hne hsub => ?_⟩
          have hjle := hpred_le j hne hsub
          rcases lt_or_eq_of_le hjle with hlt | heq
          · exact Or.inl hlt
          · right
            refine ⟨heq, Finset.Subset.trans ?_ hUw⟩
            exact Finset.subset_biUnion_of_mem (fun u => (g u).2)
              (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hne, hsub, heq⟩)
        rcases (hg i0).2 (h, w) hcand with hlt | ⟨heq, _⟩ <;> omega
      have hpow_step : 2 ^ (h + 1) = 2 * 2 ^ h := by rw [pow_succ]; ring
      have hpow_pos : 1 ≤ 2 ^ h := Nat.one_le_pow h 2 (by omega)
      by_cases hcase : ∀ a ∈ U, ∃ j ∈ Q, a ∈ minA j
      · -- Case 1: every a in U appears in minA j_a for some j_a in Q
        have hpart : ∀ a : Fin 2, ∃ P : Finset (Fin m),
            (∀ k ∈ P, x k ⊆ x i0) ∧ P.card ≤ 3 * (2 ^ h - 1) + 1 ∧
            (a ∈ U → ∀ S g', P ⊆ S → i0 ∈ S → coherent S g' → (g' i0).1 ≤ h → a ∈ (g' i0).2) := by
          intro a
          by_cases haU : a ∈ U
          · rcases hcase a haU with ⟨ja, hjaQ, ha_min⟩
            rcases Finset.mem_filter.mp hjaQ with ⟨_, _, hja_sub, hja_lvl⟩
            rcases ih ja (by omega) with ⟨Sa, hSa_sub, hSa_card, hSa_force⟩
            refine ⟨insert ja Sa, ?_, ?_, ?_⟩
            · intro k hk
              rcases Finset.mem_insert.mp hk with rfl | hkS
              · exact hja_sub
              · exact Finset.Subset.trans (hSa_sub k hkS) hja_sub
            · have := Finset.card_insert_le ja Sa; omega
            · intro _ S g' hPS hi0S hcoh hi0le
              have hjaS : ja ∈ S := hPS (Finset.mem_insert_self ja Sa)
              have hSaS : Sa ⊆ S := Finset.Subset.trans (Finset.subset_insert ja Sa) hPS
              have hge_ja := hforce_ge S Sa ja h g' hSaS hjaS hcoh hSa_force
              rcases hcoh.2 ja hjaS i0 hi0S hja_sub with hlt | ⟨_, hsub2⟩
              · omega
              · exact hsub2 (hminA_sub ja (g' ja).2 (hcoh.1 ja hjaS) ha_min)
          · exact ⟨∅, fun k hk => by simp at hk, by simp, fun ha => absurd ha haU⟩
        rcases hpart 0 with ⟨P0, hP0_sub, hP0_card, hP0_ok⟩
        rcases hpart 1 with ⟨P1, hP1_sub, hP1_card, hP1_ok⟩
        let S : Finset (Fin m) := insert i0 (P0 ∪ P1)
        refine ⟨S, ?_, ?_, ?_⟩
        · intro k hk
          rcases Finset.mem_insert.mp hk with rfl | hk01
          · exact hi0_sub
          · rcases Finset.mem_union.mp hk01 with hk0 | hk1
            · exact Finset.Subset.trans (hP0_sub k hk0) hi0_sub
            · exact Finset.Subset.trans (hP1_sub k hk1) hi0_sub
        · dsimp only [S]
          have h1 := Finset.card_insert_le i0 (P0 ∪ P1)
          have h2 := Finset.card_union_le P0 P1
          omega
        · right
          intro g' hcoh
          by_cases hge : h + 1 ≤ (g' i0).1
          · exact ⟨i0, Finset.mem_insert_self i0 _, hi0_sub, hge⟩
          · exfalso
            have hi0le : (g' i0).1 ≤ h := by omega
            have hi0S : i0 ∈ S := Finset.mem_insert_self i0 _
            have hP0S : P0 ⊆ S := Finset.Subset.trans Finset.subset_union_left (Finset.subset_insert i0 _)
            have hP1S : P1 ⊆ S := Finset.Subset.trans Finset.subset_union_right (Finset.subset_insert i0 _)
            have hUw : U ⊆ (g' i0).2 := by
              intro a haU
              have ha01 : a = 0 ∨ a = 1 := by
                have := a.isLt
                by_cases h0 : a.val = 0
                · left; exact Fin.ext h0
                · right; exact Fin.ext (by omega)
              rcases ha01 with rfl | rfl
              · exact hP0_ok haU S g' hP0S hi0S hcoh hi0le
              · exact hP1_ok haU S g' hP1S hi0S hcoh hi0le
            exact hno_sup (g' i0).2 (hcoh.1 i0 hi0S) hUw
      · -- Case 2: some a in U is missing from minA j for all j in Q
        have hex_miss : ∃ a ∈ U, ∀ j ∈ Q, a ∉ minA j := by
          by_contra hno; apply hcase; intro a haU
          by_contra hno2; exact hno ⟨a, haU, fun j hjQ hm => hno2 ⟨j, hjQ, hm⟩⟩
        rcases hex_miss with ⟨a, haU, ha_miss⟩
        rcases fin2_cases_eq a with ⟨b, hba, hab_all⟩
        have hex_ja : ∃ j, j ∈ Q ∧ a ∈ (g j).2 := by
          rcases Finset.mem_biUnion.mp haU with ⟨j, hjQ, haj⟩
          exact ⟨j, hjQ, haj⟩
        rcases exists_min_card x (fun j => j ∈ Q ∧ a ∈ (g j).2) hex_ja with ⟨ja, ⟨hjaQ, haja⟩, hja_min⟩
        rcases Finset.mem_filter.mp hjaQ with ⟨_, hja_ne, hja_sub, hja_lvl⟩
        let Qa : Finset (Fin m) := Finset.univ.filter (fun k => k ≠ ja ∧ x k ⊆ x ja ∧ (g k).1 = h)
        have hQa_in_Q : ∀ k ∈ Qa, k ∈ Q := by
          intro k hk
          rcases Finset.mem_filter.mp hk with ⟨_, hkne, hksub, hklvl⟩
          have hlt1 := strict_card_lt hx hkne hksub
          have hlt2 := strict_card_lt hx hja_ne hja_sub
          have hkne0 : k ≠ i0 := fun h => by subst h; omega
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ k, hkne0, Finset.Subset.trans hksub hja_sub, hklvl⟩
        have hQa_no_a : ∀ k ∈ Qa, a ∉ (g k).2 := by
          intro k hk hak
          rcases Finset.mem_filter.mp hk with ⟨_, hkne, hksub, _⟩
          have hlt := strict_card_lt hx hkne hksub
          have hle := hja_min k ⟨hQa_in_Q k hk, hak⟩
          omega
        -- Implication at ja: every w in A ja with b in w also has a in w
        have himp_ja : ∀ w ∈ A ja, b ∈ w → a ∈ w := by
          intro w hw hbw
          have hcand : w ∈ A ja ∧ ∀ k, k ≠ ja → x k ⊆ x ja → beforeSt (g k) (h, w) := by
            refine ⟨hw, fun k hkne hksub => ?_⟩
            have hlt1 := strict_card_lt hx hkne hksub
            have hlt2 := strict_card_lt hx hja_ne hja_sub
            have hkne0 : k ≠ i0 := fun h => by subst h; omega
            have hkle := hpred_le k hkne0 (Finset.Subset.trans hksub hja_sub)
            rcases lt_or_eq_of_le hkle with hlt | heq
            · exact Or.inl hlt
            · right
              refine ⟨heq, fun c hc => ?_⟩
              have hkQa : k ∈ Qa := Finset.mem_filter.mpr ⟨Finset.mem_univ k, hkne, hksub, heq⟩
              rcases hab_all c with rfl | rfl
              · exact absurd hc (hQa_no_a k hkQa)
              · exact hbw
          rcases (hg ja).2 (h, w) hcand with hlt | ⟨_, hsub2⟩
          · omega
          · exact hsub2 haja
        -- There exists k in Qa with b in (g k).2
        have hex_jb : ∃ k, k ∈ Qa ∧ b ∈ (g k).2 := by
          by_contra hno
          have hcand : minA ja ∈ A ja ∧ ∀ k, k ≠ ja → x k ⊆ x ja → beforeSt (g k) (h, minA ja) := by
            refine ⟨hminA_mem ja, fun k hkne hksub => ?_⟩
            have hlt1 := strict_card_lt hx hkne hksub
            have hlt2 := strict_card_lt hx hja_ne hja_sub
            have hkne0 : k ≠ i0 := fun h => by subst h; omega
            have hkle := hpred_le k hkne0 (Finset.Subset.trans hksub hja_sub)
            rcases lt_or_eq_of_le hkle with hlt | heq
            · exact Or.inl hlt
            · right
              refine ⟨heq, fun c hc => ?_⟩
              have hkQa : k ∈ Qa := Finset.mem_filter.mpr ⟨Finset.mem_univ k, hkne, hksub, heq⟩
              rcases hab_all c with rfl | rfl
              · exact absurd hc (hQa_no_a k hkQa)
              · exact absurd ⟨k, hkQa, hc⟩ hno
          rcases (hg ja).2 (h, minA ja) hcand with hlt | ⟨_, hsub2⟩
          · omega
          · exact ha_miss ja hjaQ (hsub2 haja)
        rcases exists_min_card x (fun k => k ∈ Qa ∧ b ∈ (g k).2) hex_jb with ⟨jb, ⟨hjbQa, hbjb⟩, hjb_min⟩
        rcases Finset.mem_filter.mp hjbQa with ⟨_, hjb_ne, hjb_sub, hjb_lvl⟩
        -- Prove b in minA jb
        have hb_min : b ∈ minA jb := by
          have hcand : minA jb ∈ A jb ∧ ∀ l, l ≠ jb → x l ⊆ x jb → beforeSt (g l) (h, minA jb) := by
            refine ⟨hminA_mem jb, fun l hlne hlsub => ?_⟩
            have hlt1 := strict_card_lt hx hlne hlsub
            have hlt2 := strict_card_lt hx hjb_ne hjb_sub
            have hlt3 := strict_card_lt hx hja_ne hja_sub
            have hlne_a : l ≠ ja := fun h => by subst h; omega
            have hlne_0 : l ≠ i0 := fun h => by subst h; omega
            have hlle := hpred_le l hlne_0 (Finset.Subset.trans (Finset.Subset.trans hlsub hjb_sub) hja_sub)
            rcases lt_or_eq_of_le hlle with hlt | heq
            · exact Or.inl hlt
            · right
              refine ⟨heq, fun c hc => ?_⟩
              have hlQa : l ∈ Qa := Finset.mem_filter.mpr ⟨Finset.mem_univ l, hlne_a, Finset.Subset.trans hlsub hjb_sub, heq⟩
              rcases hab_all c with rfl | rfl
              · exact absurd hc (hQa_no_a l hlQa)
              · have hle := hjb_min l ⟨hlQa, hc⟩; omega
          rcases (hg jb).2 (h, minA jb) hcand with hlt | ⟨_, hsub2⟩
          · omega
          · exact hsub2 hbjb
        -- Apply IH once at (jb, h)
        rcases ih jb (by omega) with ⟨Sb, hSb_sub, hSb_card, hSb_force⟩
        let S : Finset (Fin m) := insert i0 (insert ja (insert jb Sb))
        refine ⟨S, ?_, ?_, ?_⟩
        · intro k hk
          rcases Finset.mem_insert.mp hk with rfl | hk1
          · exact hi0_sub
          · rcases Finset.mem_insert.mp hk1 with rfl | hk2
            · exact Finset.Subset.trans hja_sub hi0_sub
            · rcases Finset.mem_insert.mp hk2 with rfl | hk3
              · exact Finset.Subset.trans (Finset.Subset.trans hjb_sub hja_sub) hi0_sub
              · exact Finset.Subset.trans (Finset.Subset.trans (Finset.Subset.trans (hSb_sub k hk3) hjb_sub) hja_sub) hi0_sub
        · dsimp only [S]
          have h1 := Finset.card_insert_le i0 (insert ja (insert jb Sb))
          have h2 := Finset.card_insert_le ja (insert jb Sb)
          have h3 := Finset.card_insert_le jb Sb
          omega
        · right
          intro g' hcoh
          by_cases hge : h + 1 ≤ (g' i0).1
          · exact ⟨i0, Finset.mem_insert_self i0 _, hi0_sub, hge⟩
          · exfalso
            have hi0S : i0 ∈ S := Finset.mem_insert_self i0 _
            have hjaS : ja ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_self ja _)
            have hjbS : jb ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self jb _))
            have hSbS : Sb ⊆ S := Finset.Subset.trans (Finset.subset_insert jb Sb)
              (Finset.Subset.trans (Finset.subset_insert ja _) (Finset.subset_insert i0 _))
            have hge_jb := hforce_ge S Sb jb h g' hSbS hjbS hcoh hSb_force
            have hba_ord := hcoh.2 jb hjbS ja hjaS hjb_sub
            have ha0_ord := hcoh.2 ja hjaS i0 hi0S hja_sub
            have hsub_ba : (g' jb).2 ⊆ (g' ja).2 := by
              rcases hba_ord with hlt | ⟨_, hs⟩
              · rcases ha0_ord with hlt2 | ⟨heq2, _⟩ <;> omega
              · exact hs
            have hsub_a0 : (g' ja).2 ⊆ (g' i0).2 := by
              rcases ha0_ord with hlt2 | ⟨_, hs⟩
              · rcases hba_ord with hlt | ⟨heq, _⟩ <;> omega
              · exact hs
            have hb_ja : b ∈ (g' ja).2 := hsub_ba (hminA_sub jb (g' jb).2 (hcoh.1 jb hjbS) hb_min)
            have ha_ja : a ∈ (g' ja).2 := himp_ja (g' ja).2 (hcoh.1 ja hjaS) hb_ja
            have hUw : U ⊆ (g' i0).2 := by
              intro c _
              rcases hab_all c with rfl | rfl
              · exact hsub_a0 ha_ja
              · exact hsub_a0 hb_ja
            exact hno_sup (g' i0).2 (hcoh.1 i0 hi0S) hUw
  -- Combine into the two conclusions of L-lib-1306
  constructor
  · intro i h
    constructor
    · intro hf
      exact hbuild h i ((hforces_univ_iff i h).mp hf)
    · rintro ⟨S, _, _, hfS⟩
      rcases hfS with rfl | hf'
      · exact Or.inl rfl
      · right
        intro g' hg'
        rcases hf' g' (hcoh_mono S Finset.univ g' (Finset.subset_univ S) hg') with ⟨j, _, hjx, hle⟩
        exact ⟨j, Finset.mem_univ j, hjx, hle⟩
  · intro r
    constructor
    · rintro ⟨C, tap, hfan, hrb, hout, htap_lt, hnot_le, hA_ok⟩ S _
      exact ⟨C, tap, hfan, hrb, hout, htap_lt, hnot_le, fun i _ => hA_ok i (Finset.mem_univ i)⟩
    · intro hallS
      have hfit_univ_iff : fits Finset.univ r ↔ ∀ i, (g i).1 < 2 ^ r := by
        have h1 := (hreal r).1
        constructor
        · rintro ⟨C, tap, hfan, hrb, hout, htap_lt, hnot_le, hA_ok⟩
          exact h1.mp ⟨C, tap, hfan, hrb, hout, htap_lt, hnot_le, fun i => hA_ok i (Finset.mem_univ i)⟩
        · intro hlt
          rcases h1.mpr hlt with ⟨C, tap, hfan, hrb, hout, htap_lt, hnot_le, hA_ok⟩
          exact ⟨C, tap, hfan, hrb, hout, htap_lt, hnot_le, fun i _ => hA_ok i⟩
      rw [hfit_univ_iff]
      intro i
      by_contra hge
      have hi_ge : 2 ^ r ≤ (g i).1 := by omega
      rcases hbuild (2 ^ r) i hi_ge with ⟨S, _, hScard, hSforce⟩
      rcases hallS S hScard with ⟨C, tap, hfan, hrb, hout, htap_lt, hnot_le, hA_ok⟩
      let inpOf : Fin m → List Bool := fun k => List.ofFn (fun j : Fin n => decide (j ∈ x k)) ++ [false, true]
      let hC : Fin m → st := fun k =>
        (2 ^ notCount C - 1 - notVal n C (inpOf k),
         Finset.univ.filter (fun a => (C.wires (inpOf k)).getD (tap a) false = true))
      have hcoh_C : coherent S hC := by
        refine ⟨fun k hk => hA_ok k hk, fun j hj k hk hsub => ?_⟩
        have hle : ∀ u < n + 2, (inpOf j).getD u false = true → (inpOf k).getD u false = true := by
          intro u hu hv
          by_cases hun : u < n
          · have hjv : (inpOf j).getD u false = decide ((⟨u, hun⟩ : Fin n) ∈ x j) := by
              simp only [inpOf, List.getD_eq_getElem?_getD,
                List.getElem?_append_left (by simp; omega : u < (List.ofFn (fun l : Fin n => decide (l ∈ x j))).length),
                List.getElem?_ofFn, dite_eq_left hun, Option.getD_some]
            have hkv : (inpOf k).getD u false = decide ((⟨u, hun⟩ : Fin n) ∈ x k) := by
              simp only [inpOf, List.getD_eq_getElem?_getD,
                List.getElem?_append_left (by simp; omega : u < (List.ofFn (fun l : Fin n => decide (l ∈ x k))).length),
                List.getElem?_ofFn, dite_eq_left hun, Option.getD_some]
            rw [hjv, decide_eq_true_eq] at hv
            rw [hkv, decide_eq_true_eq]
            exact hsub hv
          · have hu1 : u = n ∨ u = n + 1 := by omega
            rcases hu1 with rfl | rfl <;> simp [inpOf, List.getD_eq_getElem?_getD] at hv ⊢
        have hanti := notVal_anti C hfan hrb (inpOf j) (inpOf k) (by simp [inpOf]) (by simp [inpOf]) hle
        have hlt_j := notVal_lt n C (inpOf j)
        have hlt_k := notVal_lt n C (inpOf k)
        rcases hanti with hlt | ⟨heq, hmono⟩
        · exact Or.inl (by dsimp only [hC]; omega)
        · right
          refine ⟨by dsimp only [hC]; omega, fun a ha => ?_⟩
          simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
          exact hmono (tap a) (htap_lt a) ha
      have hpow_pos : 1 ≤ 2 ^ r := Nat.one_le_pow r 2 (by omega)
      rcases hSforce with h0 | hf'
      · omega
      · rcases hf' hC hcoh_C with ⟨j, _, _, hjle⟩
        have hlt_j := notVal_lt n C (inpOf j)
        have hpow_le : 2 ^ notCount C ≤ 2 ^ r := Nat.pow_le_pow_right (by omega) hnot_le
        have hpow_posC : 1 ≤ 2 ^ notCount C := Nat.one_le_pow _ _ (by omega)
        dsimp only [hC] at hjle
        omega

private lemma inter_congr_aux {t : ℕ} (Ai : Finset (Finset (Fin t)))
    (h : ∀ a b, a ∈ Ai → b ∈ Ai → ∀ c : Finset (Fin t), (∀ u, u ∈ c ↔ u ∈ a ∧ u ∈ b) → c ∈ Ai) :
    ∀ a b, a ∈ Ai → b ∈ Ai → a ∩ b ∈ Ai :=
  fun a b ha hb => h a b ha hb (a ∩ b) (fun _ => Finset.mem_inter)

private lemma main_aux :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    ∀ (n m : Nat) (x : Fin m → Finset (Fin n)) (A : Fin m → Finset (Finset (Fin 2))),
      Function.Injective x → (∀ i, (A i).Nonempty) →
      (∀ i u v, u ∈ A i → v ∈ A i → u ∩ v ∈ A i) →
      let st := Nat × Finset (Fin 2)
      let coherent := fun (S : Finset (Fin m)) (g : Fin m → st) =>
        (∀ i ∈ S, (g i).2 ∈ A i) ∧ ∀ i ∈ S, ∀ j ∈ S, x i ⊆ x j →
          (g i).1 < (g j).1 ∨ ((g i).1 = (g j).1 ∧ (g i).2 ⊆ (g j).2)
      let forces := fun (S : Finset (Fin m)) (i : Fin m) (h : Nat) =>
        h = 0 ∨ ∀ g, coherent S g → ∃ j ∈ S, x j ⊆ x i ∧ h ≤ (g j).1
      let fits := fun (S : Finset (Fin m)) (r : Nat) =>
        ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin 2 → Nat),
          PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
          C.output < n+2+C.size ∧ (∀ a, tap a < n+2+C.size) ∧ PEqualNP.NotBracket.notCount C ≤ r ∧
          ∀ i ∈ S, (Finset.univ.filter (fun a =>
            (C.wires (List.ofFn (fun j : Fin n => decide (j ∈ x i)) ++ [false,true])).getD (tap a) false = true)) ∈ A i
      (∀ i h, forces Finset.univ i h ↔ ∃ S, (∀ j ∈ S, x j ⊆ x i) ∧
        S.card ≤ 3*(2^h-1) ∧ forces S i h) ∧
        ∀ r, fits Finset.univ r ↔ ∀ S, S.card ≤ 3*(2^(2^r)-1) → fits S r := by
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  intro n m x A hx hAne hAinter st coherent forces fits
  have hAinter' := fun i => inter_congr_aux (A i) (fun a b ha hb c hc => by
    have heq : c = a ∩ b := by ext u; rw [hc u, Finset.mem_inter]
    rw [heq]; exact hAinter i a b ha hb)
  rcases main_core n m x A hx hAne hAinter' with ⟨h1, h2⟩
  dsimp only at h1 h2
  have hfits_iff : ∀ S r, fits S r ↔
      (∃ (C : Circuit) (tap : Fin 2 → ℕ),
        FanInTwo C ∧ ReadsBack (n + 2) C ∧
        C.output < n + 2 + C.size ∧ (∀ a, tap a < n + 2 + C.size) ∧ notCount C ≤ r ∧
        ∀ i ∈ S, (@Finset.filter (Fin 2)
          (fun a => (C.wires (List.ofFn (fun j : Fin n => @decide (j ∈ x i) (@Finset.decidableMem (Fin n) (instDecidableEqFin n) j (x i))) ++ [false, true])).getD (tap a) false = true)
          (fun a => instDecidableEqBool _ _) Finset.univ) ∈ A i) := by
    intro S r
    dsimp only [fits]
    refine exists_congr fun C => exists_congr fun tap =>
      and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
      and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun i => forall_congr' fun _ => ?_
    rw [input_congr_dec (x i) (fun j => Classical.propDecidable (j ∈ x i))
      (fun j => @Finset.decidableMem (Fin n) (instDecidableEqFin n) j (x i))]
    rw [filter_congr_dec Finset.univ _ (fun a => Classical.propDecidable _) (fun a => instDecidableEqBool _ _)]
  refine ⟨h1, fun r => ?_⟩
  rw [hfits_iff Finset.univ r]
  constructor
  · intro hf S hSc
    exact (hfits_iff S r).mpr ((h2 r).mp hf S hSc)
  · intro hallS
    exact (h2 r).mpr (fun S hSc => (hfits_iff S r).mp (hallS S hSc))

end PEqualNP.Outside.L_lib_1312_aux


namespace PEqualNP.Outside.L_lib_1312_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket

-- =========================================================================
-- Dual circuit: swap AND/OR, swap the two constant wires
-- =========================================================================

def swc (n i : ℕ) : ℕ := if i = n then n + 1 else if i = n + 1 then n else i

lemma swc_lt {n i b : ℕ} (hi : i < b) (hb : n + 2 ≤ b) : swc n i < b := by
  unfold swc; split_ifs <;> omega

lemma swc_ge {n i : ℕ} (hi : n + 2 ≤ i) : swc n i = i := by
  unfold swc; split_ifs <;> omega

def dualGate (n : ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.and => ⟨GateOp.or, g.inputs.map (swc n)⟩
  | GateOp.or => ⟨GateOp.and, g.inputs.map (swc n)⟩
  | GateOp.not => ⟨GateOp.not, [swc n (g.inputs.headD n)]⟩
  | _ => g

def dualC (n : ℕ) (C : Circuit) : Circuit := ⟨C.gates.map (dualGate n), C.output⟩

lemma dualC_size (n : ℕ) (C : Circuit) : (dualC n C).size = C.size := by
  simp [Circuit.size, dualC]

lemma dualC_gates_length (n : ℕ) (C : Circuit) : (dualC n C).gates.length = C.gates.length := by
  simp [dualC]

lemma gateAt_dualC (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt (dualC n C) j = dualGate n (gateAt C j) := by
  simp only [gateAt, dualC, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some]

lemma dualGate_op_not (n : ℕ) (g : Gate) :
    (dualGate n g).op = GateOp.not ↔ g.op = GateOp.not := by
  rcases g with ⟨op, ins⟩
  cases op <;> simp [dualGate]

lemma dualC_fan (n : ℕ) (C : Circuit) (hfan : FanInTwo C) : FanInTwo (dualC n C) := by
  intro g hg
  simp only [dualC, List.mem_map] at hg
  rcases hg with ⟨g0, hg0, rfl⟩
  rcases hfan g0 hg0 with ⟨hop, hlen⟩
  rcases g0 with ⟨op, ins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with h | h | h <;> subst h <;> simp_all [dualGate]

lemma dualC_rb (n : ℕ) (C : Circuit) (hrb : ReadsBack (n + 2) C) :
    ReadsBack (n + 2) (dualC n C) := by
  intro j hj i hi
  rw [dualC_gates_length] at hj
  rw [gateAt_dualC n C j hj] at hi
  have hrbj := hrb j hj
  rcases hg : gateAt C j with ⟨op, ins⟩
  rw [hg] at hi hrbj
  cases op with
  | and =>
    simp only [dualGate, List.mem_map] at hi
    rcases hi with ⟨i0, hi0, rfl⟩
    exact swc_lt (hrbj i0 hi0) (by omega)
  | or =>
    simp only [dualGate, List.mem_map] at hi
    rcases hi with ⟨i0, hi0, rfl⟩
    exact swc_lt (hrbj i0 hi0) (by omega)
  | not =>
    simp only [dualGate, List.mem_singleton] at hi
    subst hi
    apply swc_lt _ (by omega)
    cases ins with
    | nil => show n < n + 2 + j; omega
    | cons a rest => simpa using hrbj a (by simp)
  | mod p => simpa [dualGate] using hrbj i hi
  | maj => simpa [dualGate] using hrbj i hi

lemma notCount_dualC (n : ℕ) (C : Circuit) : notCount (dualC n C) = notCount C := by
  unfold notCount
  simp only [dualC, List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro g _
  simp only [Function.comp_apply, decide_eq_decide]
  exact dualGate_op_not n g

lemma any_map_neg (l : List ℕ) (f g : ℕ → Bool) (h : ∀ i ∈ l, g i = !f i) :
    (l.map g).any id = !((l.map f).all id) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.any_cons, List.all_cons, id]
    rw [h a (by simp), ih (fun i hi => h i (by simp [hi]))]
    cases f a <;> simp

lemma all_map_neg (l : List ℕ) (f g : ℕ → Bool) (h : ∀ i ∈ l, g i = !f i) :
    (l.map g).all id = !((l.map f).any id) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.any_cons, List.all_cons, id]
    rw [h a (by simp), ih (fun i hi => h i (by simp [hi]))]
    cases f a <;> simp

lemma dual_wires (n : ℕ) (C : Circuit) (hfan : FanInTwo C) (hrb : ReadsBack (n + 2) C)
    (inp1 inp2 : List Bool) (hl1 : inp1.length = n + 2) (hl2 : inp2.length = n + 2)
    (hin : ∀ i < n + 2, inp2.getD (swc n i) false = !inp1.getD i false)
    (hn : inp1.getD n false = false) :
    ∀ w < n + 2 + C.size,
      ((dualC n C).wires inp2).getD (swc n w) false = !(C.wires inp1).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hlt : w < n + 2
    · unfold Circuit.wires
      rw [wires_foldl_getD_lt C.gates inp1 w (by omega)]
      rw [wires_foldl_getD_lt _ inp2 (swc n w) (by rw [hl2]; exact swc_lt hlt le_rfl)]
      exact hin w hlt
    · set j := w - (n + 2)
      have hj_len : j < C.gates.length := by
        have : C.size = C.gates.length := rfl
        omega
      have hw_eq : w = n + 2 + j := by omega
      rw [swc_ge (by omega : n + 2 ≤ w), hw_eq]
      have h1 := wires_getD_gate C inp1 j hj_len (by rw [hl1]; exact hrb)
      have h2 := wires_getD_gate (dualC n C) inp2 j (by rw [dualC_gates_length]; exact hj_len)
        (by rw [hl2]; exact dualC_rb n C hrb)
      rw [hl1] at h1; rw [hl2] at h2
      rw [h1, h2, gateAt_dualC n C j hj_len]
      have hrbj := hrb j hj_len
      have hg_mem : gateAt C j ∈ C.gates := by
        simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj_len, Option.getD_some]
        exact List.getElem_mem hj_len
      have hop := (hfan _ hg_mem).1
      have hIH : ∀ i ∈ (gateAt C j).inputs,
          ((dualC n C).wires inp2).getD (swc n i) false = !(C.wires inp1).getD i false := by
        intro i hi
        have := hrbj i hi
        exact ih i (by omega) (by omega)
      rcases hg : gateAt C j with ⟨op, ins⟩
      rw [hg] at hop hIH
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with h | h | h <;> subst h
      · simp only [dualGate, GateOp.eval, List.map_map]
        exact any_map_neg ins _ _ hIH
      · simp only [dualGate, GateOp.eval, List.map_map]
        exact all_map_neg ins _ _ hIH
      · simp only [dualGate, GateOp.eval, List.map_cons, List.map_nil, List.headD_cons]
        cases ins with
        | nil =>
          simp only [List.headD_nil, List.map_nil]
          have hn' := ih n (by omega) (by omega)
          rw [hn']
          unfold Circuit.wires
          rw [wires_foldl_getD_lt C.gates inp1 n (by omega), hn]
        | cons a rest =>
          simp only [List.headD_cons, List.map_cons]
          rw [hIH a (by simp)]


-- =========================================================================
-- The fence instance
-- =========================================================================

abbrev Pt (k D : ℕ) := Fin (k + 1) ⊕ (Fin k ⊕ (Fin k × Fin (2 * D)))

def rel {k D : ℕ} : Pt k D → Pt k D → Bool
  | Sum.inl i, Sum.inl i' => decide (i.val = i'.val)
  | Sum.inr (Sum.inl i), Sum.inl i' => decide (i'.val = i.val ∨ i'.val = i.val + 1)
  | Sum.inr (Sum.inl i), Sum.inr (Sum.inl i') => decide (i.val = i'.val)
  | Sum.inr (Sum.inr (i, _)), Sum.inl i' => decide (i'.val = i.val ∨ i'.val = i.val + 1)
  | Sum.inr (Sum.inr (i, _)), Sum.inr (Sum.inl i') => decide (i.val = i'.val)
  | Sum.inr (Sum.inr (i, s)), Sum.inr (Sum.inr (i', s')) => decide (i.val = i'.val ∧ s.val ≤ s'.val)
  | _, _ => false

lemma rel_refl {k D : ℕ} (p : Pt k D) : rel p p = true := by
  rcases p with i | i | ⟨i, s⟩ <;> simp [rel]

lemma rel_trans {k D : ℕ} (a b c : Pt k D) (h1 : rel a b = true) (h2 : rel b c = true) :
    rel a c = true := by
  rcases a with i | i | ⟨i, s⟩ <;> rcases b with j | j | ⟨j, t⟩ <;> rcases c with l | l | ⟨l, u⟩ <;>
    simp only [rel, decide_eq_true_eq, Bool.false_eq_true] at h1 h2 ⊢ <;> omega

lemma rel_antisymm {k D : ℕ} (a b : Pt k D) (h1 : rel a b = true) (h2 : rel b a = true) : a = b := by
  rcases a with i | i | ⟨i, s⟩ <;> rcases b with j | j | ⟨j, t⟩ <;>
    simp only [rel, decide_eq_true_eq, Bool.false_eq_true, Sum.inl.injEq, Sum.inr.injEq,
      Prod.mk.injEq, Fin.ext_iff, reduceCtorEq] at h1 h2 ⊢ <;> omega

def X {k D : ℕ} (q : Pt k D) : Finset (Pt k D) := Finset.univ.filter (fun z => rel z q = true)

lemma mem_X {k D : ℕ} (z q : Pt k D) : z ∈ X q ↔ rel z q = true := by simp [X]

lemma rel_of_X_sub {k D : ℕ} {p q : Pt k D} (h : X p ⊆ X q) : rel p q = true :=
  (mem_X p q).1 (h ((mem_X p p).2 (rel_refl p)))

lemma X_sub_of_rel {k D : ℕ} {p q : Pt k D} (h : rel p q = true) : X p ⊆ X q := fun z hz =>
  (mem_X z q).2 (rel_trans z p q ((mem_X z p).1 hz) h)

lemma X_inj {k D : ℕ} : Function.Injective (@X k D) := fun p q h =>
  rel_antisymm p q (rel_of_X_sub (by rw [h])) (rel_of_X_sub (by rw [h]))

def AT {k D : ℕ} (P Q : Finset (Finset (Fin 2))) : Pt k D → Finset (Finset (Fin 2))
  | Sum.inl i => if i.val = 0 then {{0}} else if i.val = k then {{1}} else Q
  | Sum.inr (Sum.inl _) => P
  | Sum.inr (Sum.inr (_, s)) => if s.val % 2 = 0 then {Finset.univ} else {∅}

def lab {k D : ℕ} (j : ℕ) : Pt k D → ℕ × Finset (Fin 2)
  | Sum.inl i => (D, if i.val < j then {0} else {1})
  | Sum.inr (Sum.inl i) => (D, if i.val < j then {0} else {1})
  | Sum.inr (Sum.inr (_, s)) => ((s.val + 1) / 2, if s.val % 2 = 0 then Finset.univ else ∅)

lemma bef_of_lt {a b : ℕ × Finset (Fin 2)} (h : a.1 < b.1) : beforeSt a b := Or.inl h

lemma bef_of_le_empty {a b : ℕ × Finset (Fin 2)} (h : a.1 ≤ b.1) (he : a.2 = ∅) : beforeSt a b := by
  rcases Nat.lt_or_ge a.1 b.1 with h1 | h1
  · exact Or.inl h1
  · exact Or.inr ⟨by omega, by rw [he]; exact Finset.empty_subset _⟩

lemma bef_of_eq_sub {a b : ℕ × Finset (Fin 2)} (h : a.1 = b.1) (hs : a.2 ⊆ b.2) : beforeSt a b :=
  Or.inr ⟨h, hs⟩

lemma lab_chain_bef {k D : ℕ} (j : ℕ) (i : Fin k) (s : Fin (2 * D)) (b : ℕ × Finset (Fin 2))
    (hb : (s.val + 1) / 2 ≤ b.1) (hb2 : s.val % 2 = 0 → (s.val + 1) / 2 < b.1) :
    beforeSt (lab (k := k) (D := D) j (Sum.inr (Sum.inr (i, s)))) b := by
  by_cases hs : s.val % 2 = 0
  · exact bef_of_lt (by simp only [lab]; exact hb2 hs)
  · exact bef_of_le_empty (by simp only [lab]; exact hb) (by simp [lab, hs])

lemma lab_words {k D : ℕ} (hk : 1 ≤ k) (P Q : Finset (Finset (Fin 2)))
    (hP0 : {0} ∈ P) (hP1 : {1} ∈ P) (hQ0 : {0} ∈ Q) (hQ1 : {1} ∈ Q)
    (j : Fin (k + 1)) (p : Pt k D) (hp : p ≠ Sum.inl j) :
    (lab j.val p).2 ∈ AT P Q p ∧ (lab j.val p).1 ≤ D := by
  rcases p with i | i | ⟨i, s⟩
  · have hij : i.val ≠ j.val := fun h => hp (by rw [Fin.ext h])
    have hi := i.isLt
    have hj := j.isLt
    simp only [lab, AT]
    refine ⟨?_, le_rfl⟩
    split_ifs <;> first | omega | simp_all
  · simp only [lab, AT]
    refine ⟨?_, le_rfl⟩
    split_ifs <;> assumption
  · simp only [lab, AT]
    have hs := s.isLt
    refine ⟨?_, by omega⟩
    split_ifs <;> simp

lemma lab_coh {k D : ℕ} (j : Fin (k + 1)) (p q : Pt k D) (hq : q ≠ Sum.inl j)
    (h : rel p q = true) : beforeSt (lab j.val p) (lab j.val q) := by
  rcases p with i | i | ⟨i, s⟩ <;> rcases q with i' | i' | ⟨i', s'⟩ <;>
    simp only [rel, decide_eq_true_eq, Bool.false_eq_true] at h
  · have : i = i' := Fin.ext h
    subst this; exact Or.inr ⟨rfl, subset_refl _⟩
  · have hij : i'.val ≠ j.val := fun h' => hq (by rw [Fin.ext h'])
    refine Or.inr ⟨by simp only [lab], ?_⟩
    simp only [lab]
    split_ifs with h1 h2 h2
    · exact subset_refl _
    · omega
    · omega
    · exact subset_refl _
  · have : i = i' := Fin.ext h
    subst this; exact Or.inr ⟨rfl, subset_refl _⟩
  · have hs := s.isLt
    apply lab_chain_bef
    · simp only [lab]; omega
    · intro h2; simp only [lab]; omega
  · have hs := s.isLt
    apply lab_chain_bef
    · simp only [lab]; omega
    · intro h2; simp only [lab]; omega
  · rcases h with ⟨h1, h2⟩
    have : i = i' := Fin.ext h1
    subst this
    rcases Nat.lt_or_ge s.val s'.val with hlt | hge
    · apply lab_chain_bef
      · simp only [lab]; omega
      · intro h3; simp only [lab]; omega
    · have : s = s' := Fin.ext (by omega)
      subst this; exact Or.inr ⟨rfl, subset_refl _⟩

lemma fin2_eq_singleton0 (w : Finset (Fin 2)) (h0 : (0 : Fin 2) ∈ w) (hu : w ≠ Finset.univ) :
    w = {0} := by
  have h1 : (1 : Fin 2) ∉ w := by
    intro h1; apply hu; ext b; fin_cases b <;> simp [h0, h1]
  ext b; fin_cases b <;> simp [h0, h1]

lemma infeas {k D : ℕ} (hk : 1 ≤ k) (P Q : Finset (Finset (Fin 2))) (hPe : ∅ ∉ P)
    (hQu : Finset.univ ∉ Q)
    (g : Pt k D → ℕ × Finset (Fin 2)) (hw : ∀ p, (g p).2 ∈ AT P Q p) (hl : ∀ p, (g p).1 ≤ D)
    (hc : ∀ p q, rel p q = true → beforeSt (g p) (g q)) : False := by
  have hchain : ∀ (i : Fin k) (s : ℕ) (hs : s < 2 * D),
      (s + 1) / 2 ≤ (g (Sum.inr (Sum.inr (i, ⟨s, hs⟩)))).1 := by
    intro i s
    induction s with
    | zero => intro hs; simp
    | succ s ih =>
      intro hs
      have ih' := ih (by omega)
      have hb := hc (Sum.inr (Sum.inr (i, ⟨s, by omega⟩))) (Sum.inr (Sum.inr (i, ⟨s + 1, hs⟩)))
        (by simp [rel])
      have hw1 := hw (Sum.inr (Sum.inr (i, ⟨s, by omega⟩)))
      have hw2 := hw (Sum.inr (Sum.inr (i, ⟨s + 1, hs⟩)))
      simp only [AT] at hw1 hw2
      rcases hb with hlt | ⟨heq, hsub⟩
      · omega
      · by_cases hs2 : s % 2 = 0
        · have hs3 : ¬ (s + 1) % 2 = 0 := by omega
          rw [if_pos hs2, Finset.mem_singleton] at hw1
          rw [if_neg hs3, Finset.mem_singleton] at hw2
          rw [hw1, hw2] at hsub
          exact absurd (hsub (Finset.mem_univ 0)) (Finset.notMem_empty 0)
        · omega
  have hmin : ∀ i : Fin k, (g (Sum.inr (Sum.inl i))).1 = D := by
    intro i
    have h1 := hl (Sum.inr (Sum.inl i))
    rcases Nat.eq_zero_or_pos D with hD | hD
    · omega
    · have h2 := hchain i (2 * D - 1) (by omega)
      have hb := hc (Sum.inr (Sum.inr (i, ⟨2 * D - 1, by omega⟩))) (Sum.inr (Sum.inl i))
        (by simp [rel])
      have : (2 * D - 1 + 1) / 2 = D := by omega
      rcases hb with hlt | ⟨heq, _⟩ <;> omega
  have hadj : ∀ (i : Fin k) (i' : Fin (k + 1)), (i'.val = i.val ∨ i'.val = i.val + 1) →
      (g (Sum.inr (Sum.inl i))).2 ⊆ (g (Sum.inl i')).2 := by
    intro i i' hii
    have hb := hc (Sum.inr (Sum.inl i)) (Sum.inl i') (by simp [rel, hii])
    have h1 := hmin i
    have h2 := hl (Sum.inl i')
    rcases hb with hlt | ⟨_, hsub⟩
    · omega
    · exact hsub
  have hstep : ∀ t : ℕ, (ht : t < k) → (g (Sum.inl ⟨t, by omega⟩)).2 = {0} →
      (0 : Fin 2) ∈ (g (Sum.inl ⟨t + 1, by omega⟩)).2 := by
    intro t ht hM
    have hm := hadj ⟨t, ht⟩ ⟨t, by omega⟩ (Or.inl rfl)
    have hm2 := hadj ⟨t, ht⟩ ⟨t + 1, by omega⟩ (Or.inr rfl)
    rw [hM] at hm
    have hwm := hw (Sum.inr (Sum.inl ⟨t, ht⟩))
    simp only [AT] at hwm
    have hm0 : (g (Sum.inr (Sum.inl ⟨t, ht⟩))).2 = {0} := by
      rcases Finset.subset_singleton_iff.mp hm with h | h
      · rw [h] at hwm; exact absurd hwm hPe
      · exact h
    rw [hm0] at hm2
    exact hm2 (Finset.mem_singleton_self 0)
  have hfence : ∀ t : ℕ, (ht : t < k) → (g (Sum.inl ⟨t, by omega⟩)).2 = {0} := by
    intro t
    induction t with
    | zero =>
      intro ht
      have := hw (Sum.inl ⟨0, by omega⟩)
      simpa [AT] using this
    | succ t ih =>
      intro ht
      have h0 := hstep t (by omega) (ih (by omega))
      have hwM := hw (Sum.inl ⟨t + 1, by omega⟩)
      simp only [AT] at hwM
      rw [if_neg (by omega), if_neg (by omega)] at hwM
      exact fin2_eq_singleton0 _ h0 (fun h => hQu (h ▸ hwM))
  have h0 := hstep (k - 1) (by omega) (hfence (k - 1) (by omega))
  have hwM : (g (Sum.inl ⟨k, by omega⟩)).2 = {1} := by
    have := hw (Sum.inl ⟨k, by omega⟩)
    have hk0 : ¬ (k = 0) := by omega
    simpa [AT, hk0] using this
  have hk1 : k - 1 + 1 = k := by omega
  have : (⟨k - 1 + 1, by omega⟩ : Fin (k + 1)) = ⟨k, by omega⟩ := Fin.ext hk1
  rw [this, hwM] at h0
  simp at h0

lemma fin2_incomp_inter : ∀ u v : Finset (Fin 2), u ∩ v ≠ u → u ∩ v ≠ v →
    ((u = {0} ∧ v = {1}) ∨ (u = {1} ∧ v = {0})) := by decide

lemma fin2_incomp_union : ∀ u v : Finset (Fin 2), u ∪ v ≠ u → u ∪ v ≠ v →
    ((u = {0} ∧ v = {1}) ∨ (u = {1} ∧ v = {0})) := by decide

lemma inter_fail (A : Finset (Finset (Fin 2))) (u v c : Finset (Fin 2)) (hu : u ∈ A) (hv : v ∈ A)
    (hc : ∀ a, a ∈ c ↔ a ∈ u ∧ a ∈ v) (hcA : c ∉ A) : {0} ∈ A ∧ {1} ∈ A ∧ ∅ ∉ A := by
  have hceq : c = u ∩ v := by ext a; rw [hc a, Finset.mem_inter]
  subst hceq
  have h1 : u ∩ v ≠ u := fun h => hcA (by rw [h]; exact hu)
  have h2 : u ∩ v ≠ v := fun h => hcA (by rw [h]; exact hv)
  rcases fin2_incomp_inter u v h1 h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨hu, hv, by simpa using hcA⟩
  · exact ⟨hv, hu, by simpa using hcA⟩

lemma union_fail (A : Finset (Finset (Fin 2))) (u v c : Finset (Fin 2)) (hu : u ∈ A) (hv : v ∈ A)
    (hc : ∀ a, a ∈ c ↔ a ∈ u ∨ a ∈ v) (hcA : c ∉ A) :
    {0} ∈ A ∧ {1} ∈ A ∧ Finset.univ ∉ A := by
  have hceq : c = u ∪ v := by ext a; rw [hc a, Finset.mem_union]
  subst hceq
  have h1 : u ∪ v ≠ u := fun h => hcA (by rw [h]; exact hu)
  have h2 : u ∪ v ≠ v := fun h => hcA (by rw [h]; exact hv)
  have hU : ({0} : Finset (Fin 2)) ∪ {1} = Finset.univ := by decide
  have hU' : ({1} : Finset (Fin 2)) ∪ {0} = Finset.univ := by decide
  rcases fin2_incomp_union u v h1 h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨hu, hv, by rw [← hU]; exact hcA⟩
  · exact ⟨hv, hu, by rw [← hU']; exact hcA⟩

-- transport to Fin
noncomputable def eqv (k D : ℕ) : Pt k D ≃ Fin (Fintype.card (Pt k D)) := Fintype.equivFin _

noncomputable def xF (k D : ℕ) : Fin (Fintype.card (Pt k D)) → Finset (Fin (Fintype.card (Pt k D))) :=
  fun a => (X ((eqv k D).symm a)).map (eqv k D).toEmbedding

lemma xF_sub (k D : ℕ) (a b : Fin (Fintype.card (Pt k D))) :
    xF k D a ⊆ xF k D b ↔ X ((eqv k D).symm a) ⊆ X ((eqv k D).symm b) :=
  Finset.map_subset_map

lemma xF_inj (k D : ℕ) : Function.Injective (xF k D) := fun a b h => by
  have h1 : X ((eqv k D).symm a) = X ((eqv k D).symm b) := Finset.map_injective _ h
  exact (eqv k D).symm.injective (X_inj h1)

lemma exists_missing (k D K : ℕ) (hK : K < k + 1) (S : Finset (Fin (Fintype.card (Pt k D))))
    (hS : S.card ≤ K) : ∃ j : Fin (k + 1), eqv k D (Sum.inl j) ∉ S := by
  by_contra h
  push_neg at h
  have hsub : Finset.univ.image (fun j : Fin (k + 1) => eqv k D (Sum.inl j)) ⊆ S := by
    intro z hz
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hz
    rcases hz with ⟨j, rfl⟩
    exact h j
  have hinj : Function.Injective (fun j : Fin (k + 1) => eqv k D (Sum.inl j)) :=
    (eqv k D).injective.comp Sum.inl_injective
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at hc
  omega



-- =========================================================================
-- Standard-instance fitting predicate and the bridges
-- =========================================================================

def FitsStd (n m : ℕ) (x : Fin m → Finset (Fin n)) (A : Fin m → Finset (Finset (Fin 2))) (r : ℕ)
    (S : Finset (Fin m)) : Prop :=
  ∃ (C : Circuit) (tap : Fin 2 → ℕ),
    FanInTwo C ∧ ReadsBack (n + 2) C ∧
    C.output < n + 2 + C.size ∧ (∀ a, tap a < n + 2 + C.size) ∧ notCount C ≤ r ∧
    ∀ i ∈ S, (Finset.univ.filter (fun a =>
      (C.wires (List.ofFn (fun j : Fin n => decide (j ∈ x i)) ++ [false, true])).getD (tap a) false = true)) ∈ A i

lemma FitsStd_mono {n m : ℕ} {x : Fin m → Finset (Fin n)} {A : Fin m → Finset (Finset (Fin 2))} {r : ℕ}
    {S S' : Finset (Fin m)} (hsub : S' ⊆ S) (h : FitsStd n m x A r S) : FitsStd n m x A r S' := by
  rcases h with ⟨C, tap, h1, h2, h3, h4, h5, h6⟩
  exact ⟨C, tap, h1, h2, h3, h4, h5, fun i hi => h6 i (hsub hi)⟩

lemma meet_std (n m : ℕ) (x : Fin m → Finset (Fin n)) (A : Fin m → Finset (Finset (Fin 2))) (r : ℕ)
    (hx : Function.Injective x)
    (hinter : ∀ i u v, u ∈ A i → v ∈ A i → ∀ c : Finset (Fin 2),
      (∀ a, a ∈ c ↔ a ∈ u ∧ a ∈ v) → c ∈ A i) :
    FitsStd n m x A r Finset.univ ↔
      ∀ S : Finset (Fin m), S.card ≤ 3 * (2 ^ (2 ^ r) - 1) → FitsStd n m x A r S := by
  have hinter' : ∀ i u v, u ∈ A i → v ∈ A i → u ∩ v ∈ A i :=
    fun i u v hu hv => hinter i u v hu hv (u ∩ v) (fun a => Finset.mem_inter)
  by_cases hne : ∀ i, (A i).Nonempty
  · exact (main_core n m x A hx hne hinter').2 r
  · obtain ⟨i, hi⟩ : ∃ i, A i = ∅ := by
      by_contra h
      exact hne (fun i => Finset.nonempty_iff_ne_empty.mpr (fun he => h ⟨i, he⟩))
    have hK : 1 ≤ 3 * (2 ^ (2 ^ r) - 1) := by
      have : 2 ≤ 2 ^ (2 ^ r) := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ (2 ^ r) := Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow
      omega
    constructor
    · rintro ⟨C, tap, _, _, _, _, _, hw⟩
      have := hw i (Finset.mem_univ i)
      rw [hi] at this
      exact absurd this (Finset.notMem_empty _)
    · intro h
      rcases h {i} (by rw [Finset.card_singleton]; exact hK) with ⟨C, tap, _, _, _, _, _, hw⟩
      have := hw i (Finset.mem_singleton_self i)
      rw [hi] at this
      exact absurd this (Finset.notMem_empty _)

lemma enc_spec (n : ℕ) (y : Finset (Fin n)) :
    (List.ofFn (fun j : Fin n => decide (j ∈ y)) ++ [false, true]).length = n + 2 ∧
    (List.ofFn (fun j : Fin n => decide (j ∈ y)) ++ [false, true]).getD n false = false ∧
    (List.ofFn (fun j : Fin n => decide (j ∈ y)) ++ [false, true]).getD (n + 1) false = true ∧
    ∀ j : Fin n, (List.ofFn (fun j : Fin n => decide (j ∈ y)) ++ [false, true]).getD j.val false =
      decide (j ∈ y) := by
  refine ⟨by simp, by simp [List.getD_eq_getElem?_getD], by simp [List.getD_eq_getElem?_getD],
    fun j => ?_⟩
  simp only [List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by simp : j.val < (List.ofFn (fun j : Fin n => decide (j ∈ y))).length),
    List.getElem?_ofFn, dite_eq_left j.isLt, Option.getD_some]

lemma dual_std (n m : ℕ) (x : Fin m → Finset (Fin n)) (A : Fin m → Finset (Finset (Fin 2))) (r : ℕ)
    (S : Finset (Fin m)) (h : FitsStd n m x A r S) :
    FitsStd n m (fun i => (x i)ᶜ) (fun i => (A i).image compl) r S := by
  rcases h with ⟨C, tap, hfan, hrb, hout, htap, hnot, hw⟩
  refine ⟨dualC n C, fun a => swc n (tap a), dualC_fan n C hfan, dualC_rb n C hrb, ?_, ?_, ?_, ?_⟩
  · rw [dualC_size]; exact hout
  · intro a; rw [dualC_size]; exact swc_lt (htap a) (by omega)
  · rw [notCount_dualC]; exact hnot
  · intro i hi
    have e1 := enc_spec n (x i)
    have e2 := enc_spec n (x i)ᶜ
    have hdw := dual_wires n C hfan hrb
      (List.ofFn (fun j : Fin n => decide (j ∈ x i)) ++ [false, true])
      (List.ofFn (fun j : Fin n => decide (j ∈ (x i)ᶜ)) ++ [false, true]) e1.1 e2.1
      (by
        intro u hu
        by_cases hun : u < n
        · have hs : swc n u = u := by unfold swc; split_ifs <;> omega
          rw [hs]
          have h1 := e1.2.2.2 ⟨u, hun⟩
          have h2 := e2.2.2.2 ⟨u, hun⟩
          simp only at h1 h2
          rw [h1, h2]
          simp [Finset.mem_compl]
        · have hu' : u = n ∨ u = n + 1 := by omega
          rcases hu' with hu' | hu'
          · rw [hu']
            have hs : swc n n = n + 1 := by unfold swc; simp
            rw [hs]
            simp [e1.2.1, e2.2.2.1]
          · rw [hu']
            have hs : swc n (n + 1) = n := by unfold swc; simp
            rw [hs]
            simp [e1.2.2.1, e2.2.1])
      e1.2.1
    rw [Finset.mem_image]
    refine ⟨_, hw i hi, ?_⟩
    ext a
    rw [Finset.mem_compl, Finset.mem_filter, Finset.mem_filter, hdw (tap a) (htap a)]
    simp only [Finset.mem_univ, true_and]
    generalize (C.wires (List.ofFn (fun j : Fin n => decide (j ∈ x i)) ++ [false, true])).getD (tap a) false = b
    cases b <;> simp

lemma join_std (n m : ℕ) (x : Fin m → Finset (Fin n)) (A : Fin m → Finset (Finset (Fin 2))) (r : ℕ)
    (hx : Function.Injective x)
    (hunion : ∀ i u v, u ∈ A i → v ∈ A i → ∀ c : Finset (Fin 2),
      (∀ a, a ∈ c ↔ a ∈ u ∨ a ∈ v) → c ∈ A i) :
    FitsStd n m x A r Finset.univ ↔
      ∀ S : Finset (Fin m), S.card ≤ 3 * (2 ^ (2 ^ r) - 1) → FitsStd n m x A r S := by
  have hx' : Function.Injective (fun i => (x i)ᶜ) := fun a b h => hx (compl_injective h)
  have hinter' : ∀ i u v, u ∈ (A i).image compl → v ∈ (A i).image compl → ∀ c : Finset (Fin 2),
      (∀ a, a ∈ c ↔ a ∈ u ∧ a ∈ v) → c ∈ (A i).image compl := by
    intro i u v hu hv c hc
    rw [Finset.mem_image] at hu hv ⊢
    rcases hu with ⟨u0, hu0, rfl⟩
    rcases hv with ⟨v0, hv0, rfl⟩
    refine ⟨u0 ∪ v0, hunion i u0 v0 hu0 hv0 _ (fun a => Finset.mem_union), ?_⟩
    ext a
    rw [hc a]
    simp [Finset.mem_compl, Finset.mem_union]
  have hmeet := meet_std n m (fun i => (x i)ᶜ) (fun i => (A i).image compl) r hx' hinter'
  have e1 : (fun i => (x i)ᶜᶜ) = x := funext fun i => compl_compl (x i)
  have e2 : (fun i => ((A i).image compl).image compl) = A := funext fun i => by
    rw [Finset.image_image]
    have : (compl ∘ compl : Finset (Fin 2) → Finset (Fin 2)) = id := funext fun w => compl_compl w
    rw [this, Finset.image_id]
  constructor
  · intro h S _
    exact FitsStd_mono (Finset.subset_univ S) h
  · intro h
    have h1 := hmeet.2 (fun S hS => dual_std n m x A r S (h S hS))
    have h2 : FitsStd n m (fun i => (x i)ᶜᶜ) (fun i => ((A i).image compl).image compl) r Finset.univ :=
      dual_std n m _ _ r Finset.univ h1
    rw [e1, e2] at h2
    exact h2

lemma lower_std (n m : ℕ) (x : Fin m → Finset (Fin n)) (A : Fin m → Finset (Finset (Fin 2))) (r : ℕ)
    (hx : Function.Injective x) (h : FitsStd n m x A r Finset.univ) :
    ∃ g : Fin m → ℕ × Finset (Fin 2), (∀ i, (g i).2 ∈ A i) ∧ (∀ i, (g i).1 < 2 ^ r) ∧
      ∀ i j, x i ⊆ x j → beforeSt (g i) (g j) := by
  rcases h with ⟨C, tap, hfan, hrb, hout, htap, hnot, hw⟩
  let w : Fin m → Finset (Fin 2) := fun i => Finset.univ.filter (fun a =>
      (C.wires (List.ofFn (fun j : Fin n => decide (j ∈ x i)) ++ [false, true])).getD (tap a) false = true)
  let A' : Fin m → Finset (Finset (Fin 2)) := fun i => {w i}
  have hne : ∀ i, (A' i).Nonempty := fun i => Finset.singleton_nonempty _
  have hint : ∀ i a b, a ∈ A' i → b ∈ A' i → a ∩ b ∈ A' i := by
    intro i a b ha hb
    simp only [A', Finset.mem_singleton] at ha hb ⊢
    rw [ha, hb, Finset.inter_self]
  rcases lib1301_core n m 2 x A' hx hne hint with ⟨⟨g, hg, _⟩, hall⟩
  dsimp only at hg hall
  rcases hall g hg with ⟨_, _, hreal⟩
  have hlev := ((hreal r).1).mp
    ⟨C, tap, hfan, hrb, hout, htap, hnot, fun i => Finset.mem_singleton_self (w i)⟩
  refine ⟨g, fun i => ?_, hlev, fun i j hsub => ?_⟩
  · have := (hg i).1.1
    simp only [A', Finset.mem_singleton] at this
    rw [this]; exact hw i (Finset.mem_univ i)
  · by_cases hij : i = j
    · subst hij; exact beforeSt_refl _
    · exact (hg j).1.2 i hij hsub

lemma upper_std (n m : ℕ) (x : Fin m → Finset (Fin n)) (A : Fin m → Finset (Finset (Fin 2))) (r : ℕ)
    (hx : Function.Injective x) (S : Finset (Fin m)) (g : Fin m → ℕ × Finset (Fin 2))
    (hw : ∀ i ∈ S, (g i).2 ∈ A i) (hl : ∀ i ∈ S, (g i).1 < 2 ^ r)
    (hc : ∀ i ∈ S, ∀ j ∈ S, x i ⊆ x j → beforeSt (g i) (g j)) : FitsStd n m x A r S := by
  let emb : Fin S.card → Fin m := fun k => S.orderEmbOfFin rfl k
  have hemb_inj : Function.Injective emb := (S.orderEmbOfFin rfl).injective
  have hemb_mem : ∀ k, emb k ∈ S := fun k => S.orderEmbOfFin_mem rfl k
  have hemb_surj : ∀ i ∈ S, ∃ k, emb k = i := by
    intro i hi
    have : i ∈ Set.range (S.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]; exact hi
    rcases this with ⟨k, hk⟩
    exact ⟨k, hk⟩
  let y : Fin S.card → Finset (Fin n) := fun k => x (emb k)
  have hy : Function.Injective y := fun a b h => hemb_inj (hx h)
  let A' : Fin S.card → Finset (Finset (Fin 2)) := fun k => {(g (emb k)).2}
  have hne : ∀ k, (A' k).Nonempty := fun k => Finset.singleton_nonempty _
  have hint : ∀ k a b, a ∈ A' k → b ∈ A' k → a ∩ b ∈ A' k := by
    intro k a b ha hb
    simp only [A', Finset.mem_singleton] at ha hb ⊢
    rw [ha, hb, Finset.inter_self]
  rcases lib1301_core n S.card 2 y A' hy hne hint with ⟨⟨g', hg', _⟩, hall⟩
  dsimp only at hg' hall
  rcases hall g' hg' with ⟨_, hleast, hreal⟩
  have hlt : ∀ k, (g' k).1 < 2 ^ r := by
    intro k
    have hb : beforeSt (g' k) (g (emb k)) := hleast (fun k => g (emb k)) (fun k => ⟨Finset.mem_singleton_self _,
      fun j _ hsub => hc (emb j) (hemb_mem j) (emb k) (hemb_mem k) hsub⟩) k
    have := hl (emb k) (hemb_mem k)
    rcases hb with h1 | ⟨h1, _⟩ <;> omega
  rcases ((hreal r).1).mpr hlt with ⟨C, tap, hfan, hrb, hout, htap, hnot, hwC⟩
  refine ⟨C, tap, hfan, hrb, hout, htap, hnot, fun i hi => ?_⟩
  rcases hemb_surj i hi with ⟨k, rfl⟩
  have := hwC k
  simp only [A', y, Finset.mem_singleton] at this
  rw [this]
  exact hw (emb k) hi

lemma hard (L : Finset (Finset (Finset (Fin 2)))) (hsing : ∀ w : Finset (Fin 2), {w} ∈ L)
    (P Q : Finset (Finset (Fin 2))) (hPL : P ∈ L) (hQL : Q ∈ L)
    (hP0 : {0} ∈ P) (hP1 : {1} ∈ P) (hPe : ∅ ∉ P) (hQ0 : {0} ∈ Q) (hQ1 : {1} ∈ Q)
    (hQu : Finset.univ ∉ Q) (r K : ℕ) :
    ∃ (n m : ℕ) (x : Fin m → Finset (Fin n)) (A : Fin m → Finset (Finset (Fin 2))),
      Function.Injective x ∧ (∀ i, A i ∈ L) ∧ ¬ FitsStd n m x A r Finset.univ ∧
      ∀ S : Finset (Fin m), S.card ≤ K → FitsStd n m x A r S := by
  have hpow : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  refine ⟨_, _, xF (K + 1) (2 ^ r - 1), fun a => AT P Q ((eqv (K + 1) (2 ^ r - 1)).symm a),
    xF_inj _ _, ?_, ?_, ?_⟩
  · intro a
    show AT P Q ((eqv (K + 1) (2 ^ r - 1)).symm a) ∈ L
    generalize (eqv (K + 1) (2 ^ r - 1)).symm a = p
    rcases p with i | i | ⟨i, s⟩
    · simp only [AT]
      split_ifs <;> first | exact hsing _ | assumption
    · exact hPL
    · simp only [AT]
      split_ifs <;> exact hsing _
  · intro hfit
    rcases lower_std _ _ _ _ r (xF_inj _ _) hfit with ⟨g, hw, hl, hc⟩
    apply infeas (k := K + 1) (D := 2 ^ r - 1) (by omega) P Q hPe hQu
      (fun p => g (eqv (K + 1) (2 ^ r - 1) p))
    · intro p
      have := hw (eqv (K + 1) (2 ^ r - 1) p)
      simpa using this
    · intro p
      have := hl (eqv (K + 1) (2 ^ r - 1) p)
      show (g (eqv (K + 1) (2 ^ r - 1) p)).1 ≤ 2 ^ r - 1
      omega
    · intro p q hpq
      apply hc
      rw [xF_sub]
      simp only [Equiv.symm_apply_apply]
      exact X_sub_of_rel hpq
  · intro S hS
    rcases exists_missing (K + 1) (2 ^ r - 1) K (by omega) S hS with ⟨j, hj⟩
    have hne : ∀ i ∈ S, (eqv (K + 1) (2 ^ r - 1)).symm i ≠ Sum.inl j := by
      intro i hi h
      apply hj
      have : i = eqv (K + 1) (2 ^ r - 1) (Sum.inl j) := by
        rw [← h, Equiv.apply_symm_apply]
      rw [← this]; exact hi
    apply upper_std _ _ _ _ r (xF_inj _ _) S (fun a => lab j.val ((eqv (K + 1) (2 ^ r - 1)).symm a))
    · intro i hi
      exact (lab_words (by omega) P Q hP0 hP1 hQ0 hQ1 j _ (hne i hi)).1
    · intro i hi
      have := (lab_words (by omega) P Q hP0 hP1 hQ0 hQ1 j _ (hne i hi)).2
      show (lab j.val ((eqv (K + 1) (2 ^ r - 1)).symm i)).1 < 2 ^ r
      omega
    · intro i hi i' hi' hsub
      rw [xF_sub] at hsub
      exact lab_coh j _ _ (hne i' hi') (rel_of_X_sub hsub)

lemma fits_conv : letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    ∀ (n m : ℕ) (x : Fin m → Finset (Fin n)) (A : Fin m → Finset (Finset (Fin 2))) (r : ℕ)
      (S : Finset (Fin m)),
      (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin 2 → Nat),
          PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
          C.output < n+2+C.size ∧ (∀ a, tap a < n+2+C.size) ∧ PEqualNP.NotBracket.notCount C ≤ r ∧
          ∀ i ∈ S, (Finset.univ.filter (fun a =>
            (C.wires (List.ofFn (fun j : Fin n => decide (j ∈ x i)) ++ [false,true])).getD (tap a) false = true)) ∈ A i)
      ↔ FitsStd n m x A r S := by
  intro n m x A r S
  unfold FitsStd
  refine exists_congr fun C => exists_congr fun tap =>
    and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
    and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun i => forall_congr' fun _ => ?_
  rw [input_congr_dec (x i) (fun j => Classical.propDecidable (j ∈ x i))
    (fun j => @Finset.decidableMem (Fin n) (instDecidableEqFin n) j (x i))]
  rw [filter_congr_dec Finset.univ _ (fun a => Classical.propDecidable _) (fun a => instDecidableEqBool _ _)]

lemma main_thm :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    ∀ (L : Finset (Finset (Finset (Fin 2)))) (r : Nat),
      (∀ w : Finset (Fin 2), {w} ∈ L) →
      let meet := ∀ A ∈ L, ∀ u ∈ A, ∀ v ∈ A, u ∩ v ∈ A
      let join := ∀ A ∈ L, ∀ u ∈ A, ∀ v ∈ A, u ∪ v ∈ A
      let test := fun K : Nat =>
        ∀ (n m : Nat) (x : Fin m → Finset (Fin n)) (A : Fin m → Finset (Finset (Fin 2))),
          Function.Injective x → (∀ i, A i ∈ L) →
          let fits := fun (S : Finset (Fin m)) =>
            ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin 2 → Nat),
              PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
              C.output < n+2+C.size ∧ (∀ a, tap a < n+2+C.size) ∧ PEqualNP.NotBracket.notCount C ≤ r ∧
              ∀ i ∈ S, (Finset.univ.filter (fun a =>
                (C.wires (List.ofFn (fun j : Fin n => decide (j ∈ x i)) ++ [false,true])).getD (tap a) false = true)) ∈ A i
          fits Finset.univ ↔ ∀ S, S.card ≤ K → fits S
      ((∃ K, test K) ↔ meet ∨ join) ∧ ((meet ∨ join) → test (3*(2^(2^r)-1))) := by
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  intro L r hsing meet join test
  have hB : meet ∨ join → test (3 * (2 ^ (2 ^ r) - 1)) := by
    intro hmj
    dsimp only [test]
    intro n m x A hx hAL
    simp only [fits_conv]
    rcases hmj with hm | hj
    · dsimp only [meet] at hm
      apply meet_std n m x A r hx
      intro i u v hu hv c hc
      have := hm (A i) (hAL i) u hu v hv
      convert this using 1
      ext a
      simp only [hc a, Finset.mem_inter]
    · dsimp only [join] at hj
      apply join_std n m x A r hx
      intro i u v hu hv c hc
      have := hj (A i) (hAL i) u hu v hv
      convert this using 1
      ext a
      simp only [hc a, Finset.mem_union]
  have hC : (∃ K, test K) → meet ∨ join := by
    rintro ⟨K, hK⟩
    by_contra hcon
    have hnm : ¬ meet := fun h => hcon (Or.inl h)
    have hnj : ¬ join := fun h => hcon (Or.inr h)
    have hnm' : ∃ P ∈ L, ∃ u ∈ P, ∃ v ∈ P, ∃ c : Finset (Fin 2),
        (∀ a, a ∈ c ↔ a ∈ u ∧ a ∈ v) ∧ c ∉ P := by
      by_contra hne
      apply hnm
      dsimp only [meet]
      intro P hPL u hu v hv
      by_contra hc
      exact hne ⟨P, hPL, u, hu, v, hv, _, fun a => by simp only [Finset.mem_inter], hc⟩
    have hnj' : ∃ Q ∈ L, ∃ u ∈ Q, ∃ v ∈ Q, ∃ c : Finset (Fin 2),
        (∀ a, a ∈ c ↔ a ∈ u ∨ a ∈ v) ∧ c ∉ Q := by
      by_contra hne
      apply hnj
      dsimp only [join]
      intro Q hQL u hu v hv
      by_contra hc
      exact hne ⟨Q, hQL, u, hu, v, hv, _, fun a => by simp only [Finset.mem_union], hc⟩
    rcases hnm' with ⟨P, hPL, u, hu, v, hv, c, hc, hcP⟩
    rcases hnj' with ⟨Q, hQL, u', hu', v', hv', c', hc', hcQ⟩
    rcases inter_fail P u v c hu hv hc hcP with ⟨hP0, hP1, hPe⟩
    rcases union_fail Q u' v' c' hu' hv' hc' hcQ with ⟨hQ0, hQ1, hQu⟩
    rcases hard L hsing P Q hPL hQL hP0 hP1 hPe hQ0 hQ1 hQu r K with
      ⟨n, m, x, A, hx, hAL, hnf, hsm⟩
    dsimp only [test] at hK
    have h1 := hK n m x A hx hAL
    simp only [fits_conv] at h1
    exact hnf (h1.mpr hsm)
  exact ⟨⟨hC, fun h => ⟨_, hB h⟩⟩, hB⟩

end PEqualNP.Outside.L_lib_1312_aux

theorem PEqualNP.Outside.L_lib_1312 :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    ∀ (L : Finset (Finset (Finset (Fin 2)))) (r : Nat),
      (∀ w : Finset (Fin 2), {w} ∈ L) →
      let meet := ∀ A ∈ L, ∀ u ∈ A, ∀ v ∈ A, u ∩ v ∈ A
      let join := ∀ A ∈ L, ∀ u ∈ A, ∀ v ∈ A, u ∪ v ∈ A
      let test := fun K : Nat =>
        ∀ (n m : Nat) (x : Fin m → Finset (Fin n)) (A : Fin m → Finset (Finset (Fin 2))),
          Function.Injective x → (∀ i, A i ∈ L) →
          let fits := fun (S : Finset (Fin m)) =>
            ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin 2 → Nat),
              PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
              C.output < n+2+C.size ∧ (∀ a, tap a < n+2+C.size) ∧ PEqualNP.NotBracket.notCount C ≤ r ∧
              ∀ i ∈ S, (Finset.univ.filter (fun a =>
                (C.wires (List.ofFn (fun j : Fin n => decide (j ∈ x i)) ++ [false,true])).getD (tap a) false = true)) ∈ A i
          fits Finset.univ ↔ ∀ S, S.card ≤ K → fits S
      ((∃ K, test K) ↔ meet ∨ join) ∧ ((meet ∨ join) → test (3*(2^(2^r)-1))) :=
  PEqualNP.Outside.L_lib_1312_aux.main_thm
