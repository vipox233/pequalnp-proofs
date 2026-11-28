import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1430_aux

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

-- =========================================================================
-- Part A2: good inputs, computed wires, families, embedding
-- =========================================================================

def Gd (n : ℕ) (inp : List Bool) : Prop :=
  inp.length = n + 2 ∧ inp.getD n false = false ∧ inp.getD (n + 1) false = true

def Cmp {n : ℕ} (B : Builder n) (w : ℕ) (f : List Bool → Bool) : Prop :=
  w < n + 2 + B.gates.length ∧ ∀ inp, Gd n inp → B.eval inp w = f inp

lemma Cmp.ext {n : ℕ} {B B' : Builder n} {w : ℕ} {f : List Bool → Bool}
    (h : Cmp B w f) (hE : Extends B B') : Cmp B' w f :=
  ⟨by have := hE.1; have := h.1; omega, fun inp hg => (hE.2 inp hg.1 w h.1).trans (h.2 inp hg)⟩

lemma Cmp.inp {n : ℕ} (B : Builder n) (w : ℕ) (hw : w < n + 2) :
    Cmp B w (fun inp => inp.getD w false) :=
  ⟨by omega, fun inp hg => B.eval_inp inp hg.1 w hw⟩

lemma family {n : ℕ} {ι : Type} [DecidableEq ι] (f : ι → List Bool → Bool) (c : ℕ)
    (B0 : Builder n) (l : List ι)
    (step : ∀ i ∈ l, ∀ B : Builder n, Extends B0 B → ∃ (B' : Builder n) (w : ℕ), Extends B B' ∧
      B'.nots = B.nots ∧ B'.monos ≤ B.monos + c ∧ Cmp B' w (f i)) :
    ∀ (B1 : Builder n), Extends B0 B1 → ∃ (B' : Builder n) (ws : ι → ℕ),
      Extends B1 B' ∧ B'.nots = B1.nots ∧ B'.monos ≤ B1.monos + c * l.length ∧
      ∀ i ∈ l, Cmp B' (ws i) (f i) := by
  induction l with
  | nil => intro B1 _; exact ⟨B1, fun _ => 0, Extends.refl _, rfl, by simp, by simp⟩
  | cons i rest ih =>
    intro B1 h01
    obtain ⟨B2, w, h12, hn2, hm2, hc2⟩ := step i (List.mem_cons_self ..) B1 h01
    obtain ⟨B3, ws, h23, hn3, hm3, hc3⟩ :=
      ih (fun i' hi' B hB => step i' (List.mem_cons_of_mem i hi') B hB) B2 (h01.trans h12)
    refine ⟨B3, Function.update ws i w, h12.trans h23, by rw [hn3, hn2], ?_, ?_⟩
    · simp only [List.length_cons, Nat.mul_succ]; omega
    · intro i' hi'
      by_cases h : i' = i
      · subst h; simp only [Function.update_self]; exact hc2.ext h23
      · rw [Function.update_of_ne h]
        exact hc3 i' ((List.mem_cons.mp hi').resolve_left h)

lemma andOr {n : ℕ} (B : Builder n) (r : ℕ) (u v : ℕ → ℕ)
    (hu : ∀ x < r, u x < n + 2 + B.gates.length) (hv : ∀ x < r, v x < n + 2 + B.gates.length) :
    ∃ (B' : Builder n) (w : ℕ), Extends B B' ∧ B'.nots = B.nots ∧ B'.monos ≤ B.monos + 2 * r ∧
      Cmp B' w (fun inp => decide (∀ x < r, B.eval inp (u x) = true ∨ B.eval inp (v x) = true)) := by
  obtain ⟨B1, ws, h01, hn1, hm1, hc1⟩ := family (fun x inp => B.eval inp (u x) || B.eval inp (v x)) 1 B
    (List.range r) (fun x hx B2 h02 => by
      have hx' : x < r := List.mem_range.mp hx
      have ha : u x < n + 2 + B2.gates.length := by have := hu x hx'; have := h02.1; omega
      have hb : v x < n + 2 + B2.gates.length := by have := hv x hx'; have := h02.1; omega
      have hs := pushOr_spec B2 (u x) (v x) ha hb
      refine ⟨_, _, hs.1, hs.2.2.1, by rw [hs.2.2.2.1], hs.2.1, fun inp hg => ?_⟩
      rw [hs.2.2.2.2 inp hg.1, h02.2 inp hg.1 _ (hu x hx'), h02.2 inp hg.1 _ (hv x hx')])
    B (Extends.refl B)
  have hws : ∀ w ∈ (List.range r).map ws, w < n + 2 + B1.gates.length := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hw
    exact (hc1 x hx).1
  obtain ⟨B2, out, h12, hlt, hn2, hm2, hev⟩ := exists_and_list ((List.range r).map ws) B1 hws
  refine ⟨B2, out, h01.trans h12, by rw [hn2, hn1], ?_, ⟨hlt, fun inp hg => ?_⟩⟩
  · simp only [List.length_map, List.length_range] at hm2 hm1; omega
  · rw [hev inp hg.1 hg.2.2]
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_map, List.all_eq_true, List.mem_range, Function.comp, decide_eq_true_eq]
    constructor
    · intro h x hx
      have := h x hx
      rw [(hc1 x (List.mem_range.mpr hx)).2 inp hg] at this
      simpa [Bool.or_eq_true] using this
    · intro h x hx
      rw [(hc1 x (List.mem_range.mpr hx)).2 inp hg]
      simpa [Bool.or_eq_true] using h x hx

def copyG (a : ℕ) : Gate := ⟨GateOp.or, [a]⟩

lemma copies {n : ℕ} : ∀ (ins : List ℕ) (B : Builder n), (∀ w ∈ ins, w < n + 2 + B.gates.length) →
    ∃ B' : Builder n, Extends B B' ∧ B'.gates = B.gates ++ ins.map copyG ∧
      ∀ inp, inp.length = n + 2 → ∀ e < ins.length,
        B'.eval inp (n + 2 + B.gates.length + e) = B.eval inp (ins.getD e 0) := by
  intro ins
  induction ins with
  | nil => intro B _; exact ⟨B, Extends.refl B, by simp, fun _ _ e he => by simp at he⟩
  | cons a rest ih =>
    intro B hins
    have ha : a < n + 2 + B.gates.length := hins a (List.mem_cons_self ..)
    let B1 := B.push (copyG a) ⟨Or.inr (Or.inl rfl), by simp [copyG]⟩
      (fun i hi => by simp only [copyG, List.mem_singleton] at hi; subst hi; exact ha)
    have h01 : Extends B B1 := Extends.push B _ _ _
    have hlen1 : B1.gates.length = B.gates.length + 1 := by simp [B1, Builder.push]
    obtain ⟨B2, h12, hg2, hev2⟩ := ih B1 (fun w hw => by
      have := hins w (List.mem_cons_of_mem a hw); omega)
    refine ⟨B2, h01.trans h12, ?_, ?_⟩
    · rw [hg2]; simp [B1, Builder.push]
    · intro inp hinp e he
      cases e with
      | zero =>
        rw [h12.2 inp hinp _ (by omega)]
        simp only [Nat.add_zero, List.getD_cons_zero]
        rw [Builder.eval_push_new B _ _ _ inp hinp]
        simp [copyG, GateOp.eval]
      | succ e' =>
        have he' : e' < rest.length := by simp at he; omega
        have := hev2 inp hinp e' he'
        rw [hlen1] at this
        rw [show n + 2 + B.gates.length + (e' + 1) = n + 2 + (B.gates.length + 1) + e' by omega, this]
        simp only [List.getD_cons_succ]
        apply h01.2 inp hinp
        have hm : rest.getD e' 0 ∈ rest := by
          rw [List.getD_eq_getElem _ _ he']; exact List.getElem_mem he'
        exact hins _ (List.mem_cons_of_mem a hm)

def shiftG (s : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (· + s)⟩

lemma wires_take_succ (C : Circuit) (x : List Bool) (k : ℕ) (hk : k < C.gates.length) :
    (Circuit.wires ⟨C.gates.take (k+1), 0⟩ x) = Circuit.wires ⟨C.gates.take k, 0⟩ x ++
      [C.gates[k].op.eval (C.gates[k].inputs.map
        fun i => (Circuit.wires ⟨C.gates.take k, 0⟩ x).getD i false)] := by
  simp only [Circuit.wires]
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.foldl_append]
  simp

lemma shifted {n : ℕ} (C : Circuit) (L : ℕ) (hfan : FanInTwo C) (hrb : ReadsBack L C)
    (B : Builder n) (base : ℕ) (hbase : base + L = n + 2 + B.gates.length)
    (X : List Bool → List Bool)
    (hX : ∀ inp, inp.length = n + 2 → (X inp).length = L ∧
      ∀ e < L, B.eval inp (base + e) = (X inp).getD e false) :
    ∀ k ≤ C.gates.length, ∃ B' : Builder n, Extends B B' ∧
      B'.gates = B.gates ++ (C.gates.take k).map (shiftG base) ∧
      ∀ inp, inp.length = n + 2 → ∀ w < L + k,
        B'.eval inp (base + w) = (Circuit.wires ⟨C.gates.take k, 0⟩ (X inp)).getD w false := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨B, Extends.refl B, by simp, fun inp hinp w hw => ?_⟩
    simp only [List.take_zero, Circuit.wires, List.foldl_nil]
    exact (hX inp hinp).2 w (by omega)
  | succ k ih =>
    intro hk
    obtain ⟨B1, h01, hg1, hev1⟩ := ih (by omega)
    have hk' : k < C.gates.length := by omega
    have hgmem : C.gates[k] ∈ C.gates := List.getElem_mem hk'
    have hlen1 : B1.gates.length = B.gates.length + k := by
      rw [hg1]; simp only [List.length_append, List.length_map, List.length_take]; omega
    have hfg := hfan _ hgmem
    have hgate : gateAt C k = C.gates[k] := by
      simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']
    have hins : ∀ i ∈ (shiftG base C.gates[k]).inputs, i < n + 2 + B1.gates.length := by
      intro i hi
      simp only [shiftG, List.mem_map] at hi
      obtain ⟨i0, hi0, rfl⟩ := hi
      have := hrb k hk' i0 (by rw [hgate]; exact hi0)
      omega
    have hfan' : ((shiftG base C.gates[k]).op = GateOp.and ∨ (shiftG base C.gates[k]).op = GateOp.or ∨
        (shiftG base C.gates[k]).op = GateOp.not) ∧ (shiftG base C.gates[k]).inputs.length ≤ 2 := by
      simp only [shiftG, List.length_map]
      refine ⟨?_, hfg.2⟩
      have h1 := hfg.1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
      exact h1
    have h12 : Extends B1 (B1.push _ hfan' hins) := Extends.push B1 _ _ _
    refine ⟨B1.push _ hfan' hins, h01.trans h12, ?_, ?_⟩
    · simp only [Builder.push, hg1, List.take_add_one, List.getElem?_eq_getElem hk', Option.toList_some,
        List.map_append, List.append_assoc, List.map_cons, List.map_nil]
    · intro inp hinp w hw
      rw [wires_take_succ C (X inp) k hk']
      have hXlen := (hX inp hinp).1
      have hwlen : (Circuit.wires ⟨C.gates.take k, 0⟩ (X inp)).length = L + k := by
        simp only [Circuit.wires]; rw [wires_foldl_len, hXlen, List.length_take]; omega
      by_cases hwk : w < L + k
      · rw [h12.2 inp hinp _ (by omega), hev1 inp hinp w hwk]
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left (by omega)]
      · have hw' : w = L + k := by omega
        subst hw'
        rw [show base + (L + k) = n + 2 + B1.gates.length by omega]
        rw [Builder.eval_push_new B1 _ _ _ inp hinp]
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega), hwlen, Nat.sub_self]
        simp only [List.getElem?_cons_zero, Option.getD_some, shiftG, List.map_map]
        congr 1
        apply List.map_congr_left
        intro i hi
        simp only [Function.comp]
        have := hrb k hk' i (by rw [hgate]; exact hi)
        rw [show i + base = base + i by omega, hev1 inp hinp i this, List.getD_eq_getElem?_getD]

lemma filter_isNot_le (gs : List Gate) : (gs.filter fun g => isNotOp g.op).length ≤ gs.length :=
  List.length_filter_le _ _

lemma embed {n : ℕ} (C : Circuit) (L : ℕ) (hfan : FanInTwo C) (hrb : ReadsBack L C)
    (B : Builder n) (ins : List ℕ) (hlen : ins.length = L)
    (hins : ∀ w ∈ ins, w < n + 2 + B.gates.length) :
    ∃ B' : Builder n, Extends B B' ∧ B'.nots = B.nots + notCount C ∧
      B'.monos = B.monos + L + (C.size - notCount C) ∧
      ∀ inp, inp.length = n + 2 → ∀ w < L + C.size,
        B'.eval inp (n + 2 + B.gates.length + w) = (C.wires (ins.map (B.eval inp))).getD w false := by
  obtain ⟨B1, h01, hg1, hev1⟩ := copies ins B hins
  have hlen1 : B1.gates.length = B.gates.length + L := by rw [hg1]; simp [hlen]
  obtain ⟨B2, h12, hg2, hev2⟩ := shifted C L hfan hrb B1 (n + 2 + B.gates.length) (by omega)
    (fun inp => ins.map (B.eval inp)) (fun inp hinp => ⟨by simp [hlen], fun e he => by
      rw [hev1 inp hinp e (by omega)]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
      rw [List.getElem?_eq_getElem (by omega)]; simp⟩) C.gates.length le_rfl
  have hnots : B2.nots = B.nots + notCount C := by
    simp only [Builder.nots, hg2, hg1, List.filter_append, List.length_append, List.take_length]
    rw [notCount_eq_filter_isNotOp]
    have h1 : (List.map copyG ins).filter (fun g => isNotOp g.op) = [] := by
      rw [List.filter_eq_nil_iff]; intro g hg
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hg; simp [copyG, isNotOp]
    have h2 : ((C.gates).map (shiftG (n + 2 + B.gates.length))).filter (fun g => isNotOp g.op) =
        (C.gates.filter (fun g => isNotOp g.op)).map (shiftG (n + 2 + B.gates.length)) := by
      rw [List.filter_map]; rfl
    rw [h1, h2]; simp
  have hlen2 : B2.gates.length = B.gates.length + L + C.size := by
    rw [hg2, hg1]; simp [hlen, Circuit.size]; omega
  refine ⟨B2, h01.trans h12, hnots, ?_, ?_⟩
  · have e1 := Builder.gates_len_eq B
    have e2 := Builder.gates_len_eq B2
    have e3 : notCount C ≤ C.size := by
      rw [notCount_eq_filter_isNotOp]; exact List.length_filter_le _ _
    omega
  · intro inp hinp w hw
    have := hev2 inp hinp w (by simpa [Circuit.size] using hw)
    rw [List.take_length] at this
    exact this

-- =========================================================================
-- Part A3: folding the level sequence with shared NOT gates
-- =========================================================================

lemma fold {n m : ℕ} : ∀ (L : ℕ) (b : ℕ), 1 ≤ L → L ≤ 2 ^ b → ∀ (B : Builder n) (tw : ℕ → ℕ)
    (fw : ℕ → ℕ → ℕ),
    (∀ q < L, tw q < n + 2 + B.gates.length) → (∀ q < L, ∀ j < m, fw q j < n + 2 + B.gates.length) →
    ∃ (B' : Builder n) (ow : ℕ → ℕ), Extends B B' ∧ B'.nots ≤ B.nots + b ∧
      B'.monos ≤ B.monos + 4 * L * (m + 1) ∧ (∀ j < m, ow j < n + 2 + B'.gates.length) ∧
      ∀ inp, Gd n inp → (∀ q < L, ∀ j < m, B.eval inp (fw q j) = true → B.eval inp (tw q) = true) →
        ∀ lam ≤ L, (∀ q < L, B.eval inp (tw q) = true ↔ q < lam) →
          ∀ j < m, B'.eval inp (ow j) = if lam = 0 then false else B.eval inp (fw (lam - 1) j) := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
  intro b hL hLb B tw fw htw hfw
  by_cases hL1 : L = 1
  · subst hL1
    refine ⟨B, fun j => fw 0 j, Extends.refl B, by omega, by omega,
      fun j hj => hfw 0 (by omega) j hj, ?_⟩
    intro inp hg hft lam hlam htl j hj
    rcases Nat.lt_or_ge lam 1 with h0 | h1
    · have hl0 : lam = 0 := by omega
      subst hl0
      simp only [if_true]
      cases hv : B.eval inp (fw 0 j)
      · rfl
      · have := (htl 0 (by omega)).mp (hft 0 (by omega) j hj hv); omega
    · have hl1 : lam = 1 := by omega
      subst hl1; simp
  · have hL2 : 2 ≤ L := by omega
    have hb : 1 ≤ b := by
      rcases Nat.eq_zero_or_pos b with h | h
      · subst h; simp at hLb; omega
      · exact h
    have hhL : (L + 1) / 2 < L := by omega
    have hh1 : 1 ≤ (L + 1) / 2 := by omega
    have hhb : (L + 1) / 2 ≤ 2 ^ (b - 1) := by
      have : 2 ^ b = 2 * 2 ^ (b - 1) := by
        rw [← pow_succ']; congr 1; omega
      omega
    have hs1 := pushNot_spec B (tw ((L + 1) / 2)) (htw _ hhL)
    obtain ⟨hE1, hc1, hn1, hm1, hev1⟩ := hs1
    set B1 := (pushNot B (tw ((L + 1) / 2)) (htw _ hhL)).1 with hB1
    set c := (pushNot B (tw ((L + 1) / 2)) (htw _ hhL)).2 with hc
    let getw : ℕ → ℕ → ℕ := fun i j => if i < L then (if j < m then fw i j else tw i) else n
    have hgetw : ∀ i j, getw i j < n + 2 + B.gates.length := by
      intro i j; simp only [getw]
      split_ifs with h1 h2
      · exact hfw i h1 j h2
      · exact htw i h1
      · omega
    obtain ⟨B2, ws, h12, hn2, hm2, hc2⟩ := family
      (fun (qj : ℕ × ℕ) inp => B.eval inp (getw ((L + 1) / 2 + qj.1) qj.2) ||
        (B.eval inp (getw qj.1 qj.2) && !B.eval inp (tw ((L + 1) / 2)))) 2 B1
      ((List.range ((L + 1) / 2)) ×ˢ (List.range (m + 1))) (fun qj _ B' hB' => by
        have ha : getw qj.1 qj.2 < n + 2 + B'.gates.length := by
          have := hgetw qj.1 qj.2; have := hE1.1; have := hB'.1; omega
        have hcc : c < n + 2 + B'.gates.length := by have := hB'.1; omega
        have hsA := pushAnd_spec B' _ _ ha hcc
        have hb2 : getw ((L + 1) / 2 + qj.1) qj.2 < n + 2 + (pushAnd B' _ _ ha hcc).1.gates.length := by
          have := hgetw ((L + 1) / 2 + qj.1) qj.2; have := hE1.1; have := hB'.1; have := hsA.1.1; omega
        have hsO := pushOr_spec _ _ _ hb2 hsA.2.1
        refine ⟨_, _, hsA.1.trans hsO.1, by have := hsO.2.2.1; have := hsA.2.2.1; omega, by
          have := hsO.2.2.2.1; have := hsA.2.2.2.1; omega, hsO.2.1, fun inp hg => ?_⟩
        have hEB : Extends B (pushAnd B' _ _ ha hcc).1 := (hE1.trans hB').trans hsA.1
        rw [hsO.2.2.2.2 inp hg.1, hsA.2.2.2.2 inp hg.1, hEB.2 inp hg.1 _ (hgetw _ _),
          (hE1.trans hB').2 inp hg.1 _ (hgetw _ _), hB'.2 inp hg.1 _ hc1, hev1 inp hg.1])
      B1 (Extends.refl B1)
    have hws : ∀ q < (L + 1) / 2, ∀ j < m + 1, Cmp B2 (ws (q, j))
        (fun inp => B.eval inp (getw ((L + 1) / 2 + q) j) ||
          (B.eval inp (getw q j) && !B.eval inp (tw ((L + 1) / 2)))) := by
      intro q hq j hj
      exact hc2 (q, j) (List.mem_product.mpr ⟨List.mem_range.mpr hq, List.mem_range.mpr hj⟩)
    obtain ⟨B3, ow, h23, hn3, hm3, how, hev3⟩ := ih ((L + 1) / 2) hhL (b - 1) hh1 hhb B2
      (fun q => ws (q, m)) (fun q j => ws (q, j)) (fun q hq => (hws q hq m (by omega)).1)
      (fun q hq j hj => (hws q hq j (by omega)).1)
    refine ⟨B3, ow, (hE1.trans h12).trans h23, by omega, ?_, how, ?_⟩
    · rw [List.length_product, List.length_range, List.length_range] at hm2
      have h6 : 6 * ((L + 1) / 2) ≤ 4 * L := by omega
      have h7 : 6 * ((L + 1) / 2) * (m + 1) ≤ 4 * L * (m + 1) := Nat.mul_le_mul_right _ h6
      have h8 : 4 * ((L + 1) / 2) * (m + 1) + 2 * ((L + 1) / 2 * (m + 1)) =
        6 * ((L + 1) / 2) * (m + 1) := by ring
      omega
    · intro inp hg hft lam hlam htl j hj
      have hEB2 : Extends B B2 := hE1.trans h12
      have hfalse : B.eval inp n = false := by
        rw [B.eval_inp inp hg.1 n (by omega)]; exact hg.2.1
      have hgm : ∀ i, B.eval inp (getw i m) = (if i < L then B.eval inp (tw i) else false) := by
        intro i; simp only [getw, lt_irrefl, if_false]; split_ifs <;> simp [hfalse]
      have hgj : ∀ i, ∀ j' < m, B.eval inp (getw i j') =
          (if i < L then B.eval inp (fw i j') else false) := by
        intro i j' hj'; simp only [getw, if_pos hj']; split_ifs <;> simp [hfalse]
      have hval : ∀ q < (L + 1) / 2, ∀ j' < m + 1, B2.eval inp (ws (q, j')) =
          (B.eval inp (getw ((L + 1) / 2 + q) j') ||
            (B.eval inp (getw q j') && !B.eval inp (tw ((L + 1) / 2)))) :=
        fun q hq j' hj' => (hws q hq j' hj').2 inp hg
      by_cases hcase : (L + 1) / 2 < lam
      · have htrue : B.eval inp (tw ((L + 1) / 2)) = true := (htl _ hhL).mpr hcase
        have hv : ∀ q < (L + 1) / 2, ∀ j' < m + 1, B2.eval inp (ws (q, j')) =
            B.eval inp (getw ((L + 1) / 2 + q) j') := by
          intro q hq j' hj'; rw [hval q hq j' hj', htrue]; simp
        have hres := hev3 inp hg (fun q hq j' hj' h => by
            rw [hv q hq j' (by omega)] at h; rw [hv q hq m (by omega), hgm]
            rw [hgj _ j' hj'] at h
            split_ifs at h ⊢ with h1
            exact hft _ h1 j' hj' h)
          (lam - (L + 1) / 2) (by omega) (fun q hq => by
            rw [hv q hq m (by omega), hgm]
            split_ifs with h1
            · rw [htl _ h1]; omega
            · simp only [Bool.false_eq_true, false_iff]; omega) j hj
        rw [hres, if_neg (by omega), if_neg (by omega), hv _ (by omega) j (by omega), hgj _ j hj,
          if_pos (by omega)]
        congr 2; omega
      · have hfl : B.eval inp (tw ((L + 1) / 2)) = false := by
          cases h : B.eval inp (tw ((L + 1) / 2))
          · rfl
          · exact absurd ((htl _ hhL).mp h) hcase
        have hhi : ∀ i j', (L + 1) / 2 ≤ i → j' < m + 1 → B.eval inp (getw i j') = false := by
          intro i j' hi hj'
          by_cases hjm : j' < m
          · rw [hgj i j' hjm]
            split_ifs with h1
            · cases h : B.eval inp (fw i j')
              · rfl
              · have := (htl i h1).mp (hft i h1 j' hjm h); omega
            · rfl
          · rw [show j' = m by omega, hgm]
            split_ifs with h1
            · cases h : B.eval inp (tw i)
              · rfl
              · have := (htl i h1).mp h; omega
            · rfl
        have hv : ∀ q < (L + 1) / 2, ∀ j' < m + 1, B2.eval inp (ws (q, j')) =
            B.eval inp (getw q j') := by
          intro q hq j' hj'; rw [hval q hq j' hj', hfl, hhi _ j' (by omega) hj']; simp
        have hres := hev3 inp hg (fun q hq j' hj' h => by
            rw [hv q hq j' (by omega)] at h; rw [hv q hq m (by omega), hgm]
            rw [hgj _ j' hj'] at h
            split_ifs at h ⊢ with h1
            exact hft _ h1 j' hj' h)
          lam (by omega) (fun q hq => by
            rw [hv q hq m (by omega), hgm, if_pos (by omega)]
            exact htl q (by omega)) j hj
        rw [hres]
        split_ifs with h1
        · rfl
        · rw [hv _ (by omega) j (by omega), hgj _ j hj, if_pos (by omega)]

-- =========================================================================
-- Part B: cliques of the layered graph and label traces
-- =========================================================================

def adjS (n : ℕ) (E : Finset ℕ) (u v : ℕ) : Prop := u ≠ v ∧ min u v * n + max u v ∈ E

def clqS (n k : ℕ) (E : Finset ℕ) : Prop :=
  ∃ v : Fin k → Fin n, ∀ i j, i < j → adjS n E (v i).val (v j).val

def Tr (m : ℕ) (π : ℕ → Prop) (P : ℕ → ℕ → Prop) (q : ℕ) (l : ℕ → ℕ) : Prop :=
  (∀ p < q, l p < m ∧ π (l p)) ∧ (∀ p p', p < p' → p' < q → P (l p) (l p')) ∧
    (∀ p, p + 1 < q → l p ≠ l (p + 1))

def Hd (m q : ℕ) (π : ℕ → Prop) (P : ℕ → ℕ → Prop) (jok : ℕ → Prop) (k s k' s' : ℕ) : Prop :=
  if q ≤ k then s = m ∧ s' = m
  else if q ≤ k' then s' = m ∧ s < m ∧ π s ∧ (k + 1 = q → jok s)
  else s < m ∧ s' < m ∧ π s ∧ π s' ∧ (k + 1 = q → jok s) ∧ (k' + 1 = q → jok s') ∧ P s s' ∧
    (k' = k + 1 → s ≠ s')

lemma vlt {m a b s s' : ℕ} (hab : a < b) (hs : s ≤ m) : a * (m + 1) + s < b * (m + 1) + s' := by
  have h1 : (a + 1) * (m + 1) ≤ b * (m + 1) := Nat.mul_le_mul_right _ hab
  have h2 : (a + 1) * (m + 1) = a * (m + 1) + m + 1 := by ring
  omega

lemma vbound {m K a s : ℕ} (ha : a < K + 1) (hs : s ≤ m) : a * (m + 1) + s < (K + 1) * (m + 1) := by
  have := vlt (m := m) (s := s) (s' := 0) ha hs
  simpa using this

lemma adjS_symm {n : ℕ} {E : Finset ℕ} {u v : ℕ} (h : adjS n E u v) : adjS n E v u := by
  refine ⟨fun h' => h.1 h'.symm, ?_⟩
  rw [min_comm, max_comm]; exact h.2

lemma clq_iff_parts (K m : ℕ) (H : ℕ → ℕ → ℕ → ℕ → Prop) (E : Finset ℕ)
    (hE1 : ∀ k k' s s', k < k' → k' < K + 1 → s ≤ m → s' ≤ m →
      ((k * (m + 1) + s) * ((K + 1) * (m + 1)) + (k' * (m + 1) + s') ∈ E ↔ H k s k' s'))
    (hE2 : ∀ k s s', k < K + 1 → s < s' → s' ≤ m →
      (k * (m + 1) + s) * ((K + 1) * (m + 1)) + (k * (m + 1) + s') ∉ E) :
    clqS ((K + 1) * (m + 1)) (K + 1) E ↔ ∃ sp : ℕ → ℕ, (∀ p < K + 1, sp p ≤ m) ∧
      ∀ p p', p < p' → p' < K + 1 → H p (sp p) p' (sp p') := by
  constructor
  · rintro ⟨v, hv⟩
    have hadj : ∀ i j, i ≠ j → adjS ((K + 1) * (m + 1)) E (v i).val (v j).val := by
      intro i j hij
      rcases lt_or_gt_of_ne hij with h | h
      · exact hv i j h
      · exact adjS_symm (hv j i h)
    let kk : Fin (K + 1) → ℕ := fun i => (v i).val / (m + 1)
    let ss : Fin (K + 1) → ℕ := fun i => (v i).val % (m + 1)
    have hdec : ∀ i, (v i).val = kk i * (m + 1) + ss i := by
      intro i; simp only [kk, ss]; exact (Nat.div_add_mod' _ _).symm
    have hkk : ∀ i, kk i < K + 1 := by
      intro i; simp only [kk]
      rw [Nat.div_lt_iff_lt_mul (by omega)]; exact (v i).isLt
    have hss : ∀ i, ss i ≤ m := by
      intro i; simp only [ss]; have := Nat.mod_lt (v i).val (show 0 < m + 1 by omega); omega
    have hinj : ∀ i j, kk i = kk j → i = j := by
      intro i j hk
      by_contra hij
      have ha := hadj i j hij
      have hne : ss i ≠ ss j := by
        intro hs; apply ha.1; rw [hdec i, hdec j, hk, hs]
      rcases lt_or_gt_of_ne hne with hs | hs
      · have hlt : (v i).val < (v j).val := by rw [hdec i, hdec j, hk]; omega
        have := ha.2
        rw [min_eq_left hlt.le, max_eq_right hlt.le, hdec i, hdec j, hk] at this
        exact hE2 (kk j) (ss i) (ss j) (hkk j) hs (hss j) this
      · have hlt : (v j).val < (v i).val := by rw [hdec i, hdec j, hk]; omega
        have := ha.2
        rw [min_eq_right hlt.le, max_eq_left hlt.le, hdec i, hdec j, hk] at this
        exact hE2 (kk j) (ss j) (ss i) (hkk j) hs (hss i) this
    have hH : ∀ i j, kk i < kk j → H (kk i) (ss i) (kk j) (ss j) := by
      intro i j hk
      have hij : i ≠ j := by intro h; subst h; omega
      have ha := (hadj i j hij).2
      have hlt : (v i).val < (v j).val := by rw [hdec i, hdec j]; exact vlt hk (hss i)
      rw [min_eq_left hlt.le, max_eq_right hlt.le, hdec i, hdec j] at ha
      exact (hE1 _ _ _ _ hk (hkk j) (hss i) (hss j)).mp ha
    let κ : Fin (K + 1) → Fin (K + 1) := fun i => ⟨kk i, hkk i⟩
    have hκ : Function.Injective κ := by
      intro i j h; exact hinj i j (congrArg Fin.val h)
    have hsurj : Function.Surjective κ := Finite.surjective_of_injective hκ
    let pick : ℕ → Fin (K + 1) := fun p =>
      if h : p < K + 1 then Classical.choose (hsurj ⟨p, h⟩) else 0
    have hpick : ∀ p (hp : p < K + 1), kk (pick p) = p := by
      intro p hp
      simp only [pick, dif_pos hp]
      have := Classical.choose_spec (hsurj ⟨p, hp⟩)
      exact congrArg Fin.val this
    refine ⟨fun p => ss (pick p), fun p _ => hss _, fun p p' hpp hp' => ?_⟩
    have h1 := hpick p (by omega)
    have h2 := hpick p' hp'
    have := hH (pick p) (pick p') (by rw [h1, h2]; exact hpp)
    rw [h1, h2] at this
    exact this
  · rintro ⟨sp, hsp, hH⟩
    refine ⟨fun p => ⟨p.val * (m + 1) + sp p.val, vbound p.isLt (hsp p.val p.isLt)⟩, ?_⟩
    intro i j hij
    have hij' : i.val < j.val := hij
    have hlt : i.val * (m + 1) + sp i.val < j.val * (m + 1) + sp j.val :=
      vlt hij' (hsp i.val i.isLt)
    refine ⟨by simp only; omega, ?_⟩
    simp only
    rw [min_eq_left hlt.le, max_eq_right hlt.le]
    exact (hE1 _ _ _ _ hij' j.isLt (hsp _ i.isLt) (hsp _ j.isLt)).mpr (hH _ _ hij' j.isLt)

lemma parts_iff_trace (K m q : ℕ) (hK : 1 ≤ K) (hq1 : 1 ≤ q) (hq : q ≤ K + 1)
    (π : ℕ → Prop) (P : ℕ → ℕ → Prop) (jok : ℕ → Prop) :
    (∃ sp : ℕ → ℕ, (∀ p < K + 1, sp p ≤ m) ∧
      ∀ p p', p < p' → p' < K + 1 → Hd m q π P jok p (sp p) p' (sp p')) ↔
    ∃ l : ℕ → ℕ, Tr m π P q l ∧ jok (l (q - 1)) := by
  constructor
  · rintro ⟨sp, _, hH⟩
    have hok : ∀ p < q, sp p < m ∧ π (sp p) ∧ (p + 1 = q → jok (sp p)) := by
      intro p hp
      by_cases hp0 : p = 0
      · subst hp0
        have h := hH 0 1 (by omega) (by omega)
        unfold Hd at h
        rw [if_neg (by omega)] at h
        by_cases hq1' : q ≤ 1
        · rw [if_pos hq1'] at h; exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩
        · rw [if_neg hq1'] at h; exact ⟨h.1, h.2.2.1, h.2.2.2.2.1⟩
      · have h := hH 0 p (by omega) (by omega)
        unfold Hd at h
        rw [if_neg (by omega), if_neg (by omega)] at h
        exact ⟨h.2.1, h.2.2.2.1, h.2.2.2.2.2.1⟩
    refine ⟨sp, ⟨fun p hp => ⟨(hok p hp).1, (hok p hp).2.1⟩, fun p p' hpp hp' => ?_, fun p hp => ?_⟩,
      (hok (q - 1) (by omega)).2.2 (by omega)⟩
    · have h := hH p p' hpp (by omega)
      unfold Hd at h
      rw [if_neg (by omega), if_neg (by omega)] at h
      exact h.2.2.2.2.2.2.1
    · have h := hH p (p + 1) (by omega) (by omega)
      unfold Hd at h
      rw [if_neg (by omega), if_neg (by omega)] at h
      exact h.2.2.2.2.2.2.2 rfl
  · rintro ⟨l, ⟨hl1, hl2, hl3⟩, hj⟩
    refine ⟨fun p => if p < q then l p else m, fun p _ => ?_, fun p p' hpp hp' => ?_⟩
    · simp only; split_ifs with h
      · exact (hl1 p h).1.le
      · exact le_rfl
    · show Hd m q π P jok p (if p < q then l p else m) p' (if p' < q then l p' else m)
      unfold Hd
      by_cases h1 : q ≤ p
      · rw [if_pos h1, if_neg (show ¬ p < q by omega), if_neg (show ¬ p' < q by omega)]
        exact ⟨rfl, rfl⟩
      · rw [if_neg h1]
        by_cases h2 : q ≤ p'
        · rw [if_pos h2, if_neg (show ¬ p' < q by omega), if_pos (show p < q by omega)]
          refine ⟨rfl, (hl1 p (by omega)).1, (hl1 p (by omega)).2, fun he => ?_⟩
          rw [show p = q - 1 by omega]; exact hj
        · rw [if_neg h2, if_pos (show p < q by omega), if_pos (show p' < q by omega)]
          refine ⟨(hl1 p (by omega)).1, (hl1 p' (by omega)).1, (hl1 p (by omega)).2,
            (hl1 p' (by omega)).2, fun he => by omega, fun he => ?_, hl2 p p' hpp (by omega),
            fun he => ?_⟩
          · rw [show p' = q - 1 by omega]; exact hj
          · subst he; exact hl3 p (by omega)

lemma Tr.mono {m : ℕ} {π : ℕ → Prop} {P : ℕ → ℕ → Prop} {q : ℕ} {l : ℕ → ℕ}
    (h : Tr m π P q l) {q' : ℕ} (hq : q' ≤ q) : Tr m π P q' l :=
  ⟨fun p hp => h.1 p (by omega), fun p p' hpp hp' => h.2.1 p p' hpp (by omega),
    fun p hp => h.2.2 p (by omega)⟩

lemma Tr.weaken {m : ℕ} {π π' : ℕ → Prop} {P : ℕ → ℕ → Prop} {q : ℕ} {l : ℕ → ℕ}
    (h : Tr m π P q l) (hπ : ∀ a, π a → π' a) : Tr m π' P q l :=
  ⟨fun p hp => ⟨(h.1 p hp).1, hπ _ (h.1 p hp).2⟩, h.2.1, h.2.2⟩

lemma Tr.snoc {m : ℕ} {π : ℕ → Prop} {P : ℕ → ℕ → Prop} {q : ℕ} {l : ℕ → ℕ}
    (h : Tr m π P q l) (i : ℕ) (hi : i < m) (hπi : π i) (hP : ∀ p < q, P (l p) i)
    (hne : 1 ≤ q → l (q - 1) ≠ i) : Tr m π P (q + 1) (fun p => if p < q then l p else i) := by
  refine ⟨fun p hp => ?_, fun p p' hpp hp' => ?_, fun p hp => ?_⟩
  · simp only; split_ifs with h1
    · exact h.1 p h1
    · exact ⟨hi, hπi⟩
  · simp only [if_pos (show p < q by omega)]
    split_ifs with h1
    · exact h.2.1 p p' hpp h1
    · exact hP p (by omega)
  · simp only [if_pos (show p < q by omega)]
    split_ifs with h1
    · exact h.2.2 p (by omega)
    · have := hne (by omega); rwa [show q - 1 = p by omega] at this

lemma decode (m K : ℕ) (hK : 1 ≤ K) (PP : ℕ → ℕ → Prop) (QQ : ℕ → Prop) (i : ℕ) (hi : i < m)
    (hii : PP i i) (hQi : QQ i) (hext : ∀ a, QQ a → PP a i)
    (hNT : ¬ ∃ l, Tr m (fun a => PP a a) PP (K + 1) l) :
    ∃ lam0 < K, (∀ q0 < K, (∃ l, Tr m (fun a => PP a a ∧ QQ a) PP (q0 + 1) l) ↔ q0 < lam0 + 1) ∧
      ∀ j, (∃ l, Tr m (fun a => PP a a ∧ QQ a) PP (lam0 + 1) l ∧ l lam0 = j) ↔ j = i := by
  let T : ℕ → Prop := fun q => ∃ l, Tr m (fun a => PP a a ∧ QQ a) PP q l
  have hT1 : T 1 := ⟨fun _ => i, fun p hp => ⟨hi, hii, hQi⟩, fun p p' hpp hp' => by omega,
    fun p hp => by omega⟩
  let lam := Nat.findGreatest T K
  have hlam1 : 1 ≤ lam := Nat.le_findGreatest (P := T) hK hT1
  have hlamK : lam ≤ K := Nat.findGreatest_le K
  have hTlam : T lam := Nat.findGreatest_spec (P := T) hK hT1
  -- the key extension fact
  have hlast : ∀ l, Tr m (fun a => PP a a ∧ QQ a) PP lam l → l (lam - 1) = i := by
    intro l hl
    by_contra hne
    have hl' := hl.snoc i hi ⟨hii, hQi⟩ (fun p hp => hext _ (hl.1 p hp).2.2) (fun _ => hne)
    by_cases hle : lam + 1 ≤ K
    · have := Nat.le_findGreatest (P := T) hle ⟨_, hl'⟩
      omega
    · have hk : lam = K := by omega
      rw [hk] at hl'
      exact hNT ⟨_, hl'.weaken (fun a ha => ha.1)⟩
  refine ⟨lam - 1, by omega, fun q0 hq0 => ?_, fun j => ?_⟩
  · rw [show lam - 1 + 1 = lam by omega]
    constructor
    · intro h; have := Nat.le_findGreatest (P := T) (show q0 + 1 ≤ K by omega) h; omega
    · intro h; obtain ⟨l, hl⟩ := hTlam; exact ⟨l, hl.mono (by omega)⟩
  · rw [show lam - 1 + 1 = lam by omega]
    constructor
    · rintro ⟨l, hl, rfl⟩; exact hlast l hl
    · rintro rfl; obtain ⟨l, hl⟩ := hTlam; exact ⟨l, hl, hlast l hl⟩

-- =========================================================================
-- Part C: the NOT-count lower bound along chains
-- =========================================================================

lemma Tr.congr {m : ℕ} {π π' : ℕ → Prop} {P P' : ℕ → ℕ → Prop} {q : ℕ} {l : ℕ → ℕ}
    (h : Tr m π P q l) (hπ : ∀ a < m, π a → π' a) (hP : ∀ a < m, ∀ c < m, P a c → P' a c) :
    Tr m π' P' q l :=
  ⟨fun p hp => ⟨(h.1 p hp).1, hπ _ (h.1 p hp).1 (h.1 p hp).2⟩,
    fun p p' hpp hp' => hP _ (h.1 p (by omega)).1 _ (h.1 p' hp').1 (h.2.1 p p' hpp hp'), h.2.2⟩

lemma chain_bound {r m : ℕ} (C : Circuit) (hfan : FanInTwo C) (hrb : ReadsBack (r + 2) C)
    (o : Fin m → ℕ) (ho : ∀ j, o j < r + 2 + C.size) (inp : ℕ → List Bool) (K : ℕ)
    (hlen : ∀ p ≤ K, (inp p).length = r + 2)
    (hle : ∀ p < K, ∀ i < r + 2, (inp p).getD i false = true → (inp (p + 1)).getD i false = true)
    (lab : ℕ → Fin m) (hlab : ∀ p < K, lab p ≠ lab (p + 1))
    (hout : ∀ p ≤ K, ∀ j, (C.wires (inp p)).getD (o j) false = true ↔ lab p = j) :
    K < 2 ^ notCount C ∧ ∀ p < K, inp p ≠ inp (p + 1) := by
  have hstep : ∀ p < K, notVal r C (inp (p + 1)) < notVal r C (inp p) := by
    intro p hp
    rcases notVal_anti C hfan hrb (inp p) (inp (p + 1)) (hlen p (by omega))
      (hlen (p + 1) (by omega)) (hle p hp) with h | ⟨_, hmono⟩
    · exact h
    · exfalso
      have h1 : (C.wires (inp p)).getD (o (lab p)) false = true := (hout p (by omega) _).mpr rfl
      have h2 := hmono _ (ho _) h1
      have h3 := (hout (p + 1) (by omega) _).mp h2
      exact hlab p hp h3.symm
  have hacc : ∀ p ≤ K, notVal r C (inp p) + p ≤ notVal r C (inp 0) := by
    intro p hp
    induction p with
    | zero => simp
    | succ p ih => have := ih (by omega); have := hstep p (by omega); omega
  refine ⟨?_, fun p hp heq => ?_⟩
  · have := hacc K le_rfl
    have := notVal_lt r C (inp 0)
    omega
  · have h1 : (C.wires (inp p)).getD (o (lab p)) false = true := (hout p (by omega) _).mpr rfl
    rw [heq] at h1
    exact hlab p hp ((hout (p + 1) (by omega) _).mp h1).symm

lemma getD_app2 (l : List Bool) (i : ℕ) : (l ++ [false, true]).getD i false =
    if i < l.length then l.getD i false else if i = l.length + 1 then true else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; rw [List.getElem?_append_right (by omega)]; simp
  · rw [List.getElem?_append_right (by omega)]
    have : i - l.length = 0 ∨ i - l.length ≥ 2 := by omega
    rcases this with h | h
    · rw [h]; rfl
    · rw [List.getElem?_eq_none (by simp; omega)]; rfl

lemma getD_ofFn {r : ℕ} (f : Fin r → Bool) (i : ℕ) :
    (List.ofFn f).getD i false = if h : i < r then f ⟨i, h⟩ else false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split_ifs with h
  · simp [h]
  · simp [h]

def extF (m : ℕ) (Z : Fin m → Finset ℕ) (a : ℕ) : Finset ℕ := if h : a < m then Z ⟨a, h⟩ else ∅

def NTb (r m K : ℕ) (Ze Oe : ℕ → Finset ℕ) : Prop :=
  ¬ ∃ l, Tr m (fun a => Finset.range r \ Ze a ⊆ Oe a) (fun a c => Finset.range r \ Ze a ⊆ Oe c) (K + 1) l

lemma sdiff_inst (inst' : DecidableEq ℕ) (s t : Finset ℕ) :
    @SDiff.sdiff _ (@Finset.instSDiff ℕ inst') s t =
      @SDiff.sdiff _ (@Finset.instSDiff ℕ instDecidableEqNat) s t := by
  ext x; simp only [Finset.mem_sdiff]

lemma dtrue {p : Prop} {d : Decidable p} : @decide p d = true ↔ p := decide_eq_true_iff

lemma extF_fin {m : ℕ} (Z : Fin m → Finset ℕ) (i : Fin m) : extF m Z i.val = Z i := by
  simp only [extF, dif_pos i.isLt]

lemma fit_imp_NT (r m b K : ℕ) (hK : 2 ^ b ≤ K ∨ r + 1 ≤ K) (Z O : Fin m → Finset ℕ)
    (bf : Finset ℕ → List Bool) (hbl : ∀ Y, (bf Y).length = r + 2)
    (hbf : ∀ Y i, (bf Y).getD i false = true ↔ (i < r ∧ i ∈ Y) ∨ i = r + 1)
    (D : Circuit) (o : Fin m → ℕ) (hfan : FanInTwo D) (hrb : ReadsBack (r + 2) D)
    (hnc : notCount D ≤ b) (ho : ∀ j, o j < r + 2 + D.size)
    (hfit : ∀ Y ⊆ Finset.range r, ∀ i : Fin m, Finset.range r \ Z i ⊆ Y → Y ⊆ O i → ∀ j,
      (D.wires (bf Y)).getD (o j) false = true ↔ i = j) :
    NTb r m K (extF m Z) (extF m O) := by
  rintro ⟨l, hl⟩
  let Ze : ℕ → Finset ℕ := extF m Z
  let Y : ℕ → Finset ℕ := fun p => (Finset.range (p + 1)).biUnion (fun p' => Finset.range r \ Ze (l p'))
  have hYr : ∀ p, Y p ⊆ Finset.range r := by
    intro p x hx
    simp only [Y, Finset.mem_biUnion, Finset.mem_sdiff] at hx
    obtain ⟨_, _, hx, _⟩ := hx; exact hx
  have hYm : ∀ p, Y p ⊆ Y (p + 1) := by
    intro p x hx
    simp only [Y, Finset.mem_biUnion, Finset.mem_range] at hx ⊢
    obtain ⟨p', hp', hx⟩ := hx; exact ⟨p', by omega, hx⟩
  let lab : ℕ → Fin m := fun p => if h : l p < m then ⟨l p, h⟩ else
    ⟨l 0, (hl.1 0 (by omega)).1⟩
  have hlab : ∀ p < K + 1, (lab p).val = l p := by
    intro p hp; simp only [lab, dif_pos (hl.1 p hp).1]
  have hZ : ∀ p < K + 1, Z (lab p) = Ze (l p) := by
    intro p hp; simp only [Ze, extF, dif_pos (hl.1 p hp).1]
    congr 1; exact Fin.ext (hlab p hp)
  have hO : ∀ p < K + 1, O (lab p) = extF m O (l p) := by
    intro p hp; simp only [extF, dif_pos (hl.1 p hp).1]
    congr 1; exact Fin.ext (hlab p hp)
  have hout : ∀ p ≤ K, ∀ j, (D.wires (bf (Y p))).getD (o j) false = true ↔ lab p = j := by
    intro p hp j
    apply hfit (Y p) (hYr p) (lab p)
    · intro x hx
      rw [hZ p (by omega)] at hx
      simp only [Y, Finset.mem_biUnion, Finset.mem_range]
      exact ⟨p, by omega, hx⟩
    · intro x hx
      simp only [Y, Finset.mem_biUnion, Finset.mem_range] at hx
      obtain ⟨p', hp', hx⟩ := hx
      rw [hO p (by omega)]
      rcases Nat.lt_or_ge p' p with h | h
      · exact hl.2.1 p' p h (by omega) hx
      · have : p' = p := by omega
        subst this
        exact (hl.1 p' (by omega)).2 hx
  have hle : ∀ p < K, ∀ i < r + 2, (bf (Y p)).getD i false = true →
      (bf (Y (p + 1))).getD i false = true := by
    intro p _ i _ h
    rw [hbf] at h ⊢
    rcases h with ⟨h1, h2⟩ | h
    · exact Or.inl ⟨h1, hYm p h2⟩
    · exact Or.inr h
  have hlabne : ∀ p < K, lab p ≠ lab (p + 1) := by
    intro p hp heq
    have := congrArg Fin.val heq
    rw [hlab p (by omega), hlab (p + 1) (by omega)] at this
    exact hl.2.2 p (by omega) this
  obtain ⟨hK1, hne⟩ := chain_bound D hfan hrb o ho (fun p => bf (Y p)) K (fun p _ => hbl _) hle lab
    hlabne hout
  have hcard : ∀ p ≤ K, p ≤ (Y p).card := by
    intro p hp
    induction p with
    | zero => simp
    | succ p ih =>
      have h1 := ih (by omega)
      have h2 : Y p ≠ Y (p + 1) := fun h => hne p (by omega) (by simp only [h])
      have h3 : Y p ⊂ Y (p + 1) := Finset.ssubset_iff_subset_ne.mpr ⟨hYm p, h2⟩
      have := Finset.card_lt_card h3
      omega
  have h1 := hcard K le_rfl
  have h2 : (Y K).card ≤ r := by
    have := Finset.card_le_card (hYr K); simpa using this
  have h3 : 2 ^ notCount D ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) hnc
  omega

-- =========================================================================
-- Part D: the compiled circuit
-- =========================================================================

def zs (r : ℕ) (inp : List Bool) (a : ℕ) : Finset ℕ :=
  (Finset.range r).filter (fun x => inp.getD (a * r + x) false = true)

def os (m r : ℕ) (inp : List Bool) (a : ℕ) : Finset ℕ :=
  (Finset.range r).filter (fun x => inp.getD (m * r + a * r + x) false = true)

def xs (m r : ℕ) (inp : List Bool) : Finset ℕ :=
  (Finset.range r).filter (fun x => inp.getD (2 * (m * r) + x) false = true)

def PP (m r : ℕ) (inp : List Bool) (a c : ℕ) : Prop := Finset.range r \ zs r inp a ⊆ os m r inp c

def QQ (m r : ℕ) (inp : List Bool) (a : ℕ) : Prop := Finset.range r \ zs r inp a ⊆ xs m r inp

lemma PP_iff (m r : ℕ) (inp : List Bool) (a c : ℕ) : PP m r inp a c ↔
    ∀ x < r, inp.getD (a * r + x) false = true ∨ inp.getD (m * r + c * r + x) false = true := by
  unfold PP zs os
  constructor
  · intro h x hx
    by_cases hz : inp.getD (a * r + x) false = true
    · exact Or.inl hz
    · right
      have := h (Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hx, by simp only [Finset.mem_filter, not_and]; intro _; exact hz⟩)
      simp only [Finset.mem_filter] at this; exact this.2
  · intro h x hx
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range, not_and] at hx ⊢
    refine ⟨hx.1, ?_⟩
    rcases h x hx.1 with h1 | h1
    · exact absurd h1 (hx.2 hx.1)
    · exact h1

lemma QQ_iff (m r : ℕ) (inp : List Bool) (a : ℕ) : QQ m r inp a ↔
    ∀ x < r, inp.getD (a * r + x) false = true ∨ inp.getD (2 * (m * r) + x) false = true := by
  unfold QQ zs xs
  constructor
  · intro h x hx
    by_cases hz : inp.getD (a * r + x) false = true
    · exact Or.inl hz
    · right
      have := h (Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hx, by simp only [Finset.mem_filter, not_and]; intro _; exact hz⟩)
      simp only [Finset.mem_filter] at this; exact this.2
  · intro h x hx
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range, not_and] at hx ⊢
    refine ⟨hx.1, ?_⟩
    rcases h x hx.1 with h1 | h1
    · exact absurd h1 (hx.2 hx.1)
    · exact h1

lemma idx_lt {a m r x : ℕ} (ha : a < m) (hx : x < r) : a * r + x < m * r := by
  have h1 : (a + 1) * r ≤ m * r := Nat.mul_le_mul_right _ ha
  have h2 : (a + 1) * r = a * r + r := by ring
  omega

lemma and2 {n : ℕ} (B : Builder n) (u v : ℕ) (fu fv : List Bool → Bool) (hu : Cmp B u fu)
    (hv : Cmp B v fv) :
    ∃ (B' : Builder n) (o : ℕ), Extends B B' ∧ B'.nots = B.nots ∧ B'.monos ≤ B.monos + 1 ∧
      Cmp B' o (fun inp => fu inp && fv inp) := by
  have hs := pushAnd_spec B u v hu.1 hv.1
  refine ⟨_, _, hs.1, hs.2.2.1, by have := hs.2.2.2.1; omega, hs.2.1, fun inp hg => ?_⟩
  rw [hs.2.2.2.2 inp hg.1, hu.2 inp hg, hv.2 inp hg]

lemma and3 {n : ℕ} (B : Builder n) (u v w : ℕ) (fu fv fw : List Bool → Bool) (hu : Cmp B u fu)
    (hv : Cmp B v fv) (hw : Cmp B w fw) :
    ∃ (B' : Builder n) (o : ℕ), Extends B B' ∧ B'.nots = B.nots ∧ B'.monos ≤ B.monos + 2 ∧
      Cmp B' o (fun inp => fu inp && fv inp && fw inp) := by
  obtain ⟨B1, o1, h1, hn1, hm1, hc1⟩ := and2 B u v fu fv hu hv
  obtain ⟨B2, o2, h2, hn2, hm2, hc2⟩ := and2 B1 o1 w _ fw hc1 (hw.ext h1)
  exact ⟨B2, o2, h1.trans h2, by rw [hn2, hn1], by omega, hc2⟩

def gwire (n m q : ℕ) (jokB : ℕ → Bool) (Wπ : ℕ → ℕ) (Pπ : ℕ → ℕ → ℕ) (k s k' s' : ℕ) : ℕ :=
  if k = k' then n
  else if q ≤ k then (if s = m ∧ s' = m then n + 1 else n)
  else if q ≤ k' then (if s' = m ∧ s < m ∧ (k + 1 = q → jokB s = true) then Wπ s else n)
  else if s < m ∧ s' < m ∧ (k + 1 = q → jokB s = true) ∧ (k' + 1 = q → jokB s' = true) ∧
    (k' = k + 1 → s ≠ s') then Pπ s s' else n

def ewire (n m K q : ℕ) (jokB : ℕ → Bool) (Wπ : ℕ → ℕ) (Pπ : ℕ → ℕ → ℕ) (e : ℕ) : ℕ :=
  if e / ((K + 1) * (m + 1)) < e % ((K + 1) * (m + 1)) then
    gwire n m q jokB Wπ Pπ (e / ((K + 1) * (m + 1)) / (m + 1)) (e / ((K + 1) * (m + 1)) % (m + 1))
      (e % ((K + 1) * (m + 1)) / (m + 1)) (e % ((K + 1) * (m + 1)) % (m + 1))
  else n

lemma gwire_cases (n m q : ℕ) (jokB : ℕ → Bool) (Wπ : ℕ → ℕ) (Pπ : ℕ → ℕ → ℕ) (k s k' s' : ℕ) :
    gwire n m q jokB Wπ Pπ k s k' s' = n ∨ gwire n m q jokB Wπ Pπ k s k' s' = n + 1 ∨
    (∃ s0 < m, gwire n m q jokB Wπ Pπ k s k' s' = Wπ s0) ∨
    (∃ s0 < m, ∃ s1 < m, gwire n m q jokB Wπ Pπ k s k' s' = Pπ s0 s1) := by
  unfold gwire
  by_cases h1 : k = k'
  · rw [if_pos h1]; exact Or.inl rfl
  · rw [if_neg h1]
    by_cases h2 : q ≤ k
    · rw [if_pos h2]
      split_ifs
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
    · rw [if_neg h2]
      by_cases h3 : q ≤ k'
      · rw [if_pos h3]; split_ifs with h4
        · exact Or.inr (Or.inr (Or.inl ⟨s, h4.2.1, rfl⟩))
        · exact Or.inl rfl
      · rw [if_neg h3]; split_ifs with h4
        · exact Or.inr (Or.inr (Or.inr ⟨s, h4.1, s', h4.2.1, rfl⟩))
        · exact Or.inl rfl

lemma ewire_cases (n m K q : ℕ) (jokB : ℕ → Bool) (Wπ : ℕ → ℕ) (Pπ : ℕ → ℕ → ℕ) (e : ℕ) :
    ewire n m K q jokB Wπ Pπ e = n ∨ ewire n m K q jokB Wπ Pπ e = n + 1 ∨
    (∃ s0 < m, ewire n m K q jokB Wπ Pπ e = Wπ s0) ∨
    (∃ s0 < m, ∃ s1 < m, ewire n m K q jokB Wπ Pπ e = Pπ s0 s1) := by
  unfold ewire
  split_ifs
  · exact gwire_cases _ _ _ _ _ _ _ _ _ _
  · exact Or.inl rfl

lemma divmod_aux (a b c : ℕ) (hb : b < c) : (a * c + b) / c = a ∧ (a * c + b) % c = b := by
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega : 0 < c), Nat.div_eq_of_lt hb, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]

lemma pair_lt {u v N : ℕ} (hu : u < N) (hv : v < N) : u * N + v < N * N := by
  have h1 : (u + 1) * N ≤ N * N := Nat.mul_le_mul_right _ hu
  have h2 : (u + 1) * N = u * N + N := by ring
  omega

lemma ewire_at (n m K q : ℕ) (jokB : ℕ → Bool) (Wπ : ℕ → ℕ) (Pπ : ℕ → ℕ → ℕ) (k k' s s' : ℕ)
    (hk' : k' < K + 1) (hs : s ≤ m) (hs' : s' ≤ m) (hlt : k * (m + 1) + s < k' * (m + 1) + s') :
    ewire n m K q jokB Wπ Pπ ((k * (m + 1) + s) * ((K + 1) * (m + 1)) + (k' * (m + 1) + s')) =
      gwire n m q jokB Wπ Pπ k s k' s' := by
  have hv : k' * (m + 1) + s' < (K + 1) * (m + 1) := vbound hk' hs'
  have h1 := divmod_aux (k * (m + 1) + s) _ _ hv
  unfold ewire
  rw [h1.1, h1.2, if_pos hlt, (divmod_aux k s (m + 1) (by omega)).1,
    (divmod_aux k s (m + 1) (by omega)).2, (divmod_aux k' s' (m + 1) (by omega)).1,
    (divmod_aux k' s' (m + 1) (by omega)).2]

lemma test_sem (n m K q : ℕ) (hK : 1 ≤ K) (hq1 : 1 ≤ q) (hq : q ≤ K + 1) (jokB : ℕ → Bool)
    (Wπ : ℕ → ℕ) (Pπ : ℕ → ℕ → ℕ) (ev : ℕ → Bool) (hfalse : ev n = false) (htrue : ev (n + 1) = true)
    (π : ℕ → Prop) (P : ℕ → ℕ → Prop) (hW : ∀ s < m, (ev (Wπ s) = true ↔ π s))
    (hPw : ∀ s < m, ∀ s' < m, (ev (Pπ s s') = true ↔ π s ∧ π s' ∧ P s s')) :
    clqS ((K + 1) * (m + 1)) (K + 1)
      ((Finset.range ((K + 1) * (m + 1) * ((K + 1) * (m + 1)))).filter
        (fun e => ev (ewire n m K q jokB Wπ Pπ e) = true)) ↔
    ∃ l, Tr m π P q l ∧ jokB (l (q - 1)) = true := by
  rw [clq_iff_parts K m (Hd m q π P (fun s => jokB s = true)) _ ?_ ?_]
  · exact parts_iff_trace K m q hK hq1 hq π P (fun s => jokB s = true)
  · intro k k' s s' hkk hk' hs hs'
    have hlt : k * (m + 1) + s < k' * (m + 1) + s' := vlt hkk hs
    have hmem := pair_lt (vbound (show k < K + 1 by omega) hs) (vbound hk' hs')
    rw [Finset.mem_filter, Finset.mem_range, ewire_at n m K q jokB Wπ Pπ k k' s s' hk' hs hs' hlt]
    simp only [hmem, true_and]
    unfold gwire Hd
    beta_reduce
    rw [if_neg (by omega)]
    by_cases h2 : q ≤ k
    · rw [if_pos h2, if_pos h2]
      split_ifs with h3
      · exact ⟨fun _ => h3, fun _ => htrue⟩
      · rw [hfalse]; exact ⟨fun h => absurd h (by simp), fun h => absurd h h3⟩
    · rw [if_neg h2, if_neg h2]
      by_cases h3 : q ≤ k'
      · rw [if_pos h3, if_pos h3]
        split_ifs with h4
        · rw [hW s h4.2.1]
          exact ⟨fun h => ⟨h4.1, h4.2.1, h, h4.2.2⟩, fun h => h.2.2.1⟩
        · rw [hfalse]
          exact ⟨fun h => absurd h (by simp), fun h => absurd ⟨h.1, h.2.1, h.2.2.2⟩ h4⟩
      · rw [if_neg h3, if_neg h3]
        split_ifs with h4
        · rw [hPw s h4.1 s' h4.2.1]
          exact ⟨fun h => ⟨h4.1, h4.2.1, h.1, h.2.1, h4.2.2.1, h4.2.2.2.1, h.2.2, h4.2.2.2.2⟩,
            fun h => ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.2.2.1⟩⟩
        · rw [hfalse]
          exact ⟨fun h => absurd h (by simp), fun h => absurd ⟨h.1, h.2.1, h.2.2.2.2.1,
            h.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩ h4⟩
  · intro k s s' hk hss hs'
    have hlt : k * (m + 1) + s < k * (m + 1) + s' := by omega
    rw [Finset.mem_filter, ewire_at n m K q jokB Wπ Pπ k k s s' hk (by omega) hs' hlt]
    unfold gwire
    rw [if_pos rfl, hfalse]
    simp

lemma test_block {n : ℕ} (m K q : ℕ) (S : Circuit) (hSfan : FanInTwo S)
    (hSrb : ReadsBack ((K + 1) * (m + 1) * ((K + 1) * (m + 1)) + 2) S)
    (hSout : S.output < (K + 1) * (m + 1) * ((K + 1) * (m + 1)) + 2 + S.size) (hSnc : notCount S = 0)
    (jokB : ℕ → Bool) (Wπ : ℕ → ℕ) (Pπ : ℕ → ℕ → ℕ) (B : Builder n)
    (hW : ∀ s < m, Wπ s < n + 2 + B.gates.length)
    (hP : ∀ s < m, ∀ s' < m, Pπ s s' < n + 2 + B.gates.length) :
    ∃ (B' : Builder n) (o : ℕ), Extends B B' ∧ B'.nots = B.nots ∧
      B'.monos ≤ B.monos + ((K + 1) * (m + 1) * ((K + 1) * (m + 1)) + 2 + S.size) ∧
      Cmp B' o (fun inp => S.eval (List.ofFn (fun e : Fin ((K + 1) * (m + 1) * ((K + 1) * (m + 1))) =>
        B.eval inp (ewire n m K q jokB Wπ Pπ e.val)) ++ [false, true])) := by
  let ins : List ℕ := List.ofFn (fun e : Fin ((K + 1) * (m + 1) * ((K + 1) * (m + 1))) =>
    ewire n m K q jokB Wπ Pπ e.val) ++ [n, n + 1]
  have hins : ∀ w ∈ ins, w < n + 2 + B.gates.length := by
    intro w hw
    simp only [ins, List.mem_append, List.mem_ofFn, List.mem_cons,
      List.not_mem_nil, or_false] at hw
    rcases hw with ⟨e, rfl⟩ | rfl | rfl
    · rcases ewire_cases n m K q jokB Wπ Pπ e.val with h | h | ⟨s0, hs0, h⟩ | ⟨s0, hs0, s1, hs1, h⟩
      · rw [h]; omega
      · rw [h]; omega
      · rw [h]; exact hW s0 hs0
      · rw [h]; exact hP s0 hs0 s1 hs1
    · omega
    · omega
  obtain ⟨B', hE, hn, hm, hev⟩ := embed S _ hSfan hSrb B ins
    (by simp only [ins, List.length_append, List.length_ofFn]; rfl) hins
  have hlen : B'.gates.length = B.gates.length +
      ((K + 1) * (m + 1) * ((K + 1) * (m + 1)) + 2) + S.size := by
    have e1 := Builder.gates_len_eq B
    have e2 := Builder.gates_len_eq B'
    rw [hSnc] at hn hm
    omega
  refine ⟨B', n + 2 + B.gates.length + S.output, hE, by rw [hn, hSnc]; rfl,
    by rw [hm, hSnc]; omega, by omega, fun inp hg => ?_⟩
  rw [hev inp hg.1 S.output hSout]
  unfold Circuit.eval
  have hX : ins.map (B.eval inp) = List.ofFn (fun e : Fin ((K + 1) * (m + 1) * ((K + 1) * (m + 1))) =>
      B.eval inp (ewire n m K q jokB Wπ Pπ e.val)) ++ [false, true] := by
    simp only [ins, List.map_append, List.map_ofFn, List.map_cons, List.map_nil]
    rw [B.eval_inp inp hg.1 n (by omega), B.eval_inp inp hg.1 (n + 1) (by omega), hg.2.1, hg.2.2]
    rfl
  rw [hX]

lemma arith_bound (r m K s NN : ℕ) :
    2 * r * (m * m) + 2 * r * m + 1 * m + 2 * (m * m) + 2 * (m * m) + (NN + 2 + s) +
      (NN + 2 + s) * (K * m) + m * K + 4 * K * (m + 1) ≤
    32 * (r + 1) * (m + 1) ^ 2 + 32 * (K + 1) * (m + 1) * (s + NN + 1) := by
  ring_nf
  omega

def evSet (NN : ℕ) (ev : ℕ → Bool) : Finset ℕ := (Finset.range NN).filter (fun e => ev e = true)

lemma mem_evSet (NN : ℕ) (ev : ℕ → Bool) (e : ℕ) : e ∈ evSet NN ev ↔ e < NN ∧ ev e = true := by
  simp [evSet]

lemma construct (r m b K : ℕ) (hK1 : 1 ≤ K) (hKb : K ≤ 2 ^ b) (S : Circuit) (hSfan : FanInTwo S)
    (hSrb : ReadsBack ((K + 1) * (m + 1) * ((K + 1) * (m + 1)) + 2) S)
    (hSout : S.output < (K + 1) * (m + 1) * ((K + 1) * (m + 1)) + 2 + S.size) (hSnc : notCount S = 0)
    (hSsem : ∀ ev : ℕ → Bool,
      S.eval (List.ofFn (fun e : Fin ((K + 1) * (m + 1) * ((K + 1) * (m + 1))) => ev e.val) ++
        [false, true]) = true ↔
      clqS ((K + 1) * (m + 1)) (K + 1) (evSet ((K + 1) * (m + 1) * ((K + 1) * (m + 1))) ev)) :
    ∃ (B : Builder (2 * m * r + r)) (gout : ℕ) (ow : ℕ → ℕ), B.nots ≤ b ∧
      B.monos ≤ 32 * (r + 1) * (m + 1) ^ 2 + 32 * (K + 1) * (m + 1) *
        (S.size + (K + 1) * (m + 1) * ((K + 1) * (m + 1)) + 1) ∧
      gout < 2 * m * r + r + 2 + B.gates.length ∧
      (∀ j < m, ow j < 2 * m * r + r + 2 + B.gates.length) ∧
      ∀ inp, Gd (2 * m * r + r) inp →
        (B.eval inp gout = true ↔ ∃ l, Tr m (fun a => PP m r inp a a) (PP m r inp) (K + 1) l) ∧
        ((¬ ∃ l, Tr m (fun a => PP m r inp a a) (PP m r inp) (K + 1) l) → ∀ i < m,
          Finset.range r \ zs r inp i ⊆ xs m r inp → xs m r inp ⊆ os m r inp i →
          ∀ j < m, (B.eval inp (ow j) = true ↔ j = i)) := by
  have hn' : 2 * m * r + r = 2 * (m * r) + r := by ring
  -- the subset tests between lower and upper corners
  obtain ⟨B1, Pw, h01, hn1, hm1, hP⟩ := family (fun (ac : ℕ × ℕ) inp => decide (PP m r inp ac.1 ac.2))
    (2 * r) (Builder.empty (2 * m * r + r)) ((List.range m) ×ˢ (List.range m)) (fun ac hac B hB => by
      obtain ⟨a, c⟩ := ac
      obtain ⟨ha, hc⟩ := List.mem_product.mp hac
      rw [List.mem_range] at ha hc
      obtain ⟨B', w, hE, hnn, hmm, hcm⟩ := andOr B r (fun x => a * r + x) (fun x => m * r + c * r + x)
        (fun x hx => by have := idx_lt ha hx; omega) (fun x hx => by have := idx_lt hc hx; omega)
      refine ⟨B', w, hE, hnn, hmm, hcm.1, fun inp hg => ?_⟩
      rw [hcm.2 inp hg]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      rw [PP_iff]
      apply forall_congr'; intro x; apply imp_congr_right; intro hx
      rw [B.eval_inp inp hg.1 (a * r + x) (by have := idx_lt ha hx; omega),
        B.eval_inp inp hg.1 (m * r + c * r + x) (by have := idx_lt hc hx; omega)])
    (Builder.empty _) (Extends.refl _)
  rw [List.length_product, List.length_range] at hm1
  -- the tests of lower corners against the point
  obtain ⟨B2, Qw, h12, hn2, hm2, hQ⟩ := family (fun a inp => decide (QQ m r inp a)) (2 * r) B1
    (List.range m) (fun a ha B hB => by
      rw [List.mem_range] at ha
      obtain ⟨B', w, hE, hnn, hmm, hcm⟩ := andOr B r (fun x => a * r + x) (fun x => 2 * (m * r) + x)
        (fun x hx => by have := idx_lt ha hx; omega) (fun x hx => by omega)
      refine ⟨B', w, hE, hnn, hmm, hcm.1, fun inp hg => ?_⟩
      rw [hcm.2 inp hg]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      rw [QQ_iff]
      apply forall_congr'; intro x; apply imp_congr_right; intro hx
      rw [B.eval_inp inp hg.1 (a * r + x) (by have := idx_lt ha hx; omega),
        B.eval_inp inp hg.1 (2 * (m * r) + x) (by omega)])
    B1 (Extends.refl _)
  rw [List.length_range] at hm2
  have hP2 : ∀ a < m, ∀ c < m, Cmp B2 (Pw (a, c)) (fun inp => decide (PP m r inp a c)) :=
    fun a ha c hc =>
      (hP (a, c) (List.mem_product.mpr ⟨List.mem_range.mpr ha, List.mem_range.mpr hc⟩)).ext h12
  have hQ2 : ∀ a < m, Cmp B2 (Qw a) (fun inp => decide (QQ m r inp a)) :=
    fun a ha => hQ a (List.mem_range.mpr ha)
  -- vertex permissions for the point tests
  obtain ⟨B3, Ww, h23, hn3, hm3, hW⟩ := family
    (fun a inp => decide (PP m r inp a a ∧ QQ m r inp a)) 1 B2 (List.range m) (fun a ha B hB => by
      rw [List.mem_range] at ha
      obtain ⟨B', w, hE, hnn, hmm, hcm⟩ := and2 B _ _ _ _ ((hP2 a ha a ha).ext hB) ((hQ2 a ha).ext hB)
      refine ⟨B', w, hE, hnn, hmm, hcm.1, fun inp hg => ?_⟩
      rw [hcm.2 inp hg]; apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, decide_eq_true_eq])
    B2 (Extends.refl _)
  rw [List.length_range] at hm3
  have hP3 : ∀ a < m, ∀ c < m, Cmp B3 (Pw (a, c)) (fun inp => decide (PP m r inp a c)) :=
    fun a ha c hc => (hP2 a ha c hc).ext h23
  have hW3 : ∀ a < m, Cmp B3 (Ww a) (fun inp => decide (PP m r inp a a ∧ QQ m r inp a)) :=
    fun a ha => hW a (List.mem_range.mpr ha)
  -- edge permissions for the point tests
  obtain ⟨B4, PXw, h34, hn4, hm4, hPX⟩ := family (fun (ac : ℕ × ℕ) inp =>
      decide ((PP m r inp ac.1 ac.1 ∧ QQ m r inp ac.1) ∧ (PP m r inp ac.2 ac.2 ∧ QQ m r inp ac.2) ∧
        PP m r inp ac.1 ac.2)) 2 B3 ((List.range m) ×ˢ (List.range m)) (fun ac hac B hB => by
      obtain ⟨a, c⟩ := ac
      obtain ⟨ha, hc⟩ := List.mem_product.mp hac
      rw [List.mem_range] at ha hc
      obtain ⟨B', w, hE, hnn, hmm, hcm⟩ := and3 B _ _ _ _ _ _ ((hW3 a ha).ext hB) ((hW3 c hc).ext hB)
        ((hP3 a ha c hc).ext hB)
      refine ⟨B', w, hE, hnn, hmm, hcm.1, fun inp hg => ?_⟩
      rw [hcm.2 inp hg]; apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc])
    B3 (Extends.refl _)
  rw [List.length_product, List.length_range] at hm4
  have hP4 : ∀ a < m, ∀ c < m, Cmp B4 (Pw (a, c)) (fun inp => decide (PP m r inp a c)) :=
    fun a ha c hc => (hP3 a ha c hc).ext h34
  -- edge permissions for the top test
  obtain ⟨B5, PGw, h45, hn5, hm5, hPG⟩ := family (fun (ac : ℕ × ℕ) inp =>
      decide (PP m r inp ac.1 ac.1 ∧ PP m r inp ac.2 ac.2 ∧ PP m r inp ac.1 ac.2)) 2 B4
      ((List.range m) ×ˢ (List.range m)) (fun ac hac B hB => by
      obtain ⟨a, c⟩ := ac
      obtain ⟨ha, hc⟩ := List.mem_product.mp hac
      rw [List.mem_range] at ha hc
      obtain ⟨B', w, hE, hnn, hmm, hcm⟩ := and3 B _ _ _ _ _ _ ((hP4 a ha a ha).ext hB)
        ((hP4 c hc c hc).ext hB) ((hP4 a ha c hc).ext hB)
      refine ⟨B', w, hE, hnn, hmm, hcm.1, fun inp hg => ?_⟩
      rw [hcm.2 inp hg]; apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc])
    B4 (Extends.refl _)
  rw [List.length_product, List.length_range] at hm5
  have hP5 : ∀ a < m, ∀ c < m, Cmp B5 (Pw (a, c)) (fun inp => decide (PP m r inp a c)) :=
    fun a ha c hc => (hP4 a ha c hc).ext h45
  have hW5 : ∀ a < m, Cmp B5 (Ww a) (fun inp => decide (PP m r inp a a ∧ QQ m r inp a)) :=
    fun a ha => ((hW3 a ha).ext h34).ext h45
  have hPX5 : ∀ a < m, ∀ c < m, Cmp B5 (PXw (a, c)) (fun inp =>
      decide ((PP m r inp a a ∧ QQ m r inp a) ∧ (PP m r inp c c ∧ QQ m r inp c) ∧ PP m r inp a c)) :=
    fun a ha c hc =>
      (hPX (a, c) (List.mem_product.mpr ⟨List.mem_range.mpr ha, List.mem_range.mpr hc⟩)).ext h45
  have hPG5 : ∀ a < m, ∀ c < m, Cmp B5 (PGw (a, c)) (fun inp =>
      decide (PP m r inp a a ∧ PP m r inp c c ∧ PP m r inp a c)) :=
    fun a ha c hc => hPG (a, c) (List.mem_product.mpr ⟨List.mem_range.mpr ha, List.mem_range.mpr hc⟩)
  -- the top test: a trace with K+1 labels
  obtain ⟨B6, gout, h56, hn6, hm6, hg6⟩ := test_block m K (K + 1) S hSfan hSrb hSout hSnc
    (fun _ => true) (fun s => Pw (s, s)) (fun s s' => PGw (s, s')) B5
    (fun s hs => (hP5 s hs s hs).1) (fun s hs s' hs' => (hPG5 s hs s' hs').1)
  have hglob : ∀ inp, Gd (2 * m * r + r) inp → (B6.eval inp gout = true ↔
      ∃ l, Tr m (fun a => PP m r inp a a) (PP m r inp) (K + 1) l) := by
    intro inp hg
    rw [hg6.2 inp hg]
    have hfalse : B5.eval inp (2 * m * r + r) = false := by
      rw [B5.eval_inp inp hg.1 _ (by omega)]; exact hg.2.1
    have htrue : B5.eval inp (2 * m * r + r + 1) = true := by
      rw [B5.eval_inp inp hg.1 _ (by omega)]; exact hg.2.2
    refine (hSsem (fun e => B5.eval inp (ewire (2 * m * r + r) m K (K + 1) (fun _ => true)
      (fun s => Pw (s, s)) (fun s s' => PGw (s, s')) e))).trans
      ((test_sem (2 * m * r + r) m K (K + 1) hK1 (by omega) le_rfl (fun _ => true) (fun s => Pw (s, s))
        (fun s s' => PGw (s, s')) (B5.eval inp) hfalse htrue (fun a => PP m r inp a a) (PP m r inp)
        ?_ ?_).trans ?_)
    · intro s hs; rw [(hP5 s hs s hs).2 inp hg]; exact decide_eq_true_iff
    · intro s hs s' hs'; rw [(hPG5 s hs s' hs').2 inp hg]; exact decide_eq_true_iff
    · exact ⟨fun ⟨l, hl, _⟩ => ⟨l, hl⟩, fun ⟨l, hl⟩ => ⟨l, hl, rfl⟩⟩
  -- the point tests: traces below the point by length and last label
  obtain ⟨B7, Tw, h67, hn7, hm7, hT⟩ := family (fun (qj : ℕ × ℕ) inp =>
      decide (∃ l, Tr m (fun a => PP m r inp a a ∧ QQ m r inp a) (PP m r inp) (qj.1 + 1) l ∧
        l qj.1 = qj.2))
      ((K + 1) * (m + 1) * ((K + 1) * (m + 1)) + 2 + S.size) B6 ((List.range K) ×ˢ (List.range m))
      (fun qj hqj B hB => by
        obtain ⟨q0, j⟩ := qj
        obtain ⟨hq0, hj⟩ := List.mem_product.mp hqj
        rw [List.mem_range] at hq0 hj
        have hB5 : Extends B5 B := h56.trans hB
        obtain ⟨B', o, hE, hnn, hmm, hco⟩ := test_block m K (q0 + 1) S hSfan hSrb hSout hSnc
          (fun s => decide (s = j)) Ww (fun s s' => PXw (s, s')) B
          (fun s hs => ((hW5 s hs).ext hB5).1) (fun s hs s' hs' => ((hPX5 s hs s' hs').ext hB5).1)
        refine ⟨B', o, hE, hnn, hmm, hco.1, fun inp hg => ?_⟩
        rw [hco.2 inp hg]
        have hfalse : B.eval inp (2 * m * r + r) = false := by
          rw [B.eval_inp inp hg.1 _ (by omega)]; exact hg.2.1
        have htrue : B.eval inp (2 * m * r + r + 1) = true := by
          rw [B.eval_inp inp hg.1 _ (by omega)]; exact hg.2.2
        apply Bool.eq_iff_iff.mpr
        rw [decide_eq_true_iff]
        refine (hSsem (fun e => B.eval inp (ewire (2 * m * r + r) m K (q0 + 1) (fun s => decide (s = j))
          Ww (fun s s' => PXw (s, s')) e))).trans
          ((test_sem (2 * m * r + r) m K (q0 + 1) hK1 (by omega) (by omega) (fun s => decide (s = j))
            Ww (fun s s' => PXw (s, s')) (B.eval inp) hfalse htrue
            (fun a => PP m r inp a a ∧ QQ m r inp a) (PP m r inp) ?_ ?_).trans ?_)
        · intro s hs; rw [((hW5 s hs).ext hB5).2 inp hg]; exact decide_eq_true_iff
        · intro s hs s' hs'; rw [((hPX5 s hs s' hs').ext hB5).2 inp hg]; exact decide_eq_true_iff
        · simp only [Nat.add_sub_cancel, decide_eq_true_eq])
      B6 (Extends.refl _)
  rw [List.length_product, List.length_range, List.length_range] at hm7
  have hT7 : ∀ q0 < K, ∀ j < m, Cmp B7 (Tw (q0, j)) (fun inp =>
      decide (∃ l, Tr m (fun a => PP m r inp a a ∧ QQ m r inp a) (PP m r inp) (q0 + 1) l ∧ l q0 = j)) :=
    fun q0 hq0 j hj => hT (q0, j) (List.mem_product.mpr ⟨List.mem_range.mpr hq0, List.mem_range.mpr hj⟩)
  -- the level tests: any trace of a given length below the point
  obtain ⟨B8, Tqw, h78, hn8, hm8, hTq⟩ := family (fun q0 inp =>
      decide (∃ l, Tr m (fun a => PP m r inp a a ∧ QQ m r inp a) (PP m r inp) (q0 + 1) l)) m B7
      (List.range K) (fun q0 hq0 B hB => by
        rw [List.mem_range] at hq0
        have hws : ∀ w ∈ (List.range m).map (fun j => Tw (q0, j)),
            w < 2 * m * r + r + 2 + B.gates.length := by
          intro w hw
          obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hw
          exact ((hT7 q0 hq0 j (List.mem_range.mp hj)).ext hB).1
        obtain ⟨B', out, hE, hlt, hnn, hmm, hev⟩ := exists_or_list _ B hws
        refine ⟨B', out, hE, hnn, by simpa using hmm, hlt, fun inp hg => ?_⟩
        rw [hev inp hg.1 hg.2.1]
        apply Bool.eq_iff_iff.mpr
        rw [decide_eq_true_iff, List.any_map, List.any_eq_true]
        constructor
        · rintro ⟨j, hj, hv⟩
          have := ((hT7 q0 hq0 j (List.mem_range.mp hj)).ext hB).2 inp hg
          simp only [Function.comp] at hv
          rw [this, decide_eq_true_iff] at hv
          obtain ⟨l, hl, _⟩ := hv; exact ⟨l, hl⟩
        · rintro ⟨l, hl⟩
          refine ⟨l q0, List.mem_range.mpr (hl.1 q0 (by omega)).1, ?_⟩
          simp only [Function.comp]
          rw [((hT7 q0 hq0 (l q0) (hl.1 q0 (by omega)).1).ext hB).2 inp hg, decide_eq_true_iff]
          exact ⟨l, hl, rfl⟩)
      B7 (Extends.refl _)
  rw [List.length_range] at hm8
  have hTq8 : ∀ q0 < K, Cmp B8 (Tqw q0) (fun inp =>
      decide (∃ l, Tr m (fun a => PP m r inp a a ∧ QQ m r inp a) (PP m r inp) (q0 + 1) l)) :=
    fun q0 hq0 => hTq q0 (List.mem_range.mpr hq0)
  have hT8 : ∀ q0 < K, ∀ j < m, Cmp B8 (Tw (q0, j)) (fun inp =>
      decide (∃ l, Tr m (fun a => PP m r inp a a ∧ QQ m r inp a) (PP m r inp) (q0 + 1) l ∧ l q0 = j)) :=
    fun q0 hq0 j hj => (hT7 q0 hq0 j hj).ext h78
  -- fold the levels with shared NOT gates
  obtain ⟨B9, ow, h89, hn9, hm9, how, hev9⟩ := fold (m := m) K b hK1 hKb B8 Tqw (fun q j => Tw (q, j))
    (fun q hq => (hTq8 q hq).1) (fun q hq j hj => (hT8 q hq j hj).1)
  have h0n : (Builder.empty (2 * m * r + r)).nots = 0 := rfl
  have h0m : (Builder.empty (2 * m * r + r)).monos = 0 := rfl
  refine ⟨B9, gout, ow, by omega, ?_, ?_, how, fun inp hg => ⟨?_, ?_⟩⟩
  · have := arith_bound r m K S.size ((K + 1) * (m + 1) * ((K + 1) * (m + 1)))
    omega
  · have := hg6.1; have := h67.1; have := h78.1; have := h89.1; omega
  · rw [h89.2 inp hg.1 gout (by have := hg6.1; have := h67.1; have := h78.1; omega),
      h78.2 inp hg.1 gout (by have := hg6.1; have := h67.1; omega), h67.2 inp hg.1 gout hg6.1]
    exact hglob inp hg
  · intro hNT i hi hzx hxo j hj
    obtain ⟨lam0, hlam0, hlev, hlast⟩ := decode m K hK1 (PP m r inp) (QQ m r inp) i hi
      (Finset.Subset.trans hzx hxo) hzx (fun a ha => Finset.Subset.trans ha hxo) hNT
    rw [hev9 inp hg (fun q hq j' hj' h => by
        rw [(hT8 q hq j' hj').2 inp hg, decide_eq_true_iff] at h
        rw [(hTq8 q hq).2 inp hg, decide_eq_true_iff]
        obtain ⟨l, hl, _⟩ := h; exact ⟨l, hl⟩) (lam0 + 1) (by omega) (fun q hq => by
        rw [(hTq8 q hq).2 inp hg, decide_eq_true_iff]; exact hlev q hq) j hj]
    rw [if_neg (by omega), Nat.add_sub_cancel, (hT8 lam0 hlam0 j hj).2 inp hg, decide_eq_true_iff]
    exact hlast j

-- =========================================================================
-- Part E: inputs of the book, restriction to one book, and the statement
-- =========================================================================

lemma gl (l1 l2 : List Bool) (i : ℕ) (h : i < l1.length) : (l1 ++ l2).getD i false = l1.getD i false := by
  simp only [List.getD_eq_getElem?_getD]; rw [List.getElem?_append_left h]

lemma gr (l1 l2 : List Bool) (i : ℕ) (h : l1.length ≤ i) :
    (l1 ++ l2).getD i false = l2.getD (i - l1.length) false := by
  simp only [List.getD_eq_getElem?_getD]; rw [List.getElem?_append_right h]

lemma flat_len (m r : ℕ) (g : Fin m → Fin r → Bool) :
    ((List.ofFn (fun i => List.ofFn (g i))).flatten).length = m * r := by
  simp [List.length_flatten, List.sum_ofFn]

lemma flat_getD (m r : ℕ) (g : Fin m → Fin r → Bool) (a x : ℕ) (ha : a < m) (hx : x < r) :
    (List.ofFn (fun i => List.ofFn (g i))).flatten.getD (a * r + x) false = g ⟨a, ha⟩ ⟨x, hx⟩ := by
  have hlt : a * r + x < m * r := idx_lt ha hx
  have hr : 0 < r := by omega
  have key : (List.ofFn (fun i => List.ofFn (g i))).flatten = List.ofFn (fun w : Fin (m * r) =>
      g ⟨w.val / r, Nat.div_lt_of_lt_mul (lt_of_lt_of_eq w.isLt (Nat.mul_comm m r))⟩
        ⟨w.val % r, Nat.mod_lt _ hr⟩) := by
    rw [List.ofFn_mul]
    congr 2
    funext i
    congr 1
    funext j
    exact congrArg₂ g (Fin.ext (divmod_aux i.val j.val r j.isLt).1.symm)
      (Fin.ext (divmod_aux i.val j.val r j.isLt).2.symm)
  rw [key, getD_ofFn, dif_pos hlt]
  exact congrArg₂ g (Fin.ext (divmod_aux a x r hx).1) (Fin.ext (divmod_aux a x r hx).2)

lemma I_facts (m r : ℕ) (gZ gO : Fin m → Fin r → Bool) (gX : Fin r → Bool) (I : List Bool)
    (hI : I = (List.ofFn (fun i => List.ofFn (gZ i))).flatten ++
      (List.ofFn (fun i => List.ofFn (gO i))).flatten ++ List.ofFn gX ++ [false, true]) :
    Gd (2 * m * r + r) I ∧
    (∀ a (ha : a < m) x (hx : x < r), I.getD (a * r + x) false = gZ ⟨a, ha⟩ ⟨x, hx⟩) ∧
    (∀ a (ha : a < m) x (hx : x < r), I.getD (m * r + a * r + x) false = gO ⟨a, ha⟩ ⟨x, hx⟩) ∧
    (∀ x (hx : x < r), I.getD (2 * (m * r) + x) false = gX ⟨x, hx⟩) := by
  have hn' : 2 * m * r + r = 2 * (m * r) + r := by ring
  have h1 := flat_len m r gZ
  have h2 := flat_len m r gO
  have h3 : (List.ofFn gX).length = r := List.length_ofFn
  have hL : ((List.ofFn (fun i => List.ofFn (gZ i))).flatten ++
      (List.ofFn (fun i => List.ofFn (gO i))).flatten ++ List.ofFn gX).length = 2 * (m * r) + r := by
    simp only [List.length_append, h1, h2, h3]; ring
  subst hI
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp only [List.length_append, h1, h2, h3, List.length_cons, List.length_nil]; ring
  · rw [getD_app2, hL, if_neg (by omega), if_neg (by omega)]
  · rw [getD_app2, hL, if_neg (by omega), if_pos (by omega)]
  · intro a ha x hx
    have := idx_lt ha hx
    rw [gl _ _ _ (by simp only [List.length_append, h1, h2, h3]; omega), gl _ _ _ (by simp only [List.length_append, h1, h2]; omega),
      gl _ _ _ (by rw [h1]; omega), flat_getD m r gZ a x ha hx]
  · intro a ha x hx
    have := idx_lt ha hx
    rw [gl _ _ _ (by simp only [List.length_append, h1, h2, h3]; omega), gl _ _ _ (by simp only [List.length_append, h1, h2]; omega),
      gr _ _ _ (by rw [h1]; omega), h1, show m * r + a * r + x - m * r = a * r + x by omega,
      flat_getD m r gO a x ha hx]
  · intro x hx
    rw [gl _ _ _ (by simp only [List.length_append, h1, h2, h3]; omega),
      gr _ _ _ (by simp only [List.length_append, h1, h2]; omega), List.length_append, h1, h2,
      show 2 * (m * r) + x - (m * r + m * r) = x by omega, getD_ofFn, dif_pos hx]

lemma getD_map_ofFn {k : ℕ} (g : Fin k → ℕ) (f : ℕ → Bool) (w : ℕ) (hw : w < k) :
    ((List.ofFn g).map f).getD w false = f (g ⟨w, hw⟩) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_ofFn, hw]

def insF (m r : ℕ) (Ze Oe : ℕ → Finset ℕ) (w : ℕ) : ℕ :=
  if w < m * r then (if w % r ∈ Ze (w / r) then r + 1 else r)
  else if w < 2 * (m * r) then (if (w - m * r) % r ∈ Oe ((w - m * r) / r) then r + 1 else r)
  else if w < 2 * (m * r) + r then w - 2 * (m * r)
  else if w = 2 * (m * r) + r then r else r + 1

lemma insF_lt (m r : ℕ) (Ze Oe : ℕ → Finset ℕ) (w : ℕ) : insF m r Ze Oe w < r + 2 := by
  unfold insF; split_ifs <;> omega

lemma restrict (m r : ℕ) (Ze Oe : ℕ → Finset ℕ) (hZ : ∀ a, Ze a ⊆ Finset.range r)
    (hO : ∀ a, Oe a ⊆ Finset.range r) (D : Circuit) (hfan : FanInTwo D)
    (hrb : ReadsBack (2 * m * r + r + 2) D) :
    ∃ D' : Circuit, FanInTwo D' ∧ ReadsBack (r + 2) D' ∧ D'.output < r + 2 + D'.size ∧
      notCount D' = notCount D ∧ (∀ w < 2 * m * r + r + 2 + D.size, r + 2 + w < r + 2 + D'.size) ∧
      ∀ bf : List Bool, bf.length = r + 2 → bf.getD r false = false → bf.getD (r + 1) false = true →
        ∃ inp, Gd (2 * m * r + r) inp ∧ (∀ a < m, zs r inp a = Ze a) ∧
          (∀ a < m, os m r inp a = Oe a) ∧
          xs m r inp = (Finset.range r).filter (fun x => bf.getD x false = true) ∧
          ∀ w < 2 * m * r + r + 2 + D.size,
            (D'.wires bf).getD (r + 2 + w) false = (D.wires inp).getD w false := by
  have hn' : 2 * m * r + r = 2 * (m * r) + r := by ring
  let ins : List ℕ := List.ofFn (fun w : Fin (2 * m * r + r + 2) => insF m r Ze Oe w.val)
  have h0 : (Builder.empty r).gates.length = 0 := rfl
  have hins : ∀ w ∈ ins, w < r + 2 + (Builder.empty r).gates.length := by
    intro w hw
    simp only [ins, List.mem_ofFn] at hw
    obtain ⟨y, rfl⟩ := hw
    have := insF_lt m r Ze Oe y.val
    omega
  obtain ⟨B', hE, hn, hm, hev⟩ := embed D _ hfan hrb (Builder.empty r) ins (List.length_ofFn) hins
  have hlen : B'.gates.length = 2 * m * r + r + 2 + D.size := by
    have e2 := Builder.gates_len_eq B'
    have e3 : notCount D ≤ D.size := by
      rw [notCount_eq_filter_isNotOp]; exact List.length_filter_le _ _
    have h0n : (Builder.empty r).nots = 0 := rfl
    have h0m : (Builder.empty r).monos = 0 := rfl
    omega
  refine ⟨B'.toCircuit 0, B'.toCircuit_fanInTwo 0, fun j hj i hi => B'.rb j hj i hi, ?_, ?_, ?_, ?_⟩
  · show 0 < r + 2 + B'.gates.length; omega
  · rw [← Builder.nots_eq_notCount, hn, show (Builder.empty r).nots = 0 from rfl, Nat.zero_add]
  · intro w hw; show r + 2 + w < r + 2 + B'.gates.length; omega
  · intro bf hbl hb0 hb1
    have hev0 : ∀ w < r + 2, (Builder.empty r).eval bf w = bf.getD w false :=
      fun w hw => (Builder.empty r).eval_inp bf hbl w hw
    have hget : ∀ w < 2 * m * r + r + 2, (ins.map ((Builder.empty r).eval bf)).getD w false =
        bf.getD (insF m r Ze Oe w) false := by
      intro w hw
      simp only [ins]
      rw [getD_map_ofFn _ _ w hw, hev0 _ (insF_lt m r Ze Oe w)]
    have hZx : ∀ a < m, ∀ x < r, (ins.map ((Builder.empty r).eval bf)).getD (a * r + x) false = true ↔
        x ∈ Ze a := by
      intro a ha x hx
      have hi := idx_lt ha hx
      rw [hget _ (by omega)]
      unfold insF
      rw [if_pos hi, (divmod_aux a x r hx).2, (divmod_aux a x r hx).1]
      split_ifs with h1
      · exact ⟨fun _ => h1, fun _ => hb1⟩
      · rw [hb0]; exact ⟨fun h => absurd h (by simp), fun h => absurd h h1⟩
    have hOx : ∀ a < m, ∀ x < r,
        (ins.map ((Builder.empty r).eval bf)).getD (m * r + a * r + x) false = true ↔ x ∈ Oe a := by
      intro a ha x hx
      have hi := idx_lt ha hx
      rw [hget _ (by omega)]
      unfold insF
      rw [if_neg (show ¬ (m * r + a * r + x < m * r) by omega),
        if_pos (show m * r + a * r + x < 2 * (m * r) by omega),
        show m * r + a * r + x - m * r = a * r + x by omega,
        (divmod_aux a x r hx).2, (divmod_aux a x r hx).1]
      split_ifs with h1
      · exact ⟨fun _ => h1, fun _ => hb1⟩
      · rw [hb0]; exact ⟨fun h => absurd h (by simp), fun h => absurd h h1⟩
    refine ⟨ins.map ((Builder.empty r).eval bf), ⟨by simp [ins], ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · rw [hget _ (by omega)]
      unfold insF
      rw [if_neg (show ¬ (2 * m * r + r < m * r) by omega),
        if_neg (show ¬ (2 * m * r + r < 2 * (m * r)) by omega),
        if_neg (show ¬ (2 * m * r + r < 2 * (m * r) + r) by omega),
        if_pos (show 2 * m * r + r = 2 * (m * r) + r by omega)]
      exact hb0
    · rw [hget _ (by omega)]
      unfold insF
      rw [if_neg (show ¬ (2 * m * r + r + 1 < m * r) by omega),
        if_neg (show ¬ (2 * m * r + r + 1 < 2 * (m * r)) by omega),
        if_neg (show ¬ (2 * m * r + r + 1 < 2 * (m * r) + r) by omega),
        if_neg (show ¬ (2 * m * r + r + 1 = 2 * (m * r) + r) by omega)]
      exact hb1
    · intro a ha
      ext x
      simp only [zs, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨hx, h⟩; exact (hZx a ha x hx).mp h
      · intro hx
        have hxr : x < r := Finset.mem_range.mp (hZ a hx)
        exact ⟨hxr, (hZx a ha x hxr).mpr hx⟩
    · intro a ha
      ext x
      simp only [os, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨hx, h⟩; exact (hOx a ha x hx).mp h
      · intro hx
        have hxr : x < r := Finset.mem_range.mp (hO a hx)
        exact ⟨hxr, (hOx a ha x hxr).mpr hx⟩
    · ext x
      simp only [xs, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨hx, h⟩
        rw [hget _ (by omega)] at h
        unfold insF at h
        rw [if_neg (show ¬ (2 * (m * r) + x < m * r) by omega),
          if_neg (show ¬ (2 * (m * r) + x < 2 * (m * r)) by omega),
          if_pos (show 2 * (m * r) + x < 2 * (m * r) + r by omega),
          show 2 * (m * r) + x - 2 * (m * r) = x by omega] at h
        exact ⟨hx, h⟩
      · rintro ⟨hx, h⟩
        refine ⟨hx, ?_⟩
        rw [hget _ (by omega)]
        unfold insF
        rw [if_neg (show ¬ (2 * (m * r) + x < m * r) by omega),
          if_neg (show ¬ (2 * (m * r) + x < 2 * (m * r)) by omega),
          if_pos (show 2 * (m * r) + x < 2 * (m * r) + r by omega),
          show 2 * (m * r) + x - 2 * (m * r) = x by omega]
        exact h
    · intro w hw
      have := hev bf hbl w hw
      rw [h0, Nat.add_zero] at this
      exact this

lemma bits_facts (r : ℕ) (Y : Finset ℕ) (f : Fin r → Bool) (hf : ∀ j, f j = true ↔ j.val ∈ Y) :
    (List.ofFn f ++ [false, true]).length = r + 2 ∧
    ∀ i, (List.ofFn f ++ [false, true]).getD i false = true ↔ (i < r ∧ i ∈ Y) ∨ i = r + 1 := by
  refine ⟨by simp, fun i => ?_⟩
  rw [getD_app2, List.length_ofFn]
  split_ifs with h1 h2
  · rw [getD_ofFn, dif_pos h1, hf]; simp only [Fin.val_mk]
    exact ⟨fun h => Or.inl ⟨h1, h⟩, fun h => h.elim (fun h => h.2) (fun h => by omega)⟩
  · exact ⟨fun _ => Or.inr h2, fun _ => rfl⟩
  · exact ⟨fun h => absurd h (by simp), fun h => h.elim (fun h => absurd h.1 h1) (fun h => absurd h h2)⟩

lemma NT_transfer (r m K : ℕ) (Ze Oe : ℕ → Finset ℕ) (inp : List Bool)
    (hz : ∀ a < m, zs r inp a = Ze a) (ho : ∀ a < m, os m r inp a = Oe a) :
    (∃ l, Tr m (fun a => PP m r inp a a) (PP m r inp) (K + 1) l) ↔ ¬ NTb r m K Ze Oe := by
  unfold NTb; rw [not_not]
  have hPPe : ∀ a < m, ∀ c < m, (PP m r inp a c ↔ Finset.range r \ Ze a ⊆ Oe c) := by
    intro a ha c hc; unfold PP; rw [hz a ha, ho c hc]
  constructor
  · rintro ⟨l, hl⟩
    exact ⟨l, hl.congr (fun a ha h => (hPPe a ha a ha).mp h) (fun a ha c hc h => (hPPe a ha c hc).mp h)⟩
  · rintro ⟨l, hl⟩
    exact ⟨l, hl.congr (fun a ha h => (hPPe a ha a ha).mpr h)
      (fun a ha c hc h => (hPPe a ha c hc).mpr h)⟩

lemma extF_sub {m r : ℕ} (Z : Fin m → Finset ℕ) (hZ : ∀ i, Z i ⊆ Finset.range r) (a : ℕ) :
    extF m Z a ⊆ Finset.range r := by
  unfold extF; split_ifs
  · exact hZ _
  · exact Finset.empty_subset _

end PEqualNP.Outside.L_lib_1430_aux

theorem PEqualNP.Outside.L_lib_1430 :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    let valid := fun (n : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) =>
      PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) D ∧ D.output < n+2+D.size
    let bits := fun (r : Nat) (Y : Finset Nat) => List.ofFn (fun j : Fin r => decide (j.val ∈ Y))
    let adj := fun (n : Nat) (E : Finset Nat) (u v : Nat) => u≠v ∧ min u v*n+max u v ∈ E
    let clq := fun (n k : Nat) (E : Finset Nat) => ∃ v : Fin k → Fin n,
      ∀ i j, i<j → adj n E (v i).val (v j).val
    let fit := fun {m : Nat} (r b : Nat) (A B : Fin m → Finset Nat) =>
      ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → Nat), valid r D ∧
        PEqualNP.NotBracket.notCount D ≤ b ∧ (∀ j, o j < r+2+D.size) ∧
        ∀ Y ⊆ Finset.range r, ∀ i, A i ⊆ Y → Y ⊆ B i →
          ∀ j, (D.wires (bits r Y ++ [false,true])).getD (o j) false = decide (i=j)
    let serve := fun (m r b : Nat) (sepOnly : Bool) (D : PEqualNP.CircuitLowerBounds.Circuit) (out : Fin m → Nat) =>
      let t := 2*m*r+r
      valid t D ∧ PEqualNP.NotBracket.notCount D ≤ b ∧ (∀ j, out j < t+2+D.size) ∧
        ∀ (Z O : Fin m → Finset Nat), (∀ i, Z i ⊆ Finset.range r ∧ O i ⊆ Finset.range r) →
          let A := fun i => Finset.range r \ Z i
          let sep := ∀ i j Y, A i ⊆ Y → Y ⊆ O i → A j ⊆ Y → Y ⊆ O j → i=j
          (sepOnly=true → sep) → ∀ X ⊆ Finset.range r,
            let I := (List.ofFn (fun i => bits r (Z i))).flatten ++
              (List.ofFn (fun i => bits r (O i))).flatten ++ bits r X ++ [false,true]
            (D.eval I = false ↔ fit r b A O) ∧ (fit r b A O →
              ∀ i, A i ⊆ X → X ⊆ O i → ∀ j, (D.wires I).getD (out j) false = decide (i=j))
    let solves := fun (n k : Nat) (S : PEqualNP.CircuitLowerBounds.Circuit) =>
      valid (n*n) S ∧ PEqualNP.NotBracket.notCount S=0 ∧ ∀ E ⊆ Finset.range (n*n),
        S.eval (bits (n*n) E ++ [false,true]) = decide (clq n k E)
    ∀ (r m b : Nat),
      let K := min (2^b) (r+1)
      let N := (K+1)*(m+1)
      ∀ S : PEqualNP.CircuitLowerBounds.Circuit, solves N (K+1) S →
        ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (out : Fin m → Nat), serve m r b false D out ∧
          D.size-PEqualNP.NotBracket.notCount D ≤
            32*(r+1)*(m+1)^2+32*(K+1)*(m+1)*(S.size+N*N+1) := by
  intro valid bits adj clq fit serve solves r m b K N S hS
  have hKdef : K = min (2 ^ b) (r + 1) := rfl
  have hNdef : N = (K + 1) * (m + 1) := rfl
  clear_value K N
  subst hNdef
  have hK1 : 1 ≤ K := by rw [hKdef]; have := @Nat.one_le_two_pow b; omega
  have hKb : K ≤ 2 ^ b := by rw [hKdef]; omega
  have hKor : 2 ^ b ≤ K ∨ r + 1 ≤ K := by rw [hKdef]; omega
  obtain ⟨⟨hSfan, hSrb, hSout⟩, hSnc, hSsem⟩ := hS
  obtain ⟨B, gout, ow, hBn, hBm, hgout, how, hBsem⟩ :=
    L_lib_1430_aux.construct r m b K hK1 hKb S hSfan hSrb hSout hSnc (fun ev => by
      have h := hSsem (L_lib_1430_aux.evSet ((K + 1) * (m + 1) * ((K + 1) * (m + 1))) ev)
        (fun e he => Finset.mem_range.mpr ((L_lib_1430_aux.mem_evSet _ _ e).mp he).1)
      have hb : bits ((K + 1) * (m + 1) * ((K + 1) * (m + 1)))
          (L_lib_1430_aux.evSet ((K + 1) * (m + 1) * ((K + 1) * (m + 1))) ev) =
          List.ofFn (fun e : Fin ((K + 1) * (m + 1) * ((K + 1) * (m + 1))) => ev e.val) := by
        show List.ofFn _ = List.ofFn _
        congr 1; funext e
        apply Bool.eq_iff_iff.mpr
        rw [L_lib_1430_aux.dtrue, L_lib_1430_aux.mem_evSet]
        exact ⟨fun h => h.2, fun h => ⟨e.isLt, h⟩⟩
      rw [← hb, h, L_lib_1430_aux.dtrue]
      exact Iff.rfl)
  refine ⟨B.toCircuit gout, fun j => ow j.val, ?_, ?_⟩
  swap
  · show B.gates.length - PEqualNP.NotBracket.notCount (B.toCircuit gout) ≤ _
    rw [← L_lib_1430_aux.Builder.nots_eq_notCount, L_lib_1430_aux.Builder.gates_len_eq]
    omega
  dsimp -zeta only [serve, valid]
  refine ⟨⟨L_lib_1430_aux.Builder.toCircuit_fanInTwo B gout, fun j hj i hi => B.rb j hj i hi, hgout⟩,
    by rw [← L_lib_1430_aux.Builder.nots_eq_notCount]; exact hBn, fun j => how j.val j.isLt, ?_⟩
  intro Z O hZO A sep _ X hX I
  have hZr : ∀ i, Z i ⊆ Finset.range r := fun i => (hZO i).1
  have hOr : ∀ i, O i ⊆ Finset.range r := fun i => (hZO i).2
  have hZe := L_lib_1430_aux.extF_sub Z hZr
  have hOe := L_lib_1430_aux.extF_sub O hOr
  -- the book is fit exactly when no long trace exists
  have hfit_NT : fit r b A O →
      L_lib_1430_aux.NTb r m K (L_lib_1430_aux.extF m Z) (L_lib_1430_aux.extF m O) := by
    intro hf
    dsimp only [fit, valid] at hf
    obtain ⟨D', o, ⟨hfan', hrb', _⟩, hnc', ho', hfit'⟩ := hf
    have hbf : ∀ Y, (bits r Y ++ [false, true]).length = r + 2 ∧ ∀ i,
        (bits r Y ++ [false, true]).getD i false = true ↔ (i < r ∧ i ∈ Y) ∨ i = r + 1 :=
      fun Y => L_lib_1430_aux.bits_facts r Y _ (fun j => L_lib_1430_aux.dtrue)
    refine L_lib_1430_aux.fit_imp_NT r m b K hKor Z O (fun Y => bits r Y ++ [false, true])
      (fun Y => (hbf Y).1) (fun Y => (hbf Y).2) D' o hfan' hrb' hnc' ho' ?_
    intro Y hY i h1 h2 j
    beta_reduce
    rw [hfit' Y hY i (by simp only [A]; rw [L_lib_1430_aux.sdiff_inst]; exact h1) h2 j]
    exact L_lib_1430_aux.dtrue
  have hNT_fit : L_lib_1430_aux.NTb r m K (L_lib_1430_aux.extF m Z) (L_lib_1430_aux.extF m O) →
      fit r b A O := by
    intro hNT
    obtain ⟨D', hfan', hrb', hout', hnc', hlt', hrest⟩ := L_lib_1430_aux.restrict m r
      (L_lib_1430_aux.extF m Z) (L_lib_1430_aux.extF m O) hZe hOe (B.toCircuit gout)
      (L_lib_1430_aux.Builder.toCircuit_fanInTwo B gout) (fun j hj i hi => B.rb j hj i hi)
    dsimp only [fit, valid]
    refine ⟨D', fun j => r + 2 + ow j.val, ⟨hfan', hrb', hout'⟩,
      by rw [hnc', ← L_lib_1430_aux.Builder.nots_eq_notCount]; exact hBn,
      fun j => hlt' _ (how j.val j.isLt), ?_⟩
    intro Y hY i h1 h2 j
    simp only [A] at h1
    rw [L_lib_1430_aux.sdiff_inst] at h1
    have hbf : (bits r Y ++ [false, true]).length = r + 2 ∧ ∀ i, (bits r Y ++ [false, true]).getD i false = true ↔
        (i < r ∧ i ∈ Y) ∨ i = r + 1 :=
      L_lib_1430_aux.bits_facts r Y _ (fun j => L_lib_1430_aux.dtrue)
    obtain ⟨inp, hgd, hzs', hos', hxs', hw⟩ := hrest (bits r Y ++ [false, true]) hbf.1
      (by
        cases h : (bits r Y ++ [false, true]).getD r false
        · rfl
        · rcases (hbf.2 r).mp h with ⟨h', _⟩ | h' <;> omega)
      ((hbf.2 (r + 1)).mpr (Or.inr rfl))
    have hxY : L_lib_1430_aux.xs m r inp = Y := by
      rw [hxs']
      ext x
      rw [Finset.mem_filter, Finset.mem_range, hbf.2]
      constructor
      · rintro ⟨_, ⟨_, h⟩ | h⟩
        · exact h
        · omega
      · intro h
        have := Finset.mem_range.mp (hY h)
        exact ⟨this, Or.inl ⟨this, h⟩⟩
    have hNTinp : ¬ ∃ l, L_lib_1430_aux.Tr m (fun a => L_lib_1430_aux.PP m r inp a a)
        (L_lib_1430_aux.PP m r inp) (K + 1) l :=
      fun h => ((L_lib_1430_aux.NT_transfer r m K _ _ inp hzs' hos').mp h) hNT
    have hsem := (hBsem inp hgd).2 hNTinp i.val i.isLt
      (by rw [hzs' i.val i.isLt, hxY, L_lib_1430_aux.extF_fin]; exact h1)
      (by rw [hxY, hos' i.val i.isLt, L_lib_1430_aux.extF_fin]; exact h2) j.val j.isLt
    beta_reduce
    rw [hw (ow j.val) (how j.val j.isLt)]
    change B.eval inp (ow j.val) = _
    apply Bool.eq_iff_iff.mpr
    rw [hsem, L_lib_1430_aux.dtrue]
    exact ⟨fun h => (Fin.ext h).symm, fun h => by rw [h]⟩
  -- the input of the book
  obtain ⟨hIgd, hIZ, hIO, hIX⟩ := L_lib_1430_aux.I_facts m r _ _ _ I rfl
  have hzs : ∀ a < m, L_lib_1430_aux.zs r I a = L_lib_1430_aux.extF m Z a := by
    intro a ha
    ext x
    simp only [L_lib_1430_aux.zs, Finset.mem_filter, Finset.mem_range, L_lib_1430_aux.extF, dif_pos ha]
    constructor
    · rintro ⟨hx, h⟩; rw [hIZ a ha x hx] at h; exact L_lib_1430_aux.dtrue.mp h
    · intro hx
      have hxr : x < r := Finset.mem_range.mp (hZr _ hx)
      exact ⟨hxr, by rw [hIZ a ha x hxr]; exact L_lib_1430_aux.dtrue.mpr hx⟩
  have hos : ∀ a < m, L_lib_1430_aux.os m r I a = L_lib_1430_aux.extF m O a := by
    intro a ha
    ext x
    simp only [L_lib_1430_aux.os, Finset.mem_filter, Finset.mem_range, L_lib_1430_aux.extF, dif_pos ha]
    constructor
    · rintro ⟨hx, h⟩; rw [hIO a ha x hx] at h; exact L_lib_1430_aux.dtrue.mp h
    · intro hx
      have hxr : x < r := Finset.mem_range.mp (hOr _ hx)
      exact ⟨hxr, by rw [hIO a ha x hxr]; exact L_lib_1430_aux.dtrue.mpr hx⟩
  have hxs : L_lib_1430_aux.xs m r I = X := by
    ext x
    simp only [L_lib_1430_aux.xs, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hx, h⟩; rw [hIX x hx] at h; exact L_lib_1430_aux.dtrue.mp h
    · intro hx
      have hxr : x < r := Finset.mem_range.mp (hX hx)
      exact ⟨hxr, by rw [hIX x hxr]; exact L_lib_1430_aux.dtrue.mpr hx⟩
  have hsemI := hBsem _ hIgd
  have hNTiff := L_lib_1430_aux.NT_transfer r m K _ _ _ hzs hos
  refine ⟨?_, ?_⟩
  · change B.eval I gout = false ↔ _
    constructor
    · intro h
      apply hNT_fit
      unfold L_lib_1430_aux.NTb
      intro hl
      have := hsemI.1.mpr (hNTiff.mpr (fun hn => hn hl))
      rw [h] at this; exact absurd this (by simp)
    · intro hf
      have hNT := hfit_NT hf
      cases hv : B.eval I gout
      · rfl
      · exact absurd (hNTiff.mp (hsemI.1.mp hv)) (not_not.mpr hNT)
  · intro hf i h1 h2 j
    simp only [A] at h1
    rw [L_lib_1430_aux.sdiff_inst] at h1
    have hNT := hfit_NT hf
    have hNTI := fun h => (hNTiff.mp h) hNT
    have hsem := hsemI.2 hNTI i.val i.isLt
      (by rw [hzs i.val i.isLt, hxs, L_lib_1430_aux.extF_fin]; exact h1)
      (by rw [hxs, hos i.val i.isLt, L_lib_1430_aux.extF_fin]; exact h2) j.val j.isLt
    change B.eval I (ow j.val) = _
    apply Bool.eq_iff_iff.mpr
    rw [hsem, L_lib_1430_aux.dtrue]
    exact ⟨fun h => (Fin.ext h).symm, fun h => by rw [h]⟩
