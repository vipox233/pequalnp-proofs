import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1365_aux

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
      | nil => simp [hins, GateOp.eval] at hne
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

private lemma Builder.nots_eq_notCount {n : ℕ} (B : Builder n) (out : ℕ) :
    B.nots = notCount (B.toCircuit out) := (notCount_eq_filter_isNotOp (B.toCircuit out)).symm

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
    ∀ inp, inp.length = n + 2 →
      (pushAnd B a b ha hb).1.eval inp (pushAnd B a b ha hb).2 = (B.eval inp a && B.eval inp b) := by
  dsimp only [pushAnd]
  refine ⟨Extends.push B _ _ _, by simp [Builder.push], by rw [Builder.push_nots]; rfl, fun inp hinp => ?_⟩
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
    ∀ inp, inp.length = n + 2 →
      (pushOr B a b ha hb).1.eval inp (pushOr B a b ha hb).2 = (B.eval inp a || B.eval inp b) := by
  dsimp only [pushOr]
  refine ⟨Extends.push B _ _ _, by simp [Builder.push], by rw [Builder.push_nots]; rfl, fun inp hinp => ?_⟩
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
    ∀ inp, inp.length = n + 2 →
      (pushNot B a ha).1.eval inp (pushNot B a ha).2 = !(B.eval inp a) := by
  dsimp only [pushNot]
  refine ⟨Extends.push B _ _ _, by simp [Builder.push], by rw [Builder.push_nots]; rfl, fun inp hinp => ?_⟩
  rw [Builder.eval_push_new B _ _ _ inp hinp]; rfl

private lemma exists_or_list {n : ℕ} (ws : List ℕ) :
    ∀ (B : Builder n), (∀ w ∈ ws, w < n + 2 + B.gates.length) →
      ∃ (B' : Builder n) (out : ℕ),
        Extends B B' ∧ out < n + 2 + B'.gates.length ∧
        B'.nots = B.nots ∧
        ∀ inp, inp.length = n + 2 → inp.getD n false = false →
          B'.eval inp out = ws.any (B.eval inp) := by
  induction ws with
  | nil =>
    intro B _
    refine ⟨B, n, Extends.refl B, by omega, rfl, ?_⟩
    intro inp hinp hn0
    rw [B.eval_inp inp hinp n (by omega), hn0]; rfl
  | cons w rest ih =>
    intro B hws
    cases rest with
    | nil =>
      refine ⟨B, w, Extends.refl B, hws w (List.mem_cons_self ..), rfl, ?_⟩
      intro _ _ _; simp
    | cons w2 rest2 =>
      rcases ih B (fun u hu => hws u (List.mem_cons_of_mem w hu)) with
        ⟨B1, out1, hE1, hlt1, hn1, hev1⟩
      have hw1 : w < n + 2 + B1.gates.length := by
        have := hws w (List.mem_cons_self ..); have := hE1.1; omega
      set rO := pushOr B1 w out1 hw1 hlt1
      have hsO := pushOr_spec B1 w out1 hw1 hlt1
      refine ⟨rO.1, rO.2, hE1.trans hsO.1, hsO.2.1, by rw [hsO.2.2.1, hn1], ?_⟩
      intro inp hinp hn0
      rw [hsO.2.2.2 inp hinp, hE1.2 inp hinp w (hws w (List.mem_cons_self ..)),
        hev1 inp hinp hn0]
      simp [List.any_cons]

private lemma exists_and_list {n : ℕ} (ws : List ℕ) :
    ∀ (B : Builder n), (∀ w ∈ ws, w < n + 2 + B.gates.length) →
      ∃ (B' : Builder n) (out : ℕ),
        Extends B B' ∧ out < n + 2 + B'.gates.length ∧
        B'.nots = B.nots ∧
        ∀ inp, inp.length = n + 2 → inp.getD (n + 1) false = true →
          B'.eval inp out = ws.all (B.eval inp) := by
  induction ws with
  | nil =>
    intro B _
    refine ⟨B, n + 1, Extends.refl B, by omega, rfl, ?_⟩
    intro inp hinp hn1
    rw [B.eval_inp inp hinp (n + 1) (by omega), hn1]; rfl
  | cons w rest ih =>
    intro B hws
    cases rest with
    | nil =>
      refine ⟨B, w, Extends.refl B, hws w (List.mem_cons_self ..), rfl, ?_⟩
      intro _ _ _; simp
    | cons w2 rest2 =>
      rcases ih B (fun u hu => hws u (List.mem_cons_of_mem w hu)) with
        ⟨B1, out1, hE1, hlt1, hn1, hev1⟩
      have hw1 : w < n + 2 + B1.gates.length := by
        have := hws w (List.mem_cons_self ..); have := hE1.1; omega
      set rA := pushAnd B1 w out1 hw1 hlt1
      have hsA := pushAnd_spec B1 w out1 hw1 hlt1
      refine ⟨rA.1, rA.2, hE1.trans hsA.1, hsA.2.1, by rw [hsA.2.2.1, hn1], ?_⟩
      intro inp hinp hn1
      rw [hsA.2.2.2 inp hinp, hE1.2 inp hinp w (hws w (List.mem_cons_self ..)),
        hev1 inp hinp hn1]
      simp [List.all_cons]

-- =========================================================================
-- Part 2: Binary head-bit helpers and state order
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

private def wordLe {a : ℕ} (w1 w2 : Fin a → Bool) : Prop :=
  ∀ i : Fin a, w1 i = true → w2 i = true

private def stateLe {a : ℕ} (s1 s2 : ℕ × (Fin a → Bool)) : Prop :=
  s1.1 < s2.1 ∨ (s1.1 = s2.1 ∧ wordLe s1.2 s2.2)

private lemma stateLe_refl {a : ℕ} (s : ℕ × (Fin a → Bool)) : stateLe s s :=
  Or.inr ⟨rfl, fun _ h => h⟩

private lemma stateLe_trans {a : ℕ} {s1 s2 s3 : ℕ × (Fin a → Bool)}
    (h12 : stateLe s1 s2) (h23 : stateLe s2 s3) : stateLe s1 s3 := by
  rcases h12 with h1 | ⟨h1, hw1⟩ <;> rcases h23 with h2 | ⟨h2, hw2⟩
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inr ⟨by omega, fun i hi => hw2 i (hw1 i hi)⟩

private def rawStd (n : ℕ) (x : Finset (Fin n)) : List Bool :=
  List.ofFn (fun i : Fin n => @decide (i ∈ x) (@Finset.decidableMem (Fin n) (instDecidableEqFin n) i x)) ++ [false, true]

private lemma rawStd_spec (n : ℕ) (x : Finset (Fin n)) :
    (rawStd n x).length = n + 2 ∧ (rawStd n x).getD n false = false ∧
    (rawStd n x).getD (n + 1) false = true ∧
    ∀ j : Fin n, (rawStd n x).getD j.val false = decide (j ∈ x) := by
  refine ⟨by simp [rawStd], by simp [rawStd, List.getD_eq_getElem?_getD],
    by simp [rawStd, List.getD_eq_getElem?_getD], fun j => ?_⟩
  simp only [rawStd, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by simp : j.val < (List.ofFn (fun i : Fin n => @decide (i ∈ x) (@Finset.decidableMem (Fin n) (instDecidableEqFin n) i x))).length),
    List.getElem?_ofFn, dite_eq_left j.isLt, Option.getD_some]

private lemma circuit_to_assign {n a b : ℕ} (S : Finset (Finset (Fin n)))
    (C : Circuit) (tap : Fin a → ℕ)
    (hfan : FanInTwo C) (hrb : ReadsBack (n + 2) C)
    (hnot : notCount C ≤ b) (htap : ∀ i, tap i < n + 2 + C.size) :
    ∃ σ : Finset (Fin n) → ℕ × (Fin a → Bool),
      (∀ x ∈ S, (σ x).1 < 2 ^ b) ∧
      (∀ x ∈ S, ∀ y ∈ S, x ⊆ y → stateLe (σ x) (σ y)) ∧
      (∀ x ∈ S, ∀ i : Fin a, (σ x).2 i = (C.wires (rawStd n x)).getD (tap i) false) := by
  refine ⟨fun x => (2 ^ notCount C - 1 - notVal n C (rawStd n x),
      fun i => (C.wires (rawStd n x)).getD (tap i) false), ?_, ?_, fun _ _ _ => rfl⟩
  · intro x _
    dsimp only
    have hlt := notVal_lt n C (rawStd n x)
    have hpow : 2 ^ notCount C ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) hnot
    have hpos : 1 ≤ 2 ^ notCount C := Nat.one_le_pow _ _ (by omega)
    omega
  · intro x _ y _ hxy
    have hle : ∀ u < n + 2, (rawStd n x).getD u false = true → (rawStd n y).getD u false = true := by
      intro u hu hv
      by_cases hun : u < n
      · have hx := (rawStd_spec n x).2.2.2 ⟨u, hun⟩
        have hy := (rawStd_spec n y).2.2.2 ⟨u, hun⟩
        rw [hx, decide_eq_true_eq] at hv
        rw [hy, decide_eq_true_eq]
        exact hxy hv
      · have hu1 : u = n ∨ u = n + 1 := by omega
        rcases hu1 with hu_eq | hu_eq
        · rw [hu_eq, (rawStd_spec n x).2.1] at hv; cases hv
        · rw [hu_eq]; exact (rawStd_spec n y).2.2.1
    have hanti := notVal_anti C hfan hrb (rawStd n x) (rawStd n y)
      (rawStd_spec n x).1 (rawStd_spec n y).1 hle
    have hlt_x := notVal_lt n C (rawStd n x)
    have hlt_y := notVal_lt n C (rawStd n y)
    rcases hanti with hlt | ⟨heq, hmono⟩
    · exact Or.inl (by dsimp only; omega)
    · exact Or.inr ⟨by dsimp only; omega, fun i hi => hmono (tap i) (htap i) hi⟩

private lemma assign_to_circuit {n a b : ℕ} (S : Finset (Finset (Fin n)))
    (σ : Finset (Fin n) → ℕ × (Fin a → Bool))
    (hlt_pow : ∀ x ∈ S, (σ x).1 < 2 ^ b)
    (hmono : ∀ x ∈ S, ∀ y ∈ S, x ⊆ y → stateLe (σ x) (σ y)) :
    ∃ (C : Circuit) (tap : Fin a → ℕ),
      FanInTwo C ∧ ReadsBack (n + 2) C ∧ C.output < n + 2 + C.size ∧ notCount C ≤ b ∧
      (∀ i, tap i < n + 2 + C.size) ∧
      (∀ x ∈ S, ∀ i : Fin a, (C.wires (rawStd n x)).getD (tap i) false = (σ x).2 i) := by
  let m := S.card
  let e : Fin m ≃ {x : Finset (Fin n) // x ∈ S} := (Fintype.equivFinOfCardEq (by simp [m])).symm
  let x : Fin m → Finset (Fin n) := fun i => (e i).val
  let g : Fin m → ℕ × (Fin a → Bool) := fun i => σ (x i)
  have hgx_lt : ∀ i : Fin m, (g i).1 < 2 ^ b := fun i => hlt_pow (x i) (e i).property
  have hmono_lvl : ∀ i k : Fin m, x i ⊆ x k → (g i).1 ≤ (g k).1 := by
    intro i k hsub
    dsimp only [g]
    rcases hmono (x i) (e i).property (x k) (e k).property hsub with hlt | ⟨heq, _⟩ <;> omega
  have hmono_eq : ∀ i k : Fin m, x i ⊆ x k → (g i).1 = (g k).1 → wordLe (g i).2 (g k).2 := by
    intro i k hsub heq
    dsimp only [g] at heq ⊢
    rcases hmono (x i) (e i).property (x k) (e k).property hsub with hlt | ⟨_, hw⟩
    · omega
    · exact hw
  -- Stage 0: mask indicators ind0 i computing decide (x i ⊆ x k)
  have hstage0 : ∀ (p : ℕ) (hp : p ≤ m),
      ∃ (Bp : Builder n) (ind0 : Fin p → ℕ),
        (∀ i, ind0 i < n + 2 + Bp.gates.length) ∧
        Bp.nots = 0 ∧
        ∀ (k : Fin m) (i : Fin p),
          Bp.eval (rawStd n (x k)) (ind0 i) = decide (x ⟨i.val, by have := i.isLt; omega⟩ ⊆ x k) := by
    intro p
    induction p with
    | zero =>
      intro _
      exact ⟨Builder.empty n, fun i => Fin.elim0 i, fun i => Fin.elim0 i, rfl, fun _ i => Fin.elim0 i⟩
    | succ p ih =>
      intro hp
      rcases ih (by omega) with ⟨Bp, ind0, hlt0, hn0, hev0⟩
      let ip : Fin m := ⟨p, by omega⟩
      let ws : List ℕ := ((List.finRange n).filter (fun j => decide (j ∈ x ip))).map Fin.val
      have hws_lt : ∀ w ∈ ws, w < n + 2 + Bp.gates.length := by
        intro w hw
        rcases List.mem_map.mp hw with ⟨j, _, rfl⟩
        omega
      rcases exists_and_list ws Bp hws_lt with ⟨Bp', outp, hEp, hltp, hnp, hevp⟩
      let ind' : Fin (p + 1) → ℕ := fun i => if hi : i.val < p then ind0 ⟨i.val, hi⟩ else outp
      refine ⟨Bp', ind', ?_, by rw [hnp, hn0], ?_⟩
      · intro i; dsimp only [ind']; split_ifs with hi
        · have := hlt0 ⟨i.val, hi⟩; have := hEp.1; omega
        · exact hltp
      · intro k i
        have hk := rawStd_spec n (x k)
        dsimp only [ind']; split_ifs with hi
        · rw [hEp.2 (rawStd n (x k)) hk.1 _ (hlt0 ⟨i.val, hi⟩), hev0 k ⟨i.val, hi⟩]
        · have hip : (⟨i.val, by omega⟩ : Fin m) = ip := by ext; dsimp [ip]; omega
          rw [hip, hevp (rawStd n (x k)) hk.1 hk.2.2.1, Bool.eq_iff_iff, decide_eq_true_eq]
          simp only [ws, List.all_eq_true, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
            decide_eq_true_eq]
          constructor
          · intro hall j hj
            have hval := hall j.val ⟨j, hj, rfl⟩
            rw [Bp.eval_inp (rawStd n (x k)) hk.1 j.val (by omega), hk.2.2.2 j, decide_eq_true_eq] at hval
            exact hval
          · rintro hsub w ⟨j, hj, rfl⟩
            rw [Bp.eval_inp (rawStd n (x k)) hk.1 j.val (by omega), hk.2.2.2 j, decide_eq_true_eq]
            exact hsub hj
  rcases hstage0 m le_rfl with ⟨B0, ind0, hlt0, hn0, hev0⟩
  -- Stages d = 0 .. b: refine indicators with 1 NOT per stage
  have hstages : ∀ d ≤ b,
      ∃ (Bd : Builder n) (ind : Fin m → ℕ),
        (∀ i, ind i < n + 2 + Bd.gates.length) ∧
        Bd.nots = d ∧
        ∀ (k i : Fin m),
          Bd.eval (rawStd n (x k)) (ind i) =
            decide (x i ⊆ x k ∧ (g i).1 / 2 ^ (b - d) = (g k).1 / 2 ^ (b - d)) := by
    intro d
    induction d with
    | zero =>
      intro _
      refine ⟨B0, ind0, hlt0, hn0, fun k i => ?_⟩
      rw [hev0 k i]
      have h1 : (g i).1 / 2 ^ b = 0 := Nat.div_eq_of_lt (hgx_lt i)
      have h2 : (g k).1 / 2 ^ b = 0 := Nat.div_eq_of_lt (hgx_lt k)
      simp [h1, h2]
    | succ d ih =>
      intro hd
      rcases ih (by omega) with ⟨Bd, ind, hltd, hnd, hevd⟩
      set s := b - 1 - d
      have hs1 : b - d = s + 1 := by omega
      have hs0 : b - (d + 1) = s := by omega
      let posList : List ℕ := ((List.finRange m).filter (fun i => bitAt (g i).1 s)).map ind
      have hpos_lt : ∀ w ∈ posList, w < n + 2 + Bd.gates.length := by
        intro w hw
        rcases List.mem_map.mp hw with ⟨i, _, rfl⟩
        exact hltd i
      rcases exists_or_list posList Bd hpos_lt with ⟨Bor, inW, hEor, hltIn, hnOr, hevOr⟩
      have hinW_val : ∀ k : Fin m, Bor.eval (rawStd n (x k)) inW = bitAt (g k).1 s := by
        intro k
        have hk := rawStd_spec n (x k)
        rw [hevOr (rawStd n (x k)) hk.1 hk.2.1, Bool.eq_iff_iff]
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
      have hnot_val : ∀ k : Fin m, rNot.1.eval (rawStd n (x k)) rNot.2 = !(bitAt (g k).1 s) := by
        intro k
        rw [hsNot.2.2.2 (rawStd n (x k)) (rawStd_spec n (x k)).1, hinW_val k]
      have hupd : ∀ (p : ℕ) (hp : p ≤ m),
          ∃ (Bp : Builder n) (ind' : Fin p → ℕ),
            Extends rNot.1 Bp ∧ (∀ i, ind' i < n + 2 + Bp.gates.length) ∧
            Bp.nots = rNot.1.nots ∧
            ∀ (k : Fin m) (i : Fin p),
              let im : Fin m := ⟨i.val, by have := i.isLt; omega⟩
              Bp.eval (rawStd n (x k)) (ind' i) =
                decide (x im ⊆ x k ∧ (g im).1 / 2 ^ s = (g k).1 / 2 ^ s) := by
        intro p
        induction p with
        | zero =>
          intro _
          exact ⟨rNot.1, fun i => Fin.elim0 i, Extends.refl _, fun i => Fin.elim0 i, rfl,
            fun _ i => Fin.elim0 i⟩
        | succ p ihp =>
          intro hp
          rcases ihp (by omega) with ⟨Bp, ind', hEp, hltp, hnp, hevp⟩
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
            refine ⟨rA.1, ind'', hEp.trans hEA, ?_, by rw [hsA.2.2.1, hnp], ?_⟩
            · intro i; dsimp only [ind'']; split_ifs with hi
              · have := hltp ⟨i.val, hi⟩; have := hEA.1; omega
              · exact hsA.2.1
            · intro k i
              have hk := rawStd_spec n (x k)
              dsimp only [ind'']; split_ifs with hi
              · rw [hsA.1.2 (rawStd n (x k)) hk.1 _ (hltp ⟨i.val, hi⟩)]
                exact hevp k ⟨i.val, hi⟩
              · have hip : (⟨i.val, by omega⟩ : Fin m) = ip := by ext; dsimp [ip]; omega
                rw [hip, hsA.2.2.2 (rawStd n (x k)) hk.1, (hEnot.trans hEp).2 (rawStd n (x k)) hk.1 _ (hltd ip),
                  hEp.2 (rawStd n (x k)) hk.1 _ hsNot.2.1, hevd k ip, hnot_val k, hs1, Bool.eq_iff_iff]
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
            refine ⟨Bp, ind'', hEp, ?_, hnp, ?_⟩
            · intro i; dsimp only [ind'']; split_ifs with hi
              · exact hltp ⟨i.val, hi⟩
              · exact hind_lt
            · intro k i
              have hk := rawStd_spec n (x k)
              dsimp only [ind'']; split_ifs with hi
              · exact hevp k ⟨i.val, hi⟩
              · have hip : (⟨i.val, by omega⟩ : Fin m) = ip := by ext; dsimp [ip]; omega
                rw [hip, (hEnot.trans hEp).2 (rawStd n (x k)) hk.1 _ (hltd ip), hevd k ip, hs1, Bool.eq_iff_iff]
                simp only [decide_eq_true_eq]
                constructor
                · rintro ⟨hsub, hpref⟩
                  exact ⟨hsub, prefix_step_eq (hmono_lvl ip k hsub) hpref (fun h => by rw [hbit1] at h; cases h)⟩
                · rintro ⟨hsub, hdiv⟩
                  refine ⟨hsub, ?_⟩
                  rw [pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hdiv]
      rcases hupd m le_rfl with ⟨Bnext, indNext, _, hltNext, hnNext, hevNext⟩
      refine ⟨Bnext, indNext, hltNext, ?_, fun k i => ?_⟩
      · rw [hnNext, hsNot.2.2.1, hnOr, hnd]
      · rw [hs0]; exact hevNext k i
  rcases hstages b le_rfl with ⟨Br, indR, hltr, hnr, hevr⟩
  -- Final stage: for each q : Fin a, tap q = OR of indR i for i with (g i).2 q = true
  have htaps : ∀ (p : ℕ) (hp : p ≤ a),
      ∃ (Bp : Builder n) (tap : Fin p → ℕ),
        Extends Br Bp ∧ (∀ q, tap q < n + 2 + Bp.gates.length) ∧
        Bp.nots = Br.nots ∧
        ∀ (k : Fin m) (q : Fin p),
          Bp.eval (rawStd n (x k)) (tap q) = (g k).2 ⟨q.val, by have := q.isLt; omega⟩ := by
    intro p
    induction p with
    | zero =>
      intro _
      exact ⟨Br, fun q => Fin.elim0 q, Extends.refl Br, fun q => Fin.elim0 q, rfl, fun _ q => Fin.elim0 q⟩
    | succ p ih =>
      intro hp
      rcases ih (by omega) with ⟨Bp, tap, hEp, hltp, hnp, hevp⟩
      let qp : Fin a := ⟨p, by omega⟩
      let ws : List ℕ := ((List.finRange m).filter (fun i => (g i).2 qp)).map indR
      have hws_lt : ∀ w ∈ ws, w < n + 2 + Bp.gates.length := by
        intro w hw
        rcases List.mem_map.mp hw with ⟨i, _, rfl⟩
        have := hltr i; have := hEp.1; omega
      rcases exists_or_list ws Bp hws_lt with ⟨Bp', outp, hE1, hlt1, hn1, hev1⟩
      let tap' : Fin (p + 1) → ℕ := fun q => if hq : q.val < p then tap ⟨q.val, hq⟩ else outp
      refine ⟨Bp', tap', hEp.trans hE1, ?_, by rw [hn1, hnp], ?_⟩
      · intro q; dsimp only [tap']; split_ifs with hq
        · have := hltp ⟨q.val, hq⟩; have := hE1.1; omega
        · exact hlt1
      · intro k q
        have hk := rawStd_spec n (x k)
        dsimp only [tap']; split_ifs with hq
        · rw [hE1.2 (rawStd n (x k)) hk.1 _ (hltp ⟨q.val, hq⟩)]
          exact hevp k ⟨q.val, hq⟩
        · have hqp : (⟨q.val, by omega⟩ : Fin a) = qp := by ext; dsimp [qp]; omega
          rw [hqp, hev1 (rawStd n (x k)) hk.1 hk.2.1, Bool.eq_iff_iff]
          simp only [ws, List.any_eq_true, List.mem_map, List.mem_filter, List.mem_finRange, true_and]
          constructor
          · rintro ⟨w, ⟨i, hgi, rfl⟩, hev⟩
            rw [hEp.2 (rawStd n (x k)) hk.1 _ (hltr i), hevr k i, Nat.sub_self, pow_zero,
              Nat.div_one, Nat.div_one, decide_eq_true_eq] at hev
            exact hmono_eq i k hev.1 hev.2 qp hgi
          · intro hgk
            refine ⟨indR k, ⟨k, hgk, rfl⟩, ?_⟩
            rw [hEp.2 (rawStd n (x k)) hk.1 _ (hltr k), hevr k k, decide_eq_true_eq]
            exact ⟨Finset.Subset.refl _, rfl⟩
  rcases htaps a le_rfl with ⟨Bfin, tap, _, hltFin, hnFin, hevFin⟩
  refine ⟨Bfin.toCircuit 0, tap, Bfin.toCircuit_fanInTwo 0, Bfin.rb,
    by dsimp [Builder.toCircuit]; omega, by rw [← Bfin.nots_eq_notCount 0, hnFin, hnr], hltFin, ?_⟩
  intro u hu i
  let k : Fin m := e.symm ⟨u, hu⟩
  have hxk : x k = u := by dsimp [x, k]; simp
  have h1 := hevFin k i
  rw [hxk] at h1
  simpa [Builder.eval, Builder.toCircuit, g, hxk] using h1

-- =========================================================================
-- Part 3: Combinatorial bound arithmetic
-- =========================================================================

private def innerBound (g : ℕ) : ℕ → ℕ
  | 0 => 1 + g
  | k + 1 => 1 + (k + 1) * innerBound g k

private def levelBound (a : ℕ) : ℕ → ℕ
  | 0 => innerBound 0 a
  | d + 1 => innerBound (levelBound a d) a

private def fBound (a d k : ℕ) : ℕ :=
  innerBound (match d with | 0 => 0 | d' + 1 => levelBound a d') k

private lemma fBound_zero_zero (a : ℕ) : fBound a 0 0 = 1 := rfl

private lemma fBound_succ_zero (a d : ℕ) : fBound a (d + 1) 0 = 1 + fBound a d a := by
  cases d <;> rfl

private lemma fBound_succ_k (a d k : ℕ) : fBound a d (k + 1) = 1 + (k + 1) * fBound a d k := rfl

private lemma innerBound_eq (g k : ℕ) :
    innerBound g k =
      (Finset.range (k + 1)).sum (fun j => Nat.factorial k / Nat.factorial (k - j)) +
        Nat.factorial k * g := by
  induction k with
  | zero => simp [innerBound]
  | succ k ih =>
    simp only [innerBound, ih]
    conv_rhs => rw [Finset.sum_range_succ']
    have h0 : Nat.factorial (k + 1) / Nat.factorial (k + 1 - 0) = 1 := by
      simp [Nat.div_self (Nat.factorial_pos (k + 1))]
    rw [h0]
    have hsum : (Finset.range (k + 1)).sum (fun j => Nat.factorial (k + 1) / Nat.factorial (k + 1 - (j + 1))) =
        (k + 1) * (Finset.range (k + 1)).sum (fun j => Nat.factorial k / Nat.factorial (k - j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Nat.succ_sub_succ, Nat.factorial_succ,
        Nat.mul_div_assoc (k + 1) (Nat.factorial_dvd_factorial (Nat.sub_le k j))]
    rw [hsum, Nat.factorial_succ]
    ring

private lemma levelBound_eq (a d : ℕ) :
    levelBound a d =
      ((Finset.range (a + 1)).sum (fun j => Nat.factorial a / Nat.factorial (a - j))) *
        (Finset.range (d + 1)).sum (fun j => (Nat.factorial a) ^ j) := by
  set F := Nat.factorial a
  set H := (Finset.range (a + 1)).sum (fun j => F / Nat.factorial (a - j))
  induction d with
  | zero =>
    simp [levelBound, innerBound_eq, F, H]
  | succ d ih =>
    simp only [levelBound, innerBound_eq, ih, F, H]
    have hrhs : (Finset.range (d + 1 + 1)).sum (fun j => (Nat.factorial a) ^ j) =
        1 + Nat.factorial a * (Finset.range (d + 1)).sum (fun j => (Nat.factorial a) ^ j) := by
      rw [Finset.sum_range_succ', pow_zero, add_comm]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_succ']
    rw [hrhs]
    ring

private lemma fBound_top_eq (a b : ℕ) :
    fBound a (2 ^ b - 1) a =
      ((Finset.range (a + 1)).sum (fun j => Nat.factorial a / Nat.factorial (a - j))) *
        (Finset.range (2 ^ b)).sum (fun j => (Nat.factorial a) ^ j) := by
  have hpos : 1 ≤ 2 ^ b := Nat.one_le_pow _ _ (by omega)
  have hfb : fBound a (2 ^ b - 1) a = levelBound a (2 ^ b - 1) := by
    cases h : 2 ^ b - 1 <;> rfl
  rw [hfb, levelBound_eq, Nat.sub_add_cancel hpos]

-- =========================================================================
-- Part 4: Outward forest decomposition and witness theorem
-- =========================================================================

private def isForest {n : ℕ} (U : Finset (Finset (Fin n))) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, y ⊆ x → z ⊆ x → y ⊆ z ∨ z ⊆ y

private lemma isForest_subset {n : ℕ} {U W : Finset (Finset (Fin n))}
    (hF : isForest U) (hWU : W ⊆ U) : isForest W :=
  fun x hx y hy z hz => hF x (hWU hx) y (hWU hy) z (hWU hz)

private def isRoot {n : ℕ} (U : Finset (Finset (Fin n))) (r : Finset (Fin n)) : Prop :=
  r ∈ U ∧ ∀ y ∈ U, y ⊆ r → y = r

private lemma exists_unique_root {n : ℕ} {U : Finset (Finset (Fin n))} (hF : isForest U)
    {x : Finset (Fin n)} (hx : x ∈ U) :
    ∃! r, isRoot U r ∧ r ⊆ x := by
  let anc := U.filter (fun y => y ⊆ x)
  have hne : anc.Nonempty := ⟨x, Finset.mem_filter.mpr ⟨hx, Finset.Subset.refl _⟩⟩
  rcases Finset.exists_min_image anc Finset.card hne with ⟨r, hr_anc, hr_min⟩
  rcases Finset.mem_filter.mp hr_anc with ⟨hrU, hrx⟩
  have hr_root : isRoot U r := by
    refine ⟨hrU, fun y hyU hyr => ?_⟩
    have hy_anc : y ∈ anc := Finset.mem_filter.mpr ⟨hyU, Finset.Subset.trans hyr hrx⟩
    have hcard : r.card ≤ y.card := hr_min y hy_anc
    exact Finset.eq_of_subset_of_card_le hyr hcard
  refine ⟨r, ⟨hr_root, hrx⟩, fun r' ⟨hr'_root, hr'x⟩ => ?_⟩
  rcases hF x hx r hrU r' hr'_root.1 hrx hr'x with hrr' | hr'r
  · exact (hr'_root.2 r hrU hrr').symm
  · exact hr_root.2 r' hr'_root.1 hr'r

private def ValidFrom {n a : ℕ} (M : ℕ) (S : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → ℕ × (Fin a → Bool) → Prop) (s0 : ℕ × (Fin a → Bool)) : Prop :=
  ∃ τ : Finset (Fin n) → ℕ × (Fin a → Bool),
    (∀ x ∈ S, (τ x).1 < M ∧ L x (τ x)) ∧
    (∀ x ∈ S, stateLe s0 (τ x)) ∧
    (∀ x ∈ S, ∀ y ∈ S, x ⊆ y → stateLe (τ x) (τ y))

private lemma validFrom_mono_set {n a M : ℕ} {S1 S2 : Finset (Finset (Fin n))}
    {L : Finset (Fin n) → ℕ × (Fin a → Bool) → Prop} {s0 : ℕ × (Fin a → Bool)}
    (h12 : S1 ⊆ S2) (h : ValidFrom M S2 L s0) : ValidFrom M S1 L s0 := by
  rcases h with ⟨τ, h1, h2, h3⟩
  exact ⟨τ, fun x hx => h1 x (h12 hx), fun x hx => h2 x (h12 hx),
    fun x hx y hy => h3 x (h12 hx) y (h12 hy)⟩

private lemma validFrom_mono_lb {n a M : ℕ} {S : Finset (Finset (Fin n))}
    {L : Finset (Fin n) → ℕ × (Fin a → Bool) → Prop} {s0 s1 : ℕ × (Fin a → Bool)}
    (hle : stateLe s0 s1) (h : ValidFrom M S L s1) : ValidFrom M S L s0 := by
  rcases h with ⟨τ, h1, h2, h3⟩
  exact ⟨τ, h1, fun x hx => stateLe_trans hle (h2 x hx), h3⟩

private def subtree {n : ℕ} (U : Finset (Finset (Fin n))) (x : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  U.filter (fun z => x ⊆ z)

private lemma forest_validFrom_iff_roots {n a M : ℕ} {U : Finset (Finset (Fin n))} (hF : isForest U)
    (L : Finset (Fin n) → ℕ × (Fin a → Bool) → Prop) (s0 : ℕ × (Fin a → Bool)) :
    ValidFrom M U L s0 ↔ ∀ r, isRoot U r → ValidFrom M (subtree U r) L s0 := by
  constructor
  · intro hU r _
    exact validFrom_mono_set (Finset.filter_subset _ _) hU
  · intro hall
    have hchoice : ∀ r, isRoot U r →
        ∃ τ : Finset (Fin n) → ℕ × (Fin a → Bool),
          (∀ x ∈ subtree U r, (τ x).1 < M ∧ L x (τ x)) ∧
          (∀ x ∈ subtree U r, stateLe s0 (τ x)) ∧
          (∀ x ∈ subtree U r, ∀ y ∈ subtree U r, x ⊆ y → stateLe (τ x) (τ y)) := hall
    let rootOf : Finset (Fin n) → Finset (Fin n) := fun x =>
      if hx : x ∈ U then Classical.choose (exists_unique_root hF hx) else x
    have hrootOf_spec : ∀ x (hx : x ∈ U),
        isRoot U (rootOf x) ∧ rootOf x ⊆ x ∧
        ∀ r', isRoot U r' → r' ⊆ x → r' = rootOf x := by
      intro x hx
      have hspec := Classical.choose_spec (exists_unique_root hF hx)
      refine ⟨?_, ?_, fun r' hr' hsub => ?_⟩
      · simp only [rootOf, dif_pos hx]; exact hspec.1.1
      · simp only [rootOf, dif_pos hx]; exact hspec.1.2
      · simp only [rootOf, dif_pos hx]; exact hspec.2 r' ⟨hr', hsub⟩
    let τOf : Finset (Fin n) → Finset (Fin n) → ℕ × (Fin a → Bool) := fun r =>
      if hr : isRoot U r then Classical.choose (hchoice r hr) else fun _ => s0
    have hτOf_spec : ∀ r (hr : isRoot U r),
        (∀ x ∈ subtree U r, (τOf r x).1 < M ∧ L x (τOf r x)) ∧
        (∀ x ∈ subtree U r, stateLe s0 (τOf r x)) ∧
        (∀ x ∈ subtree U r, ∀ y ∈ subtree U r, x ⊆ y → stateLe (τOf r x) (τOf r y)) := by
      intro r hr
      simp only [τOf, dif_pos hr]
      exact Classical.choose_spec (hchoice r hr)
    refine ⟨fun x => τOf (rootOf x) x, ?_, ?_, ?_⟩
    · intro x hx
      have hr := hrootOf_spec x hx
      exact (hτOf_spec (rootOf x) hr.1).1 x (Finset.mem_filter.mpr ⟨hx, hr.2.1⟩)
    · intro x hx
      have hr := hrootOf_spec x hx
      exact (hτOf_spec (rootOf x) hr.1).2.1 x (Finset.mem_filter.mpr ⟨hx, hr.2.1⟩)
    · intro x hx y hy hxy
      dsimp only
      have hrx := hrootOf_spec x hx
      have hry := hrootOf_spec y hy
      have hreq : rootOf x = rootOf y := hry.2.2 (rootOf x) hrx.1 (Finset.Subset.trans hrx.2.1 hxy)
      rw [hreq]
      exact (hτOf_spec (rootOf y) hry.1).2.2 x
        (Finset.mem_filter.mpr ⟨hx, by rw [← hreq]; exact hrx.2.1⟩)
        y (Finset.mem_filter.mpr ⟨hy, hry.2.1⟩) hxy

private lemma subtree_witness {n a M : ℕ} (ha : 0 < a) {U : Finset (Finset (Fin n))} (hF : isForest U)
    (L : Finset (Fin n) → ℕ × (Fin a → Bool) → Prop) :
    ∀ (idx : ℕ) (x : Finset (Fin n)) (s0 : ℕ × (Fin a → Bool)),
      x ∈ U → s0.1 < M →
      let d := M - 1 - s0.1
      let k := (Finset.univ.filter (fun i : Fin a => s0.2 i = false)).card
      d * (a + 1) + k = idx →
      ¬ ValidFrom M (subtree U x) L s0 →
      ∃ S : Finset (Finset (Fin n)), S ⊆ subtree U x ∧ S.card ≤ fBound a d k ∧ ¬ ValidFrom M S L s0 := by
  intro idx
  induction idx using Nat.strong_induction_on with
  | _ idx ih =>
    intro x s0 hxU hs0_lt d k hidx hnot
    -- Pick a deepest (maximal cardinality) bad node x* in subtree U x
    let Bad := (subtree U x).filter (fun y => ¬ ValidFrom M (subtree U y) L s0)
    have hx_bad : x ∈ Bad := Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hxU, Finset.Subset.refl _⟩, hnot⟩
    rcases Finset.exists_max_image Bad Finset.card ⟨x, hx_bad⟩ with ⟨xs, hxs_bad, hxs_max⟩
    rcases Finset.mem_filter.mp hxs_bad with ⟨hxs_Tx, hxs_not⟩
    rcases Finset.mem_filter.mp hxs_Tx with ⟨hxsU, hxxs⟩
    have hTxs_sub : subtree U xs ⊆ subtree U x := by
      intro z hz
      rcases Finset.mem_filter.mp hz with ⟨hzU, hxsz⟩
      exact Finset.mem_filter.mpr ⟨hzU, Finset.Subset.trans hxxs hxsz⟩
    -- Prove ¬ L xs s0
    have hnotL : ¬ L xs s0 := by
      intro hLxs
      apply hxs_not
      let strict := (subtree U xs).erase xs
      have hstrict_sub : strict ⊆ U := Finset.Subset.trans (Finset.erase_subset _ _) (Finset.filter_subset _ _)
      have hstrict_forest : isForest strict := isForest_subset hF hstrict_sub
      have hstrict_valid : ValidFrom M strict L s0 := by
        rw [forest_validFrom_iff_roots hstrict_forest]
        intro r hr
        have hr_mem : r ∈ strict := hr.1
        rcases Finset.mem_erase.mp hr_mem with ⟨hr_ne, hr_Txs⟩
        have hr_Tx : r ∈ subtree U x := hTxs_sub hr_Txs
        have hr_card_gt : xs.card < r.card := by
          have hsub : xs ⊆ r := (Finset.mem_filter.mp hr_Txs).2
          exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun h => hr_ne h.symm⟩)
        have hr_ok : ValidFrom M (subtree U r) L s0 := by
          by_contra hr_bad
          have hle := hxs_max r (Finset.mem_filter.mpr ⟨hr_Tx, hr_bad⟩)
          omega
        exact validFrom_mono_set (by
          intro z hz
          rcases Finset.mem_filter.mp hz with ⟨hzs, hrz⟩
          exact Finset.mem_filter.mpr ⟨hstrict_sub hzs, hrz⟩) hr_ok
      rcases hstrict_valid with ⟨τ, hτ1, hτ2, hτ3⟩
      refine ⟨fun z => if z = xs then s0 else τ z, ?_, ?_, ?_⟩
      · intro z hz
        by_cases hzx : z = xs
        · subst hzx; simp only [ite_true]; exact ⟨hs0_lt, hLxs⟩
        · simp only [if_neg hzx]
          exact hτ1 z (Finset.mem_erase.mpr ⟨hzx, hz⟩)
      · intro z hz
        by_cases hzx : z = xs
        · subst hzx; simp only [ite_true]; exact stateLe_refl s0
        · simp only [if_neg hzx]
          exact hτ2 z (Finset.mem_erase.mpr ⟨hzx, hz⟩)
      · intro z1 hz1 z2 hz2 h12
        dsimp only
        by_cases h1 : z1 = xs
        · rw [h1]
          by_cases h2 : z2 = xs
          · rw [h2]; simp only [ite_true]; exact stateLe_refl s0
          · simp only [ite_true, if_neg h2]
            exact hτ2 z2 (Finset.mem_erase.mpr ⟨h2, hz2⟩)
        · have h2 : z2 ≠ xs := by
            intro h2eq
            rw [h2eq] at h12
            have hxz1 : xs ⊆ z1 := (Finset.mem_filter.mp hz1).2
            exact h1 (Finset.Subset.antisymm h12 hxz1)
          simp only [if_neg h1, if_neg h2]
          exact hτ3 z1 (Finset.mem_erase.mpr ⟨h1, hz1⟩) z2 (Finset.mem_erase.mpr ⟨h2, hz2⟩) h12
    -- Now split on k and d
    let Z := Finset.univ.filter (fun i : Fin a => s0.2 i = false)
    have hk_eq : Z.card = k := rfl
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · have hall_true : ∀ i : Fin a, s0.2 i = true := by
        intro i
        cases hi : s0.2 i with
        | true => rfl
        | false =>
          have hmem : i ∈ Z := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
          have hpos : 0 < Z.card := Finset.card_pos.mpr ⟨i, hmem⟩
          omega
      rcases Nat.eq_zero_or_pos d with hd0 | hdpos
      · -- Subcase k = 0, d = 0
        refine ⟨{xs}, Finset.singleton_subset_iff.mpr hxs_Tx, ?_, ?_⟩
        · rw [hd0, hk0, fBound_zero_zero]; simp
        · rintro ⟨τ, hτ1, hτ2, _⟩
          have h1 := hτ1 xs (Finset.mem_singleton_self xs)
          have h2 := hτ2 xs (Finset.mem_singleton_self xs)
          have heq : τ xs = s0 := by
            apply Prod.ext
            · rcases h2 with hlt | ⟨heq, _⟩ <;> omega
            · funext i
              rcases h2 with hlt | ⟨_, hw⟩
              · omega
              · rw [hall_true i]; exact hw i (hall_true i)
          rw [heq] at h1
          exact hnotL h1.2
      · -- Subcase k = 0, d > 0
        set d' := d - 1
        have hd_eq : d = d' + 1 := by omega
        let s1 : ℕ × (Fin a → Bool) := (s0.1 + 1, fun _ => false)
        have hs1_lt : s1.1 < M := by dsimp [s1, d] at *; omega
        have hle01 : stateLe s0 s1 := Or.inl (by dsimp [s1]; omega)
        have hnot1 : ¬ ValidFrom M (subtree U xs) L s1 :=
          fun h => hxs_not (validFrom_mono_lb hle01 h)
        have hd1 : M - 1 - s1.1 = d' := by dsimp [s1, d', d]; omega
        have hk1 : (Finset.univ.filter (fun i : Fin a => s1.2 i = false)).card = a := by
          simp [s1]
        have hidx1 : d' * (a + 1) + a < idx := by
          rw [← hidx, hd_eq, hk0]
          have : (d' + 1) * (a + 1) = d' * (a + 1) + a + 1 := by ring
          omega
        rcases ih (d' * (a + 1) + a) hidx1 xs s1 hxsU hs1_lt (by rw [hd1, hk1]) hnot1 with
          ⟨S1, hS1_sub, hS1_card, hS1_not⟩
        rw [hd1, hk1] at hS1_card
        refine ⟨insert xs S1, Finset.insert_subset hxs_Tx (Finset.Subset.trans hS1_sub hTxs_sub), ?_, ?_⟩
        · rw [hd_eq, hk0, fBound_succ_zero]
          exact le_trans (Finset.card_insert_le xs S1) (by omega)
        · rintro ⟨τ, hτ1, hτ2, hτ3⟩
          have hxs_mem : xs ∈ insert xs S1 := Finset.mem_insert_self xs S1
          have h1 := hτ1 xs hxs_mem
          have h2 := hτ2 xs hxs_mem
          have hs1_le_xs : stateLe s1 (τ xs) := by
            rcases h2 with hlt | ⟨heq, hw⟩
            · have hge : s0.1 + 1 ≤ (τ xs).1 := by omega
              rcases lt_or_eq_of_le hge with hlt' | heq'
              · exact Or.inl hlt'
              · exact Or.inr ⟨heq', fun i hi => by simp [s1] at hi⟩
            · exfalso
              have hteq : τ xs = s0 := by
                apply Prod.ext heq.symm
                funext i
                rw [hall_true i]; exact hw i (hall_true i)
              rw [hteq] at h1
              exact hnotL h1.2
          apply hS1_not
          refine ⟨τ, fun z hz => hτ1 z (Finset.mem_insert_of_mem hz), fun z hz => ?_,
            fun z1 hz1 z2 hz2 => hτ3 z1 (Finset.mem_insert_of_mem hz1) z2 (Finset.mem_insert_of_mem hz2)⟩
          have hxsz : xs ⊆ z := (Finset.mem_filter.mp (hS1_sub hz)).2
          exact stateLe_trans hs1_le_xs (hτ3 xs hxs_mem z (Finset.mem_insert_of_mem hz) hxsz)
    · -- Subcase k > 0
      set k' := k - 1
      have hk_eq' : k = k' + 1 := by omega
      have hbranch : ∀ i : Fin a, i ∈ Z →
          ∃ Si : Finset (Finset (Fin n)), Si ⊆ subtree U xs ∧ Si.card ≤ fBound a d k' ∧
            ¬ ValidFrom M Si L (s0.1, Function.update s0.2 i true) := by
        intro i hiZ
        have hi0 : s0.2 i = false := (Finset.mem_filter.mp hiZ).2
        let si : ℕ × (Fin a → Bool) := (s0.1, Function.update s0.2 i true)
        have hle0i : stateLe s0 si := by
          right
          refine ⟨rfl, fun j hj => ?_⟩
          by_cases hji : j = i
          · subst hji; rw [hi0] at hj; cases hj
          · simpa [si, Function.update, hji] using hj
        have hnoti : ¬ ValidFrom M (subtree U xs) L si :=
          fun h => hxs_not (validFrom_mono_lb hle0i h)
        have hZi_eq : Finset.univ.filter (fun j : Fin a => si.2 j = false) = Z.erase i := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, Z, si]
          by_cases hji : j = i
          · subst hji; simp [Function.update]
          · simp [Function.update, hji]
        have hki : (Finset.univ.filter (fun j : Fin a => si.2 j = false)).card = k' := by
          rw [hZi_eq, Finset.card_erase_of_mem hiZ, hk_eq, hk_eq']; omega
        have hdi : M - 1 - si.1 = d := rfl
        have hidxi : d * (a + 1) + k' < idx := by rw [← hidx, hk_eq']; omega
        rcases ih (d * (a + 1) + k') hidxi xs si hxsU hs0_lt (by rw [hdi, hki]) hnoti with
          ⟨Si, hSi_sub, hSi_card, hSi_not⟩
        rw [hdi, hki] at hSi_card
        exact ⟨Si, hSi_sub, hSi_card, hSi_not⟩
      let SOf : Fin a → Finset (Finset (Fin n)) := fun i =>
        if hi : i ∈ Z then Classical.choose (hbranch i hi) else ∅
      have hSOf_spec : ∀ i (hi : i ∈ Z),
          SOf i ⊆ subtree U xs ∧ (SOf i).card ≤ fBound a d k' ∧
          ¬ ValidFrom M (SOf i) L (s0.1, Function.update s0.2 i true) := by
        intro i hi
        simp only [SOf, dif_pos hi]
        exact Classical.choose_spec (hbranch i hi)
      let S := insert xs (Z.biUnion SOf)
      refine ⟨S, ?_, ?_, ?_⟩
      · apply Finset.insert_subset hxs_Tx
        rw [Finset.biUnion_subset]
        intro i hiZ
        exact Finset.Subset.trans (hSOf_spec i hiZ).1 hTxs_sub
      · rw [hk_eq', fBound_succ_k]
        calc S.card ≤ (Z.biUnion SOf).card + 1 := Finset.card_insert_le xs _
          _ ≤ Z.sum (fun i => (SOf i).card) + 1 := Nat.add_le_add_right Finset.card_biUnion_le 1
          _ ≤ Z.sum (fun _ => fBound a d k') + 1 :=
              Nat.add_le_add_right (Finset.sum_le_sum fun i hi => (hSOf_spec i hi).2.1) 1
          _ = Z.card * fBound a d k' + 1 := by simp
          _ = 1 + (k' + 1) * fBound a d k' := by rw [hk_eq, hk_eq']; omega
      · rintro ⟨τ, hτ1, hτ2, hτ3⟩
        have hxs_mem : xs ∈ S := Finset.mem_insert_self xs _
        have h1 := hτ1 xs hxs_mem
        have h2 := hτ2 xs hxs_mem
        have hex_i : ∃ i ∈ Z, stateLe (s0.1, Function.update s0.2 i true) (τ xs) := by
          rcases h2 with hlt | ⟨heq, hw⟩
          · rcases Finset.card_pos.mp (by omega : 0 < Z.card) with ⟨i, hiZ⟩
            exact ⟨i, hiZ, Or.inl hlt⟩
          · have hne_w : (τ xs).2 ≠ s0.2 := by
              intro hweq
              have hteq : τ xs = s0 := Prod.ext heq.symm hweq
              rw [hteq] at h1
              exact hnotL h1.2
            have hex_diff : ∃ i : Fin a, (τ xs).2 i ≠ s0.2 i := by
              by_contra hall
              push_neg at hall
              exact hne_w (funext hall)
            rcases hex_diff with ⟨i, hi_ne⟩
            have hi0 : s0.2 i = false := by
              cases hs0i : s0.2 i with
              | false => rfl
              | true =>
                have hti := hw i hs0i
                rw [hti, hs0i] at hi_ne
                exact absurd rfl hi_ne
            have hti : (τ xs).2 i = true := by
              cases htv : (τ xs).2 i with
              | true => rfl
              | false => rw [htv, hi0] at hi_ne; exact absurd rfl hi_ne
            have hiZ : i ∈ Z := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi0⟩
            refine ⟨i, hiZ, Or.inr ⟨heq, fun j hj => ?_⟩⟩
            by_cases hji : j = i
            · subst hji; exact hti
            · simp only [Function.update, hji, ite_false] at hj
              exact hw j hj
        rcases hex_i with ⟨i, hiZ, hsi_le⟩
        have hSi_sub_S : SOf i ⊆ S :=
          Finset.Subset.trans (Finset.subset_biUnion_of_mem SOf hiZ) (Finset.subset_insert xs _)
        apply (hSOf_spec i hiZ).2.2
        refine ⟨τ, fun z hz => hτ1 z (hSi_sub_S hz), fun z hz => ?_,
          fun z1 hz1 z2 hz2 => hτ3 z1 (hSi_sub_S hz1) z2 (hSi_sub_S hz2)⟩
        have hxsz : xs ⊆ z := (Finset.mem_filter.mp ((hSOf_spec i hiZ).1 hz)).2
        exact stateLe_trans hsi_le (hτ3 xs hxs_mem z (hSi_sub_S hz) hxsz)

private lemma forest_witness {n a b : ℕ} (ha : 0 < a) {U : Finset (Finset (Fin n))} (hF : isForest U)
    (L : Finset (Fin n) → ℕ × (Fin a → Bool) → Prop)
    (hnot : ¬ ValidFrom (2 ^ b) U L (0, fun _ => false)) :
    ∃ S : Finset (Finset (Fin n)), S ⊆ U ∧
      S.card ≤ ((Finset.range (a + 1)).sum (fun j => Nat.factorial a / Nat.factorial (a - j))) *
        (Finset.range (2 ^ b)).sum (fun j => (Nat.factorial a) ^ j) ∧
      ¬ ValidFrom (2 ^ b) S L (0, fun _ => false) := by
  have hex_root : ∃ r, isRoot U r ∧ ¬ ValidFrom (2 ^ b) (subtree U r) L (0, fun _ => false) := by
    by_contra hall
    push_neg at hall
    exact hnot ((forest_validFrom_iff_roots hF L (0, fun _ => false)).mpr hall)
  rcases hex_root with ⟨r, hr, hr_not⟩
  have hpos : 0 < 2 ^ b := Nat.pos_of_ne_zero (by positivity)
  have hd : 2 ^ b - 1 - 0 = 2 ^ b - 1 := rfl
  have hk : (Finset.univ.filter (fun _ : Fin a => false = false)).card = a := by simp
  rcases subtree_witness ha hF L ((2 ^ b - 1) * (a + 1) + a) r (0, fun _ => false)
      hr.1 hpos (by rw [hd, hk]) hr_not with ⟨S, hS_sub, hS_card, hS_not⟩
  rw [hd, hk, fBound_top_eq] at hS_card
  exact ⟨S, Finset.Subset.trans hS_sub (Finset.filter_subset _ _), hS_card, hS_not⟩

-- =========================================================================
-- Part 5: Main core theorem (a = 0 and a > 0)
-- =========================================================================

private lemma main_core (n a B : ℕ) (V J U : Finset (Finset (Fin n)))
    (ok : Finset (Fin n) → (Fin a → Bool) → Prop)
    (hJV : J ⊆ V) (hU_iff : ∀ x, x ∈ U ↔ x ∈ V ∧ x ∉ J) (hF : isForest U) :
    let bound := fun (a b : ℕ) =>
      let F := Nat.factorial a
      let H := (Finset.range (a + 1)).sum (fun j => F / Nat.factorial (a - j))
      if a = 0 then 1 else H * (Finset.range (2 ^ b)).sum (fun j => F ^ j)
    let words := {x : Finset (Fin n) // x ∈ J} → Fin a → Bool
    let fitStd := fun (S : Finset (Finset (Fin n))) (b : ℕ) (extra : words → Prop) =>
      ∃ (C : Circuit) (tap : Fin a → ℕ),
        FanInTwo C ∧ ReadsBack (n + 2) C ∧
        C.output < n + 2 + C.size ∧ notCount C ≤ b ∧
        (∀ i, tap i < n + 2 + C.size) ∧
        (∀ x ∈ S, ok x (fun i => (C.wires (rawStd n x)).getD (tap i) false)) ∧
        extra (fun j i => (C.wires (rawStd n j.val)).getD (tap i) false)
    let K := if a = 0 then 1 else 2 ^ (a + B)
    ∃ S : Finset (Finset (Fin n)), J ⊆ S ∧ S ⊆ V ∧
      S.card ≤ J.card + K ^ J.card * bound a B ∧
      ∀ b ≤ B, ∀ extra : words → Prop, fitStd V b extra ↔ fitStd S b extra := by
  intro bound words fitStd K
  -- Helper: fitStd S b extra ↔ ∃ ω, extra ω ∧ feas S b ω
  let feas := fun (S : Finset (Finset (Fin n))) (b : ℕ) (ω : words) =>
    ∃ σ : Finset (Fin n) → ℕ × (Fin a → Bool),
      (∀ x ∈ S, (σ x).1 < 2 ^ b ∧ ok x (σ x).2) ∧
      (∀ x ∈ S, ∀ y ∈ S, x ⊆ y → stateLe (σ x) (σ y)) ∧
      (∀ j : {x : Finset (Fin n) // x ∈ J}, (σ j.val).2 = ω j)
  have hfit_iff : ∀ (S : Finset (Finset (Fin n))), J ⊆ S → ∀ b extra,
      fitStd S b extra ↔ ∃ ω : words, extra ω ∧ feas S b ω := by
    intro S hJS b extra
    constructor
    · rintro ⟨C, tap, hfan, hrb, _, hnot, htap, hok, hextra⟩
      rcases circuit_to_assign S C tap hfan hrb hnot htap with ⟨σ, hlt, hmono, hev⟩
      refine ⟨fun j i => (C.wires (rawStd n j.val)).getD (tap i) false, hextra, σ, ?_, hmono, ?_⟩
      · intro x hx
        refine ⟨hlt x hx, ?_⟩
        have hweq : (σ x).2 = fun i => (C.wires (rawStd n x)).getD (tap i) false := funext (hev x hx)
        rw [hweq]; exact hok x hx
      · intro j
        funext i
        exact hev j.val (hJS j.property) i
    · rintro ⟨ω, hextra, σ, hσ1, hmono, hω⟩
      rcases assign_to_circuit S σ (fun x hx => (hσ1 x hx).1) hmono with
        ⟨C, tap, hfan, hrb, hout, hnot, htap, hev⟩
      refine ⟨C, tap, hfan, hrb, hout, hnot, htap, ?_, ?_⟩
      · intro x hx
        have hweq : (fun i => (C.wires (rawStd n x)).getD (tap i) false) = (σ x).2 := funext (hev x hx)
        rw [hweq]; exact (hσ1 x hx).2
      · have hjeq : (fun j : {x : Finset (Fin n) // x ∈ J} => fun i => (C.wires (rawStd n j.val)).getD (tap i) false) = ω := by
          funext j i
          rw [hev j.val (hJS j.property) i, hω j]
        rw [hjeq]; exact hextra
  have hfeas_sub : ∀ {S1 S2 : Finset (Finset (Fin n))} {b : ℕ} {ω : words},
      S1 ⊆ S2 → feas S2 b ω → feas S1 b ω := by
    intro S1 S2 b ω h12 ⟨σ, h1, h2, h3⟩
    exact ⟨σ, fun x hx => h1 x (h12 hx), fun x hx y hy => h2 x (h12 hx) y (h12 hy), h3⟩
  have hfeas_mono_b : ∀ {S : Finset (Finset (Fin n))} {b1 b2 : ℕ} {ω : words},
      b1 ≤ b2 → feas S b1 ω → feas S b2 ω := by
    intro S b1 b2 ω h12 ⟨σ, h1, h2, h3⟩
    have hpow : 2 ^ b1 ≤ 2 ^ b2 := Nat.pow_le_pow_right (by omega) h12
    exact ⟨σ, fun x hx => ⟨lt_of_lt_of_le (h1 x hx).1 hpow, (h1 x hx).2⟩, h2, h3⟩
  -- Case split on a = 0 vs a > 0
  by_cases ha0 : a = 0
  · subst ha0
    have hK1 : K = 1 := rfl
    have hb1 : bound 0 B = 1 := rfl
    let w0 : Fin 0 → Bool := Fin.elim0
    have huniq_w : ∀ w : Fin 0 → Bool, w = w0 := fun w => funext (fun i => Fin.elim0 i)
    by_cases hall : ∀ x ∈ V, ok x w0
    · refine ⟨J, Finset.Subset.refl _, hJV, ?_, fun b _ extra => ?_⟩
      · rw [hK1, hb1]; simp
      · rw [hfit_iff V hJV b extra, hfit_iff J (Finset.Subset.refl _) b extra]
        constructor
        · rintro ⟨ω, hex, hf⟩; exact ⟨ω, hex, hfeas_sub hJV hf⟩
        · rintro ⟨ω, hex, _⟩
          refine ⟨ω, hex, fun _ => (0, w0), ?_, fun _ _ _ _ _ => stateLe_refl _, fun j => (huniq_w (ω j)).symm⟩
          intro x hx
          exact ⟨Nat.pos_of_ne_zero (by positivity), hall x hx⟩
    · push_neg at hall
      rcases hall with ⟨x0, hx0V, hnot_ok⟩
      refine ⟨insert x0 J, Finset.subset_insert x0 J, Finset.insert_subset hx0V hJV, ?_, fun b _ extra => ?_⟩
      · rw [hK1, hb1, one_pow, mul_one]
        exact Finset.card_insert_le x0 J
      · rw [hfit_iff V hJV b extra, hfit_iff (insert x0 J) (Finset.subset_insert x0 J) b extra]
        constructor
        · rintro ⟨ω, hex, hf⟩; exact ⟨ω, hex, hfeas_sub (Finset.insert_subset hx0V hJV) hf⟩
        · rintro ⟨ω, _, σ, hσ1, _, _⟩
          have hok0 := (hσ1 x0 (Finset.mem_insert_self x0 J)).2
          rw [huniq_w (σ x0).2] at hok0
          exact absurd hok0 hnot_ok
  · -- Case a > 0
    have hapos : 0 < a := Nat.pos_of_ne_zero ha0
    have hK_eq : K = 2 ^ (a + B) := by simp [K, ha0]
    have hbound_eq : ∀ b, bound a b =
        ((Finset.range (a + 1)).sum (fun j => Nat.factorial a / Nat.factorial (a - j))) *
          (Finset.range (2 ^ b)).sum (fun j => (Nat.factorial a) ^ j) := by
      intro b; simp [bound, ha0]
    have hbound_mono : ∀ b ≤ B, bound a b ≤ bound a B := by
      intro b hb
      rw [hbound_eq b, hbound_eq B]
      apply Nat.mul_le_mul_left
      have hpow : 2 ^ b ≤ 2 ^ B := Nat.pow_le_pow_right (by omega) hb
      exact Finset.sum_le_sum_of_subset (Finset.range_mono hpow)
    -- For each ω : words, build a witness subset S_ω ⊆ U
    have hfor_word : ∀ ω : words,
        ∃ Sω : Finset (Finset (Fin n)), Sω ⊆ U ∧ Sω.card ≤ (2 ^ B) ^ J.card * bound a B ∧
          ∀ b ≤ B, ¬ feas V b ω → ¬ feas (J ∪ Sω) b ω := by
      intro ω
      by_cases hfail : ∃ b ≤ B, ¬ feas V b ω
      · -- Choose the largest b ≤ B where ¬ feas V b ω
        let failSet := (Finset.range (B + 1)).filter (fun b => ¬ feas V b ω)
        have hfail_ne : failSet.Nonempty := by
          rcases hfail with ⟨b0, hb0, hnf⟩
          exact ⟨b0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hnf⟩⟩
        let bm := failSet.max' hfail_ne
        have hbm_mem : bm ∈ failSet := Finset.max'_mem failSet hfail_ne
        have hbm_le : bm ≤ B := by
          have := (Finset.mem_filter.mp hbm_mem).1
          rw [Finset.mem_range] at this; omega
        have hbm_not : ¬ feas V bm ω := (Finset.mem_filter.mp hbm_mem).2
        have hbm_max : ∀ b ≤ B, ¬ feas V b ω → b ≤ bm := fun b hb hnb =>
          Finset.le_max' failSet b (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hnb⟩)
        -- Check whether ω already fails ok on J
        by_cases hokJ : ∀ j : {x : Finset (Fin n) // x ∈ J}, ok j.val (ω j)
        · -- Enumerate rank profiles ρ : {x // x ∈ J} → Fin (2 ^ bm)
          let Prof := {x : Finset (Fin n) // x ∈ J} → Fin (2 ^ bm)
          let profOk := fun (ρ : Prof) =>
            ∀ j1 j2 : {x : Finset (Fin n) // x ∈ J}, j1.val ⊆ j2.val →
              stateLe ((ρ j1).val, ω j1) ((ρ j2).val, ω j2)
          let Lprof := fun (ρ : Prof) (x : Finset (Fin n)) (s : ℕ × (Fin a → Bool)) =>
            ok x s.2 ∧
            (∀ j : {y : Finset (Fin n) // y ∈ J}, j.val ⊆ x → stateLe ((ρ j).val, ω j) s) ∧
            (∀ j : {y : Finset (Fin n) // y ∈ J}, x ⊆ j.val → stateLe s ((ρ j).val, ω j))
          have hprof_witness : ∀ ρ : Prof,
              ∃ Sρ : Finset (Finset (Fin n)), Sρ ⊆ U ∧ Sρ.card ≤ bound a B ∧
                (profOk ρ → ¬ ValidFrom (2 ^ bm) Sρ (Lprof ρ) (0, fun _ => false)) := by
            intro ρ
            by_cases hp : profOk ρ
            · have hnotU : ¬ ValidFrom (2 ^ bm) U (Lprof ρ) (0, fun _ => false) := by
                rintro ⟨τ, hτ1, _, hτ3⟩
                apply hbm_not
                let σ : Finset (Fin n) → ℕ × (Fin a → Bool) := fun x =>
                  if hx : x ∈ J then ((ρ ⟨x, hx⟩).val, ω ⟨x, hx⟩) else τ x
                refine ⟨σ, ?_, ?_, ?_⟩
                · intro x hxV
                  by_cases hxJ : x ∈ J
                  · simp only [σ, dif_pos hxJ]
                    exact ⟨(ρ ⟨x, hxJ⟩).isLt, hokJ ⟨x, hxJ⟩⟩
                  · simp only [σ, dif_neg hxJ]
                    have hxU : x ∈ U := (hU_iff x).mpr ⟨hxV, hxJ⟩
                    exact ⟨(hτ1 x hxU).1, (hτ1 x hxU).2.1⟩
                · intro x hxV y hyV hxy
                  by_cases hxJ : x ∈ J <;> by_cases hyJ : y ∈ J
                  · simp only [σ, dif_pos hxJ, dif_pos hyJ]
                    exact hp ⟨x, hxJ⟩ ⟨y, hyJ⟩ hxy
                  · simp only [σ, dif_pos hxJ, dif_neg hyJ]
                    have hyU : y ∈ U := (hU_iff y).mpr ⟨hyV, hyJ⟩
                    exact (hτ1 y hyU).2.2.1 ⟨x, hxJ⟩ hxy
                  · simp only [σ, dif_neg hxJ, dif_pos hyJ]
                    have hxU : x ∈ U := (hU_iff x).mpr ⟨hxV, hxJ⟩
                    exact (hτ1 x hxU).2.2.2 ⟨y, hyJ⟩ hxy
                  · simp only [σ, dif_neg hxJ, dif_neg hyJ]
                    exact hτ3 x ((hU_iff x).mpr ⟨hxV, hxJ⟩) y ((hU_iff y).mpr ⟨hyV, hyJ⟩) hxy
                · intro j
                  simp only [σ, dif_pos j.property]
              rcases forest_witness hapos hF (Lprof ρ) hnotU with ⟨Sρ, hSρ_sub, hSρ_card, hSρ_not⟩
              refine ⟨Sρ, hSρ_sub, le_trans hSρ_card ?_, fun _ => hSρ_not⟩
              rw [← hbound_eq bm]
              exact hbound_mono bm hbm_le
            · exact ⟨∅, Finset.empty_subset U, Nat.zero_le _, fun h => absurd h hp⟩
          let SOf : Prof → Finset (Finset (Fin n)) := fun ρ => Classical.choose (hprof_witness ρ)
          have hSOf_spec : ∀ ρ : Prof,
              SOf ρ ⊆ U ∧ (SOf ρ).card ≤ bound a B ∧
              (profOk ρ → ¬ ValidFrom (2 ^ bm) (SOf ρ) (Lprof ρ) (0, fun _ => false)) :=
            fun ρ => Classical.choose_spec (hprof_witness ρ)
          let Sω := Finset.univ.biUnion SOf
          refine ⟨Sω, ?_, ?_, ?_⟩
          · rw [Finset.biUnion_subset]
            intro ρ _
            exact (hSOf_spec ρ).1
          · calc Sω.card ≤ Finset.univ.sum (fun ρ : Prof => (SOf ρ).card) := Finset.card_biUnion_le
              _ ≤ Finset.univ.sum (fun _ : Prof => bound a B) :=
                  Finset.sum_le_sum fun ρ _ => (hSOf_spec ρ).2.1
              _ = Fintype.card Prof * bound a B := by simp
              _ = (2 ^ bm) ^ J.card * bound a B := by
                  simp [Prof, Fintype.card_fun, Fintype.card_coe]
              _ ≤ (2 ^ B) ^ J.card * bound a B := by
                  apply Nat.mul_le_mul_right
                  exact Nat.pow_le_pow_left (Nat.pow_le_pow_right (by omega) hbm_le) J.card
          · intro b hb hnotV hfeasS
            have hle_bm : b ≤ bm := hbm_max b hb hnotV
            have hfeas_bm : feas (J ∪ Sω) bm ω := hfeas_mono_b hle_bm hfeasS
            rcases hfeas_bm with ⟨σ, hσ1, hσ2, hσ3⟩
            let ρ : Prof := fun j => ⟨(σ j.val).1, (hσ1 j.val (Finset.mem_union_left _ j.property)).1⟩
            have hp : profOk ρ := by
              intro j1 j2 h12
              have hle := hσ2 j1.val (Finset.mem_union_left _ j1.property)
                j2.val (Finset.mem_union_left _ j2.property) h12
              have h1 : ((ρ j1).val, ω j1) = σ j1.val := Prod.ext rfl (hσ3 j1).symm
              have h2 : ((ρ j2).val, ω j2) = σ j2.val := Prod.ext rfl (hσ3 j2).symm
              rw [h1, h2]; exact hle
            apply (hSOf_spec ρ).2.2 hp
            have hSρ_sub : SOf ρ ⊆ J ∪ Sω :=
              Finset.Subset.trans (Finset.subset_biUnion_of_mem SOf (Finset.mem_univ ρ)) Finset.subset_union_right
            refine ⟨σ, ?_, fun x _ => ?_, fun x hx y hy => hσ2 x (hSρ_sub hx) y (hSρ_sub hy)⟩
            · intro x hx
              have hxJS := hSρ_sub hx
              refine ⟨(hσ1 x hxJS).1, (hσ1 x hxJS).2, fun j hjx => ?_, fun j hxj => ?_⟩
              · have h1 : ((ρ j).val, ω j) = σ j.val := Prod.ext rfl (hσ3 j).symm
                rw [h1]
                exact hσ2 j.val (Finset.mem_union_left _ j.property) x hxJS hjx
              · have h1 : ((ρ j).val, ω j) = σ j.val := Prod.ext rfl (hσ3 j).symm
                rw [h1]
                exact hσ2 x hxJS j.val (Finset.mem_union_left _ j.property) hxj
            · rcases Nat.eq_zero_or_pos (σ x).1 with h0 | hpos
              · exact Or.inr ⟨h0.symm, fun _ h => by cases h⟩
              · exact Or.inl hpos
        · -- Some j ∈ J fails ok j (ω j), so Sω = ∅ already fails on J
          push_neg at hokJ
          rcases hokJ with ⟨j0, hj0_not⟩
          refine ⟨∅, Finset.empty_subset U, Nat.zero_le _, ?_⟩
          intro b _ _ ⟨σ, hσ1, _, hσ3⟩
          have hok0 := (hσ1 j0.val (Finset.mem_union_left _ j0.property)).2
          rw [hσ3 j0] at hok0
          exact hj0_not hok0
      · -- ω succeeds for all b ≤ B
        push_neg at hfail
        exact ⟨∅, Finset.empty_subset U, Nat.zero_le _, fun b hb hnot => absurd (hfail b hb) hnot⟩
    -- Union S_ω over all ω : words
    let SW : words → Finset (Finset (Fin n)) := fun ω => Classical.choose (hfor_word ω)
    have hSW_spec : ∀ ω : words,
        SW ω ⊆ U ∧ (SW ω).card ≤ (2 ^ B) ^ J.card * bound a B ∧
        ∀ b ≤ B, ¬ feas V b ω → ¬ feas (J ∪ SW ω) b ω :=
      fun ω => Classical.choose_spec (hfor_word ω)
    let S := J ∪ Finset.univ.biUnion SW
    have hJS : J ⊆ S := Finset.subset_union_left
    have hSV : S ⊆ V := by
      apply Finset.union_subset hJV
      rw [Finset.biUnion_subset]
      intro ω _ x hx
      exact ((hU_iff x).mp ((hSW_spec ω).1 hx)).1
    refine ⟨S, hJS, hSV, ?_, fun b hb extra => ?_⟩
    · calc S.card ≤ J.card + (Finset.univ.biUnion SW).card := Finset.card_union_le _ _
        _ ≤ J.card + Finset.univ.sum (fun ω : words => (SW ω).card) :=
            Nat.add_le_add_left Finset.card_biUnion_le _
        _ ≤ J.card + Finset.univ.sum (fun _ : words => (2 ^ B) ^ J.card * bound a B) :=
            Nat.add_le_add_left (Finset.sum_le_sum fun ω _ => (hSW_spec ω).2.1) _
        _ = J.card + Fintype.card words * ((2 ^ B) ^ J.card * bound a B) := by simp
        _ = J.card + (2 ^ a) ^ J.card * ((2 ^ B) ^ J.card * bound a B) := by
            simp [words, Fintype.card_fun, Fintype.card_coe]
        _ = J.card + K ^ J.card * bound a B := by
            rw [hK_eq, pow_add, mul_pow, mul_assoc]
    · rw [hfit_iff V hJV b extra, hfit_iff S hJS b extra]
      constructor
      · rintro ⟨ω, hex, hf⟩
        exact ⟨ω, hex, hfeas_sub hSV hf⟩
      · rintro ⟨ω, hex, hfS⟩
        refine ⟨ω, hex, ?_⟩
        by_contra hnotV
        have hsubω : J ∪ SW ω ⊆ S :=
          Finset.union_subset_union_right (Finset.subset_biUnion_of_mem SW (Finset.mem_univ ω))
        exact (hSW_spec ω).2.2 b hb hnotV (hfeas_sub hsubω hfS)

private lemma raw_congr_dec {n : ℕ} (x : Finset (Fin n))
    (d1 d2 : ∀ i : Fin n, Decidable (i ∈ x)) :
    (List.ofFn (fun i : Fin n => @decide (i ∈ x) (d1 i)) ++ [false, true]) =
    (List.ofFn (fun i : Fin n => @decide (i ∈ x) (d2 i)) ++ [false, true]) := by
  have hd : d1 = d2 := funext fun i => Subsingleton.elim _ _
  rw [hd]

private lemma main_aux :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    let bound := fun (a b : Nat) =>
      let F := Nat.factorial a
      let H := (Finset.range (a+1)).sum (fun j => F / Nat.factorial (a-j))
      if a = 0 then 1 else H * (Finset.range (2^b)).sum (fun j => F^j)
    let forest := fun (n : Nat) (V : Finset (Finset (Fin n))) =>
      ∀ x ∈ V, ∀ y ∈ V, ∀ z ∈ V, y ⊆ x → z ⊆ x → y ⊆ z ∨ z ⊆ y
    let raw := fun (n : Nat) (x : Finset (Fin n)) =>
      List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false,true]
    ∀ (n a B : Nat) (V J : Finset (Finset (Fin n)))
        (ok : Finset (Fin n) → (Fin a → Bool) → Prop), J ⊆ V → forest n (V \ J) →
      let words := {x : Finset (Fin n) // x ∈ J} → Fin a → Bool
      let fit := fun (S : Finset (Finset (Fin n))) (b : Nat) (extra : words → Prop) =>
        ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin a → Nat),
          PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
          C.output < n+2+C.size ∧ PEqualNP.NotBracket.notCount C ≤ b ∧
          (∀ i, tap i < n+2+C.size) ∧
          (∀ x ∈ S, ok x (fun i => (C.wires (raw n x)).getD (tap i) false)) ∧
          extra (fun j i => (C.wires (raw n j.val)).getD (tap i) false)
      let K := if a = 0 then 1 else 2^(a+B)
      ∃ S : Finset (Finset (Fin n)), J ⊆ S ∧ S ⊆ V ∧
        S.card ≤ J.card + K^J.card * bound a B ∧
        ∀ b ≤ B, ∀ extra : words → Prop, fit V b extra ↔ fit S b extra := by
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  intro bound forest raw n a B V J ok hJV hF words fit K
  have hU_iff : ∀ x, x ∈ V \ J ↔ x ∈ V ∧ x ∉ J := fun x => Finset.mem_sdiff
  have hraw_eq : ∀ x : Finset (Fin n), raw n x = rawStd n x := fun x =>
    raw_congr_dec x (fun i => Classical.propDecidable (i ∈ x))
      (fun i => @Finset.decidableMem (Fin n) (instDecidableEqFin n) i x)
  rcases main_core n a B V J (V \ J) ok hJV hU_iff hF with ⟨S, hJS, hSV, hcard, hiff⟩
  have hcard' : S.card ≤ J.card + K ^ J.card * bound a B := by
    dsimp only [K, bound]
    by_cases ha0 : a = 0
    · simp only [if_pos ha0] at hcard ⊢; exact hcard
    · simp only [if_neg ha0] at hcard ⊢; exact hcard
  refine ⟨S, hJS, hSV, hcard', fun b hb extra => ?_⟩
  have hfit_eq : ∀ T : Finset (Finset (Fin n)),
      fit T b extra ↔
        ∃ (C : Circuit) (tap : Fin a → ℕ),
          FanInTwo C ∧ ReadsBack (n + 2) C ∧
          C.output < n + 2 + C.size ∧ notCount C ≤ b ∧
          (∀ i, tap i < n + 2 + C.size) ∧
          (∀ x ∈ T, ok x (fun i => (C.wires (rawStd n x)).getD (tap i) false)) ∧
          extra (fun j i => (C.wires (rawStd n j.val)).getD (tap i) false) := by
    intro T
    dsimp only [fit]
    simp_rw [hraw_eq]
  rw [hfit_eq V, hfit_eq S]
  exact hiff b hb extra

end PEqualNP.Outside.L_lib_1365_aux

theorem PEqualNP.Outside.L_lib_1365 :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    let bound := fun (a b : Nat) =>
      let F := Nat.factorial a
      let H := (Finset.range (a+1)).sum (fun j => F / Nat.factorial (a-j))
      if a = 0 then 1 else H * (Finset.range (2^b)).sum (fun j => F^j)
    let forest := fun (n : Nat) (V : Finset (Finset (Fin n))) =>
      ∀ x ∈ V, ∀ y ∈ V, ∀ z ∈ V, y ⊆ x → z ⊆ x → y ⊆ z ∨ z ⊆ y
    let raw := fun (n : Nat) (x : Finset (Fin n)) =>
      List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false,true]
    ∀ (n a B : Nat) (V J : Finset (Finset (Fin n)))
        (ok : Finset (Fin n) → (Fin a → Bool) → Prop), J ⊆ V → forest n (V \ J) →
      let words := {x : Finset (Fin n) // x ∈ J} → Fin a → Bool
      let fit := fun (S : Finset (Finset (Fin n))) (b : Nat) (extra : words → Prop) =>
        ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin a → Nat),
          PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
          C.output < n+2+C.size ∧ PEqualNP.NotBracket.notCount C ≤ b ∧
          (∀ i, tap i < n+2+C.size) ∧
          (∀ x ∈ S, ok x (fun i => (C.wires (raw n x)).getD (tap i) false)) ∧
          extra (fun j i => (C.wires (raw n j.val)).getD (tap i) false)
      let K := if a = 0 then 1 else 2^(a+B)
      ∃ S : Finset (Finset (Fin n)), J ⊆ S ∧ S ⊆ V ∧
        S.card ≤ J.card + K^J.card * bound a B ∧
        ∀ b ≤ B, ∀ extra : words → Prop, fit V b extra ↔ fit S b extra := by
  exact PEqualNP.Outside.L_lib_1365_aux.main_aux
