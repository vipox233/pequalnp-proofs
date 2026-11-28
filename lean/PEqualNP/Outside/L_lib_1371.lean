import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1371_aux

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
      push Not at hno
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
-- Part 2: Binary head-bit helpers, rawStd, and exact size realization
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

private def wordsStd {n a : ℕ} (mask : Fin m → Finset (Fin n)) (C : Circuit) (tap : Fin a → ℕ) (t : Fin m) :
    Finset (Fin a) :=
  @Finset.filter (Fin a) (fun i => (C.wires (rawStd n (mask t))).getD (tap i) false = true)
    (fun i => instDecidableEqBool _ _) Finset.univ

private lemma realize_ranked {n m a h : ℕ} (mask : Fin m → Finset (Fin n))
    (rk : Fin m → ℕ) (wd : Fin m → Finset (Fin a))
    (hrk_lt : ∀ t, rk t < 2 ^ h)
    (hmono : ∀ t u, mask t ⊆ mask u → rk t < rk u ∨ (rk t = rk u ∧ wd t ⊆ wd u)) :
    ∃ (C : Circuit) (tap : Fin a → ℕ),
      FanInTwo C ∧ ReadsBack (n + 2) C ∧ C.output < n + 2 + C.size ∧
      (∀ i, tap i < n + 2 + C.size) ∧ notCount C ≤ h ∧ C.size ≤ m * (n + 2 * h + a) + h ∧
      ∀ t, wordsStd mask C tap t = wd t := by
  have hmono_lvl : ∀ i k : Fin m, mask i ⊆ mask k → rk i ≤ rk k := by
    intro i k hsub
    rcases hmono i k hsub with hlt | ⟨heq, _⟩ <;> omega
  have hmono_eq : ∀ i k : Fin m, mask i ⊆ mask k → rk i = rk k → wd i ⊆ wd k := by
    intro i k hsub heq
    rcases hmono i k hsub with hlt | ⟨_, hsubw⟩
    · omega
    · exact hsubw
  -- Stage 0: mask indicators
  have hstage0 : ∀ (p : ℕ) (hp : p ≤ m),
      ∃ (Bp : Builder n) (ind0 : Fin p → ℕ),
        (∀ i, ind0 i < n + 2 + Bp.gates.length) ∧
        Bp.nots = 0 ∧ Bp.monos ≤ p * n ∧
        ∀ (k : Fin m) (i : Fin p),
          Bp.eval (rawStd n (mask k)) (ind0 i) = decide (mask ⟨i.val, by have := i.isLt; omega⟩ ⊆ mask k) := by
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
      let ws : List ℕ := ((List.finRange n).filter (fun j => decide (j ∈ mask ip))).map Fin.val
      have hws_len : ws.length ≤ n := by
        calc ws.length = ((List.finRange n).filter (fun j => decide (j ∈ mask ip))).length := by simp [ws]
          _ ≤ (List.finRange n).length := List.length_filter_le _ _
          _ = n := List.length_finRange
      have hws_lt : ∀ w ∈ ws, w < n + 2 + Bp.gates.length := by
        intro w hw; rcases List.mem_map.mp hw with ⟨j, _, rfl⟩; omega
      rcases exists_and_list ws Bp hws_lt with ⟨Bp', outp, hEp, hltp, hnp, hmp, hevp⟩
      let ind' : Fin (p + 1) → ℕ := fun i => if hi : i.val < p then ind0 ⟨i.val, hi⟩ else outp
      refine ⟨Bp', ind', ?_, by rw [hnp, hn0], ?_, ?_⟩
      · intro i; dsimp only [ind']; split_ifs with hi
        · have := hlt0 ⟨i.val, hi⟩; have := hEp.1; omega
        · exact hltp
      · have hmul : (p + 1) * n = p * n + n := by ring
        omega
      · intro k i
        have hk := rawStd_spec n (mask k)
        dsimp only [ind']; split_ifs with hi
        · rw [hEp.2 (rawStd n (mask k)) hk.1 _ (hlt0 ⟨i.val, hi⟩), hev0 k ⟨i.val, hi⟩]
        · have hip : (⟨i.val, by omega⟩ : Fin m) = ip := by ext; dsimp [ip]; omega
          rw [hip, hevp (rawStd n (mask k)) hk.1 hk.2.2.1, Bool.eq_iff_iff, decide_eq_true_eq]
          simp only [ws, List.all_eq_true, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
            decide_eq_true_eq]
          constructor
          · intro hall j hj
            have hval := hall j.val ⟨j, hj, rfl⟩
            rw [Bp.eval_inp (rawStd n (mask k)) hk.1 j.val (by omega), hk.2.2.2 j, decide_eq_true_eq] at hval
            exact hval
          · rintro hsub w ⟨j, hj, rfl⟩
            rw [Bp.eval_inp (rawStd n (mask k)) hk.1 j.val (by omega), hk.2.2.2 j, decide_eq_true_eq]
            exact hsub hj
  rcases hstage0 m le_rfl with ⟨B0, ind0, hlt0, hn0, hm0, hev0⟩
  -- Stages d = 0 .. h
  have hstages : ∀ d ≤ h,
      ∃ (Bd : Builder n) (ind : Fin m → ℕ),
        (∀ i, ind i < n + 2 + Bd.gates.length) ∧
        Bd.nots = d ∧ Bd.monos ≤ m * n + 2 * m * d ∧
        ∀ (k i : Fin m),
          Bd.eval (rawStd n (mask k)) (ind i) =
            decide (mask i ⊆ mask k ∧ rk i / 2 ^ (h - d) = rk k / 2 ^ (h - d)) := by
    intro d
    induction d with
    | zero =>
      intro _
      refine ⟨B0, ind0, hlt0, hn0, by simpa using hm0, fun k i => ?_⟩
      rw [hev0 k i]
      have h1 : rk i / 2 ^ h = 0 := Nat.div_eq_of_lt (hrk_lt i)
      have h2 : rk k / 2 ^ h = 0 := Nat.div_eq_of_lt (hrk_lt k)
      simp [h1, h2]
    | succ d ih =>
      intro hd
      rcases ih (by omega) with ⟨Bd, ind, hltd, hnd, hmd, hevd⟩
      set s := h - 1 - d
      have hs1 : h - d = s + 1 := by omega
      have hs0 : h - (d + 1) = s := by omega
      let posList : List ℕ := ((List.finRange m).filter (fun i => bitAt (rk i) s)).map ind
      have hpos_len : posList.length ≤ m := by
        calc posList.length = ((List.finRange m).filter (fun i => bitAt (rk i) s)).length := by simp [posList]
          _ ≤ (List.finRange m).length := List.length_filter_le _ _
          _ = m := List.length_finRange
      have hpos_lt : ∀ w ∈ posList, w < n + 2 + Bd.gates.length := by
        intro w hw; rcases List.mem_map.mp hw with ⟨i, _, rfl⟩; exact hltd i
      rcases exists_or_list posList Bd hpos_lt with ⟨Bor, inW, hEor, hltIn, hnOr, hmOr, hevOr⟩
      have hinW_val : ∀ k : Fin m, Bor.eval (rawStd n (mask k)) inW = bitAt (rk k) s := by
        intro k
        have hk := rawStd_spec n (mask k)
        rw [hevOr (rawStd n (mask k)) hk.1 hk.2.1, Bool.eq_iff_iff]
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
      have hnot_val : ∀ k : Fin m, rNot.1.eval (rawStd n (mask k)) rNot.2 = !(bitAt (rk k) s) := by
        intro k
        rw [hsNot.2.2.2.2 (rawStd n (mask k)) (rawStd_spec n (mask k)).1, hinW_val k]
      have hupd : ∀ (p : ℕ) (hp : p ≤ m),
          ∃ (Bp : Builder n) (ind' : Fin p → ℕ),
            Extends rNot.1 Bp ∧ (∀ i, ind' i < n + 2 + Bp.gates.length) ∧
            Bp.nots = rNot.1.nots ∧ Bp.monos ≤ rNot.1.monos + p ∧
            ∀ (k : Fin m) (i : Fin p),
              let im : Fin m := ⟨i.val, by have := i.isLt; omega⟩
              Bp.eval (rawStd n (mask k)) (ind' i) =
                decide (mask im ⊆ mask k ∧ rk im / 2 ^ s = rk k / 2 ^ s) := by
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
          by_cases hbit : bitAt (rk ip) s = false
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
              have hk := rawStd_spec n (mask k)
              dsimp only [ind'']; split_ifs with hi
              · rw [hsA.1.2 (rawStd n (mask k)) hk.1 _ (hltp ⟨i.val, hi⟩)]
                exact hevp k ⟨i.val, hi⟩
              · have hip : (⟨i.val, by omega⟩ : Fin m) = ip := by ext; dsimp [ip]; omega
                rw [hip, hsA.2.2.2.2 (rawStd n (mask k)) hk.1, (hEnot.trans hEp).2 (rawStd n (mask k)) hk.1 _ (hltd ip),
                  hEp.2 (rawStd n (mask k)) hk.1 _ hsNot.2.1, hevd k ip, hnot_val k, hs1, Bool.eq_iff_iff]
                simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
                constructor
                · rintro ⟨⟨hsub, hpref⟩, hbk0⟩
                  exact ⟨hsub, prefix_step_eq (hmono_lvl ip k hsub) hpref (fun _ => hbk0)⟩
                · rintro ⟨hsub, hdiv⟩
                  have hpref : rk ip / 2 ^ (s + 1) = rk k / 2 ^ (s + 1) := by
                    rw [pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hdiv]
                  have hbk0 : bitAt (rk k) s = false := by
                    unfold bitAt at hbit ⊢; rw [← hdiv]; exact hbit
                  exact ⟨⟨hsub, hpref⟩, hbk0⟩
          · have hbit1 : bitAt (rk ip) s = true := Bool.eq_true_of_not_eq_false hbit
            let ind'' : Fin (p + 1) → ℕ := fun i => if hi : i.val < p then ind' ⟨i.val, hi⟩ else ind ip
            refine ⟨Bp, ind'', hEp, ?_, hnp, by omega, ?_⟩
            · intro i; dsimp only [ind'']; split_ifs with hi
              · exact hltp ⟨i.val, hi⟩
              · exact hind_lt
            · intro k i
              have hk := rawStd_spec n (mask k)
              dsimp only [ind'']; split_ifs with hi
              · exact hevp k ⟨i.val, hi⟩
              · have hip : (⟨i.val, by omega⟩ : Fin m) = ip := by ext; dsimp [ip]; omega
                rw [hip, (hEnot.trans hEp).2 (rawStd n (mask k)) hk.1 _ (hltd ip), hevd k ip, hs1, Bool.eq_iff_iff]
                simp only [decide_eq_true_eq]
                constructor
                · rintro ⟨hsub, hpref⟩
                  exact ⟨hsub, prefix_step_eq (hmono_lvl ip k hsub) hpref (fun h => by rw [hbit1] at h; cases h)⟩
                · rintro ⟨hsub, hdiv⟩
                  refine ⟨hsub, ?_⟩
                  rw [pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hdiv]
      rcases hupd m le_rfl with ⟨Bnext, indNext, _, hltNext, hnNext, hmNext, hevNext⟩
      refine ⟨Bnext, indNext, hltNext, ?_, ?_, fun k i => ?_⟩
      · rw [hnNext, hsNot.2.2.1, hnOr, hnd]
      · have hm_not : rNot.1.monos = Bor.monos := hsNot.2.2.2.1
        have hmul : 2 * m * (d + 1) = 2 * m * d + m + m := by ring
        omega
      · rw [hs0]; exact hevNext k i
  rcases hstages h le_rfl with ⟨Br, indR, hltr, hnr, hmr, hevr⟩
  -- Final stage: taps
  have htaps : ∀ (p : ℕ) (hp : p ≤ a),
      ∃ (Bp : Builder n) (tap : Fin p → ℕ),
        Extends Br Bp ∧ (∀ q, tap q < n + 2 + Bp.gates.length) ∧
        Bp.nots = Br.nots ∧ Bp.monos ≤ Br.monos + p * m ∧
        ∀ (k : Fin m) (q : Fin p),
          Bp.eval (rawStd n (mask k)) (tap q) = decide ((⟨q.val, by have := q.isLt; omega⟩ : Fin a) ∈ wd k) := by
    intro p
    induction p with
    | zero =>
      intro _
      exact ⟨Br, fun q => Fin.elim0 q, Extends.refl Br, fun q => Fin.elim0 q, rfl, by simp, fun _ q => Fin.elim0 q⟩
    | succ p ih =>
      intro hp
      rcases ih (by omega) with ⟨Bp, tap, hEp, hltp, hnp, hmp, hevp⟩
      let qp : Fin a := ⟨p, by omega⟩
      let ws : List ℕ := ((List.finRange m).filter (fun i => decide (qp ∈ wd i))).map indR
      have hws_len : ws.length ≤ m := by
        calc ws.length = ((List.finRange m).filter (fun i => decide (qp ∈ wd i))).length := by simp [ws]
          _ ≤ (List.finRange m).length := List.length_filter_le _ _
          _ = m := List.length_finRange
      have hws_lt : ∀ w ∈ ws, w < n + 2 + Bp.gates.length := by
        intro w hw; rcases List.mem_map.mp hw with ⟨i, _, rfl⟩
        have := hltr i; have := hEp.1; omega
      rcases exists_or_list ws Bp hws_lt with ⟨Bp', outp, hE1, hlt1, hn1, hm1, hev1⟩
      let tap' : Fin (p + 1) → ℕ := fun q => if hq : q.val < p then tap ⟨q.val, hq⟩ else outp
      refine ⟨Bp', tap', hEp.trans hE1, ?_, by rw [hn1, hnp], ?_, ?_⟩
      · intro q; dsimp only [tap']; split_ifs with hq
        · have := hltp ⟨q.val, hq⟩; have := hE1.1; omega
        · exact hlt1
      · have hmul : (p + 1) * m = p * m + m := by ring
        omega
      · intro k q
        have hk := rawStd_spec n (mask k)
        dsimp only [tap']; split_ifs with hq
        · rw [hE1.2 (rawStd n (mask k)) hk.1 _ (hltp ⟨q.val, hq⟩)]
          exact hevp k ⟨q.val, hq⟩
        · have hqp : (⟨q.val, by omega⟩ : Fin a) = qp := by ext; dsimp [qp]; omega
          rw [hqp, hev1 (rawStd n (mask k)) hk.1 hk.2.1, Bool.eq_iff_iff, decide_eq_true_eq]
          simp only [ws, List.any_eq_true, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
            decide_eq_true_eq]
          constructor
          · rintro ⟨w, ⟨i, hai, rfl⟩, hev⟩
            rw [hEp.2 (rawStd n (mask k)) hk.1 _ (hltr i), hevr k i, Nat.sub_self, pow_zero,
              Nat.div_one, Nat.div_one, decide_eq_true_eq] at hev
            exact hmono_eq i k hev.1 hev.2 hai
          · intro hak
            refine ⟨indR k, ⟨k, hak, rfl⟩, ?_⟩
            rw [hEp.2 (rawStd n (mask k)) hk.1 _ (hltr k), hevr k k, decide_eq_true_eq]
            exact ⟨Finset.Subset.refl _, rfl⟩
  rcases htaps a le_rfl with ⟨Bfin, tap, _, hltFin, hnFin, hmFin, hevFin⟩
  refine ⟨Bfin.toCircuit 0, tap, Bfin.toCircuit_fanInTwo 0, Bfin.rb,
    by dsimp [Builder.toCircuit]; omega, hltFin,
    by rw [← Bfin.nots_eq_notCount 0, hnFin, hnr], ?_, ?_⟩
  · change Bfin.gates.length ≤ m * (n + 2 * h + a) + h
    rw [Bfin.gates_len_eq, hnFin, hnr]
    have hmul : m * (n + 2 * h + a) = m * n + 2 * m * h + a * m := by ring
    omega
  · intro t
    ext q
    simp only [wordsStd, Finset.mem_filter, Finset.mem_univ, true_and]
    change Bfin.eval (rawStd n (mask t)) (tap q) = true ↔ q ∈ wd t
    rw [hevFin t q, decide_eq_true_eq]

-- =========================================================================
-- Part 3: Rank compression to Fin q
-- =========================================================================

private lemma log2_limit_ge (L : ℕ) (hL : 1 ≤ L) : L ≤ 2 ^ Nat.log2 (2 * L - 1) := by
  have hne : 2 * L - 1 ≠ 0 := by omega
  have hlt : 2 * L - 1 < 2 ^ (Nat.log2 (2 * L - 1) + 1) := Nat.lt_log2_self
  rw [pow_succ] at hlt
  omega

private lemma q_eq_min_pow (b L : ℕ) (hL : 1 ≤ L) :
    let h := min b (Nat.log2 (2 * L - 1))
    min (2 ^ h) L = min (2 ^ b) L := by
  intro h
  by_cases hle : b ≤ Nat.log2 (2 * L - 1)
  · have hh : h = b := Nat.min_eq_left hle
    rw [hh]
  · have hh : h = Nat.log2 (2 * L - 1) := Nat.min_eq_right (by omega)
    have h1 : L ≤ 2 ^ h := by rw [hh]; exact log2_limit_ge L hL
    have h2 : L ≤ 2 ^ b := le_trans h1 (Nat.pow_le_pow_right (by omega) (by omega))
    rw [Nat.min_eq_right h1, Nat.min_eq_right h2]

private lemma compress_ranks {n m a b : ℕ} (mask : Fin m → Finset (Fin n))
    (r0 : Fin m → ℕ) (w0 : Fin m → Finset (Fin a))
    (hr0_lt : ∀ t, r0 t < 2 ^ b)
    (hmono : ∀ t u, mask t ⊆ mask u → r0 t < r0 u ∨ (r0 t = r0 u ∧ w0 t ⊆ w0 u)) :
    let limit := max 1 (min m (n + 1))
    let h := min b (Nat.log2 (2 * limit - 1))
    let q := min (2 ^ h) limit
    ∃ r : Fin m → Fin q,
      ∀ t u, mask t ⊆ mask u → (r t).val < (r u).val ∨ (r t = r u ∧ w0 t ⊆ w0 u) := by
  intro limit h q
  have hlim_pos : 1 ≤ limit := le_max_left _ _
  have hq_eq : q = min (2 ^ b) limit := q_eq_min_pow b limit hlim_pos
  -- Build compressed rank dp : Fin m → ℕ by strong induction on r0 t
  have hbuild : ∀ K : ℕ, ∃ dp : Fin m → ℕ,
      (∀ t, r0 t < K →
        (∀ u, mask u ⊆ mask t → r0 u < r0 t → dp u + 1 ≤ dp t) ∧
        (dp t ≤ r0 t) ∧
        (dp t ≤ (mask t).card) ∧
        (dp t < (Finset.univ.filter (fun u : Fin m => r0 u ≤ r0 t)).card) ∧
        (∀ u, mask u ⊆ mask t → r0 u = r0 t → dp u ≤ dp t)) := by
    intro K
    induction K with
    | zero =>
      exact ⟨fun _ => 0, fun _ ht => by omega⟩
    | succ K ih =>
      rcases ih with ⟨dp, hdp⟩
      let next : Fin m → ℕ := fun t =>
        if r0 t < K then dp t
        else
          let P := Finset.univ.filter (fun u : Fin m => mask u ⊆ mask t ∧ r0 u < r0 t)
          if hP : P.Nonempty then P.sup' hP (fun u => dp u + 1) else 0
      have hnext_lt : ∀ u, r0 u < K → next u = dp u := fun u hu => by simp only [next, if_pos hu]
      refine ⟨next, fun t ht => ?_⟩
      by_cases htk : r0 t < K
      · have h1 := hdp t htk
        rw [hnext_lt t htk]
        refine ⟨fun u hsub hlt => ?_, h1.2.1, h1.2.2.1, h1.2.2.2.1, fun u hsub heq => ?_⟩
        · rw [hnext_lt u (by omega)]; exact h1.1 u hsub hlt
        · rw [hnext_lt u (by omega)]; exact h1.2.2.2.2 u hsub heq
      · have hteq : r0 t = K := by omega
        let P := Finset.univ.filter (fun u : Fin m => mask u ⊆ mask t ∧ r0 u < r0 t)
        have hnt : next t = if hP : P.Nonempty then P.sup' hP (fun u => dp u + 1) else 0 := by
          simp only [next, if_neg htk, P]
        have hstep1 : ∀ u, mask u ⊆ mask t → r0 u < r0 t → next u + 1 ≤ next t := by
          intro u hsub hlt
          rw [hnext_lt u (by omega), hnt]
          have huP : u ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_univ u, hsub, hlt⟩
          rw [dif_pos ⟨u, huP⟩]
          exact Finset.le_sup' (fun v => dp v + 1) huP
        have hstep2 : next t ≤ r0 t := by
          rw [hnt]
          split_ifs with hP
          · apply Finset.sup'_le hP
            intro u huP
            have hlt : r0 u < r0 t := (Finset.mem_filter.mp huP).2.2
            have := (hdp u (by omega)).2.1
            omega
          · exact Nat.zero_le _
        have hstep3 : next t ≤ (mask t).card := by
          rw [hnt]
          split_ifs with hP
          · apply Finset.sup'_le hP
            intro u huP
            rcases (Finset.mem_filter.mp huP).2 with ⟨hsub, hlt⟩
            have hne : mask u ≠ mask t := by
              intro hmeq
              have hrev := hmono t u (by rw [hmeq])
              rcases hrev with hlt' | ⟨heq', _⟩ <;> omega
            have hcard_lt : (mask u).card < (mask t).card :=
              Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
            have := (hdp u (by omega)).2.2.1
            omega
          · exact Nat.zero_le _
        have hstep4 : next t < (Finset.univ.filter (fun u : Fin m => r0 u ≤ r0 t)).card := by
          rw [hnt]
          split_ifs with hP
          · rcases Finset.exists_mem_eq_sup' hP (fun u => dp u + 1) with ⟨u0, hu0P, hsup⟩
            rw [hsup]
            have hlt : r0 u0 < r0 t := (Finset.mem_filter.mp hu0P).2.2
            have hu0_card := (hdp u0 (by omega)).2.2.2.1
            have hssub : Finset.univ.filter (fun v : Fin m => r0 v ≤ r0 u0) ⊂
                Finset.univ.filter (fun v : Fin m => r0 v ≤ r0 t) := by
              rw [Finset.ssubset_iff_subset_ne]
              refine ⟨fun v hv => ?_, fun heq => ?_⟩
              · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢; omega
              · have ht_mem : t ∈ Finset.univ.filter (fun v : Fin m => r0 v ≤ r0 t) := by simp
                rw [← heq] at ht_mem
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht_mem
                omega
            have hclt := Finset.card_lt_card hssub
            omega
          · exact Finset.card_pos.mpr ⟨t, by simp⟩
        have hstep5 : ∀ u, mask u ⊆ mask t → r0 u = r0 t → next u ≤ next t := by
          intro u hsub heq
          have huk : ¬ r0 u < K := by omega
          let Pu := Finset.univ.filter (fun v : Fin m => mask v ⊆ mask u ∧ r0 v < r0 u)
          have hnu : next u = if hPu : Pu.Nonempty then Pu.sup' hPu (fun v => dp v + 1) else 0 := by
            simp only [next, if_neg huk, Pu]
          rw [hnu, hnt]
          split_ifs with hPu hP
          · apply Finset.sup'_le hPu
            intro v hvPu
            rcases (Finset.mem_filter.mp hvPu).2 with ⟨hvu, hlt⟩
            have hvP : v ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_univ v, Finset.Subset.trans hvu hsub, by omega⟩
            exact Finset.le_sup' (fun w => dp w + 1) hvP
          · exfalso
            rcases hPu with ⟨v, hvPu⟩
            rcases (Finset.mem_filter.mp hvPu).2 with ⟨hvu, hlt⟩
            exact hP ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, Finset.Subset.trans hvu hsub, by omega⟩⟩
          · exact Nat.zero_le _
          · exact le_rfl
        exact ⟨hstep1, hstep2, hstep3, hstep4, hstep5⟩
  rcases hbuild (2 ^ b) with ⟨dp, hdp⟩
  have hdp_lt : ∀ t : Fin m, dp t < q := by
    intro t
    have ht := hdp t (hr0_lt t)
    have h1 : dp t < 2 ^ b := lt_of_le_of_lt ht.2.1 (hr0_lt t)
    have h2 : dp t < n + 1 := by
      have hc : (mask t).card ≤ n := by simpa using Finset.card_le_univ (mask t)
      have := ht.2.2.1
      omega
    have h3 : dp t < m := by
      have hc : (Finset.univ.filter (fun u : Fin m => r0 u ≤ r0 t)).card ≤ m := by
        simpa using Finset.card_le_univ (Finset.univ.filter (fun u : Fin m => r0 u ≤ r0 t))
      have := ht.2.2.2.1
      omega
    rw [hq_eq]
    have hlim : min m (n + 1) ≤ limit := le_max_right _ _
    omega
  refine ⟨fun t => ⟨dp t, hdp_lt t⟩, fun t u htu => ?_⟩
  have hu := hdp u (hr0_lt u)
  rcases hmono t u htu with hlt | ⟨heq, hsubw⟩
  · left
    have := hu.1 t htu hlt
    dsimp only; omega
  · have hle : dp t ≤ dp u := hu.2.2.2.2 t htu heq
    rcases lt_or_eq_of_le hle with hlt' | heq'
    · exact Or.inl hlt'
    · exact Or.inr ⟨Fin.ext heq', hsubw⟩

-- =========================================================================
-- Part 4: Flag lattice, join/meet, and Birkhoff implication representation
-- =========================================================================

private noncomputable def flagStd {q a : ℕ} (r : Fin q) (w : Finset (Fin a)) (s : Fin q) (i : Option (Fin a)) : Bool :=
  @decide (s.val < r.val ∨ (s = r ∧ ∃ v, i = some v ∧ v ∈ w)) (Classical.propDecidable _)

private def stBefore {q a : ℕ} (x y : Fin q × Finset (Fin a)) : Prop :=
  x.1.val < y.1.val ∨ (x.1 = y.1 ∧ x.2 ⊆ y.2)

private lemma stBefore_iff_flag {q a : ℕ} (x y : Fin q × Finset (Fin a)) :
    stBefore x y ↔ ∀ s i, flagStd x.1 x.2 s i = true → flagStd y.1 y.2 s i = true := by
  constructor
  · intro hxy s i hx
    simp only [flagStd, decide_eq_true_eq] at hx ⊢
    rcases hxy with hlt | ⟨heq, hsub⟩
    · rcases hx with hs | ⟨rfl, _⟩
      · exact Or.inl (by omega)
      · exact Or.inl hlt
    · rcases hx with hs | ⟨rfl, v, rfl, hv⟩
      · exact Or.inl (by rw [← heq]; exact hs)
      · exact Or.inr ⟨heq, v, rfl, hsub hv⟩
  · intro hflag
    have hle : x.1.val ≤ y.1.val := by
      by_contra hgt
      have h1 : flagStd x.1 x.2 y.1 none = true := by
        simp only [flagStd, decide_eq_true_eq]
        exact Or.inl (by omega)
      have h2 := hflag y.1 none h1
      simp only [flagStd, decide_eq_true_eq] at h2
      rcases h2 with hlt | ⟨_, v, hv, _⟩
      · omega
      · cases hv
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact Or.inl hlt
    · right
      have hr : x.1 = y.1 := Fin.ext heq
      refine ⟨hr, fun v hv => ?_⟩
      have h1 : flagStd x.1 x.2 x.1 (some v) = true := by
        simp [flagStd, hv]
      have h2 := hflag x.1 (some v) h1
      simp only [flagStd, decide_eq_true_eq, hr] at h2
      rcases h2 with hlt | ⟨_, v', hv', hv'y⟩
      · omega
      · cases hv'; exact hv'y

private lemma flagStd_eq_iff {q a : ℕ} (x y : Fin q × Finset (Fin a)) :
    (∀ s i, flagStd x.1 x.2 s i = flagStd y.1 y.2 s i) ↔ x = y := by
  constructor
  · intro h
    have h1 : stBefore x y := (stBefore_iff_flag x y).mpr (fun s i hs => by rw [← h s i]; exact hs)
    have h2 : stBefore y x := (stBefore_iff_flag y x).mpr (fun s i hs => by rw [h s i]; exact hs)
    rcases h1 with hlt1 | ⟨heq1, hsub1⟩ <;> rcases h2 with hlt2 | ⟨_, hsub2⟩
    · omega
    · omega
    · omega
    · exact Prod.ext heq1 (Finset.Subset.antisymm hsub1 hsub2)
  · rintro rfl _ _; rfl

private def stMeet {q a : ℕ} (x y : Fin q × Finset (Fin a)) : Fin q × Finset (Fin a) :=
  if x.1.val < y.1.val then x
  else if y.1.val < x.1.val then y
  else (x.1, x.2 ∩ y.2)

private def stJoin {q a : ℕ} (x y : Fin q × Finset (Fin a)) : Fin q × Finset (Fin a) :=
  if x.1.val < y.1.val then y
  else if y.1.val < x.1.val then x
  else (x.1, x.2 ∪ y.2)

private lemma flagStd_stMeet {q a : ℕ} (x y : Fin q × Finset (Fin a)) (s : Fin q) (i : Option (Fin a)) :
    flagStd (stMeet x y).1 (stMeet x y).2 s i = (flagStd x.1 x.2 s i && flagStd y.1 y.2 s i) := by
  unfold stMeet
  by_cases h1 : x.1.val < y.1.val
  · simp only [if_pos h1]
    have himp : flagStd x.1 x.2 s i = true → flagStd y.1 y.2 s i = true :=
      (stBefore_iff_flag x y).mp (Or.inl h1) s i
    cases hx : flagStd x.1 x.2 s i
    · simp
    · simp [himp hx]
  · by_cases h2 : y.1.val < x.1.val
    · simp only [if_neg h1, if_pos h2]
      have himp : flagStd y.1 y.2 s i = true → flagStd x.1 x.2 s i = true :=
        (stBefore_iff_flag y x).mp (Or.inl h2) s i
      cases hy : flagStd y.1 y.2 s i
      · simp
      · simp [himp hy]
    · simp only [if_neg h1, if_neg h2]
      have heq : x.1 = y.1 := Fin.ext (by omega)
      rw [Bool.eq_iff_iff]
      simp only [Bool.and_eq_true, flagStd, decide_eq_true_eq, heq]
      constructor
      · rintro (hs | ⟨rfl, v, rfl, hv⟩)
        · exact ⟨Or.inl hs, Or.inl hs⟩
        · rcases Finset.mem_inter.mp hv with ⟨hvx, hvy⟩
          exact ⟨Or.inr ⟨rfl, v, rfl, hvx⟩, Or.inr ⟨rfl, v, rfl, hvy⟩⟩
      · rintro ⟨hs1 | ⟨rfl, v, rfl, hvx⟩, hs2 | ⟨_, v', hv', hvy⟩⟩
        · exact Or.inl hs1
        · omega
        · omega
        · cases hv'
          exact Or.inr ⟨rfl, v, rfl, Finset.mem_inter.mpr ⟨hvx, hvy⟩⟩

private lemma flagStd_stJoin {q a : ℕ} (x y : Fin q × Finset (Fin a)) (s : Fin q) (i : Option (Fin a)) :
    flagStd (stJoin x y).1 (stJoin x y).2 s i = (flagStd x.1 x.2 s i || flagStd y.1 y.2 s i) := by
  unfold stJoin
  by_cases h1 : x.1.val < y.1.val
  · simp only [if_pos h1]
    have himp : flagStd x.1 x.2 s i = true → flagStd y.1 y.2 s i = true :=
      (stBefore_iff_flag x y).mp (Or.inl h1) s i
    cases hx : flagStd x.1 x.2 s i
    · simp
    · simp [himp hx]
  · by_cases h2 : y.1.val < x.1.val
    · simp only [if_neg h1, if_pos h2]
      have himp : flagStd y.1 y.2 s i = true → flagStd x.1 x.2 s i = true :=
        (stBefore_iff_flag y x).mp (Or.inl h2) s i
      cases hy : flagStd y.1 y.2 s i
      · simp
      · simp [himp hy]
    · simp only [if_neg h1, if_neg h2]
      have heq : x.1 = y.1 := Fin.ext (by omega)
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, flagStd, decide_eq_true_eq, heq]
      constructor
      · rintro (hs | ⟨rfl, v, rfl, hv⟩)
        · exact Or.inl (Or.inl hs)
        · rcases Finset.mem_union.mp hv with hvx | hvy
          · exact Or.inl (Or.inr ⟨rfl, v, rfl, hvx⟩)
          · exact Or.inr (Or.inr ⟨rfl, v, rfl, hvy⟩)
      · rintro ((hs | ⟨rfl, v, rfl, hvx⟩) | (hs | ⟨rfl, v, rfl, hvy⟩))
        · exact Or.inl hs
        · exact Or.inr ⟨rfl, v, rfl, Finset.mem_union_left _ hvx⟩
        · exact Or.inl hs
        · exact Or.inr ⟨rfl, v, rfl, Finset.mem_union_right _ hvy⟩

private lemma cost_stMeet_stJoin {q a : ℕ} (c : Finset (Fin a) → ℕ)
    (hsub : ∀ U V, c (U ∩ V) + c (U ∪ V) ≤ c U + c V)
    (x y : Fin q × Finset (Fin a)) :
    c (stMeet x y).2 + c (stJoin x y).2 ≤ c x.2 + c y.2 := by
  unfold stMeet stJoin
  by_cases h1 : x.1.val < y.1.val
  · simp only [if_pos h1]; omega
  · by_cases h2 : y.1.val < x.1.val
    · simp only [if_neg h1, if_pos h2]; omega
    · simp only [if_neg h1, if_neg h2]
      exact hsub x.2 y.2

private lemma main_core (n m a b j : ℕ) (mask : Fin m → Finset (Fin n)) (mark : Fin j → Fin m)
    (cost : Fin m → Finset (Fin a) → ℕ)
    (hsub : ∀ t U V, cost t (U ∩ V) + cost t (U ∪ V) ≤ cost t U + cost t V) :
    let limit := max 1 (min m (n + 1))
    let h := min b (Nat.log2 (2 * limit - 1))
    let q := min (2 ^ h) limit
    let node := Sum Bool (Fin j × Fin q × Option (Fin a))
    let valid := fun (C : Circuit) (tap : Fin a → ℕ) =>
      FanInTwo C ∧ ReadsBack (n + 2) C ∧
      C.output < n + 2 + C.size ∧ (∀ i, tap i < n + 2 + C.size) ∧ notCount C ≤ b
    let lossStd := fun C tap => Finset.univ.sum (fun t => cost t (wordsStd mask C tap t))
    ∃ (opt : ℕ) (imp : node → node → Prop),
      (∀ C tap, valid C tap → opt ≤ lossStd C tap) ∧ (∃ C tap, valid C tap ∧ lossStd C tap = opt) ∧
      ∀ W : Fin j → Finset (Fin a),
        let sat := ∃ r : Fin j → Fin q,
          let bit : node → Bool := Sum.elim id
            (fun z => flagStd (r z.1) (W z.1) z.2.1 z.2.2)
          ∀ u v, imp u v → bit u = true → bit v = true
        ((∃ C tap, valid C tap ∧ lossStd C tap = opt ∧ ∀ k, wordsStd mask C tap (mark k) = W k) ↔ sat) ∧
        (sat → ∃ C tap, valid C tap ∧ lossStd C tap = opt ∧ (∀ k, wordsStd mask C tap (mark k) = W k) ∧
          notCount C ≤ h ∧ C.size ≤ m * (n + 2 * h + a) + h) := by
  intro limit h q node valid lossStd
  have hlim_pos : 1 ≤ limit := le_max_left _ _
  have hq_pos : 0 < q := by
    have h1 : 0 < 2 ^ h := Nat.pos_of_ne_zero (by positivity)
    omega
  have hh_le_b : h ≤ b := Nat.min_le_left _ _
  have hq_le_pow : q ≤ 2 ^ h := Nat.min_le_left _ _
  let Assign := Fin m → Fin q × Finset (Fin a)
  let Feas : Assign → Prop := fun A => ∀ t u, mask t ⊆ mask u → stBefore (A t) (A u)
  let aLoss : Assign → ℕ := fun A => Finset.univ.sum (fun t => cost t (A t).2)
  let A0 : Assign := fun _ => (⟨0, hq_pos⟩, ∅)
  have hA0_feas : Feas A0 := fun _ _ _ => Or.inr ⟨rfl, Finset.Subset.refl _⟩
  let feasSet : Finset Assign := Finset.univ.filter Feas
  have hfeas_ne : feasSet.Nonempty := ⟨A0, Finset.mem_filter.mpr ⟨Finset.mem_univ A0, hA0_feas⟩⟩
  rcases Finset.exists_min_image feasSet aLoss hfeas_ne with ⟨Amin, hAmin_mem, hAmin_min⟩
  let opt := aLoss Amin
  have hopt_le : ∀ A : Assign, Feas A → opt ≤ aLoss A := fun A hA =>
    hAmin_min A (Finset.mem_filter.mpr ⟨Finset.mem_univ A, hA⟩)
  let OptSet : Finset Assign := feasSet.filter (fun A => aLoss A = opt)
  have hOpt_mem : ∀ A, A ∈ OptSet ↔ Feas A ∧ aLoss A = opt := by
    intro A; simp [OptSet, feasSet]
  have hOpt_ne : OptSet.Nonempty := ⟨Amin, (hOpt_mem Amin).mpr ⟨(Finset.mem_filter.mp hAmin_mem).2, rfl⟩⟩
  -- Valid circuit -> feasible compressed Assign with same words
  have hcirc_to_assign : ∀ C tap, valid C tap →
      ∃ A : Assign, Feas A ∧ ∀ t, (A t).2 = wordsStd mask C tap t := by
    intro C tap ⟨hfan, hrb, _, htap, hnot⟩
    let r0 : Fin m → ℕ := fun t => 2 ^ notCount C - 1 - notVal n C (rawStd n (mask t))
    let w0 : Fin m → Finset (Fin a) := wordsStd mask C tap
    have hr0_lt : ∀ t, r0 t < 2 ^ b := by
      intro t
      have hlt := notVal_lt n C (rawStd n (mask t))
      have hpow : 2 ^ notCount C ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) hnot
      have hpos : 1 ≤ 2 ^ notCount C := Nat.one_le_pow _ _ (by omega)
      dsimp only [r0]; omega
    have hmono0 : ∀ t u, mask t ⊆ mask u → r0 t < r0 u ∨ (r0 t = r0 u ∧ w0 t ⊆ w0 u) := by
      intro t u htu
      have hle : ∀ v < n + 2, (rawStd n (mask t)).getD v false = true → (rawStd n (mask u)).getD v false = true := by
        intro v hv hval
        by_cases hvn : v < n
        · have ht := (rawStd_spec n (mask t)).2.2.2 ⟨v, hvn⟩
          have hu := (rawStd_spec n (mask u)).2.2.2 ⟨v, hvn⟩
          rw [ht, decide_eq_true_eq] at hval
          rw [hu, decide_eq_true_eq]
          exact htu hval
        · have hv1 : v = n ∨ v = n + 1 := by omega
          rcases hv1 with hveq | hveq
          · rw [hveq, (rawStd_spec n (mask t)).2.1] at hval; cases hval
          · rw [hveq]; exact (rawStd_spec n (mask u)).2.2.1
      have hanti := notVal_anti C hfan hrb (rawStd n (mask t)) (rawStd n (mask u))
        (rawStd_spec n (mask t)).1 (rawStd_spec n (mask u)).1 hle
      have hlt_t := notVal_lt n C (rawStd n (mask t))
      have hlt_u := notVal_lt n C (rawStd n (mask u))
      rcases hanti with hlt | ⟨heq, hmono⟩
      · exact Or.inl (by dsimp only [r0]; omega)
      · right
        refine ⟨by dsimp only [r0]; omega, fun i hi => ?_⟩
        simp only [w0, wordsStd, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        exact hmono (tap i) (htap i) hi
    rcases compress_ranks mask r0 w0 hr0_lt hmono0 with ⟨r, hr_mono⟩
    exact ⟨fun t => (r t, w0 t), hr_mono, fun _ => rfl⟩
  -- Feasible Assign -> valid circuit with notCount ≤ h and size ≤ m*(n+2*h+a)+h
  have hassign_to_circ : ∀ A : Assign, Feas A →
      ∃ C tap, valid C tap ∧ (∀ t, wordsStd mask C tap t = (A t).2) ∧
        notCount C ≤ h ∧ C.size ≤ m * (n + 2 * h + a) + h := by
    intro A hA
    have hrk_lt : ∀ t, (A t).1.val < 2 ^ h := fun t => lt_of_lt_of_le (A t).1.isLt hq_le_pow
    have hmono : ∀ t u, mask t ⊆ mask u → (A t).1.val < (A u).1.val ∨ ((A t).1.val = (A u).1.val ∧ (A t).2 ⊆ (A u).2) := by
      intro t u htu
      rcases hA t u htu with hlt | ⟨heq, hsubw⟩
      · exact Or.inl hlt
      · exact Or.inr ⟨congrArg Fin.val heq, hsubw⟩
    rcases realize_ranked mask (fun t => (A t).1.val) (fun t => (A t).2) hrk_lt hmono with
      ⟨C, tap, hfan, hrb, hout, htap, hnot, hsz, hwds⟩
    exact ⟨C, tap, ⟨hfan, hrb, hout, htap, le_trans hnot hh_le_b⟩, hwds, hnot, hsz⟩
  -- Meet and join on Assign preserve OptSet
  let aMeet : Assign → Assign → Assign := fun A1 A2 t => stMeet (A1 t) (A2 t)
  let aJoin : Assign → Assign → Assign := fun A1 A2 t => stJoin (A1 t) (A2 t)
  have hFeas_meet : ∀ A1 A2, Feas A1 → Feas A2 → Feas (aMeet A1 A2) := by
    intro A1 A2 h1 h2 t u htu
    rw [stBefore_iff_flag]
    intro s i hflag
    dsimp only [aMeet] at hflag ⊢
    rw [flagStd_stMeet] at hflag ⊢
    simp only [Bool.and_eq_true] at hflag ⊢
    exact ⟨(stBefore_iff_flag (A1 t) (A1 u)).mp (h1 t u htu) s i hflag.1,
      (stBefore_iff_flag (A2 t) (A2 u)).mp (h2 t u htu) s i hflag.2⟩
  have hFeas_join : ∀ A1 A2, Feas A1 → Feas A2 → Feas (aJoin A1 A2) := by
    intro A1 A2 h1 h2 t u htu
    rw [stBefore_iff_flag]
    intro s i hflag
    dsimp only [aJoin] at hflag ⊢
    rw [flagStd_stJoin] at hflag ⊢
    simp only [Bool.or_eq_true] at hflag ⊢
    rcases hflag with h | h
    · exact Or.inl ((stBefore_iff_flag (A1 t) (A1 u)).mp (h1 t u htu) s i h)
    · exact Or.inr ((stBefore_iff_flag (A2 t) (A2 u)).mp (h2 t u htu) s i h)
  have hOpt_meet_join : ∀ A1 A2, A1 ∈ OptSet → A2 ∈ OptSet →
      aMeet A1 A2 ∈ OptSet ∧ aJoin A1 A2 ∈ OptSet := by
    intro A1 A2 h1 h2
    rcases (hOpt_mem A1).mp h1 with ⟨hf1, hl1⟩
    rcases (hOpt_mem A2).mp h2 with ⟨hf2, hl2⟩
    have hfm : Feas (aMeet A1 A2) := hFeas_meet A1 A2 hf1 hf2
    have hfj : Feas (aJoin A1 A2) := hFeas_join A1 A2 hf1 hf2
    have hlm : opt ≤ aLoss (aMeet A1 A2) := hopt_le _ hfm
    have hlj : opt ≤ aLoss (aJoin A1 A2) := hopt_le _ hfj
    have hsum : aLoss (aMeet A1 A2) + aLoss (aJoin A1 A2) ≤ aLoss A1 + aLoss A2 := by
      dsimp only [aLoss, aMeet, aJoin]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun t _ => cost_stMeet_stJoin (cost t) (hsub t) (A1 t) (A2 t)
    exact ⟨(hOpt_mem _).mpr ⟨hfm, by omega⟩, (hOpt_mem _).mpr ⟨hfj, by omega⟩⟩
  -- Boundary bit vector of an assignment
  let bBit : Assign → node → Bool := fun A =>
    Sum.elim id (fun z => flagStd (A (mark z.1)).1 (A (mark z.1)).2 z.2.1 z.2.2)
  have hbBit_meet : ∀ A1 A2 u, bBit (aMeet A1 A2) u = (bBit A1 u && bBit A2 u) := by
    intro A1 A2 u
    cases u with
    | inl c => cases c <;> rfl
    | inr z => exact flagStd_stMeet (A1 (mark z.1)) (A2 (mark z.1)) z.2.1 z.2.2
  have hbBit_join : ∀ A1 A2 u, bBit (aJoin A1 A2) u = (bBit A1 u || bBit A2 u) := by
    intro A1 A2 u
    cases u with
    | inl c => cases c <;> rfl
    | inr z => exact flagStd_stJoin (A1 (mark z.1)) (A2 (mark z.1)) z.2.1 z.2.2
  -- Finite nonempty meet & join over subsets of OptSet
  have hfin_meet : ∀ S : Finset Assign, S.Nonempty → S ⊆ OptSet →
      ∃ M ∈ OptSet, ∀ u : node, bBit M u = true ↔ ∀ A ∈ S, bBit A u = true := by
    intro S hne
    induction hne using Finset.Nonempty.cons_induction with
    | singleton A =>
      intro hsubS
      exact ⟨A, hsubS (Finset.mem_singleton_self A), fun u => by simp⟩
    | cons A S' hnot hne' ih =>
      intro hsubS
      rcases ih (fun X hX => hsubS (Finset.mem_cons_of_mem hX)) with ⟨M', hM', hM'b⟩
      have hA : A ∈ OptSet := hsubS (Finset.mem_cons_self A S')
      refine ⟨aMeet A M', (hOpt_meet_join A M' hA hM').1, fun u => ?_⟩
      rw [hbBit_meet, Bool.and_eq_true, hM'b u]
      simp
  have hfin_join : ∀ S : Finset Assign, S.Nonempty → S ⊆ OptSet →
      ∃ J ∈ OptSet, ∀ u : node, bBit J u = true ↔ ∃ A ∈ S, bBit A u = true := by
    intro S hne
    induction hne using Finset.Nonempty.cons_induction with
    | singleton A =>
      intro hsubS
      exact ⟨A, hsubS (Finset.mem_singleton_self A), fun u => by simp⟩
    | cons A S' hnot hne' ih =>
      intro hsubS
      rcases ih (fun X hX => hsubS (Finset.mem_cons_of_mem hX)) with ⟨J', hJ', hJ'b⟩
      have hA : A ∈ OptSet := hsubS (Finset.mem_cons_self A S')
      refine ⟨aJoin A J', (hOpt_meet_join A J' hA hJ').2, fun u => ?_⟩
      rw [hbBit_join, Bool.or_eq_true, hJ'b u]
      simp
  -- Define the implication relation imp
  let imp : node → node → Prop := fun u v => ∀ A ∈ OptSet, bBit A u = true → bBit A v = true
  refine ⟨opt, imp, ?_, ?_, fun W => ?_⟩
  · intro C tap hv
    rcases hcirc_to_assign C tap hv with ⟨A, hA, hw⟩
    have hle := hopt_le A hA
    have heq : aLoss A = lossStd C tap := by
      dsimp only [aLoss, lossStd]
      apply Finset.sum_congr rfl
      intro t _; rw [hw t]
    omega
  · rcases hassign_to_circ Amin (Finset.mem_filter.mp hAmin_mem).2 with ⟨C, tap, hv, hw, _, _⟩
    refine ⟨C, tap, hv, ?_⟩
    dsimp only [lossStd, opt, aLoss]
    apply Finset.sum_congr rfl
    intro t _; rw [hw t]
  · intro sat
    have hsat_to_opt : sat → ∃ A ∈ OptSet, ∀ k, (A (mark k)).2 = W k := by
      rintro ⟨r, hsat⟩
      let bit : node → Bool := Sum.elim id (fun z => flagStd (r z.1) (W z.1) z.2.1 z.2.2)
      let T : Finset node := Finset.univ.filter (fun u => bit u = true)
      have hT_ne : T.Nonempty := ⟨Sum.inl true, by simp [T, bit]⟩
      have hfor_u : ∀ u : node, u ∈ T → ∃ Au ∈ OptSet, bBit Au u = true ∧ ∀ v, bBit Au v = true → bit v = true := by
        intro u huT
        have hbu : bit u = true := (Finset.mem_filter.mp huT).2
        let Su := OptSet.filter (fun A => bBit A u = true)
        have hSu_ne : Su.Nonempty := by
          by_contra hempty
          have hno : ∀ A ∈ OptSet, bBit A u ≠ true := fun A hA hba =>
            hempty ⟨A, Finset.mem_filter.mpr ⟨hA, hba⟩⟩
          have himp_f : imp u (Sum.inl false) := fun A hA hba => absurd hba (hno A hA)
          have hf := hsat u (Sum.inl false) himp_f hbu
          simp [bit] at hf
        rcases hfin_meet Su hSu_ne (Finset.filter_subset _ _) with ⟨Au, hAu, hAub⟩
        refine ⟨Au, hAu, (hAub u).mpr (fun A hA => (Finset.mem_filter.mp hA).2), fun v hv => ?_⟩
        have hall : ∀ A ∈ Su, bBit A v = true := (hAub v).mp hv
        have himp_uv : imp u v := fun A hA hba => hall A (Finset.mem_filter.mpr ⟨hA, hba⟩)
        exact hsat u v himp_uv hbu
      let pick : node → Assign := fun u => if hu : u ∈ T then Classical.choose (hfor_u u hu) else Amin
      have hpick_spec : ∀ u (hu : u ∈ T),
          pick u ∈ OptSet ∧ bBit (pick u) u = true ∧ ∀ v, bBit (pick u) v = true → bit v = true := by
        intro u hu
        simp only [pick, dif_pos hu]
        exact Classical.choose_spec (hfor_u u hu)
      let img : Finset Assign := T.image pick
      have himg_ne : img.Nonempty := hT_ne.image pick
      have himg_sub : img ⊆ OptSet := by
        intro A hA
        rcases Finset.mem_image.mp hA with ⟨u, huT, rfl⟩
        exact (hpick_spec u huT).1
      rcases hfin_join img himg_ne himg_sub with ⟨Astar, hAstar, hAstar_b⟩
      have hbit_eq : ∀ v : node, bBit Astar v = bit v := by
        intro v
        rw [Bool.eq_iff_iff, hAstar_b v]
        constructor
        · rintro ⟨A, hAimg, hAv⟩
          rcases Finset.mem_image.mp hAimg with ⟨u, huT, rfl⟩
          exact (hpick_spec u huT).2.2 v hAv
        · intro hbv
          have hvT : v ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ v, hbv⟩
          exact ⟨pick v, Finset.mem_image_of_mem pick hvT, (hpick_spec v hvT).2.1⟩
      refine ⟨Astar, hAstar, fun k => ?_⟩
      have hpair : Astar (mark k) = (r k, W k) := by
        rw [← flagStd_eq_iff]
        intro s i
        exact hbit_eq (Sum.inr (k, s, i))
      exact congrArg Prod.snd hpair
    constructor
    · constructor
      · rintro ⟨C, tap, hv, hloss, hW⟩
        rcases hcirc_to_assign C tap hv with ⟨A, hA, hw⟩
        have hAloss : aLoss A = opt := by
          rw [← hloss]
          dsimp only [aLoss, lossStd]
          apply Finset.sum_congr rfl
          intro t _; rw [hw t]
        have hAopt : A ∈ OptSet := (hOpt_mem A).mpr ⟨hA, hAloss⟩
        refine ⟨fun k => (A (mark k)).1, fun u v huv hbu => ?_⟩
        have hbeq : ∀ x : node,
            Sum.elim id (fun z : Fin j × Fin q × Option (Fin a) => flagStd (A (mark z.1)).1 (W z.1) z.2.1 z.2.2) x =
              bBit A x := by
          intro x
          cases x with
          | inl c => rfl
          | inr z =>
            dsimp only [bBit, Sum.elim]
            rw [← hW z.1, hw (mark z.1)]
        rw [hbeq u] at hbu
        rw [hbeq v]
        exact huv A hAopt hbu
      · intro hsat
        rcases hsat_to_opt hsat with ⟨A, hAopt, hAW⟩
        rcases (hOpt_mem A).mp hAopt with ⟨hAfeas, hAloss⟩
        rcases hassign_to_circ A hAfeas with ⟨C, tap, hv, hw, _, _⟩
        refine ⟨C, tap, hv, ?_, fun k => by rw [hw (mark k), hAW k]⟩
        rw [← hAloss]
        dsimp only [lossStd, aLoss]
        apply Finset.sum_congr rfl
        intro t _; rw [hw t]
    · intro hsat
      rcases hsat_to_opt hsat with ⟨A, hAopt, hAW⟩
      rcases (hOpt_mem A).mp hAopt with ⟨hAfeas, hAloss⟩
      rcases hassign_to_circ A hAfeas with ⟨C, tap, hv, hw, hnot, hsz⟩
      refine ⟨C, tap, hv, ?_, fun k => by rw [hw (mark k), hAW k], hnot, hsz⟩
      rw [← hAloss]
      dsimp only [lossStd, aLoss]
      apply Finset.sum_congr rfl
      intro t _; rw [hw t]

private lemma raw_eq_rawStd {n : ℕ} (x : Finset (Fin n)) (d : ∀ i : Fin n, Decidable (i ∈ x)) :
    (List.ofFn (fun i : Fin n => @decide (i ∈ x) (d i)) ++ [false, true]) = rawStd n x := by
  unfold rawStd
  have hd : d = (fun i => @Finset.decidableMem (Fin n) (instDecidableEqFin n) i x) :=
    funext fun i => Subsingleton.elim _ _
  rw [hd]

private lemma submod_congr_aux {m a : ℕ} (cost : Fin m → Finset (Fin a) → ℕ)
    (h : ∀ t (U V : Finset (Fin a)) (I S : Finset (Fin a)),
      (∀ x, x ∈ I ↔ x ∈ U ∧ x ∈ V) → (∀ x, x ∈ S ↔ x ∈ U ∨ x ∈ V) →
      cost t I + cost t S ≤ cost t U + cost t V) :
    ∀ t (U V : Finset (Fin a)), cost t (U ∩ V) + cost t (U ∪ V) ≤ cost t U + cost t V :=
  fun t U V => h t U V (U ∩ V) (U ∪ V) (fun _ => Finset.mem_inter) (fun _ => Finset.mem_union)

private lemma main_aux :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    ∀ (n m a b j : Nat) (mask : Fin m → Finset (Fin n)) (mark : Fin j → Fin m)
        (cost : Fin m → Finset (Fin a) → Nat),
      (∀ t U V, cost t (U ∩ V) + cost t (U ∪ V) ≤ cost t U + cost t V) →
      let limit := max 1 (min m (n+1))
      let h := min b (Nat.log2 (2*limit-1))
      let q := min (2^h) limit
      let flag := fun (r : Fin q) (w : Finset (Fin a)) (s : Fin q) (i : Option (Fin a)) =>
        decide (s.val < r.val ∨ (s = r ∧ ∃ v, i = some v ∧ v ∈ w))
      let node := Sum Bool (Fin j × Fin q × Option (Fin a))
      let valid := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin a → Nat) =>
        PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
        C.output < n+2+C.size ∧ (∀ i, tap i < n+2+C.size) ∧ PEqualNP.NotBracket.notCount C ≤ b
      let words := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin a → Nat) (t : Fin m) =>
        Finset.univ.filter (fun i => (C.wires
          (List.ofFn (fun v : Fin n => decide (v ∈ mask t)) ++ [false,true])).getD (tap i) false)
      let loss := fun C tap => Finset.univ.sum (fun t => cost t (words C tap t))
      ∃ (opt : Nat) (imp : node → node → Prop),
        (∀ C tap, valid C tap → opt ≤ loss C tap) ∧ (∃ C tap, valid C tap ∧ loss C tap = opt) ∧
        ∀ W : Fin j → Finset (Fin a),
          let sat := ∃ r : Fin j → Fin q,
            let bit : node → Bool := Sum.elim id
              (fun z => flag (r z.1) (W z.1) z.2.1 z.2.2)
            ∀ u v, imp u v → bit u = true → bit v = true
          ((∃ C tap, valid C tap ∧ loss C tap = opt ∧ ∀ k, words C tap (mark k) = W k) ↔ sat) ∧
          (sat → ∃ C tap, valid C tap ∧ loss C tap = opt ∧ (∀ k, words C tap (mark k) = W k) ∧
            PEqualNP.NotBracket.notCount C ≤ h ∧ C.size ≤ m*(n+2*h+a)+h) := by
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  intro n m a b j mask mark cost hsub limit h q flag node valid words loss
  have hsub' := submod_congr_aux cost (fun t U V I S hI hS => by
    have h1 : I = U ∩ V := by ext x; rw [hI x, Finset.mem_inter]
    have h2 : S = U ∪ V := by ext x; rw [hS x, Finset.mem_union]
    rw [h1, h2]; exact hsub t U V)
  have hwords_eq : ∀ C tap t, words C tap t = wordsStd mask C tap t := by
    intro C tap t
    ext i
    simp only [words, wordsStd, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [raw_eq_rawStd (mask t)]
  have hloss_eq : ∀ C tap, loss C tap = Finset.univ.sum (fun t => cost t (wordsStd mask C tap t)) := by
    intro C tap
    dsimp only [loss]
    apply Finset.sum_congr rfl
    intro t _; rw [hwords_eq]
  have hflag_eq : ∀ r w s i, flag r w s i = flagStd r w s i := fun _ _ _ _ => rfl
  rcases main_core n m a b j mask mark cost hsub' with ⟨opt, imp, hopt1, hopt2, hW⟩
  refine ⟨opt, imp, ?_, ?_, fun W => ?_⟩
  · intro C tap hv; rw [hloss_eq]; exact hopt1 C tap hv
  · rcases hopt2 with ⟨C, tap, hv, hl⟩; exact ⟨C, tap, hv, by rw [hloss_eq]; exact hl⟩
  · have hW' := hW W
    simp_rw [hwords_eq, hloss_eq, hflag_eq]
    exact hW'

end PEqualNP.Outside.L_lib_1371_aux

theorem PEqualNP.Outside.L_lib_1371 :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    ∀ (n m a b j : Nat) (mask : Fin m → Finset (Fin n)) (mark : Fin j → Fin m)
        (cost : Fin m → Finset (Fin a) → Nat),
      (∀ t U V, cost t (U ∩ V) + cost t (U ∪ V) ≤ cost t U + cost t V) →
      let limit := max 1 (min m (n+1))
      let h := min b (Nat.log2 (2*limit-1))
      let q := min (2^h) limit
      let flag := fun (r : Fin q) (w : Finset (Fin a)) (s : Fin q) (i : Option (Fin a)) =>
        decide (s.val < r.val ∨ (s = r ∧ ∃ v, i = some v ∧ v ∈ w))
      let node := Sum Bool (Fin j × Fin q × Option (Fin a))
      let valid := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin a → Nat) =>
        PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
        C.output < n+2+C.size ∧ (∀ i, tap i < n+2+C.size) ∧ PEqualNP.NotBracket.notCount C ≤ b
      let words := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin a → Nat) (t : Fin m) =>
        Finset.univ.filter (fun i => (C.wires
          (List.ofFn (fun v : Fin n => decide (v ∈ mask t)) ++ [false,true])).getD (tap i) false)
      let loss := fun C tap => Finset.univ.sum (fun t => cost t (words C tap t))
      ∃ (opt : Nat) (imp : node → node → Prop),
        (∀ C tap, valid C tap → opt ≤ loss C tap) ∧ (∃ C tap, valid C tap ∧ loss C tap = opt) ∧
        ∀ W : Fin j → Finset (Fin a),
          let sat := ∃ r : Fin j → Fin q,
            let bit : node → Bool := Sum.elim id
              (fun z => flag (r z.1) (W z.1) z.2.1 z.2.2)
            ∀ u v, imp u v → bit u = true → bit v = true
          ((∃ C tap, valid C tap ∧ loss C tap = opt ∧ ∀ k, words C tap (mark k) = W k) ↔ sat) ∧
          (sat → ∃ C tap, valid C tap ∧ loss C tap = opt ∧ (∀ k, words C tap (mark k) = W k) ∧
            PEqualNP.NotBracket.notCount C ≤ h ∧ C.size ≤ m*(n+2*h+a)+h) := by
  exact PEqualNP.Outside.L_lib_1371_aux.main_aux
