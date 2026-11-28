import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1263_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket
open Classical

-- =========================================================================
-- Part 1: Circuit wire semantics and Markov NOT-count lower bound
-- =========================================================================

private def runsAux {α : Type*} (g : Finset α → α → Bool) : ℕ → Finset α → Prop :=
  Nat.rec (motive := fun _ => Finset α → Prop) (fun _ => True)
    (fun _ prev x => ∃ u v j, prev u ∧ u ⊆ v ∧ v ⊆ x ∧ g u j = true ∧ g v j = false)

private lemma list_any_congr {α : Type*} (l : List α) (f1 f2 : α → Bool)
    (h : ∀ x ∈ l, f1 x = f2 x) : l.any f1 = l.any f2 := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.any_cons, h a (List.mem_cons_self ..),
      ih (fun x hx => h x (List.mem_cons_of_mem a hx))]

private lemma list_all_congr {α : Type*} (l : List α) (f1 f2 : α → Bool)
    (h : ∀ x ∈ l, f1 x = f2 x) : l.all f1 = l.all f2 := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.all_cons, h a (List.mem_cons_self ..),
      ih (fun x hx => h x (List.mem_cons_of_mem a hx))]

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

private lemma notIdx_length (C : Circuit) :
    ((List.range C.gates.length).filter (fun j => isNotOp (gateAt C j).op)).length =
      notCount C := by
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
    have hmem1 : l1[k] ∈ l1 := List.getElem_mem hk1
    have h1k : l1.getD k false = true := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk1, Option.getD_some]
      exact h1 _ hmem1
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

private lemma markov_lower_bound {n d : ℕ} (g : Finset (Fin n) → Fin n → Bool)
    (C : Circuit) (hfan : FanInTwo C) (hrb : ReadsBack (n + 2) C)
    (tap : Fin n → Fin (n + 2 + C.size))
    (htap : ∀ x j, (C.wires (List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true])).getD
      (tap j).val false = g x j)
    (hruns : runsAux g d Finset.univ) :
    d < 2 ^ notCount C := by
  let inp : Finset (Fin n) → List Bool :=
    fun x => List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true]
  have hinp_len : ∀ x, (inp x).length = n + 2 := by
    intro x; simp [inp]
  let wire : Finset (Fin n) → ℕ → Bool := fun x k => (C.wires (inp x)).getD k false
  let notIdx : List ℕ := (List.range C.gates.length).filter (fun j => isNotOp (gateAt C j).op)
  let notBits : Finset (Fin n) → List Bool := fun x => notIdx.map (fun j => !(wire x (n + 2 + j)))
  let notVal : Finset (Fin n) → ℕ := fun x => bitsToNat (notBits x)
  have hwire_gate : ∀ x j, j < C.gates.length →
      wire x (n + 2 + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (wire x)) := by
    intro x j hj
    have hrb' : ReadsBack (inp x).length C := by rw [hinp_len x]; exact hrb
    have h := wires_getD_gate C (inp x) j hj hrb'
    rw [hinp_len x] at h
    exact h
  have hwire_inp : ∀ (x : Finset (Fin n)) (k : ℕ), k < n + 2 →
      wire x k = (inp x).getD k false := by
    intro x k hk
    dsimp only [wire, Circuit.wires]
    exact wires_foldl_getD_lt C.gates (inp x) k (by rw [hinp_len x]; exact hk)
  have hmono_prefix : ∀ (u v : Finset (Fin n)), u ⊆ v →
      ∀ (k : ℕ), k < n + 2 + C.gates.length →
        (∀ j < C.gates.length, (gateAt C j).op = GateOp.not → n + 2 + j < k →
          wire u (n + 2 + j) = wire v (n + 2 + j)) →
        (∀ j, k = n + 2 + j → (gateAt C j).op = GateOp.not →
          (!(wire u k)) = true → (!(wire v k)) = true) ∧
        ((∀ j, k = n + 2 + j → (gateAt C j).op ≠ GateOp.not) →
          wire u k = true → wire v k = true) := by
    intro u v huv k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk hnotEq
      have hprev : ∀ i < k, wire u i = true → wire v i = true := by
        intro i hik hui
        by_cases hlt : i < n + 2
        · have h1 := (ih i hik (by omega) (fun j hj hop hlt' => hnotEq j hj hop (by omega))).2
          exact h1 (fun j hEq => by omega) hui
        · set j := i - (n + 2)
          have hij : i = n + 2 + j := by omega
          have hj : j < C.gates.length := by omega
          by_cases hop : (gateAt C j).op = GateOp.not
          · rw [hij] at hui ⊢
            rw [← hnotEq j hj hop (by omega)]; exact hui
          · have h1 := (ih i hik (by omega) (fun j' hj' hop' hlt' => hnotEq j' hj' hop' (by omega))).2
            refine h1 (fun j' hEq => ?_) hui
            have : j' = j := by omega
            subst this; exact hop
      constructor
      · intro j hkj hop hu
        have hj : j < C.gates.length := by omega
        rw [hkj, hwire_gate u j hj, hop] at hu
        rw [hkj, hwire_gate v j hj, hop]
        simp only [GateOp.eval, Bool.not_not] at hu ⊢
        cases hins : (gateAt C j).inputs with
        | nil => simp [hins] at hu
        | cons i0 rest =>
          simp only [hins, List.map_cons, List.headD_cons] at hu ⊢
          have hi0 : i0 < n + 2 + j := hrb j hj i0 (by rw [hins]; exact List.mem_cons_self ..)
          exact hprev i0 (by omega) hu
      · intro hnotNot hu
        by_cases hlt : k < n + 2
        · rw [hwire_inp u k hlt] at hu
          rw [hwire_inp v k hlt]
          by_cases hkn : k < n
          · simp only [inp, List.getD_eq_getElem?_getD,
              List.getElem?_append_left (by simp; omega : k < (List.ofFn (fun i : Fin n => decide (i ∈ u))).length),
              List.getElem?_append_left (by simp; omega : k < (List.ofFn (fun i : Fin n => decide (i ∈ v))).length),
              List.getElem?_ofFn, dite_eq_left hkn, Option.getD_some, decide_eq_true_eq] at hu ⊢
            exact huv hu
          · have hge : (List.ofFn (fun i : Fin n => decide (i ∈ u))).length ≤ k := by simp; omega
            have hge2 : (List.ofFn (fun i : Fin n => decide (i ∈ v))).length ≤ k := by simp; omega
            simp only [inp, List.getD_eq_getElem?_getD, List.getElem?_append_right hge,
              List.getElem?_append_right hge2, List.length_ofFn] at hu ⊢
            exact hu
        · set j := k - (n + 2)
          have hkj : k = n + 2 + j := by omega
          have hj : j < C.gates.length := by omega
          have hgmem : gateAt C j ∈ C.gates := by
            simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
            exact List.getElem_mem hj
          have hfan_j := (hfan (gateAt C j) hgmem).1
          have hne : (gateAt C j).op ≠ GateOp.not := hnotNot j hkj
          have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
            rcases hfan_j with h1 | h2 | h3
            · exact Or.inl h1
            · exact Or.inr h2
            · exact absurd h3 hne
          rw [hkj, hwire_gate u j hj] at hu
          rw [hkj, hwire_gate v j hj]
          refine gateOp_mono _ hop _ _ (by simp) ?_ hu
          intro idx hidx h1
          simp only [List.length_map] at hidx
          have hmem : (gateAt C j).inputs[idx] ∈ (gateAt C j).inputs := List.getElem_mem hidx
          have hilt : (gateAt C j).inputs[idx] < n + 2 + j := hrb j hj _ hmem
          simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
            List.getElem?_eq_getElem hidx, Option.map_some, Option.getD_some] at h1 ⊢
          exact hprev _ (by omega) h1
  have hnotIdx_sorted : ∀ (a b : ℕ) (hab : a < b) (hb : b < notIdx.length),
      notIdx[a]'(by omega) < notIdx[b]'hb := by
    have hpair : notIdx.Pairwise (· < ·) := List.Pairwise.filter _ List.pairwise_lt_range
    intro a b hab hb
    exact List.pairwise_iff_getElem.mp hpair a b (by omega) hb hab
  have hnotIdx_mem : ∀ j, j ∈ notIdx ↔ j < C.gates.length ∧ (gateAt C j).op = GateOp.not := by
    intro j
    simp [notIdx, List.mem_filter, List.mem_range, isNotOp_eq_true]
  have hbits_diff_lt : ∀ (u v : Finset (Fin n)), u ⊆ v → notBits u ≠ notBits v → notVal u < notVal v := by
    intro u v huv heq
    have hex : ∃ m, m < notIdx.length ∧ (notBits u).getD m false ≠ (notBits v).getD m false := by
      by_contra hall
      push Not at hall
      apply heq
      apply List.ext_getElem (by simp [notBits])
      intro m hm1 hm2
      have h1 := hall m (by simp [notBits] at hm1; exact hm1)
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm1,
        List.getElem?_eq_getElem hm2, Option.getD_some] using h1
    let m0 := Nat.find hex
    have hm0_spec : m0 < notIdx.length ∧ (notBits u).getD m0 false ≠ (notBits v).getD m0 false :=
      Nat.find_spec hex
    have hm0_min : ∀ k < m0, (notBits u).getD k false = (notBits v).getD k false := by
      intro k hk
      by_contra hne
      exact Nat.find_min hex hk ⟨by omega, hne⟩
    set j0 := notIdx[m0]'hm0_spec.1
    have hj0_mem : j0 ∈ notIdx := List.getElem_mem hm0_spec.1
    rcases (hnotIdx_mem j0).mp hj0_mem with ⟨hj0_lt, hj0_op⟩
    have hprev_eq : ∀ j < C.gates.length, (gateAt C j).op = GateOp.not → n + 2 + j < n + 2 + j0 →
        wire u (n + 2 + j) = wire v (n + 2 + j) := by
      intro j hj hop hlt
      have hjmem : j ∈ notIdx := (hnotIdx_mem j).mpr ⟨hj, hop⟩
      rcases List.getElem_of_mem hjmem with ⟨k, hk, hkj⟩
      have hkm0 : k < m0 := by
        by_contra hge
        rcases lt_or_eq_of_le (by omega : m0 ≤ k) with hlt' | rfl
        · have := hnotIdx_sorted m0 k hlt' hk; omega
        · omega
      have heq_k := hm0_min k hkm0
      simp only [notBits, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hk, Option.map_some, Option.getD_some, hkj] at heq_k
      cases huw : wire u (n + 2 + j) <;> cases hvw : wire v (n + 2 + j) <;> simp [huw, hvw] at heq_k ⊢
    have hstep := (hmono_prefix u v huv (n + 2 + j0) (by omega) hprev_eq).1 j0 rfl hj0_op
    have hget_u : (notBits u).getD m0 false = !(wire u (n + 2 + j0)) := by
      simp only [notBits, j0, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hm0_spec.1, Option.map_some, Option.getD_some]
    have hget_v : (notBits v).getD m0 false = !(wire v (n + 2 + j0)) := by
      simp only [notBits, j0, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hm0_spec.1, Option.map_some, Option.getD_some]
    have hne_m0 := hm0_spec.2
    rw [hget_u, hget_v] at hne_m0
    have hft : (!(wire u (n + 2 + j0))) = false ∧ (!(wire v (n + 2 + j0))) = true := by
      cases h1 : !(wire u (n + 2 + j0)) <;> cases h2 : !(wire v (n + 2 + j0))
      · exact absurd (h1.trans h2.symm) hne_m0
      · exact ⟨rfl, rfl⟩
      · exact absurd (hstep h1) (by rw [h2]; simp)
      · exact absurd (h1.trans h2.symm) hne_m0
    exact bitsToNat_lt_of_first_diff (notBits u) (notBits v) (by simp [notBits])
      ⟨m0, by simp [notBits, hm0_spec.1], hm0_min, by rw [hget_u]; exact hft.1, by rw [hget_v]; exact hft.2⟩
  have hnotVal_mono : ∀ (u v : Finset (Fin n)), u ⊆ v → notVal u ≤ notVal v := by
    intro u v huv
    by_cases heq : notBits u = notBits v
    · simp [notVal, heq]
    · exact Nat.le_of_lt (hbits_diff_lt u v huv heq)
  have hnotVal_lt : ∀ (u v : Finset (Fin n)) (j : Fin n),
      u ⊆ v → g u j = true → g v j = false → notVal u < notVal v := by
    intro u v j huv hgu hgv
    by_cases hne : notBits u ≠ notBits v
    · exact hbits_diff_lt u v huv hne
    · exfalso
      push Not at hne
      have hall_not : ∀ j' < C.gates.length, (gateAt C j').op = GateOp.not →
          wire u (n + 2 + j') = wire v (n + 2 + j') := by
        intro j' hj' hop'
        rcases List.getElem_of_mem ((hnotIdx_mem j').mpr ⟨hj', hop'⟩) with ⟨k, hk, hkj⟩
        have hkeq : (notBits u)[k]'(by simp [notBits, hk]) = (notBits v)[k]'(by simp [notBits, hk]) := by
          simp [hne]
        simp only [notBits, List.getElem_map, hkj] at hkeq
        cases huw : wire u (n + 2 + j') <;> cases hvw : wire v (n + 2 + j') <;> simp [huw, hvw] at hkeq ⊢
      have hwt_u : wire u (tap j).val = true := by rw [← hgu]; exact htap u j
      have hwt_v : wire v (tap j).val = false := by rw [← hgv]; exact htap v j
      have htap_lt : (tap j).val < n + 2 + C.gates.length := (tap j).isLt
      by_cases hlt_in : (tap j).val < n + 2
      · have h1 := (hmono_prefix u v huv (tap j).val htap_lt (fun j' hj' hop' _ => hall_not j' hj' hop')).2
          (fun j' hEq => by omega) hwt_u
        rw [hwt_v] at h1; cases h1
      · set j' := (tap j).val - (n + 2)
        have hEq : (tap j).val = n + 2 + j' := by omega
        have hj' : j' < C.gates.length := by omega
        by_cases hop' : (gateAt C j').op = GateOp.not
        · have h1 := hall_not j' hj' hop'
          rw [← hEq, hwt_u, hwt_v] at h1; cases h1
        · have h1 := (hmono_prefix u v huv (tap j).val htap_lt (fun j'' hj'' hop'' _ => hall_not j'' hj'' hop'')).2
            (fun j'' hEq' => by
              have hjj : j'' = j' := by omega
              rw [hjj]; exact hop') hwt_u
          rw [hwt_v] at h1; cases h1
  have hruns_le : ∀ (k : ℕ) (x : Finset (Fin n)), runsAux g k x → k ≤ notVal x := by
    intro k
    induction k with
    | zero => intro _ _; exact Nat.zero_le _
    | succ k ih =>
      intro x hx
      rcases hx with ⟨u, v, j, hru, huv, hvx, hgu, hgv⟩
      have h1 := ih u hru
      have h2 := hnotVal_lt u v j huv hgu hgv
      have h3 := hnotVal_mono v x hvx
      omega
  have hle := hruns_le d Finset.univ hruns
  have hlt : notVal Finset.univ < 2 ^ notCount C := by
    have h1 := bitsToNat_lt (notBits Finset.univ)
    have h2 : (notBits Finset.univ).length = notCount C := by
      dsimp only [notBits, notIdx]
      rw [List.length_map, notIdx_length C]
    rw [h2] at h1
    exact h1
  omega

-- =========================================================================
-- Part 2: Circuit Builder for monotone + NOT circuits
-- =========================================================================

private structure Builder (n : ℕ) where
  gates : List Gate
  fan : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2
  rb : ∀ j < gates.length, ∀ i ∈ (gates.getD j ⟨GateOp.or, []⟩).inputs, i < n + 2 + j

private def Builder.toCircuit {n : ℕ} (B : Builder n) : Circuit := ⟨B.gates, 0⟩

private def Builder.eval {n : ℕ} (B : Builder n) (inp : List Bool) (w : ℕ) : Bool :=
  (B.toCircuit.wires inp).getD w false

private def Builder.nots {n : ℕ} (B : Builder n) : ℕ :=
  (B.gates.filter fun g => isNotOp g.op).length

private def Builder.monos {n : ℕ} (B : Builder n) : ℕ :=
  (B.gates.filter fun g => !(isNotOp g.op)).length

private lemma Builder.nots_eq_notCount {n : ℕ} (B : Builder n) :
    B.nots = notCount B.toCircuit := (notCount_eq_filter_isNotOp B.toCircuit).symm

private lemma Builder.size_eq_nots_add_monos {n : ℕ} (B : Builder n) :
    B.toCircuit.size = B.nots + B.monos := by
  unfold Builder.toCircuit Builder.nots Builder.monos Circuit.size
  suffices ∀ gs : List Gate,
      gs.length = (gs.filter fun g => isNotOp g.op).length + (gs.filter fun g => !(isNotOp g.op)).length from
    this B.gates
  intro gs
  induction gs with
  | nil => simp
  | cons g gs ih =>
    simp only [List.length_cons, List.filter_cons]
    cases isNotOp g.op <;> simp <;> omega

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

private lemma Builder.eval_empty {n : ℕ} (inp : List Bool) (w : ℕ) :
    (Builder.empty n).eval inp w = inp.getD w false := rfl

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

private def pushBin {n : ℕ} (B : Builder n) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (a b : ℕ) (ha : a < n + 2 + B.gates.length) (hb : b < n + 2 + B.gates.length) :
    Builder n × ℕ :=
  (B.push ⟨op, [a, b]⟩
    ⟨by rcases hop with rfl | rfl <;> simp, by simp⟩
    (fun i hi => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with rfl | rfl <;> assumption),
   n + 2 + B.gates.length)

private lemma pushBin_spec {n : ℕ} (B : Builder n) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (a b : ℕ) (ha : a < n + 2 + B.gates.length) (hb : b < n + 2 + B.gates.length) :
    Extends B (pushBin B op hop a b ha hb).1 ∧
    (pushBin B op hop a b ha hb).2 < n + 2 + (pushBin B op hop a b ha hb).1.gates.length ∧
    (pushBin B op hop a b ha hb).1.nots = B.nots ∧
    (pushBin B op hop a b ha hb).1.monos = B.monos + 1 ∧
    ∀ inp, inp.length = n + 2 →
      (pushBin B op hop a b ha hb).1.eval inp (pushBin B op hop a b ha hb).2 =
        op.eval [B.eval inp a, B.eval inp b] := by
  have hopf : isNotOp op = false := by rcases hop with rfl | rfl <;> rfl
  dsimp only [pushBin]
  refine ⟨Extends.push B _ _ _, ?_, ?_, ?_, ?_⟩
  · simp [Builder.push]
  · rw [Builder.push_nots]; simp [hopf]
  · rw [Builder.push_monos]; simp [hopf]
  · intro inp hinp
    rw [Builder.eval_push_new B _ _ _ inp hinp]; rfl

private def pushNot {n : ℕ} (B : Builder n) (a : ℕ) (ha : a < n + 2 + B.gates.length) :
    Builder n × ℕ :=
  (B.push ⟨GateOp.not, [a]⟩
    ⟨Or.inr (Or.inr rfl), by simp⟩
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
  refine ⟨Extends.push B _ _ _, ?_, ?_, ?_, ?_⟩
  · simp [Builder.push]
  · rw [Builder.push_nots]; simp [isNotOp]
  · rw [Builder.push_monos]; simp [isNotOp]
  · intro inp hinp
    rw [Builder.eval_push_new B _ _ _ inp hinp]; rfl

private lemma exists_or_list {n : ℕ} (ws : List ℕ) :
    ∀ (B : Builder n), (∀ w ∈ ws, w < n + 2 + B.gates.length) →
      ∃ (B' : Builder n) (out : ℕ),
        Extends B B' ∧ out < n + 2 + B'.gates.length ∧
        B'.nots = B.nots ∧ B'.monos ≤ B.monos + ws.length ∧
        ∀ inp, inp.length = n + 2 → inp.getD n false = false →
          B'.eval inp out = ws.any (B.eval inp) := by
  induction hlen : ws.length using Nat.strong_induction_on generalizing ws with
  | _ m ih =>
    intro B hws
    match ws with
    | [] =>
      refine ⟨B, n, Extends.refl B, by omega, rfl, by simp, ?_⟩
      intro inp hinp hn
      rw [show B.eval inp n = (Builder.empty n).eval inp n from by
        unfold Builder.eval Builder.toCircuit Builder.empty Circuit.wires
        exact wires_foldl_getD_lt B.gates inp n (by omega)]
      rw [Builder.eval_empty, hn]; rfl
    | [w] =>
      refine ⟨B, w, Extends.refl B, hws w (List.mem_cons_self ..), rfl, by simp, ?_⟩
      intro inp _ _; simp
    | w1 :: w2 :: rest =>
      have hw1 := hws w1 (List.mem_cons_self ..)
      have hw2 := hws w2 (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      set res1 := pushBin B GateOp.or (Or.inr rfl) w1 w2 hw1 hw2
      have hsp1 := pushBin_spec B GateOp.or (Or.inr rfl) w1 w2 hw1 hw2
      have hE1 : Extends B res1.1 := hsp1.1
      have hlt1 : res1.2 < n + 2 + res1.1.gates.length := hsp1.2.1
      have hn1 : res1.1.nots = B.nots := hsp1.2.2.1
      have hm1 : res1.1.monos = B.monos + 1 := hsp1.2.2.2.1
      have hev1 := hsp1.2.2.2.2
      have hws' : ∀ w ∈ res1.2 :: rest, w < n + 2 + res1.1.gates.length := by
        intro w hw
        rcases List.mem_cons.mp hw with rfl | hw'
        · exact hlt1
        · have h1 := hws w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw'))
          have h2 := hE1.1; omega
      rcases ih (res1.2 :: rest).length (by simp at hlen ⊢; omega) (res1.2 :: rest) rfl res1.1 hws' with
        ⟨B2, out2, hE2, hlt2, hn2, hm2, hev2⟩
      refine ⟨B2, out2, hE1.trans hE2, hlt2, hn2.trans hn1, ?_, ?_⟩
      · have hlen1 : (res1.2 :: rest).length = rest.length + 1 := rfl
        have hlen2 : (w1 :: w2 :: rest).length = rest.length + 2 := rfl
        omega
      intro inp hinp hn
      rw [hev2 inp hinp hn]
      simp only [List.any_cons]
      have h1 : res1.1.eval inp res1.2 = (B.eval inp w1 || B.eval inp w2) := by
        rw [hev1 inp hinp]; simp [GateOp.eval]
      rw [h1]
      have hrest : rest.any (res1.1.eval inp) = rest.any (B.eval inp) :=
        list_any_congr rest _ _ (fun w hw => hE1.2 inp hinp w
          (hws w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw))))
      rw [hrest, Bool.or_assoc]

private lemma exists_and_list {n : ℕ} (ws : List ℕ) :
    ∀ (B : Builder n), (∀ w ∈ ws, w < n + 2 + B.gates.length) →
      ∃ (B' : Builder n) (out : ℕ),
        Extends B B' ∧ out < n + 2 + B'.gates.length ∧
        B'.nots = B.nots ∧ B'.monos ≤ B.monos + ws.length ∧
        ∀ inp, inp.length = n + 2 → inp.getD (n + 1) false = true →
          B'.eval inp out = ws.all (B.eval inp) := by
  induction hlen : ws.length using Nat.strong_induction_on generalizing ws with
  | _ m ih =>
    intro B hws
    match ws with
    | [] =>
      refine ⟨B, n + 1, Extends.refl B, by omega, rfl, by simp, ?_⟩
      intro inp hinp hn1
      rw [show B.eval inp (n + 1) = (Builder.empty n).eval inp (n + 1) from by
        unfold Builder.eval Builder.toCircuit Builder.empty Circuit.wires
        exact wires_foldl_getD_lt B.gates inp (n + 1) (by omega)]
      rw [Builder.eval_empty, hn1]; rfl
    | [w] =>
      refine ⟨B, w, Extends.refl B, hws w (List.mem_cons_self ..), rfl, by simp, ?_⟩
      intro inp _ _; simp
    | w1 :: w2 :: rest =>
      have hw1 := hws w1 (List.mem_cons_self ..)
      have hw2 := hws w2 (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      set res1 := pushBin B GateOp.and (Or.inl rfl) w1 w2 hw1 hw2
      have hsp1 := pushBin_spec B GateOp.and (Or.inl rfl) w1 w2 hw1 hw2
      have hE1 : Extends B res1.1 := hsp1.1
      have hlt1 : res1.2 < n + 2 + res1.1.gates.length := hsp1.2.1
      have hn1 : res1.1.nots = B.nots := hsp1.2.2.1
      have hm1 : res1.1.monos = B.monos + 1 := hsp1.2.2.2.1
      have hev1 := hsp1.2.2.2.2
      have hws' : ∀ w ∈ res1.2 :: rest, w < n + 2 + res1.1.gates.length := by
        intro w hw
        rcases List.mem_cons.mp hw with rfl | hw'
        · exact hlt1
        · have h1 := hws w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw'))
          have h2 := hE1.1; omega
      rcases ih (res1.2 :: rest).length (by simp at hlen ⊢; omega) (res1.2 :: rest) rfl res1.1 hws' with
        ⟨B2, out2, hE2, hlt2, hn2, hm2, hev2⟩
      refine ⟨B2, out2, hE1.trans hE2, hlt2, hn2.trans hn1, ?_, ?_⟩
      · have hlen1 : (res1.2 :: rest).length = rest.length + 1 := rfl
        have hlen2 : (w1 :: w2 :: rest).length = rest.length + 2 := rfl
        omega
      intro inp hinp hn1'
      rw [hev2 inp hinp hn1']
      simp only [List.all_cons]
      have h1 : res1.1.eval inp res1.2 = (B.eval inp w1 && B.eval inp w2) := by
        rw [hev1 inp hinp]; simp [GateOp.eval]
      rw [h1]
      have hrest : rest.all (res1.1.eval inp) = rest.all (B.eval inp) :=
        list_all_congr rest _ _ (fun w hw => hE1.2 inp hinp w
          (hws w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw))))
      rw [hrest, Bool.and_assoc]

private lemma exists_leaveOneOut_or {n L : ℕ} (B : Builder n) (ws : Fin L → ℕ)
    (hws : ∀ i, ws i < n + 2 + B.gates.length) :
    ∃ (B' : Builder n) (out : Fin L → ℕ),
      Extends B B' ∧ (∀ i, out i < n + 2 + B'.gates.length) ∧
      B'.nots = B.nots ∧ B'.monos ≤ B.monos + 3 * L ∧
      ∀ inp, inp.length = n + 2 → inp.getD n false = false →
        ∀ i : Fin L, B'.eval inp (out i) = decide (∃ j : Fin L, j ≠ i ∧ B.eval inp (ws j) = true) := by
  have hpref : ∀ k : ℕ, k ≤ L →
      ∃ (B1 : Builder n) (pref : Fin (k + 1) → ℕ),
        Extends B B1 ∧ (∀ j, pref j < n + 2 + B1.gates.length) ∧
        B1.nots = B.nots ∧ B1.monos ≤ B.monos + k ∧
        ∀ inp, inp.length = n + 2 → inp.getD n false = false →
          ∀ j : Fin (k + 1), B1.eval inp (pref j) =
            decide (∃ t : Fin L, t.val < j.val ∧ B.eval inp (ws t) = true) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨B, fun _ => n, Extends.refl B, fun _ => by dsimp only; omega, rfl, by simp, ?_⟩
      intro inp hinp hn j
      have hj0 : j.val = 0 := by omega
      rw [show B.eval inp n = (Builder.empty n).eval inp n from by
        unfold Builder.eval Builder.toCircuit Builder.empty Circuit.wires
        exact wires_foldl_getD_lt B.gates inp n (by omega)]
      rw [Builder.eval_empty, hn]
      symm; rw [decide_eq_false_iff_not]; rintro ⟨t, ht, _⟩; omega
    | succ k ih =>
      intro hk
      rcases ih (by omega) with ⟨B1, pref1, hE1, hlt1, hn1, hm1, hev1⟩
      let wPrev := pref1 ⟨k, Nat.lt_succ_self k⟩
      let wCur := ws ⟨k, by omega⟩
      have hwPrev : wPrev < n + 2 + B1.gates.length := hlt1 ⟨k, Nat.lt_succ_self k⟩
      have hwCur : wCur < n + 2 + B1.gates.length := by have := hws ⟨k, by omega⟩; have := hE1.1; omega
      set res := pushBin B1 GateOp.or (Or.inr rfl) wPrev wCur hwPrev hwCur
      have hsp := pushBin_spec B1 GateOp.or (Or.inr rfl) wPrev wCur hwPrev hwCur
      have hEres : Extends B1 res.1 := hsp.1
      have hltres : res.2 < n + 2 + res.1.gates.length := hsp.2.1
      have hnres : res.1.nots = B1.nots := hsp.2.2.1
      have hmres : res.1.monos = B1.monos + 1 := hsp.2.2.2.1
      let pref2 : Fin (k + 2) → ℕ := fun j =>
        if hj : j.val < k + 1 then pref1 ⟨j.val, hj⟩ else res.2
      refine ⟨res.1, pref2, hE1.trans hEres, ?_, hnres.trans hn1, by omega, ?_⟩
      · intro j; dsimp only [pref2]; split_ifs with hj
        · have := hlt1 ⟨j.val, hj⟩; have := hEres.1; omega
        · exact hltres
      · intro inp hinp hn j
        dsimp only [pref2]
        split_ifs with hj
        · rw [hEres.2 inp hinp _ (hlt1 ⟨j.val, hj⟩), hev1 inp hinp hn ⟨j.val, hj⟩]
        · have hjk : j.val = k + 1 := by omega
          rw [hsp.2.2.2.2 inp hinp]
          simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          rw [hev1 inp hinp hn ⟨k, Nat.lt_succ_self k⟩, hE1.2 inp hinp wCur (hws ⟨k, by omega⟩)]
          rw [Bool.eq_iff_iff]
          simp only [Bool.or_eq_true, decide_eq_true_eq, hjk]
          constructor
          · rintro (⟨t, ht, hbt⟩ | hbk)
            · exact ⟨t, by omega, hbt⟩
            · exact ⟨⟨k, by omega⟩, by dsimp only; omega, hbk⟩
          · rintro ⟨t, ht, hbt⟩
            by_cases htk : t.val < k
            · exact Or.inl ⟨t, htk, hbt⟩
            · have htEq : t = ⟨k, by omega⟩ := by ext; dsimp only; omega
              rw [htEq] at hbt; exact Or.inr hbt
  rcases hpref L le_rfl with ⟨B1, pref, hE1, hlt1, hn1, hm1, hev1⟩
  have hsuff : ∀ k : ℕ, k ≤ L →
      ∃ (B2 : Builder n) (suff : Fin (k + 1) → ℕ),
        Extends B1 B2 ∧ (∀ j, suff j < n + 2 + B2.gates.length) ∧
        B2.nots = B1.nots ∧ B2.monos ≤ B1.monos + k ∧
        ∀ inp, inp.length = n + 2 → inp.getD n false = false →
          ∀ j : Fin (k + 1), B2.eval inp (suff j) =
            decide (∃ t : Fin L, L - j.val ≤ t.val ∧ B.eval inp (ws t) = true) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨B1, fun _ => n, Extends.refl B1, fun _ => by dsimp only; omega, rfl, by simp, ?_⟩
      intro inp hinp hn j
      have hj0 : j.val = 0 := by omega
      rw [show B1.eval inp n = (Builder.empty n).eval inp n from by
        unfold Builder.eval Builder.toCircuit Builder.empty Circuit.wires
        exact wires_foldl_getD_lt B1.gates inp n (by omega)]
      rw [Builder.eval_empty, hn]
      symm; rw [decide_eq_false_iff_not]
      rintro ⟨t, ht, _⟩; have := t.isLt; omega
    | succ k ih =>
      intro hk
      rcases ih (by omega) with ⟨B2, suff1, hE2, hlt2, hn2, hm2, hev2⟩
      let wPrev := suff1 ⟨k, Nat.lt_succ_self k⟩
      let wCur := ws ⟨L - (k + 1), by omega⟩
      have hwPrev : wPrev < n + 2 + B2.gates.length := hlt2 ⟨k, Nat.lt_succ_self k⟩
      have hwCur : wCur < n + 2 + B2.gates.length := by
        have := hws ⟨L - (k + 1), by omega⟩; have := hE1.1; have := hE2.1; omega
      set res := pushBin B2 GateOp.or (Or.inr rfl) wPrev wCur hwPrev hwCur
      have hsp := pushBin_spec B2 GateOp.or (Or.inr rfl) wPrev wCur hwPrev hwCur
      have hEres : Extends B2 res.1 := hsp.1
      have hltres : res.2 < n + 2 + res.1.gates.length := hsp.2.1
      have hnres : res.1.nots = B2.nots := hsp.2.2.1
      have hmres : res.1.monos = B2.monos + 1 := hsp.2.2.2.1
      let suff2 : Fin (k + 2) → ℕ := fun j =>
        if hj : j.val < k + 1 then suff1 ⟨j.val, hj⟩ else res.2
      refine ⟨res.1, suff2, hE2.trans hEres, ?_, hnres.trans hn2, by omega, ?_⟩
      · intro j; dsimp only [suff2]; split_ifs with hj
        · have := hlt2 ⟨j.val, hj⟩; have := hEres.1; omega
        · exact hltres
      · intro inp hinp hn j
        dsimp only [suff2]
        split_ifs with hj
        · rw [hEres.2 inp hinp _ (hlt2 ⟨j.val, hj⟩), hev2 inp hinp hn ⟨j.val, hj⟩]
        · have hjk : j.val = k + 1 := by omega
          rw [hsp.2.2.2.2 inp hinp]
          simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          rw [hev2 inp hinp hn ⟨k, Nat.lt_succ_self k⟩,
            (hE1.trans hE2).2 inp hinp wCur (hws ⟨L - (k + 1), by omega⟩)]
          rw [Bool.eq_iff_iff]
          simp only [Bool.or_eq_true, decide_eq_true_eq, hjk]
          constructor
          · rintro (⟨t, ht, hbt⟩ | hbk)
            · exact ⟨t, by omega, hbt⟩
            · exact ⟨⟨L - (k + 1), by omega⟩, by dsimp only; omega, hbk⟩
          · rintro ⟨t, ht, hbt⟩
            by_cases htk : L - k ≤ t.val
            · exact Or.inl ⟨t, htk, hbt⟩
            · have htEq : t = ⟨L - (k + 1), by omega⟩ := by ext; dsimp only; omega
              rw [htEq] at hbt; exact Or.inr hbt
  rcases hsuff L le_rfl with ⟨B2, suff, hE2, hlt2, hn2, hm2, hev2⟩
  have hcomb : ∀ k : ℕ, k ≤ L →
      ∃ (B3 : Builder n) (out : Fin k → ℕ),
        Extends B2 B3 ∧ (∀ i, out i < n + 2 + B3.gates.length) ∧
        B3.nots = B2.nots ∧ B3.monos ≤ B2.monos + k ∧
        ∀ inp, inp.length = n + 2 → inp.getD n false = false →
          ∀ i : Fin k, B3.eval inp (out i) =
            decide (∃ j : Fin L, j.val ≠ i.val ∧ B.eval inp (ws j) = true) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨B2, fun i => Fin.elim0 i, Extends.refl B2, fun i => Fin.elim0 i, rfl, by simp,
        fun _ _ _ i => Fin.elim0 i⟩
    | succ k ih =>
      intro hk
      rcases ih (by omega) with ⟨B3, out1, hE3, hlt3, hn3, hm3, hev3⟩
      let wP := pref ⟨k, by omega⟩
      let wS := suff ⟨L - (k + 1), by omega⟩
      have hwP : wP < n + 2 + B3.gates.length := by
        have := hlt1 ⟨k, by omega⟩; have := hE2.1; have := hE3.1; omega
      have hwS : wS < n + 2 + B3.gates.length := by
        have := hlt2 ⟨L - (k + 1), by omega⟩; have := hE3.1; omega
      set res := pushBin B3 GateOp.or (Or.inr rfl) wP wS hwP hwS
      have hsp := pushBin_spec B3 GateOp.or (Or.inr rfl) wP wS hwP hwS
      have hEres : Extends B3 res.1 := hsp.1
      have hltres : res.2 < n + 2 + res.1.gates.length := hsp.2.1
      have hnres : res.1.nots = B3.nots := hsp.2.2.1
      have hmres : res.1.monos = B3.monos + 1 := hsp.2.2.2.1
      let out2 : Fin (k + 1) → ℕ := fun i =>
        if hi : i.val < k then out1 ⟨i.val, hi⟩ else res.2
      refine ⟨res.1, out2, hE3.trans hEres, ?_, hnres.trans hn3, by omega, ?_⟩
      · intro i; dsimp only [out2]; split_ifs with hi
        · have := hlt3 ⟨i.val, hi⟩; have := hEres.1; omega
        · exact hltres
      · intro inp hinp hn i
        dsimp only [out2]
        split_ifs with hi
        · rw [hEres.2 inp hinp _ (hlt3 ⟨i.val, hi⟩), hev3 inp hinp hn ⟨i.val, hi⟩]
        · have hik : i.val = k := by omega
          rw [hsp.2.2.2.2 inp hinp]
          simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          rw [(hE2.trans hE3).2 inp hinp wP (hlt1 ⟨k, by omega⟩),
            hE3.2 inp hinp wS (hlt2 ⟨L - (k + 1), by omega⟩),
            hev1 inp hinp hn ⟨k, by omega⟩,
            hev2 inp hinp hn ⟨L - (k + 1), by omega⟩]
          rw [Bool.eq_iff_iff]
          simp only [Bool.or_eq_true, decide_eq_true_eq, hik]
          constructor
          · rintro (⟨t, ht, hbt⟩ | ⟨t, ht, hbt⟩)
            · exact ⟨t, by omega, hbt⟩
            · exact ⟨t, by omega, hbt⟩
          · rintro ⟨t, ht, hbt⟩
            by_cases hlt : t.val < k
            · exact Or.inl ⟨t, hlt, hbt⟩
            · exact Or.inr ⟨t, by omega, hbt⟩
  rcases hcomb L le_rfl with ⟨B3, out, hE3, hlt3, hn3, hm3, hev3⟩
  refine ⟨B3, out, hE1.trans (hE2.trans hE3), hlt3, by omega, by omega, ?_⟩
  intro inp hinp hn i
  rw [hev3 inp hinp hn i]
  congr 1; apply propext
  constructor
  · rintro ⟨j, hne, hbj⟩; exact ⟨j, fun h => hne (congrArg Fin.val h), hbj⟩
  · rintro ⟨j, hne, hbj⟩; exact ⟨j, fun h => hne (Fin.ext h), hbj⟩

-- =========================================================================
-- Part 3: Finite field F_q geometry (char 2) and graph H
-- =========================================================================

section FieldGeom


private abbrev FieldQ (s : ℕ) := GaloisField 2 (2 * s)

private lemma fieldQ_add_self (s : ℕ) (x : FieldQ s) : x + x = 0 := by
  have h2 : (2 : FieldQ s) = 0 := by
    have hmap := map_natCast (algebraMap (ZMod 2) (FieldQ s)) 2
    have hz : ((2 : ℕ) : ZMod 2) = 0 := rfl
    rw [hz, map_zero] at hmap
    exact hmap.symm
  calc x + x = (2 : FieldQ s) * x := by ring
    _ = 0 * x := by rw [h2]
    _ = 0 := zero_mul x

private lemma fieldQ_add_eq_zero_iff (s : ℕ) (x y : FieldQ s) : x + y = 0 ↔ x = y := by
  constructor
  · intro h
    have h1 := fieldQ_add_self s y
    calc x = x + (y + y) := by rw [h1, add_zero]
      _ = (x + y) + y := by ring
      _ = 0 + y := by rw [h]
      _ = y := zero_add y
  · rintro rfl; exact fieldQ_add_self s x

private lemma fieldQ_card (s : ℕ) [Fintype (FieldQ s)] (hs : 1 ≤ s) :
    Fintype.card (FieldQ s) = (2 ^ s) * (2 ^ s) := by
  have h := GaloisField.card 2 (2 * s) (by omega)
  rw [← Nat.card_eq_fintype_card, h, show 2 * s = s + s by omega, pow_add]

private abbrev Pt (s : ℕ) := {p : FieldQ s × FieldQ s // p ≠ (0, 0)}

private lemma pt_card (s : ℕ) [Fintype (FieldQ s)] (hs : 1 ≤ s) :
    Fintype.card (Pt s) = ((2 ^ s) * (2 ^ s)) * ((2 ^ s) * (2 ^ s)) - 1 := by
  have h1 : Fintype.card (Pt s) = ((Finset.univ : Finset (FieldQ s × FieldQ s)).erase (0, 0)).card := by
    rw [Fintype.card_subtype]
    congr 1; ext p; simp [Finset.mem_erase]
  rw [h1, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_prod,
    fieldQ_card s hs]

private def adjPt {s : ℕ} (p1 p2 : Pt s) : Prop :=
  p1.1.1 * p2.1.2 + p1.1.2 * p2.1.1 = 1

private lemma adjPt_symm {s : ℕ} {p1 p2 : Pt s} (h : adjPt p1 p2) : adjPt p2 p1 := by
  unfold adjPt at h ⊢; linear_combination h

private lemma adjPt_irrefl {s : ℕ} (p : Pt s) : ¬ adjPt p p := by
  intro h
  unfold adjPt at h
  have h0 : p.1.1 * p.1.2 + p.1.2 * p.1.1 = 0 := by
    rw [mul_comm p.1.2 p.1.1]; exact fieldQ_add_self s _
  rw [h0] at h
  exact zero_ne_one h

private lemma adjPt_deg {s : ℕ} [Fintype (FieldQ s)] (hs : 1 ≤ s) (p : Pt s) :
    ((Finset.univ : Finset (Pt s)).filter (fun r => adjPt p r)).card = (2 ^ s) * (2 ^ s) := by
  rw [← fieldQ_card s hs, ← Finset.card_univ]
  by_cases ha : p.1.1 ≠ 0
  · refine Finset.card_bij'
      (fun r _ => r.1.1)
      (fun c _ => ⟨(c, p.1.1⁻¹ * (1 + p.1.2 * c)), by
        intro hEq
        have hc : c = 0 := congrArg Prod.fst hEq
        have hd : p.1.1⁻¹ * (1 + p.1.2 * c) = 0 := congrArg Prod.snd hEq
        subst hc
        simp [ha] at hd⟩) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro c _
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      dsimp only [adjPt]
      have h1 : p.1.1 * (p.1.1⁻¹ * (1 + p.1.2 * c)) = 1 + p.1.2 * c := by
        rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]
      rw [h1, add_assoc, fieldQ_add_self s (p.1.2 * c), add_zero]
    · intro r hr
      have hradj : p.1.1 * r.1.2 + p.1.2 * r.1.1 = 1 := (Finset.mem_filter.mp hr).2
      apply Subtype.ext; apply Prod.ext; rfl
      have h1 : p.1.1 * r.1.2 = 1 + p.1.2 * r.1.1 := by
        have h0 := fieldQ_add_self s (p.1.2 * r.1.1)
        linear_combination hradj - h0
      calc p.1.1⁻¹ * (1 + p.1.2 * r.1.1) = p.1.1⁻¹ * (p.1.1 * r.1.2) := by rw [← h1]
        _ = (p.1.1⁻¹ * p.1.1) * r.1.2 := by ring
        _ = r.1.2 := by rw [inv_mul_cancel₀ ha, one_mul]
    · intro c _; rfl
  · push Not at ha
    have hb : p.1.2 ≠ 0 := by
      intro hb0; exact p.2 (Prod.ext ha hb0)
    refine Finset.card_bij'
      (fun r _ => r.1.2)
      (fun d _ => ⟨(p.1.2⁻¹, d), by intro hEq; have := congrArg Prod.fst hEq; exact inv_ne_zero hb this⟩)
      ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro d _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, adjPt, ha, zero_mul, zero_add]
      exact mul_inv_cancel₀ hb
    · intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, adjPt, ha, zero_mul, zero_add] at hr
      apply Subtype.ext; apply Prod.ext
      · calc p.1.2⁻¹ = p.1.2⁻¹ * 1 := (mul_one _).symm
          _ = p.1.2⁻¹ * (p.1.2 * r.1.1) := by rw [← hr]
          _ = (p.1.2⁻¹ * p.1.2) * r.1.1 := by ring
          _ = r.1.1 := by rw [inv_mul_cancel₀ hb, one_mul]
      · rfl
    · intro d _; rfl

private noncomputable def rayOf {s : ℕ} (p : Pt s) : Option (FieldQ s) :=
  if p.1.2 = 0 then none else some (p.1.1 * p.1.2⁻¹)

private lemma rayOf_eq_iff_det_zero {s : ℕ} (p1 p2 : Pt s) :
    rayOf p1 = rayOf p2 ↔ p1.1.1 * p2.1.2 + p1.1.2 * p2.1.1 = 0 := by
  unfold rayOf
  by_cases h1 : p1.1.2 = 0 <;> by_cases h2 : p2.1.2 = 0
  · simp [h1, h2]
  · rw [if_pos h1, if_neg h2, h1, zero_mul, add_zero]
    have ha1 : p1.1.1 ≠ 0 := fun ha => p1.2 (Prod.ext ha h1)
    simp [mul_ne_zero ha1 h2]
  · rw [if_neg h1, if_pos h2, h2, mul_zero, zero_add]
    have ha2 : p2.1.1 ≠ 0 := fun ha => p2.2 (Prod.ext ha h2)
    simp [mul_ne_zero h1 ha2]
  · rw [if_neg h1, if_neg h2, Option.some.injEq,
      fieldQ_add_eq_zero_iff]
    constructor
    · intro h
      calc p1.1.1 * p2.1.2 = (p1.1.1 * p1.1.2⁻¹) * p1.1.2 * p2.1.2 := by
            rw [mul_assoc (p1.1.1) (p1.1.2⁻¹) (p1.1.2), inv_mul_cancel₀ h1, mul_one]
        _ = (p2.1.1 * p2.1.2⁻¹) * p1.1.2 * p2.1.2 := by rw [h]
        _ = p1.1.2 * p2.1.1 * (p2.1.2⁻¹ * p2.1.2) := by ring
        _ = p1.1.2 * p2.1.1 := by rw [inv_mul_cancel₀ h2, mul_one]
    · intro h
      calc p1.1.1 * p1.1.2⁻¹ = (p1.1.1 * p2.1.2) * (p1.1.2⁻¹ * p2.1.2⁻¹) := by
            rw [show (p1.1.1 * p2.1.2) * (p1.1.2⁻¹ * p2.1.2⁻¹) =
              p1.1.1 * p1.1.2⁻¹ * (p2.1.2 * p2.1.2⁻¹) by ring, mul_inv_cancel₀ h2, mul_one]
        _ = (p1.1.2 * p2.1.1) * (p1.1.2⁻¹ * p2.1.2⁻¹) := by rw [h]
        _ = p2.1.1 * p2.1.2⁻¹ * (p1.1.2 * p1.1.2⁻¹) := by ring
        _ = p2.1.1 * p2.1.2⁻¹ := by rw [mul_inv_cancel₀ h1, mul_one]

private lemma common_nb_card {s : ℕ} [Fintype (FieldQ s)] (p1 p2 : Pt s) (hne : p1 ≠ p2) :
    ((Finset.univ : Finset (Pt s)).filter (fun r => adjPt p1 r ∧ adjPt p2 r)).card ≤
      if rayOf p1 = rayOf p2 then 0 else 1 := by
  by_cases hray : rayOf p1 = rayOf p2
  · rw [if_pos hray, Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro r _ ⟨hr1, hr2⟩
    have hdet : p1.1.1 * p2.1.2 + p1.1.2 * p2.1.1 = 0 := (rayOf_eq_iff_det_zero p1 p2).mp hray
    unfold adjPt at hr1 hr2
    have h1 : (p1.1.1 + p2.1.1) * r.1.2 + (p1.1.2 + p2.1.2) * r.1.1 = 0 := by
      have h0 := fieldQ_add_self s (1 : FieldQ s)
      linear_combination hr1 + hr2 + h0
    have hdx : p1.1.1 * (p1.1.2 + p2.1.2) = p1.1.2 * (p1.1.1 + p2.1.1) := by
      rw [← fieldQ_add_eq_zero_iff]
      have h0 := fieldQ_add_self s (p1.1.1 * p1.1.2)
      linear_combination hdet + h0
    have hprod1 : p1.1.1 + p2.1.1 = 0 := by
      have hcalc : (p1.1.1 + p2.1.1) * (p1.1.1 * r.1.2 + p1.1.2 * r.1.1) = 0 := by
        calc (p1.1.1 + p2.1.1) * (p1.1.1 * r.1.2 + p1.1.2 * r.1.1)
            = p1.1.1 * ((p1.1.1 + p2.1.1) * r.1.2) + (p1.1.2 * (p1.1.1 + p2.1.1)) * r.1.1 := by ring
          _ = p1.1.1 * ((p1.1.1 + p2.1.1) * r.1.2) + (p1.1.1 * (p1.1.2 + p2.1.2)) * r.1.1 := by rw [← hdx]
          _ = p1.1.1 * ((p1.1.1 + p2.1.1) * r.1.2 + (p1.1.2 + p2.1.2) * r.1.1) := by ring
          _ = p1.1.1 * 0 := by rw [h1]
          _ = 0 := mul_zero _
      rw [hr1, mul_one] at hcalc; exact hcalc
    have hprod2 : p1.1.2 + p2.1.2 = 0 := by
      have hcalc : (p1.1.2 + p2.1.2) * (p1.1.1 * r.1.2 + p1.1.2 * r.1.1) = 0 := by
        calc (p1.1.2 + p2.1.2) * (p1.1.1 * r.1.2 + p1.1.2 * r.1.1)
            = (p1.1.1 * (p1.1.2 + p2.1.2)) * r.1.2 + p1.1.2 * ((p1.1.2 + p2.1.2) * r.1.1) := by ring
          _ = (p1.1.2 * (p1.1.1 + p2.1.1)) * r.1.2 + p1.1.2 * ((p1.1.2 + p2.1.2) * r.1.1) := by rw [hdx]
          _ = p1.1.2 * ((p1.1.1 + p2.1.1) * r.1.2 + (p1.1.2 + p2.1.2) * r.1.1) := by ring
          _ = p1.1.2 * 0 := by rw [h1]
          _ = 0 := mul_zero _
      rw [hr1, mul_one] at hcalc; exact hcalc
    exact hne (Subtype.ext (Prod.ext ((fieldQ_add_eq_zero_iff s ..).mp hprod1)
      ((fieldQ_add_eq_zero_iff s ..).mp hprod2)))
  · rw [if_neg hray]
    have hdet : p1.1.1 * p2.1.2 + p1.1.2 * p2.1.1 ≠ 0 := by
      intro h0; exact hray ((rayOf_eq_iff_det_zero p1 p2).mpr h0)
    rw [Finset.card_le_one]
    intro r1 hr1 r2 hr2
    rcases (Finset.mem_filter.mp hr1).2 with ⟨hr1a, hr1b⟩
    rcases (Finset.mem_filter.mp hr2).2 with ⟨hr2a, hr2b⟩
    unfold adjPt at hr1a hr1b hr2a hr2b
    have hdx : p1.1.1 * (r1.1.2 + r2.1.2) + p1.1.2 * (r1.1.1 + r2.1.1) = 0 := by
      have h0 := fieldQ_add_self s (1 : FieldQ s)
      linear_combination hr1a + hr2a + h0
    have hdy : p2.1.1 * (r1.1.2 + r2.1.2) + p2.1.2 * (r1.1.1 + r2.1.1) = 0 := by
      have h0 := fieldQ_add_self s (1 : FieldQ s)
      linear_combination hr1b + hr2b + h0
    have h1 : (p1.1.1 * p2.1.2 + p1.1.2 * p2.1.1) * (r1.1.1 + r2.1.1) = 0 := by
      have h0 := fieldQ_add_self s (p1.1.1 * p2.1.1 * (r1.1.2 + r2.1.2))
      linear_combination p1.1.1 * hdy + p2.1.1 * hdx - h0
    have h2 : (p1.1.1 * p2.1.2 + p1.1.2 * p2.1.1) * (r1.1.2 + r2.1.2) = 0 := by
      have h0 := fieldQ_add_self s (p1.1.2 * p2.1.2 * (r1.1.1 + r2.1.1))
      linear_combination p2.1.2 * hdx + p1.1.2 * hdy - h0
    have hx := (mul_eq_zero.mp h1).resolve_left hdet
    have hy := (mul_eq_zero.mp h2).resolve_left hdet
    exact Subtype.ext (Prod.ext ((fieldQ_add_eq_zero_iff s ..).mp hx)
      ((fieldQ_add_eq_zero_iff s ..).mp hy))

private lemma nat_cauchy_schwarz {α : Type*} (S : Finset α) (f : α → ℕ) :
    (∑ x ∈ S, f x) ^ 2 ≤ S.card * ∑ x ∈ S, f x ^ 2 := by
  have hZ : (0 : ℤ) ≤ ∑ x ∈ S, ∑ y ∈ S, ((f x : ℤ) - (f y : ℤ)) ^ 2 :=
    Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ => sq_nonneg _))
  have hexp : (∑ x ∈ S, ∑ y ∈ S, ((f x : ℤ) - (f y : ℤ)) ^ 2) =
      2 * ((S.card : ℤ) * (∑ x ∈ S, (f x : ℤ) ^ 2) - (∑ x ∈ S, (f x : ℤ)) ^ 2) := by
    have h1 : ∀ x ∈ S, (∑ y ∈ S, ((f x : ℤ) - (f y : ℤ)) ^ 2) =
        (S.card : ℤ) * (f x : ℤ) ^ 2 - 2 * (f x : ℤ) * (∑ y ∈ S, (f y : ℤ)) +
          ∑ y ∈ S, (f y : ℤ) ^ 2 := by
      intro x _
      have hsq : ∀ y ∈ S, ((f x : ℤ) - (f y : ℤ)) ^ 2 =
          (f x : ℤ) ^ 2 - 2 * (f x : ℤ) * (f y : ℤ) + (f y : ℤ) ^ 2 := fun y _ => by ring
      rw [Finset.sum_congr rfl hsq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    ring
  have hle : (∑ x ∈ S, (f x : ℤ)) ^ 2 ≤ (S.card : ℤ) * (∑ x ∈ S, (f x : ℤ) ^ 2) := by linarith
  have hcast : ((∑ x ∈ S, f x) ^ 2 : ℤ) ≤ ((S.card * ∑ x ∈ S, f x ^ 2 : ℕ) : ℤ) := by
    push_cast; exact hle
  exact Int.ofNat_le.mp hcast

private lemma indep_bound {s : ℕ} [Fintype (FieldQ s)] (hs : 1 ≤ s) (A : Finset (Pt s))
    (hind : ∀ u ∈ A, ∀ v ∈ A, ¬ adjPt u v) :
    let rootQ := 2 ^ s
    let q := rootQ * rootQ
    A.card ≤ (rootQ - 1) * (q + 1) := by
  intro rootQ q
  set h := A.card
  by_cases hh0 : h = 0
  · rw [hh0]; exact Nat.zero_le _
  set Ac : Finset (Pt s) := Finset.univ \ A
  have hAc_card : Ac.card = q * q - 1 - h := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, pt_card s hs]
  let d : Pt s → ℕ := fun w => (A.filter (fun v => adjPt v w)).card
  have hsum_d : ∑ w ∈ Ac, d w = q * h := by
    have h1 : (∑ w ∈ Ac, d w) = ∑ v ∈ A, (Ac.filter (fun w => adjPt v w)).card := by
      simp only [d, Finset.card_filter]
      rw [Finset.sum_comm]
    rw [h1]
    have h2 : ∀ v ∈ A, (Ac.filter (fun w => adjPt v w)).card = q := by
      intro v hv
      have hfilt_eq : Ac.filter (fun w => adjPt v w) = Finset.univ.filter (fun w => adjPt v w) := by
        ext w
        simp only [Ac, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
        exact ⟨fun hw => hw.2, fun hw => ⟨fun hwA => hind v hv w hwA hw, hw⟩⟩
      rw [hfilt_eq]; exact adjPt_deg hs v
    rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, mul_comm]
  let c : Option (FieldQ s) → ℕ := fun ray => (A.filter (fun v => rayOf v = ray)).card
  have hsum_c : ∑ ray : Option (FieldQ s), c ray = h := by
    simp only [c, Finset.card_filter]
    rw [Finset.sum_comm]
    have h1 : ∀ v ∈ A, (∑ ray : Option (FieldQ s), if rayOf v = ray then 1 else 0) = 1 := by
      intro v _
      rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul, mul_one]
  have hcs1 : h ^ 2 ≤ (q + 1) * ∑ ray : Option (FieldQ s), c ray ^ 2 := by
    have h1 := nat_cauchy_schwarz (Finset.univ : Finset (Option (FieldQ s))) c
    rw [hsum_c, Finset.card_univ, Fintype.card_option, fieldQ_card s hs] at h1
    exact h1
  have hpairs_eq : (∑ w ∈ Ac, d w * d w) =
      (∑ w ∈ Ac, d w) +
        ∑ v1 ∈ A, ∑ v2 ∈ A.erase v1, (Ac.filter (fun w => adjPt v1 w ∧ adjPt v2 w)).card := by
    have hsplit : ∀ w ∈ Ac, d w * d w =
        d w + ∑ v1 ∈ A, ∑ v2 ∈ A.erase v1, if adjPt v1 w ∧ adjPt v2 w then 1 else 0 := by
      intro w _
      set Sw := A.filter (fun v => adjPt v w)
      have hcard : d w = Sw.card := rfl
      have hsum2 : (∑ v1 ∈ A, ∑ v2 ∈ A.erase v1, if adjPt v1 w ∧ adjPt v2 w then 1 else 0) =
          ∑ v1 ∈ Sw, (Sw.erase v1).card := by
        have hstep1 : ∀ v1 ∈ A,
            (∑ v2 ∈ A.erase v1, if adjPt v1 w ∧ adjPt v2 w then 1 else 0) =
              if adjPt v1 w then (Sw.erase v1).card else 0 := by
          intro v1 _
          by_cases h1 : adjPt v1 w
          · rw [if_pos h1]
            simp only [h1, true_and, Finset.sum_boole, Nat.cast_id]
            congr 1; ext v2; simp [Sw, Finset.mem_erase, Finset.mem_filter, and_comm, and_left_comm]
          · rw [if_neg h1]
            simp [h1]
        rw [Finset.sum_congr rfl hstep1, ← Finset.sum_filter]
      rw [hsum2, hcard]
      have hterm : ∀ v1 ∈ Sw, (Sw.erase v1).card = Sw.card - 1 :=
        fun v1 hv1 => Finset.card_erase_of_mem hv1
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul]
      cases hSw : Sw.card with
      | zero => simp
      | succ k => simp only [Nat.add_sub_cancel]; ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro v1 _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro v2 _
    rw [Finset.card_filter]
  have hpairs_le : (∑ v1 ∈ A, ∑ v2 ∈ A.erase v1, (Ac.filter (fun w => adjPt v1 w ∧ adjPt v2 w)).card) ≤
      h ^ 2 - ∑ ray : Option (FieldQ s), c ray ^ 2 := by
    have hterm : ∀ v1 ∈ A, ∀ v2 ∈ A.erase v1,
        (Ac.filter (fun w => adjPt v1 w ∧ adjPt v2 w)).card ≤
          if rayOf v1 = rayOf v2 then 0 else 1 := by
      intro v1 _ v2 hv2
      have hne : v1 ≠ v2 := (Finset.mem_erase.mp hv2).1.symm
      have hsub : Ac.filter (fun w => adjPt v1 w ∧ adjPt v2 w) ⊆
          Finset.univ.filter (fun w => adjPt v1 w ∧ adjPt v2 w) :=
        Finset.filter_subset_filter _ (Finset.subset_univ _)
      exact le_trans (Finset.card_le_card hsub) (common_nb_card v1 v2 hne)
    have hle1 : (∑ v1 ∈ A, ∑ v2 ∈ A.erase v1, (Ac.filter (fun w => adjPt v1 w ∧ adjPt v2 w)).card) ≤
        ∑ v1 ∈ A, ∑ v2 ∈ A.erase v1, if rayOf v1 = rayOf v2 then 0 else 1 :=
      Finset.sum_le_sum (fun v1 hv1 => Finset.sum_le_sum (fun v2 hv2 => hterm v1 hv1 v2 hv2))
    have hsum_nonprop :
        (∑ v1 ∈ A, ∑ v2 ∈ A.erase v1, if rayOf v1 = rayOf v2 then 0 else 1) +
          (∑ ray : Option (FieldQ s), c ray ^ 2) = h ^ 2 := by
      have h2 : ∀ v1 ∈ A,
          (∑ v2 ∈ A.erase v1, if rayOf v1 = rayOf v2 then 0 else 1) =
            (∑ v2 ∈ A, if rayOf v1 = rayOf v2 then 0 else 1) := by
        intro v1 hv1
        rw [← Finset.add_sum_erase A _ hv1, if_pos rfl, zero_add]
      rw [Finset.sum_congr rfl h2]
      have h3 : (∑ v1 ∈ A, ∑ v2 ∈ A, if rayOf v1 = rayOf v2 then 0 else 1) +
          (∑ v1 ∈ A, ∑ v2 ∈ A, if rayOf v1 = rayOf v2 then 1 else 0) = h ^ 2 := by
        rw [← Finset.sum_add_distrib]
        have h4 : ∀ v1 ∈ A,
            ((∑ v2 ∈ A, if rayOf v1 = rayOf v2 then 0 else 1) +
              ∑ v2 ∈ A, if rayOf v1 = rayOf v2 then 1 else 0) = h := by
          intro v1 _
          rw [← Finset.sum_add_distrib]
          have h5 : ∀ v2 ∈ A, (if rayOf v1 = rayOf v2 then 0 else 1) +
              (if rayOf v1 = rayOf v2 then 1 else 0) = 1 := by
            intro v2 _; split_ifs <;> rfl
          rw [Finset.sum_congr rfl h5, Finset.sum_const, smul_eq_mul, mul_one]
        rw [Finset.sum_congr rfl h4, Finset.sum_const, smul_eq_mul, sq]
      have hray_sq : (∑ ray : Option (FieldQ s), c ray ^ 2) =
          ∑ v1 ∈ A, ∑ v2 ∈ A, if rayOf v1 = rayOf v2 then 1 else 0 := by
        have hsq : ∀ ray : Option (FieldQ s),
            c ray ^ 2 = ∑ v1 ∈ A, ∑ v2 ∈ A, if rayOf v1 = ray ∧ rayOf v2 = ray then 1 else 0 := by
          intro ray
          rw [sq]
          dsimp only [c]
          rw [Finset.card_filter, Finset.sum_mul]
          apply Finset.sum_congr rfl; intro v1 _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro v2 _
          by_cases h1 : rayOf v1 = ray <;> by_cases h2 : rayOf v2 = ray <;> simp [h1, h2]
        rw [Finset.sum_congr rfl (fun ray _ => hsq ray), Finset.sum_comm]
        apply Finset.sum_congr rfl; intro v1 _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro v2 _
        by_cases heq : rayOf v1 = rayOf v2
        · rw [if_pos heq]
          have hrew : ∀ ray : Option (FieldQ s),
              (if rayOf v1 = ray ∧ rayOf v2 = ray then 1 else 0) =
                if rayOf v1 = ray then 1 else 0 := by
            intro ray; rw [← heq]; simp
          rw [Finset.sum_congr rfl (fun ray _ => hrew ray), Finset.sum_ite_eq,
            if_pos (Finset.mem_univ _)]
        · rw [if_neg heq]
          apply Finset.sum_eq_zero; intro ray _
          rw [if_neg]; rintro ⟨rfl, h2⟩; exact heq h2.symm
      rw [hray_sq]; exact h3
    omega
  have hcs2 : (q * h) ^ 2 ≤ Ac.card * ∑ w ∈ Ac, d w ^ 2 := by
    have h1 := nat_cauchy_schwarz Ac d
    rw [hsum_d] at h1
    exact h1
  have hsum_sq_mul : (q + 1) * (∑ w ∈ Ac, d w ^ 2) ≤ q * h * (h + q + 1) := by
    have hsq_eq : (∑ w ∈ Ac, d w ^ 2) = ∑ w ∈ Ac, d w * d w := by
      apply Finset.sum_congr rfl; intro w _; rw [sq]
    rw [hsq_eq, hpairs_eq, hsum_d]
    have hsum_c_le : ∑ ray : Option (FieldQ s), c ray ^ 2 ≤ h ^ 2 := by
      have : ∀ ray : Option (FieldQ s), c ray ^ 2 ≤ c ray * h := by
        intro ray
        have hcle : c ray ≤ h := Finset.card_filter_le A _
        rw [sq]; exact Nat.mul_le_mul_left _ hcle
      calc ∑ ray : Option (FieldQ s), c ray ^ 2
          ≤ ∑ ray : Option (FieldQ s), c ray * h := Finset.sum_le_sum (fun r _ => this r)
        _ = (∑ ray : Option (FieldQ s), c ray) * h := (Finset.sum_mul ..).symm
        _ = h ^ 2 := by rw [hsum_c, sq]
    have hmul : (q + 1) * (q * h + (h ^ 2 - ∑ ray : Option (FieldQ s), c ray ^ 2)) ≤
        q * h * (h + q + 1) := by
      have hz : (q + 1) * (h ^ 2 - ∑ ray : Option (FieldQ s), c ray ^ 2) +
          (q + 1) * ∑ ray : Option (FieldQ s), c ray ^ 2 = (q + 1) * h ^ 2 := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hsum_c_le]
      nlinarith
    have hle2 := Nat.mul_le_mul_left (q + 1) (Nat.add_le_add_left hpairs_le (q * h))
    exact le_trans hle2 hmul
  have hA_le_n : h ≤ q * q - 1 := by
    have h1 : A.card ≤ Fintype.card (Pt s) := Finset.card_le_univ A
    rw [pt_card s hs] at h1; exact h1
  have hq_ge : 4 ≤ q := by
    have hr : 2 ≤ rootQ := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ s := Nat.pow_le_pow_right (by omega) hs
    dsimp only [q]; nlinarith
  have hkey : (h + q + 1) ^ 2 ≤ (rootQ * (q + 1)) ^ 2 := by
    have hstep1 : (q + 1) * (q * h) ^ 2 ≤ Ac.card * ((q + 1) * ∑ w ∈ Ac, d w ^ 2) := by
      have := Nat.mul_le_mul_left (q + 1) hcs2
      linarith
    have hstep2 : (q + 1) * (q * h) ^ 2 ≤ Ac.card * (q * h * (h + q + 1)) :=
      le_trans hstep1 (Nat.mul_le_mul_left Ac.card hsum_sq_mul)
    have hqh_pos : 0 < q * h := Nat.mul_pos (by omega) (by omega)
    have hstep3 : (q + 1) * (q * h) ≤ Ac.card * (h + q + 1) := by
      have : (q * h) * ((q + 1) * (q * h)) ≤ (q * h) * (Ac.card * (h + q + 1)) := by linarith
      exact Nat.le_of_mul_le_mul_left this hqh_pos
    rw [hAc_card] at hstep3
    have hsub1 : (q * q - 1 - h) + h + 1 = q * q := by omega
    have hqeq : rootQ * rootQ = q := rfl
    nlinarith
  have hlin : h + q + 1 ≤ rootQ * (q + 1) := by
    by_contra hgt
    have hlt : rootQ * (q + 1) < h + q + 1 := by omega
    have hsq : (rootQ * (q + 1)) ^ 2 < (h + q + 1) ^ 2 := Nat.pow_lt_pow_left hlt (by omega)
    omega
  have hr1 : 1 ≤ rootQ := by
    have : 2 ≤ rootQ := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ s := Nat.pow_le_pow_right (by omega) hs
    omega
  have hdist : (rootQ - 1) * (q + 1) + (q + 1) = rootQ * (q + 1) := by
    rw [← Nat.add_one_mul, Nat.sub_add_cancel hr1]
  omega

-- =========================================================================
-- Part 4: Affine rank function g and its 2-NOT circuit
-- =========================================================================

private noncomputable def evalDir {s : ℕ} (d : Option (FieldQ s)) (p : FieldQ s × FieldQ s) : FieldQ s :=
  match d with
  | none => p.2
  | some m => p.1 + m * p.2

private lemma two_pts_unique_line {s : ℕ} (p1 p2 : Pt s) (hne : p1 ≠ p2) :
    ∃! dc : Option (FieldQ s) × FieldQ s, evalDir dc.1 p1.1 = dc.2 ∧ evalDir dc.1 p2.1 = dc.2 := by
  by_cases hy : p1.1.2 = p2.1.2
  · have hx : p1.1.1 ≠ p2.1.1 := fun h => hne (Subtype.ext (Prod.ext h hy))
    refine ⟨(none, p1.1.2), ⟨rfl, hy.symm⟩, ?_⟩
    rintro ⟨d, c⟩ ⟨h1, h2⟩
    cases d with
    | none => simp only [evalDir] at h1; subst h1; rfl
    | some m =>
      simp only [evalDir] at h1 h2
      have hEq : p1.1.1 + m * p1.1.2 = p2.1.1 + m * p2.1.2 := h1.trans h2.symm
      rw [hy] at hEq
      exact absurd (add_right_cancel hEq) hx
  · have hdy : p1.1.2 + p2.1.2 ≠ 0 := fun h => hy ((fieldQ_add_eq_zero_iff s ..).mp h)
    let m := (p1.1.1 + p2.1.1) * (p1.1.2 + p2.1.2)⁻¹
    let c0 := p1.1.1 + m * p1.1.2
    refine ⟨(some m, c0), ⟨rfl, ?_⟩, ?_⟩
    · dsimp only [evalDir, c0, m]
      rw [← fieldQ_add_eq_zero_iff]
      have h1 : (p1.1.1 + p2.1.1) * (p1.1.2 + p2.1.2)⁻¹ * (p1.1.2 + p2.1.2) = p1.1.1 + p2.1.1 := by
        rw [mul_assoc, inv_mul_cancel₀ hdy, mul_one]
      have h0 := fieldQ_add_self s (p1.1.1 + p2.1.1)
      linear_combination h1 + h0
    · rintro ⟨d, c⟩ ⟨h1, h2⟩
      cases d with
      | none => simp only [evalDir] at h1 h2; exact absurd (h1.trans h2.symm) hy
      | some m' =>
        simp only [evalDir] at h1 h2
        have hEq : (p1.1.1 + p2.1.1) + m' * (p1.1.2 + p2.1.2) = 0 := by
          have h0 := fieldQ_add_self s c
          linear_combination h1 + h2 + h0
        have hm' : m' = m := by
          have h3 : m' * (p1.1.2 + p2.1.2) = p1.1.1 + p2.1.1 :=
            ((fieldQ_add_eq_zero_iff s ..).mp hEq).symm
          calc m' = m' * (p1.1.2 + p2.1.2) * (p1.1.2 + p2.1.2)⁻¹ := by
                rw [mul_assoc, mul_inv_cancel₀ hdy, mul_one]
            _ = m := by rw [h3]
        subst hm'
        have hc : c = c0 := h1.symm
        subst hc; rfl

private noncomputable def affRank {s : ℕ} (x : Finset (Pt s)) : ℕ :=
  if x = ∅ then 0
  else if x.card = 1 then 1
  else if ∃ d c, ∀ u ∈ x, evalDir d u.1 = c then 2
  else 3

private noncomputable def gAff {s : ℕ} (x : Finset (Pt s)) (p : Pt s) : Bool :=
  decide (affRank x < affRank (insert p x))

private lemma affRank_le_three {s : ℕ} (x : Finset (Pt s)) : affRank x ≤ 3 := by
  unfold affRank; split_ifs <;> omega

private lemma affRank_mono {s : ℕ} {u v : Finset (Pt s)} (huv : u ⊆ v) :
    affRank u ≤ affRank v := by
  unfold affRank
  have hcard : u.card ≤ v.card := Finset.card_le_card huv
  by_cases hu0 : u = ∅
  · rw [if_pos hu0]; exact Nat.zero_le _
  · rw [if_neg hu0]
    have hv0 : v ≠ ∅ := fun hv => hu0 (Finset.subset_empty.mp (hv ▸ huv))
    rw [if_neg hv0]
    by_cases hu1 : u.card = 1
    · rw [if_pos hu1]; split_ifs <;> omega
    · rw [if_neg hu1]
      have hupos : 0 < u.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hu0)
      have hv1 : v.card ≠ 1 := by omega
      rw [if_neg hv1]
      by_cases hul : ∃ d c, ∀ w ∈ u, evalDir d w.1 = c
      · rw [if_pos hul]; split_ifs <;> omega
      · rw [if_neg hul]
        have hvl : ¬ ∃ d c, ∀ w ∈ v, evalDir d w.1 = c := by
          rintro ⟨d, c, hdc⟩; exact hul ⟨d, c, fun w hw => hdc w (huv hw)⟩
        rw [if_neg hvl]

private lemma insert_empty_singleton {α : Type*} (p : α) : insert p (∅ : Finset α) = {p} := by
  ext x; simp

private lemma gAff_of_sep_line {s : ℕ} (x : Finset (Pt s)) (p : Pt s)
    (d : Option (FieldQ s)) (c : FieldQ s)
    (hx : ∀ u ∈ x, evalDir d u.1 = c) (hp : evalDir d p.1 ≠ c) :
    gAff x p = true := by
  unfold gAff
  rw [decide_eq_true_eq]
  have hpni : p ∉ x := fun hmem => hp (hx p hmem)
  by_cases h0 : x = ∅
  · subst h0
    have h1 : affRank (∅ : Finset (Pt s)) = 0 := by unfold affRank; simp
    have h2 : affRank ({p} : Finset (Pt s)) = 1 := by unfold affRank; simp
    have hins : insert p (∅ : Finset (Pt s)) = {p} := by ext z; simp
    rw [h1, hins, h2]; omega
  · by_cases h1 : x.card = 1
    · have hr1 : affRank x = 1 := by
        unfold affRank; rw [if_neg h0, if_pos h1]
      have hcard2 : (insert p x).card = 2 := by rw [Finset.card_insert_of_notMem hpni, h1]
      rcases Finset.card_eq_one.mp h1 with ⟨u, rfl⟩
      have hne : p ≠ u := fun h => hpni (by simp [h])
      rcases (two_pts_unique_line p u hne).exists with ⟨⟨d', c'⟩, h1', h2'⟩
      have hr2 : affRank (insert p {u}) = 2 := by
        unfold affRank
        have hex : ∃ d c, ∀ w ∈ (insert p {u} : Finset (Pt s)), evalDir d w.1 = c :=
          ⟨d', c', fun w hw => by
            rcases Finset.mem_insert.mp hw with rfl | hw'
            · exact h1'
            · simp at hw'; subst hw'; exact h2'⟩
        rw [if_neg (Finset.insert_ne_empty _ _), if_neg (by omega), if_pos hex]
      rw [hr1, hr2]; omega
    · have hge2 : 2 ≤ x.card := by
        have hpos : 0 < x.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h0)
        omega
      have hr2 : affRank x = 2 := by
        unfold affRank
        rw [if_neg h0, if_neg h1,
          if_pos ⟨d, c, hx⟩]
      have hr3 : affRank (insert p x) = 3 := by
        unfold affRank
        have hcard3 : (insert p x).card = x.card + 1 := Finset.card_insert_of_notMem hpni
        rw [if_neg (Finset.insert_ne_empty _ _),
          if_neg (by omega), if_neg]
        rintro ⟨d', c', hdc'⟩
        rcases Finset.one_lt_card.mp (by omega : 1 < x.card) with ⟨u1, hu1, u2, hu2, hne⟩
        have huniq := (two_pts_unique_line u1 u2 hne).unique (y₁ := (d', c')) (y₂ := (d, c))
          ⟨hdc' u1 (Finset.mem_insert_of_mem hu1), hdc' u2 (Finset.mem_insert_of_mem hu2)⟩
          ⟨hx u1 hu1, hx u2 hu2⟩
        have hdEq : d' = d := congrArg Prod.fst huniq
        have hcEq : c' = c := congrArg Prod.snd huniq
        subst hdEq; subst hcEq
        exact hp (hdc' p (Finset.mem_insert_self p x))
      rw [hr2, hr3]; omega

private lemma gAff_fits {s : ℕ} :
    (∀ (x : Finset (Pt s)) (p : Pt s), (∀ u ∈ x, adjPt u p) → gAff x p = true) ∧
    (∀ (x : Finset (Pt s)) (p : Pt s), p ∈ x → gAff x p = false) := by
  constructor
  · intro x p hall
    by_cases hb : p.1.2 = 0
    · have ha : p.1.1 ≠ 0 := fun h => p.2 (Prod.ext h hb)
      refine gAff_of_sep_line x p none p.1.1⁻¹ ?_ ?_
      · intro u hu
        have hadj := hall u hu
        unfold adjPt at hadj
        rw [hb, mul_zero, zero_add] at hadj
        dsimp only [evalDir]
        calc u.1.2 = (p.1.1⁻¹ * p.1.1) * u.1.2 := by rw [inv_mul_cancel₀ ha, one_mul]
          _ = p.1.1⁻¹ * (u.1.2 * p.1.1) := by ring
          _ = p.1.1⁻¹ * 1 := by rw [hadj]
          _ = p.1.1⁻¹ := mul_one _
      · dsimp only [evalDir]; rw [hb]; exact (inv_ne_zero ha).symm
    · refine gAff_of_sep_line x p (some (p.1.1 * p.1.2⁻¹)) p.1.2⁻¹ ?_ ?_
      · intro u hu
        have hadj := hall u hu
        unfold adjPt at hadj
        dsimp only [evalDir]
        calc u.1.1 + p.1.1 * p.1.2⁻¹ * u.1.2
            = (u.1.1 * p.1.2 + u.1.2 * p.1.1) * p.1.2⁻¹ := by
                rw [add_mul, mul_assoc u.1.1 p.1.2 p.1.2⁻¹, mul_inv_cancel₀ hb, mul_one]; ring
          _ = 1 * p.1.2⁻¹ := by rw [hadj]
          _ = p.1.2⁻¹ := one_mul _
      · dsimp only [evalDir]
        have h1 : p.1.1 + p.1.1 * p.1.2⁻¹ * p.1.2 = 0 := by
          rw [mul_assoc, inv_mul_cancel₀ hb, mul_one]; exact fieldQ_add_self s _
        rw [h1]; exact (inv_ne_zero hb).symm
  · intro x p hp
    unfold gAff
    rw [Finset.insert_eq_of_mem hp]
    simp

private lemma gAff_iff {s : ℕ} (x : Finset (Pt s)) (p : Pt s) :
    gAff x p = true ↔
      affRank x = 0 ∨
      (affRank x = 1 ∧ ∃ u ∈ x, u ≠ p) ∨
      (affRank x = 2 ∧ ∀ d : Option (FieldQ s), ∃ u ∈ x, evalDir d u.1 ≠ evalDir d p.1) := by
  constructor
  · intro hg
    unfold gAff at hg
    rw [decide_eq_true_eq] at hg
    have hpni : p ∉ x := by
      intro hmem; rw [Finset.insert_eq_of_mem hmem] at hg; omega
    have hrle := affRank_le_three (insert p x)
    by_cases h0 : x = ∅
    · left; subst h0; unfold affRank; simp
    · by_cases h1 : x.card = 1
      · right; left
        refine ⟨by unfold affRank; rw [if_neg h0, if_pos h1], ?_⟩
        rcases Finset.card_eq_one.mp h1 with ⟨u, rfl⟩
        exact ⟨u, Finset.mem_singleton_self u, fun h => hpni (by simp [h])⟩
      · by_cases h2 : ∃ d c, ∀ u ∈ x, evalDir d u.1 = c
        · right; right
          have hr2 : affRank x = 2 := by
            unfold affRank
            rw [if_neg h0, if_neg h1,
              if_pos h2]
          refine ⟨hr2, ?_⟩
          intro d
          by_contra hall
          push Not at hall
          have hsub : ∀ u ∈ insert p x, evalDir d u.1 = evalDir d p.1 := by
            intro u hu
            rcases Finset.mem_insert.mp hu with rfl | hu'
            · rfl
            · exact hall u hu'
          have hcard2 : (insert p x).card = x.card + 1 := Finset.card_insert_of_notMem hpni
          have hpos : 0 < x.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h0)
          have hr_ins : affRank (insert p x) = 2 := by
            unfold affRank
            rw [if_neg (Finset.insert_ne_empty _ _),
              if_neg (by omega),
              if_pos ⟨d, evalDir d p.1, hsub⟩]
          omega
        · have hr3 : affRank x = 3 := by
            unfold affRank
            rw [if_neg h0, if_neg h1,
              if_neg h2]
          omega
  · rintro (h0 | ⟨h1, u, hu, hne⟩ | ⟨h2, hall⟩)
    · have hemp : x = ∅ := by
        by_contra hne'; unfold affRank at h0
        rw [if_neg hne'] at h0; split_ifs at h0 <;> omega
      subst hemp
      have hins : insert p (∅ : Finset (Pt s)) = {p} := by ext z; simp
      unfold gAff; rw [decide_eq_true_eq, hins]
      have ha0 : affRank (∅ : Finset (Pt s)) = 0 := by unfold affRank; simp
      have ha1 : affRank ({p} : Finset (Pt s)) = 1 := by unfold affRank; simp
      omega
    · have hcard1 : x.card = 1 := by
        by_contra hne1; unfold affRank at h1
        by_cases h0 : x = ∅
        · rw [if_pos h0] at h1; omega
        · rw [if_neg h0, if_neg hne1] at h1; split_ifs at h1 <;> omega
      rcases Finset.card_eq_one.mp hcard1 with ⟨u0, rfl⟩
      simp only [Finset.mem_singleton] at hu; subst hu
      have hpni : p ∉ ({u} : Finset (Pt s)) := by simp [hne.symm]
      rcases (two_pts_unique_line p u hne.symm).exists with ⟨⟨d', c'⟩, h1', h2'⟩
      unfold gAff; rw [decide_eq_true_eq, h1]
      have hr2 : affRank (insert p {u}) = 2 := by
        unfold affRank
        have hex : ∃ d c, ∀ w ∈ (insert p {u} : Finset (Pt s)), evalDir d w.1 = c :=
          ⟨d', c', fun w hw => by
            rcases Finset.mem_insert.mp hw with rfl | hw'
            · exact h1'
            · simp at hw'; subst hw'; exact h2'⟩
        rw [if_neg (Finset.insert_ne_empty _ _),
          if_neg (by rw [Finset.card_insert_of_notMem hpni]; simp),
          if_pos hex]
      omega
    · have hlin : ∃ d c, ∀ u ∈ x, evalDir d u.1 = c := by
        by_contra hnol; unfold affRank at h2
        by_cases h0 : x = ∅
        · rw [if_pos h0] at h2; omega
        · by_cases h1 : x.card = 1
          · rw [if_neg h0, if_pos h1] at h2; omega
          · rw [if_neg h0, if_neg h1, if_neg hnol] at h2; omega
      rcases hlin with ⟨d, c, hdc⟩
      rcases hall d with ⟨u, hu, hune⟩
      have hpc : evalDir d p.1 ≠ c := fun h => hune ((hdc u hu).trans h.symm)
      exact gAff_of_sep_line x p d c hdc hpc

private lemma gAff_antimono {s : ℕ} {x y : Finset (Pt s)} (hxy : x ⊆ y) (p : Pt s)
    (hy : gAff y p = true) : gAff x p = true := by
  rcases (gAff_iff y p).mp hy with h0 | ⟨h1, u, hu, hne⟩ | ⟨h2, hall⟩
  · have hemp : y = ∅ := by
      by_contra h; unfold affRank at h0
      rw [if_neg h] at h0; split_ifs at h0 <;> omega
    subst hemp; rw [Finset.subset_empty] at hxy; subst hxy; exact hy
  · have hcard1 : y.card = 1 := by
      by_contra hne1; unfold affRank at h1
      by_cases h0 : y = ∅
      · rw [if_pos h0] at h1; omega
      · rw [if_neg h0, if_neg hne1] at h1; split_ifs at h1 <;> omega
    rcases Finset.card_eq_one.mp hcard1 with ⟨u0, rfl⟩
    simp only [Finset.mem_singleton] at hu; subst hu
    rcases Finset.subset_singleton_iff.mp hxy with rfl | rfl
    · exact (gAff_iff ∅ p).mpr (Or.inl (by unfold affRank; simp))
    · exact hy
  · have hlin : ∃ d c, ∀ u ∈ y, evalDir d u.1 = c := by
      by_contra hnol; unfold affRank at h2
      by_cases h0 : y = ∅
      · rw [if_pos h0] at h2; omega
      · by_cases h1 : y.card = 1
        · rw [if_neg h0, if_pos h1] at h2; omega
        · rw [if_neg h0, if_neg h1, if_neg hnol] at h2; omega
    rcases hlin with ⟨d, c, hdc⟩
    rcases hall d with ⟨u, hu, hune⟩
    have hpc : evalDir d p.1 ≠ c := fun h => hune ((hdc u hu).trans h.symm)
    exact gAff_of_sep_line x p d c (fun w hw => hdc w (hxy hw)) hpc

private lemma gAff_not_runs4 {s : ℕ} [Fintype (FieldQ s)] : ¬ runsAux (@gAff s) 4 Finset.univ := by
  have hle : ∀ k x, runsAux (@gAff s) k x → k ≤ affRank x := by
    intro k
    induction k with
    | zero => intro _ _; exact Nat.zero_le _
    | succ k ih =>
      intro x hx
      rcases hx with ⟨u, v, p, hru, huv, hvx, hgu, hgv⟩
      have h1 := ih u hru
      have h2 := affRank_mono huv
      have h3 := affRank_mono hvx
      have hne : affRank u ≠ affRank v := by
        intro heq
        rcases (gAff_iff u p).mp hgu with h0 | ⟨h1', w, hw, hne'⟩ | ⟨h2', hall⟩
        · have hv0 : affRank v = 0 := heq.symm.trans h0
          have : gAff v p = true := (gAff_iff v p).mpr (Or.inl hv0)
          rw [hgv] at this; cases this
        · have hv1 : affRank v = 1 := heq.symm.trans h1'
          have : gAff v p = true := (gAff_iff v p).mpr (Or.inr (Or.inl ⟨hv1, w, huv hw, hne'⟩))
          rw [hgv] at this; cases this
        · have hv2 : affRank v = 2 := heq.symm.trans h2'
          have : gAff v p = true :=
            (gAff_iff v p).mpr (Or.inr (Or.inr ⟨hv2, fun d => let ⟨w, hw, hne'⟩ := hall d; ⟨w, huv hw, hne'⟩⟩))
          rw [hgv] at this; cases this
      omega
  intro h4
  have h1 := hle 4 Finset.univ h4
  have h2 := affRank_le_three (Finset.univ : Finset (Pt s))
  omega

private lemma mon_size_bound {q n : ℕ} (hqn : q ≤ n) :
    (q + 1) * n + 3 * q * (q + 1) + 3 * n + n + n + n + (q + 1) * q + 5 + (q + 5) * n ≤
      12 * (q + 1) * (n + 1) := by
  have hq4 : 4 * q * (q + 1) ≤ 4 * n * (q + 1) :=
    Nat.mul_le_mul_right (q + 1) (Nat.mul_le_mul_left 4 hqn)
  nlinarith

-- Build the 2-NOT circuit for gAff transferred along ePt : Pt s ≃ Fin n
set_option maxHeartbeats 1200000 in
private lemma exists_gAff_circuit (s : ℕ) [Fintype (FieldQ s)] (hs : 1 ≤ s) :
    let rootQ := 2 ^ s
    let q := rootQ * rootQ
    let n := q * q - 1
    ∀ (ePt : Pt s ≃ Fin n),
      ∃ (C : Circuit) (tap : Fin n → Fin (n + 2 + C.size)),
        FanInTwo C ∧ ReadsBack (n + 2) C ∧ C.output < n + 2 + C.size ∧
        notCount C = 2 ∧ C.size - notCount C ≤ 12 * (q + 1) * (n + 1) ∧
        ∀ (x : Finset (Fin n)) (j : Fin n),
          (C.wires (List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true])).getD (tap j).val false =
            gAff (x.map ePt.symm.toEmbedding) (ePt.symm j) := by
  intro rootQ q n ePt
  have hq_ge : 4 ≤ q := by
    have hr : 2 ≤ rootQ := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ s := Nat.pow_le_pow_right (by omega) hs
    dsimp only [q]; nlinarith
  have hn_pos : 0 < n := by
    dsimp only [n]
    have : 16 ≤ q * q := by nlinarith
    omega
  let eDir : Option (FieldQ s) ≃ Fin (q + 1) :=
    (Fintype.equivFin (Option (FieldQ s))).trans
      (finCongr (by rw [Fintype.card_option, fieldQ_card s hs]))
  let eVal : FieldQ s ≃ Fin q :=
    (Fintype.equivFin (FieldQ s)).trans (finCongr (fieldQ_card s hs))
  let B0 := Builder.empty n
  have hB0_eval : ∀ (x : Finset (Fin n)) (i : Fin n),
      B0.eval (List.ofFn (fun k : Fin n => decide (k ∈ x)) ++ [false, true]) i.val = decide (i ∈ x) := by
    intro x i
    dsimp only [B0]; rw [Builder.eval_empty]
    simp only [List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by simp : i.val < (List.ofFn (fun k : Fin n => decide (k ∈ x))).length),
      List.getElem?_ofFn, dite_eq_left i.isLt, Option.getD_some]
  -- Step 1: inLine(d, c) = OR_{p : evalDir d p = c} x_p, total <= (q+1)*n gates
  have hstep1 :
      ∃ (B1 : Builder n) (inLine : Fin (q + 1) → Fin q → ℕ),
        Extends B0 B1 ∧ (∀ d c, inLine d c < n + 2 + B1.gates.length) ∧
        B1.nots = 0 ∧ B1.monos ≤ (q + 1) * n ∧
        ∀ (x : Finset (Fin n)) (d : Fin (q + 1)) (c : Fin q),
          B1.eval (List.ofFn (fun k : Fin n => decide (k ∈ x)) ++ [false, true]) (inLine d c) =
            decide (∃ i ∈ x, evalDir (eDir.symm d) (ePt.symm i).1 = eVal.symm c) := by
    have hdir : ∀ (d : Fin (q + 1)) (B : Builder n), Extends B0 B →
        ∃ (B' : Builder n) (wires : Fin q → ℕ),
          Extends B B' ∧ (∀ c, wires c < n + 2 + B'.gates.length) ∧
          B'.nots = B.nots ∧ B'.monos ≤ B.monos + n ∧
          ∀ (x : Finset (Fin n)) (c : Fin q),
            B'.eval (List.ofFn (fun k : Fin n => decide (k ∈ x)) ++ [false, true]) (wires c) =
              decide (∃ i ∈ x, evalDir (eDir.symm d) (ePt.symm i).1 = eVal.symm c) := by
      intro d B hEB
      let bucket : Fin q → List ℕ := fun c =>
        ((List.finRange n).filter (fun i => decide (evalDir (eDir.symm d) (ePt.symm i).1 = eVal.symm c))).map Fin.val
      have hsum_len : (∑ c : Fin q, (bucket c).length) = n := by
        have hcard : ∀ c : Fin q, (bucket c).length =
            ((Finset.univ : Finset (Fin n)).filter
              (fun i => evalDir (eDir.symm d) (ePt.symm i).1 = eVal.symm c)).card := by
          intro c
          dsimp only [bucket]
          rw [List.length_map, ← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _)]
          congr 1; ext i; simp [List.mem_filter, List.mem_finRange]
        rw [Finset.sum_congr rfl (fun c _ => hcard c)]
        simp only [Finset.card_filter]
        rw [Finset.sum_comm]
        have h1 : ∀ i : Fin n,
            (∑ c : Fin q, if evalDir (eDir.symm d) (ePt.symm i).1 = eVal.symm c then 1 else 0) = 1 := by
          intro i
          rw [Finset.sum_eq_single (eVal (evalDir (eDir.symm d) (ePt.symm i).1))]
          · simp
          · intro c _ hne; rw [if_neg]; intro h; apply hne; rw [h, Equiv.apply_symm_apply]
          · intro hni; exact absurd (Finset.mem_univ _) hni
        rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul, mul_one]
      have hiter : ∀ (k : ℕ) (hk : k ≤ q),
          ∃ (Bk : Builder n) (wires : Fin k → ℕ),
            Extends B Bk ∧ (∀ c, wires c < n + 2 + Bk.gates.length) ∧
            Bk.nots = B.nots ∧
            Bk.monos ≤ B.monos + ∑ c : Fin k, (bucket ⟨c.val, by omega⟩).length ∧
            ∀ (x : Finset (Fin n)) (c : Fin k),
              Bk.eval (List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true]) (wires c) =
                decide (∃ i ∈ x, evalDir (eDir.symm d) (ePt.symm i).1 = eVal.symm ⟨c.val, by omega⟩) := by
        intro k
        induction k with
        | zero =>
          intro _
          exact ⟨B, fun c => Fin.elim0 c, Extends.refl B, fun c => Fin.elim0 c, rfl, by simp,
            fun _ c => Fin.elim0 c⟩
        | succ k ih =>
          intro hk
          rcases ih (by omega) with ⟨Bk, wk, hEk, hltk, hnk, hmk, hevk⟩
          let ck : Fin q := ⟨k, by omega⟩
          have hws : ∀ w ∈ bucket ck, w < n + 2 + Bk.gates.length := by
            intro w hw
            rcases List.mem_map.mp hw with ⟨i, _, rfl⟩
            omega
          rcases exists_or_list (bucket ck) Bk hws with ⟨Bk', outNew, hEnew, hltnew, hnnew, hmnew, hevnew⟩
          let wk' : Fin (k + 1) → ℕ := fun c => if hc : c.val < k then wk ⟨c.val, hc⟩ else outNew
          refine ⟨Bk', wk', hEk.trans hEnew, ?_, hnnew.trans hnk, ?_, ?_⟩
          · intro c; dsimp only [wk']; split_ifs with hc
            · have := hltk ⟨c.val, hc⟩; have := hEnew.1; omega
            · exact hltnew
          · rw [Fin.sum_univ_castSucc]
            have hsc : (∑ c : Fin k, (bucket ⟨(Fin.castSucc c).val, by omega⟩).length) =
                ∑ c : Fin k, (bucket ⟨c.val, by omega⟩).length := Finset.sum_congr rfl (fun _ _ => rfl)
            have hlast : (⟨(Fin.last k).val, by omega⟩ : Fin q) = ck := by ext; rfl
            rw [hsc, hlast]; omega
          · intro x c
            dsimp only [wk']
            let inp := List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true]
            have hinp : inp.length = n + 2 := by simp [inp]
            have hn0 : inp.getD n false = false := by
              simp [inp, List.getD_eq_getElem?_getD, List.getElem?_append_right]
            split_ifs with hc
            · rw [hEnew.2 inp hinp _ (hltk ⟨c.val, hc⟩), hevk x ⟨c.val, hc⟩]
            · have hck : c.val = k := by omega
              rw [hevnew inp hinp hn0]
              rw [Bool.eq_iff_iff]
              simp only [List.any_eq_true, decide_eq_true_eq, bucket, List.mem_map, List.mem_filter,
                List.mem_finRange, true_and]
              constructor
              · rintro ⟨w, ⟨i, hi, rfl⟩, hbw⟩
                have h0 := (hEB.trans hEk).2 inp hinp i.val (by simp [B0]; omega)
                rw [h0, hB0_eval] at hbw
                have hcEq : (⟨c.val, by omega⟩ : Fin q) = ck := by ext; exact hck
                rw [hcEq]
                exact ⟨i, of_decide_eq_true hbw, hi⟩
              · rintro ⟨i, hi, heq⟩
                have hcEq : (⟨c.val, by omega⟩ : Fin q) = ck := by ext; exact hck
                rw [hcEq] at heq
                refine ⟨i.val, ⟨i, heq, rfl⟩, ?_⟩
                rw [(hEB.trans hEk).2 inp hinp i.val (by simp [B0]; omega), hB0_eval]
                exact decide_eq_true hi
      rcases hiter q le_rfl with ⟨Bq, wq, hEq, hltq, hnq, hmq, hevq⟩
      refine ⟨Bq, wq, hEq, hltq, hnq, ?_, hevq⟩
      have hsum_eq : (∑ c : Fin q, (bucket ⟨c.val, c.isLt⟩).length) = n := hsum_len
      omega
    have hall_dir : ∀ (k : ℕ) (hk : k ≤ q + 1),
        ∃ (Bk : Builder n) (wires : Fin k → Fin q → ℕ),
          Extends B0 Bk ∧ (∀ d c, wires d c < n + 2 + Bk.gates.length) ∧
          Bk.nots = 0 ∧ Bk.monos ≤ k * n ∧
          ∀ (x : Finset (Fin n)) (d : Fin k) (c : Fin q),
            Bk.eval (List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true]) (wires d c) =
              decide (∃ i ∈ x, evalDir (eDir.symm ⟨d.val, by omega⟩) (ePt.symm i).1 = eVal.symm c) := by
      intro k
      induction k with
      | zero =>
        intro _
        exact ⟨B0, fun d => Fin.elim0 d, Extends.refl B0, fun d => Fin.elim0 d, rfl,
          by simp [B0, Builder.empty, Builder.monos], fun _ d => Fin.elim0 d⟩
      | succ k ih =>
        intro hk
        rcases ih (by omega) with ⟨Bk, wk, hEk, hltk, hnk, hmk, hevk⟩
        rcases hdir ⟨k, by omega⟩ Bk hEk with ⟨Bk', wNew, hEnew, hltnew, hnnew, hmnew, hevnew⟩
        let wk' : Fin (k + 1) → Fin q → ℕ := fun d => if hd : d.val < k then wk ⟨d.val, hd⟩ else wNew
        refine ⟨Bk', wk', hEk.trans hEnew, ?_, by omega, ?_, ?_⟩
        · intro d c; dsimp only [wk']; split_ifs with hd
          · have := hltk ⟨d.val, hd⟩ c; have := hEnew.1; omega
          · exact hltnew c
        · have : (k + 1) * n = k * n + n := by ring
          omega
        · intro x d c
          dsimp only [wk']
          let inp := List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true]
          have hinp : inp.length = n + 2 := by simp [inp]
          split_ifs with hd
          · rw [hEnew.2 inp hinp _ (hltk ⟨d.val, hd⟩ c), hevk x ⟨d.val, hd⟩ c]
          · have hdk : d.val = k := by omega
            have hdEq : (⟨d.val, by omega⟩ : Fin (q + 1)) = ⟨k, by omega⟩ := by ext; exact hdk
            rw [hdEq]; exact hevnew x c
    exact hall_dir (q + 1) le_rfl
  rcases hstep1 with ⟨B1, inLine, hE1, hlt1, hn1, hm1, hev1⟩
  -- Step 2: outLine(d, c) = OR_{c' ≠ c} inLine(d, c') using 3*q gates per d
  have hstep2 :
      ∃ (B2 : Builder n) (outLine : Fin (q + 1) → Fin q → ℕ),
        Extends B1 B2 ∧ (∀ d c, outLine d c < n + 2 + B2.gates.length) ∧
        B2.nots = 0 ∧ B2.monos ≤ B1.monos + 3 * q * (q + 1) ∧
        ∀ (x : Finset (Fin n)) (d : Fin (q + 1)) (c : Fin q),
          B2.eval (List.ofFn (fun k : Fin n => decide (k ∈ x)) ++ [false, true]) (outLine d c) =
            decide (∃ i ∈ x, evalDir (eDir.symm d) (ePt.symm i).1 ≠ eVal.symm c) := by
    have hall : ∀ (k : ℕ) (hk : k ≤ q + 1),
        ∃ (Bk : Builder n) (outL : Fin k → Fin q → ℕ),
          Extends B1 Bk ∧ (∀ d c, outL d c < n + 2 + Bk.gates.length) ∧
          Bk.nots = 0 ∧ Bk.monos ≤ B1.monos + 3 * q * k ∧
          ∀ (x : Finset (Fin n)) (d : Fin k) (c : Fin q),
            Bk.eval (List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true]) (outL d c) =
              decide (∃ i ∈ x, evalDir (eDir.symm ⟨d.val, by omega⟩) (ePt.symm i).1 ≠ eVal.symm c) := by
      intro k
      induction k with
      | zero =>
        intro _
        exact ⟨B1, fun d => Fin.elim0 d, Extends.refl B1, fun d => Fin.elim0 d, hn1, by simp,
          fun _ d => Fin.elim0 d⟩
      | succ k ih =>
        intro hk
        rcases ih (by omega) with ⟨Bk, outk, hEk, hltk, hnk, hmk, hevk⟩
        let dk : Fin (q + 1) := ⟨k, by omega⟩
        have hws : ∀ c : Fin q, inLine dk c < n + 2 + Bk.gates.length := fun c => by
          have := hlt1 dk c; have := hEk.1; omega
        rcases exists_leaveOneOut_or Bk (inLine dk) hws with ⟨Bk', outNew, hEnew, hltnew, hnnew, hmnew, hevnew⟩
        let outk' : Fin (k + 1) → Fin q → ℕ := fun d => if hd : d.val < k then outk ⟨d.val, hd⟩ else outNew
        refine ⟨Bk', outk', hEk.trans hEnew, ?_, by omega, ?_, ?_⟩
        · intro d c; dsimp only [outk']; split_ifs with hd
          · have := hltk ⟨d.val, hd⟩ c; have := hEnew.1; omega
          · exact hltnew c
        · have : 3 * q * (k + 1) = 3 * q * k + 3 * q := by ring
          omega
        · intro x d c
          dsimp only [outk']
          let inp := List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true]
          have hinp : inp.length = n + 2 := by simp [inp]
          have hn0 : inp.getD n false = false := by
            simp [inp, List.getD_eq_getElem?_getD, List.getElem?_append_right]
          split_ifs with hd
          · rw [hEnew.2 inp hinp _ (hltk ⟨d.val, hd⟩ c), hevk x ⟨d.val, hd⟩ c]
          · have hdk : d.val = k := by omega
            rw [hevnew inp hinp hn0 c]
            rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]
            have hdEq : (⟨d.val, by omega⟩ : Fin (q + 1)) = dk := by ext; exact hdk
            rw [hdEq]
            constructor
            · rintro ⟨c', hc'ne, hbc'⟩
              rw [hEk.2 inp hinp _ (hlt1 dk c'), hev1 x dk c'] at hbc'
              rcases of_decide_eq_true hbc' with ⟨i, hi, heq⟩
              refine ⟨i, hi, ?_⟩
              rw [heq]
              intro hEq; exact hc'ne (eVal.symm.injective hEq)
            · rintro ⟨i, hi, hne⟩
              let c' := eVal (evalDir (eDir.symm dk) (ePt.symm i).1)
              refine ⟨c', fun h => hne (by rw [← h]; exact (eVal.symm_apply_apply _).symm), ?_⟩
              rw [hEk.2 inp hinp _ (hlt1 dk c'), hev1 x dk c']
              exact decide_eq_true ⟨i, hi, (eVal.symm_apply_apply _).symm⟩
    exact hall (q + 1) le_rfl
  rcases hstep2 with ⟨B2, outLine, hE2, hlt2, hn2, hm2, hev2⟩
  -- Step 3: outPt, T1, T2, T3
  have hwsPt : ∀ i : Fin n, i.val < n + 2 + B2.gates.length := fun i => by omega
  rcases exists_leaveOneOut_or B2 (fun i : Fin n => i.val) hwsPt with
    ⟨B3, outPt, hE3, hlt3, hn3, hm3, hev3⟩
  have hT1_ws : ∀ w ∈ (List.finRange n).map Fin.val, w < n + 2 + B3.gates.length := by
    intro w hw; rcases List.mem_map.mp hw with ⟨i, _, rfl⟩; omega
  rcases exists_or_list ((List.finRange n).map Fin.val) B3 hT1_ws with
    ⟨B3', wT1, hET1, hltT1, hnT1, hmT1, hevT1⟩
  have hstepT2pairs :
      ∃ (B4 : Builder n) (pairW : Fin n → ℕ),
        Extends B3' B4 ∧ (∀ i, pairW i < n + 2 + B4.gates.length) ∧
        B4.nots = 0 ∧ B4.monos ≤ B3'.monos + n ∧
        ∀ (x : Finset (Fin n)) (i : Fin n),
          B4.eval (List.ofFn (fun k : Fin n => decide (k ∈ x)) ++ [false, true]) (pairW i) =
            decide (i ∈ x ∧ ∃ j ∈ x, j ≠ i) := by
    have hall : ∀ (k : ℕ) (hk : k ≤ n),
        ∃ (Bk : Builder n) (pw : Fin k → ℕ),
          Extends B3' Bk ∧ (∀ i, pw i < n + 2 + Bk.gates.length) ∧
          Bk.nots = 0 ∧ Bk.monos ≤ B3'.monos + k ∧
          ∀ (x : Finset (Fin n)) (i : Fin k),
            Bk.eval (List.ofFn (fun j : Fin n => decide (j ∈ x)) ++ [false, true]) (pw i) =
              decide (⟨i.val, by omega⟩ ∈ x ∧ ∃ j ∈ x, j ≠ ⟨i.val, by omega⟩) := by
      intro k
      induction k with
      | zero =>
        intro _
        exact ⟨B3', fun i => Fin.elim0 i, Extends.refl _, fun i => Fin.elim0 i,
          by omega, by simp, fun _ i => Fin.elim0 i⟩
      | succ k ih =>
        intro hk
        rcases ih (by omega) with ⟨Bk, pwk, hEk, hltk, hnk, hmk, hevk⟩
        let ik : Fin n := ⟨k, by omega⟩
        have hwi : ik.val < n + 2 + Bk.gates.length := by omega
        have hwo : outPt ik < n + 2 + Bk.gates.length := by
          have := hlt3 ik; have := hET1.1; have := hEk.1; omega
        set res := pushBin Bk GateOp.and (Or.inl rfl) ik.val (outPt ik) hwi hwo
        have hsp := pushBin_spec Bk GateOp.and (Or.inl rfl) ik.val (outPt ik) hwi hwo
        have hEres : Extends Bk res.1 := hsp.1
        have hltres : res.2 < n + 2 + res.1.gates.length := hsp.2.1
        have hnres : res.1.nots = Bk.nots := hsp.2.2.1
        have hmres : res.1.monos = Bk.monos + 1 := hsp.2.2.2.1
        let pwk' : Fin (k + 1) → ℕ := fun i => if hi : i.val < k then pwk ⟨i.val, hi⟩ else res.2
        refine ⟨res.1, pwk', hEk.trans hEres, ?_, by omega, by omega, ?_⟩
        · intro i; dsimp only [pwk']; split_ifs with hi
          · have := hltk ⟨i.val, hi⟩; have := hEres.1; omega
          · exact hltres
        · intro x i
          dsimp only [pwk']
          let inp := List.ofFn (fun j : Fin n => decide (j ∈ x)) ++ [false, true]
          have hinp : inp.length = n + 2 := by simp [inp]
          have hn0 : inp.getD n false = false := by
            simp [inp, List.getD_eq_getElem?_getD, List.getElem?_append_right]
          split_ifs with hi
          · rw [hEres.2 inp hinp _ (hltk ⟨i.val, hi⟩), hevk x ⟨i.val, hi⟩]
          · have hik : i.val = k := by omega
            rw [hsp.2.2.2.2 inp hinp]
            simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
            rw [(hE1.trans (hE2.trans (hE3.trans (hET1.trans hEk)))).2 inp hinp ik.val (by simp [B0]; omega),
              hB0_eval x ik,
              (hET1.trans hEk).2 inp hinp (outPt ik) (hlt3 ik),
              hev3 inp hinp hn0 ik]
            have hsub : ∀ j : Fin n, B2.eval inp j.val = decide (j ∈ x) := fun j => by
              rw [(hE1.trans hE2).2 inp hinp j.val (by simp [B0]; omega), hB0_eval x j]
            rw [Bool.eq_iff_iff]
            simp only [hsub, Bool.and_eq_true, decide_eq_true_eq]
            have hiEq : (⟨i.val, by omega⟩ : Fin n) = ik := by ext; exact hik
            rw [hiEq]
            constructor
            · rintro ⟨h1, j, hne, hj⟩; exact ⟨h1, j, hj, hne⟩
            · rintro ⟨h1, j, hj, hne⟩; exact ⟨h1, j, hne, hj⟩
    exact hall n le_rfl
  rcases hstepT2pairs with ⟨B4, pairW, hE4, hlt4, hn4, hm4, hev4⟩
  have hT2_ws : ∀ w ∈ (List.finRange n).map pairW, w < n + 2 + B4.gates.length := by
    intro w hw; rcases List.mem_map.mp hw with ⟨i, _, rfl⟩; exact hlt4 i
  rcases exists_or_list ((List.finRange n).map pairW) B4 hT2_ws with
    ⟨B4', wT2, hET2, hltT2, hnT2, hmT2, hevT2⟩
  let allLines : List ℕ :=
    (List.finRange (q + 1)).flatMap (fun d => (List.finRange q).map (fun c => outLine d c))
  have hallLines_len : allLines.length = (q + 1) * q := by
    dsimp only [allLines]
    rw [List.length_flatMap]
    simp [List.map_const', List.sum_replicate, smul_eq_mul]
  have hT3_ws : ∀ w ∈ allLines, w < n + 2 + B4'.gates.length := by
    intro w hw
    rcases List.mem_flatMap.mp hw with ⟨d, _, hwc⟩
    rcases List.mem_map.mp hwc with ⟨c, _, rfl⟩
    have := hlt2 d c; have := hE3.1; have := hET1.1; have := hE4.1; have := hET2.1; omega
  rcases exists_and_list allLines B4' hT3_ws with ⟨B5, wT3, hET3, hltT3, hnT3, hmT3, hevT3⟩
  -- Step 4: 2-NOT decoder for E0, E1, E2 from T1, T2, T3
  have hwT1 : wT1 < n + 2 + B5.gates.length := by
    have := hE4.1; have := hET2.1; have := hET3.1; omega
  have hwT2 : wT2 < n + 2 + B5.gates.length := by
    have := hET3.1; omega
  have hwT3 : wT3 < n + 2 + B5.gates.length := hltT3
  set rNT2 := pushNot B5 wT2 hwT2
  have hsNT2 := pushNot_spec B5 wT2 hwT2
  have hE_NT2 : Extends B5 rNT2.1 := hsNT2.1
  have hlt_NT2 : rNT2.2 < n + 2 + rNT2.1.gates.length := hsNT2.2.1
  have hn_NT2 : rNT2.1.nots = B5.nots + 1 := hsNT2.2.2.1
  have hm_NT2 : rNT2.1.monos = B5.monos := hsNT2.2.2.2.1
  set rT1nT2 := pushBin rNT2.1 GateOp.and (Or.inl rfl) wT1 rNT2.2 (by have := hE_NT2.1; omega) hlt_NT2
  have hsT1nT2 := pushBin_spec rNT2.1 GateOp.and (Or.inl rfl) wT1 rNT2.2 (by have := hE_NT2.1; omega) hlt_NT2
  have hE_T1nT2 : Extends rNT2.1 rT1nT2.1 := hsT1nT2.1
  have hlt_T1nT2 : rT1nT2.2 < n + 2 + rT1nT2.1.gates.length := hsT1nT2.2.1
  have hn_T1nT2 : rT1nT2.1.nots = rNT2.1.nots := hsT1nT2.2.2.1
  have hm_T1nT2 : rT1nT2.1.monos = rNT2.1.monos + 1 := hsT1nT2.2.2.2.1
  set rOdd := pushBin rT1nT2.1 GateOp.or (Or.inr rfl) rT1nT2.2 wT3
    hlt_T1nT2 (by have := hE_NT2.1; have := hE_T1nT2.1; omega)
  have hsOdd := pushBin_spec rT1nT2.1 GateOp.or (Or.inr rfl) rT1nT2.2 wT3
    hlt_T1nT2 (by have := hE_NT2.1; have := hE_T1nT2.1; omega)
  have hE_Odd : Extends rT1nT2.1 rOdd.1 := hsOdd.1
  have hlt_Odd : rOdd.2 < n + 2 + rOdd.1.gates.length := hsOdd.2.1
  have hn_Odd : rOdd.1.nots = rT1nT2.1.nots := hsOdd.2.2.1
  have hm_Odd : rOdd.1.monos = rT1nT2.1.monos + 1 := hsOdd.2.2.2.1
  set rEven := pushNot rOdd.1 rOdd.2 hlt_Odd
  have hsEven := pushNot_spec rOdd.1 rOdd.2 hlt_Odd
  have hE_Even : Extends rOdd.1 rEven.1 := hsEven.1
  have hlt_Even : rEven.2 < n + 2 + rEven.1.gates.length := hsEven.2.1
  have hn_Even : rEven.1.nots = rOdd.1.nots + 1 := hsEven.2.2.1
  have hm_Even : rEven.1.monos = rOdd.1.monos := hsEven.2.2.2.1
  have hwNT2' : rNT2.2 < n + 2 + rEven.1.gates.length := by
    have := hE_T1nT2.1; have := hE_Odd.1; have := hE_Even.1; omega
  have hwOdd' : rOdd.2 < n + 2 + rEven.1.gates.length := by
    have := hE_Even.1; omega
  set rE0 := pushBin rEven.1 GateOp.and (Or.inl rfl) rEven.2 rNT2.2 hlt_Even hwNT2'
  have hsE0 := pushBin_spec rEven.1 GateOp.and (Or.inl rfl) rEven.2 rNT2.2 hlt_Even hwNT2'
  have hE_E0 : Extends rEven.1 rE0.1 := hsE0.1
  have hlt_E0 : rE0.2 < n + 2 + rE0.1.gates.length := hsE0.2.1
  have hn_E0 : rE0.1.nots = rEven.1.nots := hsE0.2.2.1
  have hm_E0 : rE0.1.monos = rEven.1.monos + 1 := hsE0.2.2.2.1
  set rE1 := pushBin rE0.1 GateOp.and (Or.inl rfl) rOdd.2 rNT2.2
    (by have := hE_E0.1; omega) (by have := hE_E0.1; omega)
  have hsE1 := pushBin_spec rE0.1 GateOp.and (Or.inl rfl) rOdd.2 rNT2.2
    (by have := hE_E0.1; omega) (by have := hE_E0.1; omega)
  have hE_E1 : Extends rE0.1 rE1.1 := hsE1.1
  have hlt_E1 : rE1.2 < n + 2 + rE1.1.gates.length := hsE1.2.1
  have hn_E1 : rE1.1.nots = rE0.1.nots := hsE1.2.2.1
  have hm_E1 : rE1.1.monos = rE0.1.monos + 1 := hsE1.2.2.2.1
  set rE2 := pushBin rE1.1 GateOp.and (Or.inl rfl) rEven.2 wT2
    (by have := hE_E0.1; have := hE_E1.1; omega)
    (by have := hE_NT2.1; have := hE_T1nT2.1; have := hE_Odd.1; have := hE_Even.1; have := hE_E0.1; have := hE_E1.1; omega)
  have hsE2 := pushBin_spec rE1.1 GateOp.and (Or.inl rfl) rEven.2 wT2
    (by have := hE_E0.1; have := hE_E1.1; omega)
    (by have := hE_NT2.1; have := hE_T1nT2.1; have := hE_Odd.1; have := hE_Even.1; have := hE_E0.1; have := hE_E1.1; omega)
  have hE_E2 : Extends rE1.1 rE2.1 := hsE2.1
  have hlt_E2 : rE2.2 < n + 2 + rE2.1.gates.length := hsE2.2.1
  have hn_E2 : rE2.1.nots = rE1.1.nots := hsE2.2.2.1
  have hm_E2 : rE2.1.monos = rE1.1.monos + 1 := hsE2.2.2.2.1
  let B6 := rE2.1
  have hE56 : Extends B5 B6 :=
    hE_NT2.trans (hE_T1nT2.trans (hE_Odd.trans (hE_Even.trans (hE_E0.trans (hE_E1.trans hE_E2)))))
  have hB6_nots : B6.nots = 2 := by
    dsimp only [B6]; omega
  have hB6_monos : B6.monos = B5.monos + 5 := by
    dsimp only [B6]; omega
  have hev_ranks : ∀ x : Finset (Fin n),
      let inp := List.ofFn (fun k : Fin n => decide (k ∈ x)) ++ [false, true]
      let sx := x.map ePt.symm.toEmbedding
      B6.eval inp rE0.2 = decide (affRank sx = 0) ∧
      B6.eval inp rE1.2 = decide (affRank sx = 1) ∧
      B6.eval inp rE2.2 = decide (affRank sx = 2) := by
    intro x inp sx
    have hinp : inp.length = n + 2 := by simp [inp]
    have hn0 : inp.getD n false = false := by
      simp [inp, List.getD_eq_getElem?_getD, List.getElem?_append_right]
    have hn1' : inp.getD (n + 1) false = true := by
      simp [inp, List.getD_eq_getElem?_getD, List.getElem?_append_right]
    have hT1_val : B5.eval inp wT1 = decide (1 ≤ affRank sx) := by
      rw [(hE4.trans (hET2.trans hET3)).2 inp hinp wT1 hltT1, hevT1 inp hinp hn0]
      rw [Bool.eq_iff_iff]
      simp only [List.any_eq_true, List.mem_map, List.mem_finRange, true_and, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨i, rfl⟩, hbi⟩
        rw [(hE1.trans (hE2.trans hE3)).2 inp hinp i.val (by simp [B0]; omega), hB0_eval x i] at hbi
        have hne : sx ≠ ∅ := Finset.Nonempty.ne_empty ⟨ePt.symm i, Finset.mem_map.mpr ⟨i, of_decide_eq_true hbi, rfl⟩⟩
        unfold affRank; rw [if_neg hne]; split_ifs <;> omega
      · intro hr1
        have hne : sx ≠ ∅ := by intro h; rw [h] at hr1; unfold affRank at hr1; simp at hr1
        rcases Finset.nonempty_iff_ne_empty.mpr hne with ⟨p, hp⟩
        rcases Finset.mem_map.mp hp with ⟨i, hi, _⟩
        refine ⟨i.val, ⟨i, rfl⟩, ?_⟩
        rw [(hE1.trans (hE2.trans hE3)).2 inp hinp i.val (by simp [B0]; omega), hB0_eval x i]
        exact decide_eq_true hi
    have hT2_val : B5.eval inp wT2 = decide (2 ≤ affRank sx) := by
      rw [hET3.2 inp hinp wT2 hltT2, hevT2 inp hinp hn0]
      rw [Bool.eq_iff_iff]
      simp only [List.any_eq_true, List.mem_map, List.mem_finRange, true_and, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨i, rfl⟩, hbi⟩
        rw [hev4 x i] at hbi
        rcases of_decide_eq_true hbi with ⟨hi, j, hj, hne⟩
        have hcard : 2 ≤ sx.card := by
          rw [Finset.card_map]
          have hlt := Finset.one_lt_card.mpr ⟨i, hi, j, hj, hne.symm⟩
          omega
        have hne0 : sx ≠ ∅ := by intro h; rw [h] at hcard; simp at hcard
        unfold affRank
        rw [if_neg hne0, if_neg (by omega)]
        split_ifs <;> omega
      · intro hr2
        have hcard : 1 < sx.card := by
          by_contra hle
          unfold affRank at hr2
          by_cases h0 : sx = ∅
          · rw [if_pos h0] at hr2; omega
          · have h1 : sx.card = 1 := by
              have hpos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h0); omega
            rw [if_neg h0, if_pos h1] at hr2; omega
        rw [Finset.card_map] at hcard
        rcases Finset.one_lt_card.mp hcard with ⟨i, hi, j, hj, hne⟩
        refine ⟨pairW i, ⟨i, rfl⟩, ?_⟩
        rw [hev4 x i]
        exact decide_eq_true ⟨hi, j, hj, hne.symm⟩
    have hT3_val : B5.eval inp wT3 = decide (3 ≤ affRank sx) := by
      rw [hevT3 inp hinp hn1']
      rw [Bool.eq_iff_iff]
      simp only [List.all_eq_true, allLines, List.mem_flatMap, List.mem_map, List.mem_finRange,
        true_and, decide_eq_true_eq]
      constructor
      · intro hall
        have hnol : ¬ ∃ d c, ∀ u ∈ sx, evalDir d u.1 = c := by
          rintro ⟨d, c, hdc⟩
          have hw := hall (outLine (eDir d) (eVal c)) ⟨eDir d, eVal c, rfl⟩
          rw [(hE3.trans (hET1.trans (hE4.trans hET2))).2 inp hinp _ (hlt2 _ _),
            hev2 x (eDir d) (eVal c)] at hw
          rcases of_decide_eq_true hw with ⟨i, hi, hne⟩
          simp only [Equiv.symm_apply_apply] at hne
          exact hne (hdc (ePt.symm i) (Finset.mem_map.mpr ⟨i, hi, rfl⟩))
        have hne0 : sx ≠ ∅ := by intro h; rw [h] at hnol; exact hnol ⟨none, 0, fun _ hu => by cases hu⟩
        have hne1 : sx.card ≠ 1 := by
          intro h1; rcases Finset.card_eq_one.mp h1 with ⟨u, hu⟩
          exact hnol ⟨none, evalDir none u.1, fun w hw => by rw [hu] at hw; simp at hw; subst hw; rfl⟩
        unfold affRank
        rw [if_neg hne0, if_neg hne1,
          if_neg hnol]
      · intro hr3 w hw
        rcases hw with ⟨d, c, rfl⟩
        rw [(hE3.trans (hET1.trans (hE4.trans hET2))).2 inp hinp _ (hlt2 _ _), hev2 x d c]
        rw [decide_eq_true_eq]
        by_contra hno
        push Not at hno
        have hlin : ∃ d' c', ∀ u ∈ sx, evalDir d' u.1 = c' := by
          refine ⟨eDir.symm d, eVal.symm c, fun u hu => ?_⟩
          rcases Finset.mem_map.mp hu with ⟨i, hi, rfl⟩
          exact hno i hi
        unfold affRank at hr3
        split_ifs at hr3 <;> omega
    have hrle := affRank_le_three sx
    have hNT2_v : rNT2.1.eval inp rNT2.2 = !(B5.eval inp wT2) := hsNT2.2.2.2.2 inp hinp
    have hT1nT2_v : rT1nT2.1.eval inp rT1nT2.2 = (B5.eval inp wT1 && !(B5.eval inp wT2)) := by
      rw [hsT1nT2.2.2.2.2 inp hinp]; simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
      rw [hE_NT2.2 inp hinp _ hwT1, hNT2_v]
    have hOdd_v : rOdd.1.eval inp rOdd.2 =
        ((B5.eval inp wT1 && !(B5.eval inp wT2)) || B5.eval inp wT3) := by
      rw [hsOdd.2.2.2.2 inp hinp]; simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
      rw [hT1nT2_v, (hE_NT2.trans hE_T1nT2).2 inp hinp _ hwT3]
    have hEven_v : rEven.1.eval inp rEven.2 = !(rOdd.1.eval inp rOdd.2) := hsEven.2.2.2.2 inp hinp
    have hE0_v : B6.eval inp rE0.2 = (rEven.1.eval inp rEven.2 && !(B5.eval inp wT2)) := by
      rw [(hE_E1.trans hE_E2).2 inp hinp _ hlt_E0, hsE0.2.2.2.2 inp hinp]
      simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
      rw [(hE_T1nT2.trans (hE_Odd.trans hE_Even)).2 inp hinp _ hlt_NT2, hNT2_v]
    have hE1_v : B6.eval inp rE1.2 = (rOdd.1.eval inp rOdd.2 && !(B5.eval inp wT2)) := by
      rw [hE_E2.2 inp hinp _ hlt_E1, hsE1.2.2.2.2 inp hinp]
      simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
      rw [(hE_Even.trans hE_E0).2 inp hinp _ hlt_Odd,
        (hE_T1nT2.trans (hE_Odd.trans (hE_Even.trans hE_E0))).2 inp hinp _ hlt_NT2, hNT2_v]
    have hE2_v : B6.eval inp rE2.2 = (rEven.1.eval inp rEven.2 && B5.eval inp wT2) := by
      rw [hsE2.2.2.2.2 inp hinp]
      simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
      rw [(hE_E0.trans hE_E1).2 inp hinp _ hlt_Even,
        (hE_NT2.trans (hE_T1nT2.trans (hE_Odd.trans (hE_Even.trans (hE_E0.trans hE_E1))))).2 inp hinp _ hwT2]
    rw [hE0_v, hE1_v, hE2_v, hEven_v, hOdd_v, hT1_val, hT2_val, hT3_val]
    have : affRank sx = 0 ∨ affRank sx = 1 ∨ affRank sx = 2 ∨ affRank sx = 3 := by omega
    rcases this with hr | hr | hr | hr <;> simp [hr]
  -- Step 5: Per-vertex tap j = E0 ∨ (E1 ∧ outPt j) ∨ (E2 ∧ missLine j)
  have hstep5 :
      ∃ (B7 : Builder n) (tapW : Fin n → ℕ),
        Extends B6 B7 ∧ (∀ j, tapW j < n + 2 + B7.gates.length) ∧
        B7.nots = 2 ∧ B7.monos ≤ B6.monos + (q + 5) * n ∧
        ∀ (x : Finset (Fin n)) (j : Fin n),
          B7.eval (List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true]) (tapW j) =
            gAff (x.map ePt.symm.toEmbedding) (ePt.symm j) := by
    have hall : ∀ (k : ℕ) (hk : k ≤ n),
        ∃ (Bk : Builder n) (tw : Fin k → ℕ),
          Extends B6 Bk ∧ (∀ j, tw j < n + 2 + Bk.gates.length) ∧
          Bk.nots = 2 ∧ Bk.monos ≤ B6.monos + (q + 5) * k ∧
          ∀ (x : Finset (Fin n)) (j : Fin k),
            Bk.eval (List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true]) (tw j) =
              gAff (x.map ePt.symm.toEmbedding) (ePt.symm ⟨j.val, by omega⟩) := by
      intro k
      induction k with
      | zero =>
        intro _
        exact ⟨B6, fun j => Fin.elim0 j, Extends.refl B6, fun j => Fin.elim0 j, hB6_nots, by simp,
          fun _ j => Fin.elim0 j⟩
      | succ k ih =>
        intro hk
        rcases ih (by omega) with ⟨Bk, twk, hEk, hltk, hnk, hmk, hevk⟩
        let jk : Fin n := ⟨k, by omega⟩
        let missWs : List ℕ :=
          (List.finRange (q + 1)).map (fun d => outLine d (eVal (evalDir (eDir.symm d) (ePt.symm jk).1)))
        have hmiss_len : missWs.length = q + 1 := by simp [missWs]
        have hmiss_lt : ∀ w ∈ missWs, w < n + 2 + Bk.gates.length := by
          intro w hw
          rcases List.mem_map.mp hw with ⟨d, _, rfl⟩
          have := hlt2 d (eVal (evalDir (eDir.symm d) (ePt.symm jk).1))
          have := hE3.1; have := hET1.1; have := hE4.1; have := hET2.1
          have := hET3.1; have := hE56.1; have := hEk.1; omega
        rcases exists_and_list missWs Bk hmiss_lt with ⟨Bmiss, wMiss, hEmiss, hltMiss, hnMiss, hmMiss, hevMiss⟩
        have hE_all_miss : Extends B6 Bmiss := hEk.trans hEmiss
        have hB6_le : rE2.1.gates.length ≤ Bmiss.gates.length := hE_all_miss.1
        have hwE0 : rE0.2 < n + 2 + Bmiss.gates.length := by
          have := hE_E1.1; have := hE_E2.1; omega
        have hwE1 : rE1.2 < n + 2 + Bmiss.gates.length := by
          have := hE_E2.1; omega
        have hwE2 : rE2.2 < n + 2 + Bmiss.gates.length := by
          omega
        have hwOut : outPt jk < n + 2 + Bmiss.gates.length := by
          have := hlt3 jk; have := hET1.1; have := hE4.1; have := hET2.1
          have := hET3.1; have := hE56.1; have := hE_all_miss.1; omega
        set rA1 := pushBin Bmiss GateOp.and (Or.inl rfl) rE1.2 (outPt jk) hwE1 hwOut
        have hsA1 := pushBin_spec Bmiss GateOp.and (Or.inl rfl) rE1.2 (outPt jk) hwE1 hwOut
        have hE_A1 : Extends Bmiss rA1.1 := hsA1.1
        have hlt_A1 : rA1.2 < n + 2 + rA1.1.gates.length := hsA1.2.1
        have hn_A1 : rA1.1.nots = Bmiss.nots := hsA1.2.2.1
        have hm_A1 : rA1.1.monos = Bmiss.monos + 1 := hsA1.2.2.2.1
        set rA2 := pushBin rA1.1 GateOp.and (Or.inl rfl) rE2.2 wMiss
          (by have := hE_A1.1; omega) (by have := hE_A1.1; omega)
        have hsA2 := pushBin_spec rA1.1 GateOp.and (Or.inl rfl) rE2.2 wMiss
          (by have := hE_A1.1; omega) (by have := hE_A1.1; omega)
        have hE_A2 : Extends rA1.1 rA2.1 := hsA2.1
        have hlt_A2 : rA2.2 < n + 2 + rA2.1.gates.length := hsA2.2.1
        have hn_A2 : rA2.1.nots = rA1.1.nots := hsA2.2.2.1
        have hm_A2 : rA2.1.monos = rA1.1.monos + 1 := hsA2.2.2.2.1
        set rO1 := pushBin rA2.1 GateOp.or (Or.inr rfl) rE0.2 rA1.2
          (by have := hE_A1.1; have := hE_A2.1; omega) (by have := hE_A2.1; omega)
        have hsO1 := pushBin_spec rA2.1 GateOp.or (Or.inr rfl) rE0.2 rA1.2
          (by have := hE_A1.1; have := hE_A2.1; omega) (by have := hE_A2.1; omega)
        have hE_O1 : Extends rA2.1 rO1.1 := hsO1.1
        have hlt_O1 : rO1.2 < n + 2 + rO1.1.gates.length := hsO1.2.1
        have hn_O1 : rO1.1.nots = rA2.1.nots := hsO1.2.2.1
        have hm_O1 : rO1.1.monos = rA2.1.monos + 1 := hsO1.2.2.2.1
        set rO2 := pushBin rO1.1 GateOp.or (Or.inr rfl) rO1.2 rA2.2
          hlt_O1 (by have := hE_O1.1; omega)
        have hsO2 := pushBin_spec rO1.1 GateOp.or (Or.inr rfl) rO1.2 rA2.2
          hlt_O1 (by have := hE_O1.1; omega)
        have hE_O2 : Extends rO1.1 rO2.1 := hsO2.1
        have hlt_O2 : rO2.2 < n + 2 + rO2.1.gates.length := hsO2.2.1
        have hn_O2 : rO2.1.nots = rO1.1.nots := hsO2.2.2.1
        have hm_O2 : rO2.1.monos = rO1.1.monos + 1 := hsO2.2.2.2.1
        have hEstep : Extends Bk rO2.1 :=
          hEmiss.trans (hE_A1.trans (hE_A2.trans (hE_O1.trans hE_O2)))
        let twk' : Fin (k + 1) → ℕ := fun j => if hj : j.val < k then twk ⟨j.val, hj⟩ else rO2.2
        refine ⟨rO2.1, twk', hEk.trans hEstep, ?_, by omega, ?_, ?_⟩
        · intro j; dsimp only [twk']; split_ifs with hj
          · have := hltk ⟨j.val, hj⟩; have := hEstep.1; omega
          · exact hlt_O2
        · have : (q + 5) * (k + 1) = (q + 5) * k + (q + 1) + 4 := by ring
          omega
        · intro x j
          dsimp only [twk']
          let inp := List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true]
          have hinp : inp.length = n + 2 := by simp [inp]
          have hn0 : inp.getD n false = false := by
            simp [inp, List.getD_eq_getElem?_getD, List.getElem?_append_right]
          have hn1' : inp.getD (n + 1) false = true := by
            simp [inp, List.getD_eq_getElem?_getD, List.getElem?_append_right]
          split_ifs with hj
          · rw [hEstep.2 inp hinp _ (hltk ⟨j.val, hj⟩), hevk x ⟨j.val, hj⟩]
          · have hjk : j.val = k := by omega
            have hjEq : (⟨j.val, by omega⟩ : Fin n) = jk := by ext; exact hjk
            rw [hjEq]
            have hmiss_v : Bmiss.eval inp wMiss =
                decide (∀ d : Option (FieldQ s), ∃ u ∈ x.map ePt.symm.toEmbedding,
                  evalDir d u.1 ≠ evalDir d (ePt.symm jk).1) := by
              rw [hevMiss inp hinp hn1']
              rw [Bool.eq_iff_iff]
              simp only [List.all_eq_true, missWs, List.mem_map, List.mem_finRange, true_and,
                decide_eq_true_eq]
              constructor
              · intro hall d
                have hw := hall _ ⟨eDir d, rfl⟩
                rw [(hE3.trans (hET1.trans (hE4.trans (hET2.trans (hET3.trans (hE56.trans hEk)))))).2
                  inp hinp _ (hlt2 _ _), hev2 x (eDir d) _] at hw
                rcases of_decide_eq_true hw with ⟨i, hi, hne⟩
                simp only [Equiv.symm_apply_apply] at hne
                exact ⟨ePt.symm i, Finset.mem_map.mpr ⟨i, hi, rfl⟩, hne⟩
              · intro hall w hw
                rcases hw with ⟨d, rfl⟩
                rw [(hE3.trans (hET1.trans (hE4.trans (hET2.trans (hET3.trans (hE56.trans hEk)))))).2
                  inp hinp _ (hlt2 _ _), hev2 x d _]
                rw [decide_eq_true_eq]
                rcases hall (eDir.symm d) with ⟨u, hu, hne⟩
                rcases Finset.mem_map.mp hu with ⟨i, hi, rfl⟩
                exact ⟨i, hi, by simpa only [Equiv.symm_apply_apply, Equiv.coe_toEmbedding] using hne⟩
            have hout_v : Bmiss.eval inp (outPt jk) =
                decide (∃ u ∈ x.map ePt.symm.toEmbedding, u ≠ ePt.symm jk) := by
              rw [(hET1.trans (hE4.trans (hET2.trans (hET3.trans (hE56.trans hE_all_miss))))).2
                inp hinp _ (hlt3 jk), hev3 inp hinp hn0 jk]
              have hsub : ∀ i : Fin n, B2.eval inp i.val = decide (i ∈ x) := fun i => by
                rw [(hE1.trans hE2).2 inp hinp i.val (by simp [B0]; omega), hB0_eval x i]
              rw [Bool.eq_iff_iff]
              simp only [hsub, decide_eq_true_eq]
              constructor
              · rintro ⟨i, hne, hi⟩
                exact ⟨ePt.symm i, Finset.mem_map.mpr ⟨i, hi, rfl⟩, fun h => hne (ePt.symm.injective h)⟩
              · rintro ⟨u, hu, hne⟩
                rcases Finset.mem_map.mp hu with ⟨i, hi, rfl⟩
                exact ⟨i, fun h => hne (congrArg ePt.symm h), hi⟩
            have hranks := hev_ranks x
            dsimp only at hranks
            have hB6eq : B6.gates.length = rE2.1.gates.length := rfl
            have hA1_v : rA1.1.eval inp rA1.2 = (B6.eval inp rE1.2 && Bmiss.eval inp (outPt jk)) := by
              rw [hsA1.2.2.2.2 inp hinp]; simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
              rw [hE_all_miss.2 inp hinp _ (by have := hE_E2.1; omega)]
            have hA2_v : rA2.1.eval inp rA2.2 = (B6.eval inp rE2.2 && Bmiss.eval inp wMiss) := by
              rw [hsA2.2.2.2.2 inp hinp]; simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
              rw [(hE_all_miss.trans hE_A1).2 inp hinp _ hlt_E2, hE_A1.2 inp hinp _ hltMiss]
            have hO1_v : rO1.1.eval inp rO1.2 = (B6.eval inp rE0.2 || rA1.1.eval inp rA1.2) := by
              rw [hsO1.2.2.2.2 inp hinp]; simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
              rw [(hE_all_miss.trans (hE_A1.trans hE_A2)).2 inp hinp _ (by have := hE_E1.1; have := hE_E2.1; omega),
                hE_A2.2 inp hinp _ hlt_A1]
            rw [hsO2.2.2.2.2 inp hinp]
            simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
            rw [hO1_v, hE_O1.2 inp hinp _ hlt_A2, hA1_v, hA2_v,
              hranks.1, hranks.2.1, hranks.2.2, hout_v, hmiss_v]
            rw [Bool.eq_iff_iff, gAff_iff]
            simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
            exact or_assoc
    exact hall n le_rfl
  rcases hstep5 with ⟨B7, tapW, hE7, hlt7, hn7, hm7, hev7⟩
  refine ⟨B7.toCircuit, fun j => ⟨tapW j, hlt7 j⟩, ?_, B7.rb, ?_, ?_, ?_, hev7⟩
  · intro g hg
    rcases B7.fan g hg with ⟨hop, hlen⟩
    exact ⟨by rcases hop with h | h | h <;> simp [h], hlen⟩
  · dsimp only [Builder.toCircuit]; omega
  · rw [← B7.nots_eq_notCount]; exact hn7
  · have hsz := B7.size_eq_nots_add_monos
    have hnc := B7.nots_eq_notCount
    have hdiff : B7.toCircuit.size - notCount B7.toCircuit = B7.monos := by omega
    rw [hdiff]
    simp only [List.length_map, List.length_finRange, hallLines_len] at hmT1 hmT2 hmT3
    have hqn : q ≤ n := by
      have h1 : 4 * q ≤ q * q := Nat.mul_le_mul_right q hq_ge
      dsimp only [n]; omega
    have htot : B7.monos ≤ (q + 1) * n + 3 * q * (q + 1) + 3 * n + n + n + n + (q + 1) * q + 5 + (q + 5) * n := by
      calc B7.monos ≤ B6.monos + (q + 5) * n := hm7
        _ = B5.monos + 5 + (q + 5) * n := by rw [hB6_monos]
        _ ≤ (B4'.monos + (q + 1) * q) + 5 + (q + 5) * n := by omega
        _ ≤ ((B4.monos + n) + (q + 1) * q) + 5 + (q + 5) * n := by omega
        _ ≤ (((B3'.monos + n) + n) + (q + 1) * q) + 5 + (q + 5) * n := by omega
        _ ≤ ((((B3.monos + n) + n) + n) + (q + 1) * q) + 5 + (q + 5) * n := by omega
        _ ≤ (((((B2.monos + 3 * n) + n) + n) + n) + (q + 1) * q) + 5 + (q + 5) * n := by omega
        _ ≤ ((((((B1.monos + 3 * q * (q + 1)) + 3 * n) + n) + n) + n) + (q + 1) * q) + 5 + (q + 5) * n := by omega
        _ ≤ (q + 1) * n + 3 * q * (q + 1) + 3 * n + n + n + n + (q + 1) * q + 5 + (q + 5) * n := by omega
    exact le_trans htot (mon_size_bound hqn)

end FieldGeom

-- =========================================================================
-- Part 5: Main proof assembly for L-lib-1263
-- =========================================================================

private def colorG_core {n k : ℕ} (color : Fin n → Fin k) (x : Finset (Fin n)) (j : Fin n) : Bool :=
  decide (∀ i ∈ x, color i ≠ color j)

private def input_core {n : ℕ} (x : Finset (Fin n)) : List Bool :=
  List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true]

private lemma main_core (s : ℕ) (hs : 1 ≤ s) :
    let rootQ := 2 ^ s
    let q := rootQ * rootQ
    let n := q * q - 1
    ∃ H : Fin n → Fin n → Prop, Symmetric H ∧ (∀ i, ¬ H i i) ∧
    (∀ i, ((Finset.univ : Finset (Fin n)).filter (fun j => H i j)).card = q) ∧
    let fits := fun (g : Finset (Fin n) → Fin n → Bool) =>
      (∀ x j, (∀ i ∈ x, H i j) → g x j = true) ∧ (∀ x j, j ∈ x → g x j = false)
    let computes := fun (C : Circuit) (g : Finset (Fin n) → Fin n → Bool) =>
      FanInTwo C ∧ ReadsBack (n + 2) C ∧
      C.output < n + 2 + C.size ∧ ∃ tap : Fin n → Fin (n + 2 + C.size),
        ∀ x j, (C.wires (input_core x)).getD (tap j).val false = g x j
    (∀ g, fits g → runsAux g 3 Finset.univ ∧ ∀ C, computes C g → 2 ≤ notCount C) ∧
    (∃ g, fits g ∧ (∀ x y, x ⊆ y → ∀ j, g y j = true → g x j = true) ∧
      ¬ runsAux g 4 Finset.univ ∧ ∃ C, computes C g ∧ notCount C = 2 ∧
        C.size - notCount C ≤ 12 * (q + 1) * (n + 1)) ∧
    (∀ A : Finset (Fin n), (∀ i ∈ A, ∀ j ∈ A, ¬ H i j) → A.card ≤ (rootQ - 1) * (q + 1)) ∧
    ∀ (k : Nat) (color : Fin n → Fin k), (∀ i j, H i j → color i ≠ color j) →
      let g := colorG_core color
      rootQ + 1 ≤ k ∧ runsAux g (rootQ + 1) Finset.univ ∧
      ∀ C, computes C g → s + 1 ≤ notCount C := by
  letI : Fintype (FieldQ s) := Fintype.ofFinite (FieldQ s)
  intro rootQ q n
  let ePt : Pt s ≃ Fin n := (Fintype.equivFin (Pt s)).trans (finCongr (pt_card s hs))
  let H : Fin n → Fin n → Prop := fun i j => adjPt (ePt.symm i) (ePt.symm j)
  have hsym : Symmetric H := fun _ _ h => adjPt_symm h
  have hirr : ∀ i, ¬ H i i := fun i => adjPt_irrefl (ePt.symm i)
  have hdeg : ∀ i, ((Finset.univ : Finset (Fin n)).filter (fun j => H i j)).card = q := by
    intro i
    change ((Finset.univ : Finset (Fin n)).filter (fun j => H i j)).card = (2 ^ s) * (2 ^ s)
    rw [← adjPt_deg hs (ePt.symm i)]
    refine Finset.card_bij' (fun j _ => ePt.symm j) (fun p _ => ePt p) ?_ ?_ ?_ ?_
    · intro j hj; simp only [Finset.mem_filter, Finset.mem_univ, true_and, H] at hj ⊢; exact hj
    · intro p hp; simp only [Finset.mem_filter, Finset.mem_univ, true_and, H, Equiv.symm_apply_apply] at hp ⊢; exact hp
    · intro j _; exact ePt.apply_symm_apply j
    · intro p _; exact ePt.symm_apply_apply p
  refine ⟨H, hsym, hirr, hdeg, ?_, ?_, ?_, ?_⟩
  · -- Part 1: triangle forces runs 3 and 2 ≤ notCount C
    intro g ⟨hfit1, hfit2⟩
    let v1 : Pt s := ⟨(1, 0), fun h => one_ne_zero (congrArg Prod.fst h)⟩
    let v2 : Pt s := ⟨(0, 1), fun h => one_ne_zero (congrArg Prod.snd h)⟩
    let v3 : Pt s := ⟨(1, 1), fun h => one_ne_zero (congrArg Prod.fst h)⟩
    have h12 : adjPt v1 v2 := by simp [adjPt, v1, v2]
    have h13 : adjPt v1 v3 := by simp [adjPt, v1, v3]
    have h23 : adjPt v2 v3 := by simp [adjPt, v2, v3]
    let i1 := ePt v1; let i2 := ePt v2; let i3 := ePt v3
    have hH12 : H i1 i2 := by simp [H, i1, i2, h12]
    have hH13 : H i1 i3 := by simp [H, i1, i3, h13]
    have hH23 : H i2 i3 := by simp [H, i2, i3, h23]
    have hruns3 : runsAux g 3 Finset.univ := by
      refine ⟨{i1, i2}, {i1, i2, i3}, i3, ?_, ?_, Finset.subset_univ _, ?_, ?_⟩
      · refine ⟨{i1}, {i1, i2}, i2, ?_, ?_, Finset.Subset.rfl, ?_, ?_⟩
        · refine ⟨∅, {i1}, i1, trivial, Finset.empty_subset _, Finset.Subset.rfl, ?_, ?_⟩
          · exact hfit1 ∅ i1 (fun _ h => by cases h)
          · exact hfit2 {i1} i1 (Finset.mem_singleton_self i1)
        · intro x hx; simp only [Finset.mem_singleton] at hx; subst hx; simp
        · exact hfit1 {i1} i2 (fun a ha => by simp at ha; subst ha; exact hH12)
        · exact hfit2 {i1, i2} i2 (by simp)
      · intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        rcases hx with rfl | rfl <;> simp
      · exact hfit1 {i1, i2} i3 (fun a ha => by simp at ha; rcases ha with rfl | rfl; exact hH13; exact hH23)
      · exact hfit2 {i1, i2, i3} i3 (by simp)
    refine ⟨hruns3, ?_⟩
    intro C ⟨hfan, hrb, _, tap, htap⟩
    have hlt := markov_lower_bound g C hfan hrb tap htap hruns3
    by_contra hlt2
    have hle1 : notCount C ≤ 1 := by omega
    have : 2 ^ notCount C ≤ 2 := by
      calc 2 ^ notCount C ≤ 2 ^ 1 := Nat.pow_le_pow_right (by omega) hle1
        _ = 2 := by norm_num
    omega
  · -- Part 2: gAff satisfies fits, anti-mono, ¬ runs 4, and 2-NOT circuit
    let g : Finset (Fin n) → Fin n → Bool := fun x j => gAff (x.map ePt.symm.toEmbedding) (ePt.symm j)
    refine ⟨g, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · intro x j hall
      apply gAff_fits.1
      intro u hu
      rcases Finset.mem_map.mp hu with ⟨i, hi, rfl⟩
      exact hall i hi
    · intro x j hj
      exact gAff_fits.2 _ _ (Finset.mem_map.mpr ⟨j, hj, rfl⟩)
    · intro x y hxy j hy
      exact gAff_antimono (Finset.map_subset_map.mpr hxy) (ePt.symm j) hy
    · intro h4
      apply gAff_not_runs4 (s := s)
      have htrans : ∀ k (x : Finset (Fin n)), runsAux g k x →
          runsAux (@gAff s) k (x.map ePt.symm.toEmbedding) := by
        intro k
        induction k with
        | zero => intro _ _; trivial
        | succ k ih =>
          intro x ⟨u, v, j, hru, huv, hvx, hgu, hgv⟩
          exact ⟨u.map ePt.symm.toEmbedding, v.map ePt.symm.toEmbedding, ePt.symm j,
            ih u hru, Finset.map_subset_map.mpr huv, Finset.map_subset_map.mpr hvx, hgu, hgv⟩
      have hmap : (Finset.univ : Finset (Fin n)).map ePt.symm.toEmbedding = Finset.univ := by
        ext p; simp only [Finset.mem_map, Finset.mem_univ, true_and, iff_true]
        exact ⟨ePt p, ePt.symm_apply_apply p⟩
      rw [← hmap]
      exact htrans 4 Finset.univ h4
    · rcases exists_gAff_circuit s hs ePt with ⟨C, tap, hfan, hrb, hout, hnot, hsz, hev⟩
      exact ⟨C, ⟨hfan, hrb, hout, tap, hev⟩, hnot, hsz⟩
  · -- Part 3: Independent set bound
    intro A hind
    have hmap : (A.map ePt.symm.toEmbedding).card ≤ (rootQ - 1) * (q + 1) := by
      apply indep_bound hs
      intro u hu v hv
      rcases Finset.mem_map.mp hu with ⟨i, hi, rfl⟩
      rcases Finset.mem_map.mp hv with ⟨j, hj, rfl⟩
      exact hind i hi j hj
    rwa [Finset.card_map] at hmap
  · -- Part 4: Coloring lower bound
    intro k color hcol g
    have hcol_le : ∀ c : Fin k, ((Finset.univ : Finset (Fin n)).filter (fun i => color i = c)).card ≤
        (rootQ - 1) * (q + 1) := by
      intro c
      have hind : ∀ i ∈ Finset.univ.filter (fun i => color i = c),
          ∀ j ∈ Finset.univ.filter (fun i => color i = c), ¬ H i j := by
        intro i hi j hj hij
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
        exact hcol i j hij (hi.trans hj.symm)
      have hmap : ((Finset.univ.filter (fun i => color i = c)).map ePt.symm.toEmbedding).card ≤
          (rootQ - 1) * (q + 1) := by
        apply indep_bound hs
        intro u hu v hv
        rcases Finset.mem_map.mp hu with ⟨i, hi, rfl⟩
        rcases Finset.mem_map.mp hv with ⟨j, hj, rfl⟩
        exact hind i hi j hj
      rwa [Finset.card_map] at hmap
    have hsum_n : n = ∑ c : Fin k, ((Finset.univ : Finset (Fin n)).filter (fun i => color i = c)).card := by
      simp only [Finset.card_filter]
      rw [Finset.sum_comm]
      have h1 : ∀ i : Fin n, (∑ c : Fin k, if color i = c then 1 else 0) = 1 := by
        intro i; rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
      rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, mul_one]
    have hnk : n ≤ k * ((rootQ - 1) * (q + 1)) := by
      rw [hsum_n]
      calc ∑ c : Fin k, ((Finset.univ : Finset (Fin n)).filter (fun i => color i = c)).card
          ≤ ∑ _c : Fin k, (rootQ - 1) * (q + 1) := Finset.sum_le_sum (fun c _ => hcol_le c)
        _ = k * ((rootQ - 1) * (q + 1)) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    have hr_ge : 2 ≤ rootQ := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ s := Nat.pow_le_pow_right (by omega) hs
    have hn_fac : n = (rootQ + 1) * ((rootQ - 1) * (q + 1)) := by
      have h1 : (rootQ + 1) * (rootQ - 1) = q - 1 := by
        have hsq : rootQ * rootQ = q := rfl
        have hge1 : 1 ≤ rootQ := by omega
        zify [hge1, (show 1 ≤ q by nlinarith)]
        nlinarith
      have hq1 : 1 ≤ q := by dsimp only [q]; nlinarith
      have h2 : (q - 1) * (q + 1) = q * q - 1 := by
        zify [hq1, (show 1 ≤ q * q by nlinarith)]
        ring
      rw [← mul_assoc, h1, h2]
    have hpos : 0 < (rootQ - 1) * (q + 1) := Nat.mul_pos (by omega) (by omega)
    have hk_ge : rootQ + 1 ≤ k := by
      rw [hn_fac] at hnk
      exact Nat.le_of_mul_le_mul_right hnk hpos
    let used : Finset (Fin k) := Finset.univ.image color
    have hused_ge : rootQ + 1 ≤ used.card := by
      have hsum_u : n = ∑ c ∈ used, ((Finset.univ : Finset (Fin n)).filter (fun i => color i = c)).card := by
        conv_lhs => rw [hsum_n]
        symm
        apply Finset.sum_subset (Finset.subset_univ used)
        intro c _ hc
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro i _ hi
        exact hc (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)
      have hnu : n ≤ used.card * ((rootQ - 1) * (q + 1)) := by
        rw [hsum_u]
        calc ∑ c ∈ used, ((Finset.univ : Finset (Fin n)).filter (fun i => color i = c)).card
            ≤ ∑ _c ∈ used, (rootQ - 1) * (q + 1) := Finset.sum_le_sum (fun c _ => hcol_le c)
          _ = used.card * ((rootQ - 1) * (q + 1)) := by rw [Finset.sum_const, smul_eq_mul]
      rw [hn_fac] at hnu
      exact Nat.le_of_mul_le_mul_right hnu hpos
    have hruns_r : runsAux g (rootQ + 1) Finset.univ := by
      have hsub : ∀ (m : ℕ) (S : Finset (Fin k)), S ⊆ used → S.card = m →
          ∃ X : Finset (Fin n), (∀ i ∈ X, color i ∈ S) ∧ runsAux g m X := by
        intro m
        induction m with
        | zero =>
          intro _ _ _
          exact ⟨∅, (fun _ h => by cases h), trivial⟩
        | succ m ih =>
          intro S hSu hScard
          rcases Finset.card_pos.mp (by omega : 0 < S.card) with ⟨c0, hc0⟩
          have hsub' : S.erase c0 ⊆ used := (Finset.erase_subset c0 S).trans hSu
          have hcard' : (S.erase c0).card = m := by rw [Finset.card_erase_of_mem hc0, hScard]; omega
          rcases ih (S.erase c0) hsub' hcard' with ⟨X, hXcol, hXruns⟩
          rcases Finset.mem_image.mp (hSu hc0) with ⟨v0, _, hv0⟩
          refine ⟨insert v0 X, ?_, ?_⟩
          · intro i hi
            rcases Finset.mem_insert.mp hi with rfl | hi'
            · rw [hv0]; exact hc0
            · exact Finset.erase_subset c0 S (hXcol i hi')
          · refine ⟨X, insert v0 X, v0, hXruns, Finset.subset_insert v0 X, Finset.Subset.rfl, ?_, ?_⟩
            · dsimp only [g, colorG_core]; rw [decide_eq_true_eq]
              intro i hi hEq
              have := hXcol i hi
              rw [hEq, hv0] at this
              exact (Finset.notMem_erase c0 S) this
            · dsimp only [g, colorG_core]; rw [decide_eq_false_iff_not]
              intro hall; exact hall v0 (Finset.mem_insert_self v0 X) rfl
      rcases Finset.exists_subset_card_eq hused_ge with ⟨S, hSu, hScard⟩
      rcases hsub (rootQ + 1) S hSu hScard with ⟨X, _, hXruns⟩
      have hmono_runs : ∀ m (A B : Finset (Fin n)), A ⊆ B → runsAux g m A → runsAux g m B := by
        intro m
        cases m with
        | zero => intro _ _ _ _; trivial
        | succ m =>
          intro A B hAB ⟨u, v, j, hru, huv, hvA, hgu, hgv⟩
          exact ⟨u, v, j, hru, huv, hvA.trans hAB, hgu, hgv⟩
      exact hmono_runs (rootQ + 1) X Finset.univ (Finset.subset_univ X) hXruns
    refine ⟨hk_ge, hruns_r, ?_⟩
    intro C ⟨hfan, hrb, _, tap, htap⟩
    have hlt := markov_lower_bound g C hfan hrb tap htap hruns_r
    have hlt2 : 2 ^ s < 2 ^ notCount C := by dsimp only [rootQ] at hlt; omega
    have hlt_exp : s < notCount C := (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp hlt2
    omega

private lemma card_filter_congr_inst {α : Type*} {s : Finset α} {P Q : α → Prop}
    {d1 : DecidablePred P} {d2 : DecidablePred Q} (h : ∀ x ∈ s, P x ↔ Q x) :
    (@Finset.filter α P d1 s).card = (@Finset.filter α Q d2 s).card := by
  congr 1; ext x; simp only [Finset.mem_filter]; exact and_congr_right (h x)

private lemma computes_congr_dec {n : ℕ} (C : Circuit) (g1 g2 : Finset (Fin n) → Fin n → Bool)
    {d1 d2 : ∀ (x : Finset (Fin n)) (i : Fin n), Decidable (i ∈ x)}
    (hg : g1 = g2) :
    (FanInTwo C ∧ ReadsBack (n + 2) C ∧ C.output < n + 2 + C.size ∧
      ∃ tap : Fin n → Fin (n + 2 + C.size),
        ∀ x j, (C.wires (List.ofFn (fun i : Fin n => @decide (i ∈ x) (d1 x i)) ++ [false, true])).getD (tap j).val false = g1 x j) ↔
    (FanInTwo C ∧ ReadsBack (n + 2) C ∧ C.output < n + 2 + C.size ∧
      ∃ tap : Fin n → Fin (n + 2 + C.size),
        ∀ x j, (C.wires (List.ofFn (fun i : Fin n => @decide (i ∈ x) (d2 x i)) ++ [false, true])).getD (tap j).val false = g2 x j) := by
  subst hg
  have hd : d1 = d2 := funext fun x => funext fun i => Subsingleton.elim _ _
  subst hd
  exact Iff.rfl

private lemma decide_forall_congr {n k : ℕ} (color : Fin n → Fin k)
    {d1 d2 : ∀ (x : Finset (Fin n)) (j : Fin n), Decidable (∀ i ∈ x, color i ≠ color j)} :
    (fun x j => @decide (∀ i ∈ x, color i ≠ color j) (d1 x j)) =
    (fun x j => @decide (∀ i ∈ x, color i ≠ color j) (d2 x j)) :=
  funext fun x => funext fun j => by rw [Subsingleton.elim (d1 x j) (d2 x j)]

private lemma runsAux_congr {n : ℕ} {g1 g2 : Finset (Fin n) → Fin n → Bool}
    (h : g1 = g2) {m : ℕ} {x : Finset (Fin n)} :
    runsAux g1 m x → runsAux g2 m x :=
  fun hr => h ▸ hr

private lemma main_aux :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    ∀ s : Nat, 1 ≤ s →
      let rootQ := 2^s
      let q := rootQ*rootQ
      let n := q*q-1
      ∃ H : Fin n → Fin n → Prop, Symmetric H ∧ (∀ i, ¬ H i i) ∧
      (∀ i, ((Finset.univ : Finset (Fin n)).filter (fun j => H i j)).card=q) ∧
      let fits := fun (g : Finset (Fin n) → Fin n → Bool) =>
        (∀ x j, (∀ i ∈ x, H i j) → g x j=true) ∧ (∀ x j, j ∈ x → g x j=false)
      let computes := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (g : Finset (Fin n) → Fin n → Bool) =>
        PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
        C.output < n+2+C.size ∧ ∃ tap : Fin n → Fin (n+2+C.size),
          ∀ x j, let input := List.ofFn (fun i : Fin n => decide (i∈x)) ++ [false,true]
                 (C.wires input).getD (tap j).val false = g x j
      let runs := fun (g : Finset (Fin n) → Fin n → Bool) =>
        Nat.rec (motive := fun _ => Finset (Fin n) → Prop) (fun _ => True)
          (fun _ prev x => ∃ u v j, prev u ∧ u ⊆ v ∧ v ⊆ x ∧ g u j=true ∧ g v j=false)
      (∀ g, fits g → runs g 3 Finset.univ ∧ ∀ C, computes C g → 2 ≤ PEqualNP.NotBracket.notCount C) ∧
      (∃ g, fits g ∧ (∀ x y, x ⊆ y → ∀ j, g y j=true → g x j=true) ∧
        ¬ runs g 4 Finset.univ ∧ ∃ C, computes C g ∧ PEqualNP.NotBracket.notCount C = 2 ∧
          C.size - PEqualNP.NotBracket.notCount C ≤ 12*(q+1)*(n+1)) ∧
      (∀ A : Finset (Fin n), (∀ i ∈ A, ∀ j ∈ A, ¬ H i j) → A.card ≤ (rootQ-1)*(q+1)) ∧
      ∀ (k : Nat) (color : Fin n → Fin k), (∀ i j, H i j → color i ≠ color j) →
        let g := fun (x : Finset (Fin n)) (j : Fin n) => decide (∀ i ∈ x, color i ≠ color j)
        rootQ+1 ≤ k ∧ runs g (rootQ+1) Finset.univ ∧
        ∀ C, computes C g → s+1 ≤ PEqualNP.NotBracket.notCount C := by
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  intro s hs rootQ q n
  rcases main_core s hs with ⟨H, hsym, hirr, hdeg, h1, h2, h3, h4⟩
  refine ⟨H, hsym, hirr, fun i => (card_filter_congr_inst (fun _ _ => Iff.rfl)).trans (hdeg i), ?_, ?_, h3, ?_⟩
  · intro g hfit
    rcases h1 g hfit with ⟨hr, hc⟩
    exact ⟨hr, fun C hC => hc C ((computes_congr_dec C g g rfl).mp hC)⟩
  · rcases h2 with ⟨g, hfit, hanti, hnr, C, hC, hnot, hsz⟩
    exact ⟨g, hfit, hanti, hnr, C, (computes_congr_dec C g g rfl).mpr hC, hnot, hsz⟩
  · intro k color hcol
    rcases h4 k color hcol with ⟨hk, hr, hc⟩
    have hEq : colorG_core color = (fun (x : Finset (Fin n)) (j : Fin n) => decide (∀ i ∈ x, color i ≠ color j)) :=
      funext fun x => funext fun j => congrArg (fun d => @decide _ d) (Subsingleton.elim _ _)
    refine ⟨hk, ?_, ?_⟩
    · change runsAux _ (rootQ + 1) Finset.univ
      exact runsAux_congr hEq hr
    · intro C hC
      apply hc C
      rcases hC with ⟨hfan, hrb, hout, tap, htap⟩
      refine ⟨hfan, hrb, hout, tap, fun x j => ?_⟩
      have hinp : input_core x = List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true] := by
        unfold input_core; congr 1; congr 1; funext i; exact congrArg (fun d => @decide _ d) (Subsingleton.elim _ _)
      rw [hinp, htap x j]
      exact (congrFun (congrFun hEq x) j).symm

end PEqualNP.Outside.L_lib_1263_aux

theorem PEqualNP.Outside.L_lib_1263 :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    ∀ s : Nat, 1 ≤ s →
      let rootQ := 2^s
      let q := rootQ*rootQ
      let n := q*q-1
      ∃ H : Fin n → Fin n → Prop, Symmetric H ∧ (∀ i, ¬ H i i) ∧
      (∀ i, ((Finset.univ : Finset (Fin n)).filter (fun j => H i j)).card=q) ∧
      let fits := fun (g : Finset (Fin n) → Fin n → Bool) =>
        (∀ x j, (∀ i ∈ x, H i j) → g x j=true) ∧ (∀ x j, j ∈ x → g x j=false)
      let computes := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (g : Finset (Fin n) → Fin n → Bool) =>
        PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
        C.output < n+2+C.size ∧ ∃ tap : Fin n → Fin (n+2+C.size),
          ∀ x j, let input := List.ofFn (fun i : Fin n => decide (i∈x)) ++ [false,true]
                 (C.wires input).getD (tap j).val false = g x j
      let runs := fun (g : Finset (Fin n) → Fin n → Bool) =>
        Nat.rec (motive := fun _ => Finset (Fin n) → Prop) (fun _ => True)
          (fun _ prev x => ∃ u v j, prev u ∧ u ⊆ v ∧ v ⊆ x ∧ g u j=true ∧ g v j=false)
      (∀ g, fits g → runs g 3 Finset.univ ∧ ∀ C, computes C g → 2 ≤ PEqualNP.NotBracket.notCount C) ∧
      (∃ g, fits g ∧ (∀ x y, x ⊆ y → ∀ j, g y j=true → g x j=true) ∧
        ¬ runs g 4 Finset.univ ∧ ∃ C, computes C g ∧ PEqualNP.NotBracket.notCount C = 2 ∧
          C.size - PEqualNP.NotBracket.notCount C ≤ 12*(q+1)*(n+1)) ∧
      (∀ A : Finset (Fin n), (∀ i ∈ A, ∀ j ∈ A, ¬ H i j) → A.card ≤ (rootQ-1)*(q+1)) ∧
      ∀ (k : Nat) (color : Fin n → Fin k), (∀ i j, H i j → color i ≠ color j) →
        let g := fun (x : Finset (Fin n)) (j : Fin n) => decide (∀ i ∈ x, color i ≠ color j)
        rootQ+1 ≤ k ∧ runs g (rootQ+1) Finset.univ ∧
        ∀ C, computes C g → s+1 ≤ PEqualNP.NotBracket.notCount C := by
  exact PEqualNP.Outside.L_lib_1263_aux.main_aux
