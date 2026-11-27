import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29918_aux

open PEqualNP.CircuitLowerBounds

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_stepWire_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, stepWire, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_stepWire_prefix (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by
      simp only [stepWire, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (stepWire w g) hlt]
    simp only [stepWire, List.getD_eq_getElem _ _ hi,
      List.getD_eq_getElem _ _ (by simp; omega : i < (w ++ [_]).length),
      List.getElem_append_left hi]

lemma wires_len (C : Circuit) (x : Fin 7 → Bool) :
    (C.wires (List.ofFn x)).length = 7 + C.gates.length := by
  unfold Circuit.wires
  change (C.gates.foldl stepWire (List.ofFn x)).length = _
  rw [foldl_stepWire_len, List.length_ofFn]

lemma wire_getD_input (C : Circuit) (x : Fin 7 → Bool) (i : Fin 7) :
    (C.wires (List.ofFn x)).getD i.val false = x i := by
  unfold Circuit.wires
  change (C.gates.foldl stepWire (List.ofFn x)).getD i.val false = x i
  have hi : i.val < (List.ofFn x).length := by simp
  rw [foldl_stepWire_prefix C.gates (List.ofFn x) i.val hi, List.getD_eq_getElem _ _ hi,
    List.getElem_ofFn]

def pre (C : Circuit) (x : Fin 7 → Bool) (j : ℕ) : List Bool :=
  (C.gates.take j).foldl stepWire (List.ofFn x)

lemma pre_len (C : Circuit) (x : Fin 7 → Bool) (j : ℕ) (hj : j ≤ C.gates.length) :
    (pre C x j).length = 7 + j := by
  unfold pre
  rw [foldl_stepWire_len, List.length_ofFn, List.length_take]
  omega

lemma pre_getD_lt (C : Circuit) (x : Fin 7 → Bool) (j a : ℕ) (hj : j ≤ C.gates.length)
    (ha : a < 7 + j) :
    (pre C x j).getD a false = (C.wires (List.ofFn x)).getD a false := by
  unfold Circuit.wires pre
  change _ = (C.gates.foldl stepWire (List.ofFn x)).getD a false
  have hsplit : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
  conv_rhs => rw [hsplit]
  rw [List.foldl_append]
  have hlen : ((C.gates.take j).foldl stepWire (List.ofFn x)).length = 7 + j := by
    rw [foldl_stepWire_len, List.length_ofFn, List.length_take]
    omega
  rw [foldl_stepWire_prefix (C.gates.drop j) _ a (by omega)]

lemma pre_getD_ge (C : Circuit) (x : Fin 7 → Bool) (j a : ℕ) (hj : j ≤ C.gates.length)
    (ha : 7 + j ≤ a) : (pre C x j).getD a false = false := by
  apply List.getD_eq_default
  rw [pre_len C x j hj]
  exact ha

lemma wire_gate (C : Circuit) (x : Fin 7 → Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires (List.ofFn x)).getD (7 + j) false =
      (C.gates[j]'hj).op.eval ((C.gates[j]'hj).inputs.map fun i => (pre C x j).getD i false) := by
  unfold Circuit.wires pre
  change (C.gates.foldl stepWire (List.ofFn x)).getD (7 + j) false = _
  have hsplit : C.gates = C.gates.take j ++ (C.gates[j]'hj) :: C.gates.drop (j + 1) := by
    have h1 : C.gates.take j ++ C.gates.drop j = C.gates := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = (C.gates[j]'hj) :: C.gates.drop (j + 1) :=
      List.drop_eq_getElem_cons hj
    rw [← h2, h1]
  conv_lhs => rw [hsplit]
  rw [List.foldl_append, List.foldl_cons]
  set pref := (C.gates.take j).foldl stepWire (List.ofFn x)
  have hlen : pref.length = 7 + j := by
    rw [foldl_stepWire_len, List.length_ofFn, List.length_take]
    omega
  have hlt : 7 + j < (stepWire pref (C.gates[j]'hj)).length := by
    simp only [stepWire, List.length_append, List.length_cons, List.length_nil, hlen]
    omega
  rw [foldl_stepWire_prefix (C.gates.drop (j + 1)) (stepWire pref (C.gates[j]'hj)) (7 + j) hlt]
  dsimp only [stepWire]
  have hlt' : 7 + j < (pref ++ [(C.gates[j]'hj).op.eval
      ((C.gates[j]'hj).inputs.map fun i => pref.getD i false)]).length := by
    simp only [List.length_append, List.length_cons, List.length_nil, hlen]
    omega
  rw [List.getD_eq_getElem _ _ hlt', List.getElem_append_right (by omega : pref.length ≤ 7 + j)]
  simp only [hlen, Nat.sub_self, List.getElem_cons_zero]

def gin (C : Circuit) (j : ℕ) : List ℕ := (C.gates.getD j ⟨GateOp.and, []⟩).inputs

def E (C : Circuit) : ℕ → Finset ℕ → Finset ℕ
  | 0, T => T
  | n + 1, T =>
    if 7 + n ∈ T then E C n ((T.erase (7 + n)) ∪ ((gin C n).toFinset.filter (· < 7 + n)))
    else E C n T

lemma E_card (C : Circuit) (hC : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    ∀ n (T : Finset ℕ), n ≤ C.gates.length → (E C n T).card ≤ T.card + n := by
  intro n
  induction n with
  | zero => intro T _; simp [E]
  | succ n ih =>
    intro T hn
    simp only [E]
    split_ifs with hm
    · have h1 := ih ((T.erase (7 + n)) ∪ ((gin C n).toFinset.filter (· < 7 + n))) (by omega)
      have ha := Finset.card_union_le (T.erase (7 + n)) ((gin C n).toFinset.filter (· < 7 + n))
      have hb := Finset.card_erase_of_mem hm
      have hf := Finset.card_filter_le (gin C n).toFinset (· < 7 + n)
      have ht := List.toFinset_card_le (gin C n)
      have hg : (gin C n).length ≤ 2 := by
        unfold gin
        rw [List.getD_eq_getElem _ _ (by omega)]
        exact hC _ (List.getElem_mem _)
      have hpos : 0 < T.card := Finset.card_pos.mpr ⟨_, hm⟩
      omega
    · have := ih T (by omega)
      omega

lemma E_zero_not_mem (C : Circuit) :
    ∀ n (T : Finset ℕ), 0 ∉ T → (∀ j < n, 0 ∉ gin C j) → 0 ∉ E C n T := by
  intro n
  induction n with
  | zero => intro T hT _; simpa [E] using hT
  | succ n ih =>
    intro T hT hg
    simp only [E]
    split_ifs
    · apply ih
      · simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_filter, List.mem_toFinset,
          not_or]
        exact ⟨fun h => hT h.2, fun h => hg n (by omega) h.1⟩
      · intro j hj
        exact hg j (by omega)
    · exact ih T hT (fun j hj => hg j (by omega))

lemma E_agree (C : Circuit) (x x' : Fin 7 → Bool) :
    ∀ n (T : Finset ℕ), n ≤ C.gates.length → (∀ w ∈ T, w < 7 + n) →
      (∀ i : Fin 7, i.val ∈ E C n T → x i = x' i) →
      ∀ w ∈ T, (C.wires (List.ofFn x)).getD w false = (C.wires (List.ofFn x')).getD w false := by
  intro n
  induction n with
  | zero =>
    intro T _ hT hx w hw
    have hw7 : w < 7 := by
      have := hT w hw
      omega
    have h1 := wire_getD_input C x ⟨w, hw7⟩
    have h2 := wire_getD_input C x' ⟨w, hw7⟩
    simp only at h1 h2
    rw [h1, h2]
    exact hx ⟨w, hw7⟩ (by simpa [E] using hw)
  | succ n ih =>
    intro T hn hT hx
    simp only [E] at hx
    split_ifs at hx with hm
    · set T' := (T.erase (7 + n)) ∪ ((gin C n).toFinset.filter (· < 7 + n)) with hT'
      have hT'lt : ∀ w ∈ T', w < 7 + n := by
        intro w hw
        simp only [hT', Finset.mem_union, Finset.mem_erase, Finset.mem_filter] at hw
        rcases hw with ⟨hne, hwT⟩ | ⟨_, hlt⟩
        · have := hT w hwT
          omega
        · exact hlt
      have hag := ih T' (by omega) hT'lt hx
      intro w hw
      by_cases hwm : w = 7 + n
      · subst hwm
        have hnl : n < C.gates.length := by omega
        rw [wire_gate C x n hnl, wire_gate C x' n hnl]
        congr 1
        refine List.map_congr_left ?_
        intro a ha
        by_cases hal : a < 7 + n
        · rw [pre_getD_lt C x n a (by omega) hal, pre_getD_lt C x' n a (by omega) hal]
          apply hag
          simp only [hT', Finset.mem_union, Finset.mem_filter, List.mem_toFinset]
          right
          refine ⟨?_, hal⟩
          unfold gin
          rw [List.getD_eq_getElem _ _ hnl]
          exact ha
        · rw [pre_getD_ge C x n a (by omega) (by omega), pre_getD_ge C x' n a (by omega) (by omega)]
      · apply hag
        simp only [hT', Finset.mem_union, Finset.mem_erase]
        exact Or.inl ⟨hwm, hw⟩
    · have hT2 : ∀ w ∈ T, w < 7 + n := by
        intro w hw
        have h1 := hT w hw
        have h2 : w ≠ 7 + n := fun h => hm (h ▸ hw)
        omega
      exact ih T (by omega) hT2 hx

def f7 (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) ||
    (x 6 && x 0)

def pt (l : List Bool) : Fin 7 → Bool := fun t => l.getD t.val false

end PEqualNP.Outside.L_meta_29918_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_29918_aux in
theorem PEqualNP.Outside.L_meta_29918 : (¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 8 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 10 ∈ (C.gates.get i).inputs ∧ 10 ≠ 0 ∧ 10 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 10 false = true)) := by
  rintro ⟨C, ⟨iv, hiv⟩, ⟨kv, hkv⟩, hi8, hFan, hSize, hEval, h0i, h0uniq, hiOr, hkAnd, hik,
    h15k, h10i, -, -, -⟩
  dsimp only at hi8 hik h15k
  subst hi8
  have hlen : C.gates.length = 10 := hSize
  have hk9 : kv = 9 := by omega
  subst hk9
  have hi8' : (8 : ℕ) < C.gates.length := by omega
  have hk9' : (9 : ℕ) < C.gates.length := by omega
  simp only [List.get_eq_getElem] at h0i h10i hiOr hkAnd h15k
  have hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2 := fun g hg => (hFan g hg).2
  have hev : ∀ x, (C.wires (List.ofFn x)).getD C.output false = f7 x := fun x => hEval x

  have hno0 : ∀ j (hj : j < C.gates.length), j ≠ 8 → 0 ∉ (C.gates[j]'hj).inputs := by
    intro j hj hj8 hmem
    have h := h0uniq ⟨j, hj⟩ (by simpa using hmem)
    exact hj8 (congrArg Fin.val h)
  have hgin0 : ∀ j < 8, 0 ∉ gin C j := by
    intro j hj
    unfold gin
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact hno0 j (by omega) (by omega)

  have indep0 : ∀ c, c ≠ 0 → c < 15 → ∀ x x' : Fin 7 → Bool,
      (∀ t : Fin 7, t ≠ 0 → x t = x' t) →
      (C.wires (List.ofFn x)).getD c false = (C.wires (List.ofFn x')).getD c false := by
    intro c hc0 hc x x' hxx
    refine E_agree C x x' 8 {c} (by omega) (by simp; omega) ?_ c (by simp)
    intro t ht
    apply hxx
    intro htt
    apply E_zero_not_mem C 8 {c} (by simp; omega) hgin0
    rw [htt] at ht
    simpa using ht

  have hin8 : (C.gates[8]'hi8').inputs = [0, 10] ∨ (C.gates[8]'hi8').inputs = [10, 0] := by
    have hl := hfan _ (List.getElem_mem hi8')
    revert h0i h10i hl
    generalize (C.gates[8]'hi8').inputs = l
    intro h0 h10 hl
    rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp at h0
    · simp at h0 h10
      omega
    · simp at h0 h10 ⊢
      omega
    · simp at hl
  have g8val : ∀ x : Fin 7 → Bool,
      (C.wires (List.ofFn x)).getD 15 false = (x 0 || (C.wires (List.ofFn x)).getD 10 false) := by
    intro x
    have h := wire_gate C x 8 hi8'
    rw [hiOr] at h
    have e0 : (pre C x 8).getD 0 false = x 0 := by
      rw [pre_getD_lt C x 8 0 (by omega) (by omega)]
      simpa using wire_getD_input C x 0
    have e10 : (pre C x 8).getD 10 false = (C.wires (List.ofFn x)).getD 10 false :=
      pre_getD_lt C x 8 10 (by omega) (by omega)
    rcases hin8 with h' | h'
    · rw [h'] at h
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
        Bool.or_false, e0, e10] at h
      exact h
    · rw [h'] at h
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
        Bool.or_false, e0, e10] at h
      rw [Bool.or_comm]
      exact h
  have hf_e0 : f7 (pt [true, false, false, false, false, false, false]) = false := by decide
  have hf_e01 : f7 (pt [true, true, false, false, false, false, false]) = true := by decide
  have hf_e1 : f7 (pt [false, true, false, false, false, false, false]) = false := by decide
  have he0 : pt [true, false, false, false, false, false, false] 0 = true := rfl
  by_cases ho : C.output = 15 ∨ C.output = 16
  swap
  ·
    push_neg at ho
    by_cases ho0 : C.output = 0
    · have h := hev (pt [true, false, false, false, false, false, false])
      rw [ho0, hf_e0] at h
      have h0 := wire_getD_input C (pt [true, false, false, false, false, false, false]) 0
      simp only [Fin.val_zero] at h0
      rw [h0, he0] at h
      exact absurd h (by decide)
    by_cases hlt : C.output < 15
    · have h1 := hev (pt [true, true, false, false, false, false, false])
      have h2 := hev (pt [false, true, false, false, false, false, false])
      have h := indep0 C.output ho0 hlt (pt [true, true, false, false, false, false, false])
        (pt [false, true, false, false, false, false, false]) (by decide)
      rw [h, h2, hf_e01, hf_e1] at h1
      exact absurd h1 (by decide)
    · have h1 := hev (pt [true, true, false, false, false, false, false])
      rw [List.getD_eq_default _ _ (by rw [wires_len]; omega), hf_e01] at h1
      exact absurd h1 (by decide)
  rcases ho with ho15 | ho16
  ·
    have h := hev (pt [true, false, false, false, false, false, false])
    rw [ho15, g8val, he0, Bool.true_or, hf_e0] at h
    exact absurd h (by decide)

  have h15 : 15 ∈ (C.gates[9]'hk9').inputs := by simpa using h15k
  have hl9 := hfan _ (List.getElem_mem hk9')
  have h09 : 0 ∉ (C.gates[9]'hk9').inputs := hno0 9 hk9' (by omega)
  have hpre15 : ∀ x, (pre C x 9).getD 15 false = (C.wires (List.ofFn x)).getD 15 false :=
    fun x => pre_getD_lt C x 9 15 (by omega) (by omega)
  have hw : ∀ x, (C.wires (List.ofFn x)).getD 16 false =
      GateOp.and.eval ((C.gates[9]'hk9').inputs.map fun i => (pre C x 9).getD i false) := by
    intro x
    have h := wire_gate C x 9 hk9'
    rw [hkAnd] at h
    exact h
  obtain ⟨c, hcmem, hc⟩ : ∃ c, c ∈ (C.gates[9]'hk9').inputs ∧ ∀ x,
      (C.wires (List.ofFn x)).getD 16 false =
        ((C.wires (List.ofFn x)).getD 15 false && (pre C x 9).getD c false) := by
    revert hw h15 hl9
    generalize (C.gates[9]'hk9').inputs = l
    intro h15 hl9 hw
    rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp at h15
    · simp at h15
      subst h15
      refine ⟨15, by simp, fun x => ?_⟩
      rw [hw x]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
      rw [hpre15 x, Bool.and_self]
    · simp at h15
      rcases h15 with rfl | rfl
      · refine ⟨b, by simp, fun x => ?_⟩
        rw [hw x]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
        rw [hpre15 x]
      · refine ⟨a, by simp, fun x => ?_⟩
        rw [hw x]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
        rw [hpre15 x, Bool.and_comm]
    · simp at hl9
  have hc0 : c ≠ 0 := fun h => h09 (h ▸ hcmem)
  by_cases hc15 : c = 15
  · subst hc15
    have h := hev (pt [true, false, false, false, false, false, false])
    rw [ho16, hc, hpre15, g8val, he0, Bool.true_or, Bool.and_self, hf_e0] at h
    exact absurd h (by decide)
  by_cases hc16 : 16 ≤ c
  · have h := hev (pt [true, true, false, false, false, false, false])
    rw [ho16, hc, pre_getD_ge C _ 9 c (by omega) (by omega), Bool.and_false, hf_e01] at h
    exact absurd h (by decide)
  have hclt : c < 15 := by omega
  have hcB : ∀ x, (pre C x 9).getD c false = (C.wires (List.ofFn x)).getD c false :=
    fun x => pre_getD_lt C x 9 c (by omega) (by omega)

  have key : ∀ a ap : Fin 7 → Bool, (∀ t : Fin 7, t ≠ 0 → a t = ap t) → a 0 = false →
      f7 ap = true → (C.wires (List.ofFn a)).getD 10 false = f7 a := by
    intro a ap hagree ha0 hfp
    have h1 := hev ap
    rw [ho16, hc, hcB, hfp, Bool.and_eq_true] at h1
    have hB : (C.wires (List.ofFn a)).getD c false = true := by
      rw [indep0 c hc0 hclt a ap hagree]
      exact h1.2
    have h2 := hev a
    rw [ho16, hc, hcB, g8val, ha0, hB, Bool.false_or, Bool.and_true] at h2
    exact h2

  have hE := E_card C hfan 4 {10} (by omega)
  rw [Finset.card_singleton] at hE
  have hEag : ∀ a a' : Fin 7 → Bool, (∀ t : Fin 7, t.val ∈ E C 4 {10} → a t = a' t) →
      (C.wires (List.ofFn a)).getD 10 false = (C.wires (List.ofFn a')).getD 10 false :=
    fun a a' h => E_agree C a a' 4 {10} (by omega) (by simp) h 10 (by simp)
  have close : ∀ (m : ℕ) (a a' ap ap' : Fin 7 → Bool), m ∉ E C 4 {10} →
      (∀ t : Fin 7, t ≠ 0 → a t = ap t) → (∀ t : Fin 7, t ≠ 0 → a' t = ap' t) →
      a 0 = false → a' 0 = false → f7 ap = true → f7 ap' = true →
      (∀ t : Fin 7, t.val ≠ m → a t = a' t) → f7 a ≠ f7 a' → False := by
    intro m a a' ap ap' hmE h1 h2 h3 h4 h5 h6 h7 h8
    apply h8
    rw [← key a ap h1 h3 h5, ← key a' ap' h2 h4 h6]
    exact hEag a a' (fun t ht => h7 t (fun h => hmE (h ▸ ht)))
  obtain ⟨m, hm, hmE⟩ : ∃ m ∈ ({1, 2, 3, 4, 5, 6} : Finset ℕ), m ∉ E C 4 {10} := by
    by_contra hcon
    push_neg at hcon
    have hsub := Finset.card_le_card (fun m hm => hcon m hm)
    have h6 : ({1, 2, 3, 4, 5, 6} : Finset ℕ).card = 6 := by decide
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
  · exact close 1 (pt [false, false, true, false, false, false, true])
      (pt [false, true, true, false, false, false, true])
      (pt [true, false, true, false, false, false, true])
      (pt [true, true, true, false, false, false, true]) hmE (by decide) (by decide) rfl rfl
      (by decide) (by decide) (by decide) (by decide)
  · exact close 2 (pt [false, true, false, false, false, false, false])
      (pt [false, true, true, false, false, false, false])
      (pt [true, true, false, false, false, false, false])
      (pt [true, true, true, false, false, false, false]) hmE (by decide) (by decide) rfl rfl
      (by decide) (by decide) (by decide) (by decide)
  · exact close 3 (pt [false, true, false, false, true, false, false])
      (pt [false, true, false, true, true, false, false])
      (pt [true, true, false, false, true, false, false])
      (pt [true, true, false, true, true, false, false]) hmE (by decide) (by decide) rfl rfl
      (by decide) (by decide) (by decide) (by decide)
  · exact close 4 (pt [false, true, false, true, false, false, false])
      (pt [false, true, false, true, true, false, false])
      (pt [true, true, false, true, false, false, false])
      (pt [true, true, false, true, true, false, false]) hmE (by decide) (by decide) rfl rfl
      (by decide) (by decide) (by decide) (by decide)
  · exact close 5 (pt [false, true, false, false, true, false, false])
      (pt [false, true, false, false, true, true, false])
      (pt [true, true, false, false, true, false, false])
      (pt [true, true, false, false, true, true, false]) hmE (by decide) (by decide) rfl rfl
      (by decide) (by decide) (by decide) (by decide)
  · exact close 6 (pt [false, true, false, false, false, true, false])
      (pt [false, true, false, false, false, true, true])
      (pt [true, true, false, false, false, true, false])
      (pt [true, true, false, false, false, true, true]) hmE (by decide) (by decide) rfl rfl
      (by decide) (by decide) (by decide) (by decide)
