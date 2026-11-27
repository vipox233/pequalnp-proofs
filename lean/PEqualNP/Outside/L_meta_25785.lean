import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25785

open PEqualNP.CircuitLowerBounds

def oneHot (n : ℕ) (x : Fin n) : List Bool :=
  List.ofFn (fun h : Fin n => decide (h = x))

def Allowed (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, g.op = GateOp.or ∧ g.inputs.length ≤ 2

def ComputesMatrix {p q : ℕ} (M : Fin p → Fin q → Bool) (C : Circuit) : Prop :=
  Allowed C ∧ ∀ i : Fin p, ∃ w : ℕ, ∀ j : Fin q,
    (C.wires (oneHot q j)).getD w false = M i j

def evalGates (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma wires_eq_evalGates (C : Circuit) (x : List Bool) :
    C.wires x = evalGates C.gates x := rfl

lemma evalGates_nil (x : List Bool) : evalGates [] x = x := rfl

lemma evalGates_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    evalGates (g :: gs) x =
      evalGates gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) := rfl

lemma evalGates_append (gs1 gs2 : List Gate) (x : List Bool) :
    evalGates (gs1 ++ gs2) x = evalGates gs2 (evalGates gs1 x) := by
  simp only [evalGates, List.foldl_append]

lemma evalGates_length (gs : List Gate) (x : List Bool) :
    (evalGates gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [evalGates]
  | cons g gs ih =>
    rw [evalGates_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma evalGates_getD_prefix (gs : List Gate) (x : List Bool) {v : ℕ} (hv : v < x.length) :
    (evalGates gs x).getD v false = x.getD v false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [evalGates_cons]
    have hv' : v < (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]).length := by
      simp only [List.length_append, List.length_singleton]
      omega
    rw [ih _ hv']
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hv]

lemma evalGates_getD_of_ge (gs : List Gate) (x : List Bool) {v : ℕ}
    (hv : x.length + gs.length ≤ v) :
    (evalGates gs x).getD v false = false := by
  have hlen : (evalGates gs x).length ≤ v := by
    rw [evalGates_length]
    exact hv
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen, Option.getD_none]

lemma evalGates_getD_gate (gs : List Gate) (x : List Bool) {t : ℕ} (ht : t < gs.length) :
    (evalGates gs x).getD (x.length + t) false =
      (gs[t]).op.eval ((gs[t]).inputs.map fun i =>
        if i < x.length + t then (evalGates gs x).getD i false else false) := by
  have hsplit : gs = gs.take t ++ gs[t] :: gs.drop (t + 1) := by
    have h1 := (List.take_append_drop t gs).symm
    have h2 : gs.drop t = gs[t] :: gs.drop (t + 1) := List.drop_eq_getElem_cons ht
    rw [h2] at h1
    exact h1
  conv_lhs => rw [hsplit]
  rw [evalGates_append, evalGates_cons]
  set w0 := evalGates (gs.take t) x
  have hw0len : w0.length = x.length + t := by
    rw [evalGates_length, List.length_take]
    omega
  have hlt : x.length + t < (w0 ++ [(gs[t]).op.eval ((gs[t]).inputs.map fun i => w0.getD i false)]).length := by
    simp only [List.length_append, List.length_singleton, hw0len]
    omega
  rw [evalGates_getD_prefix _ _ hlt]
  have hidx : (w0 ++ [(gs[t]).op.eval ((gs[t]).inputs.map fun i => w0.getD i false)]).getD (x.length + t) false =
      (gs[t]).op.eval ((gs[t]).inputs.map fun i => w0.getD i false) := by
    rw [← hw0len]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
      Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rw [hidx]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < x.length + t
  · simp only [hi, ↓reduceIte]
    conv_rhs => rw [hsplit]
    rw [evalGates_append]
    have hi' : i < w0.length := by omega
    exact (evalGates_getD_prefix _ _ hi').symm
  · simp only [hi, ↓reduceIte]
    have hge : w0.length ≤ i := by omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge, Option.getD_none]

lemma oneHot_length (n : ℕ) (x : Fin n) : (oneHot n x).length = n := by
  simp only [oneHot, List.length_ofFn]

lemma oneHot_getD (n : ℕ) (x : Fin n) {v : ℕ} (hv : v < n) :
    (oneHot n x).getD v false = decide (v = x.val) := by
  simp only [oneHot, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hv, ↓reduceDIte,
    Option.getD_some]
  exact decide_eq_decide.2 Fin.ext_iff

lemma oneHot_finCongr {n m : ℕ} (h : n = m) (x : Fin n) :
    oneHot n x = oneHot m (finCongr h x) := by
  subst h
  rfl

lemma wires_getD_input (C : Circuit) (n : ℕ) (x : Fin n) {v : ℕ} (hv : v < n) :
    (C.wires (oneHot n x)).getD v false = decide (v = x.val) := by
  rw [wires_eq_evalGates, evalGates_getD_prefix C.gates (oneHot n x) (by rw [oneHot_length]; exact hv)]
  exact oneHot_getD n x hv

lemma wires_getD_gate_or {C : Circuit} (hA : Allowed C) (x : List Bool) {t : ℕ}
    (ht : t < C.gates.length) :
    (C.wires x).getD (x.length + t) false = true ↔
      ∃ u ∈ (C.gates[t]).inputs, u < x.length + t ∧ (C.wires x).getD u false = true := by
  rw [wires_eq_evalGates, evalGates_getD_gate C.gates x ht]
  have hg : (C.gates[t]).op = GateOp.or := (hA _ (List.getElem_mem ht)).1
  rw [hg]
  simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, htrue⟩
    by_cases hlt : u < x.length + t
    · simp only [hlt, ↓reduceIte] at htrue
      exact ⟨u, hu, hlt, htrue⟩
    · simp only [hlt, ↓reduceIte] at htrue
      exact absurd htrue (by decide)
  · rintro ⟨u, hu, hlt, htrue⟩
    refine ⟨true, ⟨u, hu, ?_⟩, rfl⟩
    simp only [hlt, ↓reduceIte]
    exact htrue

lemma wires_append_prefix (C : Circuit) (gs : List Gate) (x : List Bool) {v : ℕ}
    (hv : v < x.length + C.gates.length) :
    ((Circuit.mk (C.gates ++ gs) C.output).wires x).getD v false = (C.wires x).getD v false := by
  rw [wires_eq_evalGates, evalGates_append, wires_eq_evalGates]
  apply evalGates_getD_prefix
  rw [evalGates_length]
  exact hv

lemma appendOr_one {p : ℕ} (D : Circuit) (a b : ℕ)
    (ha : a < p + D.gates.length) (hb : b < p + D.gates.length) (hD : Allowed D) :
    let D' : Circuit := ⟨D.gates ++ [⟨GateOp.or, [a, b]⟩], D.output⟩
    Allowed D' ∧ D'.gates.length = D.gates.length + 1 ∧
    (∀ x : List Bool, x.length = p → ∀ v < p + D.gates.length,
      (D'.wires x).getD v false = (D.wires x).getD v false) ∧
    (∀ x : List Bool, x.length = p →
      ((D'.wires x).getD (p + D.gates.length) false = true ↔
        (D.wires x).getD a false = true ∨ (D.wires x).getD b false = true)) := by
  intro D'
  have hA' : Allowed D' := by
    intro g hg
    simp only [D', List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hD g hg
    · exact ⟨rfl, by simp⟩
  refine ⟨hA', by simp [D'], ?_, ?_⟩
  · intro x hx v hv
    apply wires_append_prefix
    omega
  · intro x hx
    have ht : D.gates.length < D'.gates.length := by simp [D']
    have hgate := wires_getD_gate_or hA' x ht
    rw [hx] at hgate
    rw [hgate]
    have hget : D'.gates[D.gates.length]'ht = ⟨GateOp.or, [a, b]⟩ := by
      simp [D']
    rw [hget]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨u, rfl | rfl, hlt, hu⟩
      · left
        rwa [wires_append_prefix D _ x (by omega)] at hu
      · right
        rwa [wires_append_prefix D _ x (by omega)] at hu
    · rintro (hu | hu)
      · refine ⟨a, Or.inl rfl, ha, ?_⟩
        rwa [wires_append_prefix D _ x (by omega)]
      · refine ⟨b, Or.inr rfl, hb, ?_⟩
        rwa [wires_append_prefix D _ x (by omega)]

lemma appendOrList_exists {p : ℕ} (D : Circuit) (hD : Allowed D)
    (ws : List ℕ) (hne : ws ≠ []) (hws : ∀ a ∈ ws, a < p + D.gates.length) :
    ∃ (D' : Circuit) (w : ℕ),
      Allowed D' ∧
      D'.gates.length = D.gates.length + (ws.length - 1) ∧
      w < p + D'.gates.length ∧
      (∀ x : List Bool, x.length = p → ∀ v < p + D.gates.length,
        (D'.wires x).getD v false = (D.wires x).getD v false) ∧
      (∀ x : List Bool, x.length = p →
        ((D'.wires x).getD w false = true ↔ ∃ a ∈ ws, (D.wires x).getD a false = true)) := by
  cases ws with
  | nil => exact absurd rfl hne
  | cons a rest =>
    clear hne
    induction rest generalizing a D with
    | nil =>
      refine ⟨D, a, hD, by simp, hws a List.mem_cons_self, fun _ _ _ _ => rfl, ?_⟩
      intro x _
      simp
    | cons b rest' ih =>
      have ha : a < p + D.gates.length := hws a List.mem_cons_self
      have hb : b < p + D.gates.length := hws b (List.mem_cons_of_mem _ List.mem_cons_self)
      have h1 := appendOr_one D a b ha hb hD
      set D1 : Circuit := ⟨D.gates ++ [⟨GateOp.or, [a, b]⟩], D.output⟩
      have hA1 : Allowed D1 := h1.1
      have hlen1 : D1.gates.length = D.gates.length + 1 := h1.2.1
      have hpre1 := h1.2.2.1
      have hval1 := h1.2.2.2
      set w1 := p + D.gates.length
      have hws1 : ∀ c ∈ w1 :: rest', c < p + D1.gates.length := by
        intro c hc
        simp only [List.mem_cons] at hc
        rcases hc with rfl | hc
        · omega
        · have := hws c (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc))
          omega
      obtain ⟨D', w, hA', hlen', hw', hpre', hval'⟩ :=
        ih D1 hA1 w1 hws1
      refine ⟨D', w, hA', ?_, hw', ?_, ?_⟩
      · simp only [List.length_cons] at hlen' ⊢
        omega
      · intro x hx v hv
        rw [hpre' x hx v (by omega), hpre1 x hx v hv]
      · intro x hx
        rw [hval' x hx]
        simp only [List.mem_cons]
        constructor
        · rintro ⟨c, rfl | hc, hct⟩
          · rw [hval1 x hx] at hct
            rcases hct with hat | hbt
            · exact ⟨a, Or.inl rfl, hat⟩
            · exact ⟨b, Or.inr (Or.inl rfl), hbt⟩
          · have hc_lt : c < p + D.gates.length :=
              hws c (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc))
            rw [hpre1 x hx c hc_lt] at hct
            exact ⟨c, Or.inr (Or.inr hc), hct⟩
        · rintro ⟨c, rfl | rfl | hc, hct⟩
          · exact ⟨w1, Or.inl rfl, (hval1 x hx).2 (Or.inl hct)⟩
          · exact ⟨w1, Or.inl rfl, (hval1 x hx).2 (Or.inr hct)⟩
          · have hc_lt : c < p + D.gates.length :=
              hws c (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc))
            refine ⟨c, Or.inr hc, ?_⟩
            rwa [hpre1 x hx c hc_lt]

def gatePreds (C : Circuit) (q v : ℕ) : Finset ℕ :=
  if h : q ≤ v ∧ v < q + C.gates.length then
    ((C.gates[v - q]'(by omega)).inputs.filter (fun u => u < v)).toFinset
  else ∅

lemma gatePreds_lt {C : Circuit} {q u v : ℕ} (h : u ∈ gatePreds C q v) : u < v := by
  unfold gatePreds at h
  split_ifs at h with hv
  · simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at h
    exact h.2
  · simp at h

lemma gatePreds_bounds {C : Circuit} {q u v : ℕ} (h : u ∈ gatePreds C q v) :
    q ≤ v ∧ v < q + C.gates.length := by
  unfold gatePreds at h
  split_ifs at h with hv
  · exact hv
  · simp at h

lemma gatePreds_card_le {C : Circuit} (hA : Allowed C) (q v : ℕ) :
    (gatePreds C q v).card ≤ 2 := by
  unfold gatePreds
  split_ifs with hv
  · have ht : v - q < C.gates.length := by omega
    have h1 := List.toFinset_card_le ((C.gates[v - q]'ht).inputs.filter (fun u => u < v))
    have h2 := List.length_filter_le (fun u => decide (u < v)) (C.gates[v - q]'ht).inputs
    have h3 := (hA (C.gates[v - q]'ht) (List.getElem_mem ht)).2
    omega
  · simp

lemma mem_gatePreds_iff {C : Circuit} {q u v : ℕ} (hv1 : q ≤ v) (hv2 : v < q + C.gates.length) :
    u ∈ gatePreds C q v ↔ u ∈ (C.gates[v - q]'(by omega)).inputs ∧ u < v := by
  simp only [gatePreds, hv1, hv2, and_self, ↓reduceDIte, List.mem_toFinset, List.mem_filter,
    decide_eq_true_eq]

def reach (E : ℕ → Finset ℕ) (a b : ℕ) : Prop :=
  ∀ S : ℕ → Prop, S a → (∀ u v, S u → u ∈ E v → S v) → S b

lemma reach_refl {E : ℕ → Finset ℕ} {a : ℕ} : reach E a a :=
  fun _ ha _ => ha

lemma reach_step {E : ℕ → Finset ℕ} {a u v : ℕ} (h : reach E a u) (he : u ∈ E v) :
    reach E a v :=
  fun S ha hstep => hstep u v (h S ha hstep) he

lemma reach_trans {E : ℕ → Finset ℕ} {a b c : ℕ} (h1 : reach E a b) (h2 : reach E b c) :
    reach E a c :=
  fun S ha hstep => h2 S (h1 S ha hstep) hstep

lemma reach_cases_right {E : ℕ → Finset ℕ} {a b : ℕ} (h : reach E a b) :
    a = b ∨ ∃ u ∈ E b, reach E a u := by
  apply h (fun x => a = x ∨ ∃ u ∈ E x, reach E a u) (Or.inl rfl)
  intro u v hu huv
  rcases hu with rfl | ⟨w, hwu, haw⟩
  · exact Or.inr ⟨a, huv, reach_refl⟩
  · exact Or.inr ⟨u, huv, reach_step haw hwu⟩

lemma reach_cases_left {E : ℕ → Finset ℕ} {a b : ℕ} (h : reach E a b) :
    a = b ∨ ∃ w, a ∈ E w ∧ reach E w b := by
  apply h (fun x => a = x ∨ ∃ w, a ∈ E w ∧ reach E w x) (Or.inl rfl)
  intro u v hu huv
  rcases hu with rfl | ⟨w, haw, hwu⟩
  · exact Or.inr ⟨v, huv, reach_refl⟩
  · exact Or.inr ⟨w, haw, reach_step hwu huv⟩

lemma wires_iff_reach {C : Circuit} (hA : Allowed C) {q : ℕ} (j : Fin q) :
    ∀ v < q + C.gates.length,
      (C.wires (oneHot q j)).getD v false = true ↔ reach (gatePreds C q) j.val v := by
  intro v
  induction v using Nat.strong_induction_on with
  | ind v ih =>
    intro hv
    by_cases hvq : v < q
    · rw [wires_getD_input C q j hvq, decide_eq_true_eq]
      constructor
      · intro h
        rw [h]
        exact reach_refl
      · intro hr
        rcases reach_cases_right hr with h | ⟨u, hu, _⟩
        · exact h.symm
        · have hb := gatePreds_bounds hu
          omega
    · have hge : q ≤ v := by omega
      have ht : v - q < C.gates.length := by omega
      have hv_eq : (oneHot q j).length + (v - q) = v := by
        rw [oneHot_length]
        omega
      have hgate := wires_getD_gate_or hA (oneHot q j) ht
      rw [hv_eq] at hgate
      rw [hgate]
      constructor
      · rintro ⟨u, hu, hlt, hut⟩
        have hpred : u ∈ gatePreds C q v := (mem_gatePreds_iff hge hv).2 ⟨hu, hlt⟩
        have hru : reach (gatePreds C q) j.val u := (ih u hlt (by omega)).1 hut
        exact reach_step hru hpred
      · intro hr
        rcases reach_cases_right hr with h | ⟨u, hpred, hru⟩
        · omega
        · have hlt : u < v := gatePreds_lt hpred
          have hu : u ∈ (C.gates[v - q]'ht).inputs := ((mem_gatePreds_iff hge hv).1 hpred).1
          exact ⟨u, hu, hlt, (ih u hlt (by omega)).2 hru⟩

theorem transpose_computes {p q : ℕ} (M : Fin p → Fin q → Bool)
    (hrow : ∀ i : Fin p, ∃ j : Fin q, M i j = true)
    (hcol : ∀ j : Fin q, ∃ i : Fin p, M i j = true)
    {C : Circuit} (hC : ComputesMatrix M C) :
    ∃ D : Circuit, ComputesMatrix (fun j i => M i j) D ∧ D.gates.length + q ≤ C.gates.length + p := by
  classical
  obtain ⟨hA, hM⟩ := hC
  choose out hout using hM
  set m := C.gates.length
  have hout_lt : ∀ i : Fin p, out i < q + m := by
    intro i
    obtain ⟨j, hj⟩ := hrow i
    by_contra hge
    have hfalse : (C.wires (oneHot q j)).getD (out i) false = false := by
      rw [wires_eq_evalGates]
      apply evalGates_getD_of_ge
      rw [oneHot_length]
      omega
    rw [hout i j] at hfalse
    rw [hj] at hfalse
    exact Bool.noConfusion hfalse
  set E := gatePreds C q
  let live (v : ℕ) : Prop :=
    (∃ j : Fin q, reach E j.val v) ∧ (∃ i : Fin p, reach E v (out i))
  set L : Finset ℕ := (Finset.range (q + m)).filter live
  have hrange_L : Finset.range q ⊆ L := by
    intro v hv
    rw [Finset.mem_range] at hv
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), ?_, ?_⟩
    · exact ⟨⟨v, hv⟩, reach_refl⟩
    · obtain ⟨i, hi⟩ := hcol ⟨v, hv⟩
      have htrue : (C.wires (oneHot q ⟨v, hv⟩)).getD (out i) false = true := by
        rw [hout i ⟨v, hv⟩]
        exact hi
      exact ⟨i, (wires_iff_reach hA ⟨v, hv⟩ (out i) (hout_lt i)).1 htrue⟩
  have hout_L : ∀ i : Fin p, out i ∈ L := by
    intro i
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (hout_lt i), ?_, ⟨i, reach_refl⟩⟩
    obtain ⟨j, hj⟩ := hrow i
    have htrue : (C.wires (oneHot q j)).getD (out i) false = true := by
      rw [hout i j]
      exact hj
    exact ⟨j, (wires_iff_reach hA j (out i) (hout_lt i)).1 htrue⟩
  let Oout (v : ℕ) : Finset (Fin p) := Finset.univ.filter (fun i => out i = v)
  let Wout (v : ℕ) : Finset ℕ := L.filter (fun w => v ∈ E w)
  let outDeg (v : ℕ) : ℕ := (Oout v).card + (Wout v).card
  have houtDeg_pos : ∀ v ∈ L, 1 ≤ outDeg v := by
    intro v hv
    obtain ⟨_, ⟨j, hjv⟩, ⟨i, hvi⟩⟩ := Finset.mem_filter.1 hv
    rcases reach_cases_left hvi with rfl | ⟨w, hvw, hwi⟩
    · have hi : i ∈ Oout (out i) := Finset.mem_filter.2 ⟨Finset.mem_univ i, rfl⟩
      have hpos : 0 < (Oout (out i)).card := Finset.card_pos.2 ⟨i, hi⟩
      change 1 ≤ (Oout (out i)).card + (Wout (out i)).card
      omega
    · have hw_bounds := gatePreds_bounds hvw
      have hwL : w ∈ L :=
        Finset.mem_filter.2 ⟨Finset.mem_range.2 hw_bounds.2, ⟨j, reach_step hjv hvw⟩, ⟨i, hwi⟩⟩
      have hwW : w ∈ Wout v := Finset.mem_filter.2 ⟨hwL, hvw⟩
      have hpos : 0 < (Wout v).card := Finset.card_pos.2 ⟨w, hwW⟩
      change 1 ≤ (Oout v).card + (Wout v).card
      omega
  have hbuild : ∀ n ≤ q + m,
      ∃ (D : Circuit) (φ : ℕ → ℕ),
        Allowed D ∧
        D.gates.length = ∑ v ∈ L.filter (fun v => q + m - n ≤ v), (outDeg v - 1) ∧
        ∀ v ∈ L, q + m - n ≤ v →
          φ v < p + D.gates.length ∧
          ∀ i : Fin p, ((D.wires (oneHot p i)).getD (φ v) false = true ↔ reach E v (out i)) := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨⟨[], 0⟩, fun _ => 0, fun _ hg => by simp at hg, ?_, ?_⟩
      · have hemp : L.filter (fun v => q + m - 0 ≤ v) = ∅ := by
          ext v
          simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
          intro hv
          have hvlt : v < q + m := Finset.mem_range.1 (Finset.mem_filter.1 hv).1
          omega
        rw [hemp]
        simp
      · intro v hv hge
        have hvlt : v < q + m := Finset.mem_range.1 (Finset.mem_filter.1 hv).1
        omega
    | succ n ih =>
      intro hle
      obtain ⟨D, φ, hAD, hlenD, hφ⟩ := ih (by omega)
      set t := q + m - (n + 1)
      have ht_succ : q + m - n = t + 1 := by omega
      by_cases htL : t ∈ L
      · have hfilt : L.filter (fun v => t ≤ v) = insert t (L.filter (fun v => q + m - n ≤ v)) := by
          ext v
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hvL, htv⟩
            by_cases hvt : v = t
            · exact Or.inl hvt
            · exact Or.inr ⟨hvL, by omega⟩
          · rintro (rfl | ⟨hvL, htv⟩)
            · exact ⟨htL, le_refl _⟩
            · exact ⟨hvL, by omega⟩
        have ht_nmem : t ∉ L.filter (fun v => q + m - n ≤ v) := by
          simp only [Finset.mem_filter, not_and]
          intro _
          omega
        set ws : List ℕ := (Oout t).toList.map Fin.val ++ (Wout t).toList.map φ
        have hws_len : ws.length = outDeg t := by
          simp only [ws, List.length_append, List.length_map, Finset.length_toList, outDeg]
        have hws_ne : ws ≠ [] := by
          intro hemp
          have h0 : ws.length = 0 := by rw [hemp]; rfl
          have hpos := houtDeg_pos t htL
          omega
        have hws_lt : ∀ a ∈ ws, a < p + D.gates.length := by
          intro a ha
          simp only [ws, List.mem_append, List.mem_map, Finset.mem_toList] at ha
          rcases ha with ⟨i, _, rfl⟩ | ⟨w, hw, rfl⟩
          · omega
          · obtain ⟨hwL, htw⟩ := Finset.mem_filter.1 hw
            have hlt : t < w := gatePreds_lt htw
            exact (hφ w hwL (by omega)).1
        obtain ⟨D', wt, hAD', hlenD', hwt_lt, hpreD', hvalD'⟩ :=
          appendOrList_exists D hAD ws hws_ne hws_lt
        refine ⟨D', fun v => if v = t then wt else φ v, hAD', ?_, ?_⟩
        · rw [hfilt, Finset.sum_insert ht_nmem, hlenD', hlenD, hws_len]
          omega
        · intro v hvL htv
          by_cases hvt : v = t
          · subst hvt
            simp only [↓reduceIte]
            refine ⟨hwt_lt, fun i => ?_⟩
            rw [hvalD' (oneHot p i) (oneHot_length p i)]
            simp only [ws, List.mem_append, List.mem_map, Finset.mem_toList]
            constructor
            · rintro ⟨a, ⟨i', hi', rfl⟩ | ⟨w, hw, rfl⟩, hat⟩
              · rw [wires_getD_input D p i i'.isLt, decide_eq_true_eq] at hat
                have hii' : i' = i := Fin.ext hat
                subst hii'
                have heq : out i' = t := (Finset.mem_filter.1 hi').2
                rw [heq]
                exact reach_refl
              · obtain ⟨hwL, hvw⟩ := Finset.mem_filter.1 hw
                have hlt : t < w := gatePreds_lt hvw
                have hrw : reach E w (out i) := ((hφ w hwL (by omega)).2 i).1 hat
                exact reach_trans (reach_step reach_refl hvw) hrw
            · intro hrv
              rcases reach_cases_left hrv with hveq | ⟨w, hvw, hrw⟩
              · refine ⟨i.val, Or.inl ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ i, hveq.symm⟩, rfl⟩, ?_⟩
                rw [wires_getD_input D p i i.isLt]
                simp
              · obtain ⟨_, ⟨j, hjv⟩, _⟩ := Finset.mem_filter.1 hvL
                have hw_bounds := gatePreds_bounds hvw
                have hwL : w ∈ L :=
                  Finset.mem_filter.2 ⟨Finset.mem_range.2 hw_bounds.2, ⟨j, reach_step hjv hvw⟩, ⟨i, hrw⟩⟩
                have hwW : w ∈ Wout t := Finset.mem_filter.2 ⟨hwL, hvw⟩
                have hlt : t < w := gatePreds_lt hvw
                exact ⟨φ w, Or.inr ⟨w, hwW, rfl⟩, ((hφ w hwL (by omega)).2 i).2 hrw⟩
          · simp only [hvt, ↓reduceIte]
            have hvge : q + m - n ≤ v := by omega
            obtain ⟨hφlt, hφval⟩ := hφ v hvL hvge
            refine ⟨by omega, fun i => ?_⟩
            rw [hpreD' (oneHot p i) (oneHot_length p i) (φ v) hφlt]
            exact hφval i
      · have hfilt : L.filter (fun v => t ≤ v) = L.filter (fun v => q + m - n ≤ v) := by
          ext v
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hvL, htv⟩
            refine ⟨hvL, ?_⟩
            have hne : v ≠ t := fun h => htL (h ▸ hvL)
            omega
          · rintro ⟨hvL, htv⟩
            exact ⟨hvL, by omega⟩
        refine ⟨D, φ, hAD, ?_, ?_⟩
        · rw [hfilt]
          exact hlenD
        · intro v hvL htv
          have hne : v ≠ t := fun h => htL (h ▸ hvL)
          exact hφ v hvL (by omega)
  obtain ⟨D, φ, hAD, hlenD, hφ⟩ := hbuild (q + m) (le_refl _)
  have hfilt0 : L.filter (fun v => q + m - (q + m) ≤ v) = L := by
    ext v
    simp
  rw [hfilt0] at hlenD
  have hsum_sub : D.gates.length + L.card = ∑ v ∈ L, outDeg v := by
    rw [hlenD]
    have h1 : ∀ v ∈ L, (outDeg v - 1) + 1 = outDeg v := fun v hv => by
      have := houtDeg_pos v hv
      omega
    calc (∑ v ∈ L, (outDeg v - 1)) + L.card
        = ∑ v ∈ L, ((outDeg v - 1) + 1) := by rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
      _ = ∑ v ∈ L, outDeg v := Finset.sum_congr rfl h1
  have hsum_O : ∑ v ∈ L, (Oout v).card = p := by
    have h1 : ∀ v ∈ L, (Oout v).card = ∑ i : Fin p, if out i = v then 1 else 0 := by
      intro v _
      simp only [Oout, Finset.card_filter]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    have h2 : ∀ i : Fin p, (∑ v ∈ L, if out i = v then 1 else 0) = 1 := by
      intro i
      rw [Finset.sum_ite_eq L (out i)]
      simp [hout_L i]
    simp [h2]
  have hsum_W : ∑ v ∈ L, (Wout v).card ≤ 2 * (L.card - q) := by
    have h1 : ∀ v ∈ L, (Wout v).card = ∑ w ∈ L, if v ∈ E w then 1 else 0 := by
      intro v _
      simp only [Wout, Finset.card_filter]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    have h2 : ∀ w ∈ L, (∑ v ∈ L, if v ∈ E w then 1 else 0) ≤ if q ≤ w then 2 else 0 := by
      intro w _
      by_cases hqw : q ≤ w
      · simp only [hqw, ↓reduceIte]
        have hle1 : (∑ v ∈ L, if v ∈ E w then 1 else 0) = (L.filter (fun v => v ∈ E w)).card := by
          simp only [Finset.card_filter]
        rw [hle1]
        have hsub : L.filter (fun v => v ∈ E w) ⊆ E w := fun v hv => (Finset.mem_filter.1 hv).2
        exact le_trans (Finset.card_le_card hsub) (gatePreds_card_le hA q w)
      · simp only [hqw, ↓reduceIte]
        have hzero : ∀ v ∈ L, (if v ∈ E w then 1 else 0) = 0 := by
          intro v _
          have hne : v ∉ E w := fun hv => hqw (gatePreds_bounds hv).1
          simp [hne]
        rw [Finset.sum_eq_zero hzero]
    have h3 : (∑ w ∈ L, ∑ v ∈ L, if v ∈ E w then 1 else 0) ≤
        ∑ w ∈ L, if q ≤ w then 2 else 0 := Finset.sum_le_sum h2
    have h4 : (∑ w ∈ L, if q ≤ w then 2 else 0) = 2 * (L.filter (fun w => q ≤ w)).card := by
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
    have h5 : (L.filter (fun w => w < q)).card = q := by
      have heq : L.filter (fun w => w < q) = Finset.range q := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨fun h => h.2, fun h => ⟨hrange_L (Finset.mem_range.2 h), h⟩⟩
      rw [heq, Finset.card_range]
    have h6 : (L.filter (fun w => w < q)).card + (L.filter (fun w => q ≤ w)).card = L.card := by
      have hdisj : Disjoint (L.filter (fun w => w < q)) (L.filter (fun w => q ≤ w)) := by
        rw [Finset.disjoint_filter]
        intro w _ h1 h2
        omega
      have hunion : L.filter (fun w => w < q) ∪ L.filter (fun w => q ≤ w) = L := by
        ext w
        simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
        · intro h
          by_cases hlt : w < q
          · exact Or.inl ⟨h, hlt⟩
          · exact Or.inr ⟨h, by omega⟩
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
    omega
  have hL_le : L.card ≤ q + m := by
    have hsub : L ⊆ Finset.range (q + m) := Finset.filter_subset _ _
    exact le_trans (Finset.card_le_card hsub) (by rw [Finset.card_range])
  have hL_ge : q ≤ L.card := by
    have h := Finset.card_le_card hrange_L
    rwa [Finset.card_range] at h
  have hsum_split : ∑ v ∈ L, outDeg v = (∑ v ∈ L, (Oout v).card) + ∑ v ∈ L, (Wout v).card := by
    exact Finset.sum_add_distrib
  refine ⟨D, ⟨hAD, ?_⟩, ?_⟩
  · intro j
    have hjL : j.val ∈ L := hrange_L (Finset.mem_range.2 j.isLt)
    refine ⟨φ j.val, fun i => ?_⟩
    apply Bool.eq_iff_iff.2
    rw [(hφ j.val hjL (by omega)).2 i]
    rw [← wires_iff_reach hA j (out i) (hout_lt i), hout i j]
  · omega

lemma testBit_add_two_pow {a n j : ℕ} (ha : a < 2 ^ n) :
    (a + 2 ^ n).testBit j = if j = n then true else a.testBit j := by
  have hpow : 0 < 2 ^ n := Nat.two_pow_pos n
  by_cases hjn : j = n
  · subst hjn
    simp only [↓reduceIte, Nat.testBit_eq_decide_div_mod_eq]
    have hdiv : (a + 2 ^ j) / 2 ^ j = 1 := by
      rw [Nat.add_div_right _ hpow, Nat.div_eq_of_lt ha]
    rw [hdiv]
    rfl
  · simp only [hjn, ↓reduceIte]
    by_cases hlt : j < n
    · simp only [Nat.testBit_eq_decide_div_mod_eq]
      have hsub : n = j + (n - j - 1 + 1) := by omega
      have hpow_eq : 2 ^ n = 2 ^ j * (2 * 2 ^ (n - j - 1)) := by
        conv_lhs => rw [hsub]
        rw [Nat.pow_add, Nat.pow_succ]
        ring
      have hdiv : (a + 2 ^ n) / 2 ^ j = a / 2 ^ j + 2 * 2 ^ (n - j - 1) := by
        rw [hpow_eq, Nat.add_mul_div_left _ _ (Nat.two_pow_pos j)]
      rw [hdiv]
      have hmod : (a / 2 ^ j + 2 * 2 ^ (n - j - 1)) % 2 = (a / 2 ^ j) % 2 := by omega
      rw [hmod]
    · have hge : n + 1 ≤ j := by omega
      have hpow_le : 2 ^ (n + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) hge
      have hlt1 : a + 2 ^ n < 2 ^ j := by
        have : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [Nat.pow_succ]; omega
        omega
      have hlt2 : a < 2 ^ j := by omega
      rw [Nat.testBit_lt_two_pow hlt1, Nat.testBit_lt_two_pow hlt2]

def toNum {n : ℕ} (f : Fin n → Bool) : ℕ :=
  ∑ i : Fin n, if f i then 2 ^ i.val else 0

lemma toNum_lt {n : ℕ} (f : Fin n → Bool) : toNum f < 2 ^ n := by
  induction n with
  | zero => simp [toNum]
  | succ n ih =>
    rw [toNum, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    have h1 : (∑ i : Fin n, if f i.castSucc then 2 ^ i.val else 0) < 2 ^ n :=
      ih (fun i => f i.castSucc)
    have hpow : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [Nat.pow_succ]; omega
    cases f (Fin.last n) <;> simp <;> omega

lemma testBit_toNum {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    Nat.testBit (toNum f) i.val = f i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    rw [toNum, Fin.sum_univ_castSucc]
    set S := toNum (fun j : Fin n => f j.castSucc)
    have hS : S < 2 ^ n := toNum_lt _
    have hSeq : (∑ j : Fin n, if f j.castSucc then 2 ^ j.castSucc.val else 0) = S := rfl
    rw [hSeq]
    cases hlast : f (Fin.last n)
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      refine Fin.lastCases ?_ ?_ i
      · rw [Fin.val_last, hlast]
        exact Nat.testBit_lt_two_pow hS
      · intro j
        exact ih (fun x => f x.castSucc) j
    · simp only [↓reduceIte, Fin.val_last]
      rw [testBit_add_two_pow hS]
      refine Fin.lastCases ?_ ?_ i
      · simp [hlast]
      · intro j
        have hne : j.val ≠ n := Nat.ne_of_lt j.isLt
        simp only [Fin.val_castSucc, hne, ↓reduceIte]
        exact ih (fun x => f x.castSucc) j

lemma nat_eq_of_testBit_lt {n a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n)
    (h : ∀ j : Fin n, a.testBit j.val = b.testBit j.val) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < n
  · exact h ⟨j, hj⟩
  · have hle : 2 ^ n ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha hle),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hb hle)]

lemma nat_pos_has_testBit {n u : ℕ} (hu : u < 2 ^ n) (hne : u ≠ 0) :
    ∃ t : Fin n, u.testBit t.val = true := by
  by_contra hall
  push Not at hall
  have heq : u = 0 := by
    apply nat_eq_of_testBit_lt hu (Nat.two_pow_pos n)
    intro t
    have hf := hall t
    cases h : u.testBit t.val
    · simp
    · exact absurd h hf
  exact hne heq

lemma two_pow_ge_succ (n : ℕ) (hn : 1 ≤ n) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => decide
    | succ m =>
      have h1 := ih (by omega)
      have h2 : 2 ^ (m + 2) = 2 ^ (m + 1) + 2 ^ (m + 1) := by rw [Nat.pow_succ]; omega
      omega

lemma succAbove_val {q : ℕ} (x0 : Fin (q + 1)) (j : Fin q) :
    (x0.succAbove j).val = if j.val < x0.val then j.val else j.val + 1 := by
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> simp

lemma drop_zero_col {p q : ℕ} (M : Fin p → Fin (q + 1) → Bool) (x0 : Fin (q + 1))
    (hzero : ∀ i, M i x0 = false) (hrow : ∀ i, ∃ j, M i j = true)
    {C : Circuit} (hC : ComputesMatrix M C) :
    ∃ C' : Circuit,
      ComputesMatrix (fun i (j : Fin q) => M i (x0.succAbove j)) C' ∧
      C'.gates.length = C.gates.length := by
  obtain ⟨hA, hM⟩ := hC
  let bad (v : ℕ) : Bool := (C.wires (oneHot (q + 1) x0)).getD v false
  let reidx (v : ℕ) : ℕ := if v < x0.val then v else v - 1
  let gates' : List Gate :=
    List.ofFn (fun t : Fin C.gates.length =>
      ⟨GateOp.or, (((C.gates[t.val]).inputs.filter (fun u => u < q + 1 + t.val && !bad u)).map reidx)⟩)
  let C' : Circuit := ⟨gates', 0⟩
  have hlen' : C'.gates.length = C.gates.length := by simp [C', gates']
  have hA' : Allowed C' := by
    intro g hg
    simp only [C', gates', List.mem_ofFn] at hg
    obtain ⟨t, rfl⟩ := hg
    refine ⟨rfl, ?_⟩
    rw [List.length_map]
    exact le_trans (List.length_filter_le _ _) (hA _ (List.getElem_mem t.isLt)).2
  have hsim : ∀ v < q + 1 + C.gates.length, bad v = false →
      ∀ j : Fin q,
        (C'.wires (oneHot q j)).getD (reidx v) false =
          (C.wires (oneHot (q + 1) (x0.succAbove j))).getD v false := by
    intro v
    induction v using Nat.strong_induction_on with
    | ind v ih =>
      intro hv hbv j
      by_cases hvq : v < q + 1
      · have hne : v ≠ x0.val := by
          intro heq
          have hbtrue : bad v = true := by
            dsimp only [bad]
            rw [wires_getD_input C (q + 1) x0 hvq, heq]
            simp
          rw [hbtrue] at hbv
          exact Bool.noConfusion hbv
        have hre_lt : reidx v < q := by
          simp only [reidx]
          split_ifs <;> omega
        rw [wires_getD_input C' q j hre_lt, wires_getD_input C (q + 1) (x0.succAbove j) hvq]
        have hiff : reidx v = j.val ↔ v = (x0.succAbove j).val := by
          rw [succAbove_val]
          dsimp only [reidx]
          split_ifs <;> omega
        exact decide_eq_decide.2 hiff
      · set t := v - (q + 1)
        have ht : t < C.gates.length := by omega
        have hveq : q + 1 + t = v := by omega
        have hre_eq : reidx v = q + t := by
          simp only [reidx]
          have : ¬ v < x0.val := by omega
          simp only [this, ↓reduceIte]
          omega
        rw [hre_eq]
        apply Bool.eq_iff_iff.2
        have hlt' : t < C'.gates.length := by omega
        have hL := wires_getD_gate_or hA' (oneHot q j) hlt'
        rw [oneHot_length] at hL
        have hR := wires_getD_gate_or hA (oneHot (q + 1) (x0.succAbove j)) ht
        rw [oneHot_length, hveq] at hR
        rw [hL, hR]
        have hget' : C'.gates[t]'hlt' =
            ⟨GateOp.or, (((C.gates[t]'ht).inputs.filter (fun u => u < q + 1 + t && !bad u)).map reidx)⟩ := by
          simp [C', gates']
        rw [hget']
        simp only [List.mem_map, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
        constructor
        · rintro ⟨w, ⟨u, ⟨hu, hult, hbu⟩, rfl⟩, _, hwt⟩
          refine ⟨u, hu, by omega, ?_⟩
          rwa [← ih u (by omega) (by omega) hbu j]
        · rintro ⟨u, hu, hult, hut⟩
          have hbu : bad u = false := by
            by_contra hbu_ne
            have hbu_true : bad u = true := by
              cases h : bad u
              · exact absurd h hbu_ne
              · rfl
            have hbv_true : bad v = true := by
              have hb := wires_getD_gate_or hA (oneHot (q + 1) x0) ht
              rw [oneHot_length, hveq] at hb
              exact hb.2 ⟨u, hu, hult, hbu_true⟩
            rw [hbv_true] at hbv
            exact Bool.noConfusion hbv
          have hre_lt : reidx u < q + t := by
            have hne_u : u ≠ x0.val := by
              intro heq
              have hbt : bad u = true := by
                dsimp only [bad]
                rw [wires_getD_input C (q + 1) x0 (heq.symm ▸ x0.isLt), heq]
                simp
              rw [hbt] at hbu
              exact Bool.noConfusion hbu
            simp only [reidx]
            split_ifs <;> omega
          refine ⟨reidx u, ⟨u, ⟨hu, by omega, hbu⟩, rfl⟩, hre_lt, ?_⟩
          rw [ih u (by omega) (by omega) hbu j]
          exact hut
  refine ⟨C', ⟨hA', ?_⟩, hlen'⟩
  intro i
  obtain ⟨w, hw⟩ := hM i
  have hbw : bad w = false := by
    simp only [bad, hw x0, hzero i]
  have hw_lt : w < q + 1 + C.gates.length := by
    obtain ⟨j, hj⟩ := hrow i
    by_contra hge
    have hfalse : (C.wires (oneHot (q + 1) j)).getD w false = false := by
      rw [wires_eq_evalGates]
      apply evalGates_getD_of_ge
      rw [oneHot_length]
      omega
    rw [hw j, hj] at hfalse
    exact Bool.noConfusion hfalse
  refine ⟨reidx w, fun j => ?_⟩
  rw [hsim w hw_lt hbw j, hw (x0.succAbove j)]

lemma insert_zero_col {p q : ℕ} (M : Fin p → Fin (q + 1) → Bool) (x0 : Fin (q + 1))
    (hzero : ∀ i, M i x0 = false) (hrow : ∀ i, ∃ j : Fin q, M i (x0.succAbove j) = true)
    {C' : Circuit} (hC' : ComputesMatrix (fun i (j : Fin q) => M i (x0.succAbove j)) C') :
    ∃ C : Circuit, ComputesMatrix M C ∧ C.gates.length = C'.gates.length := by
  obtain ⟨hA', hM'⟩ := hC'
  let emb (v : ℕ) : ℕ := if v < x0.val then v else v + 1
  let gates : List Gate :=
    List.ofFn (fun t : Fin C'.gates.length =>
      ⟨GateOp.or, (((C'.gates[t.val]).inputs.filter (fun u => u < q + t.val)).map emb)⟩)
  let C : Circuit := ⟨gates, 0⟩
  have hlen : C.gates.length = C'.gates.length := by simp [C, gates]
  have hA : Allowed C := by
    intro g hg
    simp only [C, gates, List.mem_ofFn] at hg
    obtain ⟨t, rfl⟩ := hg
    refine ⟨rfl, ?_⟩
    rw [List.length_map]
    exact le_trans (List.length_filter_le _ _) (hA' _ (List.getElem_mem t.isLt)).2
  have hsim : ∀ v < q + C'.gates.length, ∀ j : Fin q,
      (C.wires (oneHot (q + 1) (x0.succAbove j))).getD (emb v) false =
        (C'.wires (oneHot q j)).getD v false := by
    intro v
    induction v using Nat.strong_induction_on with
    | ind v ih =>
      intro hv j
      by_cases hvq : v < q
      · have hemb_lt : emb v < q + 1 := by
          simp only [emb]
          split_ifs <;> omega
        rw [wires_getD_input C (q + 1) (x0.succAbove j) hemb_lt,
            wires_getD_input C' q j hvq]
        have hiff : emb v = (x0.succAbove j).val ↔ v = j.val := by
          rw [succAbove_val]
          dsimp only [emb]
          split_ifs <;> omega
        exact decide_eq_decide.2 hiff
      · set t := v - q
        have ht : t < C'.gates.length := by omega
        have hveq : q + t = v := by omega
        have hemb_eq : emb v = q + 1 + t := by
          simp only [emb]
          have : ¬ v < x0.val := by omega
          simp only [this, ↓reduceIte]
          omega
        rw [hemb_eq]
        apply Bool.eq_iff_iff.2
        have hlt : t < C.gates.length := by omega
        have hL := wires_getD_gate_or hA (oneHot (q + 1) (x0.succAbove j)) hlt
        rw [oneHot_length] at hL
        have hR := wires_getD_gate_or hA' (oneHot q j) ht
        rw [oneHot_length, hveq] at hR
        rw [hL, hR]
        have hget : C.gates[t]'hlt =
            ⟨GateOp.or, (((C'.gates[t]'ht).inputs.filter (fun u => u < q + t)).map emb)⟩ := by
          simp [C, gates]
        rw [hget]
        simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro ⟨w, ⟨u, ⟨hu, hult⟩, rfl⟩, _, hwt⟩
          refine ⟨u, hu, by omega, ?_⟩
          rwa [← ih u (by omega) (by omega) j]
        · rintro ⟨u, hu, hult, hut⟩
          have hemb_lt : emb u < q + 1 + t := by
            simp only [emb]
            split_ifs <;> omega
          refine ⟨emb u, ⟨u, ⟨hu, by omega⟩, rfl⟩, hemb_lt, ?_⟩
          rw [ih u (by omega) (by omega) j]
          exact hut
  have hsim0 : ∀ v < q + C'.gates.length,
      (C.wires (oneHot (q + 1) x0)).getD (emb v) false = false := by
    intro v
    induction v using Nat.strong_induction_on with
    | ind v ih =>
      intro hv
      by_cases hvq : v < q
      · have hemb_lt : emb v < q + 1 := by
          simp only [emb]
          split_ifs <;> omega
        rw [wires_getD_input C (q + 1) x0 hemb_lt]
        have hne : emb v ≠ x0.val := by
          simp only [emb]
          split_ifs <;> omega
        simp [hne]
      · set t := v - q
        have ht : t < C'.gates.length := by omega
        have hemb_eq : emb v = q + 1 + t := by
          simp only [emb]
          have : ¬ v < x0.val := by omega
          simp only [this, ↓reduceIte]
          omega
        rw [hemb_eq]
        by_contra hne
        have htrue : (C.wires (oneHot (q + 1) x0)).getD (q + 1 + t) false = true := by
          cases h : (C.wires (oneHot (q + 1) x0)).getD (q + 1 + t) false
          · exact absurd h hne
          · rfl
        have hlt : t < C.gates.length := by omega
        have hL := wires_getD_gate_or hA (oneHot (q + 1) x0) hlt
        rw [oneHot_length] at hL
        obtain ⟨w, hw, _, hwt⟩ := hL.1 htrue
        have hget : C.gates[t]'hlt =
            ⟨GateOp.or, (((C'.gates[t]'ht).inputs.filter (fun u => u < q + t)).map emb)⟩ := by
          simp [C, gates]
        rw [hget] at hw
        simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at hw
        obtain ⟨u, ⟨_, hult⟩, rfl⟩ := hw
        have hf := ih u (by omega) (by omega)
        rw [hf] at hwt
        exact Bool.noConfusion hwt
  refine ⟨C, ⟨hA, ?_⟩, hlen⟩
  intro i
  obtain ⟨w, hw⟩ := hM' i
  have hw_lt : w < q + C'.gates.length := by
    obtain ⟨j, hj⟩ := hrow i
    by_contra hge
    have hfalse : (C'.wires (oneHot q j)).getD w false = false := by
      rw [wires_eq_evalGates]
      apply evalGates_getD_of_ge
      rw [oneHot_length]
      omega
    rw [hw j] at hfalse
    dsimp only at hfalse
    rw [hj] at hfalse
    exact Bool.noConfusion hfalse
  refine ⟨emb w, fun x => ?_⟩
  by_cases hx : x = x0
  · subst hx
    rw [hsim0 w hw_lt, hzero i]
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hx
    rw [hsim w hw_lt j, hw j]

lemma embed_extra_inputs {a b : ℕ} (D : Circuit) (hD : Allowed D) :
    let emb : ℕ → ℕ := fun v => if v < a then v else v + b
    ∃ C : Circuit,
      Allowed C ∧ C.gates.length = D.gates.length ∧
      (∀ v < a + D.gates.length, ∀ i : Fin (a + b),
        (C.wires (oneHot (a + b) i)).getD (emb v) false =
          if hi : i.val < a then (D.wires (oneHot a ⟨i.val, hi⟩)).getD v false else false) := by
  intro emb
  let gates : List Gate :=
    List.ofFn (fun t : Fin D.gates.length =>
      ⟨GateOp.or, (((D.gates[t.val]).inputs.filter (fun u => u < a + t.val)).map emb)⟩)
  let C : Circuit := ⟨gates, 0⟩
  have hlen : C.gates.length = D.gates.length := by simp [C, gates]
  have hA : Allowed C := by
    intro g hg
    simp only [C, gates, List.mem_ofFn] at hg
    obtain ⟨t, rfl⟩ := hg
    refine ⟨rfl, ?_⟩
    rw [List.length_map]
    exact le_trans (List.length_filter_le _ _) (hD _ (List.getElem_mem t.isLt)).2
  refine ⟨C, hA, hlen, ?_⟩
  intro v
  induction v using Nat.strong_induction_on with
  | ind v ih =>
    intro hv i
    by_cases hva : v < a
    · have hemb : emb v = v := by simp only [emb, hva, ↓reduceIte]
      rw [hemb, wires_getD_input C (a + b) i (by omega)]
      by_cases hi : i.val < a
      · simp only [hi, ↓reduceDIte]
        rw [wires_getD_input D a ⟨i.val, hi⟩ hva]
      · simp only [hi, ↓reduceDIte]
        have hne : v ≠ i.val := by omega
        simp [hne]
    · set t := v - a
      have ht : t < D.gates.length := by omega
      have hveq : a + t = v := by omega
      have hemb : emb v = a + b + t := by
        simp only [emb, hva, ↓reduceIte]
        omega
      rw [hemb]
      have hlt : t < C.gates.length := by omega
      have hget : C.gates[t]'hlt =
          ⟨GateOp.or, (((D.gates[t]'ht).inputs.filter (fun u => u < a + t)).map emb)⟩ := by
        simp [C, gates]
      by_cases hi : i.val < a
      · simp only [hi, ↓reduceDIte]
        apply Bool.eq_iff_iff.2
        have hL := wires_getD_gate_or hA (oneHot (a + b) i) hlt
        rw [oneHot_length] at hL
        have hR := wires_getD_gate_or hD (oneHot a ⟨i.val, hi⟩) ht
        rw [oneHot_length, hveq] at hR
        rw [hL, hR, hget]
        simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro ⟨w, ⟨u, ⟨hu, hult⟩, rfl⟩, _, hwt⟩
          refine ⟨u, hu, by omega, ?_⟩
          have hih := ih u (by omega) (by omega) i
          simp only [hi, ↓reduceDIte] at hih
          rwa [← hih]
        · rintro ⟨u, hu, hult, hut⟩
          have hemb_lt : emb u < a + b + t := by
            simp only [emb]
            split_ifs <;> omega
          refine ⟨emb u, ⟨u, ⟨hu, by omega⟩, rfl⟩, hemb_lt, ?_⟩
          have hih := ih u (by omega) (by omega) i
          simp only [hi, ↓reduceDIte] at hih
          rwa [hih]
      · simp only [hi, ↓reduceDIte]
        by_contra hne
        have htrue : (C.wires (oneHot (a + b) i)).getD (a + b + t) false = true := by
          cases h : (C.wires (oneHot (a + b) i)).getD (a + b + t) false
          · exact absurd h hne
          · rfl
        have hL := wires_getD_gate_or hA (oneHot (a + b) i) hlt
        rw [oneHot_length] at hL
        obtain ⟨w, hw, _, hwt⟩ := hL.1 htrue
        rw [hget] at hw
        simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at hw
        obtain ⟨u, ⟨_, hult⟩, rfl⟩ := hw
        have hih := ih u (by omega) (by omega) i
        simp only [hi, ↓reduceDIte] at hih
        rw [hih] at hwt
        exact Bool.noConfusion hwt

lemma build_all_nonempty (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : Circuit, Allowed C ∧ C.gates.length = 2 ^ n - n - 1 ∧
      ∀ m : ℕ, 1 ≤ m → m < 2 ^ n →
        ∃ w < n + C.gates.length, ∀ i : Fin n,
          (C.wires (oneHot n i)).getD w false = Nat.testBit m i.val := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      refine ⟨⟨[], 0⟩, fun _ hg => by simp at hg, by decide, ?_⟩
      intro m hm1 hm2
      have hm : m = 1 := by omega
      subst hm
      refine ⟨0, by decide, fun i => ?_⟩
      fin_cases i
      rfl
    | succ n0 =>
      set n := n0 + 1
      obtain ⟨Cn, hAn, hlenn, hwn⟩ := ih (by omega)
      classical
      have hw_ex : ∀ m : Fin (2 ^ n - 1),
          ∃ w < n + Cn.gates.length, ∀ i : Fin n,
            (Cn.wires (oneHot n i)).getD w false = Nat.testBit (m.val + 1) i.val := by
        intro m
        exact hwn (m.val + 1) (by omega) (by omega)
      choose wn hwn_lt hwn_val using hw_ex
      obtain ⟨C1, hA1, hlen1, hsim1⟩ := embed_extra_inputs (a := n) (b := 1) Cn hAn
      let emb : ℕ → ℕ := fun v => if v < n then v else v + 1
      let extra : List Gate :=
        List.ofFn (fun t : Fin (2 ^ n - 1) => ⟨GateOp.or, [emb (wn t), n]⟩)
      let C2 : Circuit := ⟨C1.gates ++ extra, C1.output⟩
      have hA2 : Allowed C2 := by
        intro g hg
        simp only [C2, List.mem_append, extra, List.mem_ofFn] at hg
        rcases hg with hg | ⟨t, rfl⟩
        · exact hA1 g hg
        · exact ⟨rfl, by simp⟩
      have hpow_ge : n + 1 ≤ 2 ^ n := two_pow_ge_succ n (by omega)
      have hlen2 : C2.gates.length = 2 ^ (n + 1) - (n + 1) - 1 := by
        simp only [C2, List.length_append, hlen1, hlenn, extra, List.length_ofFn]
        have hpow : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [Nat.pow_succ]; omega
        omega
      refine ⟨C2, hA2, hlen2, ?_⟩
      intro m hm1 hm2
      by_cases hm_lt : m < 2 ^ n
      · set t : Fin (2 ^ n - 1) := ⟨m - 1, by omega⟩
        have ht_eq : t.val + 1 = m := by simp only [t]; omega
        have hemb_lt : emb (wn t) < n + 1 + C1.gates.length := by
          have := hwn_lt t
          simp only [emb]
          split_ifs <;> omega
        refine ⟨emb (wn t), by simp only [C2, List.length_append]; omega, fun i => ?_⟩
        rw [wires_append_prefix C1 extra (oneHot (n + 1) i) (by rw [oneHot_length]; exact hemb_lt)]
        rw [hsim1 (wn t) (hwn_lt t) i]
        by_cases hi : i.val < n
        · simp only [hi, ↓reduceDIte, hwn_val t ⟨i.val, hi⟩, ht_eq]
        · simp only [hi, ↓reduceDIte]
          have hin : i.val = n := by omega
          rw [hin, Nat.testBit_lt_two_pow hm_lt]
      · by_cases hm_eq : m = 2 ^ n
        · subst hm_eq
          refine ⟨n, by omega, fun i => ?_⟩
          rw [wires_getD_input C2 (n + 1) i (by omega), Nat.testBit_two_pow]
        · set t : Fin (2 ^ n - 1) := ⟨m - 2 ^ n - 1, by
            have hpow : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [Nat.pow_succ]; omega
            omega⟩
          have ht_eq : t.val + 1 = m - 2 ^ n := by simp only [t]; omega
          have hm_decomp : (t.val + 1) + 2 ^ n = m := by omega
          have hgate_idx : C1.gates.length + t.val < C2.gates.length := by
            simp only [C2, List.length_append, extra, List.length_ofFn]
            omega
          refine ⟨n + 1 + (C1.gates.length + t.val), by omega, fun i => ?_⟩
          apply Bool.eq_iff_iff.2
          have hG := wires_getD_gate_or hA2 (oneHot (n + 1) i) hgate_idx
          rw [oneHot_length] at hG
          rw [hG]
          have hget : C2.gates[C1.gates.length + t.val]'hgate_idx =
              ⟨GateOp.or, [emb (wn t), n]⟩ := by
            simp [C2, extra]
          rw [hget]
          have hemb_lt : emb (wn t) < n + 1 + C1.gates.length := by
            have := hwn_lt t
            simp only [emb]
            split_ifs <;> omega
          have hw1_eval : (C2.wires (oneHot (n + 1) i)).getD (emb (wn t)) false =
              if hi : i.val < n then Nat.testBit (t.val + 1) i.val else false := by
            rw [wires_append_prefix C1 extra (oneHot (n + 1) i) (by rw [oneHot_length]; exact hemb_lt)]
            rw [hsim1 (wn t) (hwn_lt t) i]
            by_cases hi : i.val < n
            · simp only [hi, ↓reduceDIte, hwn_val t ⟨i.val, hi⟩]
            · simp only [hi, ↓reduceDIte]
          have hwn_eval : (C2.wires (oneHot (n + 1) i)).getD n false = decide (n = i.val) :=
            wires_getD_input C2 (n + 1) i (by omega)
          rw [← hm_decomp, testBit_add_two_pow (by omega)]
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          constructor
          · rintro ⟨u, rfl | rfl, _, hut⟩
            · rw [hw1_eval] at hut
              by_cases hi : i.val < n
              · simp only [hi, ↓reduceDIte] at hut
                have hne : i.val ≠ n := by omega
                simp [hne, hut]
              · simp only [hi, ↓reduceDIte] at hut
                exact Bool.noConfusion hut
            · rw [hwn_eval, decide_eq_true_eq] at hut
              simp [hut.symm]
          · intro hbit
            by_cases hin : i.val = n
            · refine ⟨n, Or.inr rfl, by omega, ?_⟩
              rw [hwn_eval, decide_eq_true_eq]
              exact hin.symm
            · simp only [hin, ↓reduceIte] at hbit
              have hi : i.val < n := by omega
              refine ⟨emb (wn t), Or.inl rfl, by omega, ?_⟩
              rw [hw1_eval]
              simp only [hi, ↓reduceDIte]
              exact hbit

lemma finset_pos_bijection (S : Finset ℕ) :
    let pos : ℕ → ℕ := fun t => (S.filter (· < t)).card
    (∀ t ∈ S, pos t < S.card) ∧
    (∀ t1 ∈ S, ∀ t2 ∈ S, t1 < t2 → pos t1 < pos t2) ∧
    (∀ m < S.card, ∃ t ∈ S, pos t = m) := by
  intro pos
  have hlt : ∀ t ∈ S, pos t < S.card := by
    intro t ht
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.filter_subset _ _, fun heq => ?_⟩
    have hmem : t ∈ S.filter (· < t) := heq.symm ▸ ht
    exact Nat.lt_irrefl t (Finset.mem_filter.1 hmem).2
  have hmono : ∀ t1 ∈ S, ∀ t2 ∈ S, t1 < t2 → pos t1 < pos t2 := by
    intro t1 ht1 t2 ht2 h12
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨fun x hx => ?_, fun heq => ?_⟩
    · obtain ⟨hxS, hx1⟩ := Finset.mem_filter.1 hx
      exact Finset.mem_filter.2 ⟨hxS, lt_trans hx1 h12⟩
    · have hmem : t1 ∈ S.filter (· < t2) := Finset.mem_filter.2 ⟨ht1, h12⟩
      rw [← heq] at hmem
      exact Nat.lt_irrefl t1 (Finset.mem_filter.1 hmem).2
  refine ⟨hlt, hmono, ?_⟩
  intro m hm
  have hinj : Set.InjOn pos (S : Set ℕ) := by
    intro a ha b hb hab
    rcases lt_trichotomy a b with h1 | h2 | h3
    · exact absurd hab (Nat.ne_of_lt (hmono a ha b hb h1))
    · exact h2
    · exact absurd hab.symm (Nat.ne_of_lt (hmono b hb a ha h3))
  have hsub : S.image pos ⊆ Finset.range S.card := by
    intro y hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hy
    exact Finset.mem_range.2 (hlt t ht)
  have hcard : (S.image pos).card = (Finset.range S.card).card := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have heq : S.image pos = Finset.range S.card := Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
  have hmem : m ∈ S.image pos := by
    rw [heq]
    exact Finset.mem_range.2 hm
  exact Finset.mem_image.1 hmem

lemma adjoin_optional_bits {k r : ℕ} (hrk : r ≤ k) (C0 : Circuit) (hA0 : Allowed C0)
    (w0 : Fin (2 ^ r) → ℕ) (hw0_lt : ∀ y, w0 y < k + r + C0.gates.length)
    (hw0_val : ∀ y : Fin (2 ^ r), ∀ i : Fin (k + r),
      (C0.wires (oneHot (k + r) i)).getD (w0 y) false =
        if i.val < 2 * r then (Nat.testBit y.val (i.val / 2) == decide (i.val % 2 = 1)) else false) :
    ∀ m ≤ k - r, ∃ C : Circuit, Allowed C ∧ C.gates.length = C0.gates.length + 2 ^ r * (2 ^ m - 1) ∧
      ∀ (y : Fin (2 ^ r)) (u : Fin (2 ^ m)),
        ∃ w < k + r + C.gates.length, ∀ i : Fin (k + r),
          (C.wires (oneHot (k + r) i)).getD w false =
            if i.val < 2 * r then (Nat.testBit y.val (i.val / 2) == decide (i.val % 2 = 1))
            else if i.val < 2 * r + m then Nat.testBit u.val (i.val - 2 * r)
            else false := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨C0, hA0, by simp, ?_⟩
    intro y u
    refine ⟨w0 y, hw0_lt y, fun i => ?_⟩
    rw [hw0_val y i]
    by_cases hi : i.val < 2 * r
    · simp only [hi, ↓reduceIte]
    · simp only [Nat.add_zero, hi, ↓reduceIte]
  | succ m ih =>
    intro hm
    obtain ⟨Cm, hAm, hlenm, hwm⟩ := ih (by omega)
    classical
    choose wm hwm_lt hwm_val using hwm
    have hpow_pos : 0 < 2 ^ m := Nat.two_pow_pos m
    let extra : List Gate :=
      List.ofFn (fun idx : Fin (2 ^ r * 2 ^ m) =>
        let y : Fin (2 ^ r) := ⟨idx.val / 2 ^ m, Nat.div_lt_of_lt_mul (lt_of_lt_of_eq idx.isLt (Nat.mul_comm _ _))⟩
        let u : Fin (2 ^ m) := ⟨idx.val % 2 ^ m, Nat.mod_lt _ hpow_pos⟩
        ⟨GateOp.or, [wm y u, 2 * r + m]⟩)
    let C1 : Circuit := ⟨Cm.gates ++ extra, Cm.output⟩
    have hA1 : Allowed C1 := by
      intro g hg
      simp only [C1, List.mem_append, extra, List.mem_ofFn] at hg
      rcases hg with hg | ⟨idx, rfl⟩
      · exact hAm g hg
      · exact ⟨rfl, by simp⟩
    have hlen1 : C1.gates.length = C0.gates.length + 2 ^ r * (2 ^ (m + 1) - 1) := by
      simp only [C1, List.length_append, hlenm, extra, List.length_ofFn]
      have hpow : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [Nat.pow_succ]; omega
      have h1 : 1 ≤ 2 ^ m := Nat.two_pow_pos m
      have hsub : 2 ^ (m + 1) - 1 = (2 ^ m - 1) + 2 ^ m := by omega
      rw [hsub, Nat.mul_add]
      omega
    refine ⟨C1, hA1, hlen1, ?_⟩
    intro y u'
    by_cases hu' : u'.val < 2 ^ m
    · set u : Fin (2 ^ m) := ⟨u'.val, hu'⟩
      refine ⟨wm y u, by simp only [C1, List.length_append]; have := hwm_lt y u; omega, fun i => ?_⟩
      rw [wires_append_prefix Cm extra (oneHot (k + r) i) (by rw [oneHot_length]; exact hwm_lt y u)]
      rw [hwm_val y u i]
      by_cases hi1 : i.val < 2 * r
      · simp only [hi1, ↓reduceIte]
      · simp only [hi1, ↓reduceIte]
        by_cases hi2 : i.val < 2 * r + m
        · have hi3 : i.val < 2 * r + (m + 1) := by omega
          simp only [hi2, hi3, ↓reduceIte, u]
        · by_cases hi3 : i.val < 2 * r + (m + 1)
          · simp only [hi2, hi3, ↓reduceIte]
            have heq : i.val - 2 * r = m := by omega
            rw [heq, Nat.testBit_lt_two_pow hu']
          · simp only [hi2, hi3, ↓reduceIte]
    · set u : Fin (2 ^ m) := ⟨u'.val - 2 ^ m, by
        have hpow : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [Nat.pow_succ]; omega
        have := u'.isLt
        omega⟩
      have hu_decomp : u.val + 2 ^ m = u'.val := by simp only [u]; omega
      have hidx_lt : y.val * 2 ^ m + u.val < 2 ^ r * 2 ^ m := by
        have hy : y.val + 1 ≤ 2 ^ r := y.isLt
        have hu : u.val < 2 ^ m := u.isLt
        calc y.val * 2 ^ m + u.val
            < y.val * 2 ^ m + 2 ^ m := Nat.add_lt_add_left hu _
          _ = (y.val + 1) * 2 ^ m := by rw [Nat.succ_mul]
          _ ≤ 2 ^ r * 2 ^ m := Nat.mul_le_mul_right _ hy
      set idx : Fin (2 ^ r * 2 ^ m) := ⟨y.val * 2 ^ m + u.val, hidx_lt⟩
      have hgate_lt : Cm.gates.length + idx.val < C1.gates.length := by
        simp only [C1, List.length_append, extra, List.length_ofFn]
        omega
      refine ⟨k + r + (Cm.gates.length + idx.val), by omega, fun i => ?_⟩
      apply Bool.eq_iff_iff.2
      have hG := wires_getD_gate_or hA1 (oneHot (k + r) i) hgate_lt
      rw [oneHot_length] at hG
      rw [hG]
      have hdiv : idx.val / 2 ^ m = y.val := by
        simp only [idx]
        rw [mul_comm y.val, Nat.mul_add_div hpow_pos, Nat.div_eq_of_lt u.isLt, Nat.add_zero]
      have hmod : idx.val % 2 ^ m = u.val := by
        simp only [idx]
        rw [mul_comm y.val, Nat.mul_add_mod, Nat.mod_eq_of_lt u.isLt]
      have hget : C1.gates[Cm.gates.length + idx.val]'hgate_lt =
          ⟨GateOp.or, [wm y u, 2 * r + m]⟩ := by
        have h1 : C1.gates[Cm.gates.length + idx.val]'hgate_lt = extra[idx.val]'(by simp [extra]) := by
          simp [C1]
        rw [h1]
        simp only [extra, List.getElem_ofFn]
        have hy_eq : (⟨idx.val / 2 ^ m, Nat.div_lt_of_lt_mul (lt_of_lt_of_eq idx.isLt (Nat.mul_comm _ _))⟩ : Fin (2 ^ r)) = y :=
          Fin.ext hdiv
        have hu_eq : (⟨idx.val % 2 ^ m, Nat.mod_lt _ hpow_pos⟩ : Fin (2 ^ m)) = u :=
          Fin.ext hmod
        rw [hy_eq, hu_eq]
      rw [hget]
      have hwm_eval : (C1.wires (oneHot (k + r) i)).getD (wm y u) false =
          (Cm.wires (oneHot (k + r) i)).getD (wm y u) false :=
        wires_append_prefix Cm extra (oneHot (k + r) i) (by rw [oneHot_length]; exact hwm_lt y u)
      have hopt_eval : (C1.wires (oneHot (k + r) i)).getD (2 * r + m) false =
          decide (2 * r + m = i.val) :=
        wires_getD_input C1 (k + r) i (by omega)
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro ⟨a, rfl | rfl, _, hat⟩
        · rw [hwm_eval, hwm_val y u i] at hat
          by_cases hi1 : i.val < 2 * r
          · simp only [hi1, ↓reduceIte] at hat ⊢
            exact hat
          · simp only [hi1, ↓reduceIte] at hat ⊢
            by_cases hi2 : i.val < 2 * r + m
            · have hi3 : i.val < 2 * r + (m + 1) := by omega
              simp only [hi2, ↓reduceIte] at hat
              simp only [hi3, ↓reduceIte]
              rw [← hu_decomp, testBit_add_two_pow u.isLt]
              have hne : i.val - 2 * r ≠ m := by omega
              simp [hne, hat]
            · simp only [hi2, ↓reduceIte] at hat
              exact Bool.noConfusion hat
        · rw [hopt_eval, decide_eq_true_eq] at hat
          have hi1 : ¬ i.val < 2 * r := by omega
          have hi3 : i.val < 2 * r + (m + 1) := by omega
          simp only [hi1, hi3, ↓reduceIte]
          rw [← hu_decomp, testBit_add_two_pow u.isLt]
          have heq : i.val - 2 * r = m := by omega
          simp [heq]
      · intro hbit
        by_cases hi1 : i.val < 2 * r
        · simp only [hi1, ↓reduceIte] at hbit
          refine ⟨wm y u, Or.inl rfl, by have := hwm_lt y u; omega, ?_⟩
          rw [hwm_eval, hwm_val y u i]
          simp [hi1, hbit]
        · simp only [hi1, ↓reduceIte] at hbit
          by_cases hi3 : i.val < 2 * r + (m + 1)
          · simp only [hi3, ↓reduceIte] at hbit
            rw [← hu_decomp, testBit_add_two_pow u.isLt] at hbit
            by_cases him : i.val - 2 * r = m
            · refine ⟨2 * r + m, Or.inr rfl, by omega, ?_⟩
              rw [hopt_eval, decide_eq_true_eq]
              omega
            · simp only [him, ↓reduceIte] at hbit
              have hi2 : i.val < 2 * r + m := by omega
              refine ⟨wm y u, Or.inl rfl, by have := hwm_lt y u; omega, ?_⟩
              rw [hwm_eval, hwm_val y u i]
              simp [hi1, hi2, hbit]
          · simp only [hi3, ↓reduceIte] at hbit
            exact Bool.noConfusion hbit

lemma solve_r_zero (k : ℕ) (hk : 2 ≤ k) (sign : Fin k → Bool) (s : ℕ) :
    (∃ C : Circuit, Allowed C ∧
      (∀ j : Fin k, ∃ w : ℕ, ∀ x : Fin (2 ^ k),
        (C.wires (oneHot (2 ^ k) x)).getD w false = (Nat.testBit x.val j.val == sign j)) ∧
      C.gates.length + k ≤ s) ↔
    2 * (2 ^ k - k - 1) + k ≤ s := by
  let M : Fin k → Fin (2 ^ k) → Bool := fun j x => (Nat.testBit x.val j.val == sign j)
  let x0 : Fin (2 ^ k) := ⟨toNum (fun j : Fin k => !(sign j)), toNum_lt _⟩
  have hx0_zero : ∀ j : Fin k, M j x0 = false := by
    intro j
    simp only [M, x0, testBit_toNum]
    cases sign j <;> rfl
  have hpow_pos : 1 ≤ 2 ^ k := Nat.two_pow_pos k
  set q := 2 ^ k - 1
  have hq1 : q + 1 = 2 ^ k := by omega
  let eFin : Fin (q + 1) ≃ Fin (2 ^ k) := finCongr hq1
  let M1 : Fin k → Fin (q + 1) → Bool := fun j x => M j (eFin x)
  let x0' : Fin (q + 1) := eFin.symm x0
  have hx0'_zero : ∀ j : Fin k, M1 j x0' = false := by
    intro j
    simp only [M1, x0', Equiv.apply_symm_apply]
    exact hx0_zero j
  let Mlive : Fin k → Fin q → Bool := fun j u => M1 j (x0'.succAbove u)
  have hMlive_row : ∀ j : Fin k, ∃ u : Fin q, Mlive j u = true := by
    intro j
    let x : Fin (2 ^ k) := ⟨toNum (fun i : Fin k => sign i), toNum_lt _⟩
    have hx_ne : x ≠ x0 := by
      intro heq
      have h0 := congrArg (fun a : Fin (2 ^ k) => Nat.testBit a.val 0) heq
      simp only [x, x0] at h0
      have h0' : Nat.testBit (toNum (fun i : Fin k => sign i)) (⟨0, by omega⟩ : Fin k).val =
          Nat.testBit (toNum (fun i : Fin k => !(sign i))) (⟨0, by omega⟩ : Fin k).val := h0
      rw [testBit_toNum, testBit_toNum] at h0'
      cases h : sign ⟨0, by omega⟩ <;> rw [h] at h0' <;> exact Bool.noConfusion h0'
    have hx'_ne : eFin.symm x ≠ x0' := fun h => hx_ne (eFin.symm.injective h)
    obtain ⟨u, hu⟩ := Fin.exists_succAbove_eq hx'_ne
    refine ⟨u, ?_⟩
    simp only [Mlive, hu, M1, Equiv.apply_symm_apply, M, x, testBit_toNum, beq_self_eq_true]
  have hM1_row : ∀ j : Fin k, ∃ x : Fin (q + 1), M1 j x = true := by
    intro j
    obtain ⟨u, hu⟩ := hMlive_row j
    exact ⟨x0'.succAbove u, hu⟩
  have hMlive_col : ∀ u : Fin q, ∃ j : Fin k, Mlive j u = true := by
    intro u
    by_contra hall
    push Not at hall
    have hne : x0'.succAbove u ≠ x0' := Fin.succAbove_ne x0' u
    have hne2 : eFin (x0'.succAbove u) ≠ x0 := by
      intro heq
      apply hne
      have := congrArg eFin.symm heq
      simp only [Equiv.symm_apply_apply] at this
      exact this
    apply hne2
    apply Fin.ext
    apply nat_eq_of_testBit_lt (eFin (x0'.succAbove u)).isLt x0.isLt
    intro j
    have hf : Mlive j u = false := by
      cases h : Mlive j u
      · rfl
      · exact absurd h (hall j)
    simp only [Mlive, M1, M] at hf
    simp only [x0, testBit_toNum]
    cases hb : Nat.testBit (eFin (x0'.succAbove u)).val j.val <;>
      cases hs : sign j <;> simp [hb, hs] at hf ⊢
  have hMlive_inj : ∀ u1 u2 : Fin q, (∀ j : Fin k, Mlive j u1 = Mlive j u2) → u1 = u2 := by
    intro u1 u2 h
    apply Fin.succAbove_right_injective (p := x0')
    apply eFin.injective
    apply Fin.ext
    apply nat_eq_of_testBit_lt (eFin (x0'.succAbove u1)).isLt (eFin (x0'.succAbove u2)).isLt
    intro j
    have hj := h j
    simp only [Mlive, M1, M] at hj
    cases h1 : Nat.testBit (eFin (x0'.succAbove u1)).val j.val <;>
      cases h2 : Nat.testBit (eFin (x0'.succAbove u2)).val j.val <;>
      cases hs : sign j <;> simp [h1, h2, hs] at hj ⊢
  have hcong : ∀ C : Circuit, ComputesMatrix M C ↔ ComputesMatrix M1 C := by
    intro C
    constructor
    · rintro ⟨hA, hM⟩
      refine ⟨hA, fun j => ?_⟩
      obtain ⟨w, hw⟩ := hM j
      refine ⟨w, fun x => ?_⟩
      rw [oneHot_finCongr hq1 x]
      exact hw (eFin x)
    · rintro ⟨hA, hM1⟩
      refine ⟨hA, fun j => ?_⟩
      obtain ⟨w, hw⟩ := hM1 j
      refine ⟨w, fun x => ?_⟩
      have hx := hw (eFin.symm x)
      rw [oneHot_finCongr hq1.symm x]
      simpa [eFin, M1] using hx
  constructor
  · rintro ⟨C, hA, hM, hsz⟩
    have hC1 : ComputesMatrix M1 C := (hcong C).1 ⟨hA, hM⟩
    obtain ⟨Clive, hClive, hlen_live⟩ := drop_zero_col M1 x0' hx0'_zero hM1_row hC1
    obtain ⟨D, ⟨hAD, hMD⟩, hszD⟩ := transpose_computes Mlive hMlive_row hMlive_col hClive
    choose z hz using hMD
    dsimp only at hz
    have hz_lt : ∀ u : Fin q, z u < k + D.gates.length := by
      intro u
      obtain ⟨j, hj⟩ := hMlive_col u
      by_contra hge
      have hfalse : (D.wires (oneHot k j)).getD (z u) false = false := by
        rw [wires_eq_evalGates]
        apply evalGates_getD_of_ge
        rw [oneHot_length]
        omega
      rw [hz u j, hj] at hfalse
      exact Bool.noConfusion hfalse
    have hz_inj : Function.Injective z := by
      intro u1 u2 heq
      apply hMlive_inj u1 u2
      intro j
      rw [← hz u1 j, ← hz u2 j, heq]
    have hq_le : q ≤ k + D.gates.length := by
      have hsub : Finset.univ.image z ⊆ Finset.range (k + D.gates.length) := by
        intro w hw
        obtain ⟨u, _, rfl⟩ := Finset.mem_image.1 hw
        exact Finset.mem_range.2 (hz_lt u)
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective _ hz_inj, Finset.card_univ, Fintype.card_fin,
          Finset.card_range] at hcard
      exact hcard
    have hpow_ge : k + 1 ≤ 2 ^ k := two_pow_ge_succ k (by omega)
    omega
  · intro hs
    obtain ⟨D, hAD, hlenD, hD⟩ := build_all_nonempty k (by omega)
    have hMD : ComputesMatrix (fun u j => Mlive j u) D := by
      refine ⟨hAD, fun u => ?_⟩
      let m := toNum (fun j : Fin k => Mlive j u)
      have hm_lt : m < 2 ^ k := toNum_lt _
      have hm_pos : 1 ≤ m := by
        obtain ⟨j, hj⟩ := hMlive_col u
        by_contra h0
        have hm0 : m = 0 := by omega
        have hbit := testBit_toNum (fun j : Fin k => Mlive j u) j
        change Nat.testBit m j.val = Mlive j u at hbit
        rw [hm0, Nat.zero_testBit] at hbit
        rw [hj] at hbit
        exact Bool.noConfusion hbit
      obtain ⟨w, _, hw⟩ := hD m hm_pos hm_lt
      refine ⟨w, fun j => ?_⟩
      rw [hw j]
      exact testBit_toNum (fun j : Fin k => Mlive j u) j
    obtain ⟨Clive, hClive, hszLive⟩ :=
      transpose_computes (fun u j => Mlive j u) hMlive_col hMlive_row hMD
    obtain ⟨C, hC1, hlenC⟩ := insert_zero_col M1 x0' hx0'_zero hMlive_row hClive
    have hC : ComputesMatrix M C := (hcong C).2 hC1
    have hpow_ge : k + 1 ≤ 2 ^ k := two_pow_ge_succ k (by omega)
    refine ⟨C, hC.1, hC.2, ?_⟩
    omega

lemma decide_two_mul_add_mod (t : ℕ) (b : Bool) :
    decide ((2 * t + if b then 1 else 0) % 2 = 1) = b := by
  cases b <;> simp

lemma two_mul_add_div (t : ℕ) (b : Bool) :
    (2 * t + if b then 1 else 0) / 2 = t := by
  cases b
  · simp
  · simp only [↓reduceIte]; omega

lemma decide_bool_mod (b : Bool) :
    decide ((if b then 1 else 0) % 2 = 1) = b := by
  cases b <;> rfl

lemma solve_r_pos (k : ℕ) (hk : 2 ≤ k) (B : Finset (Fin k)) (sign : Fin k → Bool) (s : ℕ)
    (hr : 0 < B.card) :
    let r := B.card
    (∃ C : Circuit, Allowed C ∧
      (∀ j : Fin k, ∃ w : ℕ, ∀ x : Fin (2 ^ k),
        (C.wires (oneHot (2 ^ k) x)).getD w false = (Nat.testBit x.val j.val == sign j)) ∧
      (∀ j ∈ B, ∃ w : ℕ, ∀ x : Fin (2 ^ k),
        (C.wires (oneHot (2 ^ k) x)).getD w false = (Nat.testBit x.val j.val == !(sign j))) ∧
      C.gates.length + (k - r) ≤ s) ↔
    ∃ d : ℕ,
      (∃ D : Circuit, Allowed D ∧ D.gates.length ≤ d ∧
        ∀ y : Fin (2 ^ r), ∃ z : ℕ, ∀ i : Fin (2 * r),
          (D.wires (oneHot (2 * r) i)).getD z false =
            (Nat.testBit y.val (i.val / 2) == decide (i.val % 2 = 1))) ∧
      d + 2 * 2 ^ k ≤ s + 2 ^ r + 2 * r := by
  classical
  intro r
  have hrk : r ≤ k := by
    have h := Finset.card_le_univ B
    rwa [Fintype.card_fin] at h
  have hBcard : Fintype.card { j : Fin k // j ∈ B } = r := Fintype.card_coe B
  have hCcard : Fintype.card { j : Fin k // j ∉ B } = k - r := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, hBcard]
  let eB : Fin r ≃ { j : Fin k // j ∈ B } := (Fintype.equivFinOfCardEq hBcard).symm
  let eC : Fin (k - r) ≃ { j : Fin k // j ∉ B } := (Fintype.equivFinOfCardEq hCcard).symm
  let M : Fin (k + r) → Fin (2 ^ k) → Bool := fun i x =>
    if hi : i.val < 2 * r then
      let j := (eB ⟨i.val / 2, by omega⟩).val
      (Nat.testBit x.val j.val == decide (i.val % 2 = 1))
    else
      let j := (eC ⟨i.val - 2 * r, by omega⟩).val
      (Nat.testBit x.val j.val == sign j)
  have hM_equiv : ∀ C : Circuit,
      ((∀ j : Fin k, ∃ w : ℕ, ∀ x : Fin (2 ^ k),
          (C.wires (oneHot (2 ^ k) x)).getD w false = (Nat.testBit x.val j.val == sign j)) ∧
       (∀ j ∈ B, ∃ w : ℕ, ∀ x : Fin (2 ^ k),
          (C.wires (oneHot (2 ^ k) x)).getD w false = (Nat.testBit x.val j.val == !(sign j)))) ↔
      (∀ i : Fin (k + r), ∃ w : ℕ, ∀ x : Fin (2 ^ k),
        (C.wires (oneHot (2 ^ k) x)).getD w false = M i x) := by
    intro C
    constructor
    · rintro ⟨h1, h2⟩ i
      simp only [M]
      by_cases hi : i.val < 2 * r
      · simp only [hi, ↓reduceDIte]
        set jb := eB ⟨i.val / 2, by omega⟩
        by_cases hb : decide (i.val % 2 = 1) = sign jb.val
        · rw [hb]
          exact h1 jb.val
        · have hb' : decide (i.val % 2 = 1) = !(sign jb.val) := by
            cases h : decide (i.val % 2 = 1) <;> cases hs : sign jb.val <;>
              simp [h, hs] at hb ⊢
          rw [hb']
          exact h2 jb.val jb.property
      · simp only [hi, ↓reduceDIte]
        exact h1 (eC ⟨i.val - 2 * r, by omega⟩).val
    · intro hM
      refine ⟨fun j => ?_, fun j hj => ?_⟩
      · by_cases hj : j ∈ B
        · set t := eB.symm ⟨j, hj⟩
          let b := sign j
          let i : Fin (k + r) := ⟨2 * t.val + if b then 1 else 0, by cases b <;> simp <;> omega⟩
          obtain ⟨w, hw⟩ := hM i
          refine ⟨w, fun x => ?_⟩
          rw [hw x]
          have hi : i.val < 2 * r := by simp only [i]; cases b <;> simp <;> omega
          simp only [M, hi, ↓reduceDIte]
          have hdiv : i.val / 2 = t.val := two_mul_add_div t.val b
          have hmod : decide (i.val % 2 = 1) = b := decide_two_mul_add_mod t.val b
          have heq : (⟨i.val / 2, by omega⟩ : Fin r) = t := Fin.ext hdiv
          rw [heq, hmod]
          simp [t, b]
        · set t := eC.symm ⟨j, hj⟩
          let i : Fin (k + r) := ⟨2 * r + t.val, by omega⟩
          obtain ⟨w, hw⟩ := hM i
          refine ⟨w, fun x => ?_⟩
          rw [hw x]
          have hi : ¬ i.val < 2 * r := by simp only [i]; omega
          simp only [M, hi, ↓reduceDIte]
          have hsub : (⟨i.val - 2 * r, by omega⟩ : Fin (k - r)) = t := by
            apply Fin.ext
            simp only [i]
            omega
          rw [hsub]
          simp [t]
      · set t := eB.symm ⟨j, hj⟩
        let b := !(sign j)
        let i : Fin (k + r) := ⟨2 * t.val + if b then 1 else 0, by cases b <;> simp <;> omega⟩
        obtain ⟨w, hw⟩ := hM i
        refine ⟨w, fun x => ?_⟩
        rw [hw x]
        have hi : i.val < 2 * r := by simp only [i]; cases b <;> simp <;> omega
        simp only [M, hi, ↓reduceDIte]
        have hdiv : i.val / 2 = t.val := two_mul_add_div t.val b
        have hmod : decide (i.val % 2 = 1) = b := decide_two_mul_add_mod t.val b
        have heq : (⟨i.val / 2, by omega⟩ : Fin r) = t := Fin.ext hdiv
        rw [heq, hmod]
        simp [t, b]
  let pack (y : Fin (2 ^ r)) (u : Fin (2 ^ (k - r))) : Fin (2 ^ k) :=
    ⟨toNum (fun j : Fin k =>
      if hj : j ∈ B then
        Nat.testBit y.val (eB.symm ⟨j, hj⟩).val
      else
        (Nat.testBit u.val (eC.symm ⟨j, hj⟩).val == sign j)), toNum_lt _⟩
  let unpack (x : Fin (2 ^ k)) : Fin (2 ^ r) × Fin (2 ^ (k - r)) :=
    (⟨toNum (fun t : Fin r => Nat.testBit x.val (eB t).val.val), toNum_lt _⟩,
     ⟨toNum (fun t : Fin (k - r) => (Nat.testBit x.val (eC t).val.val == sign (eC t).val)), toNum_lt _⟩)
  have hpack_M : ∀ y u (i : Fin (k + r)),
      M i (pack y u) =
        if i.val < 2 * r then (Nat.testBit y.val (i.val / 2) == decide (i.val % 2 = 1))
        else Nat.testBit u.val (i.val - 2 * r) := by
    intro y u i
    by_cases hi : i.val < 2 * r
    · simp only [M, hi, ↓reduceDIte, ↓reduceIte, pack, testBit_toNum]
      have hmem : (eB ⟨i.val / 2, by omega⟩).val ∈ B := (eB ⟨i.val / 2, by omega⟩).property
      simp only [hmem, ↓reduceDIte]
      have hsym : (eB.symm ⟨(eB ⟨i.val / 2, by omega⟩).val, hmem⟩).val = i.val / 2 := by
        have h := eB.symm_apply_apply ⟨i.val / 2, by omega⟩
        exact congrArg Fin.val h
      rw [hsym]
    · simp only [M, hi, ↓reduceDIte, ↓reduceIte, pack, testBit_toNum]
      have hnmem : (eC ⟨i.val - 2 * r, by omega⟩).val ∉ B := (eC ⟨i.val - 2 * r, by omega⟩).property
      simp only [hnmem, ↓reduceDIte]
      have hsym : (eC.symm ⟨(eC ⟨i.val - 2 * r, by omega⟩).val, hnmem⟩).val = i.val - 2 * r := by
        have h := eC.symm_apply_apply ⟨i.val - 2 * r, by omega⟩
        exact congrArg Fin.val h
      rw [hsym]
      cases Nat.testBit u.val (i.val - 2 * r) <;> cases sign (eC ⟨i.val - 2 * r, by omega⟩).val <;> rfl
  have hpack_unpack : ∀ x : Fin (2 ^ k), pack (unpack x).1 (unpack x).2 = x := by
    intro x
    apply Fin.ext
    apply nat_eq_of_testBit_lt (pack _ _).isLt x.isLt
    intro j
    simp only [pack, unpack, testBit_toNum]
    by_cases hj : j ∈ B
    · simp only [hj, ↓reduceDIte]
      have h := eB.apply_symm_apply ⟨j, hj⟩
      exact congrArg (fun a : { j : Fin k // j ∈ B } => Nat.testBit x.val a.val.val) h
    · simp only [hj, ↓reduceDIte]
      have h := eC.apply_symm_apply ⟨j, hj⟩
      have h1 : (eC (eC.symm ⟨j, hj⟩)).val = j := congrArg Subtype.val h
      rw [h1]
      cases Nat.testBit x.val j.val <;> cases sign j <;> rfl
  have hunpack_pack : ∀ y u, unpack (pack y u) = (y, u) := by
    intro y u
    apply Prod.ext
    · apply Fin.ext
      apply nat_eq_of_testBit_lt (unpack _).1.isLt y.isLt
      intro t
      simp only [unpack, pack, testBit_toNum]
      have hmem : (eB t).val ∈ B := (eB t).property
      simp only [hmem, ↓reduceDIte]
      have h := eB.symm_apply_apply t
      exact congrArg (fun a : Fin r => Nat.testBit y.val a.val) h
    · apply Fin.ext
      apply nat_eq_of_testBit_lt (unpack _).2.isLt u.isLt
      intro t
      simp only [unpack, pack, testBit_toNum]
      have hnmem : (eC t).val ∉ B := (eC t).property
      simp only [hnmem, ↓reduceDIte]
      have h := eC.symm_apply_apply t
      have h1 : (eC.symm ⟨(eC t).val, hnmem⟩).val = t.val := congrArg Fin.val h
      rw [h1]
      cases Nat.testBit u.val t.val <;> cases sign (eC t).val <;> rfl
  have hM_row : ∀ i : Fin (k + r), ∃ x : Fin (2 ^ k), M i x = true := by
    intro i
    by_cases hi : i.val < 2 * r
    · let y : Fin (2 ^ r) := ⟨toNum (fun t : Fin r => decide (i.val % 2 = 1)), toNum_lt _⟩
      let u : Fin (2 ^ (k - r)) := ⟨0, Nat.two_pow_pos _⟩
      refine ⟨pack y u, ?_⟩
      rw [hpack_M y u i]
      simp only [hi, ↓reduceIte, y]
      have hbit := testBit_toNum (fun t : Fin r => decide (i.val % 2 = 1)) ⟨i.val / 2, by omega⟩
      simp only at hbit
      rw [hbit, beq_self_eq_true]
    · let y : Fin (2 ^ r) := ⟨0, Nat.two_pow_pos _⟩
      let u : Fin (2 ^ (k - r)) := ⟨2 ^ (i.val - 2 * r), Nat.pow_lt_pow_right (by omega) (by omega)⟩
      refine ⟨pack y u, ?_⟩
      rw [hpack_M y u i]
      simp only [hi, ↓reduceIte, u, Nat.testBit_two_pow_self]
  have hM_col : ∀ x : Fin (2 ^ k), ∃ i : Fin (k + r), M i x = true := by
    intro x
    set y := (unpack x).1
    let b := Nat.testBit y.val 0
    let i : Fin (k + r) := ⟨if b then 1 else 0, by cases b <;> simp <;> omega⟩
    refine ⟨i, ?_⟩
    rw [← hpack_unpack x, hpack_M]
    have hi : i.val < 2 * r := by simp only [i]; cases b <;> simp <;> omega
    have hdiv : i.val / 2 = 0 := by simp only [i]; cases b <;> simp <;> omega
    have hmod : decide (i.val % 2 = 1) = b := decide_bool_mod b
    simp only [hi, ↓reduceIte, hdiv, hmod, y, b, beq_self_eq_true]
  have hM_col_inj : ∀ x1 x2 : Fin (2 ^ k), (∀ i : Fin (k + r), M i x1 = M i x2) → x1 = x2 := by
    intro x1 x2 h
    rw [← hpack_unpack x1, ← hpack_unpack x2]
    have h1 : (unpack x1).1 = (unpack x2).1 := by
      apply Fin.ext
      apply nat_eq_of_testBit_lt (unpack x1).1.isLt (unpack x2).1.isLt
      intro t
      let i : Fin (k + r) := ⟨2 * t.val + 1, by omega⟩
      have hi := h i
      rw [← hpack_unpack x1, ← hpack_unpack x2, hpack_M, hpack_M] at hi
      have hlt : i.val < 2 * r := by simp only [i]; omega
      have hdiv : i.val / 2 = t.val := by simp only [i]; omega
      have hmod : decide (i.val % 2 = 1) = true := by
        rw [decide_eq_true_eq]
        simp only [i]
        omega
      simp only [hlt, ↓reduceIte, hdiv, hmod, beq_true] at hi
      exact hi
    have h2 : (unpack x1).2 = (unpack x2).2 := by
      apply Fin.ext
      apply nat_eq_of_testBit_lt (unpack x1).2.isLt (unpack x2).2.isLt
      intro t
      let i : Fin (k + r) := ⟨2 * r + t.val, by omega⟩
      have hi := h i
      rw [← hpack_unpack x1, ← hpack_unpack x2, hpack_M, hpack_M] at hi
      have hge : ¬ i.val < 2 * r := by simp only [i]; omega
      have hsub : i.val - 2 * r = t.val := by simp only [i]; omega
      simp only [hge, ↓reduceIte, hsub] at hi
      exact hi
    rw [h1, h2]
  have hpow_mul : 2 ^ r * 2 ^ (k - r) = 2 ^ k := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hrk]
  constructor
  · rintro ⟨C, hA, h1, h2, hsz⟩
    have hCM : ComputesMatrix M C := ⟨hA, (hM_equiv C).1 ⟨h1, h2⟩⟩
    obtain ⟨C', ⟨hA', hM'⟩, hsz'⟩ := transpose_computes M hM_row hM_col hCM
    choose z hz using hM'
    dsimp only at hz
    have hz_lt : ∀ x : Fin (2 ^ k), z x < k + r + C'.gates.length := by
      intro x
      obtain ⟨i, hi⟩ := hM_col x
      by_contra hge
      have hfalse : (C'.wires (oneHot (k + r) i)).getD (z x) false = false := by
        rw [wires_eq_evalGates]
        apply evalGates_getD_of_ge
        rw [oneHot_length]
        omega
      rw [hz x i, hi] at hfalse
      exact Bool.noConfusion hfalse
    have hz_inj : Function.Injective z := by
      intro x1 x2 heq
      apply hM_col_inj x1 x2
      intro i
      rw [← hz x1 i, ← hz x2 i, heq]
    let isOpt (v : ℕ) : Prop :=
      ∃ t : Fin (k - r), (C'.wires (oneHot (k + r) ⟨2 * r + t.val, by omega⟩)).getD v false = true
    set optGates : Finset ℕ := (Finset.range C'.gates.length).filter (fun t => isOpt (k + r + t))
    set pureGates : Finset ℕ := (Finset.range C'.gates.length).filter (fun t => ¬ isOpt (k + r + t))
    have hpart : pureGates.card + optGates.card = C'.gates.length := by
      have hdisj : Disjoint pureGates optGates := by
        rw [Finset.disjoint_filter]
        intro t _ h1 h2
        exact h1 h2
      have hunion : pureGates ∪ optGates = Finset.range C'.gates.length := by
        ext t
        simp only [pureGates, optGates, Finset.mem_union, Finset.mem_filter]
        tauto
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_range]
    set Mixed : Finset (Fin (2 ^ r) × Fin (2 ^ (k - r))) :=
      Finset.univ.filter (fun p => p.2.val ≠ 0)
    have hMixed_card : Mixed.card + 2 ^ r = 2 ^ k := by
      set Pure : Finset (Fin (2 ^ r) × Fin (2 ^ (k - r))) :=
        Finset.univ.filter (fun p => p.2.val = 0)
      have hdisj : Disjoint Mixed Pure := by
        rw [Finset.disjoint_filter]
        intro p _ h1 h2
        exact h1 h2
      have hunion : Mixed ∪ Pure = Finset.univ := by
        ext p
        simp only [Mixed, Pure, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        exact ne_or_eq _ _
      have hPure_card : Pure.card = 2 ^ r := by
        have hbij : Pure = Finset.univ.image (fun y : Fin (2 ^ r) => (y, (⟨0, Nat.two_pow_pos _⟩ : Fin (2 ^ (k - r))))) := by
          ext ⟨y, u⟩
          simp only [Pure, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq]
          constructor
          · intro hu
            exact ⟨y, rfl, Fin.ext hu.symm⟩
          · rintro ⟨y', rfl, rfl⟩
            rfl
        rw [hbij, Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1),
            Finset.card_univ, Fintype.card_fin]
      have hall := Finset.card_union_of_disjoint hdisj
      rw [hunion, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
          hpow_mul, hPure_card] at hall
      exact hall.symm
    have hMixed_map : ∀ p ∈ Mixed, z (pack p.1 p.2) ≥ k + r ∧ z (pack p.1 p.2) - (k + r) ∈ optGates := by
      intro ⟨y, u⟩ hp
      have hu_ne : u.val ≠ 0 := (Finset.mem_filter.1 hp).2
      obtain ⟨t, ht⟩ := nat_pos_has_testBit u.isLt hu_ne
      let iOpt : Fin (k + r) := ⟨2 * r + t.val, by omega⟩
      have hopt_true : (C'.wires (oneHot (k + r) iOpt)).getD (z (pack y u)) false = true := by
        rw [hz (pack y u) iOpt, hpack_M]
        have hge : ¬ iOpt.val < 2 * r := by simp only [iOpt]; omega
        have hsub : iOpt.val - 2 * r = t.val := by simp only [iOpt]; omega
        simp only [hge, ↓reduceIte, hsub, ht]
      let b0 := Nat.testBit y.val 0
      let iPair : Fin (k + r) := ⟨if b0 then 1 else 0, by cases b0 <;> simp <;> omega⟩
      have hpair_true : (C'.wires (oneHot (k + r) iPair)).getD (z (pack y u)) false = true := by
        rw [hz (pack y u) iPair, hpack_M]
        have hlt : iPair.val < 2 * r := by simp only [iPair]; cases b0 <;> simp <;> omega
        have hdiv : iPair.val / 2 = 0 := by simp only [iPair]; cases b0 <;> simp <;> omega
        have hmod : decide (iPair.val % 2 = 1) = b0 := decide_bool_mod b0
        simp only [hlt, ↓reduceIte, hdiv, hmod, b0, beq_self_eq_true]
      have hge_kr : k + r ≤ z (pack y u) := by
        by_contra hlt
        have hlt' : z (pack y u) < k + r := by omega
        rw [wires_getD_input C' (k + r) iOpt hlt', decide_eq_true_eq] at hopt_true
        rw [wires_getD_input C' (k + r) iPair hlt', decide_eq_true_eq] at hpair_true
        have heq : iOpt.val = iPair.val := by omega
        have hiPair_le : iPair.val ≤ 1 := by simp only [iPair]; split_ifs <;> omega
        have hiOpt_ge : 2 * r ≤ iOpt.val := by simp only [iOpt]; omega
        omega
      have hlt_all := hz_lt (pack y u)
      dsimp only
      refine ⟨hge_kr, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), ?_⟩⟩
      refine ⟨t, ?_⟩
      have heq : k + r + (z (pack y u) - (k + r)) = z (pack y u) := by omega
      rw [heq]
      exact hopt_true
    have hopt_ge : Mixed.card ≤ optGates.card := by
      let f : Fin (2 ^ r) × Fin (2 ^ (k - r)) → ℕ := fun p => z (pack p.1 p.2) - (k + r)
      have hsub : Mixed.image f ⊆ optGates := by
        intro w hw
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hw
        exact (hMixed_map p hp).2
      have hinj : Set.InjOn f (Mixed : Set _) := by
        intro p1 hp1 p2 hp2 heq
        have hge1 := (hMixed_map p1 hp1).1
        have hge2 := (hMixed_map p2 hp2).1
        have hz_eq : z (pack p1.1 p1.2) = z (pack p2.1 p2.2) := by
          simp only [f] at heq
          omega
        have hpack_eq := hz_inj hz_eq
        have hu := congrArg unpack hpack_eq
        rw [hunpack_pack, hunpack_pack] at hu
        exact hu
      calc Mixed.card
          = (Mixed.image f).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ optGates.card := Finset.card_le_card hsub
    set d := pureGates.card
    let pos : ℕ → ℕ := fun t => (pureGates.filter (· < t)).card
    obtain ⟨hpos_lt, hpos_mono, hpos_surj⟩ := finset_pos_bijection pureGates
    have hinv_ex : ∀ m : Fin d, ∃ t ∈ pureGates, pos t = m.val := fun m => hpos_surj m.val m.isLt
    choose inv hinv_mem hinv_pos using hinv_ex
    have hinv_pos_eq : ∀ (t : ℕ) (ht : t ∈ pureGates), inv ⟨pos t, hpos_lt t ht⟩ = t := by
      intro t ht
      have hm := hinv_mem ⟨pos t, hpos_lt t ht⟩
      have hp := hinv_pos ⟨pos t, hpos_lt t ht⟩
      rcases lt_trichotomy (inv ⟨pos t, hpos_lt t ht⟩) t with h1 | h2 | h3
      · exact absurd hp (Nat.ne_of_lt (hpos_mono _ hm _ ht h1))
      · exact h2
      · exact absurd hp.symm (Nat.ne_of_lt (hpos_mono _ ht _ hm h3))
    let comp (u : ℕ) : ℕ := if u < 2 * r then u else 2 * r + pos (u - (k + r))
    have hinv_lt : ∀ m : Fin d, inv m < C'.gates.length := fun m =>
      Finset.mem_range.1 (Finset.mem_filter.1 (hinv_mem m)).1
    let Dgates : List Gate :=
      List.ofFn (fun m : Fin d =>
        ⟨GateOp.or, (((C'.gates[inv m]'(hinv_lt m)).inputs.filter (fun u => u < k + r + inv m)).map comp)⟩)
    let D : Circuit := ⟨Dgates, 0⟩
    have hlenD : D.gates.length = d := by simp [D, Dgates]
    have hAD : Allowed D := by
      intro g hg
      simp only [D, Dgates, List.mem_ofFn] at hg
      obtain ⟨m, rfl⟩ := hg
      refine ⟨rfl, ?_⟩
      rw [List.length_map]
      exact le_trans (List.length_filter_le _ _) (hA' _ (List.getElem_mem (hinv_lt m))).2
    have hnotOpt_class : ∀ v < k + r + C'.gates.length, ¬ isOpt v →
        v < 2 * r ∨ (k + r ≤ v ∧ v - (k + r) ∈ pureGates) := by
      intro v hv hno
      by_cases hv1 : v < 2 * r
      · exact Or.inl hv1
      · by_cases hv2 : v < k + r
        · exfalso
          apply hno
          refine ⟨⟨v - 2 * r, by omega⟩, ?_⟩
          rw [wires_getD_input C' (k + r) ⟨2 * r + (v - 2 * r), by omega⟩ hv2, decide_eq_true_eq]
          dsimp only
          omega
        · right
          refine ⟨by omega, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), ?_⟩⟩
          have heq : k + r + (v - (k + r)) = v := by omega
          rw [heq]
          exact hno
    have hsimD : ∀ v < k + r + C'.gates.length, ¬ isOpt v → ∀ i : Fin (2 * r),
        (D.wires (oneHot (2 * r) i)).getD (comp v) false =
          (C'.wires (oneHot (k + r) ⟨i.val, by omega⟩)).getD v false := by
      intro v
      induction v using Nat.strong_induction_on with
      | ind v ih =>
        intro hv hno i
        rcases hnotOpt_class v hv hno with hv_in | ⟨hv_ge, hv_pure⟩
        · have hcomp : comp v = v := by simp only [comp, hv_in, ↓reduceIte]
          rw [hcomp, wires_getD_input D (2 * r) i hv_in,
              wires_getD_input C' (k + r) ⟨i.val, by omega⟩ (by omega)]
        · set t := v - (k + r)
          have ht_eq : k + r + t = v := by omega
          have ht_lt : t < C'.gates.length := by omega
          set m : Fin d := ⟨pos t, hpos_lt t hv_pure⟩
          have hcomp : comp v = 2 * r + m.val := by
            simp only [comp]
            have : ¬ v < 2 * r := by omega
            simp only [this, ↓reduceIte, m, t]
          rw [hcomp]
          apply Bool.eq_iff_iff.2
          have hm_lt : m.val < D.gates.length := by rw [hlenD]; exact m.isLt
          have hL := wires_getD_gate_or hAD (oneHot (2 * r) i) hm_lt
          rw [oneHot_length] at hL
          have hR := wires_getD_gate_or hA' (oneHot (k + r) ⟨i.val, by omega⟩) ht_lt
          rw [oneHot_length, ht_eq] at hR
          rw [hL, hR]
          have hinv_m : inv m = t := hinv_pos_eq t hv_pure
          have hget : D.gates[m.val]'hm_lt =
              ⟨GateOp.or, (((C'.gates[t]'ht_lt).inputs.filter (fun u => u < k + r + t)).map comp)⟩ := by
            simp only [D, Dgates, List.getElem_ofFn]
            congr 2
            simp only [hinv_m]
          rw [hget]
          simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
          have hu_notOpt : ∀ u ∈ (C'.gates[t]'ht_lt).inputs, u < v → ¬ isOpt u := by
            intro u hu hult ⟨topt, htopt⟩
            apply hno
            refine ⟨topt, ?_⟩
            have hiOpt : 2 * r + topt.val < k + r := by
              have hsum : 2 * r + (k - r) = k + r := by
                rw [Nat.two_mul, Nat.add_assoc, Nat.add_sub_of_le hrk, Nat.add_comm]
              exact hsum ▸ Nat.add_lt_add_left topt.isLt (2 * r)
            have hG := wires_getD_gate_or hA' (oneHot (k + r) ⟨2 * r + topt.val, hiOpt⟩) ht_lt
            rw [oneHot_length, ht_eq] at hG
            exact hG.2 ⟨u, hu, hult, htopt⟩
          constructor
          · rintro ⟨w, ⟨u, ⟨hu, hult⟩, rfl⟩, _, hwt⟩
            have huno := hu_notOpt u hu (by omega)
            refine ⟨u, hu, by omega, ?_⟩
            rwa [← ih u (by omega) (by omega) huno i]
          · rintro ⟨u, hu, hult, hut⟩
            have huno := hu_notOpt u hu hult
            have hcomp_lt : comp u < 2 * r + m.val := by
              rcases hnotOpt_class u (by omega) huno with hu_in | ⟨hu_ge, hu_pure⟩
              · simp only [comp, hu_in, ↓reduceIte]
                omega
              · have hnot : ¬ u < 2 * r := by omega
                simp only [comp, hnot, ↓reduceIte, m]
                have hlt_t : u - (k + r) < t := by omega
                have hpm : pos (u - (k + r)) < pos t := hpos_mono _ hu_pure _ hv_pure hlt_t
                omega
            refine ⟨comp u, ⟨u, ⟨hu, by omega⟩, rfl⟩, hcomp_lt, ?_⟩
            rw [ih u (by omega) (by omega) huno i]
            exact hut
    refine ⟨d, ⟨D, hAD, le_of_eq hlenD, ?_⟩, ?_⟩
    · intro y
      let u0 : Fin (2 ^ (k - r)) := ⟨0, Nat.two_pow_pos _⟩
      set x := pack y u0
      have hno : ¬ isOpt (z x) := by
        rintro ⟨topt, htopt⟩
        rw [hz x ⟨2 * r + topt.val, by omega⟩, hpack_M] at htopt
        have hge : ¬ 2 * r + topt.val < 2 * r := by omega
        simp only [hge, ↓reduceIte, u0, Nat.zero_testBit] at htopt
        exact Bool.noConfusion htopt
      refine ⟨comp (z x), fun i => ?_⟩
      rw [hsimD (z x) (hz_lt x) hno i, hz x ⟨i.val, by omega⟩, hpack_M]
      simp [i.isLt]
    · omega
  · rintro ⟨d, ⟨D, hAD, hlenD, hD⟩, hbound⟩
    choose z0 hz0 using hD
    have hz0_lt : ∀ y : Fin (2 ^ r), z0 y < 2 * r + D.gates.length := by
      intro y
      let b0 := Nat.testBit y.val 0
      let i0 : Fin (2 * r) := ⟨if b0 then 1 else 0, by cases b0 <;> simp <;> omega⟩
      have htrue : (D.wires (oneHot (2 * r) i0)).getD (z0 y) false = true := by
        rw [hz0 y i0]
        have hdiv : i0.val / 2 = 0 := by simp only [i0]; cases b0 <;> simp <;> omega
        have hmod : decide (i0.val % 2 = 1) = b0 := decide_bool_mod b0
        simp only [hdiv, hmod, b0, beq_self_eq_true]
      by_contra hge
      have hfalse : (D.wires (oneHot (2 * r) i0)).getD (z0 y) false = false := by
        rw [wires_eq_evalGates]
        apply evalGates_getD_of_ge
        rw [oneHot_length]
        omega
      rw [htrue] at hfalse
      exact Bool.noConfusion hfalse
    have hkr_eq : 2 * r + (k - r) = k + r := by omega
    obtain ⟨C0', hA0', hlen0', hsim0'⟩ := embed_extra_inputs (a := 2 * r) (b := k - r) D hAD
    let emb : ℕ → ℕ := fun v => if v < 2 * r then v else v + (k - r)
    have hsim0 : ∀ y : Fin (2 ^ r), ∀ i : Fin (k + r),
        (C0'.wires (oneHot (k + r) i)).getD (emb (z0 y)) false =
          if i.val < 2 * r then (Nat.testBit y.val (i.val / 2) == decide (i.val % 2 = 1)) else false := by
      intro y i
      rw [oneHot_finCongr hkr_eq.symm i, hsim0' (z0 y) (hz0_lt y) (finCongr hkr_eq.symm i)]
      simp only [finCongr_apply, Fin.val_cast]
      by_cases hi : i.val < 2 * r
      · simp only [hi, ↓reduceDIte, ↓reduceIte]
        exact hz0 y ⟨i.val, hi⟩
      · simp only [hi, ↓reduceDIte, ↓reduceIte]
    have hw0_lt : ∀ y : Fin (2 ^ r), emb (z0 y) < k + r + C0'.gates.length := by
      intro y
      have := hz0_lt y
      simp only [emb]
      split_ifs <;> omega
    obtain ⟨C', hA', hlen', hC'⟩ :=
      adjoin_optional_bits hrk C0' hA0' (fun y => emb (z0 y)) hw0_lt hsim0 (k - r) (le_refl _)
    have hCM' : ComputesMatrix (fun x i => M i x) C' := by
      refine ⟨hA', fun x => ?_⟩
      obtain ⟨w, _, hw⟩ := hC' (unpack x).1 (unpack x).2
      refine ⟨w, fun i => ?_⟩
      dsimp only
      rw [hw i]
      conv_rhs => rw [← hpack_unpack x]
      rw [hpack_M]
      by_cases hi : i.val < 2 * r
      · simp only [hi, ↓reduceIte]
      · have hi2 : i.val < 2 * r + (k - r) := by omega
        simp only [hi, hi2, ↓reduceIte]
    obtain ⟨C, hCM, hszC⟩ := transpose_computes (fun x i => M i x) hM_col hM_row hCM'
    have h12 := (hM_equiv C).2 hCM.2
    have hpow_ge : 2 ^ r ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hrk
    have hszC'_eq : C'.gates.length + 2 ^ r = D.gates.length + 2 ^ k := by
      have h1 : 1 ≤ 2 ^ (k - r) := Nat.two_pow_pos _
      rw [hlen', hlen0', Nat.mul_sub_left_distrib, mul_one, hpow_mul]
      omega
    refine ⟨C, hCM.1, h12.1, h12.2, ?_⟩
    omega

end PEqualNP.Outside.L_meta_25785

theorem PEqualNP.Outside.L_meta_25785 : ∀ (k : ℕ), 2 ≤ k → ∀ (B : Finset (Fin k)) (sign : Fin k → Bool) (s : ℕ),
  let r := B.card
  let allowed := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ g.inputs.length ≤ 2
  let wire := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (j : Fin k) (b : Bool) =>
    ∃ w : ℕ, ∀ x : Fin (2 ^ k),
      (C.wires (List.ofFn (fun h : Fin (2 ^ k) => decide (h = x)))).getD w false =
        (Nat.testBit x.val j.val == b)
  let enc := ∃ C : PEqualNP.CircuitLowerBounds.Circuit, allowed C ∧
    (∀ j : Fin k, wire C j (sign j)) ∧ (∀ j ∈ B, wire C j (!(sign j))) ∧
    C.size + (k - r) ≤ s
  let dec := fun (d : ℕ) =>
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit, allowed D ∧ D.size ≤ d ∧
      ∀ y : Fin (2 ^ r), ∃ z : ℕ, ∀ i : Fin (2 * r),
        (D.wires (List.ofFn (fun h : Fin (2 * r) => decide (h = i)))).getD z false =
          (Nat.testBit y.val (i.val / 2) == decide (i.val % 2 = 1))
  enc ↔ (if r = 0 then 2 * (2 ^ k - k - 1) + k ≤ s
         else ∃ d : ℕ, dec d ∧ d + 2 * 2 ^ k ≤ s + 2 ^ r + 2 * r) := by
  intro k hk B sign s
  dsimp only
  by_cases hr : B.card = 0
  · simp only [hr, ↓reduceIte, Nat.sub_zero]
    have hB : B = ∅ := Finset.card_eq_zero.1 hr
    have hiff := PEqualNP.Outside.L_meta_25785.solve_r_zero k hk sign s
    rw [← hiff]
    constructor
    · rintro ⟨C, hA, h1, _, hsz⟩
      exact ⟨C, hA, h1, hsz⟩
    · rintro ⟨C, hA, h1, hsz⟩
      exact ⟨C, hA, h1, fun j hj => by rw [hB] at hj; exact absurd hj (Finset.notMem_empty j), hsz⟩
  · simp only [hr, ↓reduceIte]
    exact PEqualNP.Outside.L_meta_25785.solve_r_pos k hk B sign s (Nat.pos_of_ne_zero hr)
