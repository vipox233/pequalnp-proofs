import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

namespace PEqualNP.Outside.L_meta_25463_aux

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl step x := rfl

theorem step_length (w : List Bool) (g : Gate) :
    (step w g).length = w.length + 1 := by
  simp [step]

theorem foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step_length, List.length_cons]
    omega

theorem getD_append_left {l1 l2 : List Bool} {i : ℕ} (hi : i < l1.length) :
    (l1 ++ l2).getD i false = l1.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem step_getD_lt (w : List Bool) (g : Gate) {i : ℕ} (hi : i < w.length) :
    (step w g).getD i false = w.getD i false :=
  getD_append_left hi

theorem step_getD_last (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp [step, List.getD_eq_getElem?_getD]

theorem foldl_getD_lt (gs : List Gate) (w : List Bool) {i : ℕ} (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (step w g).length := by rw [step_length]; omega
    rw [ih (step w g) hlt, step_getD_lt w g hi]

def GateOK (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem any_congr_mem {α : Type} {l : List α} {p q : α → Bool} (h : ∀ a ∈ l, p a = q a) :
    l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons]
    rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]

-- OR chain
def orChainAux (curBase acc : ℕ) : List ℕ → List Gate × ℕ
  | [] => ([], acc)
  | w :: rest =>
    let res := orChainAux (curBase + 1) curBase rest
    (⟨.or, [acc, w]⟩ :: res.1, res.2)

theorem orChainAux_len (curBase acc : ℕ) (rest : List ℕ) :
    (orChainAux curBase acc rest).1.length = rest.length := by
  induction rest generalizing curBase acc with
  | nil => rfl
  | cons w rest ih => simp [orChainAux, ih]

theorem orChainAux_out_lt (curBase acc : ℕ) (rest : List ℕ) (hacc : acc < curBase) :
    (orChainAux curBase acc rest).2 < curBase + rest.length := by
  induction rest generalizing curBase acc with
  | nil => simpa [orChainAux] using hacc
  | cons w rest ih =>
    simp only [orChainAux, List.length_cons]
    have h := ih (curBase + 1) curBase (by omega)
    omega

theorem orChainAux_ok (curBase acc : ℕ) (rest : List ℕ) :
    ∀ g ∈ (orChainAux curBase acc rest).1, GateOK g := by
  induction rest generalizing curBase acc with
  | nil => simp [orChainAux]
  | cons w rest ih =>
    intro g hg
    simp only [orChainAux, List.mem_cons] at hg
    rcases hg with rfl | hmem
    · exact ⟨by simp, by simp⟩
    · exact ih (curBase + 1) curBase g hmem

theorem orChainAux_eval (curBase acc : ℕ) (rest : List ℕ) (vec : List Bool)
    (hlen : vec.length = curBase) (hacc : acc < curBase) (hrest : ∀ w ∈ rest, w < curBase) :
    ((orChainAux curBase acc rest).1.foldl step vec).getD (orChainAux curBase acc rest).2 false =
      (vec.getD acc false || rest.any (fun w => vec.getD w false)) := by
  induction rest generalizing curBase acc vec with
  | nil => simp [orChainAux]
  | cons w rest ih =>
    simp only [orChainAux, List.foldl_cons, List.any_cons]
    set g : Gate := ⟨.or, [acc, w]⟩
    set vec' := step vec g
    have hlen' : vec'.length = curBase + 1 := by simp [vec', step_length, hlen]
    have hrest' : ∀ u ∈ rest, u < curBase + 1 := fun u hu => by
      have := hrest u (by simp [hu]); omega
    rw [ih (curBase + 1) curBase vec' hlen' (by omega) hrest']
    have hnew : vec'.getD curBase false = (vec.getD acc false || vec.getD w false) := by
      have h0 := step_getD_last vec g
      rw [hlen] at h0
      simpa [vec', g, GateOp.eval] using h0
    have hany : rest.any (fun u => vec'.getD u false) = rest.any (fun u => vec.getD u false) := by
      apply any_congr_mem
      intro u hu
      have hult : u < vec.length := by rw [hlen]; exact hrest u (by simp [hu])
      exact step_getD_lt vec g hult
    rw [hnew, hany, Bool.or_assoc]

-- Threshold-3 circuit on >= 3 wires in 5*N - 9 gates
def t3Step (curBase oPrev t2Prev t3Prev : ℕ) : List ℕ → List Gate × ℕ
  | [] => ([], t3Prev)
  | w :: rest =>
    let res := t3Step (curBase + 5) (curBase + 4) (curBase + 3) (curBase + 1) rest
    (⟨.and, [t2Prev, w]⟩ :: ⟨.or, [t3Prev, curBase]⟩ :: ⟨.and, [oPrev, w]⟩ ::
     ⟨.or, [t2Prev, curBase + 2]⟩ :: ⟨.or, [oPrev, w]⟩ :: res.1, res.2)

def atLeastThree (base : ℕ) : List ℕ → List Gate × ℕ
  | w0 :: w1 :: w2 :: rest =>
    let res := t3Step (base + 6) (base + 2) (base + 4) (base + 5) rest
    (⟨.or, [w0, w1]⟩ :: ⟨.and, [w0, w1]⟩ :: ⟨.or, [base, w2]⟩ ::
     ⟨.and, [base, w2]⟩ :: ⟨.or, [base + 1, base + 3]⟩ :: ⟨.and, [base + 1, w2]⟩ :: res.1, res.2)
  | _ => ([], 0)

theorem t3Step_len (curBase o t2 t3 : ℕ) (ws : List ℕ) :
    (t3Step curBase o t2 t3 ws).1.length = 5 * ws.length := by
  induction ws generalizing curBase o t2 t3 with
  | nil => simp [t3Step]
  | cons w rest ih =>
    simp only [t3Step, List.length_cons, ih]
    omega

theorem atLeastThree_len (base : ℕ) (ws : List ℕ) (h3 : 3 ≤ ws.length) :
    (atLeastThree base ws).1.length = 5 * ws.length - 9 := by
  match ws with
  | [] => simp at h3
  | [_] => simp at h3
  | [_, _] => simp at h3
  | _ :: _ :: _ :: rest =>
    simp only [atLeastThree, List.length_cons, t3Step_len]
    omega

theorem t3Step_out_lt (curBase o t2 t3 : ℕ) (ws : List ℕ) (ht3 : t3 < curBase) :
    (t3Step curBase o t2 t3 ws).2 < curBase + (t3Step curBase o t2 t3 ws).1.length := by
  induction ws generalizing curBase o t2 t3 with
  | nil => simpa [t3Step] using ht3
  | cons w rest ih =>
    simp only [t3Step, List.length_cons]
    have h := ih (curBase + 5) (curBase + 4) (curBase + 3) (curBase + 1) (by omega)
    omega

theorem atLeastThree_out_lt (base : ℕ) (ws : List ℕ) (h3 : 3 ≤ ws.length) :
    (atLeastThree base ws).2 < base + (atLeastThree base ws).1.length := by
  match ws with
  | [] => simp at h3
  | [_] => simp at h3
  | [_, _] => simp at h3
  | _ :: _ :: _ :: rest =>
    simp only [atLeastThree, List.length_cons]
    have h := t3Step_out_lt (base + 6) (base + 2) (base + 4) (base + 5) rest (by omega)
    omega

theorem t3Step_ok (curBase o t2 t3 : ℕ) (ws : List ℕ) :
    ∀ g ∈ (t3Step curBase o t2 t3 ws).1, GateOK g := by
  induction ws generalizing curBase o t2 t3 with
  | nil => simp [t3Step]
  | cons w rest ih =>
    intro g hg
    simp only [t3Step, List.mem_cons] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | hmem
    · exact ⟨by simp, by simp⟩
    · exact ⟨by simp, by simp⟩
    · exact ⟨by simp, by simp⟩
    · exact ⟨by simp, by simp⟩
    · exact ⟨by simp, by simp⟩
    · exact ih (curBase + 5) (curBase + 4) (curBase + 3) (curBase + 1) g hmem

theorem atLeastThree_ok (base : ℕ) (ws : List ℕ) :
    ∀ g ∈ (atLeastThree base ws).1, GateOK g := by
  match ws with
  | [] => simp [atLeastThree]
  | [_] => simp [atLeastThree]
  | [_, _] => simp [atLeastThree]
  | _ :: _ :: _ :: rest =>
    intro g hg
    simp only [atLeastThree, List.mem_cons] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | hmem
    · exact ⟨by simp, by simp⟩
    · exact ⟨by simp, by simp⟩
    · exact ⟨by simp, by simp⟩
    · exact ⟨by simp, by simp⟩
    · exact ⟨by simp, by simp⟩
    · exact ⟨by simp, by simp⟩
    · exact t3Step_ok (base + 6) (base + 2) (base + 4) (base + 5) rest g hmem

def t3Spec (o t2 t3 : Bool) : List Bool → Bool
  | [] => t3
  | b :: bs => t3Spec (o || b) (t2 || (o && b)) (t3 || (t2 && b)) bs

theorem t3Spec_count (c : ℕ) (bs : List Bool) :
    t3Spec (decide (1 ≤ c)) (decide (2 ≤ c)) (decide (3 ≤ c)) bs =
      decide (3 ≤ c + bs.count true) := by
  induction bs generalizing c with
  | nil => simp [t3Spec]
  | cons b bs ih =>
    simp only [t3Spec, List.count_cons]
    cases b with
    | false =>
      have h1 : (decide (1 ≤ c) || false) = decide (1 ≤ c) := by simp
      have h2 : (decide (2 ≤ c) || (decide (1 ≤ c) && false)) = decide (2 ≤ c) := by simp
      have h3 : (decide (3 ≤ c) || (decide (2 ≤ c) && false)) = decide (3 ≤ c) := by simp
      rw [h1, h2, h3, ih c]
      simp
    | true =>
      have h1 : (decide (1 ≤ c) || true) = decide (1 ≤ c + 1) := by simp
      have h2 : (decide (2 ≤ c) || (decide (1 ≤ c) && true)) = decide (2 ≤ c + 1) := by
        by_cases hc1 : 1 ≤ c <;> by_cases hc2 : 2 ≤ c <;> simp [hc1, hc2] <;> omega
      have h3 : (decide (3 ≤ c) || (decide (2 ≤ c) && true)) = decide (3 ≤ c + 1) := by
        by_cases hc2 : 2 ≤ c <;> by_cases hc3 : 3 ≤ c <;> simp [hc2, hc3] <;> omega
      rw [h1, h2, h3, ih (c + 1)]
      simp only [beq_self_eq_true, ↓reduceIte]
      apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; omega

theorem t3Step_eval (curBase oPrev t2Prev t3Prev : ℕ) (ws : List ℕ) (vec : List Bool)
    (hlen : vec.length = curBase) (ho : oPrev < curBase) (ht2 : t2Prev < curBase)
    (ht3 : t3Prev < curBase) (hws : ∀ w ∈ ws, w < curBase) :
    ((t3Step curBase oPrev t2Prev t3Prev ws).1.foldl step vec).getD
      (t3Step curBase oPrev t2Prev t3Prev ws).2 false =
      t3Spec (vec.getD oPrev false) (vec.getD t2Prev false) (vec.getD t3Prev false)
        (ws.map fun w => vec.getD w false) := by
  induction ws generalizing curBase oPrev t2Prev t3Prev vec with
  | nil => simp [t3Step, t3Spec]
  | cons w rest ih =>
    simp only [t3Step, List.foldl_cons, List.map_cons, t3Spec]
    have hw : w < curBase := hws w (by simp)
    set g0 : Gate := ⟨.and, [t2Prev, w]⟩
    set g1 : Gate := ⟨.or, [t3Prev, curBase]⟩
    set g2 : Gate := ⟨.and, [oPrev, w]⟩
    set g3 : Gate := ⟨.or, [t2Prev, curBase + 2]⟩
    set g4 : Gate := ⟨.or, [oPrev, w]⟩
    set v1 := step vec g0
    set v2 := step v1 g1
    set v3 := step v2 g2
    set v4 := step v3 g3
    set v5 := step v4 g4
    have hl1 : v1.length = curBase + 1 := by simp [v1, step_length, hlen]
    have hl2 : v2.length = curBase + 2 := by simp [v2, step_length, hl1]
    have hl3 : v3.length = curBase + 3 := by simp [v3, step_length, hl2]
    have hl4 : v4.length = curBase + 4 := by simp [v4, step_length, hl3]
    have hl5 : v5.length = curBase + 5 := by simp [v5, step_length, hl4]
    have hrest : ∀ u ∈ rest, u < curBase + 5 := fun u hu => by
      have := hws u (by simp [hu]); omega
    rw [ih (curBase + 5) (curBase + 4) (curBase + 3) (curBase + 1) v5 hl5
      (by omega) (by omega) (by omega) hrest]
    have hpres : ∀ u < curBase, v1.getD u false = vec.getD u false ∧
        v2.getD u false = vec.getD u false ∧ v3.getD u false = vec.getD u false ∧
        v4.getD u false = vec.getD u false ∧ v5.getD u false = vec.getD u false := by
      intro u hu
      have e1 : v1.getD u false = vec.getD u false := step_getD_lt vec g0 (by omega)
      have e2 : v2.getD u false = vec.getD u false := by rw [step_getD_lt v1 g1 (by omega), e1]
      have e3 : v3.getD u false = vec.getD u false := by rw [step_getD_lt v2 g2 (by omega), e2]
      have e4 : v4.getD u false = vec.getD u false := by rw [step_getD_lt v3 g3 (by omega), e3]
      have e5 : v5.getD u false = vec.getD u false := by rw [step_getD_lt v4 g4 (by omega), e4]
      exact ⟨e1, e2, e3, e4, e5⟩
    have hv1_0 : v1.getD curBase false = (vec.getD t2Prev false && vec.getD w false) := by
      have h := step_getD_last vec g0; rw [hlen] at h
      simp only [g0, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
        id_eq, Bool.and_true] at h
      exact h
    have hv2_1 : v2.getD (curBase + 1) false = (vec.getD t3Prev false || (vec.getD t2Prev false && vec.getD w false)) := by
      have h := step_getD_last v1 g1; rw [hl1] at h
      simp only [g1, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        id_eq, Bool.or_false] at h
      rw [(hpres t3Prev ht3).1, hv1_0] at h
      exact h
    have hv5_1 : v5.getD (curBase + 1) false = (vec.getD t3Prev false || (vec.getD t2Prev false && vec.getD w false)) := by
      rw [step_getD_lt v4 g4 (by omega), step_getD_lt v3 g3 (by omega), step_getD_lt v2 g2 (by omega), hv2_1]
    have hv3_2 : v3.getD (curBase + 2) false = (vec.getD oPrev false && vec.getD w false) := by
      have h := step_getD_last v2 g2; rw [hl2] at h
      simp only [g2, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
        id_eq, Bool.and_true] at h
      rw [(hpres oPrev ho).2.1, (hpres w hw).2.1] at h
      exact h
    have hv4_3 : v4.getD (curBase + 3) false = (vec.getD t2Prev false || (vec.getD oPrev false && vec.getD w false)) := by
      have h := step_getD_last v3 g3; rw [hl3] at h
      simp only [g3, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        id_eq, Bool.or_false] at h
      rw [(hpres t2Prev ht2).2.2.1, hv3_2] at h
      exact h
    have hv5_3 : v5.getD (curBase + 3) false = (vec.getD t2Prev false || (vec.getD oPrev false && vec.getD w false)) := by
      rw [step_getD_lt v4 g4 (by omega), hv4_3]
    have hv5_4 : v5.getD (curBase + 4) false = (vec.getD oPrev false || vec.getD w false) := by
      have h := step_getD_last v4 g4; rw [hl4] at h
      simp only [g4, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        id_eq, Bool.or_false] at h
      rw [(hpres oPrev ho).2.2.2.1, (hpres w hw).2.2.2.1] at h
      exact h
    have hmap : rest.map (fun u => v5.getD u false) = rest.map (fun u => vec.getD u false) := by
      apply List.map_congr_left
      intro u hu
      exact (hpres u (hws u (by simp [hu]))).2.2.2.2
    rw [hv5_4, hv5_3, hv5_1, hmap]

theorem atLeastThree_eval (base : ℕ) (ws : List ℕ) (vec : List Bool)
    (hlen : vec.length = base) (h3 : 3 ≤ ws.length) (hws : ∀ w ∈ ws, w < base) :
    ((atLeastThree base ws).1.foldl step vec).getD (atLeastThree base ws).2 false =
      decide (2 < (ws.map fun w => vec.getD w false).count true) := by
  match ws with
  | [] => simp at h3
  | [_] => simp at h3
  | [_, _] => simp at h3
  | w0 :: w1 :: w2 :: rest =>
    simp only [atLeastThree, List.foldl_cons]
    have hw0 : w0 < base := hws w0 (by simp)
    have hw1 : w1 < base := hws w1 (by simp)
    have hw2 : w2 < base := hws w2 (by simp)
    set g0 : Gate := ⟨.or, [w0, w1]⟩
    set g1 : Gate := ⟨.and, [w0, w1]⟩
    set g2 : Gate := ⟨.or, [base, w2]⟩
    set g3 : Gate := ⟨.and, [base, w2]⟩
    set g4 : Gate := ⟨.or, [base + 1, base + 3]⟩
    set g5 : Gate := ⟨.and, [base + 1, w2]⟩
    set v1 := step vec g0
    set v2 := step v1 g1
    set v3 := step v2 g2
    set v4 := step v3 g3
    set v5 := step v4 g4
    set v6 := step v5 g5
    have hl1 : v1.length = base + 1 := by simp [v1, step_length, hlen]
    have hl2 : v2.length = base + 2 := by simp [v2, step_length, hl1]
    have hl3 : v3.length = base + 3 := by simp [v3, step_length, hl2]
    have hl4 : v4.length = base + 4 := by simp [v4, step_length, hl3]
    have hl5 : v5.length = base + 5 := by simp [v5, step_length, hl4]
    have hl6 : v6.length = base + 6 := by simp [v6, step_length, hl5]
    have hrest : ∀ u ∈ rest, u < base + 6 := fun u hu => by
      have := hws u (by simp [hu]); omega
    rw [t3Step_eval (base + 6) (base + 2) (base + 4) (base + 5) rest v6 hl6
      (by omega) (by omega) (by omega) hrest]
    have hpres : ∀ u < base, v1.getD u false = vec.getD u false ∧
        v2.getD u false = vec.getD u false ∧ v3.getD u false = vec.getD u false ∧
        v4.getD u false = vec.getD u false ∧ v5.getD u false = vec.getD u false ∧
        v6.getD u false = vec.getD u false := by
      intro u hu
      have e1 : v1.getD u false = vec.getD u false := step_getD_lt vec g0 (by omega)
      have e2 : v2.getD u false = vec.getD u false := by rw [step_getD_lt v1 g1 (by omega), e1]
      have e3 : v3.getD u false = vec.getD u false := by rw [step_getD_lt v2 g2 (by omega), e2]
      have e4 : v4.getD u false = vec.getD u false := by rw [step_getD_lt v3 g3 (by omega), e3]
      have e5 : v5.getD u false = vec.getD u false := by rw [step_getD_lt v4 g4 (by omega), e4]
      have e6 : v6.getD u false = vec.getD u false := by rw [step_getD_lt v5 g5 (by omega), e5]
      exact ⟨e1, e2, e3, e4, e5, e6⟩
    set b0 := vec.getD w0 false
    set b1 := vec.getD w1 false
    set b2 := vec.getD w2 false
    have hv1_0 : v1.getD base false = (b0 || b1) := by
      have h := step_getD_last vec g0; rw [hlen] at h
      simp only [g0, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        id_eq, Bool.or_false] at h; exact h
    have hv2_0 : v2.getD base false = (b0 || b1) := by rw [step_getD_lt v1 g1 (by omega), hv1_0]
    have hv3_0 : v3.getD base false = (b0 || b1) := by rw [step_getD_lt v2 g2 (by omega), hv2_0]
    have hv2_1 : v2.getD (base + 1) false = (b0 && b1) := by
      have h := step_getD_last v1 g1; rw [hl1] at h
      simp only [g1, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
        id_eq, Bool.and_true] at h
      rw [(hpres w0 hw0).1, (hpres w1 hw1).1] at h; exact h
    have hv3_1 : v3.getD (base + 1) false = (b0 && b1) := by rw [step_getD_lt v2 g2 (by omega), hv2_1]
    have hv4_1 : v4.getD (base + 1) false = (b0 && b1) := by rw [step_getD_lt v3 g3 (by omega), hv3_1]
    have hv5_1 : v5.getD (base + 1) false = (b0 && b1) := by rw [step_getD_lt v4 g4 (by omega), hv4_1]
    have hv3_2 : v3.getD (base + 2) false = ((b0 || b1) || b2) := by
      have h := step_getD_last v2 g2; rw [hl2] at h
      simp only [g2, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        id_eq, Bool.or_false] at h
      rw [hv2_0, (hpres w2 hw2).2.1] at h; exact h
    have hv6_2 : v6.getD (base + 2) false = ((b0 || b1) || b2) := by
      rw [step_getD_lt v5 g5 (by omega), step_getD_lt v4 g4 (by omega), step_getD_lt v3 g3 (by omega), hv3_2]
    have hv4_3 : v4.getD (base + 3) false = ((b0 || b1) && b2) := by
      have h := step_getD_last v3 g3; rw [hl3] at h
      simp only [g3, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
        id_eq, Bool.and_true] at h
      rw [hv3_0, (hpres w2 hw2).2.2.1] at h; exact h
    have hv5_4 : v5.getD (base + 4) false = ((b0 && b1) || ((b0 || b1) && b2)) := by
      have h := step_getD_last v4 g4; rw [hl4] at h
      simp only [g4, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        id_eq, Bool.or_false] at h
      rw [hv4_1, hv4_3] at h; exact h
    have hv6_4 : v6.getD (base + 4) false = ((b0 && b1) || ((b0 || b1) && b2)) := by
      rw [step_getD_lt v5 g5 (by omega), hv5_4]
    have hv6_5 : v6.getD (base + 5) false = ((b0 && b1) && b2) := by
      have h := step_getD_last v5 g5; rw [hl5] at h
      simp only [g5, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
        id_eq, Bool.and_true] at h
      rw [hv5_1, (hpres w2 hw2).2.2.2.2.1] at h; exact h
    have hmap : rest.map (fun u => v6.getD u false) = rest.map (fun u => vec.getD u false) := by
      apply List.map_congr_left
      intro u hu
      exact (hpres u (hws u (by simp [hu]))).2.2.2.2.2
    rw [hv6_2, hv6_4, hv6_5, hmap]
    set c0 : ℕ := (if b0 then 1 else 0) + (if b1 then 1 else 0) + (if b2 then 1 else 0)
    have h1a : ∀ x y z : Bool, ((x || y) || z) = decide (1 ≤ (if x then 1 else 0) + (if y then 1 else 0) + (if z then 1 else 0)) := by decide
    have h2a : ∀ x y z : Bool, ((x && y) || ((x || y) && z)) = decide (2 ≤ (if x then 1 else 0) + (if y then 1 else 0) + (if z then 1 else 0)) := by decide
    have h3a : ∀ x y z : Bool, ((x && y) && z) = decide (3 ≤ (if x then 1 else 0) + (if y then 1 else 0) + (if z then 1 else 0)) := by decide
    rw [h1a b0 b1 b2, h2a b0 b1 b2, h3a b0 b1 b2]
    change t3Spec (decide (1 ≤ c0)) (decide (2 ≤ c0)) (decide (3 ≤ c0)) (rest.map fun w => vec.getD w false) = _
    rw [t3Spec_count c0]
    have hcnt : ((w0 :: w1 :: w2 :: rest).map fun w => vec.getD w false).count true =
        c0 + (rest.map fun w => vec.getD w false).count true := by
      simp only [List.map_cons, List.count_cons, c0, b0, b1, b2]
      have hite : ∀ x : Bool, (if (x == true) = true then 1 else 0) = (if x = true then 1 else 0) := by decide
      rw [hite, hite, hite]
      omega
    rw [hcnt]
    apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; omega

theorem map_range_getD (x : List Bool) :
    (List.range x.length).map (fun i => x.getD i false) = x := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem any_range_ofFn {n : ℕ} (a : Fin n → Bool) (x : List Bool)
    (hget : ∀ i : Fin n, x.getD i.val false = a i) :
    (List.range n).any (fun i => x.getD i false) = decide (1 ≤ (List.ofFn a).count true) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, hxi⟩
    have hai : a ⟨i, hi⟩ = true := by rw [← hget ⟨i, hi⟩]; exact hxi
    have hmem : true ∈ List.ofFn a := by
      rw [List.mem_ofFn]; exact ⟨⟨i, hi⟩, hai⟩
    have := List.count_pos_iff.mpr hmem
    omega
  · intro hc
    have hmem : true ∈ List.ofFn a := List.count_pos_iff.mp (by omega)
    rw [List.mem_ofFn] at hmem
    obtain ⟨i, hi⟩ := hmem
    exact ⟨i.val, i.isLt, by rw [hget i, hi]⟩

theorem any_range_shift_ofFn {n m : ℕ} (b : Fin m → Bool) (x : List Bool)
    (hget : ∀ j : Fin m, x.getD (n + j.val) false = b j) :
    ((List.range m).map (fun j => n + j)).any (fun i => x.getD i false) =
      decide (1 ≤ (List.ofFn b).count true) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.mem_map, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨w, ⟨j, hj, rfl⟩, hxw⟩
    have hbj : b ⟨j, hj⟩ = true := by rw [← hget ⟨j, hj⟩]; exact hxw
    have hmem : true ∈ List.ofFn b := by
      rw [List.mem_ofFn]; exact ⟨⟨j, hj⟩, hbj⟩
    have := List.count_pos_iff.mpr hmem
    omega
  · intro hc
    have hmem : true ∈ List.ofFn b := List.count_pos_iff.mp (by omega)
    rw [List.mem_ofFn] at hmem
    obtain ⟨j, hj⟩ := hmem
    exact ⟨n + j.val, ⟨j.val, j.isLt, rfl⟩, by rw [hget j, hj]⟩

theorem count_ofFn_eq_one {n : ℕ} (a : Fin n → Bool) (h : (List.ofFn a).count true = 1) :
    ∃ u : Fin n, a u = true ∧ ∀ i : Fin n, a i = decide (i = u) := by
  have hmem : true ∈ List.ofFn a := List.count_pos_iff.mp (by omega)
  rw [List.mem_ofFn] at hmem
  obtain ⟨u, hu⟩ := hmem
  refine ⟨u, hu, ?_⟩
  intro i
  by_cases hiu : i = u
  · subst hiu; simp [hu]
  · simp only [hiu, decide_false]
    by_contra hne
    have hai : a i = true := by cases h1 : a i <;> simp [h1] at hne ⊢
    -- Two distinct true positions imply count >= 2!
    have hge2 : 2 ≤ (List.ofFn a).count true := by
      have hgen : ∀ (L : List (Fin n)), L.Nodup → u ∈ L → i ∈ L →
          2 ≤ (L.map a).count true := by
        intro L hnd huL hiL
        induction L with
        | nil => simp at huL
        | cons x xs ih =>
          rw [List.nodup_cons] at hnd
          simp only [List.map_cons, List.count_cons]
          simp only [List.mem_cons] at huL hiL
          rcases huL with rfl | hu'
          · rcases hiL with rfl | hi'
            · exact absurd rfl hiu
            · have hm : true ∈ xs.map a := List.mem_map.mpr ⟨i, hi', hai⟩
              have hp := List.count_pos_iff.mpr hm
              simp only [hu, beq_self_eq_true, ↓reduceIte]; omega
          · rcases hiL with rfl | hi'
            · have hm : true ∈ xs.map a := List.mem_map.mpr ⟨u, hu', hu⟩
              have hp := List.count_pos_iff.mpr hm
              simp only [hai, beq_self_eq_true, ↓reduceIte]; omega
            · have := ih hnd.2 hu' hi'
              omega
      have h1 := hgen (List.finRange n) (List.nodup_finRange n) (List.mem_finRange u) (List.mem_finRange i)
      have hmap : (List.finRange n).map a = List.ofFn a := by
        apply List.ext_getElem <;> simp
      rw [hmap] at h1
      exact h1
    omega

end PEqualNP.Outside.L_meta_25463_aux

open PEqualNP.Outside.L_meta_25463_aux in
theorem PEqualNP.Outside.L_meta_25463 : ∀ (n m s : ℕ) (A : Fin n → Fin m → Bool), 3 ≤ n + m → (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ PEqualNP.Represents.Represents A C) → ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C' ∧ C'.size ≤ s + 6 * (n + m) ∧ ∀ (a : Fin n → Bool) (b : Fin m → Bool), C'.eval (List.ofFn a ++ List.ofFn b) = (decide (2 < (List.ofFn a).count true + (List.ofFn b).count true) || (decide ((List.ofFn a).count true + (List.ofFn b).count true = 2) && decide (∃ (u : Fin n) (v : Fin m), a u = true ∧ b v = true ∧ A u v = true))) := by
  intro n m s A hnm ⟨C, hCmono, hCsize, hCrep⟩
  by_cases hcase : n = 0 ∨ m = 0 ∨ n + m + C.gates.length ≤ C.output
  · -- Just output T3!
    let ws := List.range (n + m)
    let t3 := atLeastThree (n + m) ws
    let C' : PEqualNP.CircuitLowerBounds.Circuit := ⟨t3.1, t3.2⟩
    refine ⟨C', ?_, ?_, ?_⟩
    · intro g hg; exact atLeastThree_ok (n + m) ws g hg
    · simp only [C', PEqualNP.CircuitLowerBounds.Circuit.size]
      have hl : t3.1.length = 5 * (n + m) - 9 := by
        have := atLeastThree_len (n + m) ws (by simp [ws]; omega)
        simpa [ws] using this
      omega
    · intro a b
      set x := List.ofFn a ++ List.ofFn b
      have hxlen : x.length = n + m := by simp [x]
      simp only [C', PEqualNP.CircuitLowerBounds.Circuit.eval, wires_eq_foldl]
      rw [atLeastThree_eval (n + m) ws x hxlen (by simp [ws]; omega) (by intro w hw; simp [ws] at hw; exact hw)]
      have hmap : ws.map (fun w => x.getD w false) = x := by
        simpa [ws, hxlen] using map_range_getD x
      rw [hmap]
      have hcnt : x.count true = (List.ofFn a).count true + (List.ofFn b).count true := by
        simp [x, List.count_append]
      rw [hcnt]
      have hno : ¬ (∃ (u : Fin n) (v : Fin m), a u = true ∧ b v = true ∧ A u v = true) := by
        rintro ⟨u, v, _, _, hA⟩
        rcases hcase with rfl | rfl | hout
        · exact Fin.elim0 u
        · exact Fin.elim0 v
        · have hev := hCrep u v
          have hlenw : (C.wires (PEqualNP.Represents.oneEach u v)).length = n + m + C.gates.length := by
            rw [wires_eq_foldl, foldl_length]; simp [PEqualNP.Represents.oneEach]
          have hfalse : C.eval (PEqualNP.Represents.oneEach u v) = false := by
            simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, List.getD_eq_getElem?_getD]
            rw [List.getElem?_eq_none (by omega)]
            rfl
          rw [hfalse] at hev
          rw [hA] at hev
          cases hev
      have hd : decide (∃ (u : Fin n) (v : Fin m), a u = true ∧ b v = true ∧ A u v = true) = false :=
        decide_eq_false hno
      rw [hd]
      simp
  · push_neg at hcase
    obtain ⟨hn0, hm0, hout_lt⟩ := hcase
    have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn0
    have hm1 : 1 ≤ m := Nat.pos_of_ne_zero hm0
    let base0 := n + m + C.gates.length
    let ws := List.range (n + m)
    let gT3 := atLeastThree base0 ws
    let base1 := base0 + gT3.1.length
    let gA := orChainAux base1 0 ((List.range (n - 1)).map (fun i => i + 1))
    let base2 := base1 + gA.1.length
    let gB := orChainAux base2 n ((List.range (m - 1)).map (fun j => n + j + 1))
    let base3 := base2 + gB.1.length
    let gateBoth : PEqualNP.CircuitLowerBounds.Gate := ⟨.and, [gA.2, gB.2]⟩
    let gateHit : PEqualNP.CircuitLowerBounds.Gate := ⟨.and, [base3, C.output]⟩
    let gateOut : PEqualNP.CircuitLowerBounds.Gate := ⟨.or, [gT3.2, base3 + 1]⟩
    let C' : PEqualNP.CircuitLowerBounds.Circuit :=
      ⟨C.gates ++ gT3.1 ++ gA.1 ++ gB.1 ++ [gateBoth, gateHit, gateOut], base3 + 2⟩
    have hlT3 : gT3.1.length = 5 * (n + m) - 9 := by
      have := atLeastThree_len base0 ws (by simp [ws]; omega)
      simpa [ws] using this
    have hlA : gA.1.length = n - 1 := by simp [gA, orChainAux_len]
    have hlB : gB.1.length = m - 1 := by simp [gB, orChainAux_len]
    have hT3_lt : gT3.2 < base1 := atLeastThree_out_lt base0 ws (by simp [ws]; omega)
    have hA_lt : gA.2 < base2 := by
      have h := orChainAux_out_lt base1 0 ((List.range (n - 1)).map (fun i => i + 1)) (by omega)
      simp only [List.length_map, List.length_range] at h
      simp only [base2, hlA]
      omega
    have hB_lt : gB.2 < base3 := by
      have h := orChainAux_out_lt base2 n ((List.range (m - 1)).map (fun j => n + j + 1)) (by omega)
      simp only [List.length_map, List.length_range] at h
      simp only [base3, hlB]
      omega
    refine ⟨C', ?_, ?_, ?_⟩
    · intro g hg
      simp only [C', List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with (((h1 | h2) | h3) | h4) | (rfl | rfl | rfl)
      · exact hCmono g h1
      · exact atLeastThree_ok base0 ws g h2
      · exact orChainAux_ok base1 0 _ g h3
      · exact orChainAux_ok base2 n _ g h4
      · exact ⟨by simp [gateBoth], by simp [gateBoth]⟩
      · exact ⟨by simp [gateHit], by simp [gateHit]⟩
      · exact ⟨by simp [gateOut], by simp [gateOut]⟩
    · simp only [C', PEqualNP.CircuitLowerBounds.Circuit.size, List.length_append, List.length_cons,
        List.length_nil]
      simp only [PEqualNP.CircuitLowerBounds.Circuit.size] at hCsize
      omega
    · intro a b
      set x := List.ofFn a ++ List.ofFn b
      have hxlen : x.length = n + m := by simp [x]
      have hx_left : ∀ i : Fin n, x.getD i.val false = a i := by
        intro i
        have hlt : i.val < (List.ofFn a).length := by simp
        simp [x, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
      have hx_right : ∀ j : Fin m, x.getD (n + j.val) false = b j := by
        intro j
        simp [x, List.getD_eq_getElem?_getD]
      simp only [C', PEqualNP.CircuitLowerBounds.Circuit.eval, wires_eq_foldl, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      set v0 := C.gates.foldl step x
      set v1 := gT3.1.foldl step v0
      set v2 := gA.1.foldl step v1
      set v3 := gB.1.foldl step v2
      set v4 := step v3 gateBoth
      set v5 := step v4 gateHit
      have hl0 : v0.length = base0 := by simp [v0, base0, foldl_length, hxlen]
      have hlv1 : v1.length = base1 := by simp [v1, base1, foldl_length, hl0]
      have hlv2 : v2.length = base2 := by simp [v2, base2, foldl_length, hlv1]
      have hlv3 : v3.length = base3 := by simp [v3, base3, foldl_length, hlv2]
      have hlv4 : v4.length = base3 + 1 := by simp [v4, step_length, hlv3]
      have hlv5 : v5.length = base3 + 2 := by simp [v5, step_length, hlv4]
      -- Evaluate T3
      have hv1_T3 : v1.getD gT3.2 false = decide (2 < (List.ofFn a).count true + (List.ofFn b).count true) := by
        rw [atLeastThree_eval base0 ws v0 hl0 (by simp [ws]; omega) (by intro w hw; simp [ws] at hw; omega)]
        have hmap : ws.map (fun w => v0.getD w false) = x := by
          have hcongr : ws.map (fun w => v0.getD w false) = ws.map (fun w => x.getD w false) := by
            apply List.map_congr_left
            intro w hw; simp [ws] at hw
            exact foldl_getD_lt C.gates x (by omega)
          rw [hcongr]
          simpa [ws, hxlen] using map_range_getD x
        rw [hmap]
        simp [x, List.count_append]
      -- Evaluate A1
      have hv2_A : v2.getD gA.2 false = decide (1 ≤ (List.ofFn a).count true) := by
        rw [orChainAux_eval base1 0 _ v1 hlv1 (by omega) (by intro w hw; simp at hw; obtain ⟨i, hi, rfl⟩ := hw; omega)]
        have h0 : v1.getD 0 false = x.getD 0 false := by
          rw [foldl_getD_lt gT3.1 v0 (by omega), foldl_getD_lt C.gates x (by omega)]
        have hany : ((List.range (n - 1)).map (fun i => i + 1)).any (fun w => v1.getD w false) =
            ((List.range (n - 1)).map (fun i => i + 1)).any (fun w => x.getD w false) := by
          apply any_congr_mem
          intro w hw; simp at hw; obtain ⟨i, hi, rfl⟩ := hw
          rw [foldl_getD_lt gT3.1 v0 (by omega), foldl_getD_lt C.gates x (by omega)]
        rw [h0, hany]
        have hrng : List.range n = 0 :: (List.range (n - 1)).map (fun i => i + 1) := by
          cases n with
          | zero => omega
          | succ k => simp [List.range_succ_eq_map]
        have heq := any_range_ofFn a x hx_left
        rw [hrng, List.any_cons] at heq
        exact heq
      -- Evaluate B1
      have hv3_B : v3.getD gB.2 false = decide (1 ≤ (List.ofFn b).count true) := by
        rw [orChainAux_eval base2 n _ v2 hlv2 (by omega) (by intro w hw; simp at hw; obtain ⟨j, hj, rfl⟩ := hw; omega)]
        have h0 : v2.getD n false = x.getD n false := by
          rw [foldl_getD_lt gA.1 v1 (by omega), foldl_getD_lt gT3.1 v0 (by omega), foldl_getD_lt C.gates x (by omega)]
        have hany : ((List.range (m - 1)).map (fun j => n + j + 1)).any (fun w => v2.getD w false) =
            ((List.range (m - 1)).map (fun j => n + j + 1)).any (fun w => x.getD w false) := by
          apply any_congr_mem
          intro w hw; simp at hw; obtain ⟨j, hj, rfl⟩ := hw
          rw [foldl_getD_lt gA.1 v1 (by omega), foldl_getD_lt gT3.1 v0 (by omega), foldl_getD_lt C.gates x (by omega)]
        rw [h0, hany]
        have hrng : (List.range m).map (fun j => n + j) = n :: (List.range (m - 1)).map (fun j => n + j + 1) := by
          cases m with
          | zero => omega
          | succ k =>
            simp only [List.range_succ_eq_map, List.map_cons, Nat.add_zero, List.map_map,
              Nat.add_sub_cancel]
            rfl
        have heq := any_range_shift_ofFn b x hx_right
        rw [hrng, List.any_cons] at heq
        exact heq
      -- Evaluate Both, Hit, Out
      have hv3_A : v3.getD gA.2 false = decide (1 ≤ (List.ofFn a).count true) := by
        rw [foldl_getD_lt gB.1 v2 (by omega), hv2_A]
      have hv4_Both : v4.getD base3 false = (decide (1 ≤ (List.ofFn a).count true) && decide (1 ≤ (List.ofFn b).count true)) := by
        have h := step_getD_last v3 gateBoth; rw [hlv3] at h
        simp only [gateBoth, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          id_eq, Bool.and_true] at h
        rw [hv3_A, hv3_B] at h; exact h
      have hv4_C : v4.getD C.output false = C.eval x := by
        rw [step_getD_lt v3 gateBoth (by omega), foldl_getD_lt gB.1 v2 (by omega),
          foldl_getD_lt gA.1 v1 (by omega), foldl_getD_lt gT3.1 v0 (by omega)]
        rfl
      have hv5_Hit : v5.getD (base3 + 1) false =
          ((decide (1 ≤ (List.ofFn a).count true) && decide (1 ≤ (List.ofFn b).count true)) && C.eval x) := by
        have h := step_getD_last v4 gateHit; rw [hlv4] at h
        simp only [gateHit, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          id_eq, Bool.and_true] at h
        rw [hv4_Both, hv4_C] at h; exact h
      have hv5_T3 : v5.getD gT3.2 false = decide (2 < (List.ofFn a).count true + (List.ofFn b).count true) := by
        rw [step_getD_lt v4 gateHit (by omega), step_getD_lt v3 gateBoth (by omega),
          foldl_getD_lt gB.1 v2 (by omega), foldl_getD_lt gA.1 v1 (by omega), hv1_T3]
      have hfinal := step_getD_last v5 gateOut
      rw [hlv5] at hfinal
      simp only [gateOut, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        id_eq, Bool.or_false] at hfinal
      rw [hfinal, hv5_T3, hv5_Hit]
      set ka := (List.ofFn a).count true
      set kb := (List.ofFn b).count true
      by_cases hgt : 2 < ka + kb
      · rw [decide_eq_true hgt]; rfl
      · have hgtf : decide (2 < ka + kb) = false := decide_eq_false hgt
        rw [hgtf]
        simp only [Bool.false_or]
        by_cases heq2 : ka + kb = 2
        · have heq2t : decide (ka + kb = 2) = true := decide_eq_true heq2
          rw [heq2t]
          simp only [Bool.true_and]
          by_cases h11 : ka = 1 ∧ kb = 1
          · obtain ⟨hka, hkb⟩ := h11
            obtain ⟨u, hu, hua⟩ := count_ofFn_eq_one a hka
            obtain ⟨v, hv, hvb⟩ := count_ofFn_eq_one b hkb
            have hx_eq : x = PEqualNP.Represents.oneEach u v := by
              simp only [x, PEqualNP.Represents.oneEach]
              congr 1
              · apply List.ext_getElem <;> simp [hua]
              · apply List.ext_getElem <;> simp [hvb]
            have hCval : C.eval x = A u v := by rw [hx_eq]; exact hCrep u v
            have hex : decide (∃ (u' : Fin n) (v' : Fin m), a u' = true ∧ b v' = true ∧ A u' v' = true) = A u v := by
              apply Bool.eq_iff_iff.mpr
              simp only [decide_eq_true_eq]
              constructor
              · rintro ⟨u', v', hau', hbv', hA'⟩
                have hu' : u' = u := by
                  have := hua u'; rw [hau'] at this; exact of_decide_eq_true this.symm
                have hv' : v' = v := by
                  have := hvb v'; rw [hbv'] at this; exact of_decide_eq_true this.symm
                subst hu'; subst hv'; exact hA'
              · intro hAuv; exact ⟨u, v, hu, hv, hAuv⟩
            have hka1 : decide (1 ≤ ka) = true := by simp [hka]
            have hkb1 : decide (1 ≤ kb) = true := by simp [hkb]
            rw [hka1, hkb1, hCval, hex]
            simp
          · have hzero : ka = 0 ∨ kb = 0 := by omega
            have hno : ¬ (∃ (u : Fin n) (v : Fin m), a u = true ∧ b v = true ∧ A u v = true) := by
              rintro ⟨u, v, hau, hbv, _⟩
              rcases hzero with hka0 | hkb0
              · have hmem : true ∈ List.ofFn a := List.mem_ofFn.mpr ⟨u, hau⟩
                have := List.count_pos_iff.mpr hmem; omega
              · have hmem : true ∈ List.ofFn b := List.mem_ofFn.mpr ⟨v, hbv⟩
                have := List.count_pos_iff.mpr hmem; omega
            rw [decide_eq_false hno]
            rcases hzero with hka0 | hkb0
            · have : decide (1 ≤ ka) = false := by simp [hka0]
              rw [this]; simp
            · have : decide (1 ≤ kb) = false := by simp [hkb0]
              rw [this]; simp
        · rw [decide_eq_false heq2]
          simp only [Bool.false_and]
          have hlt2 : ka = 0 ∨ kb = 0 := by omega
          rcases hlt2 with hka0 | hkb0
          · have : decide (1 ≤ ka) = false := by simp [hka0]
            rw [this]; simp
          · have : decide (1 ≤ kb) = false := by simp [hkb0]
            rw [this]; simp
