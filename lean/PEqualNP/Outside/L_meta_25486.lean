import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25486_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

def stepF (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma stepF_length (w : List Bool) (g : Gate) : (stepF w g).length = w.length + 1 := by
  simp [stepF]

lemma fold_length (gs : List Gate) :
    ∀ w : List Bool, (gs.foldl stepF w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih, stepF_length, List.length_cons]
    omega

lemma fold_low (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl stepF w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [List.foldl_cons, ih (stepF w g) i (by rw [stepF_length]; omega)]
    simp only [stepF]
    rw [List.getD_append _ _ _ _ hi]

lemma fold_gate (gs : List Gate) : ∀ (w : List Bool) (j : ℕ) (hj : j < gs.length),
    (∀ i ∈ gs[j].inputs, i < w.length + j) →
    (gs.foldl stepF w).getD (w.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (gs.foldl stepF w).getD i false) := by
  induction gs with
  | nil => intro w j hj; simp at hj
  | cons g gs ih =>
    intro w j hj hin
    rw [List.foldl_cons]
    cases j with
    | zero =>
      simp only [List.getElem_cons_zero, Nat.add_zero] at hin ⊢
      rw [fold_low gs (stepF w g) w.length (by rw [stepF_length]; omega)]
      have h1 : (stepF w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepF]
      rw [h1]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hlt := hin i hi
      rw [fold_low gs (stepF w g) i (by rw [stepF_length]; omega)]
      simp only [stepF]
      rw [List.getD_append _ _ _ _ hlt]
    | succ j =>
      simp only [List.getElem_cons_succ] at hin ⊢
      have h := ih (stepF w g) j (by simpa using hj)
        (by intro i hi; have := hin i hi; rw [stepF_length]; omega)
      rw [stepF_length] at h
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      rw [e]
      exact h

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := fold_length _ _

lemma wires_low (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false := fold_low _ _ _ hi

lemma wires_high (C : Circuit) (x : List Bool) (i : ℕ) (hi : x.length + C.gates.length ≤ i) :
    (C.wires x).getD i false = false := by
  apply List.getD_eq_default
  rw [wires_length]
  exact hi

lemma gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getElem?_eq_getElem hj]

lemma wires_gate (N : ℕ) (C : Circuit) (hRB : ReadsBack N C) (x : List Bool) (hx : x.length = N)
    (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (N + j) false =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => (C.wires x).getD i false) := by
  subst hx
  apply fold_gate
  intro i hi
  have h := hRB j hj i (by rw [gateAt_eq C j hj]; exact hi)
  exact h

lemma oneEach_length {n m : ℕ} (u : Fin n) (v : Fin m) : (oneEach u v).length = n + m := by
  simp [oneEach]

lemma oneEach_getD {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (oneEach u v).getD i false = (decide (i = u.val) || decide (i = n + v.val)) := by
  unfold oneEach
  by_cases h1 : i < n
  · rw [List.getD_append _ _ _ _ (by simpa using h1)]
    rw [List.getD_eq_getElem _ _ (by simpa using h1)]
    have h2 : ¬ i = n + v.val := by omega
    simp [h2, Fin.ext_iff]
  · by_cases h2 : i < n + m
    · rw [List.getD_append_right _ _ _ _ (by simpa using h1)]
      rw [List.getD_eq_getElem _ _ (by simp; omega)]
      have h3 : ¬ i = u.val := by omega
      simp [h3, Fin.ext_iff]
      omega
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      have h3 : ¬ i = u.val := by omega
      have h4 : ¬ i = n + v.val := by omega
      simp [h3, h4]

lemma colOnly_length (n : ℕ) {m : ℕ} (v : Fin m) :
    (List.replicate n false ++ List.ofFn (fun c₀ : Fin m => decide (c₀ = v))).length = n + m := by
  simp

lemma colOnly_getD (n : ℕ) {m : ℕ} (v : Fin m) (i : ℕ) :
    (List.replicate n false ++ List.ofFn (fun c₀ : Fin m => decide (c₀ = v))).getD i false =
      decide (i = n + v.val) := by
  by_cases h1 : i < n
  · rw [List.getD_append _ _ _ _ (by simpa using h1)]
    rw [List.getD_eq_getElem _ _ (by simpa using h1)]
    have h3 : ¬ i = n + v.val := by omega
    simp [h3]
  · by_cases h2 : i < n + m
    · rw [List.getD_append_right _ _ _ _ (by simpa using h1)]
      rw [List.getD_eq_getElem _ _ (by simp; omega)]
      simp [Fin.ext_iff]
      omega
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      have h3 : ¬ i = n + v.val := by omega
      simp [h3]

lemma mono (N : ℕ) (C : Circuit) (hAO : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hRB : ReadsBack N C)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (hxy : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ k w : ℕ, w < k → (C.wires x).getD w false = true → (C.wires y).getD w false = true := by
  intro k
  induction k with
  | zero => intro w hw; omega
  | succ k ih =>
    intro w hw hval
    by_cases hlow : w < N
    · rw [wires_low C _ w (by rw [hx]; exact hlow)] at hval
      rw [wires_low C _ w (by rw [hy]; exact hlow)]
      exact hxy w hval
    · by_cases hhigh : N + C.gates.length ≤ w
      · rw [wires_high C _ w (by rw [hx]; exact hhigh)] at hval
        exact absurd hval (by simp)
      · obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
        have hj : j < C.gates.length := by omega
        rw [wires_gate N C hRB _ hx j hj] at hval
        rw [wires_gate N C hRB _ hy j hj]
        have hlt : ∀ i ∈ (C.gates[j]).inputs, i < N + j := by
          intro i hi
          exact hRB j hj i (by rw [gateAt_eq C j hj]; exact hi)
        rcases hAO (C.gates[j]) (List.getElem_mem hj) with hop | hop
        · rw [hop] at hval ⊢
          simp only [GateOp.eval, List.all_eq_true, List.mem_map, forall_exists_index, and_imp,
            forall_apply_eq_imp_iff₂, id_eq] at hval ⊢
          intro i hi
          exact ih i (by have := hlt i hi; omega) (hval i hi)
        · rw [hop] at hval ⊢
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, exists_exists_and_eq_and,
            id_eq] at hval ⊢
          obtain ⟨i, hi, hv⟩ := hval
          exact ⟨i, hi, ih i (by have := hlt i hi; omega) hv⟩

lemma reader_unique (C : Circuit) (w j1 j2 : ℕ)
    (h : readsIn C (Finset.range C.gates.length) w = 1)
    (h1 : j1 < C.gates.length) (h2 : j2 < C.gates.length)
    (m1 : w ∈ (C.gates[j1]).inputs) (m2 : w ∈ (C.gates[j2]).inputs) : j1 = j2 := by
  by_contra hne
  have c1 : 0 < (gateAt C j1).inputs.count w := by
    rw [gateAt_eq C j1 h1]; exact List.count_pos_iff.mpr m1
  have c2 : 0 < (gateAt C j2).inputs.count w := by
    rw [gateAt_eq C j2 h2]; exact List.count_pos_iff.mpr m2
  have hsub : ({j1, j2} : Finset ℕ) ⊆ Finset.range C.gates.length := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact Finset.mem_range.mpr h1
    · exact Finset.mem_range.mpr h2
  have hle : ∑ j ∈ ({j1, j2} : Finset ℕ), (gateAt C j).inputs.count w ≤
      ∑ j ∈ Finset.range C.gates.length, (gateAt C j).inputs.count w :=
    Finset.sum_le_sum_of_subset hsub
  rw [Finset.sum_pair hne] at hle
  unfold readsIn at h
  omega

lemma and_pair (g : Gate) (f : ℕ → Bool) (a b : ℕ) (hop : g.op = GateOp.and)
    (hin : g.inputs = [a, b] ∨ g.inputs = [b, a]) :
    g.op.eval (g.inputs.map f) = (f a && f b) := by
  rw [hop]
  rcases hin with e | e
  · simp [e, GateOp.eval]
  · simp [e, GateOp.eval, Bool.and_comm]

lemma or_pair (g : Gate) (f : ℕ → Bool) (a b : ℕ) (hop : g.op = GateOp.or)
    (hin : g.inputs = [a, b] ∨ g.inputs = [b, a]) :
    g.op.eval (g.inputs.map f) = (f a || f b) := by
  rw [hop]
  rcases hin with e | e
  · simp [e, GateOp.eval]
  · simp [e, GateOp.eval, Bool.or_comm]

lemma agree (N : ℕ) (C : Circuit) (hRB : ReadsBack N C) (x y : List Bool)
    (hx : x.length = N) (hy : y.length = N) (S : ℕ → Prop) (B : ℕ)
    (hin : ∀ w, w < N → ¬ S w → x.getD w false = y.getD w false)
    (hgate : ∀ k (hk : k < C.gates.length), N + k < B → ¬ S (N + k) →
      (∀ a ∈ (C.gates[k]).inputs, ¬ S a) ∨
        (C.wires x).getD (N + k) false = (C.wires y).getD (N + k) false) :
    ∀ w, w < B → ¬ S w → (C.wires x).getD w false = (C.wires y).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hwB hS
    by_cases hlow : w < N
    · rw [wires_low C _ w (by rw [hx]; exact hlow), wires_low C _ w (by rw [hy]; exact hlow)]
      exact hin w hlow hS
    · by_cases hhigh : N + C.gates.length ≤ w
      · rw [wires_high C _ w (by rw [hx]; exact hhigh), wires_high C _ w (by rw [hy]; exact hhigh)]
      · obtain ⟨k, rfl⟩ : ∃ k, w = N + k := ⟨w - N, by omega⟩
        have hk : k < C.gates.length := by omega
        rcases hgate k hk hwB hS with hall | heq
        · rw [wires_gate N C hRB _ hx k hk, wires_gate N C hRB _ hy k hk]
          congr 1
          apply List.map_congr_left
          intro a ha
          have hlt := hRB k hk a (by rw [gateAt_eq C k hk]; exact ha)
          exact ih a (by omega) (by omega) (hall a ha)
        · exact heq

end PEqualNP.Outside.L_meta_25486_aux

open PEqualNP.Outside.L_meta_25486_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_25486 : ∀ (n m : ℕ) (G : Fin n → Fin m → Bool)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (u v : Fin n)
    (i j t : Fin C.gates.length) (p q : ℕ),
  let g := PEqualNP.MetaComplexity.NestedCover.gateAt C
  let wire := fun z : Fin C.gates.length => n + m + z.val
  let reads := PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.gates.length)
  let binary := fun (z : Fin C.gates.length) (op : PEqualNP.CircuitLowerBounds.GateOp)
      (a b : ℕ) =>
    (g z.val).op = op ∧ ((g z.val).inputs = [a, b] ∨ (g z.val).inputs = [b, a])
  PEqualNP.MetaComplexity.Monotone2 C →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C →
  PEqualNP.Represents.Represents G C →
  u ≠ v → i ≠ j →
  binary i .or u.val p → binary j .or v.val q → binary t .and (wire i) (wire j) →
  reads u.val = 1 → reads v.val = 1 → reads (wire i) = 1 →
  C.output ∉ [u.val, v.val, wire i] →
  ∀ c : Fin m, (∃ z : Fin n, G z c = false) →
    let alone := List.replicate n false ++ List.ofFn (fun col : Fin m => decide (col = c))
    let partner := (C.wires alone).getD q false
    (G u c = true → partner = true) ∧ (G v c = true → partner = false) := by
  intro n m G C u v i j t p q
  dsimp only
  intro hM hRB hRep huv hij hi hj ht hu hv hI hout c hmiss
  let N := n + m
  let I := N + i.val
  let J := N + j.val
  let T := N + t.val
  let alone := List.replicate n false ++ List.ofFn (fun col : Fin m => decide (col = c))
  have L : alone.length = N := colOnly_length n c
  have Lr (r : Fin n) : (oneEach r c).length = N := oneEach_length r c
  have hAO : ∀ gate ∈ C.gates, gate.op = GateOp.and ∨ gate.op = GateOp.or := by
    intro gate hgate
    simpa using (hM gate hgate).1
  rw [gateAt_eq C _ i.isLt] at hi
  rw [gateAt_eq C _ j.isLt] at hj
  rw [gateAt_eq C _ t.isLt] at ht
  have mu : u.val ∈ C.gates[i.val].inputs := by rcases hi.2 with h | h <;> simp [h]
  have mv : v.val ∈ C.gates[j.val].inputs := by rcases hj.2 with h | h <;> simp [h]
  have mI : I ∈ C.gates[t.val].inputs := by rcases ht.2 with h | h <;> simp [h, I, N]
  have mJ : J ∈ C.gates[t.val].inputs := by rcases ht.2 with h | h <;> simp [h, J, N]
  have jlt : J < T := hRB _ t.isLt J (by rw [gateAt_eq C _ t.isLt]; exact mJ)
  have hIJ : I ≠ J := by
    dsimp [I,J]
    intro e
    exact hij (Fin.ext (by omega))
  have ov : C.output ≠ v.val := by intro e; apply hout; simp [e]
  have ou : C.output ≠ u.val := by intro e; apply hout; simp [e]
  have oi : C.output ≠ I := by intro e; apply hout; simp [e, I, N]
  have hinput (r : Fin n) (a : ℕ) (hne : a ≠ r.val) :
      (oneEach r c).getD a false = alone.getD a false := by
    dsimp [alone]
    rw [oneEach_getD, colOnly_getD]
    simp [hne]
  obtain ⟨z, hz⟩ := hmiss
  have off : (C.wires alone).getD C.output false = false := by
    by_contra hn
    have htr : (C.wires alone).getD C.output false = true := by simpa using hn
    have hm := mono N C hAO hRB alone (oneEach z c) L (Lr z) (by
      intro a ha
      change (List.replicate n false ++ _).getD a false = true at ha
      rw [colOnly_getD] at ha
      rw [oneEach_getD, ha]
      simp) (C.output+1) C.output (by omega) htr
    have he := hRep z c
    change (C.wires (oneEach z c)).getD C.output false = G z c at he
    rw [hm, hz] at he
    contradiction
  have onlyInputs (k : ℕ) (hk : k < C.gates.length) (ki : k ≠ i.val) (kt : k ≠ t.val) :
      ∀ a ∈ C.gates[k].inputs, ¬ (a = u.val ∨ a = I) := by
    intro a ha e
    rcases e with rfl | rfl
    · exact ki (reader_unique C _ _ _ hu hk i.isLt ha mu)
    · exact kt (reader_unique C _ _ _ hI hk t.isLt ha mI)
  have eqInputs : ∀ w, w < N → ¬ (w = u.val ∨ w = I) →
      (oneEach u c).getD w false = alone.getD w false :=
    fun w _ h => hinput u w (fun e => h (Or.inl e))
  have pre := agree N C hRB (oneEach u c) alone (Lr u) L
    (fun w => w = u.val ∨ w = I) T eqInputs (by
      intro k hk hlt hnot
      left
      apply onlyInputs k hk
      · intro h
        exact hnot (Or.inr (by simp [I,h]))
      · intro h
        simp [T,h] at hlt)
  have jval (x : List Bool) (len : x.length = N) :
      (C.wires x).getD J false =
        ((C.wires x).getD v.val false || (C.wires x).getD q false) := by
    rw [show J = N + j.val from rfl, wires_gate N C hRB x len j.val j.isLt]
    exact or_pair _ _ _ _ hj.1 hj.2
  have tval (x : List Bool) (len : x.length = N) :
      (C.wires x).getD T false =
        ((C.wires x).getD I false && (C.wires x).getD J false) := by
    rw [show T = N + t.val from rfl, wires_gate N C hRB x len t.val t.isLt]
    exact and_pair _ _ _ _ ht.1 ht.2
  constructor
  · intro hpos
    by_contra hc
    have hq : (C.wires alone).getD q false = false := by simpa [alone] using hc
    have hv0 : (C.wires alone).getD v.val false = false := by
      rw [wires_low C _ _ (by rw [L]; dsimp [N]; omega)]
      dsimp [alone]
      rw [colOnly_getD]
      simp [show v.val ≠ n + c.val by omega]
    have hj0 : (C.wires alone).getD J false = false := by rw [jval alone L, hv0, hq]; decide
    have hj1 : (C.wires (oneEach u c)).getD J false = false := by
      rw [pre J jlt (by
        intro wrong; rcases wrong with h | h
        · dsimp [J,N] at h; omega
        · exact hIJ h.symm), hj0]
    have heq := agree N C hRB (oneEach u c) alone (Lr u) L
      (fun w => w = u.val ∨ w = I) (C.output+1) eqInputs (by
        intro k hk _ hnot
        by_cases hkt : k = t.val
        · right
          subst k
          change (C.wires (oneEach u c)).getD T false = (C.wires alone).getD T false
          rw [tval _ (Lr u), tval alone L, hj1, hj0]
          simp only [Bool.and_false]
        · left
          exact onlyInputs k hk (fun e => hnot (Or.inr (by simp [I,e]))) hkt)
      C.output (by omega) (fun h => h.elim ou oi)
    have he := hRep u c
    change (C.wires (oneEach u c)).getD C.output false = G u c at he
    rw [he, hpos, off] at heq
    contradiction
  · intro hpos
    by_contra hc
    have hq : (C.wires alone).getD q false = true := by simpa [alone] using hc
    have hv1 : (C.wires (oneEach v c)).getD v.val false = true := by
      rw [wires_low C _ _ (by rw [Lr]; dsimp [N]; omega), oneEach_getD]
      simp
    have heq := agree N C hRB (oneEach v c) alone (Lr v) L
      (fun w => w = v.val) (C.output+1) (fun w _ h => hinput v w h) (by
        intro k hk _ _
        by_cases hkj : k = j.val
        · right
          subst k
          change (C.wires (oneEach v c)).getD J false = (C.wires alone).getD J false
          rw [jval _ (Lr v), jval alone L, hv1, hq]
          simp only [Bool.true_or, Bool.or_true]
        · left
          intro a ha e
          change a = v.val at e
          exact hkj (reader_unique C _ _ _ hv hk j.isLt (e ▸ ha) mv))
      C.output (by omega) ov
    have he := hRep v c
    change (C.wires (oneEach v c)).getD C.output false = G v c at he
    rw [he, hpos, off] at heq
    contradiction
