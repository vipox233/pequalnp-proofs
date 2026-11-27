import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25490_aux

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

lemma bad_input (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (f f' : ℕ → Bool)
    (h1 : g.op.eval (g.inputs.map f) = true) (h2 : g.op.eval (g.inputs.map f') = false) :
    ∃ i ∈ g.inputs, f i = true ∧ f' i = false := by
  by_contra hne
  have hall : ∀ i ∈ g.inputs, f i = true → f' i = true := by
    intro i hi hf
    by_contra hf'
    exact hne ⟨i, hi, hf, by simpa using hf'⟩
  have ht : g.op.eval (g.inputs.map f') = true := by
    rcases hop with hop | hop
    · rw [hop] at h1 ⊢
      simp only [GateOp.eval, List.all_eq_true, List.mem_map, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂, id_eq] at h1 ⊢
      intro i hi
      exact hall i hi (h1 i hi)
    · rw [hop] at h1 ⊢
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, exists_exists_and_eq_and,
        id_eq] at h1 ⊢
      obtain ⟨i, hi, hv⟩ := h1
      exact ⟨i, hi, hall i hi hv⟩
  rw [ht] at h2
  exact absurd h2 (by simp)

lemma dom (n m : ℕ) (G : Fin n → Fin m → Bool) (C : Circuit)
    (hAO : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or) (hRB : ReadsBack (n + m) C)
    (hRep : Represents G C) (v w : Fin n) (iv : ℕ) (hiv : iv < C.gates.length)
    (rv : readsIn C (Finset.range C.gates.length) v.val = 1) (mv : v.val ∈ (C.gates[iv]).inputs)
    (hout : C.output ≠ v.val) (c : Fin m)
    (HI : (C.wires (oneEach w c)).getD (n + m + iv) false = true) :
    G v c = true → G w c = true := by
  intro hvc
  have L1 : (oneEach v c).length = n + m := oneEach_length v c
  have L2 : (oneEach w c).length = n + m := oneEach_length w c
  have key : ∀ t, t ≠ v.val → (C.wires (oneEach v c)).getD t false = true →
      (C.wires (oneEach w c)).getD t false = true := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro htv h1
      by_cases hlow : t < n + m
      · rw [wires_low C _ t (by rw [L1]; exact hlow), oneEach_getD] at h1
        rw [wires_low C _ t (by rw [L2]; exact hlow), oneEach_getD]
        simp only [Bool.or_eq_true, decide_eq_true_eq] at h1 ⊢
        rcases h1 with e | e
        · exact absurd e htv
        · exact Or.inr e
      · by_cases hhigh : n + m + C.gates.length ≤ t
        · rw [wires_high C _ t (by rw [L1]; exact hhigh)] at h1
          exact absurd h1 (by simp)
        · obtain ⟨k, rfl⟩ : ∃ k, t = n + m + k := ⟨t - (n + m), by omega⟩
          have hk : k < C.gates.length := by omega
          by_cases hkv : k = iv
          · rw [hkv]
            exact HI
          · by_contra h2
            have h2' : (C.wires (oneEach w c)).getD (n + m + k) false = false := by simpa using h2
            rw [wires_gate (n + m) C hRB _ L1 k hk] at h1
            rw [wires_gate (n + m) C hRB _ L2 k hk] at h2'
            obtain ⟨a, ha, ha1, ha2⟩ :=
              bad_input _ (hAO (C.gates[k]) (List.getElem_mem hk)) _ _ h1 h2'
            have hlt : a < n + m + k := hRB k hk a (by rw [gateAt_eq C k hk]; exact ha)
            have hav : a ≠ v.val := by
              intro e
              rw [e] at ha
              exact hkv (reader_unique C _ k iv rv hk hiv ha mv)
            rw [ih a hlt hav ha1] at ha2
            exact absurd ha2 (by simp)
  have r1 := hRep v c
  have r2 := hRep w c
  unfold Circuit.eval at r1 r2
  rw [← r2]
  exact key C.output hout (by rw [r1, hvc])

lemma main (n m : ℕ) (G : Fin n → Fin m → Bool) (C : Circuit)
    (r : Fin n → Fin C.gates.length) (s : Fin n → ℕ) (v : Fin n)
    (hM : PEqualNP.MetaComplexity.Monotone2 C) (hRB : ReadsBack (n + m) C)
    (hRep : Represents G C) (hout : ∀ u : Fin n, C.output ≠ u.val)
    (hmiss : ∀ c, ∃ u, G u c = false)
    (hinc : ∀ u w, u ≠ w → ∃ c, G u c = true ∧ G w c = false)
    (hrow : ∀ u : Fin n, readsIn C (Finset.range C.gates.length) u.val = 1 ∧
      (gateAt C (r u).val).op = GateOp.or ∧
      ((gateAt C (r u).val).inputs = [u.val, s u] ∨ (gateAt C (r u).val).inputs = [s u, u.val]))
    (hcard : 2 ≤ (Finset.univ.filter (fun c => G v c = false)).card)
    (hon : ∀ c, G v c = false → (C.wires (List.replicate n false ++ List.ofFn (fun b : Fin m => decide (b = c)))).getD (s v) false = true) :
    ∃ j : Fin C.gates.length, s v = n + m + j.val ∧
      ∀ w, j ≠ r w ∧ n + m + (r w).val ∉ (gateAt C j.val).inputs := by
  have hAO : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have h := (hM g hg).1
    simpa using h
  have ho : ∀ u : Fin n, (C.gates[(r u).val]).op = GateOp.or := by
    intro u
    have h := (hrow u).2.1
    rw [gateAt_eq C _ (r u).isLt] at h
    exact h
  have hin : ∀ u : Fin n, (C.gates[(r u).val]).inputs = [u.val, s u] ∨
      (C.gates[(r u).val]).inputs = [s u, u.val] := by
    intro u
    have h := (hrow u).2.2
    rw [gateAt_eq C _ (r u).isLt] at h
    exact h
  have mu : ∀ u : Fin n, u.val ∈ (C.gates[(r u).val]).inputs := by
    intro u
    rcases hin u with e | e <;> simp [e]
  have ms : ∀ u : Fin n, s u ∈ (C.gates[(r u).val]).inputs := by
    intro u
    rcases hin u with e | e <;> simp [e]
  have hslt : ∀ u : Fin n, s u < n + m + (r u).val := by
    intro u
    exact hRB (r u).val (r u).isLt (s u) (by rw [gateAt_eq C _ (r u).isLt]; exact ms u)

  have Ion : ∀ (u : Fin n) (c : Fin m),
      (C.wires (oneEach u c)).getD (n + m + (r u).val) false = true := by
    intro u c
    have L : (oneEach u c).length = n + m := oneEach_length u c
    have hu : (C.wires (oneEach u c)).getD u.val false = true := by
      rw [wires_low C _ _ (by rw [L]; omega), oneEach_getD]
      simp
    rw [wires_gate (n + m) C hRB _ L (r u).val (r u).isLt, or_pair _ _ _ _ (ho u) (hin u), hu]
    simp

  have hcard1 : 1 < (Finset.univ.filter (fun c => G v c = false)).card := by omega
  obtain ⟨c1, hc1, c2, hc2, hne⟩ := Finset.one_lt_card.mp hcard1
  have g1 : G v c1 = false := (Finset.mem_filter.mp hc1).2
  have g2 : G v c2 = false := (Finset.mem_filter.mp hc2).2
  have e1 := hon c1 g1
  have e2 := hon c2 g2
  have hgate : n + m ≤ s v ∧ s v < n + m + C.gates.length := by
    constructor
    · by_contra hlt
      have hlt' : s v < n + m := by omega
      rw [wires_low C _ _ (by rw [colOnly_length]; exact hlt'), colOnly_getD] at e1 e2
      simp only [decide_eq_true_eq] at e1 e2
      exact hne (Fin.ext (by omega))
    · by_contra hge
      rw [wires_high C _ _ (by rw [colOnly_length]; omega)] at e1
      exact absurd e1 (by simp)
  obtain ⟨j, hj⟩ : ∃ j, s v = n + m + j := ⟨s v - (n + m), by omega⟩
  have hjlt : j < C.gates.length := by omega
  refine ⟨⟨j, hjlt⟩, hj, ?_⟩
  intro w
  constructor
  ·
    intro hjw
    have hjw' : j = (r w).val := congrArg Fin.val hjw
    by_cases hwv : w = v
    · have h := hslt v
      rw [hwv] at hjw'
      omega
    · obtain ⟨c, hvc, hwc⟩ := hinc v w (fun e => hwv e.symm)
      have L : (oneEach w c).length = n + m := oneEach_length w c
      have HI : (C.wires (oneEach w c)).getD (n + m + (r v).val) false = true := by
        have hs : (C.wires (oneEach w c)).getD (s v) false = true := by
          rw [hj, hjw']
          exact Ion w c
        rw [wires_gate (n + m) C hRB _ L (r v).val (r v).isLt, or_pair _ _ _ _ (ho v) (hin v), hs]
        simp
      have h := dom n m G C hAO hRB hRep v w (r v).val (r v).isLt (hrow v).1 (mu v) (hout v) c HI hvc
      rw [hwc] at h
      exact absurd h (by simp)
  ·
    intro hmem
    have hmem' : n + m + (r w).val ∈ (C.gates[j]).inputs := by
      rw [gateAt_eq C j hjlt] at hmem
      exact hmem
    have hlt : n + m + (r w).val < n + m + j := hRB j hjlt _ (by rw [gateAt_eq C j hjlt]; exact hmem')
    by_cases hwv : w = v
    · have h := hslt v
      rw [hwv] at hlt
      omega
    · rcases hAO (C.gates[j]) (List.getElem_mem hjlt) with hop | hop
      ·
        obtain ⟨c0, hwc0, hvc0⟩ := hinc w v hwv
        have L0 : (List.replicate n false ++ List.ofFn (fun b : Fin m => decide (b = c0))).length = n + m := colOnly_length n c0
        have hs := hon c0 hvc0
        rw [hj, wires_gate (n + m) C hRB _ L0 j hjlt, hop] at hs
        simp only [GateOp.eval, List.all_eq_true, List.mem_map, forall_exists_index, and_imp,
          forall_apply_eq_imp_iff₂, id_eq] at hs
        have hI := hs _ hmem'

        obtain ⟨z, hz⟩ := hmiss c0
        have o0 : (C.wires (List.replicate n false ++ List.ofFn (fun b : Fin m => decide (b = c0)))).getD C.output false = false := by
          by_contra hne0
          have htr : (C.wires (List.replicate n false ++ List.ofFn (fun b : Fin m => decide (b = c0)))).getD C.output false = true := by simpa using hne0
          have h := mono (n + m) C hAO hRB _ (oneEach z c0) L0 (oneEach_length z c0)
            (by
              intro a ha
              rw [colOnly_getD] at ha
              rw [oneEach_getD, ha]
              simp) (C.output + 1) C.output (by omega) htr
          have h2 := hRep z c0
          unfold Circuit.eval at h2
          rw [h, hz] at h2
          exact absurd h2 (by simp)
        have LW : (oneEach w c0).length = n + m := oneEach_length w c0
        have hA := agree (n + m) C hRB (oneEach w c0) (List.replicate n false ++ List.ofFn (fun b : Fin m => decide (b = c0))) LW L0 (fun t => t = w.val) (C.output + 1)
          (by
            intro t _ hS
            rw [oneEach_getD, colOnly_getD]
            have h3 : ¬ t = w.val := hS
            simp [h3])
          (by
            intro k hk _ _
            by_cases hkw : k = (r w).val
            · right
              rw [hkw, Ion w c0, hI]
            · left
              intro a ha e
              have e' : a = w.val := e
              rw [e'] at ha
              exact hkw (reader_unique C _ k (r w).val (hrow w).1 hk (r w).isLt ha (mu w)))
          C.output (by omega) (hout w)
        have r1 := hRep w c0
        unfold Circuit.eval at r1
        rw [r1, hwc0, o0] at hA
        exact absurd hA (by simp)
      ·
        obtain ⟨c, hvc, hwc⟩ := hinc v w (fun e => hwv e.symm)
        have L : (oneEach w c).length = n + m := oneEach_length w c
        have HI : (C.wires (oneEach w c)).getD (n + m + (r v).val) false = true := by
          have hs : (C.wires (oneEach w c)).getD (s v) false = true := by
            rw [hj, wires_gate (n + m) C hRB _ L j hjlt, hop]
            simp only [GateOp.eval, List.any_eq_true, List.mem_map, exists_exists_and_eq_and, id_eq]
            exact ⟨_, hmem', Ion w c⟩
          rw [wires_gate (n + m) C hRB _ L (r v).val (r v).isLt, or_pair _ _ _ _ (ho v) (hin v), hs]
          simp
        have h := dom n m G C hAO hRB hRep v w (r v).val (r v).isLt (hrow v).1 (mu v) (hout v) c HI hvc
        rw [hwc] at h
        exact absurd h (by simp)

end PEqualNP.Outside.L_meta_25490_aux

theorem PEqualNP.Outside.L_meta_25490 : (∀ (n m : ℕ) (G : Fin n → Fin m → Bool)
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (r : Fin n → Fin C.gates.length) (s : Fin n → ℕ) (v : Fin n),
  let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
  let wire := fun idx : Fin C.gates.length => n + m + idx.val
  let reads := PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.gates.length)
  let col := fun label : Fin m =>
    List.replicate n false ++ List.ofFn (fun b : Fin m => decide (b = label))
  PEqualNP.MetaComplexity.Monotone2 C →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C →
  PEqualNP.Represents.Represents G C →
  (∀ u : Fin n, C.output ≠ u.val) →
  (∀ c, ∃ u, G u c = false) →
  (∀ u w, u ≠ w → ∃ c, G u c = true ∧ G w c = false) →
  (∀ u : Fin n, reads u.val = 1 ∧ (gate (r u).val).op = .or ∧
    ((gate (r u).val).inputs = [u.val, s u] ∨
      (gate (r u).val).inputs = [s u, u.val])) →
  2 ≤ (Finset.univ.filter (fun c => G v c = false)).card →
  (∀ c, G v c = false → (C.wires (col c)).getD (s v) false = true) →
  ∃ j : Fin C.gates.length, s v = wire j ∧
    ∀ w, j ≠ r w ∧ wire (r w) ∉ (gate j.val).inputs) := by
  intro n m G C r s v gate wire reads col hM hRB hRep hout hmiss hinc hrow hcard hon
  exact PEqualNP.Outside.L_meta_25490_aux.main n m G C r s v hM hRB hRep hout hmiss hinc hrow hcard hon
