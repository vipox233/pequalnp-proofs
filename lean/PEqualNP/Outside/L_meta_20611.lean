import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20611_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def A : Fin 5 → Fin 5 → Bool :=
  fun u v => (12649504 : ℕ).testBit (5 * u.val + v.val)

def C_ : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.and, [10, 5]⟩, ⟨.and, [3, 6]⟩, ⟨.or, [7, 8]⟩, ⟨.and, [4, 13]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [15, 14]⟩], 16⟩

def monoTwoB (C : Circuit) : Bool :=
  C.gates.all fun g =>
    (match g.op with | GateOp.and => true | GateOp.or => true | _ => false) &&
    Nat.ble g.inputs.length 2

theorem monoTwoB_sound (C : Circuit) (h : monoTwoB C = true) : Monotone2 C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, Nat.ble_eq] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp [hop] at h1 ⊢

theorem upper : RepSizeAtMost A 7 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

def evalStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def needStep (m : ℕ) (g : Gate) (S : Finset ℕ) : Finset ℕ :=
  if m ∈ S then (S.erase m) ∪ (g.inputs.toFinset.filter (· < m)) else S

def needWires : List Gate → ℕ → Finset ℕ → Finset ℕ
  | [], _, S => S
  | g :: gs, m, S => needStep m g (needWires gs (m + 1) S)

theorem needStep_card (m : ℕ) (g : Gate) (hg : g.inputs.length ≤ 2) (S : Finset ℕ) :
    (needStep m g S).card ≤ S.card + 1 := by
  unfold needStep
  split_ifs with hm
  · have h1 : (S.erase m).card + 1 = S.card := Finset.card_erase_add_one hm
    have h2 : (g.inputs.toFinset.filter (· < m)).card ≤ 2 :=
      (Finset.card_filter_le _ _).trans ((List.toFinset_card_le g.inputs).trans hg)
    have h3 := Finset.card_union_le (S.erase m) (g.inputs.toFinset.filter (· < m))
    omega
  · omega

theorem needWires_card (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∀ m S, (needWires gs m S).card ≤ S.card + gs.length := by
  induction gs with
  | nil => intro m S; simp [needWires]
  | cons g gs ih =>
    intro m S
    simp only [needWires, List.length_cons]
    have h1 := needStep_card m g (hg g (by simp)) (needWires gs (m + 1) S)
    have h2 := ih (fun g' h' => hg g' (List.mem_cons_of_mem _ h')) (m + 1) S
    omega

theorem op_mono (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (x y : List Bool) (h : ∀ j ∈ g.inputs, x.getD j false = true → y.getD j false = true) :
    g.op.eval (g.inputs.map fun i => x.getD i false) = true →
    g.op.eval (g.inputs.map fun i => y.getD i false) = true := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hop | hop <;> rw [hop]
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id]
    intro hx j hj
    exact h j hj (hx j hj)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
    rintro ⟨j, hj, hv⟩
    exact ⟨j, hj, h j hj hv⟩

theorem getD_snoc_lt (w : List Bool) (b : Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ [b]).getD i false = w.getD i false :=
  List.getD_append w [b] false i hi

theorem getD_snoc_eq (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp

theorem getD_ge_false (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false :=
  List.getD_eq_default w false hi

theorem needWires_mono (gs : List Gate)
    (hop : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    ∀ m S (x y : List Bool), x.length = m → y.length = m →
      (∀ i ∈ needWires gs m S, i < m → x.getD i false = true → y.getD i false = true) →
      ∀ o ∈ S, (gs.foldl evalStep x).getD o false = true →
        (gs.foldl evalStep y).getD o false = true := by
  induction gs with
  | nil =>
    intro m S x y hx hy hxy o ho hxo
    simp only [List.foldl_nil] at hxo ⊢
    by_cases hlt : o < m
    · exact hxy o ho hlt hxo
    · rw [getD_ge_false x o (by omega)] at hxo
      contradiction
  | cons g gs ih =>
    intro m S x y hx hy hxy o ho
    simp only [List.foldl_cons]
    apply ih (fun g' h' => hop g' (List.mem_cons_of_mem _ h')) (m + 1) S
      (evalStep x g) (evalStep y g)
      (by simp [evalStep, hx]) (by simp [evalStep, hy])
    · intro i hi hilt hxi
      by_cases hlt : i < m
      · have hmem : i ∈ needStep m g (needWires gs (m + 1) S) := by
          unfold needStep
          split_ifs with hm
          · exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨by omega, hi⟩)
          · exact hi
        rw [evalStep, getD_snoc_lt x _ i (by omega)] at hxi
        rw [evalStep, getD_snoc_lt y _ i (by omega)]
        exact hxy i hmem hlt hxi
      · have heq : i = m := by omega
        subst i
        have hmem_m : m ∈ needWires gs (m + 1) S := hi
        rw [evalStep, ← hx, getD_snoc_eq] at hxi
        rw [evalStep, ← hy, getD_snoc_eq]
        apply op_mono g (hop g (by simp)) x y _ hxi
        intro j hj hxj
        have hjlt : j < m := by
          by_contra hge
          rw [getD_ge_false x j (by omega)] at hxj
          contradiction
        have hjmem : j ∈ needStep m g (needWires gs (m + 1) S) := by
          unfold needStep
          simp only [hmem_m, ite_true]
          exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨List.mem_toFinset.2 hj, hjlt⟩)
        exact hxy j hjmem hjlt hxj
    · exact ho

theorem oneEach_len (u v : Fin 5) : (oneEach u v).length = 10 := by
  simp [oneEach]

theorem oneEach_getD (u v : Fin 5) (i : ℕ) (hi : i < 10) :
    (oneEach u v).getD i false = true ↔ i = u.val ∨ i = 5 + v.val := by
  revert u v i hi
  decide +kernel

theorem req_left (C : Circuit) (hM : Monotone2 C) (hR : Represents A C)
    (u u' v : Fin 5) (h1 : A u v = true) (h0 : A u' v = false) :
    u.val ∈ needWires C.gates 10 {C.output} := by
  by_contra hnot
  have hmono := needWires_mono C.gates (fun g hg => (hM g hg).1) 10 {C.output}
    (oneEach u v) (oneEach u' v) (oneEach_len u v) (oneEach_len u' v)
  have hle : ∀ i ∈ needWires C.gates 10 {C.output}, i < 10 →
      (oneEach u v).getD i false = true → (oneEach u' v).getD i false = true := by
    intro i hi hilt hxi
    have hcase := (oneEach_getD u v i hilt).1 hxi
    rcases hcase with rfl | rfl
    · exact (hnot hi).elim
    · exact (oneEach_getD u' v (5 + v.val) hilt).2 (Or.inr rfl)
  have hev : C.eval (oneEach u' v) = true := hmono hle C.output (by simp) (by change C.eval (oneEach u v) = true; rw [hR u v]; exact h1)
  rw [hR u' v, h0] at hev
  contradiction

theorem req_right (C : Circuit) (hM : Monotone2 C) (hR : Represents A C)
    (u v v' : Fin 5) (h1 : A u v = true) (h0 : A u v' = false) :
    5 + v.val ∈ needWires C.gates 10 {C.output} := by
  by_contra hnot
  have hmono := needWires_mono C.gates (fun g hg => (hM g hg).1) 10 {C.output}
    (oneEach u v) (oneEach u v') (oneEach_len u v) (oneEach_len u v')
  have hle : ∀ i ∈ needWires C.gates 10 {C.output}, i < 10 →
      (oneEach u v).getD i false = true → (oneEach u v').getD i false = true := by
    intro i hi hilt hxi
    have hcase := (oneEach_getD u v i hilt).1 hxi
    rcases hcase with rfl | rfl
    · exact (oneEach_getD u v' u.val hilt).2 (Or.inl rfl)
    · exact (hnot hi).elim
  have hev : C.eval (oneEach u v') = true := hmono hle C.output (by simp) (by change C.eval (oneEach u v) = true; rw [hR u v]; exact h1)
  rw [hR u v', h0] at hev
  contradiction

theorem lower : ¬ RepSizeAtMost A 6 := by
  rintro ⟨C, hM, hS, hR⟩
  have hcard : (needWires C.gates 10 {C.output}).card ≤ 7 := by
    have h1 := needWires_card C.gates (fun g hg => (hM g hg).2) 10 {C.output}
    simp only [Finset.card_singleton] at h1
    change C.gates.length ≤ 6 at hS
    omega
  have hsub : ({1, 2, 3, 4, 5, 6, 7, 8} : Finset ℕ) ⊆ needWires C.gates 10 {C.output} := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact req_left C hM hR 1 0 0 (by decide) (by decide)
    · exact req_left C hM hR 2 0 0 (by decide) (by decide)
    · exact req_left C hM hR 3 0 1 (by decide) (by decide)
    · exact req_left C hM hR 4 0 2 (by decide) (by decide)
    · exact req_right C hM hR 1 0 1 (by decide) (by decide)
    · exact req_right C hM hR 3 1 0 (by decide) (by decide)
    · exact req_right C hM hR 4 2 0 (by decide) (by decide)
    · exact req_right C hM hR 4 3 0 (by decide) (by decide)
  have h8 : 8 ≤ (needWires C.gates 10 {C.output}).card := by
    have hle := Finset.card_le_card hsub
    simpa using hle
  omega

theorem main : RepSizeAtMost A 7 ∧ ¬ RepSizeAtMost A 6 :=
  ⟨upper, lower⟩

end PEqualNP.Outside.L_meta_20611_aux

theorem PEqualNP.Outside.L_meta_20611 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (12649504 : ℕ).testBit (5 * u.val + v.val)) 7 ∧ ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (12649504 : ℕ).testBit (5 * u.val + v.val)) 6 :=
  PEqualNP.Outside.L_meta_20611_aux.main
