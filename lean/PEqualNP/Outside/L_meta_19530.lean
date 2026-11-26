import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19530

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def gateSupp (L : List (Finset ℕ)) (g : Gate) : Finset ℕ :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset ℕ) (i : ℕ) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp (L : List (Finset ℕ)) (g : Gate) (i : ℕ) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom (gs : List Gate) (L : List (Finset ℕ)) : List (Finset ℕ) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (m : ℕ) : List (Finset ℕ) := List.ofFn fun i : Fin m => {(i : ℕ)}

theorem gate_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (idxs : List ℕ) (f1 f2 : ℕ → Bool)
    (h : ∀ a ∈ idxs, f1 a = true → f2 a = true) :
    op.eval (idxs.map f1) = true → op.eval (idxs.map f2) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    intro h1 b hb
    rcases hb with ⟨a, ha, rfl⟩
    exact h a ha (h1 (f1 a) ⟨a, ha, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    intro h1
    rcases h1 with ⟨b, ⟨a, ha, rfl⟩, hb⟩
    exact ⟨f2 a, ⟨a, ha, rfl⟩, h a ha hb⟩

def MonoRel (x y : List Bool) (L : List (Finset ℕ)) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x.getD i false = true → y.getD i false = true) →
      w.getD j false = true → w'.getD j false = true

theorem mono_wiresFrom (x y : List Bool) (gs : List Gate) :
    ∀ (L : List (Finset ℕ)) (w w' : List Bool),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) →
      MonoRel x y L w w' →
      MonoRel x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' _ h; exact h
  | cons g gs ih =>
    intro L w w' hmono h
    obtain ⟨h1, h2, h3⟩ := h
    have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmono g List.mem_cons_self
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
      (fun g' hg' => hmono g' (List.mem_cons_of_mem _ hg'))
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      exact gate_mono g.op hop g.inputs (fun i => w.getD i false) (fun i => w'.getD i false)
        (fun a ha => h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩)))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem mono_inputs (x y : List Bool) (m : ℕ) (hx : x.length = m) (hy : y.length = m) :
    MonoRel x y (inputSupps m) x y := by
  refine ⟨by simp [inputSupps, hx], by omega, ?_⟩
  intro j hj
  by_cases hjm : j < m
  · exact hj j (by simp [inputSupps, hjm])
  · rw [List.getD_eq_default _ _ (by omega)]
    intro hfalse
    cases hfalse

def Cnt (t : ℕ) (L : List (Finset ℕ)) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs (m : ℕ) : Cnt 0 (inputSupps m) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjm : j < m
  · simp [inputSupps, hjm]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]
    simp

theorem cnt_step (t : ℕ) (L : List (Finset ℕ)) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have h1 := h (W.erase L.length ∪ g.inputs.toFinset)
    have h2 := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have h1 := h W
    omega

theorem cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset ℕ)),
    (∀ g ∈ gs, g.inputs.length ≤ 2) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have h1 := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self) h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact h1

theorem oneEach_length {n : ℕ} (u v : Fin n) : (oneEach u v).length = 2 * n := by
  simp [oneEach]
  omega

theorem getD_oneEach_left {n : ℕ} (u v : Fin n) (k : ℕ) (hk : k < n) :
    (oneEach u v).getD k false = decide (k = u.val) := by
  rw [oneEach, List.getD_append _ _ _ _ (by simp [hk])]
  simp [hk, Fin.ext_iff]

theorem getD_oneEach_right {n : ℕ} (u v : Fin n) (k : ℕ) (h1 : n ≤ k) (h2 : k < 2 * n) :
    (oneEach u v).getD k false = decide (k - n = v.val) := by
  rw [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
  simp [show k - n < n by omega, Fin.ext_iff]

theorem getD_oneEach_hi {n : ℕ} (u v : Fin n) (k : ℕ) (hk : 2 * n ≤ k) :
    (oneEach u v).getD k false = false := by
  rw [List.getD_eq_default _ _ (by rw [oneEach_length]; exact hk)]

theorem main : ∀ n : ℕ, 3 ≤ n → ∀ s : ℕ,
    RepSizeAtMost (fun u v : Fin n => decide ((u : ℕ) = 0 ∨ (v : ℕ) = 0 ∨ ((u : ℕ) ≠ n - 1 ∧ (v : ℕ) ≠ n - 1))) s →
    2 * n - 3 ≤ s := by
  intro n hn s hrep
  obtain ⟨C, hmono, hsz, hev⟩ := hrep
  set S := (suppsFrom C.gates (inputSupps (2 * n))).getD C.output ∅ with hS
  set T := Finset.range (n - 1) ∪ (Finset.range (n - 1)).image (fun v => n + v) with hT
  have hsub : T ⊆ S := by
    intro w hw
    rcases Finset.mem_union.1 hw with hwL | hwR
    · rw [Finset.mem_range] at hwL
      by_contra hwS
      let u : Fin n := ⟨w, by omega⟩
      let uLast : Fin n := ⟨n - 1, by omega⟩
      let v1 : Fin n := ⟨1, by omega⟩
      have hag := (mono_wiresFrom (oneEach u v1) (oneEach uLast v1) C.gates
        (inputSupps (2 * n)) (oneEach u v1) (oneEach uLast v1)
        (fun g hg => (hmono g hg).1)
        (mono_inputs _ _ (2 * n) (oneEach_length u v1) (oneEach_length uLast v1))).2.2 C.output
      have harg : ∀ i ∈ S, (oneEach u v1).getD i false = true →
          (oneEach uLast v1).getD i false = true := by
        intro i hiS
        have hiw : i ≠ w := fun e => hwS (e ▸ hiS)
        by_cases h1 : i < n
        · rw [getD_oneEach_left u v1 i h1, getD_oneEach_left uLast v1 i h1]
          simp only [decide_eq_true_eq]
          intro heq
          exfalso
          exact hiw heq
        · by_cases h2 : i < 2 * n
          · rw [getD_oneEach_right u v1 i (by omega) h2, getD_oneEach_right uLast v1 i (by omega) h2]
            exact id
          · rw [getD_oneEach_hi u v1 i (by omega)]
            intro hfalse
            cases hfalse
      have hEvalU : C.eval (oneEach u v1) = true := by
        rw [hev u v1]
        simp [u, v1]
        omega
      have hEvalLast : C.eval (oneEach uLast v1) = true := hag harg hEvalU
      rw [hev uLast v1] at hEvalLast
      simp [uLast, v1] at hEvalLast
      omega
    · rw [Finset.mem_image] at hwR
      rcases hwR with ⟨v, hvR, rfl⟩
      rw [Finset.mem_range] at hvR
      by_contra hwS
      let u1 : Fin n := ⟨1, by omega⟩
      let vFin : Fin n := ⟨v, by omega⟩
      let vLast : Fin n := ⟨n - 1, by omega⟩
      have hag := (mono_wiresFrom (oneEach u1 vFin) (oneEach u1 vLast) C.gates
        (inputSupps (2 * n)) (oneEach u1 vFin) (oneEach u1 vLast)
        (fun g hg => (hmono g hg).1)
        (mono_inputs _ _ (2 * n) (oneEach_length u1 vFin) (oneEach_length u1 vLast))).2.2 C.output
      have harg : ∀ i ∈ S, (oneEach u1 vFin).getD i false = true →
          (oneEach u1 vLast).getD i false = true := by
        intro i hiS
        have hiv : i ≠ n + v := fun e => hwS (e ▸ hiS)
        by_cases h1 : i < n
        · rw [getD_oneEach_left u1 vFin i h1, getD_oneEach_left u1 vLast i h1]
          exact id
        · by_cases h2 : i < 2 * n
          · rw [getD_oneEach_right u1 vFin i (by omega) h2, getD_oneEach_right u1 vLast i (by omega) h2]
            simp only [decide_eq_true_eq]
            intro heq
            exfalso
            apply hiv
            change i - n = v at heq
            omega
          · rw [getD_oneEach_hi u1 vFin i (by omega)]
            intro hfalse
            cases hfalse
      have hEvalV : C.eval (oneEach u1 vFin) = true := by
        rw [hev u1 vFin]
        simp [u1, vFin]
        omega
      have hEvalLast : C.eval (oneEach u1 vLast) = true := hag harg hEvalV
      rw [hev u1 vLast] at hEvalLast
      simp [u1, vLast] at hEvalLast
      omega
  have hdisj : Disjoint (Finset.range (n - 1)) ((Finset.range (n - 1)).image (fun v => n + v)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_range] at hx1
    rw [Finset.mem_image] at hx2
    rcases hx2 with ⟨v, _, rfl⟩
    omega
  have hT_card : T.card = 2 * (n - 1) := by
    rw [hT, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ (fun a b h => by omega),
      Finset.card_range]
    omega
  have hc := cnt_suppsFrom C.gates 0 (inputSupps (2 * n)) (fun g hg => (hmono g hg).2) (cnt_inputs (2 * n)) {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS] at hc
  have hle : T.card ≤ S.card := Finset.card_le_card hsub
  have hsz' : C.gates.length ≤ s := hsz
  omega

end PEqualNP.Outside.L_meta_19530

theorem PEqualNP.Outside.L_meta_19530 : (∀ n : ℕ, 3 ≤ n → ∀ s : ℕ, PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide ((u : ℕ) = 0 ∨ (v : ℕ) = 0 ∨ ((u : ℕ) ≠ n - 1 ∧ (v : ℕ) ≠ n - 1))) s → 2 * n - 3 ≤ s) :=
  PEqualNP.Outside.L_meta_19530.main
