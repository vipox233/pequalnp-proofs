import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20608

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem getD_snoc {α : Type} (L : List α) (a d : α) (w : ℕ) :
    (L ++ [a]).getD w d = if w < L.length then L.getD w d else if w = L.length then a else d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_append_right (by omega)]
    rw [List.getElem?_eq_none (by simp; omega)]; simp

def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def dstep (D : List (Finset ℕ)) (g : Gate) : List (Finset ℕ) :=
  D ++ [g.inputs.toFinset.biUnion fun i => D.getD i ∅]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl wstep x := rfl

theorem sem (P : ℕ → Prop) : ∀ (gs : List Gate) (W1 W2 : List Bool) (D : List (Finset ℕ)),
    W1.length = D.length → W2.length = D.length →
    (∀ w, (∀ i ∈ D.getD w ∅, P i) → W1.getD w false = W2.getD w false) →
    ∀ w, (∀ i ∈ (gs.foldl dstep D).getD w ∅, P i) →
      (gs.foldl wstep W1).getD w false = (gs.foldl wstep W2).getD w false := by
  intro gs
  induction gs with
  | nil => intro W1 W2 D _ _ h; simpa using h
  | cons g gs ih =>
    intro W1 W2 D h1 h2 h
    simp only [List.foldl_cons]
    apply ih
    · simp [wstep, dstep, h1]
    · simp [wstep, dstep, h2]
    · intro w hw
      simp only [wstep, dstep] at hw ⊢
      rw [getD_snoc, getD_snoc]
      rw [getD_snoc] at hw
      rw [h1, h2]
      split_ifs with c1 c2
      · rw [ite_eq_left c1] at hw; exact h w hw
      · rw [ite_eq_right c1, ite_eq_left c2] at hw
        congr 1
        apply List.map_congr_left
        intro j hj
        apply h j
        intro i hi
        apply hw
        rw [Finset.mem_biUnion]
        exact ⟨j, List.mem_toFinset.mpr hj, hi⟩
      · rfl

theorem cardb : ∀ (gs : List Gate) (D : List (Finset ℕ)) (k : ℕ),
    (∀ g ∈ gs, g.inputs.length ≤ 2) →
    (∀ T : Finset ℕ, (T.biUnion fun w => D.getD w ∅).card ≤ T.card + k) →
    ∀ T : Finset ℕ, (T.biUnion fun w => (gs.foldl dstep D).getD w ∅).card ≤
      T.card + k + gs.length := by
  intro gs
  induction gs with
  | nil => intro D k _ h T; simpa using h T
  | cons g gs ih =>
    intro D k hg h T
    simp only [List.foldl_cons, List.length_cons]
    have := ih (dstep D g) (k + 1) (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) ?_ T
    · omega
    intro T
    have hsub : (T.biUnion fun w => (dstep D g).getD w ∅) ⊆
        ((T.erase D.length) ∪ g.inputs.toFinset).biUnion fun w => D.getD w ∅ := by
      intro i hi
      rw [Finset.mem_biUnion] at hi
      obtain ⟨w, hw, hi⟩ := hi
      simp only [dstep] at hi
      rw [getD_snoc] at hi
      rw [Finset.mem_biUnion]
      split_ifs at hi with c1 c2
      · exact ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by omega, hw⟩), hi⟩
      · rw [Finset.mem_biUnion] at hi
        obtain ⟨j, hj, hi⟩ := hi
        exact ⟨j, Finset.mem_union_right _ hj, hi⟩
      · simp at hi
    have hc := h ((T.erase D.length) ∪ g.inputs.toFinset)
    have h3 := Finset.card_union_le (T.erase D.length) g.inputs.toFinset
    have h4 := List.toFinset_card_le g.inputs
    have h5 := hg g List.mem_cons_self
    have h6 := Finset.card_le_card hsub
    by_cases hm : D.length ∈ T
    · have h7 := Finset.card_erase_of_mem hm
      have h8 : 1 ≤ T.card := Finset.card_pos.mpr ⟨_, hm⟩
      omega
    · have h9 : (T.biUnion fun w => (dstep D g).getD w ∅) =
          T.biUnion fun w => D.getD w ∅ := by
        apply Finset.biUnion_congr rfl
        intro w hw
        simp only [dstep]
        rw [getD_snoc]
        have : w ≠ D.length := fun e => hm (e ▸ hw)
        split_ifs with c1
        · rfl
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
      rw [h9]; have := h T; omega

theorem base_card (n : ℕ) (T : Finset ℕ) :
    (T.biUnion fun w => ((List.range n).map fun i => ({i} : Finset ℕ)).getD w ∅).card ≤
      T.card + 0 := by
  refine le_trans Finset.card_biUnion_le ?_
  rw [Nat.add_zero]
  calc (∑ w ∈ T, (((List.range n).map fun i => ({i} : Finset ℕ)).getD w ∅).card)
      ≤ ∑ w ∈ T, 1 := by
        apply Finset.sum_le_sum
        intro w _
        rw [List.getD_eq_getElem?_getD]
        by_cases hw : w < n
        · simp [hw]
        · rw [List.getElem?_eq_none (by simp; omega)]; simp
    _ = T.card := by simp

def depS (n : ℕ) (C : Circuit) : Finset ℕ :=
  (C.gates.foldl dstep ((List.range n).map fun j => ({j} : Finset ℕ))).getD C.output ∅

theorem depS_card (n : ℕ) (C : Circuit) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    (depS n C).card ≤ C.size + 1 := by
  have hc := cardb C.gates ((List.range n).map fun j => ({j} : Finset ℕ)) 0 hfan (base_card n)
    {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton] at hc
  unfold depS PEqualNP.CircuitLowerBounds.Circuit.size
  omega

theorem dep (C : Circuit) (n i : ℕ) (x y : List Bool) (hx : x.length = n) (hy : y.length = n)
    (hxy : ∀ j, j ≠ i → x.getD j false = y.getD j false) (hi : i ∉ depS n C) :
    C.eval x = C.eval y := by
  have key := sem (fun j => x.getD j false = y.getD j false) C.gates x y
    ((List.range n).map fun j => ({j} : Finset ℕ)) (by simp [hx]) (by simp [hy]) ?_ C.output ?_
  · unfold PEqualNP.CircuitLowerBounds.Circuit.eval
    rw [wires_eq, wires_eq]; exact key
  · intro w hw
    by_cases hwn : w < n
    · apply hw w
      simp [List.getD_eq_getElem?_getD, hwn]
    · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  · intro j hj
    have hji : j ≠ i := fun e => hi (by unfold depS; exact e ▸ hj)
    exact hxy j hji

theorem all_mono (l : List ℕ) (f g : ℕ → Bool) (h : ∀ i, f i = true → g i = true) :
    (l.map f).all id = true → (l.map g).all id = true := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.all_cons, Bool.and_eq_true, id]
    exact fun ⟨h1, h2⟩ => ⟨h a h1, ih h2⟩

theorem any_mono (l : List ℕ) (f g : ℕ → Bool) (h : ∀ i, f i = true → g i = true) :
    (l.map f).any id = true → (l.map g).any id = true := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.any_cons, Bool.or_eq_true, id]
    rintro (h1 | h2)
    · exact Or.inl (h a h1)
    · exact Or.inr (ih h2)

theorem mono : ∀ (gs : List Gate) (W1 W2 : List Bool),
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) → W1.length = W2.length →
    (∀ w, W1.getD w false = true → W2.getD w false = true) →
    ∀ w, (gs.foldl wstep W1).getD w false = true → (gs.foldl wstep W2).getD w false = true := by
  intro gs
  induction gs with
  | nil => intro W1 W2 _ _ h; simpa using h
  | cons g gs ih =>
    intro W1 W2 hop hl h
    simp only [List.foldl_cons]
    apply ih
    · exact fun g' hg' => hop g' (List.mem_cons_of_mem _ hg')
    · simp [wstep, hl]
    · intro w hw
      simp only [wstep] at hw ⊢
      rw [getD_snoc] at hw
      rw [getD_snoc, ← hl]
      by_cases c1 : w < W1.length
      · rw [ite_eq_left c1] at hw ⊢; exact h w hw
      · rw [ite_eq_right c1] at hw ⊢
        by_cases c2 : w = W1.length
        · rw [ite_eq_left c2] at hw ⊢
          rcases hop g List.mem_cons_self with e | e
          · rw [e] at hw ⊢
            exact all_mono _ _ _ h hw
          · rw [e] at hw ⊢
            exact any_mono _ _ _ h hw
        · rw [ite_eq_right c2] at hw; exact absurd hw (by decide)

theorem evmono (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C) (x y : List Bool)
    (hl : x.length = y.length) (h : ∀ w, x.getD w false = true → y.getD w false = true) :
    C.eval x = true → C.eval y = true := by
  have hop : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have := (hm g hg).1
    simpa using this
  unfold PEqualNP.CircuitLowerBounds.Circuit.eval
  rw [wires_eq, wires_eq]
  exact mono C.gates x y hop hl h C.output

private theorem oneEach_left {n : ℕ} (u v : Fin n) (k : ℕ) (hk : k < n) :
    (oneEach u v).getD k false = decide (k = u.val) := by
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_left
    (by simpa using hk : k < (List.ofFn (fun a : Fin n => decide (a = u))).length),
    List.getElem?_ofFn, dite_eq_left hk, Option.getD_some]
  simp [Fin.ext_iff]

private theorem oneEach_right {n : ℕ} (u v : Fin n) (k : ℕ) (hk : k < n) :
    (oneEach u v).getD (n + k) false = decide (k = v.val) := by
  have hl : (List.ofFn (fun a : Fin n => decide (a = u))).length = n := by simp
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_right
    (by omega : (List.ofFn (fun a : Fin n => decide (a = u))).length ≤ n+k),
    hl, Nat.add_sub_cancel_left, List.getElem?_ofFn, dite_eq_left hk, Option.getD_some]
  simp [Fin.ext_iff]

private theorem oneEach_on {n : ℕ} (u v : Fin n) (w : ℕ) :
    (oneEach u v).getD w false = true ↔ w = u.val ∨ w = n + v.val := by
  by_cases h : w < n
  · rw [oneEach_left u v w h]
    simp only [decide_eq_true_eq]
    omega
  · by_cases b : w < n+n
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (by omega : n ≤ w)
      rw [oneEach_right u v k (by omega)]
      simp only [decide_eq_true_eq]
      have := u.isLt
      omega
    · rw [List.getD_eq_default _ _ (by simp [oneEach]; omega)]
      have := u.isLt
      have := v.isLt
      have ha : w ≠ u.val := by omega
      have hb : w ≠ n + v.val := by omega
      simp [ha, hb]

private theorem mustDepend {m a b : ℕ} (C : Circuit) (hm : Monotone2 C)
    (x z : List Bool) (hx : x.length = m) (hz : z.length = m) (hb : b < m)
    (hxv : ∀ w, x.getD w false = true ↔ w = a ∨ w = b)
    (hzb : z.getD b false = true) (ex : C.eval x = true) (ez : C.eval z = false) :
    a ∈ depS m C := by
  by_contra ha
  let y := List.ofFn (fun k : Fin m => decide (k.val = b))
  have hy : y.length = m := by simp [y]
  have hyv (w : ℕ) : y.getD w false = true ↔ w = b := by
    by_cases hw : w < m
    · simp [y, List.getD_eq_getElem?_getD, hw]
    · rw [List.getD_eq_default _ _ (by omega)]
      simp [show w ≠ b by omega]
  have e := dep C m a x y hx hy (by
    intro w hw
    apply Bool.eq_iff_iff.mpr
    rw [hxv, hyv]
    simp [hw]) ha
  have ey : C.eval y = true := e ▸ ex
  have := evmono C hm y z (hy.trans hz.symm) (by
    intro w hw
    exact (hyv w |>.mp hw) ▸ hzb) ey
  simp [ez] at this

private def A : Fin 5 → Fin 5 → Bool :=
  fun u v => (31490048 : ℕ).testBit (5 * u.val + v.val)

private def witness : Circuit :=
  ⟨[⟨.and, [3, 5]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [11, 8]⟩,
    ⟨.or, [12, 9]⟩, ⟨.and, [4, 13]⟩, ⟨.or, [10, 14]⟩], 15⟩

private theorem upper : RepSizeAtMost A 6 := by
  refine ⟨witness, ?_, by decide +kernel, by decide +kernel⟩
  simp [Monotone2, witness]

private def needed : Fin 7 → ℕ := ![3, 4, 5, 6, 7, 8, 9]
private def other : Fin 7 → ℕ := ![5, 6, 3, 4, 4, 4, 4]
private def posRow : Fin 7 → Fin 5 := ![3, 4, 3, 4, 4, 4, 4]
private def posCol : Fin 7 → Fin 5 := ![0, 1, 0, 1, 2, 3, 4]
private def negRow : Fin 7 → Fin 5 := ![0, 0, 3, 4, 4, 4, 4]
private def negCol : Fin 7 → Fin 5 := ![0, 1, 1, 0, 0, 0, 0]

private theorem certificates : ∀ k : Fin 7,
    other k < 10 ∧
    ((needed k = (posRow k).val ∧ other k = 5 + (posCol k).val) ∨
      (needed k = 5 + (posCol k).val ∧ other k = (posRow k).val)) ∧
    (oneEach (negRow k) (negCol k)).getD (other k) false = true ∧
    A (posRow k) (posCol k) = true ∧ A (negRow k) (negCol k) = false := by
  decide +kernel

private theorem floorBound (C : Circuit) (hm : Monotone2 C) (hr : Represents A C) :
    6 ≤ C.size := by
  have essential (k : Fin 7) : needed k ∈ depS 10 C := by
    rcases certificates k with ⟨hb, hp, hz, hpos, hneg⟩
    apply mustDepend (a := needed k) (b := other k) C hm
      (oneEach (posRow k) (posCol k)) (oneEach (negRow k) (negCol k))
      (by simp [oneEach]) (by simp [oneEach]) hb
    · intro w
      rw [oneEach_on]
      rcases hp with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · rw [← ha, ← hb]
      · rw [← hb, ← ha, or_comm]
    · exact hz
    · exact (hr _ _).trans hpos
    · exact (hr _ _).trans hneg
  have sub : Finset.univ.image needed ⊆ depS 10 C := by
    intro a ha
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp ha
    exact essential k
  have count : (Finset.univ.image needed).card = 7 := by decide +kernel
  have hc := Finset.card_le_card sub
  have bound := depS_card 10 C (fun g hg => (hm g hg).2)
  omega

end PEqualNP.Outside.L_meta_20608

open PEqualNP.Outside.L_meta_20608 in
theorem PEqualNP.Outside.L_meta_20608 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (31490048 : ℕ).testBit (5 * u.val + v.val)) 6 ∧ ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (31490048 : ℕ).testBit (5 * u.val + v.val)) 5) := by
  refine ⟨upper, ?_⟩
  rintro ⟨C, hm, hs, hr⟩
  have h := floorBound C hm hr
  omega
