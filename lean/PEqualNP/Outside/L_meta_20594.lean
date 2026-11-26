import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20594_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (x : List Bool) : List Bool := gs.foldl stp x

def Good (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = stp (W gs x) g := by simp [W]

theorem W_len (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc, stp]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (i : ℕ) (h : i < l.length) :
    (l ++ [b]).getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_len (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_big (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem mono (gs : List Gate) : (∀ g ∈ gs, Good g) → ∀ x y : List Bool, x.length = y.length →
    (∀ i, x.getD i false = true → y.getD i false = true) →
    ∀ i, (W gs x).getD i false = true → (W gs y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => intro _ x y _ h i hi; exact h i hi
  | append_singleton gs g ih =>
    intro hg x y hxy h i hi
    have IH := ih (fun g' h => hg g' (by simp [h])) x y hxy h
    have hgg : Good g := hg g (by simp)
    have hL : (W gs x).length = (W gs y).length := by rw [W_len, W_len, hxy]
    rw [W_snoc, stp] at hi ⊢
    rcases lt_trichotomy i (W gs x).length with h1 | h1 | h1
    · rw [getD_lt _ _ _ h1] at hi
      rw [getD_lt _ _ _ (hL ▸ h1)]
      exact IH i hi
    · rw [h1, getD_len] at hi
      rw [h1, hL, getD_len]
      rcases hgg.1 with ho | ho
      · rw [ho] at hi ⊢
        simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at hi ⊢
        exact fun j hj => IH j (hi j hj)
      · rw [ho] at hi ⊢
        simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at hi ⊢
        obtain ⟨j, hj, hj'⟩ := hi
        exact ⟨j, hj, IH j hj'⟩
    · rw [getD_big _ _ (by simp; omega)] at hi
      exact absurd hi (by simp)

def ro (v : Fin 5) : List Bool := List.replicate 5 false ++ List.ofFn (fun j : Fin 5 => decide (j = v))
def lo (u : Fin 5) : List Bool := List.ofFn (fun j : Fin 5 => decide (j = u)) ++ List.replicate 5 false

theorem agree1 : ∀ (u : Fin 5) (v : Fin 5), ∀ i < 10, i ≠ (u : ℕ) →
    (oneEach u v).getD i false = (ro v).getD i false := by decide +kernel
theorem agree2 : ∀ (u : Fin 5) (v : Fin 5), ∀ i < 10, i ≠ 5 + (v : ℕ) →
    (oneEach u v).getD i false = (lo u).getD i false := by decide +kernel
theorem below1 : ∀ (u : Fin 5) (v : Fin 5), ∀ i < 10, (ro v).getD i false = true →
    (oneEach u v).getD i false = true := by decide +kernel
theorem below2 : ∀ (u : Fin 5) (v : Fin 5), ∀ i < 10, (lo u).getD i false = true →
    (oneEach u v).getD i false = true := by decide +kernel
theorem oe_len : ∀ (u : Fin 5) (v : Fin 5), (oneEach u v).length = 10 := by decide +kernel
theorem ro_len : ∀ v : Fin 5, (ro v).length = 10 := by decide +kernel
theorem lo_len : ∀ v : Fin 5, (lo v).length = 10 := by decide +kernel

theorem below_of (x y : List Bool) (hx : x.length = 10)
    (h : ∀ i < 10, x.getD i false = true → y.getD i false = true) :
    ∀ i, x.getD i false = true → y.getD i false = true := by
  intro i hi
  by_cases h8 : i < 10
  · exact h i h8 hi
  · rw [getD_big _ _ (by omega)] at hi; exact absurd hi (by simp)

theorem row_in (C : Circuit) (hC : ∀ g ∈ C.gates, Good g) (A : Fin 5 → Fin 5 → Bool)
    (hrep : Represents A C) (D : Finset ℕ) (hD8 : D ⊆ Finset.range 10)
    (hD : ∀ x y : List Bool, x.length = 10 → y.length = 10 →
      (∀ i ∈ D, x.getD i false = y.getD i false) → C.eval x = C.eval y) (u : Fin 5)
    (hu : (u : ℕ) ∉ D) : ∀ u' v, A u v = true → A u' v = true := by
  intro u' v h
  rw [← hrep u v, hD (oneEach u v) (ro v) (oe_len u v) (ro_len v) (fun i hi =>
    agree1 u v i (by simpa using hD8 hi) (fun h => hu (h ▸ hi)))] at h
  rw [← hrep u' v]
  exact mono C.gates hC (ro v) (oneEach u' v) (by rw [ro_len, oe_len])
    (below_of _ _ (ro_len v) (below1 u' v)) C.output h

theorem col_in (C : Circuit) (hC : ∀ g ∈ C.gates, Good g) (A : Fin 5 → Fin 5 → Bool)
    (hrep : Represents A C) (D : Finset ℕ) (hD8 : D ⊆ Finset.range 10)
    (hD : ∀ x y : List Bool, x.length = 10 → y.length = 10 →
      (∀ i ∈ D, x.getD i false = y.getD i false) → C.eval x = C.eval y) (v : Fin 5)
    (hv : 5 + (v : ℕ) ∉ D) : ∀ v' u, A u v = true → A u v' = true := by
  intro v' u h
  rw [← hrep u v, hD (oneEach u v) (lo u) (oe_len u v) (lo_len u) (fun i hi =>
    agree2 u v i (by simpa using hD8 hi) (fun h => hv (h ▸ hi)))] at h
  rw [← hrep u v']
  exact mono C.gates hC (lo u) (oneEach u v') (by rw [lo_len, oe_len])
    (below_of _ _ (lo_len u) (below2 u v')) C.output h

theorem support (gs : List Gate) (hgood : ∀ g ∈ gs, Good g) (S : Finset ℕ)
    (hS : ∀ i ∈ S, i < 10 + gs.length) :
    ∃ D : Finset ℕ, D ⊆ Finset.range 10 ∧ D.card ≤ S.card + gs.length ∧
      ∀ x y : List Bool, x.length = 10 → y.length = 10 →
      (∀ i ∈ D, x.getD i false = y.getD i false) →
      ∀ i ∈ S, (W gs x).getD i false = (W gs y).getD i false := by
  induction gs using List.reverseRecOn generalizing S with
  | nil =>
    exact ⟨S, fun i hi => Finset.mem_range.mpr (by simpa using hS i hi),
      by simp, fun x y hx hy h i hi => h i hi⟩
  | append_singleton gs g ih =>
    let k := 10 + gs.length
    have hpre : ∀ g' ∈ gs, Good g' := fun g' h => hgood g' (by simp [h])
    have hlen : g.inputs.length ≤ 2 := (hgood g (by simp)).2
    have hS' : ∀ i ∈ S, i ≤ k := by
      intro i hi
      have h := hS i hi
      simp only [List.length_append, List.length_singleton] at h
      omega
    by_cases hk : k ∈ S
    · let T := (S.erase k) ∪ (g.inputs.toFinset.filter (· < k))
      have hT : ∀ i ∈ T, i < k := by
        intro i hi
        rcases Finset.mem_union.mp hi with h | h
        · exact lt_of_le_of_ne (hS' i (Finset.mem_of_mem_erase h)) (Finset.ne_of_mem_erase h)
        · exact (Finset.mem_filter.mp h).2
      have hTcard : T.card ≤ S.card + 1 := by
        have h1 := Finset.card_union_le (S.erase k) (g.inputs.toFinset.filter (· < k))
        have h2 := Finset.card_filter_le g.inputs.toFinset (· < k)
        have h3 := List.toFinset_card_le g.inputs
        have h4 := Finset.card_erase_add_one hk
        change T.card ≤ _ at h1
        omega
      obtain ⟨D, hD, hc, hdet⟩ := ih hpre T hT
      refine ⟨D, hD, by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
      intro x y hx hy h i hi
      have hxk : (W gs x).length = k := by rw [W_len, hx]
      have hyk : (W gs y).length = k := by rw [W_len, hy]
      rw [W_snoc, W_snoc, stp, stp]
      by_cases he : i = k
      · rw [he, ← hxk, getD_len, hxk, ← hyk, getD_len]
        congr 1
        apply List.map_congr_left
        intro j hj
        by_cases hjk : j < k
        · exact hdet x y hx hy h j (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hj, hjk⟩))
        · rw [getD_big _ _ (by omega), getD_big _ _ (by omega)]
      · have hi' := lt_of_le_of_ne (hS' i hi) he
        rw [getD_lt _ _ _ (by omega), getD_lt _ _ _ (by omega)]
        exact hdet x y hx hy h i (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨he, hi⟩))
    · have hT : ∀ i ∈ S, i < k := fun i hi => lt_of_le_of_ne (hS' i hi) (fun e => hk (e ▸ hi))
      obtain ⟨D, hD, hc, hdet⟩ := ih hpre S hT
      refine ⟨D, hD, by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
      intro x y hx hy h i hi
      have hxk : (W gs x).length = k := by rw [W_len, hx]
      have hyk : (W gs y).length = k := by rw [W_len, hy]
      have hi' := hT i hi
      rw [W_snoc, W_snoc, stp, stp, getD_lt _ _ _ (by omega), getD_lt _ _ _ (by omega)]
      exact hdet x y hx hy h i hi

end PEqualNP.Outside.L_meta_20594_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents PEqualNP.Outside.L_meta_20594_aux in
theorem PEqualNP.Outside.L_meta_20594 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (6325248 : ℕ).testBit (5 * u.val + v.val)) 5 ∧ ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (6325248 : ℕ).testBit (5 * u.val + v.val)) 4) := by
  constructor
  · refine ⟨⟨[⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [10, 5]⟩,
      ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.and, [4, 12]⟩,
      ⟨GateOp.or, [11, 13]⟩], 14⟩, ?_, by decide, by decide +kernel⟩
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
  · let A := fun u v : Fin 5 => (6325248 : ℕ).testBit (5 * u.val + v.val)
    change ¬ RepSizeAtMost A 4
    intro h
    obtain ⟨C, hg, hsize, hrep⟩ := h
    have hgood : ∀ g ∈ C.gates, Good g := fun g hg' => by simpa [Good] using hg g hg'
    change C.gates.length ≤ 4 at hsize
    let R : Finset ℕ := {2, 3, 4, 5, 6, 7}
    have hR : R.card = 6 := by decide
    have hrow : ∀ u : Fin 5, (u : ℕ) ∈ R →
        ∃ u' v, A u v = true ∧ A u' v = false := by decide +kernel
    have hcol : ∀ v : Fin 5, 5 + (v : ℕ) ∈ R →
        ∃ v' u, A u v = true ∧ A u v' = false := by decide +kernel
    have hR8 : ∀ i ∈ R, i < 10 := by decide +kernel
    have hev : ∀ x, C.eval x = (W C.gates x).getD C.output false := fun _ => rfl
    have ho : C.output < 10 + C.gates.length := by
      by_contra! hb
      have ht : C.eval (oneEach (2 : Fin 5) (0 : Fin 5)) = true :=
        (hrep 2 0).trans (by decide +kernel)
      rw [hev, getD_big _ _ (by rw [W_len, oe_len]; exact hb)] at ht
      contradiction
    obtain ⟨D, d1, d3, d2⟩ := support C.gates hgood {C.output} (by simpa using ho)
    have hdet : ∀ x y : List Bool, x.length = 10 → y.length = 10 →
        (∀ i ∈ D, x.getD i false = y.getD i false) → C.eval x = C.eval y := by
      intro x y hx hy he
      exact d2 x y hx hy he C.output (by simp)
    have hsub : R ⊆ D := by
      intro i hi
      by_contra hiD
      have hi8 := hR8 i hi
      by_cases h4 : i < 5
      · obtain ⟨u', v, h1, h2⟩ := hrow ⟨i, h4⟩ hi
        have h3 := row_in C hgood A hrep D d1 hdet ⟨i, h4⟩ hiD u' v h1
        rw [h2] at h3
        contradiction
      · have e : 5 + (i - 5) = i := by omega
        obtain ⟨v', u, h1, h2⟩ := hcol ⟨i - 5, by omega⟩ (by simpa [e] using hi)
        have h3 := col_in C hgood A hrep D d1 hdet ⟨i - 5, by omega⟩
          (by simpa [e] using hiD) v' u h1
        rw [h2] at h3
        contradiction
    have hle := Finset.card_le_card hsub
    rw [Finset.card_singleton] at d3
    omega
