import Mathlib
import PEqualNP.Defs

-- A circuit on the ordered inputs with at most n - 1 gates other than NOT and a wire that changes at every
-- one of the n steps: the change sets of all wires are nested or disjoint, and on its change set every
-- wire is always equal or always opposite to that wire.
--
-- Proof: induction over the gate list, last gate removed. The invariant keeps a labelling of the steps
-- 0..n-1 by classes such that (W) every wire changes only at steps of one class, (N) the number of classes
-- is at least n minus the number of gates other than NOT so far, and (S) IF that count is exact and every
-- class is the whole change set of some wire, THEN the change sets are nested or disjoint and two wires
-- with nested change sets are always equal or always opposite on the smaller one. With no gates the
-- classes are the single steps. A NOT gate, a constant gate and a copy keep the labelling. An AND or OR of
-- wires a and b changes only where a or b does; if their classes differ the two classes are joined, which
-- costs one class and one gate. In (S) for the longer list the premise passes down to the shorter list:
-- the count stays exact, and the joined class can only be the change set of the new wire, which forces the
-- change sets of a and b to be their whole classes. Where a changes and b does not, an AND or OR that
-- changes equals a, so the new wire inherits a's side. At the end the wire that changes everywhere puts
-- all steps into one class, the count is exact because at most n - 1 gates are not NOT, and that wire is
-- the whole class, so the premise of (S) holds.

namespace PEqualNP.Outside.L_lib_1374

open PEqualNP.CircuitLowerBounds

/-- The wire list after running a gate list on a wire list: the fold inside `Circuit.wires`. -/
def W (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem W_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    W (gs ++ [g]) w = W gs w ++ [g.op.eval (g.inputs.map fun i => (W gs w).getD i false)] := by
  simp [W, List.foldl_append]

theorem W_len (gs : List Gate) (w : List Bool) : (W gs w).length = w.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc]; simp [ih]; omega

theorem getD_snoc (V : List Bool) (e : Bool) (i : ℕ) :
    (V ++ [e]).getD i false = if i = V.length then e else V.getD i false := by
  split_ifs with h
  · subst h; simp
  · rcases Nat.lt_or_gt_of_ne h with h | h
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem new_wire (gs : List Gate) (g : Gate) (w : List Bool) :
    (W (gs ++ [g]) w).getD (w.length + gs.length) false =
      g.op.eval (g.inputs.map fun t => (W gs w).getD t false) := by
  rw [W_snoc, getD_snoc]; simp [W_len]

theorem old_wire (gs : List Gate) (g : Gate) (w : List Bool) (i : ℕ)
    (hi : i ≠ w.length + gs.length) :
    (W (gs ++ [g]) w).getD i false = (W gs w).getD i false := by
  rw [W_snoc, getD_snoc]; simp [W_len, hi]

/-! ### Words on the ordered inputs -/

/-- The steps at which a word changes. -/
def chg {n : ℕ} (f : Fin (n + 1) → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => f i.castSucc ≠ f i.succ

theorem mem_chg {n : ℕ} (f : Fin (n + 1) → Bool) (i : Fin n) :
    i ∈ chg f ↔ f i.castSucc ≠ f i.succ := by
  simp [chg]

theorem chg_const {n : ℕ} {f : Fin (n + 1) → Bool} (h : ∀ t t', f t = f t') : chg f = ∅ := by
  ext i
  rw [mem_chg]
  simp [h i.castSucc i.succ]

theorem chg_congr {n : ℕ} {f g : Fin (n + 1) → Bool}
    (h : (∀ t, g t = f t) ∨ (∀ t, g t = !f t)) : chg g = chg f := by
  ext i
  rw [mem_chg, mem_chg]
  rcases h with h | h
  · rw [h, h]
  · rw [h, h]
    cases f i.castSucc <;> cases f i.succ <;> simp

/-- Nested or disjoint. -/
def Lam {n : ℕ} (A B : Finset (Fin n)) : Prop := A ⊆ B ∨ B ⊆ A ∨ Disjoint A B

/-- On the change set of `f` the words `f` and `g` are always equal or always opposite. -/
def Pol {n : ℕ} (f g : Fin (n + 1) → Bool) : Prop :=
  (∀ i ∈ chg f, f i.castSucc = g i.castSucc) ∨ (∀ i ∈ chg f, f i.castSucc ≠ g i.castSucc)

theorem Pol.left {n : ℕ} {f f' g : Fin (n + 1) → Bool}
    (h : (∀ t, f' t = f t) ∨ (∀ t, f' t = !f t)) (hp : Pol f g) : Pol f' g := by
  have hc := chg_congr h
  unfold Pol at *
  rw [hc]
  rcases h with h | h
  · rcases hp with hp | hp
    · exact Or.inl fun i hi => by rw [h]; exact hp i hi
    · exact Or.inr fun i hi => by rw [h]; exact hp i hi
  · rcases hp with hp | hp
    · refine Or.inr fun i hi => ?_
      rw [h, ← hp i hi]
      cases f i.castSucc <;> simp
    · refine Or.inl fun i hi => ?_
      have := hp i hi
      rw [h]
      revert this
      cases f i.castSucc <;> cases g i.castSucc <;> simp

theorem Pol.right {n : ℕ} {f g g' : Fin (n + 1) → Bool}
    (h : (∀ t, g' t = g t) ∨ (∀ t, g' t = !g t)) (hp : Pol f g) : Pol f g' := by
  unfold Pol at *
  rcases h with h | h
  · rcases hp with hp | hp
    · exact Or.inl fun i hi => by rw [h]; exact hp i hi
    · exact Or.inr fun i hi => by rw [h]; exact hp i hi
  · rcases hp with hp | hp
    · refine Or.inr fun i hi => ?_
      rw [h, hp i hi]
      cases g i.castSucc <;> simp
    · refine Or.inl fun i hi => ?_
      have := hp i hi
      rw [h]
      revert this
      cases f i.castSucc <;> cases g i.castSucc <;> simp

theorem bool_and_sub (x y c d : Bool) : (x && c) ≠ (y && d) → x ≠ y ∨ c ≠ d := by
  revert x y c d; decide

theorem bool_or_sub (x y c d : Bool) : (x || c) ≠ (y || d) → x ≠ y ∨ c ≠ d := by
  revert x y c d; decide

theorem bool_and_l (x y c : Bool) : (x && c) ≠ (y && c) → (x && c) = x := by
  revert x y c; decide

theorem bool_or_l (x y c : Bool) : (x || c) ≠ (y || c) → (x || c) = x := by
  revert x y c; decide

theorem bool_and_r (x c d : Bool) : (x && c) ≠ (x && d) → (x && c) = c := by
  revert x c d; decide

theorem bool_or_r (x c d : Bool) : (x || c) ≠ (x || d) → (x || c) = c := by
  revert x c d; decide

theorem bin_sub {n : ℕ} {f a b : Fin (n + 1) → Bool}
    (hop : (∀ t, f t = (a t && b t)) ∨ (∀ t, f t = (a t || b t))) : chg f ⊆ chg a ∪ chg b := by
  intro i hi
  rw [Finset.mem_union, mem_chg, mem_chg]
  rw [mem_chg] at hi
  rcases hop with h | h
  · rw [h, h] at hi; exact bool_and_sub _ _ _ _ hi
  · rw [h, h] at hi; exact bool_or_sub _ _ _ _ hi

theorem bin_left {n : ℕ} {f a b : Fin (n + 1) → Bool}
    (hop : (∀ t, f t = (a t && b t)) ∨ (∀ t, f t = (a t || b t))) (i : Fin n)
    (hi : i ∈ chg f) (hb : i ∉ chg b) : f i.castSucc = a i.castSucc := by
  rw [mem_chg] at hi hb
  have hb' : b i.castSucc = b i.succ := not_not.1 hb
  rcases hop with h | h
  · rw [h, h, ← hb'] at hi; rw [h]; exact bool_and_l _ _ _ hi
  · rw [h, h, ← hb'] at hi; rw [h]; exact bool_or_l _ _ _ hi

theorem bin_right {n : ℕ} {f a b : Fin (n + 1) → Bool}
    (hop : (∀ t, f t = (a t && b t)) ∨ (∀ t, f t = (a t || b t))) (i : Fin n)
    (hi : i ∈ chg f) (ha : i ∉ chg a) : f i.castSucc = b i.castSucc := by
  rw [mem_chg] at hi ha
  have ha' : a i.castSucc = a i.succ := not_not.1 ha
  rcases hop with h | h
  · rw [h, h, ← ha'] at hi; rw [h]; exact bool_and_r _ _ _ hi
  · rw [h, h, ← ha'] at hi; rw [h]; exact bool_or_r _ _ _ hi

/-! ### The invariant -/

/-- The first `K` words have nested or disjoint change sets and fixed sides. -/
def Str {n : ℕ} (F : ℕ → Fin (n + 1) → Bool) (K : ℕ) : Prop :=
  (∀ u < K, ∀ v < K, Lam (chg (F u)) (chg (F v))) ∧
  (∀ u < K, ∀ v < K, chg (F u) ⊆ chg (F v) → Pol (F u) (F v))

/-- The steps of one class. -/
def blk {n : ℕ} (cls : Fin n → ℕ) (c : ℕ) : Finset (Fin n) := Finset.univ.filter fun j => cls j = c

theorem mem_blk {n : ℕ} (cls : Fin n → ℕ) (c : ℕ) (j : Fin n) : j ∈ blk cls c ↔ cls j = c := by
  simp [blk]

/-- The invariant for the first `K` words after `P` gates other than NOT. -/
def Inv {n : ℕ} (F : ℕ → Fin (n + 1) → Bool) (K P : ℕ) : Prop :=
  ∃ cls : Fin n → ℕ,
    (∀ u < K, ∀ i ∈ chg (F u), ∀ j ∈ chg (F u), cls i = cls j) ∧
    n ≤ (Finset.univ.image cls).card + P ∧
    ((n = (Finset.univ.image cls).card + P ∧
        ∀ i : Fin n, ∃ u < K, chg (F u) = blk cls (cls i)) → Str F K)

theorem Inv.slack {n : ℕ} {F : ℕ → Fin (n + 1) → Bool} {K P : ℕ} (h : Inv F K P) :
    Inv F K (P + 1) := by
  obtain ⟨cls, hW, hN, -⟩ := h
  exact ⟨cls, hW, by omega, fun hp => absurd hp.1 (by omega)⟩

theorem Inv.congr {n : ℕ} {F F' : ℕ → Fin (n + 1) → Bool} {K P : ℕ}
    (h : ∀ u < K, F' u = F u) (hI : Inv F K P) : Inv F' K P := by
  obtain ⟨cls, hW, hN, hS⟩ := hI
  refine ⟨cls, ?_, hN, ?_⟩
  · intro u hu
    rw [h u hu]
    exact hW u hu
  · rintro ⟨heq, hfull⟩
    obtain ⟨hlam, hpol⟩ := hS ⟨heq, fun i => by
      obtain ⟨u, hu, e⟩ := hfull i
      exact ⟨u, hu, by rw [← h u hu]; exact e⟩⟩
    refine ⟨?_, ?_⟩
    · intro u hu v hv
      rw [h u hu, h v hv]
      exact hlam u hu v hv
    · intro u hu v hv hs
      rw [h u hu, h v hv] at hs ⊢
      exact hpol u hu v hv hs

/-- A new word that never changes. -/
theorem Inv.const {n : ℕ} {F : ℕ → Fin (n + 1) → Bool} {K P : ℕ} (hc : chg (F K) = ∅)
    (h : Inv F K P) : Inv F (K + 1) P := by
  obtain ⟨cls, hW, hN, hS⟩ := h
  refine ⟨cls, ?_, hN, ?_⟩
  · intro u hu i hi j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | hu
    · exact hW u hu i hi j hj
    · rw [hu, hc] at hi
      exact absurd hi (Finset.notMem_empty i)
  · rintro ⟨heq, hfull⟩
    have hfullK : ∀ i : Fin n, ∃ u < K, chg (F u) = blk cls (cls i) := by
      intro i
      obtain ⟨u, hu, hue⟩ := hfull i
      rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | hu
      · exact ⟨u, hu, hue⟩
      · exfalso
        have hi : i ∈ blk cls (cls i) := (mem_blk cls _ i).2 rfl
        rw [← hue, hu, hc] at hi
        exact Finset.notMem_empty i hi
    obtain ⟨hlam, hpol⟩ := hS ⟨heq, hfullK⟩
    refine ⟨?_, ?_⟩
    · intro u hu v hv
      rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | hu
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hv with hv | hv
        · exact hlam u hu v hv
        · exact Or.inr (Or.inl (by rw [hv, hc]; exact Finset.empty_subset _))
      · exact Or.inl (by rw [hu, hc]; exact Finset.empty_subset _)
    · intro u hu v hv hsub
      rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | hu
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hv with hv | hv
        · exact hpol u hu v hv hsub
        · refine Or.inl fun i hi => ?_
          have := hsub hi
          rw [hv, hc] at this
          exact absurd this (Finset.notMem_empty i)
      · refine Or.inl fun i hi => ?_
        rw [hu, hc] at hi
        exact absurd hi (Finset.notMem_empty i)

/-- A new word that is an old word or its negation. -/
theorem Inv.same {n : ℕ} {F : ℕ → Fin (n + 1) → Bool} {K P a : ℕ} (ha : a < K)
    (h : (∀ t, F K t = F a t) ∨ (∀ t, F K t = !F a t)) (hI : Inv F K P) : Inv F (K + 1) P := by
  have hc : chg (F K) = chg (F a) := chg_congr h
  obtain ⟨cls, hW, hN, hS⟩ := hI
  refine ⟨cls, ?_, hN, ?_⟩
  · intro u hu i hi j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | hu
    · exact hW u hu i hi j hj
    · rw [hu, hc] at hi hj
      exact hW a ha i hi j hj
  · rintro ⟨heq, hfull⟩
    have hfullK : ∀ i : Fin n, ∃ u < K, chg (F u) = blk cls (cls i) := by
      intro i
      obtain ⟨u, hu, hue⟩ := hfull i
      rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | hu
      · exact ⟨u, hu, hue⟩
      · rw [hu, hc] at hue
        exact ⟨a, ha, hue⟩
    obtain ⟨hlam, hpol⟩ := hS ⟨heq, hfullK⟩
    have key : ∀ u, u < K + 1 → ∃ u', u' < K ∧ chg (F u) = chg (F u') ∧
        ((∀ t, F u t = F u' t) ∨ (∀ t, F u t = !F u' t)) := by
      intro u hu
      rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | hu
      · exact ⟨u, hu, rfl, Or.inl fun _ => rfl⟩
      · rw [hu]
        exact ⟨a, ha, hc, h⟩
    refine ⟨?_, ?_⟩
    · intro u hu v hv
      obtain ⟨u', hu', eu, -⟩ := key u hu
      obtain ⟨v', hv', ev, -⟩ := key v hv
      rw [eu, ev]
      exact hlam u' hu' v' hv'
    · intro u hu v hv hsub
      obtain ⟨u', hu', eu, ru⟩ := key u hu
      obtain ⟨v', hv', ev, rv⟩ := key v hv
      rw [eu, ev] at hsub
      exact Pol.left ru (Pol.right rv (hpol u' hu' v' hv' hsub))

/-- A new word that is the AND or the OR of two old words. -/
theorem Inv.bin {n : ℕ} {F : ℕ → Fin (n + 1) → Bool} {K P a b : ℕ} (ha : a < K) (hb : b < K)
    (hop : (∀ t, F K t = (F a t && F b t)) ∨ (∀ t, F K t = (F a t || F b t)))
    (hI : Inv F K P) : Inv F (K + 1) (P + 1) := by
  have hsub : chg (F K) ⊆ chg (F a) ∪ chg (F b) := bin_sub hop
  obtain ⟨cls, hW, hN, hS⟩ := hI
  by_cases hm : ∀ x ∈ chg (F a), ∀ y ∈ chg (F b), cls x = cls y
  · -- the two wires change in one class: nothing is joined
    refine ⟨cls, ?_, by omega, fun hp => absurd hp.1 (by omega)⟩
    intro u hu i hi j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | hu
    · exact hW u hu i hi j hj
    · rw [hu] at hi hj
      rcases Finset.mem_union.1 (hsub hi) with hi | hi <;>
        rcases Finset.mem_union.1 (hsub hj) with hj | hj
      · exact hW a ha i hi j hj
      · exact hm i hi j hj
      · exact (hm j hj i hi).symm
      · exact hW b hb i hi j hj
  · -- two classes are joined
    simp only [not_forall] at hm
    obtain ⟨x, hx, y, hy, hxy⟩ := hm
    obtain ⟨cls', hcls'⟩ : ∃ cls' : Fin n → ℕ,
        ∀ i, cls' i = if cls i = cls y then cls x else cls i := ⟨_, fun _ => rfl⟩
    have hA : ∀ i ∈ chg (F a), cls i = cls x := fun i hi => hW a ha i hi x hx
    have hB : ∀ i ∈ chg (F b), cls i = cls y := fun i hi => hW b hb i hi y hy
    have hH : ∀ i ∈ chg (F K), cls' i = cls x := by
      intro i hi
      rcases Finset.mem_union.1 (hsub hi) with h | h
      · rw [hcls', hA i h]; simp
      · rw [hcls', hB i h]; simp
    have hW' : ∀ u < K + 1, ∀ i ∈ chg (F u), ∀ j ∈ chg (F u), cls' i = cls' j := by
      intro u hu i hi j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | hu
      · rw [hcls', hcls', hW u hu i hi j hj]
      · rw [hu] at hi hj
        rw [hH i hi, hH j hj]
    have himg : Finset.univ.image cls' =
        (Finset.univ.image cls).image (fun c => if c = cls y then cls x else c) := by
      rw [Finset.image_image]
      congr 1
      funext i
      exact hcls' i
    have hcard : (Finset.univ.image cls).card ≤ (Finset.univ.image cls').card + 1 := by
      rw [himg]
      have h1 : ((Finset.univ.image cls).erase (cls y)).card ≤
          ((Finset.univ.image cls).image (fun c => if c = cls y then cls x else c)).card := by
        rw [← Finset.card_image_of_injOn (f := fun c => if c = cls y then cls x else c)
          (s := (Finset.univ.image cls).erase (cls y))]
        · exact Finset.card_le_card (Finset.image_subset_image (Finset.erase_subset _ _))
        · intro c hc d hd hcd
          have hc' : c ≠ cls y := (Finset.mem_erase.1 (Finset.mem_coe.1 hc)).1
          have hd' : d ≠ cls y := (Finset.mem_erase.1 (Finset.mem_coe.1 hd)).1
          simpa [hc', hd'] using hcd
      have h2 := Finset.pred_card_le_card_erase (s := Finset.univ.image cls) (a := cls y)
      omega
    refine ⟨cls', hW', by omega, ?_⟩
    rintro ⟨heq, hfull⟩
    have hcardeq : n = (Finset.univ.image cls).card + P := by omega
    have hx' : cls' x = cls x := by rw [hcls']; simp
    have hy' : cls' y = cls x := by rw [hcls']; simp
    -- the joined class can only be the change set of the new word
    obtain ⟨hxK, hyK, hKe⟩ : x ∈ chg (F K) ∧ y ∈ chg (F K) ∧ chg (F K) = blk cls' (cls x) := by
      obtain ⟨u, hu, hue⟩ := hfull x
      rw [hx'] at hue
      have hxm : x ∈ chg (F u) := by rw [hue]; exact (mem_blk _ _ _).2 hx'
      have hym : y ∈ chg (F u) := by rw [hue]; exact (mem_blk _ _ _).2 hy'
      rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | hu
      · exact absurd (hW u hu x hxm y hym) hxy
      · rw [hu] at hxm hym hue
        exact ⟨hxm, hym, hue⟩
    have hmemK : ∀ i, i ∈ chg (F K) ↔ (cls i = cls x ∨ cls i = cls y) := by
      intro i
      rw [hKe, mem_blk, hcls']
      by_cases h1 : cls i = cls y
      · simp [h1]
      · simp [h1]
    have hAe : chg (F a) = blk cls (cls x) := by
      ext i
      rw [mem_blk]
      constructor
      · exact hA i
      · intro hi
        have hiK : i ∈ chg (F K) := (hmemK i).2 (Or.inl hi)
        rcases Finset.mem_union.1 (hsub hiK) with h | h
        · exact h
        · exact absurd (hi.symm.trans (hB i h)) hxy
    have hBe : chg (F b) = blk cls (cls y) := by
      ext i
      rw [mem_blk]
      constructor
      · exact hB i
      · intro hi
        have hiK : i ∈ chg (F K) := (hmemK i).2 (Or.inr hi)
        rcases Finset.mem_union.1 (hsub hiK) with h | h
        · exact absurd ((hA i h).symm.trans hi) hxy
        · exact h
    have hfullK : ∀ i : Fin n, ∃ u < K, chg (F u) = blk cls (cls i) := by
      intro i
      by_cases h1 : cls i = cls x
      · exact ⟨a, ha, by rw [h1]; exact hAe⟩
      by_cases h2 : cls i = cls y
      · exact ⟨b, hb, by rw [h2]; exact hBe⟩
      obtain ⟨u, hu, hue⟩ := hfull i
      have hi' : cls' i = cls i := by rw [hcls']; simp [h2]
      have hblk : blk cls' (cls' i) = blk cls (cls i) := by
        rw [hi']
        ext j
        rw [mem_blk, mem_blk, hcls']
        by_cases h3 : cls j = cls y
        · have e1 : (if cls j = cls y then cls x else cls j) = cls x := by simp [h3]
          rw [e1]
          constructor
          · intro h; exact absurd h.symm h1
          · intro h; exact absurd (h3.symm.trans h).symm h2
        · have e1 : (if cls j = cls y then cls x else cls j) = cls j := by simp [h3]
          rw [e1]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | hu
      · exact ⟨u, hu, by rw [hue, hblk]⟩
      · exfalso
        rw [hu] at hue
        have hiK : i ∈ chg (F K) := by rw [hue]; exact (mem_blk _ _ _).2 rfl
        rcases (hmemK i).1 hiK with h | h
        · exact h1 h
        · exact h2 h
    obtain ⟨hlam, hpol⟩ := hS ⟨hcardeq, hfullK⟩
    have hKu : chg (F K) = chg (F a) ∪ chg (F b) := by
      apply Finset.Subset.antisymm hsub
      intro i hi
      rcases Finset.mem_union.1 hi with h | h
      · exact (hmemK i).2 (Or.inl (hA i h))
      · exact (hmemK i).2 (Or.inr (hB i h))
    have hdisj : ∀ i, i ∈ chg (F a) → i ∉ chg (F b) := fun i h1 h2 =>
      hxy ((hA i h1).symm.trans (hB i h2))
    have hold : ∀ u < K, chg (F u) ⊆ chg (F a) ∨ chg (F u) ⊆ chg (F b) ∨
        Disjoint (chg (F u)) (chg (F K)) := by
      intro u hu
      by_cases he : ∃ z, z ∈ chg (F u) ∧ cls z = cls x
      · obtain ⟨z, hz, hzc⟩ := he
        refine Or.inl fun w hw => ?_
        rw [hAe, mem_blk]
        exact (hW u hu w hw z hz).trans hzc
      by_cases he2 : ∃ z, z ∈ chg (F u) ∧ cls z = cls y
      · obtain ⟨z, hz, hzc⟩ := he2
        refine Or.inr (Or.inl fun w hw => ?_)
        rw [hBe, mem_blk]
        exact (hW u hu w hw z hz).trans hzc
      refine Or.inr (Or.inr ?_)
      rw [Finset.disjoint_left]
      intro w hw hwK
      rcases (hmemK w).1 hwK with h | h
      · exact he ⟨w, hw, h⟩
      · exact he2 ⟨w, hw, h⟩
    refine ⟨?_, ?_⟩
    · intro u hu v hv
      rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | hu <;>
        rcases Nat.lt_succ_iff_lt_or_eq.1 hv with hv | hv
      · exact hlam u hu v hv
      · rw [hv]
        rcases hold u hu with h | h | h
        · exact Or.inl (h.trans (by rw [hKu]; exact Finset.subset_union_left))
        · exact Or.inl (h.trans (by rw [hKu]; exact Finset.subset_union_right))
        · exact Or.inr (Or.inr h)
      · rw [hu]
        rcases hold v hv with h | h | h
        · exact Or.inr (Or.inl (h.trans (by rw [hKu]; exact Finset.subset_union_left)))
        · exact Or.inr (Or.inl (h.trans (by rw [hKu]; exact Finset.subset_union_right)))
        · exact Or.inr (Or.inr h.symm)
      · rw [hu, hv]
        exact Or.inl (Finset.Subset.refl _)
    · intro u hu v hv hs
      rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | hu <;>
        rcases Nat.lt_succ_iff_lt_or_eq.1 hv with hv | hv
      · exact hpol u hu v hv hs
      · rw [hv] at hs ⊢
        by_cases hem : chg (F u) = ∅
        · refine Or.inl fun i hi => ?_
          rw [hem] at hi
          exact absurd hi (Finset.notMem_empty i)
        obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.2 hem
        rcases hold u hu with h | h | h
        · have hk : ∀ i ∈ chg (F u), F K i.castSucc = F a i.castSucc := fun i hi =>
            bin_left hop i (hs hi) (hdisj i (h hi))
          rcases hpol u hu a ha h with hp | hp
          · exact Or.inl fun i hi => by rw [hk i hi]; exact hp i hi
          · exact Or.inr fun i hi => by rw [hk i hi]; exact hp i hi
        · have hk : ∀ i ∈ chg (F u), F K i.castSucc = F b i.castSucc := fun i hi =>
            bin_right hop i (hs hi) (fun hia => hdisj i hia (h hi))
          rcases hpol u hu b hb h with hp | hp
          · exact Or.inl fun i hi => by rw [hk i hi]; exact hp i hi
          · exact Or.inr fun i hi => by rw [hk i hi]; exact hp i hi
        · exact absurd (hs hz) (Finset.disjoint_left.1 h hz)
      · rw [hu] at hs
        exact absurd (hW v hv x (hs hxK) y (hs hyK)) hxy
      · rw [hu, hv]
        exact Or.inl fun _ _ => rfl

/-! ### The circuit -/

/-- The ordered input number `t`. -/
def inp (n : ℕ) (t : Fin (n + 1)) : List Bool :=
  List.ofFn (fun i : Fin n => decide (i.val < t.val)) ++ [false, true]

theorem inp_len (n : ℕ) (t : Fin (n + 1)) : (inp n t).length = n + 2 := by simp [inp]

/-- The value of wire `u` on the ordered input number `t`. -/
def vl (n : ℕ) (gs : List Gate) (u : ℕ) (t : Fin (n + 1)) : Bool := (W gs (inp n t)).getD u false

theorem vl_old (n : ℕ) (gs : List Gate) (g : Gate) (u : ℕ) (hu : u < n + 2 + gs.length) :
    vl n (gs ++ [g]) u = vl n gs u := by
  funext t
  exact old_wire gs g (inp n t) u (by rw [inp_len]; omega)

theorem vl_new (n : ℕ) (gs : List Gate) (g : Gate) (t : Fin (n + 1)) :
    vl n (gs ++ [g]) (n + 2 + gs.length) t = g.op.eval (g.inputs.map fun i => vl n gs i t) := by
  have h := new_wire gs g (inp n t)
  rw [inp_len] at h
  exact h

theorem inp_getD (n : ℕ) (t : Fin (n + 1)) (u : ℕ) :
    (inp n t).getD u false = if u < n then decide (u < t.val) else decide (u = n + 1) := by
  unfold inp
  split_ifs with h
  · rw [List.getD_append _ _ _ _ (by simpa using h), List.getD_eq_getElem _ _ (by simpa using h)]
    simp
  · obtain ⟨d, rfl⟩ : ∃ d, u = n + d := ⟨u - n, by omega⟩
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp only [List.length_ofFn, Nat.add_sub_cancel_left]
    rcases d with _ | _ | d
    · simp
    · simp
    · simp

theorem base_chg (n u : ℕ) (i : Fin n) (hi : i ∈ chg (vl n [] u)) : i.val = u := by
  rw [mem_chg] at hi
  simp only [vl, W, List.foldl_nil, inp_getD, Fin.val_castSucc, Fin.val_succ] at hi
  split_ifs at hi with h
  · by_contra hne
    apply hi
    have : (u < i.val) ↔ (u < i.val + 1) := by omega
    simp [this]
  · exact absurd rfl hi

theorem inv_base (n : ℕ) : Inv (vl n []) (n + 2) 0 := by
  refine ⟨fun i => i.val, ?_, ?_, ?_⟩
  · intro u _ i hi j hj
    show i.val = j.val
    rw [base_chg n u i hi, base_chg n u j hj]
  · rw [Finset.card_image_of_injective _ Fin.val_injective]
    simp
  · intro _
    refine ⟨?_, ?_⟩
    · intro u _ v _
      by_cases h : ∃ i, i ∈ chg (vl n [] u) ∧ i ∈ chg (vl n [] v)
      · obtain ⟨i, h1, h2⟩ := h
        have huv : u = v := (base_chg n u i h1).symm.trans (base_chg n v i h2)
        rw [huv]
        exact Or.inl (Finset.Subset.refl _)
      · refine Or.inr (Or.inr ?_)
        rw [Finset.disjoint_left]
        intro i h1 h2
        exact h ⟨i, h1, h2⟩
    · intro u _ v _ hs
      by_cases h : ∃ i, i ∈ chg (vl n [] u)
      · obtain ⟨i, h1⟩ := h
        have huv : u = v := (base_chg n u i h1).symm.trans (base_chg n v i (hs h1))
        rw [huv]
        exact Or.inl fun _ _ => rfl
      · exact Or.inl fun i hi => absurd ⟨i, hi⟩ h

theorem inv_all (isNot : Gate → Bool) (hisNot : ∀ g, isNot g = true ↔ g.op = GateOp.not) (n : ℕ) :
    ∀ gs : List Gate,
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) →
      (∀ (j : ℕ) (g : Gate), gs[j]? = some g → ∀ a ∈ g.inputs, a < n + 2 + j) →
      Inv (vl n gs) (n + 2 + gs.length) (gs.filter fun g => !isNot g).length := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil => intro _ _; exact inv_base n
  | append_singleton gs g ih =>
    intro hF hR
    have ih' := ih (fun g' hg' => hF g' (List.mem_append_left _ hg'))
      (fun j g' hj a ha => hR j g' (by
        have hjl : j < gs.length := by
          by_contra hc
          rw [List.getElem?_eq_none (by omega)] at hj
          simp at hj
        rw [List.getElem?_append_left hjl]
        exact hj) a ha)
    obtain ⟨hgop, hglen⟩ := hF g (by simp)
    have hin : ∀ a ∈ g.inputs, a < n + 2 + gs.length := hR gs.length g (by simp)
    have hI : Inv (vl n (gs ++ [g])) (n + 2 + gs.length) (gs.filter fun g => !isNot g).length :=
      Inv.congr (fun u hu => vl_old n gs g u hu) ih'
    have hnew : ∀ t, vl n (gs ++ [g]) (n + 2 + gs.length) t =
        g.op.eval (g.inputs.map fun i => vl n (gs ++ [g]) i t) := by
      intro t
      rw [vl_new]
      congr 1
      apply List.map_congr_left
      intro i hi
      rw [vl_old n gs g i (hin i hi)]
    have e1 : n + 2 + (gs ++ [g]).length = n + 2 + gs.length + 1 := by simp [Nat.add_assoc]
    have e2 : ((gs ++ [g]).filter fun g => !isNot g).length =
        (gs.filter fun g => !isNot g).length + (if isNot g then 0 else 1) := by
      rw [List.filter_append]
      cases h : isNot g <;> simp [h]
    rw [e1, e2]
    by_cases hn : isNot g = true
    · -- a NOT gate
      have hop : g.op = GateOp.not := (hisNot g).1 hn
      have e3 : (if isNot g = true then 0 else 1) = 0 := by simp [hn]
      rw [e3, Nat.add_zero]
      rcases hgi : g.inputs with _ | ⟨a, rest⟩
      · apply Inv.const _ hI
        apply chg_const
        intro t t'
        rw [hnew, hnew, hgi]
        rfl
      · apply Inv.same (hin a (by rw [hgi]; simp)) _ hI
        refine Or.inr fun t => ?_
        rw [hnew, hgi, hop]
        rfl
    · -- an AND or OR gate
      have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by
        rcases hgop with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd ((hisNot g).2 h) hn
      have e3 : (if isNot g = true then 0 else 1) = 1 := by simp [hn]
      rw [e3]
      rcases hgi : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
      · apply Inv.slack
        apply Inv.const _ hI
        apply chg_const
        intro t t'
        rw [hnew, hnew, hgi]
        rfl
      · apply Inv.slack
        apply Inv.same (hin a (by rw [hgi]; simp)) _ hI
        refine Or.inl fun t => ?_
        rw [hnew, hgi]
        rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval]
      · apply Inv.bin (hin a (by rw [hgi]; simp)) (hin b (by rw [hgi]; simp)) _ hI
        rcases hop with h | h
        · refine Or.inl fun t => ?_
          rw [hnew, hgi, h]
          simp [GateOp.eval]
        · refine Or.inr fun t => ?_
          rw [hnew, hgi, h]
          simp [GateOp.eval]
      · rw [hgi] at hglen
        simp at hglen

theorem filter_split (p : Gate → Bool) (l : List Gate) :
    (l.filter p).length + (l.filter fun g => !p g).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => cases h : p a <;> simp [h] <;> omega

theorem main (n : ℕ) (C : Circuit) (root : Fin (n + 2 + C.size))
    (hF : PEqualNP.MetaComplexity.FanInTwo C)
    (hR : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C)
    (hP : C.size - PEqualNP.NotBracket.notCount C ≤ n - 1)
    (hroot : chg (vl n C.gates root.val) = Finset.univ) :
    Str (vl n C.gates) (n + 2 + C.gates.length) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨?_, ?_⟩
    · intro u _ v _
      exact Or.inl (by rw [Finset.eq_empty_of_isEmpty (chg (vl 0 C.gates u))]; exact Finset.empty_subset _)
    · intro u _ v _ _
      exact Or.inl fun i _ => i.elim0
  have hP2 := hP
  unfold PEqualNP.NotBracket.notCount Circuit.size at hP2
  obtain ⟨isNot, hisNot, hPle⟩ : ∃ isNot : Gate → Bool,
      (∀ g, isNot g = true ↔ g.op = GateOp.not) ∧
        C.gates.length - (C.gates.filter isNot).length ≤ n - 1 := by
    refine ⟨_, ?_, hP2⟩
    intro g
    simp only [decide_eq_true_eq]
  have hInv := inv_all isNot hisNot n C.gates
    (fun g hg => by
      obtain ⟨h1, h2⟩ := hF g hg
      refine ⟨?_, h2⟩
      simpa using h1)
    (fun j g hj a ha => by
      have hjl : j < C.gates.length := by
        by_contra hc
        rw [List.getElem?_eq_none (by omega)] at hj
        simp at hj
      have e : PEqualNP.MetaComplexity.NestedCover.gateAt C j = g := by
        unfold PEqualNP.MetaComplexity.NestedCover.gateAt
        rw [List.getD_eq_getElem?_getD, hj]
        rfl
      exact hR j hjl a (by rw [e]; exact ha))
  obtain ⟨cls, hW, hN, hS⟩ := hInv
  have hsplit := filter_split isNot C.gates
  have hall : ∀ i j : Fin n, cls i = cls j := fun i j =>
    hW root.val root.isLt i (by rw [hroot]; exact Finset.mem_univ _) j
      (by rw [hroot]; exact Finset.mem_univ _)
  have hc1 : (Finset.univ.image cls).card ≤ 1 := by
    apply Finset.card_le_one.2
    intro c hc d hd
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hc
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hd
    exact hall i j
  apply hS
  refine ⟨by omega, fun i => ⟨root.val, root.isLt, ?_⟩⟩
  rw [hroot]
  ext j
  rw [mem_blk]
  simp [hall j i]

end PEqualNP.Outside.L_lib_1374

theorem PEqualNP.Outside.L_lib_1374 :
∀ (n : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (root : Fin (n+2+C.size)),
  PEqualNP.MetaComplexity.FanInTwo C →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C →
  C.size - PEqualNP.NotBracket.notCount C ≤ n-1 →
  let value := fun (j : Fin (n+2+C.size)) (t : Fin (n+1)) =>
    (C.wires ((List.ofFn (fun i : Fin n => decide (i.val < t.val))) ++ [false,true])).getD j.val false
  let changes := fun j => (Finset.univ : Finset (Fin n)).filter
    (fun i => value j i.castSucc ≠ value j i.succ)
  changes root = Finset.univ →
  (∀ u v, changes u ⊆ changes v ∨ changes v ⊆ changes u ∨ Disjoint (changes u) (changes v)) ∧
  ∀ u, (∀ i ∈ changes u, value u i.castSucc = value root i.castSucc) ∨
       (∀ i ∈ changes u, value u i.castSucc ≠ value root i.castSucc) := by
  intro n C root hF hR hP value changes hroot
  have hroot' : PEqualNP.Outside.L_lib_1374.chg
      (PEqualNP.Outside.L_lib_1374.vl n C.gates root.val) = Finset.univ := hroot
  obtain ⟨hlam, hpol⟩ := PEqualNP.Outside.L_lib_1374.main n C root hF hR hP hroot'
  refine ⟨fun u v => hlam u.val u.isLt v.val v.isLt, fun u => ?_⟩
  exact hpol u.val u.isLt root.val root.isLt (by rw [hroot']; exact Finset.subset_univ _)
