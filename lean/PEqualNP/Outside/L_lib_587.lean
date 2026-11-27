import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_587_aux

private def toZ2 (b : Bool) : ZMod 2 := if b then 1 else 0

private lemma toZ2_xor (a b : Bool) : toZ2 (xor a b) = toZ2 a + toZ2 b := by
  cases a <;> cases b <;> decide

private lemma toZ2_eq_zero_iff (b : Bool) : toZ2 b = 0 ↔ b = false := by
  cases b <;> decide

private lemma toZ2_eq_one_iff (b : Bool) : toZ2 b = 1 ↔ b = true := by
  cases b <;> decide

private lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

private lemma zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

private lemma zmod2_add_eq_zero_iff (a b : ZMod 2) : a + b = 0 ↔ a = b := by
  constructor
  · intro h
    calc a = a + (b + b) := by rw [zmod2_add_self, add_zero]
      _ = (a + b) + b := (add_assoc a b b).symm
      _ = b := by rw [h, zero_add]
  · rintro rfl
    exact zmod2_add_self a

private def monEval {m r : ℕ} (mon : Finset (Fin m × Fin r)) (x : (Fin m × Fin r) → Bool) : ZMod 2 :=
  if ∀ a ∈ mon, x a = true then 1 else 0

private lemma monEval_empty {m r : ℕ} (x : (Fin m × Fin r) → Bool) :
    monEval (m := m) (r := r) ∅ x = 1 := by
  simp [monEval]

private lemma monEval_singleton {m r : ℕ} (v : Fin m × Fin r) (x : (Fin m × Fin r) → Bool) :
    monEval {v} x = toZ2 (x v) := by
  simp only [monEval, Finset.mem_singleton, forall_eq, toZ2]

private lemma monEval_union {m r : ℕ} (s t : Finset (Fin m × Fin r)) (x : (Fin m × Fin r) → Bool) :
    monEval s x * monEval t x = monEval (s ∪ t) x := by
  unfold monEval
  by_cases hs : ∀ a ∈ s, x a = true <;> by_cases ht : ∀ a ∈ t, x a = true
  · have hst : ∀ a ∈ s ∪ t, x a = true := by
      intro a ha
      rcases Finset.mem_union.mp ha with h1 | h2
      · exact hs a h1
      · exact ht a h2
    have hp1 : (∀ a ∈ s, x a = true) ↔ True := iff_true_intro hs
    have hp2 : (∀ a ∈ t, x a = true) ↔ True := iff_true_intro ht
    have hp3 : (∀ a ∈ s ∪ t, x a = true) ↔ True := iff_true_intro hst
    simp only [hp1, hp2, hp3, ↓reduceIte, mul_one]
  · have hnst : ¬ ∀ a ∈ s ∪ t, x a = true := fun h => ht (fun a ha => h a (Finset.mem_union_right s ha))
    have hp2 : (∀ a ∈ t, x a = true) ↔ False := iff_false_intro ht
    have hp3 : (∀ a ∈ s ∪ t, x a = true) ↔ False := iff_false_intro hnst
    simp only [hp2, hp3, ↓reduceIte, mul_zero]
  · have hnst : ¬ ∀ a ∈ s ∪ t, x a = true := fun h => hs (fun a ha => h a (Finset.mem_union_left t ha))
    have hp1 : (∀ a ∈ s, x a = true) ↔ False := iff_false_intro hs
    have hp3 : (∀ a ∈ s ∪ t, x a = true) ↔ False := iff_false_intro hnst
    simp only [hp1, hp3, ↓reduceIte, zero_mul]
  · have hnst : ¬ ∀ a ∈ s ∪ t, x a = true := fun h => hs (fun a ha => h a (Finset.mem_union_left t ha))
    have hp1 : (∀ a ∈ s, x a = true) ↔ False := iff_false_intro hs
    have hp3 : (∀ a ∈ s ∪ t, x a = true) ↔ False := iff_false_intro hnst
    simp only [hp1, hp3, ↓reduceIte, zero_mul]

private def polyEval {m r : ℕ} (c : Finset (Fin m × Fin r) → ZMod 2)
    (x : (Fin m × Fin r) → Bool) : ZMod 2 :=
  ∑ mon : Finset (Fin m × Fin r), c mon * monEval mon x

private lemma polyEval_add {m r : ℕ} (c1 c2 : Finset (Fin m × Fin r) → ZMod 2)
    (x : (Fin m × Fin r) → Bool) :
    polyEval (fun s => c1 s + c2 s) x = polyEval c1 x + polyEval c2 x := by
  unfold polyEval
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro s _
  ring

private lemma polyEval_smul {m r : ℕ} (a : ZMod 2) (c : Finset (Fin m × Fin r) → ZMod 2)
    (x : (Fin m × Fin r) → Bool) :
    polyEval (fun s => a * c s) x = a * polyEval c x := by
  unfold polyEval
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro s _
  ring

private lemma polyEval_injective (m r : ℕ) :
    Function.Injective (polyEval (m := m) (r := r)) := by
  intro c1 c2 heq
  have hzero : ∀ c : Finset (Fin m × Fin r) → ZMod 2,
      (∀ x, polyEval c x = 0) → ∀ mon, c mon = 0 := by
    intro c hc
    have hstrong : ∀ k : ℕ, ∀ mon : Finset (Fin m × Fin r), mon.card = k → c mon = 0 := by
      intro k
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        intro mon hcard
        let xmon : (Fin m × Fin r) → Bool := fun v => decide (v ∈ mon)
        have hx := hc xmon
        unfold polyEval at hx
        rw [Finset.sum_eq_single mon] at hx
        · have h1 : monEval mon xmon = 1 := by
            have hall : ∀ a ∈ mon, xmon a = true := fun a ha => decide_eq_true ha
            have hp : (∀ a ∈ mon, xmon a = true) ↔ True := iff_true_intro hall
            simp only [monEval, hp, ↓reduceIte]
          simpa [h1] using hx
        · intro s _ hsne
          by_cases hsub : s ⊆ mon
          · have hssub : s ⊂ mon := ssubset_iff_subset_ne.mpr ⟨hsub, hsne⟩
            have hlt : s.card < k := hcard ▸ Finset.card_lt_card hssub
            rw [ih s.card hlt s rfl, zero_mul]
          · have hnot : ¬ ∀ a ∈ s, xmon a = true := by
              intro hall
              apply hsub
              intro a ha
              exact of_decide_eq_true (hall a ha)
            have hp : (∀ a ∈ s, xmon a = true) ↔ False := iff_false_intro hnot
            simp only [monEval, hp, ↓reduceIte, mul_zero]
        · intro hnot
          exact absurd (Finset.mem_univ mon) hnot
    intro mon
    exact hstrong mon.card mon rfl
  have hdiff : ∀ x, polyEval (fun s => c1 s + c2 s) x = 0 := by
    intro x
    rw [polyEval_add, congrFun heq x, zmod2_add_self]
  funext mon
  exact (zmod2_add_eq_zero_iff (c1 mon) (c2 mon)).mp (hzero _ hdiff mon)

private lemma polyEval_surjective (m r : ℕ) :
    Function.Surjective (polyEval (m := m) (r := r)) := by
  have hbij : Function.Bijective (polyEval (m := m) (r := r)) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨polyEval_injective m r, ?_⟩
    simp [Fintype.card_finset, ZMod.card]
  exact hbij.2

private def blockSet {m r : ℕ} (i : Fin m) : Finset (Fin m × Fin r) :=
  (Finset.univ : Finset (Fin r)).image (fun j => (i, j))

private lemma card_blockSet {m r : ℕ} (i : Fin m) : (blockSet (r := r) i).card = r := by
  unfold blockSet
  rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
  simp

private lemma mem_blockSet {m r : ℕ} (i : Fin m) (v : Fin m × Fin r) :
    v ∈ blockSet i ↔ v.1 = i := by
  rcases v with ⟨i', j⟩
  simp only [blockSet, Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq]
  constructor
  · rintro ⟨_, rfl, _⟩; rfl
  · rintro rfl; exact ⟨j, rfl, rfl⟩

private lemma prodBit_toZ2 {m r : ℕ} (i : Fin m) (x : (Fin m × Fin r) → Bool) :
    toZ2 (decide (∀ j : Fin r, x (i, j) = true)) = monEval (blockSet i) x := by
  unfold toZ2 monEval
  have hiff : (∀ j : Fin r, x (i, j) = true) ↔ ∀ a ∈ blockSet i, x a = true := by
    constructor
    · intro h a ha
      rcases Finset.mem_image.mp ha with ⟨j, _, rfl⟩
      exact h j
    · intro h j
      exact h (i, j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
  by_cases h : ∀ j : Fin r, x (i, j) = true
  · have hd : decide (∀ j : Fin r, x (i, j) = true) = true := decide_eq_true h
    have hp : (∀ a ∈ blockSet i, x a = true) ↔ True := iff_true_intro (hiff.mp h)
    rw [hd]
    simp only [↓reduceIte, hp]
  · have hd : decide (∀ j : Fin r, x (i, j) = true) = false := decide_eq_false h
    have hp : (∀ a ∈ blockSet i, x a = true) ↔ False := iff_false_intro (fun h2 => h (hiff.mpr h2))
    rw [hd]
    simp only [Bool.false_eq_true, ↓reduceIte, hp]

private lemma parity_filter_toZ2 {m r : ℕ} (terms : Finset (Finset (Fin m × Fin r)))
    (x : (Fin m × Fin r) → Bool) :
    toZ2 ((((terms.filter (fun mon => ∀ a ∈ mon, x a = true)).card % 2) == 1)) =
      ∑ mon ∈ terms, monEval mon x := by
  have hcard : (∑ mon ∈ terms, monEval mon x) =
      ((terms.filter (fun mon => ∀ a ∈ mon, x a = true)).card : ZMod 2) := by
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl ?_
    intro mon _
    unfold monEval
    split_ifs <;> simp
  rw [hcard]
  set k := (terms.filter (fun mon => ∀ a ∈ mon, x a = true)).card
  have hmod : (k : ZMod 2) = ((k % 2 : ℕ) : ZMod 2) := by
    conv_lhs => rw [← Nat.div_add_mod k 2]
    push_cast
    have h2 : (2 : ZMod 2) = 0 := by decide
    simp [h2]
  rw [hmod]
  have hlt : k % 2 < 2 := Nat.mod_lt k (by decide)
  interval_cases (k % 2) <;> decide

private def setBlock {m r : ℕ} (y : (Fin m × Fin r) → Bool) (i : Fin m)
    (z : Fin r → Bool) : (Fin m × Fin r) → Bool :=
  fun v => if v.1 = i then z v.2 else y v

private lemma sum_monEval_setBlock {m r : ℕ} (y : (Fin m × Fin r) → Bool) (i : Fin m)
    (mon : Finset (Fin m × Fin r)) :
    (∑ z : Fin r → Bool, monEval mon (setBlock y i z)) =
      if blockSet i ⊆ mon then monEval (mon \ blockSet i) y else 0 := by
  classical
  by_cases hsub : blockSet i ⊆ mon
  · simp only [hsub, ↓reduceIte]
    rw [Finset.sum_eq_single (fun _ : Fin r => true)]
    · unfold monEval
      have hiff : (∀ a ∈ mon, setBlock y i (fun _ => true) a = true) ↔
          ∀ a ∈ mon \ blockSet i, y a = true := by
        constructor
        · intro h a ha
          rcases Finset.mem_sdiff.mp ha with ⟨ham, hanb⟩
          have hne : a.1 ≠ i := fun heq => hanb ((mem_blockSet i a).mpr heq)
          simpa [setBlock, hne] using h a ham
        · intro h a ham
          by_cases ha1 : a.1 = i
          · simp [setBlock, ha1]
          · have hmem : a ∈ mon \ blockSet i :=
              Finset.mem_sdiff.mpr ⟨ham, fun hb => ha1 ((mem_blockSet i a).mp hb)⟩
            simpa [setBlock, ha1] using h a hmem
      by_cases h1 : ∀ a ∈ mon \ blockSet i, y a = true
      · have hp1 : (∀ a ∈ mon \ blockSet i, y a = true) ↔ True := iff_true_intro h1
        have hp2 : (∀ a ∈ mon, setBlock y i (fun _ => true) a = true) ↔ True :=
          iff_true_intro (hiff.mpr h1)
        simp only [hp1, hp2, ↓reduceIte]
      · have hp1 : (∀ a ∈ mon \ blockSet i, y a = true) ↔ False := iff_false_intro h1
        have hp2 : (∀ a ∈ mon, setBlock y i (fun _ => true) a = true) ↔ False :=
          iff_false_intro (fun h2 => h1 (hiff.mp h2))
        simp only [hp1, hp2, ↓reduceIte]
    · intro z _ hzne
      have hex : ∃ j : Fin r, z j = false := by
        by_contra hall
        push Not at hall
        apply hzne
        funext j
        cases hzj : z j
        · exact absurd hzj (hall j)
        · rfl
      rcases hex with ⟨j, hj⟩
      have hmem : (i, j) ∈ mon := hsub ((mem_blockSet i (i, j)).mpr rfl)
      have hnot : ¬ ∀ a ∈ mon, setBlock y i z a = true := by
        intro hall
        have h1 := hall (i, j) hmem
        simp [setBlock, hj] at h1
      have hp : (∀ a ∈ mon, setBlock y i z a = true) ↔ False := iff_false_intro hnot
      simp only [monEval, hp, ↓reduceIte]
    · intro hnot
      exact absurd (Finset.mem_univ _) hnot
  · simp only [hsub, ↓reduceIte]
    have hex : ∃ j : Fin r, (i, j) ∉ mon := by
      by_contra hall
      push Not at hall
      apply hsub
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨j, _, rfl⟩
      exact hall j
    rcases hex with ⟨j0, hj0⟩
    let S0 : Finset (Fin r → Bool) := Finset.univ.filter (fun z => z j0 = false)
    let S1 : Finset (Fin r → Bool) := Finset.univ.filter (fun z => z j0 = true)
    have hdisj : Disjoint S0 S1 := by
      rw [Finset.disjoint_left]
      intro z h0 h1
      have a0 := (Finset.mem_filter.mp h0).2
      have a1 := (Finset.mem_filter.mp h1).2
      rw [a0] at a1
      exact Bool.false_ne_true a1
    have hunion : S0 ∪ S1 = Finset.univ := by
      ext z
      simp only [S0, S1, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      cases z j0
      · left; rfl
      · right; rfl
    rw [← hunion, Finset.sum_union hdisj]
    have hflip : ∑ z ∈ S1, monEval mon (setBlock y i z) = ∑ z ∈ S0, monEval mon (setBlock y i z) := by
      refine Finset.sum_bij (fun z _ => Function.update z j0 false) ?_ ?_ ?_ ?_
      · intro z _
        simp [S0]
      · intro z1 hz1 z2 hz2 heq
        funext j
        by_cases hj : j = j0
        · subst hj
          exact ((Finset.mem_filter.mp hz1).2).trans ((Finset.mem_filter.mp hz2).2).symm
        · have := congrFun heq j
          simpa [Function.update, hj] using this
      · intro z hz
        refine ⟨Function.update z j0 true, by simp [S1], ?_⟩
        funext j
        by_cases hj : j = j0
        · subst hj
          simp [Function.update, (Finset.mem_filter.mp hz).2]
        · simp [Function.update, hj]
      · intro z _
        unfold monEval
        have hiff : (∀ a ∈ mon, setBlock y i z a = true) ↔
            ∀ a ∈ mon, setBlock y i (Function.update z j0 false) a = true := by
          refine forall₂_congr fun a ha => ?_
          by_cases ha1 : a.1 = i
          · have ha2 : a.2 ≠ j0 := by
              intro h2
              apply hj0
              have heq : a = (i, j0) := Prod.ext ha1 h2
              rwa [← heq]
            simp [setBlock, ha1, Function.update, ha2]
          · simp [setBlock, ha1]
        by_cases h1 : ∀ a ∈ mon, setBlock y i z a = true
        · have hp1 : (∀ a ∈ mon, setBlock y i z a = true) ↔ True := iff_true_intro h1
          have hp2 : (∀ a ∈ mon, setBlock y i (Function.update z j0 false) a = true) ↔ True :=
            iff_true_intro (hiff.mp h1)
          simp only [hp1, hp2, ↓reduceIte]
        · have hp1 : (∀ a ∈ mon, setBlock y i z a = true) ↔ False := iff_false_intro h1
          have hp2 : (∀ a ∈ mon, setBlock y i (Function.update z j0 false) a = true) ↔ False :=
            iff_false_intro (fun h2 => h1 (hiff.mpr h2))
          simp only [hp1, hp2, ↓reduceIte]
    rw [hflip, zmod2_add_self]

private lemma card_noFullBlock (m r : ℕ) :
    ((Finset.univ : Finset (Finset (Fin m × Fin r))).filter
      (fun mon => ∀ i : Fin m, ¬ blockSet i ⊆ mon)).card = (2 ^ r - 1) ^ m := by
  classical
  let nonFull : Finset (Finset (Fin r)) :=
    (Finset.univ : Finset (Finset (Fin r))).erase Finset.univ
  have hnf_card : nonFull.card = 2 ^ r - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_finset,
      Fintype.card_fin]
  have hbij :
      ((Finset.univ : Finset (Finset (Fin m × Fin r))).filter
        (fun mon => ∀ i : Fin m, ¬ blockSet i ⊆ mon)).card =
        (Fintype.piFinset (fun _ : Fin m => nonFull)).card := by
    refine Finset.card_bij
      (fun mon _ => fun i : Fin m => Finset.univ.filter (fun j : Fin r => (i, j) ∈ mon)) ?_ ?_ ?_
    · intro mon hmon
      have hno := (Finset.mem_filter.mp hmon).2
      rw [Fintype.mem_piFinset]
      intro i
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro heq
      apply hno i
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨j, _, rfl⟩
      have hmem : j ∈ Finset.univ.filter (fun j : Fin r => (i, j) ∈ mon) := by
        rw [heq]
        exact Finset.mem_univ j
      exact (Finset.mem_filter.mp hmem).2
    · intro m1 _ m2 _ heq
      ext ⟨i, j⟩
      have hi := congrFun heq i
      have hmem := Finset.ext_iff.mp hi j
      simpa using hmem
    · intro f hf
      rw [Fintype.mem_piFinset] at hf
      refine ⟨Finset.univ.filter (fun v : Fin m × Fin r => v.2 ∈ f v.1), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro i hsub
        have hne : f i ≠ Finset.univ := (Finset.mem_erase.mp (hf i)).1
        apply hne
        ext j
        simp only [Finset.mem_univ, iff_true]
        have hmem := hsub (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
        exact (Finset.mem_filter.mp hmem).2
      · funext i
        ext j
        simp
  rw [hbij, Fintype.card_piFinset]
  simp [hnf_card]

private lemma card_pointErrors {m r : ℕ} (a : Fin m → Fin r → Bool) :
    ((Finset.univ : Finset ((Fin m × Fin r) → Bool)).filter
      (fun x => ∀ i : Fin m, decide (∀ j : Fin r, x (i, j) = a i j) = false)).card =
      (2 ^ r - 1) ^ m := by
  classical
  have hbij :
      ((Finset.univ : Finset ((Fin m × Fin r) → Bool)).filter
        (fun x => ∀ i : Fin m, decide (∀ j : Fin r, x (i, j) = a i j) = false)).card =
        (Fintype.piFinset (fun i : Fin m =>
          (Finset.univ : Finset (Fin r → Bool)).erase (a i))).card := by
    refine Finset.card_bij (fun x _ => fun i j => x (i, j)) ?_ ?_ ?_
    · intro x hx
      have hbad := (Finset.mem_filter.mp hx).2
      rw [Fintype.mem_piFinset]
      intro i
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro heq
      have hall : ∀ j : Fin r, x (i, j) = a i j := fun j => congrFun heq j
      have hf := hbad i
      simp [hall] at hf
    · intro x1 _ x2 _ heq
      funext ⟨i, j⟩
      exact congrFun (congrFun heq i) j
    · intro f hf
      rw [Fintype.mem_piFinset] at hf
      refine ⟨fun v => f v.1 v.2, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro i
      have hne : f i ≠ a i := (Finset.mem_erase.mp (hf i)).1
      have hnot : ¬ ∀ j : Fin r, f i j = a i j := fun h => hne (funext h)
      simp [hnot]
  rw [hbij, Fintype.card_piFinset]
  have hterm : ∀ i : Fin m,
      ((Finset.univ : Finset (Fin r → Bool)).erase (a i)).card = 2 ^ r - 1 := by
    intro i
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin]
  rw [Finset.prod_congr rfl (fun i _ => hterm i)]
  simp

private def errFn {m r : ℕ} (terms : Fin m → Finset (Finset (Fin m × Fin r)))
    (e : Fin m → Bool) (i : Fin m) (x : (Fin m × Fin r) → Bool) : Bool :=
  xor (xor (decide (∀ j : Fin r, x (i, j) = true))
    (((terms i).filter (fun mon => ∀ a ∈ mon, x a = true)).card % 2 == 1)) (e i)

private def cErrFn {m r : ℕ} (terms : Fin m → Finset (Finset (Fin m × Fin r)))
    (e : Fin m → Bool) (i : Fin m) (s : Finset (Fin m × Fin r)) : ZMod 2 :=
  (if s = blockSet i then 1 else 0) +
  (if s ∈ terms i then 1 else 0) +
  (if s = ∅ then toZ2 (e i) else 0)

private lemma errFn_toZ2 {m r : ℕ} (terms : Fin m → Finset (Finset (Fin m × Fin r)))
    (e : Fin m → Bool) (i : Fin m) (x : (Fin m × Fin r) → Bool) :
    toZ2 (errFn terms e i x) =
      monEval (blockSet i) x + (∑ mon ∈ terms i, monEval mon x) + toZ2 (e i) := by
  unfold errFn
  rw [toZ2_xor, toZ2_xor, prodBit_toZ2, parity_filter_toZ2]

private lemma cErrFn_eval {m r : ℕ} (terms : Fin m → Finset (Finset (Fin m × Fin r)))
    (e : Fin m → Bool) (i : Fin m) (x : (Fin m × Fin r) → Bool) :
    polyEval (cErrFn terms e i) x = toZ2 (errFn terms e i x) := by
  rw [errFn_toZ2]
  unfold polyEval cErrFn
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have h1 : (∑ s : Finset (Fin m × Fin r), (if s = blockSet i then (1 : ZMod 2) else 0) * monEval s x) =
      monEval (blockSet i) x := by
    rw [Finset.sum_eq_single (blockSet i)]
    · simp
    · intro s _ hne; simp [hne]
    · intro hnot; exact absurd (Finset.mem_univ _) hnot
  have h2 : (∑ s : Finset (Fin m × Fin r), (if s ∈ terms i then (1 : ZMod 2) else 0) * monEval s x) =
      ∑ mon ∈ terms i, monEval mon x := by
    have hite : ∀ s : Finset (Fin m × Fin r),
        (if s ∈ terms i then (1 : ZMod 2) else 0) * monEval s x =
          if s ∈ terms i then monEval s x else 0 := by
      intro s; split_ifs <;> simp
    simp_rw [hite, Finset.sum_ite_mem, Finset.univ_inter]
  have h3 : (∑ s : Finset (Fin m × Fin r), (if s = ∅ then toZ2 (e i) else 0) * monEval s x) =
      toZ2 (e i) := by
    rw [Finset.sum_eq_single (∅ : Finset (Fin m × Fin r))]
    · simp only [↓reduceIte]
      rw [monEval_empty, mul_one]
    · intro s _ hne; simp [hne]
    · intro hnot; exact absurd (Finset.mem_univ _) hnot
  rw [h1, h2, h3]

private lemma cErrFn_deg {m r : ℕ} (hr : 0 < r)
    (terms : Fin m → Finset (Finset (Fin m × Fin r)))
    (hdeg : ∀ i, ∀ mon ∈ terms i, mon.card < r) (e : Fin m → Bool)
    (i : Fin m) (s : Finset (Fin m × Fin r)) (hs : cErrFn terms e i s ≠ 0) :
    s = blockSet i ∨ s.card < r := by
  by_cases hb : s = blockSet i
  · exact Or.inl hb
  · right
    by_cases ht : s ∈ terms i
    · exact hdeg i s ht
    · by_cases he : s = ∅
      · subst he; simpa using hr
      · exfalso; apply hs; simp [cErrFn, hb, ht, he]

private lemma cErrFn_top {m r : ℕ} (hr : 0 < r)
    (terms : Fin m → Finset (Finset (Fin m × Fin r)))
    (hdeg : ∀ i, ∀ mon ∈ terms i, mon.card < r) (e : Fin m → Bool) (i : Fin m) :
    cErrFn terms e i (blockSet i) = 1 := by
  have hnot_t : blockSet (r := r) i ∉ terms i := by
    intro ht
    have h1 := hdeg i _ ht
    rw [card_blockSet] at h1
    omega
  have hne_e : blockSet (r := r) i ≠ ∅ := by
    intro he
    have h1 := card_blockSet (m := m) (r := r) i
    rw [he, Finset.card_empty] at h1
    omega
  simp [cErrFn, hnot_t, hne_e]

private lemma vanish_of_noFullBlock {m r : ℕ} (hr : 0 < r)
    (terms : Fin m → Finset (Finset (Fin m × Fin r)))
    (hdeg : ∀ i, ∀ mon ∈ terms i, mon.card < r) (e : Fin m → Bool)
    (hhits : ((Finset.univ : Finset ((Fin m × Fin r) → Bool)).filter
      (fun x => ∀ i, errFn terms e i x = false)).card = (2 ^ r - 1) ^ m) :
    let S := (Finset.univ : Finset ((Fin m × Fin r) → Bool)).filter (fun x => ∀ i, errFn terms e i x = false)
    let G := (Finset.univ : Finset (Finset (Fin m × Fin r))).filter (fun mon => ∀ i : Fin m, ¬ blockSet i ⊆ mon)
    ∀ c : Finset (Fin m × Fin r) → ZMod 2,
      (∀ s, s ∉ G → c s = 0) → (∀ x ∈ S, polyEval c x = 0) → ∀ x, polyEval c x = 0 := by
  classical
  intro S G
  have hGcard : G.card = (2 ^ r - 1) ^ m := card_noFullBlock m r
  have hmon_span : ∀ k : ℕ, ∀ mon : Finset (Fin m × Fin r), mon.card = k →
      ∃ c : Finset (Fin m × Fin r) → ZMod 2, (∀ s, s ∉ G → c s = 0) ∧
        ∀ x ∈ S, monEval mon x = polyEval c x := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro mon hcard
      by_cases hG : mon ∈ G
      · refine ⟨fun s => if s = mon then 1 else 0, ?_, ?_⟩
        · intro s hs
          have hne : s ≠ mon := fun heq => hs (heq ▸ hG)
          simp [hne]
        · intro x _
          unfold polyEval
          rw [Finset.sum_eq_single mon]
          · simp
          · intro s _ hsne; simp [hsne]
          · intro hnot; exact absurd (Finset.mem_univ mon) hnot
      · have hex_i : ∃ i : Fin m, blockSet i ⊆ mon := by
          by_contra hall
          push Not at hall
          exact hG (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hall⟩)
        rcases hex_i with ⟨i, hsub⟩
        let rest := mon \ blockSet i
        have hrest_card : rest.card < k := by
          have h1 : rest.card = mon.card - (blockSet i).card := Finset.card_sdiff_of_subset hsub
          have h2 := card_blockSet (m := m) (r := r) i
          have h3 : (blockSet i).card ≤ mon.card := Finset.card_le_card hsub
          omega
        rcases ih rest.card hrest_card rest rfl with ⟨c_rest, hc_rest_G, hc_rest_eq⟩
        have hchoose_all : ∀ t : Finset (Fin m × Fin r),
            ∃ c : Finset (Fin m × Fin r) → ZMod 2, (∀ s, s ∉ G → c s = 0) ∧
              (t ∈ terms i → ∀ x ∈ S, monEval (t ∪ rest) x = polyEval c x) := by
          intro t
          by_cases ht : t ∈ terms i
          · have hlt : (t ∪ rest).card < k := by
              have h1 := Finset.card_union_le t rest
              have h2 := hdeg i t ht
              have h3 : rest.card = mon.card - (blockSet i).card := Finset.card_sdiff_of_subset hsub
              have h4 := card_blockSet (m := m) (r := r) i
              have h5 : (blockSet i).card ≤ mon.card := Finset.card_le_card hsub
              omega
            rcases ih (t ∪ rest).card hlt (t ∪ rest) rfl with ⟨c, h1, h2⟩
            exact ⟨c, h1, fun _ => h2⟩
          · exact ⟨fun _ => 0, fun _ _ => rfl, fun h => False.elim (ht h)⟩
        choose c_t hc_t_G hc_t_eq using hchoose_all
        refine ⟨fun s => (∑ t ∈ terms i, c_t t s) + toZ2 (e i) * c_rest s, ?_, ?_⟩
        · intro s hs
          dsimp only
          have h1 : ∑ t ∈ terms i, c_t t s = 0 := Finset.sum_eq_zero (fun t _ => hc_t_G t s hs)
          rw [h1, hc_rest_G s hs, mul_zero, add_zero]
        · intro x hx
          have herr0 : toZ2 (errFn terms e i x) = 0 :=
            (toZ2_eq_zero_iff _).mpr ((Finset.mem_filter.mp hx).2 i)
          have hbi_eq : monEval (blockSet i) x = (∑ t ∈ terms i, monEval t x) + toZ2 (e i) := by
            have h := errFn_toZ2 terms e i x
            rw [herr0, add_assoc] at h
            exact (zmod2_add_eq_zero_iff _ _).mp h.symm
          have hmon_union : blockSet i ∪ rest = mon := Finset.union_sdiff_of_subset hsub
          calc monEval mon x
              = monEval (blockSet i ∪ rest) x := by rw [hmon_union]
            _ = monEval (blockSet i) x * monEval rest x := (monEval_union _ _ _).symm
            _ = ((∑ t ∈ terms i, monEval t x) + toZ2 (e i)) * monEval rest x := by rw [hbi_eq]
            _ = (∑ t ∈ terms i, monEval (t ∪ rest) x) + toZ2 (e i) * monEval rest x := by
                  rw [add_mul, Finset.sum_mul]
                  congr 1
                  exact Finset.sum_congr rfl (fun t _ => monEval_union t rest x)
            _ = (∑ t ∈ terms i, polyEval (c_t t) x) + toZ2 (e i) * polyEval c_rest x := by
                  rw [hc_rest_eq x hx]
                  congr 1
                  exact Finset.sum_congr rfl (fun t ht => hc_t_eq t ht x hx)
            _ = polyEval (fun s => (∑ t ∈ terms i, c_t t s) + toZ2 (e i) * c_rest s) x := by
                  rw [polyEval_add, polyEval_smul]
                  congr 1
                  unfold polyEval
                  simp_rw [Finset.sum_mul]
                  exact Finset.sum_comm
  let evalS : ({s : Finset (Fin m × Fin r) // s ∈ G} → ZMod 2) →
      ({x : (Fin m × Fin r) → Bool // x ∈ S} → ZMod 2) :=
    fun d x => ∑ s : {s : Finset (Fin m × Fin r) // s ∈ G}, d s * monEval s.1 x.1
  have hsurj : Function.Surjective evalS := by
    intro f
    let fExt : ((Fin m × Fin r) → Bool) → ZMod 2 := fun x => if hx : x ∈ S then f ⟨x, hx⟩ else 0
    rcases polyEval_surjective m r fExt with ⟨c0, hc0⟩
    choose cm hcm_G hcm_eq using (fun mon : Finset (Fin m × Fin r) => hmon_span mon.card mon rfl)
    refine ⟨fun s => ∑ mon : Finset (Fin m × Fin r), c0 mon * cm mon s.1, ?_⟩
    funext ⟨x, hx⟩
    have hfval : f ⟨x, hx⟩ = polyEval c0 x := by
      have := congrFun hc0 x
      simp only [fExt, hx, ↓reduceDIte] at this
      exact this.symm
    rw [hfval]
    unfold polyEval
    dsimp only [evalS]
    have hstep1 : (∑ mon : Finset (Fin m × Fin r), c0 mon * monEval mon x) =
        ∑ mon : Finset (Fin m × Fin r), c0 mon * ∑ s ∈ G, cm mon s * monEval s x := by
      refine Finset.sum_congr rfl ?_
      intro mon _
      rw [hcm_eq mon x hx]
      congr 1
      unfold polyEval
      symm
      refine Finset.sum_subset (Finset.subset_univ G) ?_
      intro s _ hs
      rw [hcm_G mon s hs, zero_mul]
    rw [hstep1]
    have hstep2 :
        (∑ s : {s : Finset (Fin m × Fin r) // s ∈ G},
          (∑ mon : Finset (Fin m × Fin r), c0 mon * cm mon s.1) * monEval s.1 x) =
        ∑ s ∈ G, (∑ mon : Finset (Fin m × Fin r), c0 mon * cm mon s) * monEval s x :=
      Finset.sum_coe_sort G (fun s =>
        (∑ mon : Finset (Fin m × Fin r), c0 mon * cm mon s) * monEval s x)
    rw [hstep2]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro mon _
    refine Finset.sum_congr rfl ?_
    intro s _
    exact mul_assoc (c0 mon) (cm mon s) (monEval s x)
  have hinj : Function.Injective evalS := by
    have hScard : S.card = (2 ^ r - 1) ^ m := hhits
    have hbij : Function.Bijective evalS := by
      rw [Fintype.bijective_iff_surjective_and_card]
      refine ⟨hsurj, ?_⟩
      simp [hGcard, hScard]
    exact hbij.1
  intro c hcG hcS
  have hres : evalS (fun s => c s.1) = evalS (fun _ => 0) := by
    funext ⟨x, hx⟩
    dsimp only [evalS]
    simp only [zero_mul, Finset.sum_const_zero]
    have hsum_G :
        (∑ s : {s : Finset (Fin m × Fin r) // s ∈ G}, c s.1 * monEval s.1 x) = polyEval c x := by
      rw [Finset.sum_coe_sort G (fun s => c s * monEval s x)]
      unfold polyEval
      refine Finset.sum_subset (Finset.subset_univ G) ?_
      intro s _ hs
      rw [hcG s hs, zero_mul]
    rw [hsum_G, hcS x hx]
  have heq_sub := hinj hres
  intro x
  unfold polyEval
  refine Finset.sum_eq_zero ?_
  intro s _
  by_cases hs : s ∈ G
  · have h0 : c s = 0 := congrFun heq_sub ⟨s, hs⟩
    rw [h0, zero_mul]
  · rw [hcG s hs, zero_mul]

private lemma forced_bit_of_vanish {m r : ℕ} (hr : 0 < r)
    (terms : Fin m → Finset (Finset (Fin m × Fin r)))
    (hdeg : ∀ i, ∀ mon ∈ terms i, mon.card < r) (e : Fin m → Bool)
    (hvanish : ∀ c : Finset (Fin m × Fin r) → ZMod 2,
      (∀ s, s ∉ (Finset.univ : Finset (Finset (Fin m × Fin r))).filter (fun mon => ∀ i : Fin m, ¬ blockSet i ⊆ mon) → c s = 0) →
      (∀ x ∈ (Finset.univ : Finset ((Fin m × Fin r) → Bool)).filter (fun x => ∀ i, errFn terms e i x = false), polyEval c x = 0) →
      ∀ x, polyEval c x = 0)
    (i : Fin m) (j : Fin r) (x : (Fin m × Fin r) → Bool) (herr_x : errFn terms e i x = true) :
    x (i, j) = decide ((1 : ZMod 2) + cErrFn terms e i ((blockSet i).erase (i, j)) = 1) := by
  classical
  let bij : ZMod 2 := cErrFn terms e i ((blockSet i).erase (i, j))
  let d : Finset (Fin m × Fin r) → ZMod 2 := fun s =>
    (if (i, j) ∈ s then cErrFn terms e i s + cErrFn terms e i (s.erase (i, j)) else 0) +
      (1 + bij) * cErrFn terms e i s
  have hd_eval : ∀ y : (Fin m × Fin r) → Bool,
      polyEval d y = (toZ2 (y (i, j)) + (1 + bij)) * toZ2 (errFn terms e i y) := by
    intro y
    rw [← cErrFn_eval terms e i y, ← monEval_singleton (i, j) y, add_mul]
    have hpart1 :
        (∑ s : Finset (Fin m × Fin r),
          (if (i, j) ∈ s then cErrFn terms e i s + cErrFn terms e i (s.erase (i, j)) else 0) * monEval s y) =
        monEval {(i, j)} y * polyEval (cErrFn terms e i) y := by
      unfold polyEval
      rw [Finset.mul_sum]
      have hstep : ∀ s : Finset (Fin m × Fin r),
          monEval {(i, j)} y * (cErrFn terms e i s * monEval s y) =
            cErrFn terms e i s * monEval (insert (i, j) s) y := by
        intro s
        rw [mul_left_comm, monEval_union, Finset.singleton_union]
      simp_rw [hstep]
      conv_rhs =>
        rw [← Finset.sum_fiberwise_of_maps_to (g := fun s : Finset (Fin m × Fin r) => insert (i, j) s)
          (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
      refine Finset.sum_congr rfl ?_
      intro s _
      by_cases hmem : (i, j) ∈ s
      · simp only [hmem, ↓reduceIte]
        have hfib : (Finset.univ : Finset (Finset (Fin m × Fin r))).filter (fun t => insert (i, j) t = s) =
            {s, s.erase (i, j)} := by
          ext t
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
            Finset.mem_singleton]
          constructor
          · intro hins
            by_cases ht : (i, j) ∈ t
            · left; rwa [Finset.insert_eq_of_mem ht] at hins
            · right; rw [← hins, Finset.erase_insert ht]
          · rintro (rfl | rfl)
            · exact Finset.insert_eq_of_mem hmem
            · exact Finset.insert_erase hmem
        have hne : s ≠ s.erase (i, j) := by
          intro h
          have hm : (i, j) ∈ s.erase (i, j) := h ▸ hmem
          exact (Finset.mem_erase.mp hm).1 rfl
        rw [hfib, Finset.sum_pair hne, Finset.insert_eq_of_mem hmem, Finset.insert_erase hmem, add_mul]
      · simp only [hmem, ↓reduceIte, zero_mul]
        have hemp : (Finset.univ : Finset (Finset (Fin m × Fin r))).filter (fun t => insert (i, j) t = s) = ∅ := by
          ext t
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          intro hins
          exact hmem (hins ▸ Finset.mem_insert_self (i, j) t)
        rw [hemp, Finset.sum_empty]
    have hsplit : polyEval d y =
        (∑ s : Finset (Fin m × Fin r),
          (if (i, j) ∈ s then cErrFn terms e i s + cErrFn terms e i (s.erase (i, j)) else 0) * monEval s y) +
        (∑ s : Finset (Fin m × Fin r), ((1 + bij) * cErrFn terms e i s) * monEval s y) := by
      unfold polyEval
      dsimp only [d]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun s _ => add_mul _ _ _)
    have hpart2 : (∑ s : Finset (Fin m × Fin r), ((1 + bij) * cErrFn terms e i s) * monEval s y) =
        (1 + bij) * polyEval (cErrFn terms e i) y :=
      polyEval_smul (1 + bij) (cErrFn terms e i) y
    rw [hsplit, hpart1, hpart2]
  have hd_G : ∀ s, s ∉ (Finset.univ : Finset (Finset (Fin m × Fin r))).filter (fun mon => ∀ i : Fin m, ¬ blockSet i ⊆ mon) →
      d s = 0 := by
    intro s hs
    have hex : ∃ i' : Fin m, blockSet i' ⊆ s := by
      by_contra hall
      push Not at hall
      exact hs (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hall⟩)
    rcases hex with ⟨i', hsub'⟩
    by_cases hsi : s = blockSet i
    · subst hsi
      have hmem : (i, j) ∈ blockSet i := (mem_blockSet i (i, j)).mpr rfl
      dsimp only [d]
      simp only [hmem, ↓reduceIte, cErrFn_top hr terms hdeg e i, mul_one]
      exact zmod2_add_self (1 + bij)
    · have hcs0 : cErrFn terms e i s = 0 := by
        by_contra hne
        rcases cErrFn_deg hr terms hdeg e i s hne with heq | hlt
        · exact hsi heq
        · have hle : (blockSet i').card ≤ s.card := Finset.card_le_card hsub'
          rw [card_blockSet] at hle
          omega
      have hcer0 : (i, j) ∈ s → cErrFn terms e i (s.erase (i, j)) = 0 := by
        intro hmem
        by_contra hne
        rcases cErrFn_deg hr terms hdeg e i (s.erase (i, j)) hne with heq | hlt
        · have hmem_er : (i, j) ∈ s.erase (i, j) := by
            rw [heq]; exact (mem_blockSet i (i, j)).mpr rfl
          exact (Finset.mem_erase.mp hmem_er).1 rfl
        · have hcard_s : s.card ≤ r := by
            have := Finset.card_erase_of_mem hmem
            have hpos : 1 ≤ s.card := Finset.one_le_card.mpr ⟨(i, j), hmem⟩
            omega
          have hle : (blockSet i').card ≤ s.card := Finset.card_le_card hsub'
          rw [card_blockSet] at hle
          have hseq : s = blockSet i' :=
            (Finset.eq_of_subset_of_card_le hsub' (by rw [card_blockSet]; omega)).symm
          have hii' : i = i' := (mem_blockSet i' (i, j)).mp (hseq ▸ hmem)
          subst hii'
          exact hsi hseq
      dsimp only [d]
      by_cases hmem : (i, j) ∈ s
      · simp [hmem, hcs0, hcer0 hmem]
      · simp [hmem, hcs0]
  have hd_S : ∀ y ∈ (Finset.univ : Finset ((Fin m × Fin r) → Bool)).filter (fun y => ∀ i, errFn terms e i y = false),
      polyEval d y = 0 := by
    intro y hy
    rw [hd_eval y, (toZ2_eq_zero_iff _).mpr ((Finset.mem_filter.mp hy).2 i), mul_zero]
  have h0 := hvanish d hd_G hd_S x
  rw [hd_eval x, (toZ2_eq_one_iff _).mpr herr_x, mul_one] at h0
  have hxe : toZ2 (x (i, j)) = 1 + bij := (zmod2_add_eq_zero_iff _ _).mp h0
  rcases zmod2_eq_zero_or_one (1 + bij) with hval | hval
  · rw [hval] at hxe ⊢
    rw [(toZ2_eq_zero_iff _).mp hxe]
    decide
  · rw [hval] at hxe ⊢
    rw [(toZ2_eq_one_iff _).mp hxe]
    decide

private lemma slice_sum_errFn {m r : ℕ} (hr : 0 < r)
    (terms : Fin m → Finset (Finset (Fin m × Fin r)))
    (hdeg : ∀ i, ∀ mon ∈ terms i, mon.card < r) (e : Fin m → Bool)
    (i : Fin m) (x : (Fin m × Fin r) → Bool) :
    (∑ z : Fin r → Bool, toZ2 (errFn terms e i (setBlock x i z))) = 1 := by
  classical
  simp_rw [← cErrFn_eval terms e i]
  unfold polyEval
  rw [Finset.sum_comm]
  have hterm : ∀ mon : Finset (Fin m × Fin r),
      (∑ z : Fin r → Bool, cErrFn terms e i mon * monEval mon (setBlock x i z)) =
        if mon = blockSet i then 1 else 0 := by
    intro mon
    rw [← Finset.mul_sum, sum_monEval_setBlock]
    by_cases heq : mon = blockSet i
    · subst heq
      simp only [subset_refl, ↓reduceIte, Finset.sdiff_self, monEval_empty,
        cErrFn_top hr terms hdeg e i, mul_one]
    · simp only [heq, ↓reduceIte]
      by_cases hsub : blockSet i ⊆ mon
      · have hc0 : cErrFn terms e i mon = 0 := by
          by_contra hne
          rcases cErrFn_deg hr terms hdeg e i mon hne with h1 | h2
          · exact heq h1
          · have hle : (blockSet i).card ≤ mon.card := Finset.card_le_card hsub
            rw [card_blockSet] at hle
            omega
        simp [hc0]
      · simp [hsub]
  rw [Finset.sum_congr rfl (fun mon _ => hterm mon), Finset.sum_eq_single (blockSet i)]
  · simp
  · intro mon _ hne; simp [hne]
  · intro hnot; exact absurd (Finset.mem_univ _) hnot

end PEqualNP.Outside.L_lib_587_aux

theorem PEqualNP.Outside.L_lib_587 : ∀ (m r : ℕ), 0 < r →
  let V := Fin m × Fin r
  let W := V → Bool
  let low := fun (f : W → Bool) =>
    ∃ terms : Finset (Finset V), (∀ mon ∈ terms, mon.card < r) ∧
      ∀ x, f x = (((terms.filter (fun mon => ∀ a ∈ mon, x a = true)).card % 2) == 1)
  let prodBit := fun (x : W) (i : Fin m) => decide (∀ j : Fin r, x (i,j) = true)
  ∀ (P : Fin m → W → Bool), (∀ i, low (P i)) →
  ∀ e : Fin m → Bool,
    let err := fun (i : Fin m) (x : W) => xor (xor (prodBit x i) (P i x)) (e i)
    let hits := ((Finset.univ : Finset W).filter (fun x => ∀ i, err i x = false)).card
    let pointErrors := ∃ a : Fin m → Fin r → Bool, ∀ i x,
      err i x = decide (∀ j : Fin r, x (i,j) = a i j)
    (hits = (2^r - 1)^m ↔ pointErrors) := by
  classical
  intro m r hr V W low prodBit P hP e err hits pointErrors
  constructor
  · intro hhits
    choose terms hdeg heval using hP
    have herr_eq : ∀ i x, err i x = PEqualNP.Outside.L_lib_587_aux.errFn terms e i x := by
      intro i x
      dsimp only [err, prodBit, PEqualNP.Outside.L_lib_587_aux.errFn]
      rw [heval i x]
    have hhits' : ((Finset.univ : Finset W).filter
        (fun x => ∀ i, PEqualNP.Outside.L_lib_587_aux.errFn terms e i x = false)).card =
        (2 ^ r - 1) ^ m := by
      simpa only [← herr_eq] using hhits
    have hvanish := PEqualNP.Outside.L_lib_587_aux.vanish_of_noFullBlock hr terms hdeg e hhits'
    let a : Fin m → Fin r → Bool := fun i j =>
      decide ((1 : ZMod 2) + PEqualNP.Outside.L_lib_587_aux.cErrFn terms e i
        ((PEqualNP.Outside.L_lib_587_aux.blockSet i).erase (i, j)) = 1)
    refine ⟨a, fun i x => ?_⟩
    rw [herr_eq i x]
    by_cases hmatch : ∀ j : Fin r, x (i, j) = a i j
    · rw [decide_eq_true hmatch]
      have hsum := PEqualNP.Outside.L_lib_587_aux.slice_sum_errFn hr terms hdeg e i x
      have hex_z : ∃ z : Fin r → Bool,
          PEqualNP.Outside.L_lib_587_aux.errFn terms e i (PEqualNP.Outside.L_lib_587_aux.setBlock x i z) = true := by
        by_contra hall
        push Not at hall
        have h0 : (∑ z : Fin r → Bool,
            PEqualNP.Outside.L_lib_587_aux.toZ2
              (PEqualNP.Outside.L_lib_587_aux.errFn terms e i (PEqualNP.Outside.L_lib_587_aux.setBlock x i z))) = 0 := by
          refine Finset.sum_eq_zero ?_
          intro z _
          have hf : PEqualNP.Outside.L_lib_587_aux.errFn terms e i (PEqualNP.Outside.L_lib_587_aux.setBlock x i z) = false := by
            cases h : PEqualNP.Outside.L_lib_587_aux.errFn terms e i (PEqualNP.Outside.L_lib_587_aux.setBlock x i z)
            · rfl
            · exact absurd h (hall z)
          exact (PEqualNP.Outside.L_lib_587_aux.toZ2_eq_zero_iff _).mpr hf
        rw [h0] at hsum
        exact absurd hsum (by decide)
      rcases hex_z with ⟨z, hz⟩
      have hzx : PEqualNP.Outside.L_lib_587_aux.setBlock x i z = x := by
        funext ⟨i', j⟩
        by_cases hi : i' = i
        · subst i'
          have hz_eq := PEqualNP.Outside.L_lib_587_aux.forced_bit_of_vanish hr terms hdeg e hvanish
            i j (PEqualNP.Outside.L_lib_587_aux.setBlock x i z) hz
          simp only [PEqualNP.Outside.L_lib_587_aux.setBlock, ↓reduceIte] at hz_eq ⊢
          exact hz_eq.trans (hmatch j).symm
        · simp [PEqualNP.Outside.L_lib_587_aux.setBlock, hi]
      rwa [hzx] at hz
    · rw [decide_eq_false hmatch]
      cases hval : PEqualNP.Outside.L_lib_587_aux.errFn terms e i x
      · rfl
      · exfalso
        exact hmatch (fun j =>
          PEqualNP.Outside.L_lib_587_aux.forced_bit_of_vanish hr terms hdeg e hvanish i j x hval)
  · rintro ⟨a, ha⟩
    dsimp only [hits]
    have hfilt : (Finset.univ : Finset W).filter (fun x => ∀ i, err i x = false) =
        (Finset.univ : Finset W).filter (fun x => ∀ i : Fin m, decide (∀ j : Fin r, x (i, j) = a i j) = false) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, ha]
    rw [hfilt]
    exact PEqualNP.Outside.L_lib_587_aux.card_pointErrors a
