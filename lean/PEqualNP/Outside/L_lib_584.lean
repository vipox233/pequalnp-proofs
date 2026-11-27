import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_584_aux

def fullBlocks {m r : Nat} (x : (Fin m × Fin r) → Bool) : Finset (Fin m) :=
  (Finset.univ : Finset (Fin m)).filter (fun i => ∀ j : Fin r, x (i, j) = true)

def extremalSet (m r k : Nat) : Finset ((Fin m × Fin r) → Bool) :=
  (Finset.univ : Finset ((Fin m × Fin r) → Bool)).filter (fun x => (fullBlocks x).card < k)

def goodMonomials (m r k : Nat) : Finset (Finset (Fin m × Fin r)) :=
  (Finset.univ : Finset (Finset (Fin m × Fin r))).filter (fun mon =>
    ((Finset.univ : Finset (Fin m)).filter (fun i => ∀ j : Fin r, (i, j) ∈ mon)).card < k)

def budgetVal (m r k : Nat) : Nat :=
  (Finset.range (m + 1)).sum (fun j =>
    if j < k then Nat.choose m j * (2 ^ r - 1) ^ (m - j) else 0)

def nonFull (r : Nat) : Finset (Fin r → Bool) :=
  (Finset.univ : Finset (Fin r → Bool)).erase (fun _ => true)

lemma mem_nonFull {r : Nat} (f : Fin r → Bool) :
    f ∈ nonFull r ↔ ¬ (∀ j : Fin r, f j = true) := by
  simp only [nonFull, Finset.mem_erase, Finset.mem_univ, and_true, ne_eq]
  constructor
  · intro h hall
    apply h
    funext j
    exact hall j
  · intro h heq
    apply h
    intro j
    simpa using congrFun heq j

lemma card_nonFull (r : Nat) : (nonFull r).card = 2 ^ r - 1 := by
  have hmem : (fun _ : Fin r => true) ∈ (Finset.univ : Finset (Fin r → Bool)) := Finset.mem_univ _
  rw [nonFull, Finset.card_erase_of_mem hmem, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin]

def fiberEquiv {m r : Nat} (J : Finset (Fin m)) :
    { x : (Fin m × Fin r) → Bool // fullBlocks x = J } ≃
      ({ i : Fin m // i ∉ J } → { f : Fin r → Bool // f ∈ nonFull r }) where
  toFun := fun x i =>
    ⟨fun j => x.1 (i.1, j), by
      rw [mem_nonFull]
      intro hall
      have hmem : i.1 ∈ fullBlocks x.1 := by
        simp [fullBlocks, hall]
      rw [x.2] at hmem
      exact i.2 hmem⟩
  invFun := fun g =>
    ⟨fun p => if h : p.1 ∈ J then true else (g ⟨p.1, h⟩).1 p.2, by
      ext i
      simp only [fullBlocks, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hi : i ∈ J
      · simp [hi]
      · simp only [hi, ↓reduceDIte, iff_false]
        exact (mem_nonFull (g ⟨i, hi⟩).1).mp (g ⟨i, hi⟩).2⟩
  left_inv := fun x => by
    apply Subtype.ext
    funext p
    by_cases hp : p.1 ∈ J
    · simp only [hp, ↓reduceDIte]
      have hmem : p.1 ∈ fullBlocks x.1 := by
        rw [x.2]
        exact hp
      simp only [fullBlocks, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      exact (hmem p.2).symm
    · simp [hp]
  right_inv := fun g => by
    funext i
    apply Subtype.ext
    funext j
    simp [i.2]

lemma card_fiber {m r : Nat} (J : Finset (Fin m)) :
    ((Finset.univ : Finset ((Fin m × Fin r) → Bool)).filter (fun x => fullBlocks x = J)).card =
      (2 ^ r - 1) ^ (m - J.card) := by
  have h1 :
      ((Finset.univ : Finset ((Fin m × Fin r) → Bool)).filter (fun x => fullBlocks x = J)).card =
        Fintype.card { x : (Fin m × Fin r) → Bool // fullBlocks x = J } := by
    rw [Fintype.card_subtype]
  rw [h1, Fintype.card_congr (fiberEquiv J), Fintype.card_fun, Fintype.card_coe, card_nonFull]
  have h2 : Fintype.card { i : Fin m // i ∉ J } = m - J.card := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin]
  rw [h2]

lemma card_extremalSet (m r k : Nat) : (extremalSet m r k).card = budgetVal m r k := by
  let s : Finset (Finset (Fin m)) :=
    (Finset.univ : Finset (Finset (Fin m))).filter (fun J => J.card < k)
  have hmaps : ∀ x ∈ extremalSet m r k, fullBlocks x ∈ s := by
    intro x hx
    simp only [extremalSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp [s, hx]
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfib : ∀ J ∈ s,
      ((extremalSet m r k).filter (fun x => fullBlocks x = J)).card =
        (2 ^ r - 1) ^ (m - J.card) := by
    intro J hJ
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hJ
    have hset :
        (extremalSet m r k).filter (fun x => fullBlocks x = J) =
          (Finset.univ : Finset ((Fin m × Fin r) → Bool)).filter (fun x => fullBlocks x = J) := by
      ext x
      simp only [extremalSet, Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
      intro hx
      rw [hx]
      exact hJ
    rw [hset, card_fiber]
  rw [Finset.sum_congr rfl hfib]
  have hmaps2 : ∀ J ∈ s, J.card ∈ Finset.range (m + 1) := by
    intro J _
    rw [Finset.mem_range]
    have hle : J.card ≤ m := by
      simpa using Finset.card_le_univ J
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps2]
  rw [budgetVal]
  refine Finset.sum_congr rfl ?_
  intro j _
  by_cases hj : j < k
  · simp only [hj, ↓reduceIte]
    have hsub : s.filter (fun J => J.card = j) =
        (Finset.univ : Finset (Fin m)).powersetCard j := by
      ext J
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard,
        Finset.subset_univ]
      constructor
      · intro h
        exact h.2
      · intro h
        exact ⟨h.symm ▸ hj, h⟩
    rw [hsub]
    have hconst :
        ∀ J ∈ (Finset.univ : Finset (Fin m)).powersetCard j,
          (2 ^ r - 1) ^ (m - J.card) = (2 ^ r - 1) ^ (m - j) := by
      intro J hJ
      rw [(Finset.mem_powersetCard.mp hJ).2]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul,
      Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  · simp only [hj, ↓reduceIte]
    have hemp : s.filter (fun J => J.card = j) = ∅ := by
      ext J
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rintro ⟨hlt, heq⟩
      exact hj (heq ▸ hlt)
    rw [hemp, Finset.sum_empty]

lemma card_goodMonomials (m r k : Nat) : (goodMonomials m r k).card = budgetVal m r k := by
  rw [← card_extremalSet]
  refine Finset.card_bij (fun mon _ => fun p => decide (p ∈ mon)) ?_ ?_ ?_
  · intro mon hmon
    rw [goodMonomials, Finset.mem_filter] at hmon
    rw [extremalSet, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa [fullBlocks] using hmon.2
  · intro mon1 _ mon2 _ h
    ext p
    have hp := congrFun h p
    simpa [decide_eq_decide] using hp
  · intro x hx
    refine ⟨(Finset.univ : Finset (Fin m × Fin r)).filter (fun p => x p = true), ?_, ?_⟩
    · rw [extremalSet, Finset.mem_filter] at hx
      rw [goodMonomials, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa [fullBlocks] using hx.2
    · funext p
      cases hxp : x p <;> simp [hxp]

def boolToZMod2 (b : Bool) : ZMod 2 :=
  if b = true then 1 else 0

lemma boolToZMod2_par (z : Nat) : boolToZMod2 (z % 2 == 1) = (z : ZMod 2) := by
  have hdiv : z = 2 * (z / 2) + z % 2 := (Nat.div_add_mod z 2).symm
  have hz : (z : ZMod 2) = ((z % 2 : Nat) : ZMod 2) := by
    conv_lhs => rw [hdiv]
    push_cast
    have h2 : (2 : ZMod 2) = 0 := by decide
    simp [h2]
  rw [hz]
  have hlt : z % 2 < 2 := Nat.mod_lt z (by decide)
  interval_cases (z % 2) <;> decide

def ev {m r : Nat} (S : Finset ((Fin m × Fin r) → Bool))
    (mon : Finset (Fin m × Fin r)) : { x : (Fin m × Fin r) → Bool // x ∈ S } → ZMod 2 :=
  fun x => if ∀ p ∈ mon, x.1 p = true then 1 else 0

lemma ev_empty {m r : Nat} (S : Finset ((Fin m × Fin r) → Bool)) :
    ev S ∅ = 1 := by
  funext x
  simp [ev]

lemma ev_union {m r : Nat} (S : Finset ((Fin m × Fin r) → Bool))
    (A B : Finset (Fin m × Fin r)) :
    ev S (A ∪ B) = ev S A * ev S B := by
  funext x
  simp only [ev, Pi.mul_apply, Finset.mem_union]
  by_cases hA : ∀ p ∈ A, x.1 p = true
  · by_cases hB : ∀ p ∈ B, x.1 p = true
    · have hAB : ∀ p, p ∈ A ∨ p ∈ B → x.1 p = true := by
        rintro p (hp | hp)
        · exact hA p hp
        · exact hB p hp
      simp only [eq_true hA, eq_true hB, eq_true hAB, ↓reduceIte, mul_one]
    · have hAB : ¬ (∀ p, p ∈ A ∨ p ∈ B → x.1 p = true) := by
        intro h
        exact hB (fun p hp => h p (Or.inr hp))
      simp only [eq_false hB, eq_false hAB, ↓reduceIte, mul_zero]
  · have hAB : ¬ (∀ p, p ∈ A ∨ p ∈ B → x.1 p = true) := by
      intro h
      exact hA (fun p hp => h p (Or.inl hp))
    simp only [eq_false hA, eq_false hAB, ↓reduceIte, zero_mul]

def blockSet (r : Nat) {m : Nat} (I : Finset (Fin m)) : Finset (Fin m × Fin r) :=
  I ×ˢ (Finset.univ : Finset (Fin r))

lemma ev_blockSet_eq_sum {m r : Nat} (S : Finset ((Fin m × Fin r) → Bool))
    (I : Finset (Fin m)) (terms : Finset (Finset (Fin m × Fin r)))
    (hq : ∀ x ∈ S,
      ((terms.filter (fun mon => ∀ p ∈ mon, x p = true)).card % 2 == 1) =
        decide (∀ i ∈ I, ∀ j : Fin r, x (i, j) = true)) :
    ev S (blockSet r I) = ∑ mon ∈ terms, ev S mon := by
  funext x
  rw [Finset.sum_apply]
  have h1 : ev S (blockSet r I) x =
      boolToZMod2 (decide (∀ i ∈ I, ∀ j : Fin r, x.1 (i, j) = true)) := by
    have hiff : (∀ p ∈ blockSet r I, x.1 p = true) ↔
        (∀ i ∈ I, ∀ j : Fin r, x.1 (i, j) = true) := by
      constructor
      · intro h i hi j
        exact h (i, j) (Finset.mem_product.mpr ⟨hi, Finset.mem_univ j⟩)
      · intro h p hp
        rcases Finset.mem_product.mp hp with ⟨hi, _⟩
        exact h p.1 hi p.2
    simp only [ev, boolToZMod2, decide_eq_true_eq, hiff]
  rw [h1, ← hq x.1 x.2, boolToZMod2_par]
  simp only [ev, Finset.sum_boole]

def spanMap {m r k : Nat} (S : Finset ((Fin m × Fin r) → Bool)) :
    ({ g : Finset (Fin m × Fin r) // g ∈ goodMonomials m r k } → ZMod 2) →ₗ[ZMod 2]
      ({ x : (Fin m × Fin r) → Bool // x ∈ S } → ZMod 2) where
  toFun := fun c => ∑ g : { g // g ∈ goodMonomials m r k }, c g • ev S g.1
  map_add' := fun c1 c2 => by
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' := fun a c => by
    simp [mul_smul, Finset.smul_sum]

lemma ev_good_mem_range {m r k : Nat} (S : Finset ((Fin m × Fin r) → Bool))
    (g : Finset (Fin m × Fin r)) (hg : g ∈ goodMonomials m r k) :
    ev S g ∈ LinearMap.range (spanMap (m := m) (r := r) (k := k) S) := by
  refine ⟨fun h => if h = ⟨g, hg⟩ then 1 else 0, ?_⟩
  simp [spanMap]

lemma card_le_budget {m r k : Nat} (hr : 0 < r) (hk : 0 < k)
    (S : Finset ((Fin m × Fin r) → Bool))
    (hS : ∀ I : Finset (Fin m), I.card = k →
      ∃ q : ((Fin m × Fin r) → Bool) → Bool,
        (∃ terms : Finset (Finset (Fin m × Fin r)),
          (∀ mon ∈ terms, mon.card ≤ r * k - 1) ∧
          ∀ word, q word = ((terms.filter (fun mon => ∀ j ∈ mon, word j = true)).card % 2 == 1)) ∧
        ∀ x ∈ S, q x = decide (∀ i ∈ I, ∀ j : Fin r, x (i, j) = true)) :
    S.card ≤ budgetVal m r k := by
  let L := spanMap (m := m) (r := r) (k := k) S
  let U := LinearMap.range L
  have hev_mem : ∀ n : Nat, ∀ mon : Finset (Fin m × Fin r), mon.card = n → ev S mon ∈ U := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro mon hcard
      by_cases hgood : mon ∈ goodMonomials m r k
      · exact ev_good_mem_range S mon hgood
      · let J : Finset (Fin m) :=
          (Finset.univ : Finset (Fin m)).filter (fun i => ∀ j : Fin r, (i, j) ∈ mon)
        have hJge : k ≤ J.card := by
          simp only [goodMonomials, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hgood
          exact hgood
        obtain ⟨I, hIJ, hIcard⟩ := Finset.exists_subset_card_eq hJge
        let B := blockSet r I
        have hBsub : B ⊆ mon := by
          intro p hp
          rcases Finset.mem_product.mp hp with ⟨hi, _⟩
          have hiJ : p.1 ∈ J := hIJ hi
          simp only [J, Finset.mem_filter, Finset.mem_univ, true_and] at hiJ
          exact hiJ p.2
        have hBcard : B.card = r * k := by
          simp [B, blockSet, Finset.card_product, hIcard, Nat.mul_comm]
        let R := mon \ B
        have hBR : B ∪ R = mon := Finset.union_sdiff_of_subset hBsub
        have hdisj : Disjoint B R := Finset.disjoint_sdiff
        have hcardBR : B.card + R.card = mon.card := by
          rw [← Finset.card_union_of_disjoint hdisj, hBR]
        obtain ⟨q, ⟨terms, hdeg, hqpar⟩, hqS⟩ := hS I hIcard
        have hBeq : ev S B = ∑ t ∈ terms, ev S t := by
          apply ev_blockSet_eq_sum S I terms
          intro x hx
          rw [← hqpar x, hqS x hx]
        have hmonEq : ev S mon = ∑ t ∈ terms, ev S (t ∪ R) := by
          rw [← hBR, ev_union, hBeq, Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro t _
          rw [ev_union]
        rw [hmonEq]
        refine U.sum_mem ?_
        intro t ht
        have htcard : t.card ≤ r * k - 1 := hdeg t ht
        have hrk : 0 < r * k := Nat.mul_pos hr hk
        have hlt : (t ∪ R).card < n := by
          have hu : (t ∪ R).card ≤ t.card + R.card := Finset.card_union_le t R
          omega
        exact ih (t ∪ R).card hlt (t ∪ R) rfl
  have hfactor : ∀ (x : { x : (Fin m × Fin r) → Bool // x ∈ S })
      (T A : Finset (Fin m × Fin r)),
      (∏ p ∈ T, (if x.1 p = true then ev S {p} else 1 + ev S {p})) * ev S A ∈ U := by
    intro x T
    induction T using Finset.induction_on with
    | empty =>
      intro A
      simpa using hev_mem A.card A rfl
    | @insert p T hp ih =>
      intro A
      rw [Finset.prod_insert hp]
      have hassoc :
          (if x.1 p = true then ev S {p} else 1 + ev S {p}) *
              (∏ q ∈ T, (if x.1 q = true then ev S {q} else 1 + ev S {q})) * ev S A =
            (∏ q ∈ T, (if x.1 q = true then ev S {q} else 1 + ev S {q})) *
              ((if x.1 p = true then ev S {p} else 1 + ev S {p}) * ev S A) := by
        ring
      rw [hassoc]
      cases hxp : x.1 p
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [add_mul, one_mul, ← ev_union, mul_add]
        exact U.add_mem (ih A) (ih ({p} ∪ A))
      · simp only [↓reduceIte]
        rw [← ev_union]
        exact ih ({p} ∪ A)
  have hdelta : ∀ x : { x : (Fin m × Fin r) → Bool // x ∈ S },
      (fun y : { y : (Fin m × Fin r) → Bool // y ∈ S } => if y = x then (1 : ZMod 2) else 0) ∈ U := by
    intro x
    have heq :
        (fun y : { y : (Fin m × Fin r) → Bool // y ∈ S } => if y = x then (1 : ZMod 2) else 0) =
          (∏ p ∈ (Finset.univ : Finset (Fin m × Fin r)),
            (if x.1 p = true then ev S {p} else 1 + ev S {p})) * ev S ∅ := by
      rw [ev_empty, mul_one]
      funext y
      rw [Finset.prod_apply]
      by_cases hyx : y = x
      · subst hyx
        simp only [↓reduceIte]
        symm
        refine Finset.prod_eq_one ?_
        intro p _
        cases hxp : y.1 p
        · simp [ev, hxp]
        · simp [ev, hxp]
      · simp only [hyx, ↓reduceIte]
        have hne : ∃ p : Fin m × Fin r, y.1 p ≠ x.1 p := by
          by_contra hall
          apply hyx
          apply Subtype.ext
          funext p
          by_contra hp
          exact hall ⟨p, hp⟩
        obtain ⟨p, hp⟩ := hne
        symm
        refine Finset.prod_eq_zero (Finset.mem_univ p) ?_
        have h11 : (1 : ZMod 2) + 1 = 0 := by decide
        cases hxp : x.1 p <;> cases hyp : y.1 p
        · exact absurd (hyp.trans hxp.symm) hp
        · simp [ev, hyp, h11]
        · simp [ev, hyp]
        · exact absurd (hyp.trans hxp.symm) hp
    rw [heq]
    exact hfactor x Finset.univ ∅
  have htop : U = ⊤ := by
    rw [eq_top_iff]
    intro f _
    have hf : f = ∑ x : { x : (Fin m × Fin r) → Bool // x ∈ S },
        f x • (fun y : { y : (Fin m × Fin r) → Bool // y ∈ S } =>
          if y = x then (1 : ZMod 2) else 0) := by
      funext y
      simp [Finset.sum_apply]
    rw [hf]
    refine U.sum_mem ?_
    intro x _
    exact U.smul_mem (f x) (hdelta x)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrank1 : Module.finrank (ZMod 2) U = S.card := by
    rw [htop, finrank_top, Module.finrank_pi, Fintype.card_coe]
  have hrank2 : Module.finrank (ZMod 2) U ≤ (goodMonomials m r k).card := by
    calc
      Module.finrank (ZMod 2) U
          ≤ Module.finrank (ZMod 2)
              ({ g : Finset (Fin m × Fin r) // g ∈ goodMonomials m r k } → ZMod 2) :=
            LinearMap.finrank_range_le L
      _ = (goodMonomials m r k).card := by
            rw [Module.finrank_pi, Fintype.card_coe]
  rw [← card_goodMonomials m r k, ← hrank1]
  exact hrank2

lemma lowers_extremal (m r k : Nat) :
    ∀ I : Finset (Fin m), I.card = k →
      ∃ q : ((Fin m × Fin r) → Bool) → Bool,
        (∃ terms : Finset (Finset (Fin m × Fin r)),
          (∀ mon ∈ terms, mon.card ≤ r * k - 1) ∧
          ∀ word, q word = ((terms.filter (fun mon => ∀ j ∈ mon, word j = true)).card % 2 == 1)) ∧
        ∀ x ∈ extremalSet m r k, q x = decide (∀ i ∈ I, ∀ j : Fin r, x (i, j) = true) := by
  intro I hI
  refine ⟨fun _ => false, ⟨∅, ?_, ?_⟩, ?_⟩
  · intro mon hmon
    exact False.elim (Finset.notMem_empty mon hmon)
  · intro word
    simp
  · intro x hx
    simp only [extremalSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    have hnot : ¬ (∀ i ∈ I, ∀ j : Fin r, x (i, j) = true) := by
      intro hall
      have hsub : I ⊆ fullBlocks x := by
        intro i hi
        simp only [fullBlocks, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hall i hi
      have hle : I.card ≤ (fullBlocks x).card := Finset.card_le_card hsub
      omega
    simp [hnot]

theorem main : (∀ (m r k : Nat), 0 < r → 0 < k →
  let V := Fin m × Fin r
  let W := V → Bool
  let par := fun (z : Nat) => z % 2 == 1
  let deg := fun (u : Nat) (f : W → Bool) =>
    ∃ terms : Finset (Finset V), (∀ mon ∈ terms, mon.card ≤ u) ∧
      ∀ word, f word = par ((terms.filter (fun mon => ∀ j ∈ mon, word j = true)).card)
  let productOn := fun (I : Finset (Fin m)) (x : W) =>
    decide (∀ i ∈ I, ∀ j : Fin r, x (i,j) = true)
  let budget := (Finset.range (m+1)).sum (fun j =>
    if j < k then Nat.choose m j * (2^r-1)^(m-j) else 0)
  let lowers := fun (S : Finset W) => ∀ I : Finset (Fin m), I.card = k →
    ∃ q : W → Bool, deg (r*k-1) q ∧ ∀ x ∈ S, q x = productOn I x
  (∀ S : Finset W, lowers S → S.card ≤ budget) ∧
  let extremal := (Finset.univ : Finset W).filter (fun sample =>
    ((Finset.univ : Finset (Fin m)).filter (fun i => ∀ j : Fin r, sample (i,j) = true)).card < k)
  lowers extremal ∧ extremal.card = budget) := by
  intro m r k hr hk
  refine ⟨?_, ?_, ?_⟩
  · intro S hS
    exact card_le_budget hr hk S hS
  · exact lowers_extremal m r k
  · exact card_extremalSet m r k

end PEqualNP.Outside.L_lib_584_aux

theorem PEqualNP.Outside.L_lib_584 : (∀ (m r k : Nat), 0 < r → 0 < k →
  let V := Fin m × Fin r
  let W := V → Bool
  let par := fun (z : Nat) => z % 2 == 1
  let deg := fun (u : Nat) (f : W → Bool) =>
    ∃ terms : Finset (Finset V), (∀ mon ∈ terms, mon.card ≤ u) ∧
      ∀ word, f word = par ((terms.filter (fun mon => ∀ j ∈ mon, word j = true)).card)
  let productOn := fun (I : Finset (Fin m)) (x : W) =>
    decide (∀ i ∈ I, ∀ j : Fin r, x (i,j) = true)
  let budget := (Finset.range (m+1)).sum (fun j =>
    if j < k then Nat.choose m j * (2^r-1)^(m-j) else 0)
  let lowers := fun (S : Finset W) => ∀ I : Finset (Fin m), I.card = k →
    ∃ q : W → Bool, deg (r*k-1) q ∧ ∀ x ∈ S, q x = productOn I x
  (∀ S : Finset W, lowers S → S.card ≤ budget) ∧
  let extremal := (Finset.univ : Finset W).filter (fun sample =>
    ((Finset.univ : Finset (Fin m)).filter (fun i => ∀ j : Fin r, sample (i,j) = true)).card < k)
  lowers extremal ∧ extremal.card = budget) := by
  exact PEqualNP.Outside.L_lib_584_aux.main
