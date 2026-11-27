import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_786

lemma zmod2_ne_zero_iff_eq_one (c : ZMod 2) : c ≠ 0 ↔ c = 1 := by
  have h : c = 0 ∨ c = 1 := by
    have hv : c.val < 2 := c.isLt
    by_cases h0 : c.val = 0
    · left; exact Fin.ext h0
    · right; exact Fin.ext (by change c.val = 1; omega)
  rcases h with rfl | rfl
  · simp [zero_ne_one]
  · simp [one_ne_zero]

lemma char2_add_self {K : Type} [Field K] [Algebra (ZMod 2) K] (a : K) : a + a = 0 := by
  have h : a + a = (1 : ZMod 2) • a + (1 : ZMod 2) • a := by simp
  rw [h, ← add_smul]
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rw [h11, zero_smul]

lemma char2_eq_of_add_eq_zero {K : Type} [Field K] [Algebra (ZMod 2) K] {a b : K}
    (h : a + b = 0) : a = b := by
  calc
    a = a + (b + b) := by rw [char2_add_self, add_zero]
    _ = (a + b) + b := by rw [add_assoc]
    _ = b := by rw [h, zero_add]

noncomputable def fullPair {K : Type} [Field K] [Algebra (ZMod 2) K]
    (bit : K →ₗ[ZMod 2] ZMod 2) : K →ₗ[ZMod 2] Module.Dual (ZMod 2) K where
  toFun w :=
    { toFun := fun y => bit (w * y)
      map_add' := fun y z => by rw [mul_add, map_add]
      map_smul' := fun c y => by rw [mul_smul_comm, map_smul]; rfl }
  map_add' w₁ w₂ := by
    ext y
    simp [add_mul, map_add]
  map_smul' c w := by
    ext y
    simp [map_smul]

lemma fullPair_injective {K : Type} [Field K] [Algebra (ZMod 2) K]
    (bit : K →ₗ[ZMod 2] ZMod 2) (hbit : bit ≠ 0) :
    Function.Injective (fullPair bit) := by
  rw [injective_iff_map_eq_zero]
  intro w hw
  by_contra hw0
  have hne : ∃ z : K, bit z ≠ 0 := by
    by_contra h
    push Not at h
    apply hbit
    ext z
    exact h z
  rcases hne with ⟨z, hz⟩
  have hwy : (fullPair bit w) (w⁻¹ * z) = 0 := by
    rw [hw]
    rfl
  change bit (w * (w⁻¹ * z)) = 0 at hwy
  rw [← mul_assoc, mul_inv_cancel₀ hw0, one_mul] at hwy
  exact hz hwy

lemma fullPair_surjective {K : Type} [Field K] [Algebra (ZMod 2) K]
    [FiniteDimensional (ZMod 2) K]
    (bit : K →ₗ[ZMod 2] ZMod 2) (hbit : bit ≠ 0) :
    Function.Surjective (fullPair bit) := by
  have hdim : Module.finrank (ZMod 2) K = Module.finrank (ZMod 2) (Module.Dual (ZMod 2) K) := by
    rw [Subspace.dual_finrank_eq]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
    (fullPair_injective bit hbit)

lemma served_iff {K : Type} [Field K] [Algebra (ZMod 2) K]
    (bit : K →ₗ[ZMod 2] ZMod 2) (g : ℕ) (d : Fin g → K) (w : K) :
    (w ≠ 0 ∧ ∃ (S : Finset (Fin g)) (x : K), S.card ≤ 2 ∧ x ≠ 0 ∧
      x = w * ∑ i ∈ S, (bit (d i * x)) • d i) ↔
    ∃ y ∈ Submodule.span (ZMod 2) (Set.range (fun ij : Fin g × Fin g => d ij.1 * d ij.2)),
      bit (w * y) ≠ 0 := by
  constructor
  · rintro ⟨_, S, x, _, hx0, hxeq⟩
    by_contra hnone
    push Not at hnone
    have hmul : ∀ k : Fin g, bit (d k * x) = 0 := by
      intro k
      rw [hxeq]
      have hsum : d k * (w * ∑ i ∈ S, (bit (d i * x)) • d i) =
          ∑ i ∈ S, (bit (d i * x)) • (w * (d k * d i)) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_smul_comm, mul_smul_comm]
        congr 1
        ring
      rw [hsum, map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_smul]
      have hmem : d k * d i ∈
          Submodule.span (ZMod 2) (Set.range (fun ij : Fin g × Fin g => d ij.1 * d ij.2)) :=
        Submodule.subset_span ⟨(k, i), rfl⟩
      rw [hnone (d k * d i) hmem, smul_zero]
    have hxzero : x = 0 := by
      rw [hxeq]
      have hs : ∑ i ∈ S, (bit (d i * x)) • d i = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [hmul i, zero_smul]
      rw [hs, mul_zero]
    exact hx0 hxzero
  · rintro ⟨y, hyP, hyne⟩
    have hw0 : w ≠ 0 := by
      intro h
      rw [h, zero_mul, map_zero] at hyne
      exact hyne rfl
    have hij_ex : ∃ i j : Fin g, bit (w * (d i * d j)) ≠ 0 := by
      by_contra hall
      push Not at hall
      have hzero : ∀ z ∈
          Submodule.span (ZMod 2) (Set.range (fun ij : Fin g × Fin g => d ij.1 * d ij.2)),
          bit (w * z) = 0 := by
        intro z hz
        induction hz using Submodule.span_induction with
        | mem z hzm => rcases hzm with ⟨⟨i, j⟩, rfl⟩; exact hall i j
        | zero => rw [mul_zero, map_zero]
        | add a b _ _ ha hb => rw [mul_add, map_add, ha, hb, add_zero]
        | smul c a _ ha => rw [mul_smul_comm, map_smul, ha, smul_zero]
      exact hyne (hzero y hyP)
    refine ⟨hw0, ?_⟩
    by_cases hdiag : ∃ i : Fin g, bit (w * (d i * d i)) ≠ 0
    · rcases hdiag with ⟨i, hi⟩
      refine ⟨{i}, w * d i, by simp, ?_, ?_⟩
      · intro hwd
        apply hi
        have h1 : w * (d i * d i) = (w * d i) * d i := by ring
        rw [h1, hwd, zero_mul, map_zero]
      · have hbit1 : bit (d i * (w * d i)) = 1 := by
          rw [← zmod2_ne_zero_iff_eq_one]
          have h1 : d i * (w * d i) = w * (d i * d i) := by ring
          rw [h1]
          exact hi
        simp [hbit1]
    · push Not at hdiag
      rcases hij_ex with ⟨i, j, hij⟩
      have hne_ij : i ≠ j := by
        intro heq
        subst heq
        exact hij (hdiag i)
      have hbit_ij : bit (w * (d i * d j)) = 1 := (zmod2_ne_zero_iff_eq_one _).mp hij
      have hdne : d i + d j ≠ 0 := by
        intro hsum
        have hdeq : d i = d j := char2_eq_of_add_eq_zero hsum
        apply hij
        rw [← hdeq]
        exact hdiag i
      refine ⟨{i, j}, w * (d i + d j), (Finset.card_pair hne_ij).le, mul_ne_zero hw0 hdne, ?_⟩
      have hbi : bit (d i * (w * (d i + d j))) = 1 := by
        have h1 : d i * (w * (d i + d j)) = w * (d i * d i) + w * (d i * d j) := by ring
        rw [h1, map_add, hdiag i, hbit_ij, zero_add]
      have hbj : bit (d j * (w * (d i + d j))) = 1 := by
        have h1 : d j * (w * (d i + d j)) = w * (d i * d j) + w * (d j * d j) := by ring
        rw [h1, map_add, hbit_ij, hdiag j, add_zero]
      rw [Finset.sum_pair hne_ij, hbi, hbj, one_smul, one_smul]

end PEqualNP.Outside.L_lib_786

theorem PEqualNP.Outside.L_lib_786 : (let F := ZMod 2
∀ (K : Type) [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
    (bit : K →ₗ[F] F), bit ≠ 0 → ∀ (g : ℕ) (d : Fin g → K),
  let P := Submodule.span F (Set.range (fun ij : Fin g × Fin g => d ij.1 * d ij.2))
  let k := Module.finrank F K
  let served := fun (w : K) => w ≠ 0 ∧
    ∃ (S : Finset (Fin g)) (x : K), S.card ≤ 2 ∧ x ≠ 0 ∧
      x = w * ∑ i ∈ S, (bit (d i * x)) • d i
  (∀ w : K, served w ↔ ∃ y ∈ P, bit (w*y) ≠ 0) ∧
    (@Finset.filter K served (fun w => Classical.propDecidable (served w)) Finset.univ).card
      + 2^(k - Module.finrank F P) = 2^k) := by
  intro F K _ _ _ _ bit hbit g d P k served
  have hserved : ∀ w : K, served w ↔ ∃ y ∈ P, bit (w * y) ≠ 0 :=
    fun w => PEqualNP.Outside.L_lib_786.served_iff bit g d w
  refine ⟨hserved, ?_⟩
  classical
  let pairMap : K →ₗ[F] Module.Dual F P :=
    (P.subtype.dualMap).comp (PEqualNP.Outside.L_lib_786.fullPair bit)
  have hsurj : Function.Surjective pairMap :=
    (LinearMap.dualMap_surjective_of_injective P.injective_subtype).comp
      (PEqualNP.Outside.L_lib_786.fullPair_surjective bit hbit)
  have hrange : LinearMap.range pairMap = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hrank_sum := LinearMap.finrank_range_add_finrank_ker pairMap
  rw [hrange, finrank_top, Subspace.dual_finrank_eq] at hrank_sum
  have hker_dim : Module.finrank F (LinearMap.ker pairMap) = k - Module.finrank F P := by
    change Module.finrank F P + Module.finrank F (LinearMap.ker pairMap) = k at hrank_sum
    omega
  have hker_iff : ∀ w : K, ¬ served w ↔ w ∈ LinearMap.ker pairMap := by
    intro w
    rw [hserved w, LinearMap.mem_ker]
    push Not
    constructor
    · intro h
      ext y
      exact h y.1 y.2
    · intro h y hy
      have h0 : pairMap w ⟨y, hy⟩ = 0 := by
        rw [h]
        rfl
      exact h0
  have hcard_K : Fintype.card K = 2 ^ k := by
    rw [Module.card_eq_pow_finrank (K := F) (V := K), ZMod.card]
  have hcard_ker : Fintype.card (LinearMap.ker pairMap) = 2 ^ (k - Module.finrank F P) := by
    rw [Module.card_eq_pow_finrank (K := F) (V := LinearMap.ker pairMap), ZMod.card, hker_dim]
  have hpart := @Finset.card_filter_add_card_filter_not K Finset.univ served
    (fun w => Classical.propDecidable (served w))
    (fun w => Classical.propDecidable (¬ served w))
  rw [Finset.card_univ] at hpart
  have hfilter_eq :
      (@Finset.filter K (fun w => ¬ served w)
        (fun w => Classical.propDecidable (¬ served w)) Finset.univ).card =
      Fintype.card (LinearMap.ker pairMap) := by
    convert (Fintype.card_subtype (fun w => ¬ served w)).symm.trans
      (Fintype.card_congr (Equiv.subtypeEquivRight hker_iff))
  have hfilter_dec :
      (@Finset.filter K served (fun w => Classical.propDecidable (served w)) Finset.univ).card +
      (@Finset.filter K (fun w => ¬ served w)
        (fun w => Classical.propDecidable (¬ served w)) Finset.univ).card =
      Fintype.card K := by
    convert hpart
  rw [hfilter_eq, hcard_ker, hcard_K] at hfilter_dec
  exact hfilter_dec
