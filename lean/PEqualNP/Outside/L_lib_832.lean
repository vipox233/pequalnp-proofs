import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_832_aux

open Classical

private def muVal (k : ℕ) : ℤ :=
  (-1 : ℤ) ^ k * (2 : ℤ) ^ (Nat.choose k 2)

private lemma choose_two_succ (r : ℕ) : Nat.choose (r + 1) 2 = Nat.choose r 2 + r := by
  rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]

private lemma card_fin_fun_zmod2 (n : ℕ) : Fintype.card (Fin n → ZMod 2) = 2 ^ n := by
  rw [Fintype.card_fun, Fintype.card_fin, ZMod.card]

private lemma card_subspace_eq_pow {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (W : Submodule (ZMod 2) V) [Fintype W] :
    Fintype.card W = 2 ^ (Module.finrank (ZMod 2) W) := by
  let e : W ≃ₗ[ZMod 2] (Fin (Module.finrank (ZMod 2) W) → ZMod 2) :=
    (Module.finBasis (ZMod 2) W).equivFun
  rw [Fintype.card_congr e.toEquiv, card_fin_fun_zmod2]

private lemma zmod2_mem_span_singleton {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (v x : V) : x ∈ Submodule.span (ZMod 2) ({v} : Set V) ↔ x = 0 ∨ x = v := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    fin_cases c
    · left; exact zero_smul (ZMod 2) v
    · right; exact one_smul (ZMod 2) v
  · rintro (hx | hx)
    · rw [hx]; exact ⟨0, zero_smul (ZMod 2) v⟩
    · rw [hx]; exact ⟨1, one_smul (ZMod 2) v⟩

private lemma zmod2_mem_sup_span {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (W : Submodule (ZMod 2) V) (v x : V) :
    x ∈ W ⊔ Submodule.span (ZMod 2) ({v} : Set V) ↔ x ∈ W ∨ x + v ∈ W := by
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨w, hw, y, hy, rfl⟩
    rcases (zmod2_mem_span_singleton v y).mp hy with hy0 | hyv
    · left; rw [hy0, add_zero]; exact hw
    · right
      rw [hyv]
      have hv2 : v + v = 0 := by
        have h2 : (2 : ZMod 2) = 0 := rfl
        rw [← two_smul (ZMod 2) v, h2, zero_smul]
      rw [add_assoc, hv2, add_zero]
      exact hw
  · rintro (hx | hxv)
    · exact ⟨x, hx, 0, Submodule.zero_mem _, add_zero x⟩
    · have hv2 : v + v = 0 := by
        have h2 : (2 : ZMod 2) = 0 := rfl
        rw [← two_smul (ZMod 2) v, h2, zero_smul]
      refine ⟨x + v, hxv, v, Submodule.subset_span rfl, ?_⟩
      rw [add_assoc, hv2, add_zero]

private lemma zmod2_sub_eq_add {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (x y : V) :
    x - y = x + y := by
  have hy2 : y + y = 0 := by
    have h2 : (2 : ZMod 2) = 0 := rfl
    rw [← two_smul (ZMod 2) y, h2, zero_smul]
  have hneg : -y = y := eq_neg_of_add_eq_zero_left hy2 |>.symm
  rw [sub_eq_add_neg, hneg]

private lemma subspace_qbinom :
    ∀ (n : ℕ) {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
      [FiniteDimensional (ZMod 2) V] [Fintype (Submodule (ZMod 2) V)],
      Module.finrank (ZMod 2) V = n →
      ∀ x : ℤ,
        (∑ U : Submodule (ZMod 2) V,
          muVal (n - Module.finrank (ZMod 2) U) * x ^ (n - Module.finrank (ZMod 2) U)) =
        ∏ i ∈ Finset.range n, (1 - (2 : ℤ) ^ i * x) := by
  intro n
  induction n with
  | zero =>
    intro V _ _ _ _ hfin x
    have hsub : Subsingleton V := Module.finrank_zero_iff.mp hfin
    have huniq : Unique (Submodule (ZMod 2) V) :=
      { default := ⊥,
        uniq := fun U => by
          ext v
          have hv : v = 0 := Subsingleton.elim v 0
          subst hv
          simp }
    rw [Fintype.sum_unique]
    simp [muVal]
  | succ n ih =>
    intro V _ _ _ _ hfin x
    let b := Module.finBasisOfFinrankEq (ZMod 2) V hfin
    let v0 : V := b ⟨0, Nat.succ_pos n⟩
    let φ : V →ₗ[ZMod 2] ZMod 2 := b.coord ⟨0, Nat.succ_pos n⟩
    let H : Submodule (ZMod 2) V := LinearMap.ker φ
    have hv0_notH : v0 ∉ H := by
      simp [H, φ, v0]
    have hφ_surj : Function.Surjective φ := by
      intro c
      exact ⟨c • v0, by simp [φ, v0]⟩
    have hH_rank : Module.finrank (ZMod 2) H = n := by
      have h1 := LinearMap.finrank_range_add_finrank_ker φ
      have hrange : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.mpr hφ_surj
      rw [hrange, finrank_top, Module.finrank_self, hfin] at h1
      dsimp only [H]
      omega
    have hH_dichot : ∀ v : V, v ∈ H ∨ v + v0 ∈ H := by
      intro v
      have hv0_phi : φ v0 = 1 := by simp [φ, v0]
      generalize hc : φ v = c
      fin_cases c
      · left; exact hc
      · right
        change φ (v + v0) = 0
        rw [map_add, hc, hv0_phi]
        rfl
    have : Finite V := Module.finite_of_finite (ZMod 2)
    have : Finite H := Subtype.finite
    have : Finite (Submodule (ZMod 2) H) := Finite.of_injective SetLike.coe SetLike.coe_injective
    letI : Fintype (Submodule (ZMod 2) H) := Fintype.ofFinite _
    let emb : Submodule (ZMod 2) H ↪ Submodule (ZMod 2) V :=
      ⟨Submodule.map H.subtype, Submodule.map_injective_of_injective H.subtype_injective⟩
    let interH : Submodule (ZMod 2) V → Submodule (ZMod 2) H :=
      fun U => U.comap H.subtype
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ) (g := interH)
      (fun _ _ => Finset.mem_univ _)]
    have hfiber : ∀ W : Submodule (ZMod 2) H,
        (∑ U ∈ Finset.univ.filter (fun U : Submodule (ZMod 2) V => interH U = W),
          muVal (n + 1 - Module.finrank (ZMod 2) U) * x ^ (n + 1 - Module.finrank (ZMod 2) U)) =
        (1 - x) * (muVal (n - Module.finrank (ZMod 2) W) * (2 * x) ^ (n - Module.finrank (ZMod 2) W)) := by
      intro W
      let Wv : Submodule (ZMod 2) V := W.map H.subtype
      have hWv_le : Wv ≤ H := by
        rintro _ ⟨w, _, rfl⟩; exact w.property
      have hWv_rank : Module.finrank (ZMod 2) Wv = Module.finrank (ZMod 2) W :=
        LinearEquiv.finrank_eq (Submodule.equivMapOfInjective H.subtype H.subtype_injective W).symm
      have hW_le_n : Module.finrank (ZMod 2) W ≤ n := by
        rw [← hH_rank]; exact Submodule.finrank_le W
      let r := n - Module.finrank (ZMod 2) W
      have hWv_mem : Wv ∈ Finset.univ.filter (fun U : Submodule (ZMod 2) V => interH U = W) := by
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        ext w
        simp [interH, Wv]
      rw [← Finset.add_sum_erase _ _ hWv_mem]
      have hrest_dim : ∀ U ∈ (Finset.univ.filter (fun U : Submodule (ZMod 2) V => interH U = W)).erase Wv,
          Module.finrank (ZMod 2) U = Module.finrank (ZMod 2) W + 1 := by
        intro U hU
        have hUne : U ≠ Wv := (Finset.mem_erase.mp hU).1
        have hUint : interH U = W := (Finset.mem_filter.mp (Finset.mem_erase.mp hU).2).2
        have hWv_le_U : Wv ≤ U := by
          rintro _ ⟨w, hw, rfl⟩
          rw [← hUint] at hw
          exact hw
        have hnot_le_H : ¬ U ≤ H := by
          intro hUH
          apply hUne
          ext v
          constructor
          · intro hv
            have hvH : v ∈ H := hUH hv
            have hw : (⟨v, hvH⟩ : H) ∈ W := by rw [← hUint]; exact hv
            exact ⟨⟨v, hvH⟩, hw, rfl⟩
          · intro hv; exact hWv_le_U hv
        have hex : ∃ u ∈ U, u ∉ H := by
          by_contra hall
          push Not at hall
          exact hnot_le_H hall
        rcases hex with ⟨u, huU, huH⟩
        have hU_eq : U = Wv ⊔ Submodule.span (ZMod 2) ({u} : Set V) := by
          apply le_antisymm
          · intro z hzU
            rw [zmod2_mem_sup_span]
            by_cases hzH : z ∈ H
            · left; exact ⟨⟨z, hzH⟩, by rw [← hUint]; exact hzU, rfl⟩
            · right
              have hzuH : z + u ∈ H := by
                rcases hH_dichot z with h1 | h1
                · exact absurd h1 hzH
                · rcases hH_dichot u with h2 | h2
                  · exact absurd h2 huH
                  · have hsum : (z + v0) + (u + v0) ∈ H := H.add_mem h1 h2
                    have hv02 : v0 + v0 = 0 := by
                      have h2' : (2 : ZMod 2) = 0 := rfl
                      rw [← two_smul (ZMod 2) v0, h2', zero_smul]
                    have heq : (z + v0) + (u + v0) = z + u := by
                      calc (z + v0) + (u + v0) = (z + u) + (v0 + v0) := by abel
                        _ = z + u := by rw [hv02, add_zero]
                    rwa [heq] at hsum
              exact ⟨⟨z + u, hzuH⟩, by rw [← hUint]; exact U.add_mem hzU huU, rfl⟩
          · exact sup_le hWv_le_U (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr huU))
        have hdisj : Disjoint Wv (Submodule.span (ZMod 2) ({u} : Set V)) := by
          rw [Submodule.disjoint_def]
          intro z hz1 hz2
          rcases (zmod2_mem_span_singleton u z).mp hz2 with rfl | rfl
          · rfl
          · exact absurd (hWv_le hz1) huH
        have hmod := Submodule.finrank_sup_add_finrank_inf_eq Wv (Submodule.span (ZMod 2) ({u} : Set V))
        rw [hdisj.eq_bot, finrank_bot, add_zero, ← hU_eq, hWv_rank] at hmod
        have hu0 : u ≠ 0 := fun h => huH (h ▸ H.zero_mem)
        have hsp1 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ({u} : Set V)) = 1 :=
          finrank_span_singleton hu0
        rw [hsp1] at hmod
        exact hmod
      rcases Submodule.exists_isCompl W with ⟨C, hWC⟩
      have : Finite C := Subtype.finite
      letI : Fintype C := Fintype.ofFinite _
      have hC_rank : Module.finrank (ZMod 2) C = r := by
        have h1 := Submodule.finrank_add_eq_of_isCompl hWC
        rw [hH_rank] at h1
        dsimp only [r]; omega
      have hC_card : Fintype.card C = 2 ^ r := by
        rw [card_subspace_eq_pow C, hC_rank]
      have hrest_card : ((Finset.univ.filter (fun U : Submodule (ZMod 2) V => interH U = W)).erase Wv).card = 2 ^ r := by
        rw [← hC_card, ← Finset.card_univ]
        refine (Finset.card_bij (fun (c : C) _ => Wv ⊔ Submodule.span (ZMod 2) ({v0 + c.val.val} : Set V))
          ?_ ?_ ?_).symm
        · intro c _
          have hv0c_notH : v0 + c.val.val ∉ H := by
            intro hmem
            have : v0 ∈ H := by
              have hsub := H.sub_mem hmem c.val.property
              simpa using hsub
            exact hv0_notH this
          refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
          · intro heq
            have hmem : v0 + c.val.val ∈ Wv := by
              rw [← heq]; exact Submodule.mem_sup_right (Submodule.subset_span rfl)
            exact hv0c_notH (hWv_le hmem)
          · ext w
            simp only [interH, Submodule.mem_comap, Submodule.coe_subtype]
            rw [zmod2_mem_sup_span]
            constructor
            · rintro (h1 | h2)
              · rcases h1 with ⟨w', hw', heq⟩
                have : w' = w := Subtype.ext heq
                rwa [← this]
              · exfalso
                have hmemH : w.val + (v0 + c.val.val) ∈ H := hWv_le h2
                have hv0H : v0 + c.val.val ∈ H := by
                  have := H.sub_mem hmemH w.property
                  simpa using this
                exact hv0c_notH hv0H
            · intro hw
              left; exact ⟨w, hw, rfl⟩
        · intro c1 _ c2 _ heq
          have hmem : v0 + c1.val.val ∈ Wv ⊔ Submodule.span (ZMod 2) ({v0 + c2.val.val} : Set V) := by
            rw [← heq]; exact Submodule.mem_sup_right (Submodule.subset_span rfl)
          rw [zmod2_mem_sup_span] at hmem
          rcases hmem with h1 | h2
          · exfalso
            have hmemH : v0 + c1.val.val ∈ H := hWv_le h1
            have : v0 ∈ H := by have := H.sub_mem hmemH c1.val.property; simpa using this
            exact hv0_notH this
          · have hsum_eq : (v0 + c1.val.val) + (v0 + c2.val.val) = c1.val.val + c2.val.val := by
              have hv02 : v0 + v0 = 0 := by
                have h2' : (2 : ZMod 2) = 0 := rfl
                rw [← two_smul (ZMod 2) v0, h2', zero_smul]
              calc (v0 + c1.val.val) + (v0 + c2.val.val)
                  = (v0 + v0) + (c1.val.val + c2.val.val) := by abel
                _ = c1.val.val + c2.val.val := by rw [hv02, zero_add]
            rw [hsum_eq] at h2
            rcases h2 with ⟨w, hw, hweq⟩
            have hdiff_H : c1.val + c2.val = w := Subtype.ext hweq.symm
            have hdiff_C : c1.val + c2.val ∈ C := C.add_mem c1.property c2.property
            have hdiff_W : c1.val + c2.val ∈ W := hdiff_H ▸ hw
            have hbot : c1.val + c2.val = 0 := by
              have hmem_inf : c1.val + c2.val ∈ W ⊓ C := ⟨hdiff_W, hdiff_C⟩
              rw [hWC.inf_eq_bot] at hmem_inf
              exact hmem_inf
            apply Subtype.ext
            have hsub : c1.val - c2.val = 0 := by rwa [zmod2_sub_eq_add]
            exact sub_eq_zero.mp hsub
        · intro U hU
          have hUne : U ≠ Wv := (Finset.mem_erase.mp hU).1
          have hUint : interH U = W := (Finset.mem_filter.mp (Finset.mem_erase.mp hU).2).2
          have hWv_le_U : Wv ≤ U := by
            rintro _ ⟨w, hw, rfl⟩; rw [← hUint] at hw; exact hw
          have hnot_le_H : ¬ U ≤ H := by
            intro hUH; apply hUne; ext v
            constructor
            · intro hv; exact ⟨⟨v, hUH hv⟩, by rw [← hUint]; exact hv, rfl⟩
            · intro hv; exact hWv_le_U hv
          have hex : ∃ u ∈ U, u ∉ H := by by_contra hall; push Not at hall; exact hnot_le_H hall
          rcases hex with ⟨u, huU, huH⟩
          have hu_v0_H : u + v0 ∈ H := (hH_dichot u).resolve_left huH
          have hmem_sup : (⟨u + v0, hu_v0_H⟩ : H) ∈ W ⊔ C := by rw [hWC.sup_eq_top]; trivial
          rcases Submodule.mem_sup.mp hmem_sup with ⟨w, hw, c, hc, hwc⟩
          refine ⟨⟨c, hc⟩, Finset.mem_univ _, ?_⟩
          have hvc_in_U : v0 + c.val ∈ U := by
            have hval : w.val + c.val = u + v0 := congrArg Subtype.val hwc
            have hv02 : v0 + v0 = 0 := by
              have h2' : (2 : ZMod 2) = 0 := rfl
              rw [← two_smul (ZMod 2) v0, h2', zero_smul]
            have heq : v0 + c.val = u + w.val := by
              have h1 := congrArg (fun t => t + (w.val + v0)) hval
              have hw2 : w.val + w.val = 0 := by
                have h2' : (2 : ZMod 2) = 0 := rfl
                rw [← two_smul (ZMod 2) w.val, h2', zero_smul]
              calc v0 + c.val = (w.val + w.val) + (v0 + c.val) := by rw [hw2, zero_add]
                _ = (w.val + c.val) + (w.val + v0) := by abel
                _ = (u + v0) + (w.val + v0) := by rw [hval]
                _ = (u + w.val) + (v0 + v0) := by abel
                _ = u + w.val := by rw [hv02, add_zero]
            rw [heq]
            exact U.add_mem huU (hWv_le_U ⟨w, hw, rfl⟩)
          have hle : Wv ⊔ Submodule.span (ZMod 2) ({v0 + c.val} : Set V) ≤ U :=
            sup_le hWv_le_U (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hvc_in_U))
          have hU_rank := hrest_dim U hU
          have hvc_notH : v0 + c.val ∉ H := by
            intro hmem
            have : v0 ∈ H := by have := H.sub_mem hmem c.property; simpa using this
            exact hv0_notH this
          have hdisj : Disjoint Wv (Submodule.span (ZMod 2) ({v0 + c.val} : Set V)) := by
            rw [Submodule.disjoint_def]
            intro z hz1 hz2
            rcases (zmod2_mem_span_singleton _ z).mp hz2 with rfl | rfl
            · rfl
            · exact absurd (hWv_le hz1) hvc_notH
          have hmod := Submodule.finrank_sup_add_finrank_inf_eq Wv (Submodule.span (ZMod 2) ({v0 + c.val} : Set V))
          have hvc0 : v0 + c.val ≠ 0 := fun h => hvc_notH (by rw [h]; exact H.zero_mem)
          rw [hdisj.eq_bot, finrank_bot, add_zero, hWv_rank,
            finrank_span_singleton hvc0] at hmod
          exact Submodule.eq_of_le_of_finrank_eq hle (hmod.trans hU_rank.symm)
      have hrest_sum : (∑ U ∈ (Finset.univ.filter (fun U : Submodule (ZMod 2) V => interH U = W)).erase Wv,
            muVal (n + 1 - Module.finrank (ZMod 2) U) * x ^ (n + 1 - Module.finrank (ZMod 2) U)) =
          (2 : ℤ) ^ r * (muVal r * x ^ r) := by
        have hconst : ∀ U ∈ (Finset.univ.filter (fun U : Submodule (ZMod 2) V => interH U = W)).erase Wv,
            muVal (n + 1 - Module.finrank (ZMod 2) U) * x ^ (n + 1 - Module.finrank (ZMod 2) U) =
              muVal r * x ^ r := by
          intro U hU
          rw [hrest_dim U hU]
          have : n + 1 - (Module.finrank (ZMod 2) W + 1) = r := by dsimp only [r]; omega
          rw [this]
        rw [Finset.sum_congr rfl hconst, Finset.sum_const, hrest_card, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      rw [hrest_sum, hWv_rank]
      have hsub1 : n + 1 - Module.finrank (ZMod 2) W = r + 1 := by dsimp only [r]; omega
      rw [hsub1]
      change muVal (r + 1) * x ^ (r + 1) + (2 : ℤ) ^ r * (muVal r * x ^ r) =
        (1 - x) * (muVal r * (2 * x) ^ r)
      dsimp only [muVal]
      rw [choose_two_succ, pow_add, pow_succ, pow_succ, mul_pow]
      ring
    rw [Finset.sum_congr rfl fun W _ => hfiber W, ← Finset.mul_sum, ih hH_rank (2 * x)]
    rw [Finset.prod_range_succ']
    simp only [pow_zero, one_mul, mul_comm (1 - x)]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [pow_succ]
    ring

private lemma mobius_above {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] [Fintype (Submodule (ZMod 2) V)] (W : Submodule (ZMod 2) V) :
    (∑ U ∈ Finset.univ.filter (fun U : Submodule (ZMod 2) V => W ≤ U),
      muVal (Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) U)) =
    if W = ⊤ then 1 else 0 := by
  let Q := V ⧸ W
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite Q := Finite.of_surjective W.mkQ (Submodule.Quotient.mk_surjective W)
  have : Finite (Submodule (ZMod 2) Q) := Finite.of_injective SetLike.coe SetLike.coe_injective
  letI : Fintype (Submodule (ZMod 2) Q) := Fintype.ofFinite _
  let q := Module.finrank (ZMod 2) Q
  have hcard_eq : (∑ U ∈ Finset.univ.filter (fun U : Submodule (ZMod 2) V => W ≤ U),
      muVal (Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) U)) =
      ∑ U' : Submodule (ZMod 2) Q, muVal (q - Module.finrank (ZMod 2) U') := by
    refine (Finset.sum_bij (fun (U' : Submodule (ZMod 2) Q) _ => U'.comap W.mkQ) ?_ ?_ ?_ ?_).symm
    · intro U' _
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      intro w hw
      change W.mkQ w ∈ U'
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).mpr hw]
      exact U'.zero_mem
    · intro U1 _ U2 _ heq
      ext x
      rcases Submodule.Quotient.mk_surjective W x with ⟨v, rfl⟩
      have := SetLike.ext_iff.mp heq v
      exact this
    · intro U hU
      have hWU : W ≤ U := (Finset.mem_filter.mp hU).2
      refine ⟨U.map W.mkQ, Finset.mem_univ _, ?_⟩
      rw [Submodule.comap_map_eq, Submodule.ker_mkQ, sup_eq_left.mpr hWU]
    · intro U' _
      congr 1
      have hWU : W ≤ U'.comap W.mkQ := by
        intro w hw
        change W.mkQ w ∈ U'
        rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).mpr hw]
        exact U'.zero_mem
      have hrank_add := LinearMap.finrank_range_add_finrank_ker (W.mkQ.domRestrict (U'.comap W.mkQ))
      have hrange : LinearMap.range (W.mkQ.domRestrict (U'.comap W.mkQ)) = U' := by
        ext x
        rcases Submodule.Quotient.mk_surjective W x with ⟨v, rfl⟩
        simp only [LinearMap.mem_range, LinearMap.domRestrict_apply, Subtype.exists, Submodule.mem_comap]
        constructor
        · rintro ⟨w, hw, heq⟩; rwa [← heq]
        · intro hx; exact ⟨v, hx, rfl⟩
      have hker_rank : Module.finrank (ZMod 2) (LinearMap.ker (W.mkQ.domRestrict (U'.comap W.mkQ))) =
          Module.finrank (ZMod 2) W := by
        let e : W ≃ₗ[ZMod 2] LinearMap.ker (W.mkQ.domRestrict (U'.comap W.mkQ)) :=
          { toFun := fun w => ⟨⟨w.val, hWU w.property⟩, by
              change W.mkQ w.val = 0
              rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).mpr w.property]⟩,
            invFun := fun z => ⟨z.val.val, by
              have hz : W.mkQ z.val.val = 0 := z.property
              rw [Submodule.mkQ_apply] at hz
              exact (Submodule.Quotient.mk_eq_zero W).mp hz⟩,
            left_inv := fun _ => rfl, right_inv := fun _ => rfl,
            map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
        exact e.finrank_eq.symm
      rw [hrange, hker_rank] at hrank_add
      change Module.finrank (ZMod 2) U' + Module.finrank (ZMod 2) W =
        Module.finrank (ZMod 2) (U'.comap W.mkQ) at hrank_add
      have hq_add := Submodule.finrank_quotient_add_finrank W
      change q + Module.finrank (ZMod 2) W = Module.finrank (ZMod 2) V at hq_add
      omega
  rw [hcard_eq]
  have h1 := subspace_qbinom q (V := Q) rfl 1
  simp only [one_pow, mul_one] at h1
  rw [h1]
  by_cases hW : W = ⊤
  · subst hW
    have hq0 : q = 0 := by
      have h := Submodule.finrank_quotient_add_finrank (⊤ : Submodule (ZMod 2) V)
      rw [finrank_top] at h
      change q + Module.finrank (ZMod 2) V = Module.finrank (ZMod 2) V at h
      omega
    simp [hq0]
  · have hqpos : 0 < q := by
      have h := Submodule.finrank_quotient_add_finrank W
      have hlt : Module.finrank (ZMod 2) W < Module.finrank (ZMod 2) V :=
        Submodule.finrank_lt hW
      change q + Module.finrank (ZMod 2) W = Module.finrank (ZMod 2) V at h
      omega
    rw [if_neg hW]
    have h0mem : 0 ∈ Finset.range q := Finset.mem_range.mpr hqpos
    exact Finset.prod_eq_zero h0mem (by simp)

private lemma mobius_below {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] [Fintype (Submodule (ZMod 2) V)] (W : Submodule (ZMod 2) V) :
    (∑ U ∈ Finset.univ.filter (fun U : Submodule (ZMod 2) V => U ≤ W),
      muVal (Module.finrank (ZMod 2) U)) =
    if W = ⊥ then 1 else 0 := by
  let r := Module.finrank (ZMod 2) W
  let e : W ≃ₗ[ZMod 2] (Fin r → ZMod 2) := (Module.finBasis (ZMod 2) W).equivFun
  letI : Fintype (Submodule (ZMod 2) (Fin r → ZMod 2)) := Fintype.ofFinite _
  let orth : Submodule (ZMod 2) (Fin r → ZMod 2) → Submodule (ZMod 2) (Fin r → ZMod 2) :=
    fun U =>
      { carrier := {x | ∀ u ∈ U, dotProduct u x = 0}, add_mem' := fun hx hy u hu => by rw [dotProduct_add, hx u hu, hy u hu, add_zero],
        zero_mem' := fun u _ => dotProduct_zero u,
        smul_mem' := fun c x hx u hu => by rw [dotProduct_smul, hx u hu, smul_zero] }
  have horth_rank : ∀ U : Submodule (ZMod 2) (Fin r → ZMod 2),
      Module.finrank (ZMod 2) (orth U) = r - Module.finrank (ZMod 2) U := by
    intro U
    let ev : (Fin r → ZMod 2) →ₗ[ZMod 2] (U →ₗ[ZMod 2] ZMod 2) :=
      { toFun := fun x =>
          { toFun := fun u => dotProduct u.val x,
            map_add' := fun u1 u2 => add_dotProduct u1.val u2.val x,
            map_smul' := fun c u => by simp [smul_dotProduct] },
        map_add' := fun x y => by ext u; exact dotProduct_add u.val x y,
        map_smul' := fun c x => by ext u; simp [dotProduct_smul] }
    have hker : LinearMap.ker ev = orth U := by
      ext x
      simp only [LinearMap.mem_ker, orth, Submodule.mem_mk, AddSubmonoid.mem_mk,
        AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
      constructor
      · intro hx u hu
        have := congrArg (fun f => f ⟨u, hu⟩) hx
        exact this
      · intro hx
        ext ⟨u, hu⟩
        exact hx u hu
    have hsurj : Function.Surjective ev := by
      intro f
      rcases Submodule.exists_isCompl U with ⟨C, hUC⟩
      let fext : (Fin r → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
        f.comp (Submodule.projectionOnto U C hUC)
      let x : Fin r → ZMod 2 := fun j => fext (Pi.single j 1)
      refine ⟨x, ?_⟩
      ext ⟨u, hu⟩
      have h1 : fext u = f ⟨u, hu⟩ := by
        change f (Submodule.projectionOnto U C hUC (⟨u, hu⟩ : U)) = f ⟨u, hu⟩
        rw [Submodule.projectionOnto_apply_left]
      rw [← h1]
      change dotProduct u x = fext u
      have hu_exp : u = ∑ j : Fin r, u j • Pi.single j (1 : ZMod 2) := by
        funext i
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        have hterm : ∀ j : Fin r, u j * (Pi.single j (1 : ZMod 2) : Fin r → ZMod 2) i =
            if j = i then u i else 0 := by
          intro j
          by_cases hji : j = i
          · subst hji; simp
          · simp [hji, Pi.single_eq_of_ne (Ne.symm hji)]
        simp [hterm]
      conv_rhs => rw [hu_exp]
      rw [map_sum]
      simp only [map_smul, smul_eq_mul, dotProduct, x]
    have hadd := LinearMap.finrank_range_add_finrank_ker ev
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hker, Module.finrank_pi, Fintype.card_fin,
      Subspace.dual_finrank_eq] at hadd
    omega
  have horth_invol : ∀ U : Submodule (ZMod 2) (Fin r → ZMod 2), orth (orth U) = U := by
    intro U
    have hle : U ≤ orth (orth U) := fun u hu x hx => by rw [dotProduct_comm]; exact hx u hu
    have hU_le : Module.finrank (ZMod 2) U ≤ r := by
      have := Submodule.finrank_le U; rwa [Module.finrank_pi, Fintype.card_fin] at this
    have hrk : Module.finrank (ZMod 2) (orth (orth U)) = Module.finrank (ZMod 2) U := by
      rw [horth_rank, horth_rank]; omega
    exact (Submodule.eq_of_le_of_finrank_eq hle hrk.symm).symm
  have hsum_eq : (∑ U ∈ Finset.univ.filter (fun U : Submodule (ZMod 2) V => U ≤ W),
      muVal (Module.finrank (ZMod 2) U)) =
      ∑ U' : Submodule (ZMod 2) (Fin r → ZMod 2),
        muVal (r - Module.finrank (ZMod 2) U') := by
    refine Finset.sum_bij (fun U _ => orth ((U.comap W.subtype).map e.toLinearMap)) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro U1 h1 U2 h2 heq
      have hU1 : U1 ≤ W := (Finset.mem_filter.mp h1).2
      have hU2 : U2 ≤ W := (Finset.mem_filter.mp h2).2
      have h12 := congrArg orth heq
      rw [horth_invol, horth_invol] at h12
      have hcom := Submodule.map_injective_of_injective e.injective h12
      ext v
      constructor
      · intro hv
        have hw : (⟨v, hU1 hv⟩ : W) ∈ U1.comap W.subtype := hv
        rw [hcom] at hw
        exact hw
      · intro hv
        have hw : (⟨v, hU2 hv⟩ : W) ∈ U2.comap W.subtype := hv
        rw [← hcom] at hw
        exact hw
    · intro U' _
      let U0 : Submodule (ZMod 2) W := (orth U').comap e.toLinearMap
      refine ⟨U0.map W.subtype, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rintro _ ⟨w, _, rfl⟩; exact w.property⟩, ?_⟩
      rw [Submodule.comap_map_eq_of_injective W.subtype_injective, Submodule.map_comap_eq_of_surjective e.surjective,
        horth_invol]
    · intro U hU
      have hUW : U ≤ W := (Finset.mem_filter.mp hU).2
      have hrank_map : Module.finrank (ZMod 2) ((U.comap W.subtype).map e.toLinearMap) =
          Module.finrank (ZMod 2) U := by
        rw [LinearEquiv.finrank_eq (Submodule.equivMapOfInjective e.toLinearMap e.injective _).symm]
        let eqv : U ≃ₗ[ZMod 2] U.comap W.subtype :=
          { toFun := fun u => ⟨⟨u.val, hUW u.property⟩, u.property⟩,
            invFun := fun z => ⟨z.val.val, z.property⟩,
            left_inv := fun _ => rfl, right_inv := fun _ => rfl,
            map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
        exact eqv.finrank_eq.symm
      have hle_r : Module.finrank (ZMod 2) U ≤ r := by
        dsimp only [r]; exact Submodule.finrank_mono hUW
      rw [horth_rank, hrank_map]
      congr 1
      omega
  rw [hsum_eq]
  have h1 := subspace_qbinom r (V := Fin r → ZMod 2) (by rw [Module.finrank_pi, Fintype.card_fin]) 1
  simp only [one_pow, mul_one] at h1
  rw [h1]
  by_cases hW : W = ⊥
  · subst hW
    have hr0 : r = 0 := finrank_bot (ZMod 2) V
    simp [hr0]
  · have hrpos : 0 < r := by
      by_contra h0
      have hr0 : Module.finrank (ZMod 2) W = 0 := by dsimp only [r] at h0; omega
      exact hW (Submodule.finrank_eq_zero.mp hr0)
    rw [if_neg hW]
    exact Finset.prod_eq_zero (Finset.mem_range.mpr hrpos) (by simp)

private lemma mobius_interval_below {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] [Fintype (Submodule (ZMod 2) V)] (W T : Submodule (ZMod 2) V)
    (hWT : W ≤ T) :
    (∑ U ∈ Finset.univ.filter (fun U : Submodule (ZMod 2) V => W ≤ U ∧ U ≤ T),
      muVal (Module.finrank (ZMod 2) U - Module.finrank (ZMod 2) W)) =
    if W = T then 1 else 0 := by
  let Q := V ⧸ W
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite Q := Finite.of_surjective W.mkQ (Submodule.Quotient.mk_surjective W)
  have : Finite (Submodule (ZMod 2) Q) := Finite.of_injective SetLike.coe SetLike.coe_injective
  letI : Fintype (Submodule (ZMod 2) Q) := Fintype.ofFinite _
  let T' : Submodule (ZMod 2) Q := T.map W.mkQ
  have hsum_eq : (∑ U ∈ Finset.univ.filter (fun U : Submodule (ZMod 2) V => W ≤ U ∧ U ≤ T),
      muVal (Module.finrank (ZMod 2) U - Module.finrank (ZMod 2) W)) =
      ∑ U' ∈ Finset.univ.filter (fun U' : Submodule (ZMod 2) Q => U' ≤ T'),
        muVal (Module.finrank (ZMod 2) U') := by
    refine (Finset.sum_bij (fun (U' : Submodule (ZMod 2) Q) _ => U'.comap W.mkQ) ?_ ?_ ?_ ?_).symm
    · intro U' hU'
      have hle : U' ≤ T' := (Finset.mem_filter.mp hU').2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
      · intro w hw; change W.mkQ w ∈ U'; rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).mpr hw]; exact U'.zero_mem
      · intro v hv
        have hvT' : W.mkQ v ∈ T' := hle hv
        rcases hvT' with ⟨t, ht, heq⟩
        have hdiff : v - t ∈ W := (Submodule.Quotient.eq W).mp heq.symm
        have h1 : v = (v - t) + t := by abel
        rw [h1]
        exact T.add_mem (hWT hdiff) ht
    · intro U1 _ U2 _ heq
      ext x
      rcases Submodule.Quotient.mk_surjective W x with ⟨v, rfl⟩
      exact SetLike.ext_iff.mp heq v
    · intro U hU
      rcases (Finset.mem_filter.mp hU).2 with ⟨hWU, hUT⟩
      refine ⟨U.map W.mkQ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Submodule.map_mono hUT⟩, ?_⟩
      rw [Submodule.comap_map_eq, Submodule.ker_mkQ, sup_eq_left.mpr hWU]
    · intro U' _
      congr 1
      have hWU : W ≤ U'.comap W.mkQ := by
        intro w hw; change W.mkQ w ∈ U'
        rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).mpr hw]; exact U'.zero_mem
      have hrank_add := LinearMap.finrank_range_add_finrank_ker (W.mkQ.domRestrict (U'.comap W.mkQ))
      have hrange : LinearMap.range (W.mkQ.domRestrict (U'.comap W.mkQ)) = U' := by
        ext x
        rcases Submodule.Quotient.mk_surjective W x with ⟨v, rfl⟩
        simp only [LinearMap.mem_range, LinearMap.domRestrict_apply, Subtype.exists, Submodule.mem_comap]
        constructor
        · rintro ⟨w, hw, heq⟩; rwa [← heq]
        · intro hx; exact ⟨v, hx, rfl⟩
      have hker_rank : Module.finrank (ZMod 2) (LinearMap.ker (W.mkQ.domRestrict (U'.comap W.mkQ))) =
          Module.finrank (ZMod 2) W := by
        let e : W ≃ₗ[ZMod 2] LinearMap.ker (W.mkQ.domRestrict (U'.comap W.mkQ)) :=
          { toFun := fun w => ⟨⟨w.val, hWU w.property⟩, by
              change W.mkQ w.val = 0
              rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).mpr w.property]⟩,
            invFun := fun z => ⟨z.val.val, by
              have hz : W.mkQ z.val.val = 0 := z.property
              rw [Submodule.mkQ_apply] at hz
              exact (Submodule.Quotient.mk_eq_zero W).mp hz⟩,
            left_inv := fun _ => rfl, right_inv := fun _ => rfl,
            map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
        exact e.finrank_eq.symm
      rw [hrange, hker_rank] at hrank_add
      change Module.finrank (ZMod 2) U' + Module.finrank (ZMod 2) W =
        Module.finrank (ZMod 2) (U'.comap W.mkQ) at hrank_add
      omega
  rw [hsum_eq, mobius_below T']
  have hiff : T' = ⊥ ↔ W = T := by
    constructor
    · intro hbot
      apply le_antisymm hWT
      intro t ht
      have hmem : W.mkQ t ∈ (⊥ : Submodule (ZMod 2) Q) := by rw [← hbot]; exact ⟨t, ht, rfl⟩
      exact (Submodule.Quotient.mk_eq_zero W).mp hmem
    · intro heq
      subst heq
      ext x
      rcases Submodule.Quotient.mk_surjective W x with ⟨v, rfl⟩
      simp only [T', Submodule.mem_map, Submodule.mem_bot]
      constructor
      · rintro ⟨w, hw, hweq⟩
        have hdiff : v - w ∈ W := (Submodule.Quotient.eq W).mp hweq.symm
        have hvW : v ∈ W := by
          have : v = (v - w) + w := by abel
          rw [this]; exact W.add_mem hdiff hw
        exact (Submodule.Quotient.mk_eq_zero W).mpr hvW
      · intro hv
        exact ⟨v, (Submodule.Quotient.mk_eq_zero W).mp hv, rfl⟩
  by_cases h : W = T
  · rw [if_pos h, if_pos (hiff.mpr h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.mp h'))]

private lemma mobius_inter_le {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] [Fintype (Submodule (ZMod 2) V)]
    (L K : Submodule (ZMod 2) V) (hKL : K ≤ L) :
    (∑ U : Submodule (ZMod 2) V,
      if U ⊓ L ≤ K then muVal (Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) U) else 0) =
    if L = ⊤ then
      ∑ W ∈ Finset.univ.filter (fun W : Submodule (ZMod 2) V => W ≤ K),
        muVal (Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) W)
    else 0 := by
  let c : Submodule (ZMod 2) V → ℤ := fun T =>
    ∑ W ∈ Finset.univ.filter (fun W : Submodule (ZMod 2) V => W ≤ K ∧ W ≤ T),
      muVal (Module.finrank (ZMod 2) T - Module.finrank (ZMod 2) W)
  have hind : ∀ U : Submodule (ZMod 2) V,
      (if U ⊓ L ≤ K then (1 : ℤ) else 0) =
      ∑ T ∈ Finset.univ.filter (fun T : Submodule (ZMod 2) V => T ≤ U ⊓ L), c T := by
    intro U
    dsimp only [c]
    have hexpand : ∀ T ∈ Finset.univ.filter (fun T : Submodule (ZMod 2) V => T ≤ U ⊓ L),
        (∑ W ∈ Finset.univ.filter (fun W : Submodule (ZMod 2) V => W ≤ K ∧ W ≤ T),
          muVal (Module.finrank (ZMod 2) T - Module.finrank (ZMod 2) W)) =
        ∑ W : Submodule (ZMod 2) V,
          if W ≤ K ∧ W ≤ T then muVal (Module.finrank (ZMod 2) T - Module.finrank (ZMod 2) W) else 0 := by
      intro T _
      rw [← Finset.sum_filter]
    rw [Finset.sum_congr rfl hexpand, Finset.sum_comm]
    have hinner : ∀ W : Submodule (ZMod 2) V,
        (∑ T ∈ Finset.univ.filter (fun T : Submodule (ZMod 2) V => T ≤ U ⊓ L),
          if W ≤ K ∧ W ≤ T then muVal (Module.finrank (ZMod 2) T - Module.finrank (ZMod 2) W) else 0) =
        if W = U ⊓ L ∧ W ≤ K then 1 else 0 := by
      intro W
      by_cases hWK : W ≤ K
      · by_cases hWU : W ≤ U ⊓ L
        · have hflt : (∑ T ∈ Finset.univ.filter (fun T : Submodule (ZMod 2) V => T ≤ U ⊓ L),
              if W ≤ K ∧ W ≤ T then muVal (Module.finrank (ZMod 2) T - Module.finrank (ZMod 2) W) else 0) =
              ∑ T ∈ Finset.univ.filter (fun T : Submodule (ZMod 2) V => W ≤ T ∧ T ≤ U ⊓ L),
                muVal (Module.finrank (ZMod 2) T - Module.finrank (ZMod 2) W) := by
            rw [← Finset.sum_filter]
            refine Finset.sum_congr ?_ (fun _ _ => rfl)
            ext T
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, hWK, true_and, and_comm]
          rw [hflt, mobius_interval_below W (U ⊓ L) hWU]
          simp [hWK]
        · have hne : W ≠ U ⊓ L := fun h => hWU (le_of_eq h)
          rw [if_neg (fun h => hne h.1)]
          refine Finset.sum_eq_zero fun T hT => ?_
          have hTU : T ≤ U ⊓ L := (Finset.mem_filter.mp hT).2
          have hnot : ¬ (W ≤ K ∧ W ≤ T) := fun h => hWU (le_trans h.2 hTU)
          rw [if_neg hnot]
      · rw [if_neg (fun h => hWK h.2)]
        refine Finset.sum_eq_zero fun T _ => ?_
        rw [if_neg (fun h => hWK h.1)]
    rw [Finset.sum_congr rfl fun W _ => hinner W]
    by_cases hle : U ⊓ L ≤ K
    · rw [if_pos hle]
      have hterm : ∀ W : Submodule (ZMod 2) V,
          (if W = U ⊓ L ∧ W ≤ K then (1 : ℤ) else 0) = if W = U ⊓ L then 1 else 0 := by
        intro W
        by_cases h : W = U ⊓ L
        · subst h; simp [hle]
        · simp [h]
      simp [hterm]
    · rw [if_neg hle]
      symm
      refine Finset.sum_eq_zero fun W _ => ?_
      rw [if_neg]; rintro ⟨rfl, h1⟩; exact hle h1
  have hstep1 : (∑ U : Submodule (ZMod 2) V,
      if U ⊓ L ≤ K then muVal (Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) U) else 0) =
      ∑ U : Submodule (ZMod 2) V, ∑ T : Submodule (ZMod 2) V,
        if T ≤ U ∧ T ≤ L then muVal (Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) U) * c T else 0 := by
    refine Finset.sum_congr rfl fun U _ => ?_
    have hmul : (if U ⊓ L ≤ K then muVal (Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) U) else 0) =
        muVal (Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) U) * (if U ⊓ L ≤ K then 1 else 0) := by
      split_ifs <;> ring
    rw [hmul, hind U, Finset.mul_sum, ← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, le_inf_iff]
  rw [hstep1, Finset.sum_comm]
  have hinner2 : ∀ T : Submodule (ZMod 2) V,
      (∑ U : Submodule (ZMod 2) V,
        if T ≤ U ∧ T ≤ L then muVal (Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) U) * c T else 0) =
      if T = ⊤ ∧ L = ⊤ then c ⊤ else 0 := by
    intro T
    by_cases hTL : T ≤ L
    · have hflt : (∑ U : Submodule (ZMod 2) V,
          if T ≤ U ∧ T ≤ L then muVal (Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) U) * c T else 0) =
          (∑ U ∈ Finset.univ.filter (fun U : Submodule (ZMod 2) V => T ≤ U),
            muVal (Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) U)) * c T := by
        rw [Finset.sum_mul, ← Finset.sum_filter]
        refine Finset.sum_congr ?_ (fun _ _ => rfl)
        ext U
        simp [hTL]
      rw [hflt, mobius_above T]
      by_cases hT : T = ⊤
      · subst hT
        have hLtop : L = ⊤ := top_unique hTL
        simp [hLtop]
      · simp [hT]
    · have hnot : ¬ (T = ⊤ ∧ L = ⊤) := by rintro ⟨rfl, rfl⟩; exact hTL le_rfl
      rw [if_neg hnot]
      refine Finset.sum_eq_zero fun U _ => ?_
      rw [if_neg (fun h => hTL h.2)]
  rw [Finset.sum_congr rfl fun T _ => hinner2 T]
  by_cases hL : L = ⊤
  · rw [if_pos hL]
    have hterm : ∀ T : Submodule (ZMod 2) V,
        (if T = ⊤ ∧ L = ⊤ then c ⊤ else 0) = if T = ⊤ then c ⊤ else 0 := by
      intro T; simp [hL]
    rw [Finset.sum_congr rfl fun T _ => hterm T, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ↓reduceIte, c, finrank_top]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext W
    simp
  · rw [if_neg hL]
    refine Finset.sum_eq_zero fun T _ => ?_
    simp [hL]

private lemma main_proof :
∀ (d m : ℕ), 2 ≤ d →
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let F := ZMod 2
  let V := Fin d → F
  let A := Fin m → F
  letI : Fintype (Submodule F V) := Fintype.ofFinite _
  ∀ (f : V →ₗ[F] A) (a : A),
    let value := ∑ U : Submodule F V,
      let k := d - Module.finrank F U
      let size := (Finset.univ.filter (fun x : V => x ∈ U ∧ x ≠ 0 ∧ f x = a)).card
      ((-1 : ℤ)^k * 2^(Nat.choose k 2)) * ((size-1 : ℕ) : ℤ)
    value = if a = 0 then
      (if f = 0 then (-1 : ℤ)^d * 2^(Nat.choose d 2) else 0)
    else if LinearMap.range f = Submodule.span F ({a} : Set A) then
      (-1 : ℤ)^d * ∏ i ∈ Finset.range (d-1), ((2 : ℤ)^(i+1)-1)
    else 0 := by
  intro d m hd F V A f a value
  have hfinV : Module.finrank (ZMod 2) (Fin d → ZMod 2) = d := by
    rw [Module.finrank_pi, Fintype.card_fin]
  have hsplit : value =
      (∑ U : Submodule F V,
        muVal (d - Module.finrank F U) *
          ((Finset.univ.filter (fun x : V => x ∈ U ∧ x ≠ 0 ∧ f x = a)).card : ℤ)) -
      (∑ U : Submodule F V,
        if ∃ x : V, x ∈ U ∧ x ≠ 0 ∧ f x = a
        then muVal (d - Module.finrank F U) else 0) := by
    dsimp only [value]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr (by ext U; simp) fun U _ => ?_
    trans (muVal (d - Module.finrank F U) *
        ((((Finset.univ.filter (fun x : V => x ∈ U ∧ x ≠ 0 ∧ f x = a)).card - 1 : ℕ) : ℤ)))
    · refine congrArg (fun (s : Finset V) => muVal (d - Module.finrank F U) * ((s.card - 1 : ℕ) : ℤ)) ?_
      ext x
      simp
    by_cases hex : ∃ x : V, x ∈ U ∧ x ≠ 0 ∧ f x = a
    · have hpos : 1 ≤ (Finset.univ.filter (fun x : V => x ∈ U ∧ x ≠ 0 ∧ f x = a)).card := by
        rcases hex with ⟨x, hx⟩
        exact Finset.card_pos.mpr ⟨x, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hx⟩
      have hcast : (((Finset.univ.filter (fun x : V => x ∈ U ∧ x ≠ 0 ∧ f x = a)).card - 1 : ℕ) : ℤ) =
          ((Finset.univ.filter (fun x : V => x ∈ U ∧ x ≠ 0 ∧ f x = a)).card : ℤ) - 1 :=
        Nat.cast_sub hpos
      rw [if_pos hex, hcast]
      ring
    · have hzero : (Finset.univ.filter (fun x : V => x ∈ U ∧ x ≠ 0 ∧ f x = a)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        exact hex ⟨x, hx⟩
      rw [if_neg hex, hzero]
      simp
  have hpiece1 : (∑ U : Submodule F V,
      muVal (d - Module.finrank F U) *
        ((Finset.univ.filter (fun x : V => x ∈ U ∧ x ≠ 0 ∧ f x = a)).card : ℤ)) = 0 := by
    have hrew : ∀ U : Submodule F V,
        muVal (d - Module.finrank F U) *
          ((Finset.univ.filter (fun x : V => x ∈ U ∧ x ≠ 0 ∧ f x = a)).card : ℤ) =
        ∑ x : V,
          if x ∈ U ∧ x ≠ 0 ∧ f x = a then muVal (d - Module.finrank F U) else 0 := by
      intro U
      rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs <;> simp
    rw [Finset.sum_congr rfl fun U _ => hrew U, Finset.sum_comm]
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hx : x ≠ 0 ∧ f x = a
    · have hflt : (∑ U : Submodule F V,
          if x ∈ U ∧ x ≠ 0 ∧ f x = a then muVal (d - Module.finrank F U) else 0) =
          ∑ U ∈ Finset.univ.filter (fun U : Submodule F V =>
              Submodule.span F ({x} : Set V) ≤ U),
            muVal (Module.finrank F V - Module.finrank F U) := by
        rw [← Finset.sum_filter]
        refine Finset.sum_congr ?_ (fun U _ => by rw [hfinV])
        ext U
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
        exact ⟨fun h => h.1, fun h => ⟨h, hx.1, hx.2⟩⟩
      rw [hflt, mobius_above]
      have hne_top : Submodule.span F ({x} : Set V) ≠ ⊤ := by
        intro htop
        have h1 : Module.finrank F (Submodule.span F ({x} : Set V)) = 1 :=
          finrank_span_singleton hx.1
        rw [htop, finrank_top, hfinV] at h1
        omega
      rw [if_neg hne_top]
    · refine Finset.sum_eq_zero fun U _ => ?_
      rw [if_neg (fun h => hx h.2)]
  have htotal0 : (∑ U : Submodule F V, muVal (d - Module.finrank F U)) = 0 := by
    have h1 := subspace_qbinom d (V := V) hfinV 1
    simp only [one_pow, mul_one] at h1
    rw [h1]
    exact Finset.prod_eq_zero (Finset.mem_range.mpr (show 0 < d by omega)) (by simp)
  have hpiece2 : value =
      ∑ U : Submodule F V,
        if ¬ (∃ x : V, x ∈ U ∧ x ≠ 0 ∧ f x = a)
        then muVal (d - Module.finrank F U) else 0 := by
    rw [hsplit, hpiece1, zero_sub]
    have hadd : (∑ U : Submodule F V,
          if ∃ x : V, x ∈ U ∧ x ≠ 0 ∧ f x = a
          then muVal (d - Module.finrank F U) else 0) +
        (∑ U : Submodule F V,
          if ¬ (∃ x : V, x ∈ U ∧ x ≠ 0 ∧ f x = a)
          then muVal (d - Module.finrank F U) else 0) = 0 := by
      trans (∑ U : Submodule F V, muVal (d - Module.finrank F U))
      · rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun U _ => ?_
        by_cases hex : ∃ x : V, x ∈ U ∧ x ≠ 0 ∧ f x = a
        · simp [hex]
        · simp [hex]
      · exact htotal0
    linarith
  rw [hpiece2]
  by_cases ha0 : a = 0
  · subst ha0
    rw [if_pos rfl]
    have hcond : ∀ U : Submodule (ZMod 2) (Fin d → ZMod 2),
        (¬ ∃ x : Fin d → ZMod 2, x ∈ U ∧ x ≠ 0 ∧ f x = 0) ↔ U ⊓ LinearMap.ker f ≤ ⊥ := by
      intro U
      constructor
      · intro hnot x ⟨hxU, hxf⟩
        by_contra hx0
        exact hnot ⟨x, hxU, hx0, hxf⟩
      · rintro hle ⟨x, hxU, hx0, hxf⟩
        exact hx0 (hle ⟨hxU, hxf⟩)
    have hrew : (∑ U : Submodule (ZMod 2) (Fin d → ZMod 2),
          if ¬ (∃ x : Fin d → ZMod 2, x ∈ U ∧ x ≠ 0 ∧ f x = 0)
          then muVal (d - Module.finrank (ZMod 2) U) else 0) =
        ∑ U : Submodule (ZMod 2) (Fin d → ZMod 2),
          if U ⊓ LinearMap.ker f ≤ ⊥
          then muVal (Module.finrank (ZMod 2) (Fin d → ZMod 2) - Module.finrank (ZMod 2) U) else 0 := by
      refine Finset.sum_congr rfl fun U _ => ?_
      rw [hfinV]
      by_cases h1 : U ⊓ LinearMap.ker f ≤ ⊥
      · rw [if_pos ((hcond U).mpr h1), if_pos h1]
      · rw [if_neg (fun h => h1 ((hcond U).mp h)), if_neg h1]
    rw [hrew, mobius_inter_le (LinearMap.ker f) ⊥ bot_le]
    have hiff_f : LinearMap.ker f = ⊤ ↔ f = 0 := LinearMap.ker_eq_top
    by_cases hf0 : f = 0
    · rw [if_pos hf0, if_pos (hiff_f.mpr hf0)]
      have hsing : Finset.univ.filter (fun W : Submodule (ZMod 2) (Fin d → ZMod 2) => W ≤ ⊥) = {⊥} := by
        ext W; simp [le_bot_iff]
      rw [hsing, Finset.sum_singleton, finrank_bot, hfinV, Nat.sub_zero]
      rfl
    · rw [if_neg hf0, if_neg (fun h => hf0 (hiff_f.mp h))]
  · rw [if_neg ha0]
    let K : Submodule (ZMod 2) (Fin d → ZMod 2) := LinearMap.ker f
    let L : Submodule (ZMod 2) (Fin d → ZMod 2) := (Submodule.span (ZMod 2) ({a} : Set (Fin m → ZMod 2))).comap f
    have hKL : K ≤ L := by
      intro x hx; change f x ∈ Submodule.span (ZMod 2) ({a} : Set _); rw [hx]; exact Submodule.zero_mem _
    have hcond : ∀ U : Submodule (ZMod 2) (Fin d → ZMod 2),
        (¬ ∃ x : Fin d → ZMod 2, x ∈ U ∧ x ≠ 0 ∧ f x = a) ↔ U ⊓ L ≤ K := by
      intro U
      constructor
      · intro hnot x ⟨hxU, hxL⟩
        rcases (zmod2_mem_span_singleton a (f x)).mp hxL with h0 | ha'
        · exact h0
        · exfalso
          have hx0 : x ≠ 0 := fun h => ha0 (by rw [← ha', h, map_zero])
          exact hnot ⟨x, hxU, hx0, ha'⟩
      · rintro hle ⟨x, hxU, _, hxa⟩
        have hxL : x ∈ L := by
          simp only [L, Submodule.mem_comap, hxa]
          exact Submodule.subset_span rfl
        have hxK : f x = 0 := hle ⟨hxU, hxL⟩
        exact ha0 (hxa.symm.trans hxK)
    have hrew : (∑ U : Submodule (ZMod 2) (Fin d → ZMod 2),
          if ¬ (∃ x : Fin d → ZMod 2, x ∈ U ∧ x ≠ 0 ∧ f x = a)
          then muVal (d - Module.finrank (ZMod 2) U) else 0) =
        ∑ U : Submodule (ZMod 2) (Fin d → ZMod 2),
          if U ⊓ L ≤ K
          then muVal (Module.finrank (ZMod 2) (Fin d → ZMod 2) - Module.finrank (ZMod 2) U) else 0 := by
      refine Finset.sum_congr rfl fun U _ => ?_
      rw [hfinV]
      by_cases h1 : U ⊓ L ≤ K
      · rw [if_pos ((hcond U).mpr h1), if_pos h1]
      · rw [if_neg (fun h => h1 ((hcond U).mp h)), if_neg h1]
    rw [hrew, mobius_inter_le L K hKL]
    by_cases hrange : LinearMap.range f = Submodule.span (ZMod 2) ({a} : Set (Fin m → ZMod 2))
    · rw [if_pos hrange]
      have hLtop : L = ⊤ := by
        ext x
        simp only [L, Submodule.mem_comap, Submodule.mem_top, iff_true]
        rw [← hrange]
        exact LinearMap.mem_range_self f x
      rw [if_pos hLtop]
      have hK_rank : Module.finrank (ZMod 2) K = d - 1 := by
        have h1 := LinearMap.finrank_range_add_finrank_ker f
        rw [hrange, finrank_span_singleton ha0, hfinV] at h1
        change 1 + Module.finrank (ZMod 2) K = d at h1
        omega
      letI : Fintype (Submodule (ZMod 2) K) := Fintype.ofFinite _
      have hsumK : (∑ W ∈ Finset.univ.filter (fun W : Submodule (ZMod 2) (Fin d → ZMod 2) => W ≤ K),
            muVal (Module.finrank (ZMod 2) (Fin d → ZMod 2) - Module.finrank (ZMod 2) W)) =
          -(∑ W' : Submodule (ZMod 2) K,
            muVal ((d - 1) - Module.finrank (ZMod 2) W') * (2 : ℤ) ^ ((d - 1) - Module.finrank (ZMod 2) W')) := by
        rw [← Finset.sum_neg_distrib]
        refine (Finset.sum_bij (fun (W' : Submodule (ZMod 2) K) _ => W'.map K.subtype) ?_ ?_ ?_ ?_).symm
        · intro W' _
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rintro _ ⟨w, _, rfl⟩; exact w.property⟩
        · intro W1 _ W2 _ heq
          exact Submodule.map_injective_of_injective K.subtype_injective heq
        · intro W hW
          have hWK : W ≤ K := (Finset.mem_filter.mp hW).2
          refine ⟨W.comap K.subtype, Finset.mem_univ _, ?_⟩
          rw [Submodule.map_comap_eq_self]
          simpa using hWK
        · intro W' _
          have hrk : Module.finrank (ZMod 2) (W'.map K.subtype) = Module.finrank (ZMod 2) W' :=
            LinearEquiv.finrank_eq (Submodule.equivMapOfInjective K.subtype K.subtype_injective W').symm
          have hle : Module.finrank (ZMod 2) W' ≤ d - 1 := by
            rw [← hK_rank]; exact Submodule.finrank_le W'
          rw [hfinV, hrk]
          have hsub : d - Module.finrank (ZMod 2) W' = (d - 1 - Module.finrank (ZMod 2) W') + 1 := by omega
          rw [hsub]
          dsimp only [muVal]
          rw [choose_two_succ, pow_add, pow_succ]
          ring
      rw [hsumK, subspace_qbinom (d - 1) hK_rank 2]
      have hprod : -(∏ i ∈ Finset.range (d - 1), (1 - (2 : ℤ) ^ i * 2)) =
          (-1 : ℤ) ^ d * ∏ i ∈ Finset.range (d - 1), ((2 : ℤ) ^ (i + 1) - 1) := by
        have hfac : (∏ i ∈ Finset.range (d - 1), (1 - (2 : ℤ) ^ i * 2)) =
            ∏ i ∈ Finset.range (d - 1), ((-1 : ℤ) * ((2 : ℤ) ^ (i + 1) - 1)) := by
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [pow_succ]; ring
        rw [hfac, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
        have hpow : (-1 : ℤ) ^ d = (-1 : ℤ) * (-1 : ℤ) ^ (d - 1) := by
          conv_lhs => rw [show d = (d - 1) + 1 by omega, pow_succ']
        rw [hpow]
        ring
      exact hprod
    · rw [if_neg hrange]
      by_cases hLtop : L = ⊤
      · rw [if_pos hLtop]
        have hKtop : K = ⊤ := by
          ext x
          simp only [K, LinearMap.mem_ker, Submodule.mem_top, iff_true]
          have hxL : x ∈ L := by rw [hLtop]; trivial
          rcases (zmod2_mem_span_singleton a (f x)).mp hxL with h0 | hfa
          · exact h0
          · exfalso
            apply hrange
            apply le_antisymm
            · rintro _ ⟨y, rfl⟩
              have hyL : y ∈ L := by rw [hLtop]; trivial
              exact hyL
            · rw [Submodule.span_le, Set.singleton_subset_iff]
              exact ⟨x, hfa⟩
        have hflt_univ : Finset.univ.filter (fun W : Submodule F V => W ≤ K) = Finset.univ := by
          ext W; simp [hKtop]
        rw [hflt_univ]
        simpa [hfinV] using htotal0
      · rw [if_neg hLtop]

end PEqualNP.Outside.L_lib_832_aux

open PEqualNP.Outside.L_lib_832_aux in
theorem PEqualNP.Outside.L_lib_832 :
∀ (d m : ℕ), 2 ≤ d →
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let F := ZMod 2
  let V := Fin d → F
  let A := Fin m → F
  letI : Fintype (Submodule F V) := Fintype.ofFinite _
  ∀ (f : V →ₗ[F] A) (a : A),
    let value := ∑ U : Submodule F V,
      let k := d - Module.finrank F U
      let size := (Finset.univ.filter (fun x : V => x ∈ U ∧ x ≠ 0 ∧ f x = a)).card
      ((-1 : ℤ)^k * 2^(Nat.choose k 2)) * ((size-1 : ℕ) : ℤ)
    value = if a = 0 then
      (if f = 0 then (-1 : ℤ)^d * 2^(Nat.choose d 2) else 0)
    else if LinearMap.range f = Submodule.span F ({a} : Set A) then
      (-1 : ℤ)^d * ∏ i ∈ Finset.range (d-1), ((2 : ℤ)^(i+1)-1)
    else 0 :=
  main_proof
