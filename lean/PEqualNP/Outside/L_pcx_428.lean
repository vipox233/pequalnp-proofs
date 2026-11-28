import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_428

open Module Submodule

section Rado

variable {E : Type} [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def G (q : ι → E) (U : ι → Submodule (ZMod 2) E) (S : Finset ι) :
    Submodule (ZMod 2) E :=
  ⨆ i ∈ S, (span (ZMod 2) {q i} ⊔ U i)

theorem le_G {q : ι → E} {U : ι → Submodule (ZMod 2) E} {S : Finset ι} {i : ι} (hi : i ∈ S) :
    span (ZMod 2) {q i} ⊔ U i ≤ G q U S :=
  le_iSup₂ (f := fun i (_ : i ∈ S) => span (ZMod 2) {q i} ⊔ U i) i hi

theorem G_le {q : ι → E} {U : ι → Submodule (ZMod 2) E} {S : Finset ι} {X : Submodule (ZMod 2) E}
    (h : ∀ i ∈ S, span (ZMod 2) {q i} ⊔ U i ≤ X) : G q U S ≤ X :=
  iSup₂_le h

theorem G_univ_bot (q : ι → E) :
    G q (fun _ => (⊥ : Submodule (ZMod 2) E)) Finset.univ = span (ZMod 2) (Set.range q) := by
  apply le_antisymm
  · refine G_le fun i _ => ?_
    rw [sup_bot_eq]
    exact span_mono (Set.singleton_subset_iff.mpr (Set.mem_range_self i))
  · rw [span_le]
    rintro _ ⟨i, rfl⟩
    exact le_G (Finset.mem_univ i) (le_sup_left (b := (⊥ : Submodule (ZMod 2) E))
      (subset_span (Set.mem_singleton _)))

theorem split_coset {U : Submodule (ZMod 2) E} (hU : U ≠ ⊥) :
    ∃ (u : E) (U' : Submodule (ZMod 2) E), u ∈ U ∧ U' ≤ U ∧ u ∉ U' ∧
      ∀ v ∈ U, v ∈ U' ∨ v + u ∈ U' := by
  obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff U).mp hU
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hu0
  refine ⟨u, U ⊓ LinearMap.ker φ, hu, inf_le_left, fun h => ?_, fun v hv => ?_⟩
  · have := (mem_inf.mp h).2
    rw [LinearMap.mem_ker, hφ] at this
    exact one_ne_zero this
  · have key : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
    rcases key (φ v) with h0 | h1
    · exact Or.inl (mem_inf.mpr ⟨hv, h0⟩)
    · refine Or.inr (mem_inf.mpr ⟨U.add_mem hv hu, ?_⟩)
      rw [LinearMap.mem_ker, map_add, h1, hφ]
      decide

theorem card_compl_eq (S : Finset ι) : (Finset.univ \ S).card = Fintype.card ι - S.card := by
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ]

theorem rado (k : ℕ) : ∀ (n : ℕ) (q : ι → E) (U : ι → Submodule (ZMod 2) E),
    ∑ i, finrank (ZMod 2) (U i) = n →
    (∀ S : Finset ι, k ≤ finrank (ZMod 2) (G q U S) + (Finset.univ \ S).card) →
    ∃ ℓ : ι → E, (∀ i, ℓ i - q i ∈ U i) ∧ k ≤ finrank (ZMod 2) (span (ZMod 2) (Set.range ℓ)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro q U hn hcond
  by_cases hall : ∀ i, U i = ⊥
  · refine ⟨q, fun i => by simp, ?_⟩
    have := hcond Finset.univ
    have hU : U = fun _ => ⊥ := funext hall
    rw [hU, G_univ_bot, Finset.sdiff_self, Finset.card_empty, add_zero] at this
    exact this
  push_neg at hall
  obtain ⟨i0, hi0⟩ := hall
  obtain ⟨u, U', hu, hU'U, huU', hsplit⟩ := split_coset hi0
  have hlt : finrank (ZMod 2) U' < finrank (ZMod 2) (U i0) :=
    Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hU'U (fun h => huU' (h ▸ hu)))
  obtain ⟨U1, hU1⟩ : ∃ U1 : ι → Submodule (ZMod 2) E, U1 = Function.update U i0 U' := ⟨_, rfl⟩
  have hsum : ∑ i, finrank (ZMod 2) (U1 i) < n := by
    rw [← hn]
    apply Finset.sum_lt_sum
    · intro i _
      by_cases h : i = i0
      · rw [hU1, h, Function.update_self]; exact hlt.le
      · rw [hU1, Function.update_of_ne h]
    · exact ⟨i0, Finset.mem_univ _, by rw [hU1, Function.update_self]; exact hlt⟩
  obtain ⟨q2, hq2⟩ : ∃ q2 : ι → E, q2 = Function.update q i0 (q i0 + u) := ⟨_, rfl⟩
  have hG1 : ∀ S : Finset ι, i0 ∉ S → G q U1 S = G q U S := by
    intro S hS
    unfold G
    refine iSup_congr fun i => iSup_congr fun hi => ?_
    have : i ≠ i0 := fun h => hS (h ▸ hi)
    simp [hU1, this]
  have hG2 : ∀ S : Finset ι, i0 ∉ S → G q2 U1 S = G q U S := by
    intro S hS
    unfold G
    refine iSup_congr fun i => iSup_congr fun hi => ?_
    have : i ≠ i0 := fun h => hS (h ▸ hi)
    simp [hU1, hq2, this]
  by_cases hc1 : ∀ S : Finset ι, k ≤ finrank (ZMod 2) (G q U1 S) + (Finset.univ \ S).card
  · obtain ⟨ℓ, hℓ, hk⟩ := ih _ hsum q U1 rfl hc1
    refine ⟨ℓ, fun i => ?_, hk⟩
    by_cases h : i = i0
    · subst h; have := hℓ i; simp only [hU1, Function.update_self] at this; exact hU'U this
    · have := hℓ i; simpa [hU1, h] using this
  by_cases hc2 : ∀ S : Finset ι, k ≤ finrank (ZMod 2) (G q2 U1 S) + (Finset.univ \ S).card
  · obtain ⟨ℓ, hℓ, hk⟩ := ih _ hsum q2 U1 rfl hc2
    refine ⟨ℓ, fun i => ?_, hk⟩
    by_cases h : i = i0
    · subst h
      have := hℓ i
      simp only [hU1, hq2, Function.update_self] at this
      have e : ℓ i - q i = (ℓ i - (q i + u)) + u := by abel
      rw [e]
      exact (U i).add_mem (hU'U this) hu
    · have := hℓ i; simpa [hU1, hq2, h] using this
  exfalso
  push_neg at hc1 hc2
  obtain ⟨S1, hS1⟩ := hc1
  obtain ⟨S2, hS2⟩ := hc2
  have h1 : i0 ∈ S1 := by
    by_contra h
    rw [hG1 S1 h] at hS1
    exact absurd (hcond S1) (not_le.mpr hS1)
  have h2 : i0 ∈ S2 := by
    by_contra h
    rw [hG2 S2 h] at hS2
    exact absurd (hcond S2) (not_le.mpr hS2)
  obtain ⟨A, hA⟩ : ∃ A, A = G q U1 S1 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = G q2 U1 S2 := ⟨_, rfl⟩
  rw [← hA] at hS1
  rw [← hB] at hS2
  have hU1i0 : U1 i0 = U' := by rw [hU1, Function.update_self]
  have hq2i0 : q2 i0 = q i0 + u := by rw [hq2, Function.update_self]
  have hU1ne : ∀ i, i ≠ i0 → U1 i = U i := fun i h => by rw [hU1, Function.update_of_ne h]
  have hq2ne : ∀ i, i ≠ i0 → q2 i = q i := fun i h => by rw [hq2, Function.update_of_ne h]
  have hqA : q i0 ∈ A := by
    rw [hA]
    exact le_G (q := q) (U := U1) h1 (le_sup_left (b := U1 i0) (subset_span (Set.mem_singleton _)))
  have hqB : q i0 + u ∈ B := by
    rw [hB, ← hq2i0]
    exact le_G (q := q2) (U := U1) h2 (le_sup_left (b := U1 i0) (subset_span (Set.mem_singleton _)))
  have hU'A : U' ≤ A := by
    have := le_G (q := q) (U := U1) h1 (i := i0)
    rw [hU1i0, ← hA] at this
    exact le_trans le_sup_right this
  have huAB : u ∈ A ⊔ B := by
    have e : u = (q i0 + u) - q i0 := by abel
    rw [e]
    exact (A ⊔ B).sub_mem (mem_sup_right hqB) (mem_sup_left hqA)
  have hsup : G q U (S1 ∪ S2) ≤ A ⊔ B := by
    refine G_le fun i hi => ?_
    by_cases h : i = i0
    · rw [h]
      refine sup_le ?_ ?_
      · rw [span_le, Set.singleton_subset_iff]; exact mem_sup_left hqA
      · intro v hv
        rcases hsplit v hv with h' | h'
        · exact mem_sup_left (hU'A h')
        · have e : v = (v + u) - u := by abel
          rw [e]
          exact (A ⊔ B).sub_mem (mem_sup_left (hU'A h')) huAB
    · rcases Finset.mem_union.mp hi with hi | hi
      · have := le_G (q := q) (U := U1) hi
        rw [hU1ne i h, ← hA] at this
        exact le_trans this le_sup_left
      · have := le_G (q := q2) (U := U1) hi
        rw [hU1ne i h, hq2ne i h, ← hB] at this
        exact le_trans this le_sup_right
  have hinf : G q U ((S1 ∩ S2).erase i0) ≤ A ⊓ B := by
    refine G_le fun i hi => ?_
    have hne := Finset.ne_of_mem_erase hi
    have hi' := Finset.mem_of_mem_erase hi
    refine le_inf ?_ ?_
    · have := le_G (q := q) (U := U1) (Finset.mem_inter.mp hi').1
      rwa [hU1ne i hne, ← hA] at this
    · have := le_G (q := q2) (U := U1) (Finset.mem_inter.mp hi').2
      rwa [hU1ne i hne, hq2ne i hne, ← hB] at this
  have hmod := Submodule.finrank_sup_add_finrank_inf_eq A B
  have hm1 := Submodule.finrank_mono hsup
  have hm2 := Submodule.finrank_mono hinf
  have hk1 := hcond (S1 ∪ S2)
  have hk2 := hcond ((S1 ∩ S2).erase i0)
  rw [card_compl_eq] at hk1 hk2 hS1 hS2
  have hcu := Finset.card_union_add_card_inter S1 S2
  have hce : ((S1 ∩ S2).erase i0).card + 1 = (S1 ∩ S2).card :=
    Finset.card_erase_add_one (Finset.mem_inter.mpr ⟨h1, h2⟩)
  have hb1 : (S1 ∪ S2).card ≤ Fintype.card ι := Finset.card_le_univ _
  have hb2 : S1.card ≤ Fintype.card ι := Finset.card_le_univ _
  have hb3 : S2.card ≤ Fintype.card ι := Finset.card_le_univ _
  have hb4 : (S1 ∩ S2).card ≤ S1.card := Finset.card_le_card Finset.inter_subset_left
  omega

end Rado

section Lower

variable {X : Type} [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]
variable {r : ℕ}

theorem zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c; decide

theorem lower_generic (K : Submodule (ZMod 2) X) (e : ℕ)
    (f : Fin r → X → ZMod 2) (Bf : Fin r → (X →ₗ[ZMod 2] X →ₗ[ZMod 2] ZMod 2))
    (hf : ∀ i x w, f i (x + w) = f i x + f i w + Bf i x w)
    (hloc : ∀ y : Fin r → X, ∃ y0 : X, ∀ i w, Bf i y0 w = Bf i (y i) w)
    (H : ∀ y0 : X, ∃ W : Submodule (ZMod 2) X, W ≤ K ∧
        finrank (ZMod 2) K ≤ finrank (ZMod 2) W + e ∧
        ∀ w ∈ W, ∀ k ∈ K, ∀ i, f i (y0 + k + w) = f i (y0 + k)) :
    ∃ (S : Finset (Fin r)) (Z : Submodule (ZMod 2) X),
      (∀ w ∈ Z, w ∈ K ∧ (∀ i, ∀ k ∈ K, Bf i k w = 0) ∧
        ∀ i ∈ S, f i w = 0 ∧ ∀ y, Bf i y w = 0) ∧
      finrank (ZMod 2) K + (Finset.univ \ S).card ≤ finrank (ZMod 2) Z + e := by
  have hf0 : ∀ i, f i 0 = 0 := by
    intro i
    have h := hf i 0 0
    simp only [add_zero, map_zero, LinearMap.zero_apply] at h
    have h2 : f i 0 + f i 0 = 0 := by
      rw [← two_mul]; exact mul_eq_zero_of_left rfl _
    linear_combination h + h2
  let R : Submodule (ZMod 2) X :=
    { carrier := {w | w ∈ K ∧ ∀ i, ∀ k ∈ K, Bf i k w = 0}
      zero_mem' := ⟨K.zero_mem, fun i k _ => map_zero _⟩, add_mem' := fun {a b} ha hb =>
        ⟨K.add_mem ha.1 hb.1, fun i k hk => by rw [map_add, ha.2 i k hk, hb.2 i k hk, add_zero]⟩
      smul_mem' := fun c a ha =>
        ⟨K.smul_mem c ha.1, fun i k hk => by rw [map_smul, ha.2 i k hk, smul_zero]⟩ }
  have hRK : R ≤ K := fun w hw => hw.1
  let q : Fin r → Module.Dual (ZMod 2) R := fun i =>
    { toFun := fun w => f i w
      map_add' := fun a b => by
        have h0 : Bf i a b = 0 := b.2.2 i a a.2.1
        simp only [Submodule.coe_add, hf, h0, add_zero]
      map_smul' := fun c a => by
        rcases zmod2_cases c with rfl | rfl
        · simp [hf0]
        · simp }
  let Φ : Fin r → (X →ₗ[ZMod 2] Module.Dual (ZMod 2) R) := fun i => (Bf i).compl₂ R.subtype
  let U : Fin r → Submodule (ZMod 2) (Module.Dual (ZMod 2) R) := fun i => LinearMap.range (Φ i)
  by_contra hno
  push_neg at hno
  have hcond : ∀ S : Finset (Fin r),
      finrank (ZMod 2) R + e + 1 - finrank (ZMod 2) K ≤
        finrank (ZMod 2) (G q U S) + (Finset.univ \ S).card := by
    intro S
    by_contra hlt
    push_neg at hlt
    let Z' : Submodule (ZMod 2) R := (G q U S).dualCoannihilator
    have hZ := hno S (Z'.map R.subtype) (by
      intro w hw
      obtain ⟨w', hw', rfl⟩ := Submodule.mem_map.mp hw
      rw [Submodule.mem_dualCoannihilator] at hw'
      refine ⟨w'.2.1, w'.2.2, fun i hi => ⟨?_, fun y => ?_⟩⟩
      · have := hw' (q i) (le_G hi (le_sup_left (b := U i) (subset_span (Set.mem_singleton _))))
        exact this
      · have := hw' (Φ i y) (le_G hi (le_sup_right (a := span (ZMod 2) {q i})
          (LinearMap.mem_range_self (Φ i) y)))
        exact this)
    rw [Submodule.finrank_map_subtype_eq] at hZ
    have hsum : finrank (ZMod 2) (G q U S) + finrank (ZMod 2) Z' = finrank (ZMod 2) R :=
      Subspace.finrank_add_finrank_dualCoannihilator_eq (G q U S)
    omega
  obtain ⟨ℓ, hℓ, hk⟩ := rado _ _ q U rfl hcond
  choose y hy using fun i => (hℓ i : ℓ i - q i ∈ LinearMap.range (Φ i))
  obtain ⟨y0, hy0⟩ := hloc y
  obtain ⟨W, hWK, hWdim, hWinv⟩ := H y0
  have hkey : ∀ w ∈ W, ∀ i, f i w + Bf i y0 w = 0 ∧ ∀ k ∈ K, Bf i k w = 0 := by
    intro w hw i
    have hA := hWinv w hw 0 K.zero_mem i
    rw [add_zero, hf] at hA
    refine ⟨by linear_combination hA, fun k hk => ?_⟩
    have hB := hWinv w hw k hk i
    rw [hf, map_add, LinearMap.add_apply] at hB
    linear_combination hB - hA
  have hWR : W ≤ R := fun w hw => ⟨hWK hw, fun i k hk => (hkey w hw i).2 k hk⟩
  have hWcoann : W.comap R.subtype ≤ (span (ZMod 2) (Set.range ℓ)).dualCoannihilator := by
    intro w hw
    rw [Submodule.mem_dualCoannihilator]
    intro φ hφ
    have hle : span (ZMod 2) (Set.range ℓ) ≤ LinearMap.ker (Module.Dual.eval (ZMod 2) R w) := by
      rw [span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, Module.Dual.eval_apply]
      have e1 : ℓ i = q i + Φ i (y i) := by rw [hy i]; abel
      rw [e1, LinearMap.add_apply]
      show f i w + Bf i (y i) w = 0
      rw [← hy0 i w]
      exact (hkey w hw i).1
    exact hle hφ
  have h1 := Submodule.finrank_mono hWcoann
  have h2 := Subspace.finrank_add_finrank_dualCoannihilator_eq (span (ZMod 2) (Set.range ℓ))
  have h3 : finrank (ZMod 2) (W.comap R.subtype) = finrank (ZMod 2) W :=
    (Submodule.comapSubtypeEquivOfLe hWR).finrank_eq
  have h4 := Submodule.finrank_mono hRK
  omega

end Lower

section Concrete

variable {r : ℕ}

noncomputable def fq (m : Fin r → ℕ) (i : Fin r) (x : ((i : Fin r) → ((Fin (m i) → ZMod 2) × (Fin (m i) → ZMod 2)) × ZMod 2)) : ZMod 2 :=
  (x i).2 + ∑ j : Fin (m i), (x i).1.1 j * (x i).1.2 j

noncomputable def Bq (m : Fin r → ℕ) (i : Fin r) : ((i : Fin r) → ((Fin (m i) → ZMod 2) × (Fin (m i) → ZMod 2)) × ZMod 2) →ₗ[ZMod 2] ((i : Fin r) → ((Fin (m i) → ZMod 2) × (Fin (m i) → ZMod 2)) × ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  LinearMap.mk₂ (ZMod 2)
    (fun x y => ∑ j : Fin (m i), ((x i).1.1 j * (y i).1.2 j + (y i).1.1 j * (x i).1.2 j))
    (fun x1 x2 y => by
      simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add, add_mul, mul_add,
        Finset.sum_add_distrib]
      ring)
    (fun c x y => by
      simp only [Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by ring)
    (fun x y1 y2 => by
      simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add, add_mul, mul_add,
        Finset.sum_add_distrib]
      ring)
    (fun c x y => by
      simp only [Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by ring)

theorem Bq_apply (m : Fin r → ℕ) (i : Fin r) (x y : ((i : Fin r) → ((Fin (m i) → ZMod 2) × (Fin (m i) → ZMod 2)) × ZMod 2)) :
    Bq m i x y = ∑ j : Fin (m i), ((x i).1.1 j * (y i).1.2 j + (y i).1.1 j * (x i).1.2 j) := rfl

theorem fq_add (m : Fin r → ℕ) (i : Fin r) (x w : ((i : Fin r) → ((Fin (m i) → ZMod 2) × (Fin (m i) → ZMod 2)) × ZMod 2)) :
    fq m i (x + w) = fq m i x + fq m i w + Bq m i x w := by
  rw [Bq_apply]
  unfold fq
  simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add, add_mul, mul_add, Finset.sum_add_distrib]
  ring

theorem Bq_symm (m : Fin r → ℕ) (i : Fin r) (x y : ((i : Fin r) → ((Fin (m i) → ZMod 2) × (Fin (m i) → ZMod 2)) × ZMod 2)) : Bq m i x y = Bq m i y x := by
  rw [Bq_apply, Bq_apply]
  refine Finset.sum_congr rfl fun j _ => by ring

theorem Bq_left_congr (m : Fin r → ℕ) (i : Fin r) {x x' : ((i : Fin r) → ((Fin (m i) → ZMod 2) × (Fin (m i) → ZMod 2)) × ZMod 2)} (h : (x i).1 = (x' i).1) (y : ((i : Fin r) → ((Fin (m i) → ZMod 2) × (Fin (m i) → ZMod 2)) × ZMod 2)) :
    Bq m i x y = Bq m i x' y := by
  rw [Bq_apply, Bq_apply, h]

theorem block_zero (m : Fin r → ℕ) (i : Fin r) (x : ((i : Fin r) → ((Fin (m i) → ZMod 2) × (Fin (m i) → ZMod 2)) × ZMod 2)) (h : ∀ y, Bq m i y x = 0) :
    (x i).1 = 0 := by
  classical
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
  · have := h (Pi.single i ((0, Pi.single j 1), 0))
    rw [Bq_apply] at this
    simpa [Pi.single_apply] using this
  · have := h (Pi.single i ((Pi.single j 1, 0), 0))
    rw [Bq_apply] at this
    simpa [Pi.single_apply] using this

theorem finrank_X (m : Fin r → ℕ) :
    finrank (ZMod 2) ((i : Fin r) → ((Fin (m i) → ZMod 2) × (Fin (m i) → ZMod 2)) × ZMod 2) = ∑ i : Fin r, (2 * m i + 1) := by
  rw [Module.finrank_pi_fintype]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_self]
  ring

theorem Z_bounds (m : Fin r → ℕ) (K Z : Submodule (ZMod 2) ((i : Fin r) → ((Fin (m i) → ZMod 2) × (Fin (m i) → ZMod 2)) × ZMod 2)) (S : Finset (Fin r))
    (hZ : ∀ w ∈ Z, w ∈ K ∧ (∀ i, ∀ k ∈ K, Bq m i k w = 0) ∧
        ∀ i ∈ S, fq m i w = 0 ∧ ∀ y, Bq m i y w = 0) :
    finrank (ZMod 2) Z ≤ (Finset.univ \ S).card + ∑ i ∈ Finset.univ \ S, m i ∧
    finrank (ZMod 2) Z + finrank (ZMod 2) K ≤ (Finset.univ \ S).card + ∑ i : Fin r, (2 * m i + 1) := by
  classical
  set T := Finset.univ \ S with hT
  let BT : LinearMap.BilinForm (ZMod 2) ((i : Fin r) → ((Fin (m i) → ZMod 2) × (Fin (m i) → ZMod 2)) × ZMod 2) := ∑ i ∈ T, Bq m i
  have hBT : ∀ x y, BT x y = ∑ i ∈ T, Bq m i x y := by
    intro x y
    simp only [BT, LinearMap.sum_apply]
  have hsymm : ∀ x y, BT x y = BT y x := by
    intro x y; rw [hBT, hBT]; exact Finset.sum_congr rfl fun i _ => Bq_symm m i x y
  set rad := LinearMap.ker BT with hrad
  have hmem_rad : ∀ x, x ∈ rad ↔ ∀ y, BT x y = 0 := by
    intro x
    rw [hrad, LinearMap.mem_ker]
    exact ⟨fun h y => by rw [h]; rfl, fun h => LinearMap.ext h⟩
  have hmem_orth : ∀ W : Submodule (ZMod 2) ((i : Fin r) → ((Fin (m i) → ZMod 2) × (Fin (m i) → ZMod 2)) × ZMod 2), ∀ v,
      v ∈ BT.orthogonal W ↔ ∀ u ∈ W, BT u v = 0 := by
    intro W v
    rfl
  have hZK : Z ≤ K := fun w hw => (hZ w hw).1
  have hZoK : Z ⊔ rad ≤ BT.orthogonal K := by
    refine sup_le (fun v hv => ?_) (fun v hv => ?_)
    · rw [hmem_orth]
      intro u hu
      rw [hBT]
      exact Finset.sum_eq_zero fun i _ => (hZ v hv).2.1 i u hu
    · rw [hmem_orth]
      intro u _
      rw [hsymm]
      exact (hmem_rad v).mp hv u
  have hZoZ : Z ⊔ rad ≤ BT.orthogonal Z := by
    intro v hv
    have := hZoK hv
    rw [hmem_orth] at this ⊢
    exact fun u hu => this u (hZK hu)
  have hZrad : finrank (ZMod 2) (Z ⊓ rad : Submodule (ZMod 2) ((i : Fin r) → ((Fin (m i) → ZMod 2) × (Fin (m i) → ZMod 2)) × ZMod 2)) ≤ T.card := by
    let L : ((i : Fin r) → ((Fin (m i) → ZMod 2) × (Fin (m i) → ZMod 2)) × ZMod 2) →ₗ[ZMod 2] (T → ZMod 2) :=
      LinearMap.pi fun i : T => (LinearMap.snd (ZMod 2) _ _).comp (LinearMap.proj (i : Fin r))
    have hinj : Function.Injective (L.domRestrict (Z ⊓ rad)) := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      rintro ⟨x, hxZ, hxr⟩ hx
      rw [LinearMap.mem_ker] at hx
      ext1
      funext i
      by_cases hi : i ∈ T
      · have h2 : (x i).2 = 0 := congrFun hx ⟨i, hi⟩
        have h1 : (x i).1 = 0 := by
          refine block_zero m i x fun y => ?_
          have := (hmem_rad x).mp hxr (Pi.single i (y i))
          rw [hBT, Finset.sum_eq_single i] at this
          · rw [Bq_left_congr m i (x' := Pi.single i (y i)) (by simp), Bq_symm]
            exact this
          · intro b _ hb
            rw [Bq_symm, Bq_left_congr m b (x' := 0) (by simp [Pi.single_eq_of_ne hb])]
            simp
          · intro h; exact absurd hi h
        exact Prod.ext h1 h2
      · have hiS : i ∈ S := by
          rw [hT, Finset.mem_sdiff] at hi; push_neg at hi; exact hi (Finset.mem_univ i)
        obtain ⟨hf0, hb0⟩ := (hZ x hxZ).2.2 i hiS
        have h1 := block_zero m i x hb0
        have h2 : (x i).2 = 0 := by
          unfold fq at hf0
          have hs : ∑ j : Fin (m i), (x i).1.1 j * (x i).1.2 j = 0 := by
            rw [h1]; simp
          rw [hs, add_zero] at hf0
          exact hf0
        exact Prod.ext h1 h2
    have := LinearMap.finrank_le_finrank_of_injective hinj
    rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at this
  have hradbig : ∑ i : Fin r, (2 * m i + 1) ≤ finrank (ZMod 2) rad + 2 * ∑ i ∈ T, m i := by
    let P : ((i : Fin r) → ((Fin (m i) → ZMod 2) × (Fin (m i) → ZMod 2)) × ZMod 2) →ₗ[ZMod 2] ((i : T) → (Fin (m i) → ZMod 2) × (Fin (m i) → ZMod 2)) :=
      LinearMap.pi fun i : T => (LinearMap.fst (ZMod 2) _ _).comp (LinearMap.proj (i : Fin r))
    have hPr : LinearMap.ker P ≤ rad := by
      intro x hx
      rw [LinearMap.mem_ker] at hx
      rw [hmem_rad]
      intro y
      rw [hBT]
      refine Finset.sum_eq_zero fun i hi => ?_
      have : (x i).1 = 0 := congrFun hx ⟨i, hi⟩
      rw [Bq_left_congr m i (x' := 0) (by simp [this])]
      simp
    have h1 := LinearMap.finrank_range_add_finrank_ker P
    have h2 := Submodule.finrank_le (LinearMap.range P)
    have h3 := Submodule.finrank_mono hPr
    rw [finrank_X] at h1
    rw [Module.finrank_pi_fintype] at h2
    have h4 : ∑ i : T, finrank (ZMod 2) ((Fin (m i) → ZMod 2) × (Fin (m i) → ZMod 2))
        = 2 * ∑ i ∈ T, m i := by
      rw [Finset.mul_sum, ← Finset.sum_coe_sort T (fun i => 2 * m i)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Module.finrank_prod, Module.finrank_fin_fun]; ring
    omega
  have hK := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := BT) K
  have hZ' := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := BT) Z
  have hsupinf := Submodule.finrank_sup_add_finrank_inf_eq Z rad
  have hm1 := Submodule.finrank_mono hZoK
  have hm2 := Submodule.finrank_mono hZoZ
  have hm3 := Submodule.finrank_mono (inf_le_right : K ⊓ LinearMap.ker BT ≤ LinearMap.ker BT)
  rw [finrank_X] at hK hZ'
  have e1 : (LinearMap.ker BT) = rad := rfl
  rw [e1] at hK hZ' hm3
  constructor <;> omega


theorem lower_bound (m : Fin r → ℕ) (d e : ℕ)
    (first : ((i : Fin r) → ((Fin (m i) → ZMod 2) × (Fin (m i) → ZMod 2)) × ZMod 2) →ₗ[ZMod 2] (Fin d → ZMod 2))
    (second : (Fin d → ZMod 2) → ((i : Fin r) → ((Fin (m i) → ZMod 2) × (Fin (m i) → ZMod 2)) × ZMod 2) →ₗ[ZMod 2] (Fin e → ZMod 2))
    (out : (Fin d → ZMod 2) → (Fin e → ZMod 2) → (Fin r → ZMod 2))
    (hout : ∀ x : ((i : Fin r) → ((Fin (m i) → ZMod 2) × (Fin (m i) → ZMod 2)) × ZMod 2), out (first x) (second (first x) x) = fun i => fq m i x) :
    ∑ i : Fin r, (2 * m i + 1) ≤ 2 * d + e ∧
      ∃ T : Finset (Fin r), T.card ≤ e ∧ ∑ i : Fin r, (2 * m i + 1) ≤ d + e + ∑ i ∈ T, m i := by
  set K := LinearMap.ker first with hKdef
  have hK : ∑ i : Fin r, (2 * m i + 1) ≤ finrank (ZMod 2) K + d := by
    have h1 : finrank (ZMod 2) (LinearMap.range first) + finrank (ZMod 2) K =
        finrank (ZMod 2) ((i : Fin r) → ((Fin (m i) → ZMod 2) × (Fin (m i) → ZMod 2)) × ZMod 2) := LinearMap.finrank_range_add_finrank_ker first
    have h2 := Submodule.finrank_le (LinearMap.range first)
    rw [finrank_X] at h1
    rw [Module.finrank_fin_fun] at h2
    omega
  have hloc : ∀ y : Fin r → ((i : Fin r) → ((Fin (m i) → ZMod 2) × (Fin (m i) → ZMod 2)) × ZMod 2), ∃ y0 : ((i : Fin r) → ((Fin (m i) → ZMod 2) × (Fin (m i) → ZMod 2)) × ZMod 2), ∀ i w, Bq m i y0 w = Bq m i (y i) w :=
    fun y => ⟨fun j => y j j, fun i w => Bq_left_congr m i rfl w⟩
  have H : ∀ y0 : ((i : Fin r) → ((Fin (m i) → ZMod 2) × (Fin (m i) → ZMod 2)) × ZMod 2), ∃ W : Submodule (ZMod 2) ((i : Fin r) → ((Fin (m i) → ZMod 2) × (Fin (m i) → ZMod 2)) × ZMod 2), W ≤ K ∧
      finrank (ZMod 2) K ≤ finrank (ZMod 2) W + e ∧
      ∀ w ∈ W, ∀ k ∈ K, ∀ i, fq m i (y0 + k + w) = fq m i (y0 + k) := by
    intro y0
    let L := (second (first y0)).domRestrict K
    refine ⟨(LinearMap.ker L).map K.subtype, Submodule.map_subtype_le _ _, ?_, ?_⟩
    · rw [Submodule.finrank_map_subtype_eq]
      have h1 := LinearMap.finrank_range_add_finrank_ker L
      have h2 := Submodule.finrank_le (LinearMap.range L)
      rw [Module.finrank_fin_fun] at h2
      omega
    · intro w hw k hk i
      obtain ⟨w', hw', rfl⟩ := Submodule.mem_map.mp hw
      have hw0 : second (first y0) (w' : ((i : Fin r) → ((Fin (m i) → ZMod 2) × (Fin (m i) → ZMod 2)) × ZMod 2)) = 0 := hw'
      have hw1 : first (w' : ((i : Fin r) → ((Fin (m i) → ZMod 2) × (Fin (m i) → ZMod 2)) × ZMod 2)) = 0 := w'.2
      have hk1 : first k = 0 := hk
      have e1 : first (y0 + k + (w' : ((i : Fin r) → ((Fin (m i) → ZMod 2) × (Fin (m i) → ZMod 2)) × ZMod 2))) = first y0 := by
        rw [map_add, map_add, hk1, hw1, add_zero, add_zero]
      have e2 : first (y0 + k) = first y0 := by rw [map_add, hk1, add_zero]
      have A := hout (y0 + k + (w' : ((i : Fin r) → ((Fin (m i) → ZMod 2) × (Fin (m i) → ZMod 2)) × ZMod 2)))
      have B := hout (y0 + k)
      rw [e1, map_add (second (first y0)), hw0, add_zero] at A
      rw [e2] at B
      have := A.symm.trans B
      exact congrFun this i
  obtain ⟨S, Z, hZ, hdim⟩ := lower_generic K e (fq m) (Bq m) (fq_add m) hloc H
  obtain ⟨hb1, hb2⟩ := Z_bounds m K Z S hZ
  have hZK : finrank (ZMod 2) Z ≤ finrank (ZMod 2) K :=
    Submodule.finrank_mono (fun w hw => (hZ w hw).1)
  refine ⟨by omega, Finset.univ \ S, by omega, by omega⟩

end Concrete


section Upper

variable {r : ℕ}

theorem protocol_of_det {X Y : Type} [AddCommGroup X] [Module (ZMod 2) X] (f : X → Y) (d e : ℕ)
    (first : X →ₗ[ZMod 2] (Fin d → ZMod 2))
    (second : (Fin d → ZMod 2) → X →ₗ[ZMod 2] (Fin e → ZMod 2))
    (hdet : ∀ x x', first x = first x' → second (first x) x = second (first x) x' → f x = f x') :
    ∃ out : (Fin d → ZMod 2) → (Fin e → ZMod 2) → Y,
      ∀ x, out (first x) (second (first x) x) = f x := by
  classical
  refine ⟨fun μ ν => f (if h : ∃ z, first z = μ ∧ second μ z = ν then h.choose else 0),
    fun x => ?_⟩
  have hex : ∃ z, first z = first x ∧ second (first x) z = second (first x) x := ⟨x, rfl, rfl⟩
  show f (if h : ∃ z, first z = first x ∧ second (first x) z = second (first x) x
    then h.choose else 0) = f x
  rw [dif_pos hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  exact (hdet x _ h1.symm h2.symm).symm

theorem pack {X : Type} [AddCommGroup X] [Module (ZMod 2) X] {ι : Type} [Fintype ι]
    (g : ι → (X →ₗ[ZMod 2] ZMod 2)) (n : ℕ) (h : Fintype.card ι ≤ n) :
    ∃ φ : X →ₗ[ZMod 2] (Fin n → ZMod 2), ∀ x, φ x = 0 → ∀ i, g i x = 0 := by
  classical
  let eqv := Fintype.equivFin ι
  refine ⟨LinearMap.pi fun t : Fin n =>
    if ht : t.val < Fintype.card ι then g (eqv.symm ⟨t.val, ht⟩) else 0, fun x hx i => ?_⟩
  have := congrFun hx ⟨(eqv i).val, lt_of_lt_of_le (eqv i).isLt h⟩
  rw [LinearMap.pi_apply, dif_pos (eqv i).isLt] at this
  simpa using this

noncomputable def coordL (m : Fin r → ℕ) : (Σ i : Fin r, Fin (m i) ⊕ (Fin (m i) ⊕ Unit)) → (((i : Fin r) → ((Fin (m i) → ZMod 2) × (Fin (m i) → ZMod 2)) × ZMod 2) →ₗ[ZMod 2] ZMod 2)
  | ⟨i, Sum.inl j⟩ =>
    { toFun := fun x => (x i).1.1 j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  | ⟨i, Sum.inr (Sum.inl j)⟩ =>
    { toFun := fun x => (x i).1.2 j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  | ⟨i, Sum.inr (Sum.inr _)⟩ =>
    { toFun := fun x => (x i).2, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

def embA (m : Fin r → ℕ) : (Σ i : Fin r, Fin (m i)) ↪ (Σ i : Fin r, Fin (m i) ⊕ (Fin (m i) ⊕ Unit)) :=
  ⟨fun p => ⟨p.1, Sum.inl p.2⟩, by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    simp only [Sigma.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    simp only [heq_eq_eq, Sum.inl.injEq] at h
    subst h; rfl⟩

def embB (m : Fin r → ℕ) : (Σ i : Fin r, Fin (m i)) ↪ (Σ i : Fin r, Fin (m i) ⊕ (Fin (m i) ⊕ Unit)) :=
  ⟨fun p => ⟨p.1, Sum.inr (Sum.inl p.2)⟩, by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    simp only [Sigma.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    simp only [heq_eq_eq, Sum.inr.injEq, Sum.inl.injEq] at h
    subst h; rfl⟩

def embC (m : Fin r → ℕ) : Fin r ↪ (Σ i : Fin r, Fin (m i) ⊕ (Fin (m i) ⊕ Unit)) :=
  ⟨fun i => ⟨i, Sum.inr (Sum.inr ())⟩, by
    intro i i' h
    simp only [Sigma.mk.injEq] at h
    exact h.1⟩

theorem embA_ne_embB (m : Fin r → ℕ) (p q : (Σ i : Fin r, Fin (m i))) : embA m p ≠ embB m q := by
  rcases p with ⟨i0, j0⟩
  rcases q with ⟨i', j'⟩
  intro h
  simp only [embA, embB, Function.Embedding.coeFn_mk, Sigma.mk.injEq] at h
  obtain ⟨rfl, h2⟩ := h

theorem embA_ne_embC (m : Fin r → ℕ) (p : (Σ i : Fin r, Fin (m i))) (i : Fin r) : embA m p ≠ embC m i := by
  rcases p with ⟨i0, j0⟩
  intro h
  simp only [embA, embC, Function.Embedding.coeFn_mk, Sigma.mk.injEq] at h
  obtain ⟨rfl, h2⟩ := h

theorem embB_ne_embC (m : Fin r → ℕ) (p : (Σ i : Fin r, Fin (m i))) (i : Fin r) : embB m p ≠ embC m i := by
  rcases p with ⟨i0, j0⟩
  intro h
  simp only [embB, embC, Function.Embedding.coeFn_mk, Sigma.mk.injEq] at h
  obtain ⟨rfl, h2⟩ := h

theorem card_coords (m : Fin r → ℕ) : Fintype.card (Σ i : Fin r, Fin (m i) ⊕ (Fin (m i) ⊕ Unit)) = ∑ i : Fin r, (2 * m i + 1) := by
  rw [Fintype.card_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
  ring

theorem upper_bound (m : Fin r → ℕ) (d e : ℕ) (T : Finset (Fin r))
    (h1 : ∑ i : Fin r, (2 * m i + 1) ≤ 2 * d + e) (hT : T.card ≤ e)
    (h2 : ∑ i : Fin r, (2 * m i + 1) ≤ d + e + ∑ i ∈ T, m i) :
    ∃ (first : ((i : Fin r) → ((Fin (m i) → ZMod 2) × (Fin (m i) → ZMod 2)) × ZMod 2) →ₗ[ZMod 2] (Fin d → ZMod 2))
      (second : (Fin d → ZMod 2) → ((i : Fin r) → ((Fin (m i) → ZMod 2) × (Fin (m i) → ZMod 2)) × ZMod 2) →ₗ[ZMod 2] (Fin e → ZMod 2))
      (out : (Fin d → ZMod 2) → (Fin e → ZMod 2) → (Fin r → ZMod 2)),
      ∀ x : ((i : Fin r) → ((Fin (m i) → ZMod 2) × (Fin (m i) → ZMod 2)) × ZMod 2), out (first x) (second (first x) x) = fun i => fq m i x := by
  classical
  obtain ⟨P, hP⟩ : ∃ P : Finset (Σ i : Fin r, Fin (m i)), P = T.sigma fun _ => Finset.univ := ⟨_, rfl⟩
  have hPcard : P.card = ∑ i ∈ T, m i := by
    rw [hP, Finset.card_sigma]
    simp
  obtain ⟨s, hs⟩ : ∃ s, s = min d (∑ i ∈ T, m i) := ⟨_, rfl⟩
  obtain ⟨E1, hE1P, hE1card⟩ := Finset.exists_subset_card_eq
    (show s ≤ P.card by rw [hPcard, hs]; exact min_le_right _ _)
  obtain ⟨Ea, hEa⟩ : ∃ X : Finset (Σ i : Fin r, Fin (m i) ⊕ (Fin (m i) ⊕ Unit)), X = E1.map (embA m) := ⟨_, rfl⟩
  obtain ⟨Hb, hHb⟩ : ∃ X : Finset (Σ i : Fin r, Fin (m i) ⊕ (Fin (m i) ⊕ Unit)), X = E1.map (embB m) := ⟨_, rfl⟩
  obtain ⟨Hc, hHc⟩ : ∃ X : Finset (Σ i : Fin r, Fin (m i) ⊕ (Fin (m i) ⊕ Unit)), X = T.map (embC m) := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ X : Finset (Σ i : Fin r, Fin (m i) ⊕ (Fin (m i) ⊕ Unit)), X = Hb ∪ Hc := ⟨_, rfl⟩
  obtain ⟨U0, hU0⟩ : ∃ X : Finset (Σ i : Fin r, Fin (m i) ⊕ (Fin (m i) ⊕ Unit)), X = Ea ∪ H := ⟨_, rfl⟩
  obtain ⟨Rest, hRest⟩ : ∃ X : Finset (Σ i : Fin r, Fin (m i) ⊕ (Fin (m i) ⊕ Unit)), X = Finset.univ \ U0 := ⟨_, rfl⟩
  have hdisjBC : Disjoint Hb Hc := by
    rw [Finset.disjoint_left]
    intro c hb hc
    rw [hHb] at hb
    rw [hHc] at hc
    obtain ⟨p, _, rfl⟩ := Finset.mem_map.mp hb
    obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hc
    exact embB_ne_embC m p i hi.symm
  have hdisjAH : Disjoint Ea H := by
    rw [Finset.disjoint_left]
    intro c ha hh
    rw [hEa] at ha
    obtain ⟨p, _, rfl⟩ := Finset.mem_map.mp ha
    rw [hH] at hh
    rcases Finset.mem_union.mp hh with hb | hc
    · rw [hHb] at hb
      obtain ⟨q, _, hq⟩ := Finset.mem_map.mp hb
      exact embA_ne_embB m p q hq.symm
    · rw [hHc] at hc
      obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hc
      exact embA_ne_embC m p i hi.symm
  have hEacard : Ea.card = s := by rw [hEa, Finset.card_map, hE1card]
  have hU0card : U0.card = 2 * s + T.card := by
    rw [hU0, Finset.card_union_of_disjoint hdisjAH, hH, Finset.card_union_of_disjoint hdisjBC,
      hEacard, hHb, hHc, Finset.card_map, Finset.card_map, hE1card]
    ring
  have hRestcard : Rest.card + 2 * s + T.card = ∑ i : Fin r, (2 * m i + 1) := by
    have h := Finset.card_sdiff_of_subset (Finset.subset_univ U0)
    rw [Finset.card_univ, card_coords, ← hRest] at h
    have hle : U0.card ≤ ∑ i : Fin r, (2 * m i + 1) := by
      rw [← card_coords]; exact Finset.card_le_univ _
    omega
  obtain ⟨Rest1, hR1sub, hR1card⟩ := Finset.exists_subset_card_eq
    (show min (d - s) Rest.card ≤ Rest.card from min_le_right _ _)
  obtain ⟨C1, hC1⟩ : ∃ X : Finset (Σ i : Fin r, Fin (m i) ⊕ (Fin (m i) ⊕ Unit)), X = Ea ∪ Rest1 := ⟨_, rfl⟩
  obtain ⟨C2, hC2⟩ : ∃ X : Finset (Σ i : Fin r, Fin (m i) ⊕ (Fin (m i) ⊕ Unit)), X = Rest \ Rest1 := ⟨_, rfl⟩
  have hC1card : C1.card ≤ d := by
    have := Finset.card_union_le Ea Rest1
    rw [← hC1, hEacard, hR1card] at this
    have : s ≤ d := by rw [hs]; exact min_le_left _ _
    omega
  have hC2card : C2.card + T.card ≤ e := by
    rw [hC2, Finset.card_sdiff_of_subset hR1sub, hR1card]
    have : s ≤ d := by rw [hs]; exact min_le_left _ _
    omega
  obtain ⟨φ1, hφ1⟩ := pack (fun c : C1 => coordL m c) d (by rw [Fintype.card_coe]; exact hC1card)
  let gT : ((i : Fin r) → ((Fin (m i) → ZMod 2) × (Fin (m i) → ZMod 2)) × ZMod 2) → T → (((i : Fin r) → ((Fin (m i) → ZMod 2) × (Fin (m i) → ZMod 2)) × ZMod 2) →ₗ[ZMod 2] ZMod 2) := fun y0 t =>
    { toFun := fun x => (x t).2 + ∑ j : Fin (m t),
        (if (⟨(t : Fin r), j⟩ : (Σ i : Fin r, Fin (m i))) ∈ E1 then (y0 t).1.1 j else 0) * (x t).1.2 j
      map_add' := fun a b => by
        simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add, mul_add, Finset.sum_add_distrib]
        ring
      map_smul' := fun c a => by
        simp only [Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]
        rw [mul_add, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun j _ => by ring }
  let gfun : ((i : Fin r) → ((Fin (m i) → ZMod 2) × (Fin (m i) → ZMod 2)) × ZMod 2) → (C2 ⊕ T) → (((i : Fin r) → ((Fin (m i) → ZMod 2) × (Fin (m i) → ZMod 2)) × ZMod 2) →ₗ[ZMod 2] ZMod 2) := fun y0 z =>
    match z with
    | Sum.inl c => coordL m c
    | Sum.inr t => gT y0 t
  have hcard2 : Fintype.card (C2 ⊕ T) ≤ e := by
    rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe]; exact hC2card
  choose φ2 hφ2 using fun y0 => pack (gfun y0) e hcard2
  refine ⟨φ1, fun μ => φ2 (if h : ∃ z, φ1 z = μ then h.choose else 0),
    protocol_of_det (fun x i => fq m i x) d e φ1
      (fun μ => φ2 (if h : ∃ z, φ1 z = μ then h.choose else 0)) ?_⟩
  intro x x' hfx hsx
  have hex : ∃ z, φ1 z = φ1 x := ⟨x, rfl⟩
  simp only [dif_pos hex] at hsx
  obtain ⟨y0, hy0⟩ : ∃ y0, y0 = hex.choose := ⟨_, rfl⟩
  rw [← hy0] at hsx
  have hy0x : φ1 y0 = φ1 x := by rw [hy0]; exact hex.choose_spec
  obtain ⟨v, hv⟩ : ∃ v, v = x' - x := ⟨_, rfl⟩
  have hv1 := hφ1 v (by rw [hv, map_sub, hfx, sub_self])
  have hv2 := hφ2 y0 v (by rw [hv, map_sub, hsx, sub_self])
  have hxy := hφ1 (x - y0) (by rw [map_sub, hy0x, sub_self])
  have hfree : ∀ c, c ∉ H → coordL m c v = 0 := by
    intro c hc
    by_cases hcA : c ∈ Ea
    · exact hv1 ⟨c, by rw [hC1]; exact Finset.mem_union_left _ hcA⟩
    have hcR : c ∈ Rest := by
      rw [hRest, Finset.mem_sdiff]
      refine ⟨Finset.mem_univ _, fun h => ?_⟩
      rw [hU0, Finset.mem_union] at h
      tauto
    by_cases hc1 : c ∈ Rest1
    · exact hv1 ⟨c, by rw [hC1]; exact Finset.mem_union_right _ hc1⟩
    exact hv2 (Sum.inl ⟨c, by rw [hC2]; exact Finset.mem_sdiff.mpr ⟨hcR, hc1⟩⟩)
  have hA_notH : ∀ i j, (⟨i, Sum.inl j⟩ : (Σ i : Fin r, Fin (m i) ⊕ (Fin (m i) ⊕ Unit))) ∉ H := by
    intro i j h
    rw [hH] at h
    rcases Finset.mem_union.mp h with hb | hc
    · rw [hHb] at hb
      obtain ⟨q, _, hq⟩ := Finset.mem_map.mp hb
      exact embA_ne_embB m ⟨i, j⟩ q hq.symm
    · rw [hHc] at hc
      obtain ⟨i', _, hi'⟩ := Finset.mem_map.mp hc
      exact embA_ne_embC m ⟨i, j⟩ i' hi'.symm
  have hB_H : ∀ i j, (⟨i, Sum.inr (Sum.inl j)⟩ : (Σ i : Fin r, Fin (m i) ⊕ (Fin (m i) ⊕ Unit))) ∈ H → (⟨i, j⟩ : (Σ i : Fin r, Fin (m i))) ∈ E1 := by
    intro i j h
    rw [hH] at h
    rcases Finset.mem_union.mp h with hb | hc
    · rw [hHb] at hb
      obtain ⟨q, hq, hqe⟩ := Finset.mem_map.mp hb
      have : embB m q = embB m ⟨i, j⟩ := hqe
      rw [(embB m).injective this] at hq
      exact hq
    · rw [hHc] at hc
      obtain ⟨i', _, hi'⟩ := Finset.mem_map.mp hc
      exact absurd hi'.symm (embB_ne_embC m ⟨i, j⟩ i')
  have hC_H : ∀ i, (⟨i, Sum.inr (Sum.inr ())⟩ : (Σ i : Fin r, Fin (m i) ⊕ (Fin (m i) ⊕ Unit))) ∈ H → i ∈ T := by
    intro i h
    rw [hH] at h
    rcases Finset.mem_union.mp h with hb | hc
    · rw [hHb] at hb
      obtain ⟨q, _, hqe⟩ := Finset.mem_map.mp hb
      exact absurd hqe (embB_ne_embC m q i)
    · rw [hHc] at hc
      obtain ⟨i', hi', hie⟩ := Finset.mem_map.mp hc
      have : embC m i' = embC m i := hie
      rw [(embC m).injective this] at hi'
      exact hi'
  have hE1T : ∀ i j, (⟨i, j⟩ : (Σ i : Fin r, Fin (m i))) ∈ E1 → i ∈ T := by
    intro i j h
    have := hE1P h
    rw [hP, Finset.mem_sigma] at this
    exact this.1
  have va : ∀ i j, (v i).1.1 j = 0 := fun i j => hfree ⟨i, Sum.inl j⟩ (hA_notH i j)
  have vb : ∀ i j, (⟨i, j⟩ : (Σ i : Fin r, Fin (m i))) ∉ E1 → (v i).1.2 j = 0 :=
    fun i j h => hfree ⟨i, Sum.inr (Sum.inl j)⟩ (fun hh => h (hB_H i j hh))
  have vc : ∀ i, i ∉ T → (v i).2 = 0 :=
    fun i h => hfree ⟨i, Sum.inr (Sum.inr ())⟩ (fun hh => h (hC_H i hh))
  have xa : ∀ i j, (⟨i, j⟩ : (Σ i : Fin r, Fin (m i))) ∈ E1 → (x i).1.1 j = (y0 i).1.1 j := by
    intro i j h
    have hmem : (⟨i, Sum.inl j⟩ : (Σ i : Fin r, Fin (m i) ⊕ (Fin (m i) ⊕ Unit))) ∈ C1 := by
      rw [hC1, hEa]
      exact Finset.mem_union_left _ (Finset.mem_map_of_mem (embA m) h)
    have : (x i).1.1 j - (y0 i).1.1 j = 0 := hxy ⟨_, hmem⟩
    exact sub_eq_zero.mp this
  have gv : ∀ t : T, (v t).2 + ∑ j : Fin (m t),
      (if (⟨(t : Fin r), j⟩ : (Σ i : Fin r, Fin (m i))) ∈ E1 then (y0 t).1.1 j else 0) * (v t).1.2 j = 0 :=
    fun t => hv2 (Sum.inr t)
  funext i
  have hx' : x' = x + v := by rw [hv]; abel
  rw [hx', fq_add, Bq_apply]
  have hfv : fq m i v = (v i).2 := by
    unfold fq
    simp [va]
  have hsum : ∑ j : Fin (m i), ((x i).1.1 j * (v i).1.2 j + (v i).1.1 j * (x i).1.2 j)
      = ∑ j : Fin (m i), (if (⟨i, j⟩ : (Σ i : Fin r, Fin (m i))) ∈ E1 then (y0 i).1.1 j else 0) * (v i).1.2 j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [va i j, zero_mul, add_zero]
    by_cases hj : (⟨i, j⟩ : (Σ i : Fin r, Fin (m i))) ∈ E1
    · rw [if_pos hj, xa i j hj]
    · rw [if_neg hj, vb i j hj, mul_zero, zero_mul]
  rw [hfv, hsum]
  by_cases hi : i ∈ T
  · have := gv ⟨i, hi⟩
    rw [add_assoc, this, add_zero]
  · rw [vc i hi]
    have : ∑ j : Fin (m i), (if (⟨i, j⟩ : (Σ i : Fin r, Fin (m i))) ∈ E1 then (y0 i).1.1 j else 0) * (v i).1.2 j = 0 :=
      Finset.sum_eq_zero fun j _ => by
        rw [if_neg (fun h => hi (hE1T i j h)), zero_mul]
    rw [this]
    ring

end Upper

end PEqualNP.Outside.L_pcx_428

theorem PEqualNP.Outside.L_pcx_428 : (∀ (r : ℕ) (m : Fin r → ℕ) (d e : ℕ),
  let F := ZMod 2
  let V := fun i : Fin r => (Fin (m i) → F) × (Fin (m i) → F)
  let X := (i : Fin r) → V i × F
  let Y := Fin r → F
  let f := fun (x : X) (i : Fin r) =>
    (x i).2 + ∑ j : Fin (m i), (x i).1.1 j * (x i).1.2 j
  let N := ∑ i : Fin r, (2*m i+1)
  (∃ (first : X →ₗ[F] (Fin d → F))
     (second : (Fin d → F) → X →ₗ[F] (Fin e → F))
     (out : (Fin d → F) → (Fin e → F) → Y),
     ∀ x : X, out (first x) (second (first x) x) = f x) ↔
    N ≤ 2*d+e ∧ ∃ T : Finset (Fin r), T.card ≤ e ∧ N ≤ d+e+∑ i ∈ T, m i) := by
  intro r m d e
  dsimp only
  constructor
  · rintro ⟨first, second, out, h⟩
    exact PEqualNP.Outside.L_pcx_428.lower_bound m d e first second out h
  · rintro ⟨h1, T, hT, h2⟩
    exact PEqualNP.Outside.L_pcx_428.upper_bound m d e T h1 hT h2
