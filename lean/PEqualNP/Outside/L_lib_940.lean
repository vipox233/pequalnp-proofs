import Mathlib
import PEqualNP.Defs

open scoped BigOperators

namespace PEqualNP.Outside.L_lib_940

open Classical

abbrev F2 := ZMod 2

lemma f2_eq_zero_or_one (x : F2) : x = 0 ∨ x = 1 := by
  rcases x with ⟨v, hv⟩
  interval_cases v
  · left; rfl
  · right; rfl

lemma fin2_cases (x : Fin 2) : x = 0 ∨ x = 1 := by
  rcases x with ⟨v, hv⟩
  interval_cases v
  · left; rfl
  · right; rfl

def nextIdx {n : ℕ} (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩

def prevIdx {n : ℕ} (i : Fin n) : Fin n :=
  ⟨(i.val + n - 1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩

lemma nextIdx_prevIdx {n : ℕ} (i : Fin n) : nextIdx (prevIdx i) = i := by
  ext
  simp only [nextIdx, prevIdx]
  have hi := i.isLt
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) hi
  by_cases h0 : i.val = 0
  · rw [h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega : n - 1 < n)]
    have h1 : n - 1 + 1 = n := by omega
    rw [h1, Nat.mod_self]
  · have h1 : (i.val + n - 1) % n = i.val - 1 := by
      have h2 : i.val + n - 1 = (i.val - 1) + n := by omega
      rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [h1]
    have h3 : i.val - 1 + 1 = i.val := by omega
    rw [h3, Nat.mod_eq_of_lt hi]

lemma prevIdx_nextIdx {n : ℕ} (i : Fin n) : prevIdx (nextIdx i) = i := by
  ext
  simp only [nextIdx, prevIdx]
  have hi := i.isLt
  by_cases hlast : i.val + 1 = n
  · rw [hlast, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt (by omega : n - 1 < n)]
    omega
  · rw [Nat.mod_eq_of_lt (by omega : i.val + 1 < n)]
    have h1 : i.val + 1 + n - 1 = i.val + n := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hi]

lemma nextIdx_injective {n : ℕ} : Function.Injective (@nextIdx n) := by
  intro i j hij
  have := congrArg prevIdx hij
  simpa [prevIdx_nextIdx] using this

lemma prevIdx_injective {n : ℕ} : Function.Injective (@prevIdx n) := by
  intro i j hij
  have := congrArg nextIdx hij
  simpa [nextIdx_prevIdx] using this

def hMat {n : ℕ} (i : Fin n) (b : Fin 4) : F2 :=
  if i.val % 2 = b.val / 2 ∧ (i.val / 2 % 3 = b.val % 2 ∨ i.val / 2 % 3 = 2)
  then (1 : F2) else 0

def laneSet {n : ℕ} (b : Fin 2) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => i.val % 2 = b.val)

def endsSet {n : ℕ} [DecidableEq (Fin n)] (S : Finset (Fin n)) : Finset (Fin n) :=
  S.filter (fun i => nextIdx i ∉ S)

def runsCard {n : ℕ} [DecidableEq (Fin n)] (S : Finset (Fin n)) : ℕ :=
  (endsSet S).card

-- Section 1: Counting bases and rewriting actual S via valid/full columns

lemma card_linIndep_fin (d : ℕ) :
    ∀ k ≤ d,
      (Finset.univ.filter (fun f : Fin k → (Fin d → F2) => LinearIndependent F2 f)).card =
        ∏ i ∈ Finset.range k, (2 ^ d - 2 ^ i) := by
  intro k
  induction k with
  | zero =>
    intro _
    simp only [Finset.range_zero, Finset.prod_empty]
    have huniv : Finset.univ.filter (fun f : Fin 0 → (Fin d → F2) => LinearIndependent F2 f) =
        Finset.univ := by
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact iff_true_intro (linearIndependent_empty_type (R := F2) (v := f))
    rw [huniv, Finset.card_univ, Fintype.card_unique]
  | succ k ih =>
    intro hkd
    rw [Finset.prod_range_succ, ← ih (Nat.le_of_succ_le hkd)]
    let e : (Fin (k + 1) → (Fin d → F2)) ≃ (Fin k → (Fin d → F2)) × (Fin d → F2) :=
      { toFun := fun f => (fun i => f i.castSucc, f (Fin.last k))
        invFun := fun p => Fin.lastCases p.2 p.1
        left_inv := fun f => by
          ext i j
          refine Fin.lastCases ?_ (fun r => ?_) i <;> simp
        right_inv := fun p => Prod.ext (by ext i j; simp) (by ext j; simp) }
    have hlin : ∀ (g : Fin k → (Fin d → F2)) (x : Fin d → F2),
        LinearIndependent F2 (Fin.lastCases x g) ↔
          LinearIndependent F2 g ∧ x ∉ Submodule.span F2 (Set.range g) := by
      intro g x
      constructor
      · intro h
        have hg : LinearIndependent F2 g := by
          have hsub := h.comp Fin.castSucc (Fin.castSucc_injective k)
          convert hsub using 1
          ext i j
          simp
        refine ⟨hg, ?_⟩
        intro hx
        rw [Submodule.mem_span_range_iff_exists_fun] at hx
        obtain ⟨c, hc⟩ := hx
        have hzero : (∑ i : Fin (k + 1),
            Fin.lastCases (motive := fun _ => F2) (1 : F2) c i •
            Fin.lastCases (motive := fun _ => Fin d → F2) x g i) = 0 := by
          rw [Fin.sum_univ_castSucc]
          simp only [Fin.lastCases_castSucc, Fin.lastCases_last, one_smul]
          rw [hc]
          ext j
          simp only [Pi.add_apply, Pi.zero_apply]
          have h2 : ∀ a : F2, a + a = 0 := fun a => by rcases f2_eq_zero_or_one a with rfl | rfl <;> decide
          exact h2 (x j)
        have hcoeff := Fintype.linearIndependent_iff.mp h
          (Fin.lastCases (motive := fun _ => F2) (1 : F2) c) hzero (Fin.last k)
        simp at hcoeff
      · rintro ⟨hg, hx⟩
        rw [Fintype.linearIndependent_iff]
        intro c hc
        rw [Fin.sum_univ_castSucc] at hc
        simp only [Fin.lastCases_castSucc, Fin.lastCases_last] at hc
        have hlast0 : c (Fin.last k) = 0 := by
          rcases f2_eq_zero_or_one (c (Fin.last k)) with h0 | h1
          · exact h0
          · exfalso
            rw [h1, one_smul] at hc
            have hxeq : x = ∑ i : Fin k, c i.castSucc • g i := by
              ext j
              have hcj := congrFun hc j
              simp only [Pi.add_apply, Pi.zero_apply] at hcj
              have h2 : ∀ a b : F2, a + b = 0 → b = a := by
                intro a b hab
                rcases f2_eq_zero_or_one a with rfl | rfl <;>
                  rcases f2_eq_zero_or_one b with rfl | rfl <;> simp_all
              exact h2 _ _ hcj
            apply hx
            rw [Submodule.mem_span_range_iff_exists_fun]
            exact ⟨fun i => c i.castSucc, hxeq.symm⟩
        rw [hlast0, zero_smul, add_zero] at hc
        have hrest := Fintype.linearIndependent_iff.mp hg (fun i => c i.castSucc) hc
        intro i
        refine Fin.lastCases hlast0 (fun j => hrest j) i
    let S_good := Finset.univ.filter (fun g : Fin k → (Fin d → F2) => LinearIndependent F2 g)
    have hcard_eq :
        (Finset.univ.filter (fun f : Fin (k + 1) → (Fin d → F2) => LinearIndependent F2 f)).card =
          ∑ g ∈ S_good, (Finset.univ.filter (fun x : Fin d → F2 => x ∉ Submodule.span F2 (Set.range g))).card := by
      have h1 :
          (Finset.univ.filter (fun f : Fin (k + 1) → (Fin d → F2) => LinearIndependent F2 f)).card =
            (Finset.univ.filter (fun p : (Fin k → (Fin d → F2)) × (Fin d → F2) =>
              LinearIndependent F2 p.1 ∧ p.2 ∉ Submodule.span F2 (Set.range p.1))).card := by
        refine Finset.card_bij (fun f _ => e f) ?_ ?_ ?_
        · intro f hf
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
          have heq : Fin.lastCases (e f).2 (e f).1 = f := e.left_inv f
          exact (hlin (e f).1 (e f).2).mp (heq.symm ▸ hf)
        · intro f₁ _ f₂ _ h; exact e.injective h
        · intro p hp
          refine ⟨e.symm p, ?_, e.right_inv p⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
          exact (hlin p.1 p.2).mpr hp
      rw [h1]
      have h2 :
          (Finset.univ.filter (fun p : (Fin k → (Fin d → F2)) × (Fin d → F2) =>
              LinearIndependent F2 p.1 ∧ p.2 ∉ Submodule.span F2 (Set.range p.1))) =
            (S_good.sigma (fun g => Finset.univ.filter (fun x : Fin d → F2 => x ∉ Submodule.span F2 (Set.range g)))).map
              ⟨fun q => (q.1, q.2), fun a b hab => by
                rcases a with ⟨a1, a2⟩; rcases b with ⟨b1, b2⟩
                simp only [Prod.mk.injEq] at hab
                rcases hab with ⟨h1, h2⟩; subst h1; subst h2; rfl⟩ := by
        ext ⟨g, x⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Finset.mem_sigma,
          Function.Embedding.coeFn_mk, S_good]
        constructor
        · rintro ⟨hg, hx⟩
          exact ⟨⟨g, x⟩, ⟨hg, hx⟩, rfl⟩
        · rintro ⟨⟨g', x'⟩, ⟨hg', hx'⟩, heq⟩
          cases heq
          exact ⟨hg', hx'⟩
      rw [h2, Finset.card_map, Finset.card_sigma]
    rw [hcard_eq]
    have hconst : ∀ g ∈ S_good,
        (Finset.univ.filter (fun x : Fin d → F2 => x ∉ Submodule.span F2 (Set.range g))).card = 2 ^ d - 2 ^ k := by
      intro g hg
      simp only [S_good, Finset.mem_filter, Finset.mem_univ, true_and] at hg
      have hcompl :
          (Finset.univ.filter (fun x : Fin d → F2 => x ∈ Submodule.span F2 (Set.range g))).card +
          (Finset.univ.filter (fun x : Fin d → F2 => x ∉ Submodule.span F2 (Set.range g))).card =
            2 ^ d := by
        rw [Finset.card_filter_add_card_filter_not]
        simp only [Finset.card_univ, Fintype.card_pi, Fintype.card_fin, ZMod.card, Finset.prod_const]
      have hspan_card :
          (Finset.univ.filter (fun x : Fin d → F2 => x ∈ Submodule.span F2 (Set.range g))).card = 2 ^ k := by
        let b : Module.Basis (Fin k) F2 (Submodule.span F2 (Set.range g)) := Module.Basis.span hg
        have heq : (Finset.univ.filter (fun x : Fin d → F2 => x ∈ Submodule.span F2 (Set.range g))).card =
            (Finset.univ : Finset (Fin k → F2)).card := by
          refine Finset.card_bij
            (fun x hx => b.equivFun ⟨x, (Finset.mem_filter.mp hx).2⟩) ?_ ?_ ?_
          · intro x _; exact Finset.mem_univ _
          · intro x₁ hx₁ x₂ hx₂ h
            have h' := b.equivFun.injective h
            exact congrArg Subtype.val h'
          · intro c _
            refine ⟨(b.equivFun.symm c).1, ?_, ?_⟩
            · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              exact (b.equivFun.symm c).2
            · exact b.equivFun.apply_symm_apply c
        rw [heq, Finset.card_univ]
        simp [Fintype.card_pi, ZMod.card]
      omega
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul]

lemma card_bases_submodule {n : ℕ} (U : Submodule F2 (Fin n → F2)) (d : ℕ)
    (hU : Module.finrank F2 U = d) :
    (Finset.univ.filter (fun f : Fin d → (Fin n → F2) =>
       LinearIndependent F2 f ∧ Submodule.span F2 (Set.range f) = U)).card =
      ∏ i ∈ Finset.range d, (2 ^ d - 2 ^ i) := by
  rw [← card_linIndep_fin d d (le_refl d)]
  let bU : Module.Basis (Fin d) F2 U := Module.finBasisOfFinrankEq F2 U hU
  let e : U ≃ₗ[F2] (Fin d → F2) := bU.equivFun
  refine Finset.card_bij
    (fun f hf => fun r => e ⟨f r, by
      have hsp := (Finset.mem_filter.mp hf).2.2
      rw [← hsp]
      exact Submodule.subset_span (Set.mem_range_self r)⟩) ?_ ?_ ?_
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
    rcases hf with ⟨hlin, hsp⟩
    rw [Fintype.linearIndependent_iff] at hlin ⊢
    intro c hc
    apply hlin c
    have hc' : (∑ r : Fin d, c r • (⟨f r, by rw [← hsp]; exact Submodule.subset_span ⟨r, rfl⟩⟩ : U)) = 0 := by
      apply e.injective
      rw [map_sum, map_zero]
      simpa only [map_smul] using hc
    have hval := congrArg Subtype.val hc'
    simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower, ZeroMemClass.coe_zero] using hval
  · intro f₁ hf₁ f₂ hf₂ heq
    ext r j
    have h1 := congrFun heq r
    have h2 := e.injective h1
    exact congrFun (congrArg Subtype.val h2) j
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    let f : Fin d → (Fin n → F2) := fun r => (e.symm (g r)).1
    have hf_lin : LinearIndependent F2 f := by
      rw [Fintype.linearIndependent_iff] at hg ⊢
      intro c hc
      apply hg c
      have hc' : (∑ r : Fin d, c r • e.symm (g r)) = 0 := by
        apply Subtype.ext
        simpa [f] using hc
      have := congrArg e hc'
      simpa only [map_sum, map_smul, LinearEquiv.apply_symm_apply, map_zero] using this
    have hf_le : Submodule.span F2 (Set.range f) ≤ U := by
      rw [Submodule.span_le]
      rintro _ ⟨r, rfl⟩
      exact (e.symm (g r)).2
    have hf_sp : Submodule.span F2 (Set.range f) = U := by
      have hfin1 : Module.finrank F2 (Submodule.span F2 (Set.range f)) = d := by
        rw [finrank_span_eq_card hf_lin, Fintype.card_fin]
      exact Submodule.eq_of_le_of_finrank_eq hf_le (by rw [hfin1, hU])
    refine ⟨f, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hf_lin, hf_sp⟩
    · ext r j
      simp [f]

lemma adj_rank_le_one_iff {d : ℕ} (u v : Fin d → F2) :
    (∀ r₁ r₂, u r₁ * v r₂ = v r₁ * u r₂) ↔ (u = 0 ∨ v = 0 ∨ u = v) := by
  constructor
  · intro h
    by_cases hu : u = 0
    · exact Or.inl hu
    · by_cases hv : v = 0
      · exact Or.inr (Or.inl hv)
      · right; right
        have ⟨r₁, hr₁⟩ : ∃ r₁, u r₁ ≠ 0 := by
          by_contra hall; push_neg at hall; exact hu (funext hall)
        have hur₁ : u r₁ = 1 := by
          rcases f2_eq_zero_or_one (u r₁) with h0 | h1
          · exact absurd h0 hr₁
          · exact h1
        have hvr₁ : v r₁ = 1 := by
          rcases f2_eq_zero_or_one (v r₁) with h0 | h1
          · exfalso; apply hv; ext r
            have := h r₁ r
            rw [hur₁, one_mul, h0, zero_mul] at this
            exact this
          · exact h1
        ext r
        have := h r₁ r
        rw [hur₁, one_mul, hvr₁, one_mul] at this
        exact this.symm
  · rintro (rfl | rfl | rfl) r₁ r₂ <;> simp

noncomputable def validCols (n m : ℕ) (S : Finset (Fin n)) : Finset (Fin n → Fin m → F2) :=
  Finset.univ.filter (fun c =>
    (∀ i, c i ≠ 0 ↔ i ∈ S) ∧
    (∀ i ∈ S, nextIdx i ∈ S → c i = c (nextIdx i)) ∧
    (∀ b : Fin 4, (∑ i : Fin n, hMat i b • c i) = 0))

noncomputable def fullCols (n d : ℕ) (S : Finset (Fin n)) : Finset (Fin n → Fin d → F2) :=
  (validCols n d S).filter (fun c => LinearIndependent F2 (fun r i => c i r))

lemma actual_eq_fullCols_card (n d : ℕ) (S : Finset (Fin n))
    [Fintype (Submodule F2 (Fin n → F2))] :
    let good := fun U : Submodule F2 (Fin n → F2) =>
      (∀ x ∈ U, ∀ b : Fin 4, (∑ i, hMat i b * x i) = 0) ∧
      (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (nextIdx i) = x (nextIdx i) * y i)
    let supp := fun U : Submodule F2 (Fin n → F2) =>
      Finset.univ.filter (fun i : Fin n => ∃ x ∈ U, x i ≠ 0)
    let spaces := (Finset.univ : Finset (Submodule F2 (Fin n → F2))).filter good
    let layer := spaces.filter (fun U : Submodule F2 (Fin n → F2) => Module.finrank F2 U = d)
    let B := ∏ i ∈ Finset.range d, (2 ^ d - 2 ^ i : ℕ)
    B * (layer.filter (fun U => supp U = S)).card = (fullCols n d S).card := by
  intro good supp spaces layer B
  let L := layer.filter (fun U => supp U = S)
  let Mset := Finset.univ.filter (fun M : Fin d → (Fin n → F2) =>
    LinearIndependent F2 M ∧
    good (Submodule.span F2 (Set.range M)) ∧
    supp (Submodule.span F2 (Set.range M)) = S)
  have hBM : B * L.card = Mset.card := by
    have hfib : Mset.card = ∑ U ∈ L, (Mset.filter (fun M => Submodule.span F2 (Set.range M) = U)).card := by
      rw [← Finset.card_eq_sum_card_fiberwise]
      intro M hM
      simp only [Finset.mem_coe, Mset, Finset.mem_filter, Finset.mem_univ, true_and] at hM
      simp only [Finset.mem_coe, L, layer, spaces, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨⟨hM.2.1, by rw [finrank_span_eq_card hM.1, Fintype.card_fin]⟩, hM.2.2⟩
    rw [hfib]
    have hconst : ∀ U ∈ L, (Mset.filter (fun M => Submodule.span F2 (Set.range M) = U)).card = B := by
      intro U hU
      simp only [L, layer, spaces, Finset.mem_filter, Finset.mem_univ, true_and] at hU
      have heq : Mset.filter (fun M => Submodule.span F2 (Set.range M) = U) =
          Finset.univ.filter (fun M : Fin d → (Fin n → F2) =>
            LinearIndependent F2 M ∧ Submodule.span F2 (Set.range M) = U) := by
        ext M
        simp only [Mset, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨⟨h1, _, _⟩, h2⟩; exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩; rw [h2]; exact ⟨⟨h1, hU.1.1, hU.2⟩, rfl⟩
      rw [heq]
      exact card_bases_submodule U d hU.1.2
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, mul_comm]
  rw [hBM]
  refine Finset.card_bij (fun M _ => fun i r => M r i) ?_ ?_ ?_
  · intro M hM
    simp only [Mset, Finset.mem_filter, Finset.mem_univ, true_and] at hM
    rcases hM with ⟨hlin, ⟨hpar, hadj⟩, hsupp⟩
    simp only [fullCols, validCols, Finset.mem_filter, Finset.mem_univ, true_and]
    have hmemM : ∀ r : Fin d, M r ∈ Submodule.span F2 (Set.range M) :=
      fun r => Submodule.subset_span ⟨r, rfl⟩
    have hsupp_iff : ∀ i : Fin n, (fun r => M r i) ≠ 0 ↔ i ∈ S := by
      intro i
      rw [← hsupp]
      simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hne
        have ⟨r, hr⟩ : ∃ r, M r i ≠ 0 := by
          by_contra hall; push_neg at hall; exact hne (funext hall)
        exact ⟨M r, hmemM r, hr⟩
      · rintro ⟨x, hx, hxi⟩ h0
        rw [Submodule.mem_span_range_iff_exists_fun] at hx
        obtain ⟨c, rfl⟩ := hx
        apply hxi
        have hzero : ∀ r, M r i = 0 := fun r => congrFun h0 r
        simp [hzero]
    refine ⟨⟨hsupp_iff, ?_, ?_⟩, hlin⟩
    · intro i hi hni
      have hrel : ∀ r₁ r₂, M r₁ i * M r₂ (nextIdx i) = M r₁ (nextIdx i) * M r₂ i :=
        fun r₁ r₂ => hadj (M r₁) (hmemM r₁) (M r₂) (hmemM r₂) i
      rcases (adj_rank_le_one_iff (fun r => M r i) (fun r => M r (nextIdx i))).mp hrel with h1 | h2 | h3
      · exact absurd h1 ((hsupp_iff i).mpr hi)
      · exact absurd h2 ((hsupp_iff (nextIdx i)).mpr hni)
      · exact h3
    · intro b
      ext r
      simpa [Finset.sum_apply] using hpar (M r) (hmemM r) b
  · intro M₁ _ M₂ _ h
    ext r i
    exact congrFun (congrFun h i) r
  · intro c hc
    simp only [fullCols, validCols, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    rcases hc with ⟨⟨hsupp, hadj, hpar⟩, hlin⟩
    let M : Fin d → (Fin n → F2) := fun r i => c i r
    refine ⟨M, ?_, rfl⟩
    simp only [Mset, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hlin, ⟨?_, ?_⟩, ?_⟩
    · intro x hx b
      rw [Submodule.mem_span_range_iff_exists_fun] at hx
      obtain ⟨α, rfl⟩ := hx
      have h1 : (∑ i : Fin n, hMat i b * (∑ r : Fin d, α r • M r) i) =
          ∑ r : Fin d, α r * (∑ i : Fin n, hMat i b * c i r) := by
        simp_rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun r _ => ?_)
        refine Finset.sum_congr rfl (fun i _ => by ring)
      rw [h1]
      apply Finset.sum_eq_zero
      intro r _
      have hpr := congrFun (hpar b) r
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hpr
      rw [hpr, mul_zero]
    · intro x hx y hy i
      rw [Submodule.mem_span_range_iff_exists_fun] at hx hy
      obtain ⟨α, rfl⟩ := hx
      obtain ⟨β, rfl⟩ := hy
      by_cases hi : i ∈ S
      · by_cases hni : nextIdx i ∈ S
        · have heq := hadj i hi hni
          have hxe : (∑ r : Fin d, α r • M r) (nextIdx i) = (∑ r : Fin d, α r • M r) i := by
            simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, M, heq]
          have hye : (∑ r : Fin d, β r • M r) (nextIdx i) = (∑ r : Fin d, β r • M r) i := by
            simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, M, heq]
          rw [hxe, hye]
        · have h0 : c (nextIdx i) = 0 := by
            by_contra hne; exact hni ((hsupp (nextIdx i)).mp hne)
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, M, h0, Pi.zero_apply,
            mul_zero, Finset.sum_const_zero, zero_mul]
      · have h0 : c i = 0 := by
          by_contra hne; exact hi ((hsupp i).mp hne)
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, M, h0, Pi.zero_apply,
          mul_zero, Finset.sum_const_zero, zero_mul]
    · ext i
      simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hsupp i]
      constructor
      · rintro ⟨x, hx, hxi⟩ h0
        rw [Submodule.mem_span_range_iff_exists_fun] at hx
        obtain ⟨α, rfl⟩ := hx
        apply hxi
        simp [M, h0]
      · intro hne
        have ⟨r, hr⟩ : ∃ r, c i r ≠ 0 := by
          by_contra hall; push_neg at hall; exact hne (funext hall)
        exact ⟨M r, Submodule.subset_span ⟨r, rfl⟩, hr⟩

lemma fullCols_empty (n d : ℕ) (hd : 1 ≤ d) : (fullCols n d ∅).card = 0 := by
  rw [Finset.card_eq_zero]
  ext c
  simp only [fullCols, validCols, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
    iff_false, not_and]
  rintro ⟨hsupp, _, _⟩ hlin
  have hc0 : ∀ i, c i = 0 := fun i => by
    by_contra hne; exact hsupp i hne
  have := Fintype.linearIndependent_iff.mp hlin (Pi.single ⟨0, by omega⟩ 1) (by
    ext i; simp [hc0 i]) ⟨0, by omega⟩
  simp at this

lemma fullCols_univ (n d : ℕ) (hn : 1 ≤ n) (hd : 2 ≤ d) :
    (fullCols n d Finset.univ).card = 0 := by
  rw [Finset.card_eq_zero]
  ext c
  simp only [fullCols, validCols, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
    iff_false, not_and]
  rintro ⟨_, hadj, _⟩ hlin
  have hconst : ∀ i : Fin n, c i = c ⟨0, by omega⟩ := by
    intro i
    have hstep : ∀ k : ℕ, (hk : k < n) → c ⟨k, hk⟩ = c ⟨0, by omega⟩ := by
      intro k
      induction k with
      | zero => intro _; rfl
      | succ k ih =>
        intro hk
        have hprev : c ⟨k, by omega⟩ = c ⟨0, by omega⟩ := ih (by omega)
        have hnxt : nextIdx (⟨k, by omega⟩ : Fin n) = ⟨k + 1, hk⟩ := by
          ext; simp [nextIdx, Nat.mod_eq_of_lt hk]
        have heq := hadj ⟨k, by omega⟩ trivial trivial
        rw [hnxt] at heq
        exact heq.symm.trans hprev
    exact hstep i.val i.isLt
  let r0 : Fin d := ⟨0, by omega⟩
  let r1 : Fin d := ⟨1, by omega⟩
  have hr01 : r0 ≠ r1 := by intro h; have := congrArg Fin.val h; simp [r0, r1] at this
  let u := c ⟨0, by omega⟩
  rcases f2_eq_zero_or_one (u r0) with h0 | h0
  · have h := Fintype.linearIndependent_iff.mp hlin (Pi.single r0 1) (by
      ext i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Pi.single_apply,
        ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, hconst i]
      exact h0) r0
    simp at h
  · rcases f2_eq_zero_or_one (u r1) with h1 | h1
    · have h := Fintype.linearIndependent_iff.mp hlin (Pi.single r1 1) (by
        ext i
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Pi.single_apply,
          ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, hconst i]
        exact h1) r1
      simp at h
    · have h := Fintype.linearIndependent_iff.mp hlin (Pi.single r0 1 + Pi.single r1 1) (by
        ext i
        simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_mul,
          Finset.sum_add_distrib]
        simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
          ↓reduceIte, hconst i, u, h0, h1]
        show (1 : F2) + 1 = 0
        decide) r0
      simp [Pi.single_apply, hr01] at h

lemma fullCols_diff_le (n d : ℕ) (hd : 2 ≤ d) (S : Finset (Fin n)) :
    (validCols n d S).card - (fullCols n d S).card ≤
      (2 ^ d - 1) * (validCols n (d - 1) S).card := by
  have hsub : fullCols n d S ⊆ validCols n d S := Finset.filter_subset _ _
  have hsd : (validCols n d S \ fullCols n d S).card = (validCols n d S).card - (fullCols n d S).card := by
    have h1 := Finset.card_sdiff_add_card_eq_card hsub
    omega
  rw [← hsd]
  let nzA : Finset (Fin d → F2) := Finset.univ.filter (fun α : Fin d → F2 => α ≠ 0)
  have hnzA_card : nzA.card = 2 ^ d - 1 := by
    have h1 : nzA = Finset.univ.erase (0 : Fin d → F2) := by ext α; simp [nzA]
    rw [h1, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    simp [Fintype.card_pi, ZMod.card]
  have hcover : (validCols n d S \ fullCols n d S) ⊆
      nzA.biUnion (fun α => (validCols n d S).filter (fun c => ∀ i, (∑ r : Fin d, α r * c i r) = 0)) := by
    intro c hc
    simp only [Finset.mem_sdiff, fullCols, Finset.mem_filter] at hc
    rcases hc with ⟨hvc, hnot⟩
    have hnlin : ¬ LinearIndependent F2 (fun r i => c i r) := fun h => hnot ⟨hvc, h⟩
    rw [Fintype.linearIndependent_iff] at hnlin
    push_neg at hnlin
    obtain ⟨α, hαsum, r0, hr0⟩ := hnlin
    have hαne : α ≠ 0 := fun h => hr0 (by simp [h])
    rw [Finset.mem_biUnion]
    refine ⟨α, by simp [nzA, hαne], ?_⟩
    simp only [Finset.mem_filter]
    refine ⟨hvc, fun i => ?_⟩
    have := congrFun hαsum i
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
  have hle1 := Finset.card_le_card hcover
  have hle2 := Finset.card_biUnion_le (s := nzA)
    (t := fun α => (validCols n d S).filter (fun c => ∀ i, (∑ r : Fin d, α r * c i r) = 0))
  have hper : ∀ α ∈ nzA,
      ((validCols n d S).filter (fun c => ∀ i, (∑ r : Fin d, α r * c i r) = 0)).card ≤
        (validCols n (d - 1) S).card := by
    intro α hα
    simp only [nzA, Finset.mem_filter, Finset.mem_univ, true_and] at hα
    have ⟨r0, hr0⟩ : ∃ r0 : Fin d, α r0 ≠ 0 := by
      by_contra hall; push_neg at hall; exact hα (funext hall)
    have hαr0 : α r0 = 1 := by
      rcases f2_eq_zero_or_one (α r0) with h0 | h1
      · exact absurd h0 hr0
      · exact h1
    have hd1 : d - 1 + 1 = d := by omega
    let eFin : Fin (d - 1 + 1) ≃ Fin d := finCongr hd1
    let r0' : Fin (d - 1 + 1) := eFin.symm r0
    let dropR : Fin (d - 1) → Fin d := fun j => eFin (r0'.succAbove j)
    have hdrop_ne : ∀ j, dropR j ≠ r0 := by
      intro j h
      have h' : r0'.succAbove j = r0' := eFin.injective (by simpa [dropR, r0'] using h)
      exact Fin.succAbove_ne r0' j h'
    have hrecover : ∀ (c : Fin n → Fin d → F2),
        (∀ i, (∑ r : Fin d, α r * c i r) = 0) →
        ∀ i, c i r0 = ∑ j : Fin (d - 1), α (dropR j) * c i (dropR j) := by
      intro c hc i
      have hsum := hc i
      rw [← Equiv.sum_comp eFin, Fin.sum_univ_succAbove _ r0'] at hsum
      have he0 : eFin r0' = r0 := eFin.apply_symm_apply r0
      rw [he0, hαr0, one_mul] at hsum
      have h2 : ∀ a b : F2, a + b = 0 → a = b := by
        intro a b hab
        rcases f2_eq_zero_or_one a with rfl | rfl <;>
          rcases f2_eq_zero_or_one b with rfl | rfl <;> simp_all
      exact h2 _ _ hsum
    refine Finset.card_le_card_of_injOn (fun c => fun i j => c i (dropR j)) ?_ ?_
    · intro c hc
      simp only [Finset.mem_coe, Finset.mem_filter, validCols, Finset.mem_univ, true_and] at hc ⊢
      rcases hc with ⟨⟨hsupp, hadj, hpar⟩, horth⟩
      refine ⟨?_, ?_, ?_⟩
      · intro i
        rw [← hsupp i]
        constructor
        · intro hne h0; apply hne; ext j; simp [h0]
        · intro hne h0
          apply hne
          ext r
          by_cases hr : r = r0
          · subst hr
            rw [hrecover c horth i]
            apply Finset.sum_eq_zero
            intro j _
            have hj := congrFun h0 j
            simp [hj]
          · have hr' : eFin.symm r ≠ r0' := fun h => hr (by
              have := congrArg eFin h; simpa [r0'] using this)
            obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hr'
            have hdj : dropR j = r := by simp [dropR, hj]
            have hj0 := congrFun h0 j
            simpa [hdj] using hj0
      · intro i hi hni
        ext j
        exact congrFun (hadj i hi hni) (dropR j)
      · intro b
        ext j
        have := congrFun (hpar b) (dropR j)
        simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
    · intro c₁ hc₁ c₂ hc₂ heq
      simp only [Finset.mem_coe, Finset.mem_filter] at hc₁ hc₂
      ext i r
      by_cases hr : r = r0
      · subst hr
        rw [hrecover c₁ hc₁.2 i, hrecover c₂ hc₂.2 i]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        have hval := congrFun (congrFun heq i) j
        dsimp only at hval
        rw [hval]
      · have hr' : eFin.symm r ≠ r0' := fun h => hr (by
          have := congrArg eFin h; simpa [r0'] using this)
        obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hr'
        have hdj : dropR j = r := by simp [dropR, hj]
        have := congrFun (congrFun heq i) j
        simpa [hdj] using this
  calc
    (validCols n d S \ fullCols n d S).card
        ≤ ∑ α ∈ nzA, ((validCols n d S).filter (fun c => ∀ i, (∑ r : Fin d, α r * c i r) = 0)).card :=
          le_trans hle1 hle2
    _ ≤ ∑ _α ∈ nzA, (validCols n (d - 1) S).card := Finset.sum_le_sum hper
    _ = (2 ^ d - 1) * (validCols n (d - 1) S).card := by
          rw [Finset.sum_const, smul_eq_mul, hnzA_card]

-- Section 2: Run collapse and exact Fourier representation of validCols

def runEndAux {n : ℕ} [DecidableEq (Fin n)] (S : Finset (Fin n)) : ℕ → Fin n → Fin n
  | 0, i => i
  | k + 1, i => if nextIdx i ∉ S then i else runEndAux S k (nextIdx i)

def runEnd {n : ℕ} [DecidableEq (Fin n)] (S : Finset (Fin n)) (i : Fin n) : Fin n :=
  runEndAux S n i

lemma nextIdx_iterate_val {n : ℕ} (k : ℕ) (i : Fin n) :
    (nextIdx^[k] i).val = (i.val + k) % n := by
  induction k with
  | zero =>
    simp [Nat.mod_eq_of_lt i.isLt]
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    simp only [nextIdx, ih]
    rw [Nat.mod_add_mod, Nat.add_assoc]

lemma exists_step_not_mem {n : ℕ} (S : Finset (Fin n)) (hne : S ≠ Finset.univ) (i : Fin n) :
    ∃ k < n, nextIdx^[k] i ∉ S := by
  have ⟨z, hz⟩ : ∃ z : Fin n, z ∉ S := by
    by_contra hall; push_neg at hall
    apply hne; ext x; simp [hall x]
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  let k := (z.val + n - i.val) % n
  refine ⟨k, Nat.mod_lt _ hn, ?_⟩
  have heq : nextIdx^[k] i = z := by
    ext
    rw [nextIdx_iterate_val]
    have hk : (i.val + k) % n = z.val := by
      dsimp only [k]
      rw [Nat.add_mod_mod]
      have hsum : i.val + (z.val + n - i.val) = z.val + n := by omega
      rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt z.isLt]
    exact hk
  rw [heq]; exact hz

lemma runEndAux_spec {n : ℕ} [DecidableEq (Fin n)] (S : Finset (Fin n)) :
    ∀ (fuel : ℕ) (i : Fin n), i ∈ S → (∃ k < fuel, nextIdx^[k + 1] i ∉ S) →
      runEndAux S fuel i ∈ endsSet S ∧
      (∀ (m : ℕ) (c : Fin n → Fin m → F2),
        (∀ x ∈ S, nextIdx x ∈ S → c x = c (nextIdx x)) → c i = c (runEndAux S fuel i)) ∧
      (∀ f : ℕ, fuel ≤ f → runEndAux S f i = runEndAux S fuel i) := by
  intro fuel
  induction fuel with
  | zero =>
    intro i _ ⟨k, hk, _⟩; omega
  | succ fuel ih =>
    intro i hi ⟨k, hk, hnk⟩
    by_cases h1 : nextIdx i ∉ S
    · refine ⟨?_, ?_, ?_⟩
      · simp [runEndAux, h1, endsSet, hi]
      · intro _ _ _; simp [runEndAux, h1]
      · intro f hf
        cases f with
        | zero => omega
        | succ f => simp [runEndAux, h1]
    · push_neg at h1
      have hkpos : 0 < k := by
        by_contra h0
        have hk0 : k = 0 := by omega
        subst hk0
        simp at hnk
        exact hnk h1
      have hex : ∃ k' < fuel, nextIdx^[k' + 1] (nextIdx i) ∉ S := by
        refine ⟨k - 1, by omega, ?_⟩
        have hstep : nextIdx^[k - 1 + 1] (nextIdx i) = nextIdx^[k + 1] i := by
          have hk1 : k - 1 + 1 = k := by omega
          rw [hk1, ← Function.iterate_succ_apply]
        rw [hstep]; exact hnk
      obtain ⟨hmem, hceq, hstab⟩ := ih (nextIdx i) h1 hex
      have hne1 : ¬ (nextIdx i ∉ S) := fun h => h h1
      refine ⟨?_, ?_, ?_⟩
      · simpa [runEndAux, hne1] using hmem
      · intro m c hadj
        simp only [runEndAux, hne1, ↓reduceIte]
        exact (hadj i hi h1).trans (hceq m c hadj)
      · intro f hf
        cases f with
        | zero => omega
        | succ f =>
          simp only [runEndAux, hne1, ↓reduceIte]
          exact hstab f (by omega)

lemma runEnd_spec {n : ℕ} [DecidableEq (Fin n)] (S : Finset (Fin n)) (hne : S ≠ Finset.univ)
    (i : Fin n) (hi : i ∈ S) :
    runEnd S i ∈ endsSet S ∧
    (∀ (m : ℕ) (c : Fin n → Fin m → F2),
      (∀ x ∈ S, nextIdx x ∈ S → c x = c (nextIdx x)) → c i = c (runEnd S i)) := by
  obtain ⟨k, hk, hnk⟩ := exists_step_not_mem S hne i
  have hkpos : 0 < k := by
    by_contra h0
    have hk0 : k = 0 := by omega
    subst hk0
    exact hnk hi
  have hex : ∃ k' < n, nextIdx^[k' + 1] i ∉ S := ⟨k - 1, by omega, by
    have hk1 : k - 1 + 1 = k := by omega
    rw [hk1]; exact hnk⟩
  obtain ⟨h1, h2, _⟩ := runEndAux_spec S n i hi hex
  exact ⟨h1, h2⟩

lemma runEnd_of_mem_ends {n : ℕ} [DecidableEq (Fin n)] (S : Finset (Fin n))
    (e : Fin n) (he : e ∈ endsSet S) : runEnd S e = e := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) e.isLt
  cases n with
  | zero => omega
  | succ m =>
    have hnot : nextIdx e ∉ S := (Finset.mem_filter.mp he).2
    simp [runEnd, runEndAux, hnot]

lemma runEnd_next {n : ℕ} [DecidableEq (Fin n)] (S : Finset (Fin n)) (hne : S ≠ Finset.univ)
    (i : Fin n) (hi : i ∈ S) (hni : nextIdx i ∈ S) :
    runEnd S i = runEnd S (nextIdx i) := by
  obtain ⟨k, hk, hnk⟩ := exists_step_not_mem S hne (nextIdx i)
  have hkpos : 0 < k := by
    by_contra h0
    have hk0 : k = 0 := by omega
    subst hk0
    exact hnk hni
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have h1 : runEnd S i = runEndAux S (n - 1) (nextIdx i) := by
    have hstep : ∀ m : ℕ, 1 ≤ m → runEndAux S m i = runEndAux S (m - 1) (nextIdx i) := by
      intro m hm
      cases m with
      | zero => omega
      | succ m =>
        have hnot : ¬ (nextIdx i ∉ S) := fun h => h hni
        simp [runEndAux, hnot]
    exact hstep n hn
  rw [h1]
  have hex : ∃ k' < n - 1, nextIdx^[k' + 1] (nextIdx i) ∉ S := by
    by_cases hkn : k = n - 1
    · exfalso
      have hcy : nextIdx^[k] (nextIdx i) = i := by
        ext; rw [nextIdx_iterate_val]; simp only [nextIdx]
        rw [Nat.mod_add_mod]
        have hsum : i.val + 1 + k = i.val + n := by omega
        rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
      rw [hcy] at hnk; exact hnk hi
    · refine ⟨k - 1, by omega, ?_⟩
      have hk1 : k - 1 + 1 = k := by omega
      rw [hk1]; exact hnk
  have hstab := (runEndAux_spec S (n - 1) (nextIdx i) hni hex).2.2 n (by omega)
  exact hstab.symm

lemma runEnd_singleton {n : ℕ} [DecidableEq (Fin n)] (S : Finset (Fin n)) (hne : S ≠ Finset.univ)
    (e : Fin n) (he : e ∈ endsSet S) (hprev : prevIdx e ∉ S) :
    S.filter (fun i => runEnd S i = e) = {e} := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hi, hre⟩
    by_contra hne_ie
    have hwalk : ∀ (fuel : ℕ) (x : Fin n), x ∈ S → x ≠ e → runEndAux S fuel x = e → False := by
      intro fuel
      induction fuel with
      | zero => intro x _ hne' heq; exact hne' heq
      | succ fuel ih =>
        intro x hx hne' heq
        by_cases hnx : nextIdx x ∉ S
        · simp [runEndAux, hnx] at heq; exact hne' heq
        · push_neg at hnx
          have hne_nx : ¬ (nextIdx x ∉ S) := fun h => h hnx
          simp only [runEndAux, hne_nx, ↓reduceIte] at heq
          by_cases hxe : nextIdx x = e
          · have hxp : x = prevIdx e := by
              rw [← hxe, prevIdx_nextIdx]
            rw [hxp] at hx
            exact hprev hx
          · exact ih (nextIdx x) hnx hxe heq
    exact hwalk n i hi hne_ie hre
  · rintro rfl
    exact ⟨(Finset.mem_filter.mp he).1, runEnd_of_mem_ends S i he⟩

def runParity {n : ℕ} [DecidableEq (Fin n)] (S : Finset (Fin n)) (e : Fin n) (b : Fin 4) : F2 :=
  ∑ i ∈ S.filter (fun i => runEnd S i = e), hMat i b

def chi (x : F2) : ℝ := if x = 0 then 1 else -1

lemma chi_add (x y : F2) : chi (x + y) = chi x * chi y := by
  have h11 : (1 : F2) + 1 = 0 := rfl
  rcases f2_eq_zero_or_one x with rfl | rfl <;> rcases f2_eq_zero_or_one y with rfl | rfl <;>
    simp [chi, h11]

lemma chi_zero : chi 0 = 1 := by simp [chi]

lemma sum_chi_f2 (a : F2) : (∑ x : F2, chi (x * a)) = if a = 0 then 2 else 0 := by
  have hsum : ∀ f : F2 → ℝ, (∑ x : F2, f x) = f 0 + f 1 := fun f => by
    change (∑ x : Fin 2, f x) = f 0 + f 1
    exact Fin.sum_univ_two _
  rcases f2_eq_zero_or_one a with rfl | rfl <;> simp [hsum, chi] <;> norm_num

lemma prod_chi_sum {ι : Type*} [Fintype ι] (f : ι → F2) :
    (∏ i : ι, chi (f i)) = chi (∑ i : ι, f i) := by
  have h : ∀ (s : Finset ι), (∏ i ∈ s, chi (f i)) = chi (∑ i ∈ s, f i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [chi_zero]
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, chi_add, ih]
  exact h Finset.univ

lemma sum_chi_vec_all {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → F2) :
    (∑ v : ι → F2, ∏ i : ι, chi (v i * u i)) = if u = 0 then (2 : ℝ) ^ Fintype.card ι else 0 := by
  rw [← Fintype.prod_sum (fun i x => chi (x * u i))]
  simp_rw [sum_chi_f2]
  by_cases hu : u = 0
  · subst hu
    simp only [Pi.zero_apply, ↓reduceIte, Finset.prod_const, Finset.card_univ]
  · rw [if_neg hu]
    have ⟨i0, hi0⟩ : ∃ i0, u i0 ≠ 0 := by
      by_contra hall; push_neg at hall; exact hu (funext hall)
    exact Finset.prod_eq_zero (Finset.mem_univ i0) (if_neg hi0)

lemma sum_chi_nonzero (m : ℕ) (u : Fin m → F2) :
    (∑ w ∈ (Finset.univ.erase (0 : Fin m → F2)), ∏ j : Fin m, chi (u j * w j)) =
      if u = 0 then (2 : ℝ) ^ m - 1 else -1 := by
  have hall := sum_chi_vec_all u
  have hcard : Fintype.card (Fin m) = m := Fintype.card_fin m
  rw [hcard] at hall
  have hcomm : ∀ w : Fin m → F2, (∏ j : Fin m, chi (u j * w j)) = ∏ j : Fin m, chi (w j * u j) :=
    fun w => Finset.prod_congr rfl (fun j _ => by rw [mul_comm])
  simp_rw [hcomm]
  have hsplit := Finset.add_sum_erase Finset.univ (fun w : Fin m → F2 => ∏ j : Fin m, chi (w j * u j))
    (Finset.mem_univ (0 : Fin m → F2))
  have h0 : (∏ j : Fin m, chi ((0 : Fin m → F2) j * u j)) = 1 := by
    simp [chi_zero]
  rw [h0, hall] at hsplit
  split_ifs at hsplit ⊢ <;> linarith

lemma validCols_card_eq_fourier (n m : ℕ) (S : Finset (Fin n)) (hne : S ≠ Finset.univ) :
    ((validCols n m S).card : ℝ) =
      (1 / ((2 : ℝ) ^ m) ^ 4) *
        ∑ v : Fin 4 → Fin m → F2,
          ∏ e ∈ endsSet S,
            if (∑ b : Fin 4, runParity S e b • v b) = 0 then ((2 : ℝ) ^ m - 1) else (-1 : ℝ) := by
  let nzV : Finset (Fin m → F2) := Finset.univ.erase (0 : Fin m → F2)
  let Wset := (endsSet S → {u : Fin m → F2 // u ∈ nzV})
  have hbij : (validCols n m S).card =
      (Finset.univ.filter (fun w : Wset =>
        ∀ b : Fin 4, (∑ e : endsSet S, runParity S e.1 b • (w e).1) = 0)).card := by
    refine Finset.card_bij
      (fun c hc => fun e : endsSet S => ⟨c e.1, by
        simp only [nzV, Finset.mem_erase, Finset.mem_univ, and_true]
        have hvc := (Finset.mem_filter.mp hc).2
        have he2 := e.2
        simp only [endsSet, Finset.mem_filter] at he2
        exact (hvc.1 e.1).mpr he2.1⟩) ?_ ?_ ?_
    · intro c hc
      simp only [validCols, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      rcases hc with ⟨hsupp, hadj, hpar⟩
      intro b
      have hpart : (∑ i : Fin n, hMat i b • c i) =
          ∑ e ∈ endsSet S, runParity S e b • c e := by
        have h1 : (∑ i : Fin n, hMat i b • c i) = ∑ i ∈ S, hMat i b • c i := by
          symm
          refine Finset.sum_subset (Finset.subset_univ S) ?_
          intro i _ hi
          have h0 : c i = 0 := by by_contra h; exact hi ((hsupp i).mp h)
          simp [h0]
        rw [h1]
        rw [← Finset.sum_fiberwise_of_maps_to (g := runEnd S) (t := endsSet S)
          (fun i hi => (runEnd_spec S hne i hi).1)]
        refine Finset.sum_congr rfl (fun e _ => ?_)
        dsimp only [runParity]
        rw [Finset.sum_smul]
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have hiS := (Finset.mem_filter.mp hi).1
        have hre := (Finset.mem_filter.mp hi).2
        have hceq := (runEnd_spec S hne i hiS).2 m c hadj
        rw [hceq, hre]
      rw [Finset.sum_coe_sort (endsSet S) (fun e => runParity S e b • c e)]
      rw [← hpart]
      exact hpar b
    · intro c₁ hc₁ c₂ hc₂ heq
      simp only [validCols, Finset.mem_filter, Finset.mem_univ, true_and] at hc₁ hc₂
      ext i j
      by_cases hi : i ∈ S
      · have he1 := (runEnd_spec S hne i hi).1
        have h1 := (runEnd_spec S hne i hi).2 m c₁ hc₁.2.1
        have h2 := (runEnd_spec S hne i hi).2 m c₂ hc₂.2.1
        have h3 := congrArg Subtype.val (congrFun heq ⟨runEnd S i, he1⟩)
        exact congrFun (h1.trans (h3.trans h2.symm)) j
      · have h1 : c₁ i = 0 := by by_contra h; exact hi ((hc₁.1 i).mp h)
        have h2 : c₂ i = 0 := by by_contra h; exact hi ((hc₂.1 i).mp h)
        rw [h1, h2]
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      let c : Fin n → Fin m → F2 := fun i =>
        if hi : i ∈ S then (w ⟨runEnd S i, (runEnd_spec S hne i hi).1⟩).1 else 0
      refine ⟨c, ?_, ?_⟩
      · simp only [validCols, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, ?_, ?_⟩
        · intro i
          by_cases hi : i ∈ S
          · simp only [c, dif_pos hi, hi, iff_true]
            exact (Finset.mem_erase.mp (w ⟨runEnd S i, (runEnd_spec S hne i hi).1⟩).2).1
          · simp [c, hi]
        · intro i hi hni
          simp only [c, dif_pos hi, dif_pos hni]
          congr 2
          exact Subtype.ext (runEnd_next S hne i hi hni)
        · intro b
          have h1 : (∑ i : Fin n, hMat i b • c i) = ∑ i ∈ S, hMat i b • c i := by
            symm
            refine Finset.sum_subset (Finset.subset_univ S) ?_
            intro i _ hi; simp [c, hi]
          rw [h1, ← Finset.sum_fiberwise_of_maps_to (g := runEnd S) (t := endsSet S)
            (fun i hi => (runEnd_spec S hne i hi).1)]
          have h2 : ∀ (e : Fin n) (he : e ∈ endsSet S),
              (∑ i ∈ S.filter (fun i => runEnd S i = e), hMat i b • c i) =
                runParity S e b • (w ⟨e, he⟩).1 := by
            intro e he
            dsimp only [runParity]
            rw [Finset.sum_smul]
            refine Finset.sum_congr rfl (fun i hi => ?_)
            have hiS := (Finset.mem_filter.mp hi).1
            have hre := (Finset.mem_filter.mp hi).2
            simp only [c, dif_pos hiS]
            congr 3
            exact Subtype.ext hre
          rw [← Finset.sum_coe_sort (endsSet S) (fun e => ∑ i ∈ S.filter (fun i => runEnd S i = e), hMat i b • c i)]
          have h3 : (∑ e : endsSet S, ∑ i ∈ S.filter (fun i => runEnd S i = e.1), hMat i b • c i) =
              ∑ e : endsSet S, runParity S e.1 b • (w e).1 :=
            Finset.sum_congr rfl (fun e _ => h2 e.1 e.2)
          rw [h3]
          exact hw b
      · ext e j
        have he2 := e.2
        simp only [endsSet, Finset.mem_filter] at he2
        have heS : e.1 ∈ S := he2.1
        have hre : runEnd S e.1 = e.1 := runEnd_of_mem_ends S e.1 e.2
        simp only [c, dif_pos heS]
        have hsub : (⟨runEnd S e.1, (runEnd_spec S hne e.1 heS).1⟩ : endsSet S) = e := Subtype.ext hre
        rw [hsub]
  rw [hbij]
  have hpos : ((2 : ℝ) ^ m) ^ 4 ≠ 0 := by positivity
  have hmain :
      (((Finset.univ.filter (fun w : Wset =>
          ∀ b : Fin 4, (∑ e : endsSet S, runParity S e.1 b • (w e).1) = 0)).card : ℝ) *
        ((2 : ℝ) ^ m) ^ 4) =
        ∑ v : Fin 4 → Fin m → F2,
          ∏ e ∈ endsSet S,
            if (∑ b : Fin 4, runParity S e b • v b) = 0 then ((2 : ℝ) ^ m - 1) else (-1 : ℝ) := by
    have hstep1 :
        ∑ w : Wset, ∑ v : Fin 4 → Fin m → F2,
            ∏ b : Fin 4, ∏ j : Fin m,
              chi (v b j * (∑ e : endsSet S, runParity S e.1 b * (w e).1 j)) =
          ((Finset.univ.filter (fun w : Wset =>
            ∀ b : Fin 4, (∑ e : endsSet S, runParity S e.1 b • (w e).1) = 0)).card : ℝ) *
            ((2 : ℝ) ^ m) ^ 4 := by
      have hinner : ∀ w : Wset,
          (∑ v : Fin 4 → Fin m → F2,
            ∏ b : Fin 4, ∏ j : Fin m,
              chi (v b j * (∑ e : endsSet S, runParity S e.1 b * (w e).1 j))) =
            if (∀ b : Fin 4, (∑ e : endsSet S, runParity S e.1 b • (w e).1) = 0)
            then ((2 : ℝ) ^ m) ^ 4 else 0 := by
        intro w
        let u : Fin 4 × Fin m → F2 := fun p => ∑ e : endsSet S, runParity S e.1 p.1 * (w e).1 p.2
        have hsum_eq := sum_chi_vec_all u
        have hcard4m : (2 : ℝ) ^ Fintype.card (Fin 4 × Fin m) = ((2 : ℝ) ^ m) ^ 4 := by
          simp only [Fintype.card_prod, Fintype.card_fin]
          rw [mul_comm, pow_mul]
        rw [hcard4m] at hsum_eq
        have heq_lhs :
            (∑ v : Fin 4 → Fin m → F2,
              ∏ b : Fin 4, ∏ j : Fin m, chi (v b j * u (b, j))) =
              ∑ v : Fin 4 × Fin m → F2, ∏ p : Fin 4 × Fin m, chi (v p * u p) := by
          refine Fintype.sum_equiv (Equiv.curry (Fin 4) (Fin m) F2).symm _ _ ?_
          intro v
          rw [Fintype.prod_prod_type]
          rfl
        rw [heq_lhs, hsum_eq]
        have hu_iff : u = 0 ↔ ∀ b : Fin 4, (∑ e : endsSet S, runParity S e.1 b • (w e).1) = 0 := by
          constructor
          · intro h b; ext j
            have := congrFun h (b, j)
            simpa [u, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
          · intro h; ext ⟨b, j⟩
            have := congrFun (h b) j
            simpa [u, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
        by_cases hu : u = 0
        · rw [if_pos hu, if_pos (hu_iff.mp hu)]
        · rw [if_neg hu, if_neg (fun h => hu (hu_iff.mpr h))]
      simp_rw [hinner]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rw [← hstep1, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    have hfactor : ∀ w : Wset,
        (∏ b : Fin 4, ∏ j : Fin m, chi (v b j * (∑ e : endsSet S, runParity S e.1 b * (w e).1 j))) =
          ∏ e : endsSet S, ∏ j : Fin m,
            chi ((∑ b : Fin 4, runParity S e.1 b • v b) j * (w e).1 j) := by
      intro w
      simp_rw [prod_chi_sum]
      congr 1
      have hL :
          (∑ b : Fin 4, ∑ j : Fin m, v b j * ∑ e : endsSet S, runParity S e.1 b * (w e).1 j) =
            ∑ b : Fin 4, ∑ j : Fin m, ∑ e : endsSet S, v b j * (runParity S e.1 b * (w e).1 j) := by
        refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun j _ => Finset.mul_sum _ _ _))
      have hR :
          (∑ e : endsSet S, ∑ j : Fin m, (∑ b : Fin 4, runParity S e.1 b • v b) j * (w e).1 j) =
            ∑ e : endsSet S, ∑ j : Fin m, ∑ b : Fin 4, (runParity S e.1 b * v b j) * (w e).1 j := by
        refine Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun j _ => ?_))
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      rw [hL, hR]
      conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun b _ => by ring))
    simp_rw [hfactor]
    dsimp only [Wset]
    rw [← Fintype.prod_sum (fun (e : endsSet S) (u : {u : Fin m → F2 // u ∈ nzV}) =>
      ∏ j : Fin m, chi ((∑ b : Fin 4, runParity S e.1 b • v b) j * u.1 j))]
    rw [← Finset.prod_coe_sort (endsSet S)]
    refine Finset.prod_congr rfl (fun e _ => ?_)
    have hsum_sub :
        (∑ u : {u : Fin m → F2 // u ∈ nzV},
            ∏ j : Fin m, chi ((∑ b : Fin 4, runParity S e.1 b • v b) j * u.1 j)) =
          ∑ u ∈ nzV, ∏ j : Fin m, chi ((∑ b : Fin 4, runParity S e.1 b • v b) j * u j) := by
      rw [← Finset.sum_coe_sort nzV]
    rw [hsum_sub]
    exact sum_chi_nonzero m (∑ b : Fin 4, runParity S e.1 b • v b)
  rw [← hmain]
  field_simp [hpos]

noncomputable def inKer {n m : ℕ} [DecidableEq (Fin n)] (v : Fin 4 → Fin m → F2) (S : Finset (Fin n)) : ℕ :=
  ((endsSet S).filter (fun e => (∑ b : Fin 4, runParity S e b • v b) = 0)).card

lemma abs_fourier_term_eq (n m : ℕ) (hm : 1 ≤ m) (v : Fin 4 → Fin m → F2) (S : Finset (Fin n)) :
    |∏ e ∈ endsSet S,
        if (∑ b : Fin 4, runParity S e b • v b) = 0 then ((2 : ℝ) ^ m - 1) else (-1 : ℝ)| =
      ((2 : ℝ) ^ m - 1) ^ (inKer v S) := by
  have hq1 : (0 : ℝ) ≤ (2 : ℝ) ^ m - 1 := by
    have : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
    linarith
  rw [Finset.abs_prod]
  have hterm : ∀ e ∈ endsSet S,
      |if (∑ b : Fin 4, runParity S e b • v b) = 0 then ((2 : ℝ) ^ m - 1) else (-1 : ℝ)| =
        if (∑ b : Fin 4, runParity S e b • v b) = 0 then ((2 : ℝ) ^ m - 1) else 1 := by
    intro e _
    split_ifs
    · exact abs_of_nonneg hq1
    · norm_num
  rw [Finset.prod_congr rfl hterm]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  rfl

-- Section 3: 2x2 transfer matrices and elementary positive-vector bounds

def matA (q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; q - 1, 1]
def matT2 (q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![2, 2; 2 * (q - 1), q]
def matA2 (q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![q, 2; 2 * (q - 1), q]
def matM6 (q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := matT2 q * matT2 q * matA2 q

def matProd : ∀ (k : ℕ), (Fin k → Matrix (Fin 2) (Fin 2) ℝ) → Matrix (Fin 2) (Fin 2) ℝ
  | 0, _ => 1
  | k + 1, f => matProd k (fun j => f j.castSucc) * f (Fin.last k)

lemma matProd_const (M : Matrix (Fin 2) (Fin 2) ℝ) :
    ∀ k : ℕ, matProd k (fun _ => M) = M ^ k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [matProd, ih, pow_succ]

lemma matProd_period3 (M0 M1 M2 : Matrix (Fin 2) (Fin 2) ℝ) :
    ∀ (t : ℕ) (f : Fin (3 * t) → Matrix (Fin 2) (Fin 2) ℝ),
      (∀ j : Fin (3 * t), f j = if j.val % 3 = 0 then M0 else if j.val % 3 = 1 then M1 else M2) →
      matProd (3 * t) f = (M0 * M1 * M2) ^ t := by
  intro t
  induction t with
  | zero => intro _ _; rfl
  | succ t ih =>
    intro f hf
    have hstep : matProd (3 * (t + 1)) f =
        matProd (3 * t) (fun j => f ⟨j.val, by omega⟩) *
          f ⟨3 * t, by omega⟩ * f ⟨3 * t + 1, by omega⟩ * f ⟨3 * t + 2, by omega⟩ := by
      rfl
    rw [hstep]
    have hih := ih (fun j => f ⟨j.val, by omega⟩) (fun j => hf ⟨j.val, by omega⟩)
    rw [hih]
    have h0 : f ⟨3 * t, by omega⟩ = M0 := by
      rw [hf]; simp [Nat.mul_mod_right]
    have h1 : f ⟨3 * t + 1, by omega⟩ = M1 := by
      rw [hf]; have : (3 * t + 1) % 3 = 1 := by omega
      simp [this]
    have h2 : f ⟨3 * t + 2, by omega⟩ = M2 := by
      rw [hf]; have : (3 * t + 2) % 3 = 2 := by omega
      simp [this]
    rw [h0, h1, h2, pow_succ]
    simp only [Matrix.mul_assoc]

lemma matProd_apply_eq_sum :
    ∀ (k : ℕ) (f : Fin k → Matrix (Fin 2) (Fin 2) ℝ) (a b : Fin 2),
      matProd k f a b =
        ∑ x : Fin (k + 1) → Fin 2,
          if x 0 = a ∧ x (Fin.last k) = b then
            ∏ j : Fin k, f j (x j.castSucc) (x j.succ)
          else 0 := by
  intro k
  induction k with
  | zero =>
    intro f a b
    simp only [matProd, Finset.univ_eq_empty, Finset.prod_empty]
    have hsum : (∑ x : Fin 1 → Fin 2, if x 0 = a ∧ x (Fin.last 0) = b then (1 : ℝ) else 0) =
        if a = b then 1 else 0 := by
      let e : (Fin 1 → Fin 2) ≃ Fin 2 := Equiv.funUnique (Fin 1) (Fin 2)
      rw [Fintype.sum_equiv e _ (fun c : Fin 2 => if c = a ∧ c = b then (1 : ℝ) else 0)
        (fun x => by simp [e, Fin.last])]
      fin_cases a <;> fin_cases b <;> simp [Fin.sum_univ_two]
    rw [hsum]
    fin_cases a <;> fin_cases b <;> simp [Matrix.one_apply]
  | succ k ih =>
    intro f a b
    simp only [matProd, Matrix.mul_apply]
    have hih : ∀ c : Fin 2,
        matProd k (fun j => f j.castSucc) a c =
          ∑ y : Fin (k + 1) → Fin 2,
            if y 0 = a ∧ y (Fin.last k) = c then
              ∏ j : Fin k, f j.castSucc (y j.castSucc) (y j.succ)
            else 0 := fun c => ih (fun j => f j.castSucc) a c
    simp_rw [hih, Finset.sum_mul]
    rw [Finset.sum_comm]
    let e : (Fin (k + 2) → Fin 2) ≃ (Fin (k + 1) → Fin 2) × Fin 2 :=
      { toFun := fun x => (fun i => x i.castSucc, x (Fin.last (k + 1)))
        invFun := fun p => Fin.lastCases p.2 p.1
        left_inv := fun x => by
          ext i
          refine Fin.lastCases ?_ (fun r => ?_) i <;> simp
        right_inv := fun p => Prod.ext (by ext i; simp) (by simp) }
    symm
    rw [Fintype.sum_equiv e _
      (fun p : (Fin (k + 1) → Fin 2) × Fin 2 =>
        if p.1 0 = a ∧ p.2 = b then
          (∏ j : Fin k, f j.castSucc (p.1 j.castSucc) (p.1 j.succ)) * f (Fin.last k) (p.1 (Fin.last k)) p.2
        else 0)
      (fun x => by
        dsimp only [e, Equiv.coe_fn_mk]
        rw [Fin.prod_univ_castSucc]
        congr 1)]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    have hL : (∑ c : Fin 2,
        (if y 0 = a ∧ y (Fin.last k) = c then ∏ j : Fin k, f j.castSucc (y j.castSucc) (y j.succ) else 0) *
          f (Fin.last k) c b) =
        if y 0 = a then
          (∏ j : Fin k, f j.castSucc (y j.castSucc) (y j.succ)) * f (Fin.last k) (y (Fin.last k)) b
        else 0 := by
      have hc : (∑ c : Fin 2,
          if c = y (Fin.last k) then
            (if y 0 = a then ∏ j : Fin k, f j.castSucc (y j.castSucc) (y j.succ) else 0) * f (Fin.last k) c b
          else 0) =
          (if y 0 = a then ∏ j : Fin k, f j.castSucc (y j.castSucc) (y j.succ) else 0) *
            f (Fin.last k) (y (Fin.last k)) b := by
        simp [Finset.sum_ite_eq']
      have heq : ∀ c : Fin 2,
          (if y 0 = a ∧ y (Fin.last k) = c then ∏ j : Fin k, f j.castSucc (y j.castSucc) (y j.succ) else 0) *
            f (Fin.last k) c b =
          if c = y (Fin.last k) then
            (if y 0 = a then ∏ j : Fin k, f j.castSucc (y j.castSucc) (y j.succ) else 0) * f (Fin.last k) c b
          else 0 := by
        intro c
        by_cases h1 : y 0 = a <;> by_cases h2 : y (Fin.last k) = c
        · subst h2; simp [h1]
        · have h2' : c ≠ y (Fin.last k) := Ne.symm h2; simp [h1, h2, h2']
        · simp [h1, h2]
        · have h2' : c ≠ y (Fin.last k) := Ne.symm h2; simp [h1, h2, h2']
      simp_rw [heq]
      rw [hc]
      split_ifs <;> ring
    have hR : (∑ z : Fin 2,
        if y 0 = a ∧ z = b then
          (∏ j : Fin k, f j.castSucc (y j.castSucc) (y j.succ)) * f (Fin.last k) (y (Fin.last k)) z
        else 0) =
        if y 0 = a then
          (∏ j : Fin k, f j.castSucc (y j.castSucc) (y j.succ)) * f (Fin.last k) (y (Fin.last k)) b
        else 0 := by
      by_cases hy : y 0 = a
      · simp [hy, Finset.sum_ite_eq']
      · simp [hy]
    rw [hL, hR]

lemma matProd_trace_eq_sum (L : ℕ) (hL : 1 ≤ L) (f : Fin L → Matrix (Fin 2) (Fin 2) ℝ) :
    (matProd L f).trace = ∑ x : Fin L → Fin 2, ∏ j : Fin L, f j (x j) (x (nextIdx j)) := by
  simp only [Matrix.trace, Matrix.diag_apply, matProd_apply_eq_sum]
  rw [Finset.sum_comm]
  have hcollapse : ∀ y : Fin (L + 1) → Fin 2,
      (∑ a : Fin 2, if y 0 = a ∧ y (Fin.last L) = a then ∏ j : Fin L, f j (y j.castSucc) (y j.succ) else 0) =
        if y 0 = y (Fin.last L) then ∏ j : Fin L, f j (y j.castSucc) (y j.succ) else 0 := by
    intro y
    by_cases h : y 0 = y (Fin.last L)
    · rw [if_pos h]
      have h1 : ∀ a : Fin 2, (y 0 = a ∧ y (Fin.last L) = a) ↔ a = y 0 := by
        intro a; rw [← h]; constructor <;> intro ha
        · exact ha.1.symm
        · exact ⟨ha.symm, ha.symm⟩
      simp_rw [h1]
      simp [Finset.sum_ite_eq']
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro a _
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact h (h1.trans h2.symm)
  simp_rw [hcollapse]
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun y _ => fun j : Fin L => y j.castSucc) ?_ ?_ ?_ ?_
  · intro _ _; exact Finset.mem_univ _
  · intro y₁ hy₁ y₂ hy₂ heq
    have h1 := (Finset.mem_filter.mp hy₁).2
    have h2 := (Finset.mem_filter.mp hy₂).2
    funext i
    refine Fin.lastCases (motive := fun idx => y₁ idx = y₂ idx) ?_ (fun j => congrFun heq j) i
    rw [← h1, ← h2]
    have h0 : (0 : Fin (L + 1)) = (⟨0, by omega⟩ : Fin L).castSucc := by ext; simp
    rw [h0]
    exact congrFun heq ⟨0, by omega⟩
  · intro x _
    let y : Fin (L + 1) → Fin 2 := Fin.lastCases (motive := fun _ => Fin 2) (x ⟨0, by omega⟩) x
    refine ⟨y, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have h0 : (0 : Fin (L + 1)) = (⟨0, by omega⟩ : Fin L).castSucc := by ext; simp
      rw [h0]
      dsimp only [y]
      rw [Fin.lastCases_castSucc, Fin.lastCases_last]
    · funext j; simp [y]
  · intro y hy
    have hclose := (Finset.mem_filter.mp hy).2
    refine Finset.prod_congr rfl (fun j _ => ?_)
    have harg : y j.succ = y (nextIdx j).castSucc := by
      by_cases hlast : j.val + 1 = L
      · have hj : j.succ = Fin.last L := by ext; simp [hlast]
        have hn : (nextIdx j).castSucc = (0 : Fin (L + 1)) := by
          ext; simp [nextIdx, hlast, Nat.mod_self]
        rw [hj, hn, ← hclose]
      · have hlt : j.val + 1 < L := by omega
        have hn : (nextIdx j).castSucc = j.succ := by
          ext; simp [nextIdx, Nat.mod_eq_of_lt hlt]
        rw [hn]
    rw [harg]

lemma sum_runs_eq_trace_A (n : ℕ) (hn : 1 ≤ n) (q : ℝ) :
    (∑ S : Finset (Fin n), (q - 1) ^ (runsCard S)) = (matA q ^ n).trace := by
  rw [← matProd_const (matA q) n, matProd_trace_eq_sum n hn]
  let e : Finset (Fin n) ≃ (Fin n → Fin 2) :=
    { toFun := fun S i => if i ∈ S then 1 else 0
      invFun := fun x => Finset.univ.filter (fun i => x i = 1)
      left_inv := fun S => by ext i; by_cases hi : i ∈ S <;> simp [hi]
      right_inv := fun x => by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases fin2_cases (x i) with h | h <;> simp [h] }
  refine Fintype.sum_equiv e _ _ ?_
  intro S
  have hterm : ∀ i : Fin n,
      matA q (e S i) (e S (nextIdx i)) = if i ∈ endsSet S then (q - 1) else 1 := by
    intro i
    simp only [e, endsSet, Finset.mem_filter]
    by_cases h1 : i ∈ S <;> by_cases h2 : nextIdx i ∈ S <;> simp [h1, h2, matA]
  simp_rw [hterm]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  have hf : Finset.univ.filter (fun i : Fin n => i ∈ endsSet S) = endsSet S := by
    ext i; simp
  rw [hf, runsCard]

lemma matA_pow_formula (q : ℝ) (hq : 1 < q) :
    ∀ k : ℕ,
      let r := Real.sqrt (q - 1)
      (matA q ^ k) 0 0 = ((1 + r) ^ k + (1 - r) ^ k) / 2 ∧
      (matA q ^ k) 0 1 = ((1 + r) ^ k - (1 - r) ^ k) / (2 * r) ∧
      (matA q ^ k) 1 0 = r * ((1 + r) ^ k - (1 - r) ^ k) / 2 ∧
      (matA q ^ k) 1 1 = ((1 + r) ^ k + (1 - r) ^ k) / 2 := by
  intro k
  let r := Real.sqrt (q - 1)
  have hrpos : 0 < r := Real.sqrt_pos.mpr (by linarith)
  have hr2 : r ^ 2 = q - 1 := Real.sq_sqrt (by linarith)
  have hA00 : matA q 0 0 = 1 := rfl
  have hA01 : matA q 0 1 = 1 := rfl
  have hA10 : matA q 1 0 = q - 1 := rfl
  have hA11 : matA q 1 1 = 1 := rfl
  induction k with
  | zero =>
    simp [Matrix.one_apply]
  | succ k ih =>
    rcases ih with ⟨h00, h01, h10, h11⟩
    rw [pow_succ]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, h00, h01, hA00, hA10, pow_succ]
      have hne : r ≠ 0 := ne_of_gt hrpos
      rw [show Real.sqrt (q - 1) = r from rfl, show q - 1 = r ^ 2 from hr2.symm]
      field_simp [hne]; ring
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, h00, h01, hA01, hA11, pow_succ]
      have hne : r ≠ 0 := ne_of_gt hrpos
      rw [show Real.sqrt (q - 1) = r from rfl]
      field_simp [hne]; ring
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, h10, h11, hA00, hA10, pow_succ]
      rw [show Real.sqrt (q - 1) = r from rfl, show q - 1 = r ^ 2 from hr2.symm]; ring
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, h10, h11, hA01, hA11, pow_succ]
      rw [show Real.sqrt (q - 1) = r from rfl]; ring

lemma trace_matA_pow_eq (q : ℝ) (hq : 1 < q) (k : ℕ) :
    (matA q ^ k).trace = (1 + Real.sqrt (q - 1)) ^ k + (1 - Real.sqrt (q - 1)) ^ k := by
  have hf := matA_pow_formula q hq k
  simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two, hf.1, hf.2.2.2]
  ring

lemma trace_matA_pow_ge_even (q : ℝ) (hq : 1 < q) (a : ℕ) :
    (1 + Real.sqrt (q - 1)) ^ (2 * a) ≤ (matA q ^ (2 * a)).trace := by
  rw [trace_matA_pow_eq q hq (2 * a)]
  have hnn : 0 ≤ (1 - Real.sqrt (q - 1)) ^ (2 * a) := by
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg _) a
  linarith

lemma trace_matA_pow_le_even (q : ℝ) (hq : 1 < q) (a : ℕ) :
    (matA q ^ (2 * a)).trace ≤ 2 * (1 + Real.sqrt (q - 1)) ^ (2 * a) := by
  rw [trace_matA_pow_eq q hq (2 * a)]
  have hr : 0 ≤ Real.sqrt (q - 1) := Real.sqrt_nonneg _
  have habs : |1 - Real.sqrt (q - 1)| ≤ 1 + Real.sqrt (q - 1) := by
    rw [abs_le]; constructor <;> linarith
  have hpow : (1 - Real.sqrt (q - 1)) ^ (2 * a) ≤ (1 + Real.sqrt (q - 1)) ^ (2 * a) := by
    calc (1 - Real.sqrt (q - 1)) ^ (2 * a)
        ≤ |1 - Real.sqrt (q - 1)| ^ (2 * a) := by
          rw [← abs_pow]; exact le_abs_self _
      _ ≤ (1 + Real.sqrt (q - 1)) ^ (2 * a) :=
          pow_le_pow_left₀ (abs_nonneg _) habs (2 * a)
  linarith

lemma mat_pow_nonneg (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : ∀ i j, 0 ≤ M i j) :
    ∀ k i j, 0 ≤ (M ^ k) i j := by
  intro k
  induction k with
  | zero =>
    intro i j; fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]
  | succ k ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg (fun c _ => mul_nonneg (ih i c) (hM c j))

lemma matT2_nonneg (q : ℝ) (hq : 1 ≤ q) : ∀ i j, 0 ≤ matT2 q i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [matT2] <;> linarith

lemma matA2_nonneg (q : ℝ) (hq : 1 ≤ q) : ∀ i j, 0 ≤ matA2 q i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [matA2] <;> linarith

lemma matM6_nonneg (q : ℝ) (hq : 1 ≤ q) : ∀ i j, 0 ≤ matM6 q i j := by
  intro i j
  have hT := matT2_nonneg q hq
  have hA := matA2_nonneg q hq
  have hTT : ∀ r c, 0 ≤ (matT2 q * matT2 q) r c := fun r c => by
    rw [Matrix.mul_apply]
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (hT r k) (hT k c))
  dsimp only [matM6]
  rw [Matrix.mul_apply]
  exact Finset.sum_nonneg (fun k _ => mul_nonneg (hTT i k) (hA k j))

lemma matT2_right_vec_le (q : ℝ) (hq : 1 ≤ q) :
    ∀ k : ℕ,
      (matT2 q ^ k) 0 0 * 2 + (matT2 q ^ k) 0 1 * q ≤ (q + 4) ^ k * 2 ∧
      (matT2 q ^ k) 1 0 * 2 + (matT2 q ^ k) 1 1 * q ≤ (q + 4) ^ k * q := by
  intro k
  induction k with
  | zero => simp [Matrix.one_apply]
  | succ k ih =>
    rcases ih with ⟨h0, h1⟩
    rw [pow_succ']
    have hnn := mat_pow_nonneg (matT2 q) (matT2_nonneg q hq) k
    have hstep0 : (matT2 q * matT2 q ^ k) 0 0 * 2 + (matT2 q * matT2 q ^ k) 0 1 * q =
        2 * ((matT2 q ^ k) 0 0 * 2 + (matT2 q ^ k) 0 1 * q) +
        2 * ((matT2 q ^ k) 1 0 * 2 + (matT2 q ^ k) 1 1 * q) := by
      simp [Matrix.mul_apply, Fin.sum_univ_two, matT2]; ring
    have hstep1 : (matT2 q * matT2 q ^ k) 1 0 * 2 + (matT2 q * matT2 q ^ k) 1 1 * q =
        2 * (q - 1) * ((matT2 q ^ k) 0 0 * 2 + (matT2 q ^ k) 0 1 * q) +
        q * ((matT2 q ^ k) 1 0 * 2 + (matT2 q ^ k) 1 1 * q) := by
      simp [Matrix.mul_apply, Fin.sum_univ_two, matT2]; ring
    have hpow : 0 ≤ (q + 4) ^ k := by positivity
    rw [hstep0, hstep1, pow_succ']
    constructor <;> nlinarith

lemma matT2_left_vec_le (q : ℝ) (hq : 1 ≤ q) :
    ∀ k : ℕ,
      2 * (matT2 q ^ k) 0 0 + 1 * (matT2 q ^ k) 1 0 ≤ (q + 4) ^ k * 2 ∧
      2 * (matT2 q ^ k) 0 1 + 1 * (matT2 q ^ k) 1 1 ≤ (q + 4) ^ k * 1 := by
  intro k
  induction k with
  | zero => simp [Matrix.one_apply]
  | succ k ih =>
    rcases ih with ⟨h0, h1⟩
    rw [pow_succ]
    have hstep0 : 2 * (matT2 q ^ k * matT2 q) 0 0 + 1 * (matT2 q ^ k * matT2 q) 1 0 =
        (2 * (matT2 q ^ k) 0 0 + 1 * (matT2 q ^ k) 1 0) * 2 +
        (2 * (matT2 q ^ k) 0 1 + 1 * (matT2 q ^ k) 1 1) * (2 * (q - 1)) := by
      simp [Matrix.mul_apply, Fin.sum_univ_two, matT2]; ring
    have hstep1 : 2 * (matT2 q ^ k * matT2 q) 0 1 + 1 * (matT2 q ^ k * matT2 q) 1 1 =
        (2 * (matT2 q ^ k) 0 0 + 1 * (matT2 q ^ k) 1 0) * 2 +
        (2 * (matT2 q ^ k) 0 1 + 1 * (matT2 q ^ k) 1 1) * q := by
      simp [Matrix.mul_apply, Fin.sum_univ_two, matT2]; ring
    have hpow : 0 ≤ (q + 4) ^ k := by positivity
    rw [hstep0, hstep1, pow_succ]
    constructor <;> nlinarith

lemma trace_matT2_pow_le (q : ℝ) (hq : 1 ≤ q) (a : ℕ) (ha : 1 ≤ a) :
    (matT2 q ^ a).trace ≤ (q + 4) ^ a + 4 * (q + 4) ^ (a - 1) := by
  have hnn := mat_pow_nonneg (matT2 q) (matT2_nonneg q hq)
  have h11 : (matT2 q ^ a) 1 1 ≤ (q + 4) ^ a := by
    have hr := (matT2_right_vec_le q hq a).2
    have hnn10 : 0 ≤ (matT2 q ^ a) 1 0 * 2 := mul_nonneg (hnn a 1 0) (by norm_num)
    nlinarith
  have h00 : (matT2 q ^ a) 0 0 ≤ 4 * (q + 4) ^ (a - 1) := by
    have ha1 : a = (a - 1) + 1 := by omega
    conv_lhs => rw [ha1, pow_succ']
    have hmul : (matT2 q * matT2 q ^ (a - 1)) 0 0 =
        2 * (matT2 q ^ (a - 1)) 0 0 + 2 * (matT2 q ^ (a - 1)) 1 0 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two, matT2]
    rw [hmul]
    have hl := (matT2_left_vec_le q hq (a - 1)).1
    have hnn00 : 0 ≤ (matT2 q ^ (a - 1)) 0 0 := hnn (a - 1) 0 0
    have hnn10 : 0 ≤ (matT2 q ^ (a - 1)) 1 0 := hnn (a - 1) 1 0
    linarith
  simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two]
  linarith

lemma matM6_right_vec_le (q : ℝ) (hq : 1 ≤ q) :
    ∀ t : ℕ,
      (matM6 q ^ t) 0 0 * 2 + (matM6 q ^ t) 0 1 * q ≤ ((q + 6) ^ 3) ^ t * 2 ∧
      (matM6 q ^ t) 1 0 * 2 + (matM6 q ^ t) 1 1 * q ≤ ((q + 6) ^ 3) ^ t * q := by
  intro t
  have h1step :
      (matM6 q) 0 0 * 2 + (matM6 q) 0 1 * q ≤ (q + 6) ^ 3 * 2 ∧
      (matM6 q) 1 0 * 2 + (matM6 q) 1 1 * q ≤ (q + 6) ^ 3 * q := by
    have h0 : (matM6 q) 0 0 * 2 + (matM6 q) 0 1 * q =
        2 * q ^ 3 + 28 * q ^ 2 + 8 * q - 16 := by
      simp [matM6, matT2, matA2, Matrix.mul_apply, Fin.sum_univ_two]; ring
    have h1 : (matM6 q) 1 0 * 2 + (matM6 q) 1 1 * q =
        q ^ 4 + 16 * q ^ 3 + 16 * q ^ 2 - 48 * q + 16 := by
      simp [matM6, matT2, matA2, Matrix.mul_apply, Fin.sum_univ_two]; ring
    rw [h0, h1]
    constructor <;> nlinarith [sq_nonneg q, sq_nonneg (q - 1)]
  induction t with
  | zero => simp [Matrix.one_apply]
  | succ t ih =>
    rcases ih with ⟨h0, h1⟩
    rw [pow_succ']
    have hnnM := matM6_nonneg q hq
    have hstep0 : (matM6 q * matM6 q ^ t) 0 0 * 2 + (matM6 q * matM6 q ^ t) 0 1 * q =
        (matM6 q) 0 0 * ((matM6 q ^ t) 0 0 * 2 + (matM6 q ^ t) 0 1 * q) +
        (matM6 q) 0 1 * ((matM6 q ^ t) 1 0 * 2 + (matM6 q ^ t) 1 1 * q) := by
      simp [Matrix.mul_apply, Fin.sum_univ_two]; ring
    have hstep1 : (matM6 q * matM6 q ^ t) 1 0 * 2 + (matM6 q * matM6 q ^ t) 1 1 * q =
        (matM6 q) 1 0 * ((matM6 q ^ t) 0 0 * 2 + (matM6 q ^ t) 0 1 * q) +
        (matM6 q) 1 1 * ((matM6 q ^ t) 1 0 * 2 + (matM6 q ^ t) 1 1 * q) := by
      simp [Matrix.mul_apply, Fin.sum_univ_two]; ring
    have hpow : 0 ≤ ((q + 6) ^ 3) ^ t := by positivity
    rw [hstep0, hstep1, pow_succ']
    constructor
    · calc (matM6 q) 0 0 * ((matM6 q ^ t) 0 0 * 2 + (matM6 q ^ t) 0 1 * q) +
           (matM6 q) 0 1 * ((matM6 q ^ t) 1 0 * 2 + (matM6 q ^ t) 1 1 * q)
          ≤ (matM6 q) 0 0 * (((q + 6) ^ 3) ^ t * 2) + (matM6 q) 0 1 * (((q + 6) ^ 3) ^ t * q) := by
            exact add_le_add (mul_le_mul_of_nonneg_left h0 (hnnM 0 0)) (mul_le_mul_of_nonneg_left h1 (hnnM 0 1))
        _ = ((matM6 q) 0 0 * 2 + (matM6 q) 0 1 * q) * ((q + 6) ^ 3) ^ t := by ring
        _ ≤ ((q + 6) ^ 3 * 2) * ((q + 6) ^ 3) ^ t := mul_le_mul_of_nonneg_right h1step.1 hpow
        _ = (q + 6) ^ 3 * ((q + 6) ^ 3) ^ t * 2 := by ring
    · calc (matM6 q) 1 0 * ((matM6 q ^ t) 0 0 * 2 + (matM6 q ^ t) 0 1 * q) +
           (matM6 q) 1 1 * ((matM6 q ^ t) 1 0 * 2 + (matM6 q ^ t) 1 1 * q)
          ≤ (matM6 q) 1 0 * (((q + 6) ^ 3) ^ t * 2) + (matM6 q) 1 1 * (((q + 6) ^ 3) ^ t * q) := by
            exact add_le_add (mul_le_mul_of_nonneg_left h0 (hnnM 1 0)) (mul_le_mul_of_nonneg_left h1 (hnnM 1 1))
        _ = ((matM6 q) 1 0 * 2 + (matM6 q) 1 1 * q) * ((q + 6) ^ 3) ^ t := by ring
        _ ≤ ((q + 6) ^ 3 * q) * ((q + 6) ^ 3) ^ t := mul_le_mul_of_nonneg_right h1step.2 hpow
        _ = (q + 6) ^ 3 * ((q + 6) ^ 3) ^ t * q := by ring

lemma trace_matM6_pow_le (q : ℝ) (hq : 1 ≤ q) (t : ℕ) :
    (matM6 q ^ t).trace ≤ 2 * (q + 6) ^ (3 * t) := by
  have hnn := mat_pow_nonneg (matM6 q) (matM6_nonneg q hq) t
  obtain ⟨h0, h1⟩ := matM6_right_vec_le q hq t
  rw [← pow_mul] at h0 h1
  have h00 : (matM6 q ^ t) 0 0 ≤ (q + 6) ^ (3 * t) := by
    have hnn01 : 0 ≤ (matM6 q ^ t) 0 1 * q := mul_nonneg (hnn 0 1) (by linarith)
    nlinarith
  have h11 : (matM6 q ^ t) 1 1 ≤ (q + 6) ^ (3 * t) := by
    have hnn10 : 0 ≤ (matM6 q ^ t) 1 0 * 2 := mul_nonneg (hnn 1 0) (by norm_num)
    nlinarith
  simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two]
  linarith

lemma mul_pow_shift (X Y : Matrix (Fin 2) (Fin 2) ℝ) :
    ∀ k : ℕ, (X * Y) ^ k * X = X * (Y * X) ^ k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    calc (X * Y) ^ (k + 1) * X
        = (X * Y) ^ k * (X * Y) * X := by rw [pow_succ]
      _ = ((X * Y) ^ k * X) * (Y * X) := by simp only [Matrix.mul_assoc]
      _ = X * (Y * X) ^ k * (Y * X) := by rw [ih]
      _ = X * (Y * X) ^ (k + 1) := by rw [pow_succ, Matrix.mul_assoc]

lemma trace_pow_mul_comm (X Y : Matrix (Fin 2) (Fin 2) ℝ) (k : ℕ) :
    ((X * Y) ^ k).trace = ((Y * X) ^ k).trace := by
  cases k with
  | zero => rfl
  | succ k =>
    calc ((X * Y) ^ (k + 1)).trace
        = (((X * Y) ^ k * X) * Y).trace := by rw [pow_succ, Matrix.mul_assoc]
      _ = (Y * ((X * Y) ^ k * X)).trace := Matrix.trace_mul_comm _ _
      _ = (Y * (X * (Y * X) ^ k)).trace := by rw [mul_pow_shift]
      _ = ((Y * X) * (Y * X) ^ k).trace := by rw [← Matrix.mul_assoc]
      _ = ((Y * X) ^ (k + 1)).trace := by rw [← pow_succ']

-- Section 4: Pair-transfer upper bound for Buckets E and O, and pigeonhole bound for Bucket R

def idxShift (t : ℕ) (ht : 1 ≤ t) (shift : Fin 2) (k : ℕ) : Fin (6 * t) :=
  ⟨(k + shift.val) % (6 * t), Nat.mod_lt _ (by omega)⟩

def pairW (q : ℝ) (isMiss : Bool) (x y z : Fin 2) : ℝ :=
  if x = 1 ∧ y = 0 then q - 1
  else if y = 1 ∧ z = 0 ∧ (x = 1 ∨ !isMiss) then q - 1
  else 1

lemma sum_pairW_eq_mat (q : ℝ) (isMiss : Bool) (x z : Fin 2) :
    (∑ y : Fin 2, pairW q isMiss x y z) =
      if isMiss then matT2 q x z else matA2 q x z := by
  cases isMiss <;> fin_cases x <;> fin_cases z <;>
    simp [Fin.sum_univ_two, pairW, matT2, matA2] <;> ring

lemma sum_inKer_pair_bound (t m : ℕ) (ht : 1 ≤ t) (hm : 1 ≤ m)
    (v : Fin 4 → Fin m → F2) (shift : Fin 2) (miss : Fin (3 * t) → Bool)
    (hmiss : ∀ j : Fin (3 * t), miss j = true →
      (∑ b : Fin 4, hMat (idxShift t ht shift (2 * j.val + 1)) b • v b) ≠ 0) :
    let q : ℝ := (2 : ℝ) ^ m
    let M : Fin (3 * t) → Matrix (Fin 2) (Fin 2) ℝ :=
      fun j => if miss j then matT2 q else matA2 q
    (∑ S ∈ (Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))),
        (q - 1) ^ (inKer v S)) ≤ (matProd (3 * t) M).trace ∧
    (∑ S ∈ ((Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))).erase (laneSet shift)),
        (q - 1) ^ (inKer v S)) ≤ (matProd (3 * t) M).trace - (q - 1) ^ (3 * t) := by
  intro q M
  have hq2 : (2 : ℝ) ≤ q := by
    have : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ m := pow_le_pow_right₀ (by norm_num) hm
    simpa [q] using this
  have hq1_ge1 : (1 : ℝ) ≤ q - 1 := by linarith
  let W : Finset (Fin (6 * t)) → ℝ := fun S =>
    ∏ j : Fin (3 * t),
      pairW q (miss j)
        (if idxShift t ht shift (2 * j.val) ∈ S then 1 else 0)
        (if idxShift t ht shift (2 * j.val + 1) ∈ S then 1 else 0)
        (if idxShift t ht shift (2 * j.val + 2) ∈ S then 1 else 0)
  have hW_nonneg : ∀ S, 0 ≤ W S := by
    intro S
    refine Finset.prod_nonneg (fun j _ => ?_)
    dsimp only [pairW]
    split_ifs <;> linarith
  have hW_sum : (∑ S : Finset (Fin (6 * t)), W S) = (matProd (3 * t) M).trace := by
    rw [matProd_trace_eq_sum (3 * t) (by omega) M]
    let eS : Finset (Fin (6 * t)) ≃ (Fin (3 * t) → Fin 2) × (Fin (3 * t) → Fin 2) :=
      { toFun := fun S =>
          (fun j => if idxShift t ht shift (2 * j.val) ∈ S then 1 else 0,
           fun j => if idxShift t ht shift (2 * j.val + 1) ∈ S then 1 else 0)
        invFun := fun p => Finset.univ.filter (fun i : Fin (6 * t) =>
          let u := (i.val + 6 * t - shift.val) % (6 * t)
          have hu_lt : u < 6 * t := Nat.mod_lt _ (by omega)
          if u % 2 = 0 then p.1 ⟨u / 2, by omega⟩ = 1 else p.2 ⟨u / 2, by omega⟩ = 1)
        left_inv := fun S => by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          set u := (i.val + 6 * t - shift.val) % (6 * t)
          have hu_lt : u < 6 * t := Nat.mod_lt _ (by omega)
          have hu_add : (u + shift.val) % (6 * t) = i.val := by
            dsimp only [u]
            rw [Nat.mod_add_mod]
            have h1 : i.val + 6 * t - shift.val + shift.val = i.val + 6 * t := by omega
            rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
          by_cases hpar : u % 2 = 0
          · rw [if_pos hpar]
            have hidx : idxShift t ht shift (2 * (u / 2)) = i := by
              ext; simp only [idxShift]
              have h2 : 2 * (u / 2) = u := by omega
              rw [h2]; exact hu_add
            rw [hidx]
            by_cases hi : i ∈ S <;> simp [hi]
          · rw [if_neg hpar]
            have hidx : idxShift t ht shift (2 * (u / 2) + 1) = i := by
              ext; simp only [idxShift]
              have h2 : 2 * (u / 2) + 1 = u := by omega
              rw [h2]; exact hu_add
            rw [hidx]
            by_cases hi : i ∈ S <;> simp [hi]
        right_inv := fun p => by
          ext j
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and, idxShift]
            have hu : ((2 * j.val + shift.val) % (6 * t) + 6 * t - shift.val) % (6 * t) = 2 * j.val := by
              have hlt : 2 * j.val + shift.val < 6 * t ∨ (2 * j.val + shift.val = 6 * t) := by omega
              rcases hlt with hlt | heq
              · rw [Nat.mod_eq_of_lt hlt]
                have h1 : 2 * j.val + shift.val + 6 * t - shift.val = 2 * j.val + 6 * t := by omega
                rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
              · rw [heq, Nat.mod_self]
                have h1 : 0 + 6 * t - shift.val = 2 * j.val := by omega
                rw [h1, Nat.mod_eq_of_lt (by omega)]
            simp only [hu, Nat.mul_mod_right, ↓reduceIte, Nat.mul_div_right _ (by omega : 0 < 2)]
            rcases fin2_cases (p.1 j) with h | h <;> simp [h]
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and, idxShift]
            have hu : ((2 * j.val + 1 + shift.val) % (6 * t) + 6 * t - shift.val) % (6 * t) = 2 * j.val + 1 := by
              have hlt : 2 * j.val + 1 + shift.val < 6 * t ∨ 2 * j.val + 1 + shift.val = 6 * t := by omega
              rcases hlt with hlt | heq
              · rw [Nat.mod_eq_of_lt hlt]
                have h1 : 2 * j.val + 1 + shift.val + 6 * t - shift.val = 2 * j.val + 1 + 6 * t := by omega
                rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
              · rw [heq, Nat.mod_self]
                have h1 : 0 + 6 * t - shift.val = 2 * j.val + 1 := by omega
                rw [h1, Nat.mod_eq_of_lt (by omega)]
            have hodd : (2 * j.val + 1) % 2 ≠ 0 := by omega
            have hdiv : (2 * j.val + 1) / 2 = j.val := by omega
            simp only [hu, hodd, ↓reduceIte, hdiv]
            rcases fin2_cases (p.2 j) with h | h <;> simp [h] }
    rw [Fintype.sum_equiv eS W
      (fun p => ∏ j : Fin (3 * t), pairW q (miss j) (p.1 j) (p.2 j) (p.1 (nextIdx j)))
      (fun S => by
        refine Finset.prod_congr rfl (fun j _ => ?_)
        dsimp only [eS, Equiv.coe_fn_mk]
        have hnxt : idxShift t ht shift (2 * (nextIdx j).val) = idxShift t ht shift (2 * j.val + 2) := by
          ext
          simp only [idxShift, nextIdx]
          by_cases hlast : j.val + 1 = 3 * t
          · rw [hlast, Nat.mod_self, Nat.mul_zero, Nat.zero_add]
            have h6 : 2 * j.val + 2 = 6 * t := by omega
            rw [h6, Nat.add_mod_left]
          · rw [Nat.mod_eq_of_lt (by omega : j.val + 1 < 3 * t)]
            have hmul2 : 2 * (j.val + 1) = 2 * j.val + 2 := by omega
            rw [hmul2]
        rw [hnxt])]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    dsimp only
    rw [← Fintype.prod_sum (fun j y => pairW q (miss j) (x j) y (x (nextIdx j)))]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [sum_pairW_eq_mat]; dsimp only [M]; split_ifs <;> rfl
  have hW_ge : ∀ S : Finset (Fin (6 * t)), S ≠ Finset.univ →
      (q - 1) ^ (inKer v S) ≤ W S := by
    intro S hne
    let Kset := (endsSet S).filter (fun e => (∑ b : Fin 4, runParity S e b • v b) = 0)
    have hKcard : inKer v S = Kset.card := rfl
    rw [hKcard]
    let f : Fin (3 * t) → ℕ := fun j =>
      (if idxShift t ht shift (2 * j.val) ∈ Kset then 1 else 0) +
      (if idxShift t ht shift (2 * j.val + 1) ∈ Kset then 1 else 0)
    have hsum_f : Kset.card = ∑ j : Fin (3 * t), f j := by
      have h1 : Kset.card = ∑ i : Fin (6 * t), if i ∈ Kset then 1 else 0 := by
        simp
      rw [h1]
      let eIdx : Fin (3 * t) × Fin 2 ≃ Fin (6 * t) :=
        { toFun := fun p => idxShift t ht shift (2 * p.1.val + p.2.val)
          invFun := fun i =>
            (⟨((i.val + 6 * t - shift.val) % (6 * t)) / 2,
              by have := Nat.mod_lt (i.val + 6 * t - shift.val) (by omega : 0 < 6 * t); omega⟩,
             ⟨((i.val + 6 * t - shift.val) % (6 * t)) % 2, Nat.mod_lt _ (by omega)⟩)
          left_inv := fun ⟨j, r⟩ => by
            ext
            · simp only [idxShift]
              have hu : ((2 * j.val + r.val + shift.val) % (6 * t) + 6 * t - shift.val) % (6 * t) =
                  2 * j.val + r.val := by
                have hle : 2 * j.val + r.val + shift.val ≤ 6 * t := by omega
                rcases lt_or_eq_of_le hle with hlt | heq
                · rw [Nat.mod_eq_of_lt hlt]
                  have h1' : 2 * j.val + r.val + shift.val + 6 * t - shift.val = 2 * j.val + r.val + 6 * t := by omega
                  rw [h1', Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
                · rw [heq, Nat.mod_self]
                  have h1' : 0 + 6 * t - shift.val = 2 * j.val + r.val := by omega
                  rw [h1', Nat.mod_eq_of_lt (by omega)]
              simp only [hu]; omega
            · simp only [idxShift]
              have hu : ((2 * j.val + r.val + shift.val) % (6 * t) + 6 * t - shift.val) % (6 * t) =
                  2 * j.val + r.val := by
                have hle : 2 * j.val + r.val + shift.val ≤ 6 * t := by omega
                rcases lt_or_eq_of_le hle with hlt | heq
                · rw [Nat.mod_eq_of_lt hlt]
                  have h1' : 2 * j.val + r.val + shift.val + 6 * t - shift.val = 2 * j.val + r.val + 6 * t := by omega
                  rw [h1', Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
                · rw [heq, Nat.mod_self]
                  have h1' : 0 + 6 * t - shift.val = 2 * j.val + r.val := by omega
                  rw [h1', Nat.mod_eq_of_lt (by omega)]
              simp only [hu]; omega
          right_inv := fun i => by
            ext
            simp only [idxShift]
            set u := (i.val + 6 * t - shift.val) % (6 * t)
            have h2 : 2 * (u / 2) + u % 2 = u := by omega
            rw [h2]
            dsimp only [u]
            rw [Nat.mod_add_mod]
            have h1' : i.val + 6 * t - shift.val + shift.val = i.val + 6 * t := by omega
            rw [h1', Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt] }
      rw [← Equiv.sum_comp eIdx, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [Fin.sum_univ_two, f, eIdx, Equiv.coe_fn_mk, Fin.val_zero, Fin.val_one, add_zero]
    rw [hsum_f, ← Finset.prod_pow_eq_pow_sum]
    have hprod_le : ∀ {ι : Type} (s : Finset ι) (a b : ι → ℝ),
        (∀ i ∈ s, 0 ≤ a i) → (∀ i ∈ s, a i ≤ b i) → (∏ i ∈ s, a i) ≤ ∏ i ∈ s, b i := by
      intro ι s a b ha hab
      induction s using Finset.induction_on with
      | empty => simp
      | insert x s hx ih =>
        rw [Finset.prod_insert hx, Finset.prod_insert hx]
        have ha_s : ∀ i ∈ s, 0 ≤ a i := fun i hi => ha i (Finset.mem_insert_of_mem hi)
        have hprod_nn : 0 ≤ ∏ i ∈ s, a i := Finset.prod_nonneg ha_s
        have hxb : 0 ≤ b x := le_trans (ha x (Finset.mem_insert_self x s)) (hab x (Finset.mem_insert_self x s))
        exact mul_le_mul (hab x (Finset.mem_insert_self x s))
          (ih ha_s (fun i hi => hab i (Finset.mem_insert_of_mem hi))) hprod_nn hxb
    refine hprod_le (Finset.univ : Finset (Fin (3 * t))) _ _
      (fun j _ => pow_nonneg (by linarith only [hq2]) _) (fun j _ => ?_)
    let p0 := idxShift t ht shift (2 * j.val)
    let p1 := idxShift t ht shift (2 * j.val + 1)
    let p2 := idxShift t ht shift (2 * j.val + 2)
    have hnxt0 : nextIdx p0 = p1 := by
      ext; simp only [nextIdx, p0, p1, idxShift]; rw [Nat.mod_add_mod]; congr 1; omega
    have hnxt1 : nextIdx p1 = p2 := by
      ext; simp only [nextIdx, p1, p2, idxShift]; rw [Nat.mod_add_mod]; congr 1; omega
    have hprev1 : prevIdx p1 = p0 := by rw [← hnxt0, prevIdx_nextIdx]
    change (q - 1) ^ ((if p0 ∈ Kset then 1 else 0) + (if p1 ∈ Kset then 1 else 0)) ≤
      pairW q (miss j) (if p0 ∈ S then 1 else 0) (if p1 ∈ S then 1 else 0) (if p2 ∈ S then 1 else 0)
    by_cases hp0 : p0 ∈ Kset
    · have hp0e : p0 ∈ endsSet S := (Finset.mem_filter.mp hp0).1
      have hp0S : p0 ∈ S := (Finset.mem_filter.mp hp0e).1
      have hp1nS : p1 ∉ S := by rw [← hnxt0]; exact (Finset.mem_filter.mp hp0e).2
      have hp1nK : p1 ∉ Kset := fun h => hp1nS (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).1
      rw [if_pos hp0, if_neg hp1nK, Nat.add_zero, pow_one]
      dsimp only [pairW]
      rw [if_pos hp0S, if_neg hp1nS]
      simp
    · by_cases hp1 : p1 ∈ Kset
      · have hp1e : p1 ∈ endsSet S := (Finset.mem_filter.mp hp1).1
        have hp1k : (∑ b : Fin 4, runParity S p1 b • v b) = 0 := (Finset.mem_filter.mp hp1).2
        have hp1S : p1 ∈ S := (Finset.mem_filter.mp hp1e).1
        have hp2nS : p2 ∉ S := by rw [← hnxt1]; exact (Finset.mem_filter.mp hp1e).2
        rw [if_neg hp0, if_pos hp1, Nat.zero_add, pow_one]
        by_cases hp0S : p0 ∈ S
        · dsimp only [pairW]
          rw [if_pos hp0S, if_pos hp1S, if_neg hp2nS]
          simp
        · have hsing : S.filter (fun i => runEnd S i = p1) = {p1} :=
            runEnd_singleton S hne p1 hp1e (by rw [hprev1]; exact hp0S)
          have hpar1 : ∀ b, runParity S p1 b = hMat p1 b := fun b => by
            simp [runParity, hsing]
          have hmiss_false : miss j = false := by
            cases hm_eq : miss j
            · rfl
            · exfalso
              apply hmiss j hm_eq
              simpa [hpar1, p1] using hp1k
          dsimp only [pairW]
          rw [if_neg hp0S, if_pos hp1S, if_neg hp2nS, hmiss_false]
          simp
      · rw [if_neg hp0, if_neg hp1, Nat.add_zero, pow_zero]
        dsimp only [pairW]
        split_ifs <;> linarith only [hq1_ge1]
  have hW_lane : W (laneSet shift) = (q - 1) ^ (3 * t) := by
    have hterm : ∀ j : Fin (3 * t),
        pairW q (miss j)
          (if idxShift t ht shift (2 * j.val) ∈ laneSet shift then 1 else 0)
          (if idxShift t ht shift (2 * j.val + 1) ∈ laneSet shift then 1 else 0)
          (if idxShift t ht shift (2 * j.val + 2) ∈ laneSet shift then 1 else 0) = q - 1 := by
      intro j
      have h0 : idxShift t ht shift (2 * j.val) ∈ laneSet shift := by
        simp only [laneSet, Finset.mem_filter, Finset.mem_univ, true_and, idxShift]
        have hmod : ((2 * j.val + shift.val) % (6 * t)) % 2 = (2 * j.val + shift.val) % 2 := by
          have hdvd : 2 ∣ 6 * t := ⟨3 * t, by ring⟩
          exact Nat.mod_mod_of_dvd _ hdvd
        rw [hmod]; omega
      have h1 : idxShift t ht shift (2 * j.val + 1) ∉ laneSet shift := by
        simp only [laneSet, Finset.mem_filter, Finset.mem_univ, true_and, idxShift]
        have hmod : ((2 * j.val + 1 + shift.val) % (6 * t)) % 2 = (2 * j.val + 1 + shift.val) % 2 := by
          have hdvd : 2 ∣ 6 * t := ⟨3 * t, by ring⟩
          exact Nat.mod_mod_of_dvd _ hdvd
        rw [hmod]; omega
      simp [pairW, h0, h1]
    simp only [W, Finset.prod_congr rfl (fun j _ => hterm j), Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  constructor
  · calc ∑ S ∈ Finset.univ.erase (Finset.univ : Finset (Fin (6 * t))), (q - 1) ^ inKer v S
        ≤ ∑ S ∈ Finset.univ.erase (Finset.univ : Finset (Fin (6 * t))), W S :=
          Finset.sum_le_sum (fun S hS => hW_ge S (Finset.mem_erase.mp hS).1)
      _ ≤ ∑ S : Finset (Fin (6 * t)), W S :=
          Finset.sum_le_univ_sum_of_nonneg hW_nonneg
      _ = (matProd (3 * t) M).trace := hW_sum
  · have hlane_ne : laneSet shift ≠ (Finset.univ : Finset (Fin (6 * t))) := by
      intro h
      have hmem : idxShift t ht shift 1 ∈ laneSet shift := by rw [h]; exact Finset.mem_univ _
      simp only [laneSet, Finset.mem_filter, Finset.mem_univ, true_and, idxShift] at hmem
      have hmod : ((1 + shift.val) % (6 * t)) % 2 = (1 + shift.val) % 2 :=
        Nat.mod_mod_of_dvd _ ⟨3 * t, by ring⟩
      rw [hmod] at hmem
      omega
    have hsplit : (∑ S ∈ (Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))).erase (laneSet shift), W S) +
        W (laneSet shift) = ∑ S ∈ Finset.univ.erase (Finset.univ : Finset (Fin (6 * t))), W S := by
      rw [add_comm]
      exact Finset.add_sum_erase _ W (Finset.mem_erase.mpr ⟨hlane_ne, Finset.mem_univ _⟩)
    have hle1 : (∑ S ∈ (Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))).erase (laneSet shift),
        (q - 1) ^ inKer v S) ≤
        ∑ S ∈ (Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))).erase (laneSet shift), W S :=
      Finset.sum_le_sum (fun S hS => hW_ge S (Finset.mem_erase.mp (Finset.mem_erase.mp hS).2).1)
    have hle2 : ∑ S ∈ Finset.univ.erase (Finset.univ : Finset (Fin (6 * t))), W S ≤ (matProd (3 * t) M).trace := by
      rw [← hW_sum]; exact Finset.sum_le_univ_sum_of_nonneg hW_nonneg
    linarith [hW_lane]

lemma hMat_eval_sum {n m : ℕ} (v : Fin 4 → Fin m → F2) (i : Fin n) :
    (∑ b : Fin 4, hMat i b • v b) =
      if i.val % 2 = 0 then
        if i.val / 2 % 3 = 0 then v 0
        else if i.val / 2 % 3 = 1 then v 1
        else v 0 + v 1
      else
        if i.val / 2 % 3 = 0 then v 2
        else if i.val / 2 % 3 = 1 then v 3
        else v 2 + v 3 := by
  have hmod2 : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
  have hmod3 : i.val / 2 % 3 = 0 ∨ i.val / 2 % 3 = 1 ∨ i.val / 2 % 3 = 2 := by omega
  rw [Fin.sum_univ_four]
  rcases hmod2 with h2 | h2 <;> rcases hmod3 with h3 | h3 | h3 <;>
    simp [hMat, h2, h3]

lemma bucket_R_inKer_le (t m : ℕ) (ht : 1 ≤ t) (v : Fin 4 → Fin m → F2)
    (hE : v 0 ≠ 0 ∨ v 1 ≠ 0) (hO : v 2 ≠ 0 ∨ v 3 ≠ 0)
    (S : Finset (Fin (6 * t))) (hne : S ≠ Finset.univ) :
    3 * inKer v S ≤ 8 * t := by
  let A := (endsSet S).filter (fun e => (∑ b : Fin 4, runParity S e b • v b) = 0)
  let A1 := A.filter (fun e => prevIdx e ∉ S)
  let A2 := A.filter (fun e => prevIdx e ∈ S)
  have hA_split : A.card = A1.card + A2.card := by
    have := Finset.card_filter_add_card_filter_not (s := A) (p := fun e => prevIdx e ∈ S)
    dsimp only [A1, A2]
    omega
  -- Bound 1: A1.card <= 2 * t
  have hA1_le : A1.card ≤ 2 * t := by
    let Bset := Finset.univ.filter (fun i : Fin (6 * t) => (∑ b : Fin 4, hMat i b • v b) = 0)
    have hsub : A1 ⊆ Bset := by
      intro e he
      simp only [A1, A, Finset.mem_filter] at he
      have hsing := runEnd_singleton S hne e he.1.1 he.2
      have hpar : ∀ b, runParity S e b = hMat e b := fun b => by simp [runParity, hsing]
      simp only [Bset, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [hpar] using he.1.2
    have hB_le : Bset.card ≤ 2 * t := by
      let e6 : Fin t × Fin 6 ≃ Fin (6 * t) :=
        { toFun := fun p => ⟨6 * p.1.val + p.2.val, by omega⟩
          invFun := fun i => (⟨i.val / 6, by omega⟩, ⟨i.val % 6, Nat.mod_lt _ (by omega)⟩)
          left_inv := fun ⟨a, b⟩ => by ext <;> simp <;> omega
          right_inv := fun i => by ext; simp; omega }
      have hcard : Bset.card = ∑ a : Fin t,
          (Finset.univ.filter (fun r : Fin 6 =>
            (∑ b : Fin 4, hMat (e6 (a, r)) b • v b) = 0)).card := by
        have h1 : Bset.card = ∑ i : Fin (6 * t), if (∑ b : Fin 4, hMat i b • v b) = 0 then 1 else 0 := by
          simp [Bset, Finset.sum_boole]
        rw [h1, ← Equiv.sum_comp e6, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        simp [Finset.sum_boole]
      rw [hcard]
      have hper : ∀ a : Fin t,
          (Finset.univ.filter (fun r : Fin 6 =>
            (∑ b : Fin 4, hMat (e6 (a, r)) b • v b) = 0)).card ≤ 2 := by
        intro a
        have hev0 : (∑ b : Fin 4, hMat (e6 (a, 0)) b • v b) = v 0 := by
          have ha1 : (e6 (a, 0)).val % 2 = 0 := by simp [e6]; omega
          have ha2 : (e6 (a, 0)).val / 2 % 3 = 0 := by simp [e6]; omega
          rw [hMat_eval_sum, ha1, ha2]; simp
        have hev1 : (∑ b : Fin 4, hMat (e6 (a, 2)) b • v b) = v 1 := by
          have ha1 : (e6 (a, 2)).val % 2 = 0 := by simp [e6]; omega
          have ha2 : (e6 (a, 2)).val / 2 % 3 = 1 := by simp [e6]; omega
          rw [hMat_eval_sum, ha1, ha2]; simp
        have hev2 : (∑ b : Fin 4, hMat (e6 (a, 4)) b • v b) = v 0 + v 1 := by
          have ha1 : (e6 (a, 4)).val % 2 = 0 := by simp [e6]; omega
          have ha2 : (e6 (a, 4)).val / 2 % 3 = 2 := by simp [e6]; omega
          rw [hMat_eval_sum, ha1, ha2]; simp
        have hodd0 : (∑ b : Fin 4, hMat (e6 (a, 1)) b • v b) = v 2 := by
          have ha1 : (e6 (a, 1)).val % 2 = 1 := by simp [e6]; omega
          have ha2 : (e6 (a, 1)).val / 2 % 3 = 0 := by simp [e6]; omega
          rw [hMat_eval_sum, ha1, ha2]; simp
        have hodd1 : (∑ b : Fin 4, hMat (e6 (a, 3)) b • v b) = v 3 := by
          have ha1 : (e6 (a, 3)).val % 2 = 1 := by simp [e6]; omega
          have ha2 : (e6 (a, 3)).val / 2 % 3 = 1 := by simp [e6]; omega
          rw [hMat_eval_sum, ha1, ha2]; simp
        have hodd2 : (∑ b : Fin 4, hMat (e6 (a, 5)) b • v b) = v 2 + v 3 := by
          have ha1 : (e6 (a, 5)).val % 2 = 1 := by simp [e6]; omega
          have ha2 : (e6 (a, 5)).val / 2 % 3 = 2 := by simp [e6]; omega
          rw [hMat_eval_sum, ha1, ha2]; simp
        rw [Finset.card_filter, Fin.sum_univ_six, hev0, hodd0, hev1, hodd1, hev2, hodd2]
        have hE_le : (if v 0 = 0 then 1 else 0) + (if v 1 = 0 then 1 else 0) + (if v 0 + v 1 = 0 then 1 else 0) ≤ 1 := by
          by_cases hv0 : v 0 = 0 <;> by_cases hv1 : v 1 = 0
          · exfalso; rcases hE with h | h <;> exact h (by assumption)
          · have hne01 : v 0 + v 1 ≠ 0 := by simp [hv0, hv1]
            simp [hv0, hv1, hne01]
          · have hne01 : v 0 + v 1 ≠ 0 := by simp [hv0, hv1]
            simp [hv0, hv1, hne01]
          · simp [hv0, hv1]; split_ifs <;> omega
        have hO_le : (if v 2 = 0 then 1 else 0) + (if v 3 = 0 then 1 else 0) + (if v 2 + v 3 = 0 then 1 else 0) ≤ 1 := by
          by_cases hv2 : v 2 = 0 <;> by_cases hv3 : v 3 = 0
          · exfalso; rcases hO with h | h <;> exact h (by assumption)
          · have hne23 : v 2 + v 3 ≠ 0 := by simp [hv2, hv3]
            simp [hv2, hv3, hne23]
          · have hne23 : v 2 + v 3 ≠ 0 := by simp [hv2, hv3]
            simp [hv2, hv3, hne23]
          · simp [hv2, hv3]; split_ifs <;> omega
        omega
      calc ∑ a : Fin t, (Finset.univ.filter (fun r : Fin 6 =>
            (∑ b : Fin 4, hMat (e6 (a, r)) b • v b) = 0)).card
          ≤ ∑ _a : Fin t, 2 := Finset.sum_le_sum (fun a _ => hper a)
        _ = 2 * t := by simp [mul_comm]
    exact le_trans (Finset.card_le_card hsub) hB_le
  -- Bound 2: 2 * A1.card + 3 * A2.card <= 6 * t via 3 pairwise-disjoint Finsets in Fin (6 * t)
  have hdisj_pack : 2 * A1.card + 3 * A2.card ≤ 6 * t := by
    let U1 := A
    let U2 := A.image nextIdx
    let U3 := A2.image prevIdx
    have hcardU1 : U1.card = A1.card + A2.card := hA_split
    have hcardU2 : U2.card = A1.card + A2.card := by
      rw [Finset.card_image_of_injective _ nextIdx_injective, hA_split]
    have hcardU3 : U3.card = A2.card := Finset.card_image_of_injective _ prevIdx_injective
    have hd12 : Disjoint U1 U2 := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [U1, A, endsSet, Finset.mem_filter] at hx1
      rcases Finset.mem_image.mp hx2 with ⟨e, he, rfl⟩
      simp only [A, endsSet, Finset.mem_filter] at he
      exact he.1.2 hx1.1.1
    have hd13 : Disjoint U1 U3 := by
      rw [Finset.disjoint_left]
      intro x hx1 hx3
      simp only [U1, A, endsSet, Finset.mem_filter] at hx1
      rcases Finset.mem_image.mp hx3 with ⟨e, he, rfl⟩
      simp only [A2, A, endsSet, Finset.mem_filter] at he
      have hnx := hx1.1.2
      rw [nextIdx_prevIdx] at hnx
      exact hnx he.1.1.1
    have hd23 : Disjoint U2 U3 := by
      rw [Finset.disjoint_left]
      intro x hx2 hx3
      rcases Finset.mem_image.mp hx2 with ⟨e1, he1, rfl⟩
      rcases Finset.mem_image.mp hx3 with ⟨e2, he2, heq⟩
      simp only [A, endsSet, Finset.mem_filter] at he1
      have h2 : prevIdx e2 ∈ S := (Finset.mem_filter.mp he2).2
      rw [heq] at h2
      exact he1.1.2 h2
    have hunion : (U1 ∪ U2 ∪ U3).card = U1.card + U2.card + U3.card := by
      rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hd13, hd23⟩),
        Finset.card_union_of_disjoint hd12]
    have hle : (U1 ∪ U2 ∪ U3).card ≤ 6 * t := by
      calc (U1 ∪ U2 ∪ U3).card ≤ (Finset.univ : Finset (Fin (6 * t))).card :=
            Finset.card_le_card (Finset.subset_univ _)
        _ = 6 * t := by simp
    omega
  change 3 * A.card ≤ 8 * t
  omega

lemma inKer_lane_le (t m : ℕ) (ht : 1 ≤ t) (v : Fin 4 → Fin m → F2) (shift : Fin 2)
    (hne : if shift = 0 then (v 0 ≠ 0 ∨ v 1 ≠ 0) else (v 2 ≠ 0 ∨ v 3 ≠ 0)) :
    inKer v (laneSet shift : Finset (Fin (6 * t))) ≤ t := by
  have hlane_ne : laneSet shift ≠ (Finset.univ : Finset (Fin (6 * t))) := by
    intro h
    have hmem : idxShift t ht shift 1 ∈ laneSet shift := by rw [h]; exact Finset.mem_univ _
    simp only [laneSet, Finset.mem_filter, Finset.mem_univ, true_and, idxShift] at hmem
    have hmod : ((1 + shift.val) % (6 * t)) % 2 = (1 + shift.val) % 2 :=
      Nat.mod_mod_of_dvd _ ⟨3 * t, by ring⟩
    rw [hmod] at hmem
    omega
  have hends_eq : endsSet (laneSet shift : Finset (Fin (6 * t))) = laneSet shift := by
    ext i
    simp only [endsSet, laneSet, Finset.mem_filter, Finset.mem_univ, true_and, and_iff_left_iff_imp]
    intro hi
    simp only [nextIdx]
    have hmod : ((i.val + 1) % (6 * t)) % 2 = (i.val + 1) % 2 :=
      Nat.mod_mod_of_dvd _ ⟨3 * t, by ring⟩
    rw [hmod]; omega
  have hpar_eq : ∀ i ∈ (laneSet shift : Finset (Fin (6 * t))), ∀ b,
      runParity (laneSet shift : Finset (Fin (6 * t))) i b = hMat i b := by
    intro i hi b
    have hprev : prevIdx i ∉ laneSet shift := by
      simp only [laneSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      simp only [prevIdx]
      have hmod : ((i.val + 6 * t - 1) % (6 * t)) % 2 = (i.val + 6 * t - 1) % 2 :=
        Nat.mod_mod_of_dvd _ ⟨3 * t, by ring⟩
      rw [hmod]; omega
    have hsing := runEnd_singleton (laneSet shift) hlane_ne i (by rw [hends_eq]; exact hi) hprev
    simp [runParity, hsing]
  have hcard : inKer v (laneSet shift : Finset (Fin (6 * t))) =
      ((laneSet shift : Finset (Fin (6 * t))).filter (fun i => (∑ b : Fin 4, hMat i b • v b) = 0)).card := by
    dsimp only [inKer]
    rw [hends_eq]
    congr 1
    refine Finset.filter_congr (fun i hi => ?_)
    simp [hpar_eq i hi]
  rw [hcard]
  let eL : Fin t × Fin 3 ≃ {i : Fin (6 * t) // i ∈ laneSet shift} :=
    { toFun := fun p => ⟨⟨6 * p.1.val + 2 * p.2.val + shift.val, by omega⟩, by
        simp only [laneSet, Finset.mem_filter, Finset.mem_univ, true_and]; omega⟩
      invFun := fun i =>
        have hi : i.1.val % 2 = shift.val := (Finset.mem_filter.mp i.2).2
        (⟨i.1.val / 6, by omega⟩, ⟨(i.1.val % 6) / 2, by omega⟩)
      left_inv := fun ⟨a, r⟩ => by ext <;> simp <;> omega
      right_inv := fun ⟨i, hi⟩ => by
        have hpar : i.val % 2 = shift.val := (Finset.mem_filter.mp hi).2
        ext; simp; omega }
  have hsum : ((laneSet shift : Finset (Fin (6 * t))).filter (fun i => (∑ b : Fin 4, hMat i b • v b) = 0)).card =
      ∑ a : Fin t, (Finset.univ.filter (fun r : Fin 3 =>
        (∑ b : Fin 4, hMat (eL (a, r)).1 b • v b) = 0)).card := by
    have h1 : ((laneSet shift : Finset (Fin (6 * t))).filter (fun i => (∑ b : Fin 4, hMat i b • v b) = 0)).card =
        ∑ i : {i : Fin (6 * t) // i ∈ laneSet shift},
          if (∑ b : Fin 4, hMat i.1 b • v b) = 0 then 1 else 0 := by
      rw [Finset.sum_coe_sort (laneSet shift : Finset (Fin (6 * t))) (fun i => if (∑ b : Fin 4, hMat i b • v b) = 0 then 1 else 0)]
      simp [Finset.sum_boole]
    rw [h1, ← Equiv.sum_comp eL, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    simp [Finset.sum_boole]
  rw [hsum]
  have hper : ∀ a : Fin t, (Finset.univ.filter (fun r : Fin 3 =>
      (∑ b : Fin 4, hMat (eL (a, r)).1 b • v b) = 0)).card ≤ 1 := by
    intro a
    fin_cases shift
    · simp only [↓reduceIte] at hne
      have h0 : (∑ b : Fin 4, hMat (eL (a, 0)).1 b • v b) = v 0 := by
        have ha1 : (eL (a, 0)).1.val % 2 = 0 := by simp [eL]; omega
        have ha2 : (eL (a, 0)).1.val / 2 % 3 = 0 := by simp [eL]; omega
        rw [hMat_eval_sum, ha1, ha2]; simp
      have h1 : (∑ b : Fin 4, hMat (eL (a, 1)).1 b • v b) = v 1 := by
        have ha1 : (eL (a, 1)).1.val % 2 = 0 := by simp [eL]; omega
        have ha2 : (eL (a, 1)).1.val / 2 % 3 = 1 := by simp [eL]; omega
        rw [hMat_eval_sum, ha1, ha2]; simp
      have h2 : (∑ b : Fin 4, hMat (eL (a, 2)).1 b • v b) = v 0 + v 1 := by
        have ha1 : (eL (a, 2)).1.val % 2 = 0 := by simp [eL]; omega
        have ha2 : (eL (a, 2)).1.val / 2 % 3 = 2 := by simp [eL]; omega
        rw [hMat_eval_sum, ha1, ha2]; simp
      rw [Finset.card_filter, Fin.sum_univ_three, h0, h1, h2]
      by_cases hv0 : v 0 = 0 <;> by_cases hv1 : v 1 = 0
      · exfalso; rcases hne with h | h <;> exact h (by assumption)
      · have hne01 : v 0 + v 1 ≠ 0 := by simp [hv0, hv1]
        simp [hv0, hv1, hne01]
      · have hne01 : v 0 + v 1 ≠ 0 := by simp [hv0, hv1]
        simp [hv0, hv1, hne01]
      · simp [hv0, hv1]; split_ifs <;> omega
    · simp only [Fin.isValue, Fin.one_eq_zero_iff, OfNat.ofNat_ne_zero, ↓reduceIte] at hne
      have h0 : (∑ b : Fin 4, hMat (eL (a, 0)).1 b • v b) = v 2 := by
        have ha1 : (eL (a, 0)).1.val % 2 = 1 := by simp [eL]; omega
        have ha2 : (eL (a, 0)).1.val / 2 % 3 = 0 := by simp [eL]; omega
        rw [hMat_eval_sum, ha1, ha2]; simp
      have h1 : (∑ b : Fin 4, hMat (eL (a, 1)).1 b • v b) = v 3 := by
        have ha1 : (eL (a, 1)).1.val % 2 = 1 := by simp [eL]; omega
        have ha2 : (eL (a, 1)).1.val / 2 % 3 = 1 := by simp [eL]; omega
        rw [hMat_eval_sum, ha1, ha2]; simp
      have h2 : (∑ b : Fin 4, hMat (eL (a, 2)).1 b • v b) = v 2 + v 3 := by
        have ha1 : (eL (a, 2)).1.val % 2 = 1 := by simp [eL]; omega
        have ha2 : (eL (a, 2)).1.val / 2 % 3 = 2 := by simp [eL]; omega
        rw [hMat_eval_sum, ha1, ha2]; simp
      rw [Finset.card_filter, Fin.sum_univ_three, h0, h1, h2]
      by_cases hv2 : v 2 = 0 <;> by_cases hv3 : v 3 = 0
      · exfalso; rcases hne with h | h <;> exact h (by assumption)
      · have hne23 : v 2 + v 3 ≠ 0 := by simp [hv2, hv3]
        simp [hv2, hv3, hne23]
      · have hne23 : v 2 + v 3 ≠ 0 := by simp [hv2, hv3]
        simp [hv2, hv3, hne23]
      · simp [hv2, hv3]; split_ifs <;> omega
  calc ∑ a : Fin t, (Finset.univ.filter (fun r : Fin 3 =>
        (∑ b : Fin 4, hMat (eL (a, r)).1 b • v b) = 0)).card
      ≤ ∑ _a : Fin t, 1 := Finset.sum_le_sum (fun a _ => hper a)
    _ = t := by simp

-- Section 5: Unified Fourier bucket bounds for validCols (used for both m = d and m = d - 1)

lemma sum_bucket_E_or_O_nonlane (t m : ℕ) (ht : 1 ≤ t) (hm : 1 ≤ m) (shift : Fin 2) :
    let q : ℝ := (2 : ℝ) ^ m
    let Bset : Finset (Fin 4 → Fin m → F2) :=
      Finset.univ.filter (fun v =>
        v ≠ 0 ∧ (if shift = 0 then (v 0 = 0 ∧ v 1 = 0) else (v 2 = 0 ∧ v 3 = 0)))
    (1 / q ^ 4) * ∑ v ∈ Bset,
      ∑ S ∈ ((Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))).erase (laneSet shift)),
        (q - 1) ^ (inKer v S) ≤
      ((q + 4) ^ (3 * t) + 4 * (q + 4) ^ (3 * t - 1) - (q - 1) ^ (3 * t)) / q ^ 2 +
        6 * (q + 6) ^ (3 * t) / q ^ 3 := by
  intro q Bset
  have hq2 : (2 : ℝ) ≤ q := by
    have : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ m := pow_le_pow_right₀ (by norm_num) hm
    simpa [q] using this
  have hqpos : (0 : ℝ) < q := by linarith
  let B1 := Bset.filter (fun v =>
    if shift = 0 then (v 2 = 0 ∨ v 3 = 0 ∨ v 2 = v 3)
    else (v 0 = 0 ∨ v 1 = 0 ∨ v 0 = v 1))
  let B2 := Bset.filter (fun v =>
    ¬ (if shift = 0 then (v 2 = 0 ∨ v 3 = 0 ∨ v 2 = v 3)
       else (v 0 = 0 ∨ v 1 = 0 ∨ v 0 = v 1)))
  have hsplit : ∑ v ∈ Bset,
      (∑ S ∈ ((Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))).erase (laneSet shift)),
        (q - 1) ^ (inKer v S)) =
      (∑ v ∈ B1, ∑ S ∈ ((Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))).erase (laneSet shift)),
        (q - 1) ^ (inKer v S)) +
      (∑ v ∈ B2, ∑ S ∈ ((Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))).erase (laneSet shift)),
        (q - 1) ^ (inKer v S)) := by
    rw [← Finset.sum_filter_add_sum_filter_not Bset
      (fun v => if shift = 0 then (v 2 = 0 ∨ v 3 = 0 ∨ v 2 = v 3) else (v 0 = 0 ∨ v 1 = 0 ∨ v 0 = v 1))]
  rw [hsplit, mul_add]
  have hB2_card : (B2.card : ℝ) ≤ q ^ 2 := by
    have hsub : B2 ⊆ Finset.univ.filter (fun v : Fin 4 → Fin m → F2 =>
        if shift = 0 then (v 0 = 0 ∧ v 1 = 0) else (v 2 = 0 ∧ v 3 = 0)) := by
      intro v hv
      simp only [B2, Bset, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      exact hv.1.2
    have hcard_eq : (Finset.univ.filter (fun v : Fin 4 → Fin m → F2 =>
        if shift = 0 then (v 0 = 0 ∧ v 1 = 0) else (v 2 = 0 ∧ v 3 = 0))).card = (2 ^ m) ^ 2 := by
      have hcard_bij : (Finset.univ.filter (fun v : Fin 4 → Fin m → F2 =>
          if shift = 0 then (v 0 = 0 ∧ v 1 = 0) else (v 2 = 0 ∧ v 3 = 0))).card =
          (Finset.univ : Finset ((Fin m → F2) × (Fin m → F2))).card := by
        refine Finset.card_bij
          (fun v _ => if shift = 0 then (v 2, v 3) else (v 0, v 1)) ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro v₁ hv₁ v₂ hv₂ heq
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv₁ hv₂
          rcases fin2_cases shift with rfl | rfl
          · simp only [↓reduceIte, Prod.mk.injEq] at hv₁ hv₂ heq
            ext b j; fin_cases b <;> dsimp only
            · simp [hv₁.1, hv₂.1]
            · simp [hv₁.2, hv₂.2]
            · exact congrFun heq.1 j
            · exact congrFun heq.2 j
          · have h10 : (1 : Fin 2) ≠ 0 := by decide
            simp only [h10, ↓reduceIte, Prod.mk.injEq] at hv₁ hv₂ heq
            ext b j; fin_cases b <;> dsimp only
            · exact congrFun heq.1 j
            · exact congrFun heq.2 j
            · simp [hv₁.1, hv₂.1]
            · simp [hv₁.2, hv₂.2]
        · intro ⟨u1, u2⟩ _
          rcases fin2_cases shift with rfl | rfl
          · refine ⟨fun b => if b = 2 then u1 else if b = 3 then u2 else 0, ?_, by simp⟩
            simp
          · refine ⟨fun b => if b = 0 then u1 else if b = 1 then u2 else 0, ?_, by simp⟩
            simp
      rw [hcard_bij]
      simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_pi, Fintype.card_fin, ZMod.card,
        Finset.prod_const, sq]
    have hle : B2.card ≤ (2 ^ m) ^ 2 := le_trans (Finset.card_le_card hsub) (le_of_eq hcard_eq)
    dsimp only [q]
    exact_mod_cast hle
  have hB1_card : (B1.card : ℝ) ≤ 3 * q := by
    let U0 := Finset.univ.filter (fun v : Fin 4 → Fin m → F2 =>
      if shift = 0 then (v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0) else (v 2 = 0 ∧ v 3 = 0 ∧ v 0 = 0))
    let U1 := Finset.univ.filter (fun v : Fin 4 → Fin m → F2 =>
      if shift = 0 then (v 0 = 0 ∧ v 1 = 0 ∧ v 3 = 0) else (v 2 = 0 ∧ v 3 = 0 ∧ v 1 = 0))
    let U2 := Finset.univ.filter (fun v : Fin 4 → Fin m → F2 =>
      if shift = 0 then (v 0 = 0 ∧ v 1 = 0 ∧ v 2 = v 3) else (v 2 = 0 ∧ v 3 = 0 ∧ v 0 = v 1))
    have hsub : B1 ⊆ U0 ∪ U1 ∪ U2 := by
      intro v hv
      simp only [B1, Bset, U0, U1, U2, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_union] at hv ⊢
      rcases fin2_cases shift with rfl | rfl
      · simp only [↓reduceIte] at hv ⊢
        rcases hv.2 with h | h | h
        · exact Or.inl (Or.inl ⟨hv.1.2.1, hv.1.2.2, h⟩)
        · exact Or.inl (Or.inr ⟨hv.1.2.1, hv.1.2.2, h⟩)
        · exact Or.inr ⟨hv.1.2.1, hv.1.2.2, h⟩
      · simp only [Fin.isValue, Fin.one_eq_zero_iff, OfNat.ofNat_ne_zero, ↓reduceIte] at hv ⊢
        rcases hv.2 with h | h | h
        · exact Or.inl (Or.inl ⟨hv.1.2.1, hv.1.2.2, h⟩)
        · exact Or.inl (Or.inr ⟨hv.1.2.1, hv.1.2.2, h⟩)
        · exact Or.inr ⟨hv.1.2.1, hv.1.2.2, h⟩
    have hU0 : U0.card ≤ 2 ^ m := by
      refine le_trans (Finset.card_le_card_of_injOn (fun v => if shift = 0 then v 3 else v 1)
        (fun _ _ => Finset.mem_univ _) ?_) (by simp [Fintype.card_pi, ZMod.card])
      intro v₁ hv₁ v₂ hv₂ heq
      simp only [Finset.mem_coe, U0, Finset.mem_filter, Finset.mem_univ, true_and] at hv₁ hv₂
      rcases fin2_cases shift with rfl | rfl
      · simp only [↓reduceIte] at hv₁ hv₂ heq
        ext b j; fin_cases b <;> dsimp only
        · simp [hv₁.1, hv₂.1]
        · simp [hv₁.2.1, hv₂.2.1]
        · simp [hv₁.2.2, hv₂.2.2]
        · exact congrFun heq j
      · simp only [Fin.isValue, Fin.one_eq_zero_iff, OfNat.ofNat_ne_zero, ↓reduceIte] at hv₁ hv₂ heq
        ext b j; fin_cases b <;> dsimp only
        · simp [hv₁.2.2, hv₂.2.2]
        · exact congrFun heq j
        · simp [hv₁.1, hv₂.1]
        · simp [hv₁.2.1, hv₂.2.1]
    have hU1 : U1.card ≤ 2 ^ m := by
      refine le_trans (Finset.card_le_card_of_injOn (fun v => if shift = 0 then v 2 else v 0)
        (fun _ _ => Finset.mem_univ _) ?_) (by simp [Fintype.card_pi, ZMod.card])
      intro v₁ hv₁ v₂ hv₂ heq
      simp only [Finset.mem_coe, U1, Finset.mem_filter, Finset.mem_univ, true_and] at hv₁ hv₂
      rcases fin2_cases shift with rfl | rfl
      · simp only [↓reduceIte] at hv₁ hv₂ heq
        ext b j; fin_cases b <;> dsimp only
        · simp [hv₁.1, hv₂.1]
        · simp [hv₁.2.1, hv₂.2.1]
        · exact congrFun heq j
        · simp [hv₁.2.2, hv₂.2.2]
      · simp only [Fin.isValue, Fin.one_eq_zero_iff, OfNat.ofNat_ne_zero, ↓reduceIte] at hv₁ hv₂ heq
        ext b j; fin_cases b <;> dsimp only
        · exact congrFun heq j
        · simp [hv₁.2.2, hv₂.2.2]
        · simp [hv₁.1, hv₂.1]
        · simp [hv₁.2.1, hv₂.2.1]
    have hU2 : U2.card ≤ 2 ^ m := by
      refine le_trans (Finset.card_le_card_of_injOn (fun v => if shift = 0 then v 2 else v 0)
        (fun _ _ => Finset.mem_univ _) ?_) (by simp [Fintype.card_pi, ZMod.card])
      intro v₁ hv₁ v₂ hv₂ heq
      simp only [Finset.mem_coe, U2, Finset.mem_filter, Finset.mem_univ, true_and] at hv₁ hv₂
      rcases fin2_cases shift with rfl | rfl
      · simp only [↓reduceIte] at hv₁ hv₂ heq
        ext b j; fin_cases b <;> dsimp only
        · simp [hv₁.1, hv₂.1]
        · simp [hv₁.2.1, hv₂.2.1]
        · exact congrFun heq j
        · change v₁ 3 j = v₂ 3 j; rw [← hv₁.2.2, ← hv₂.2.2]; exact congrFun heq j
      · simp only [Fin.isValue, Fin.one_eq_zero_iff, OfNat.ofNat_ne_zero, ↓reduceIte] at hv₁ hv₂ heq
        ext b j; fin_cases b <;> dsimp only
        · exact congrFun heq j
        · change v₁ 1 j = v₂ 1 j; rw [← hv₁.2.2, ← hv₂.2.2]; exact congrFun heq j
        · simp [hv₁.1, hv₂.1]
        · simp [hv₁.2.1, hv₂.2.1]
    have hle : B1.card ≤ 3 * 2 ^ m := by
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_union_le (U0 ∪ U1) U2
      have h3 := Finset.card_union_le U0 U1
      omega
    dsimp only [q]
    exact_mod_cast hle
  -- Bound each v in B2 using all-miss T2^a
  have hperB2 : ∀ v ∈ B2,
      (∑ S ∈ ((Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))).erase (laneSet shift)),
        (q - 1) ^ (inKer v S)) ≤
        (q + 4) ^ (3 * t) + 4 * (q + 4) ^ (3 * t - 1) - (q - 1) ^ (3 * t) := by
    intro v hv
    simp only [B2, Bset, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    have hmiss : ∀ j : Fin (3 * t), (true : Bool) = true →
        (∑ b : Fin 4, hMat (idxShift t ht shift (2 * j.val + 1)) b • v b) ≠ 0 := by
      intro j _
      rw [hMat_eval_sum]
      rcases fin2_cases shift with rfl | rfl
      · simp only [↓reduceIte, not_or] at hv
        rcases hv.2 with ⟨hv2, hv3, hv23⟩
        have hpar : (idxShift t ht 0 (2 * j.val + 1)).val % 2 = 1 := by
          simp only [idxShift, Fin.val_zero, add_zero]
          rw [Nat.mod_eq_of_lt (by omega : 2 * j.val + 1 < 6 * t)]; omega
        simp only [hpar, one_ne_zero, ↓reduceIte]
        split_ifs
        · exact hv2
        · exact hv3
        · intro hsum
          apply hv23
          ext r
          have hr := congrFun hsum r
          simp only [Pi.add_apply, Pi.zero_apply] at hr
          rcases f2_eq_zero_or_one (v 2 r) with h0 | h1 <;>
            rcases f2_eq_zero_or_one (v 3 r) with h0' | h1' <;> simp_all
      · have h10 : (1 : Fin 2) ≠ 0 := by decide
        simp only [h10, ↓reduceIte, not_or] at hv
        rcases hv.2 with ⟨hv0, hv1, hv01⟩
        have hpar : (idxShift t ht 1 (2 * j.val + 1)).val % 2 = 0 := by
          simp only [idxShift, Fin.val_one]
          have hdvd : 2 ∣ 6 * t := ⟨3 * t, by ring⟩
          have hmod := Nat.mod_mod_of_dvd (2 * j.val + 1 + 1) hdvd
          rw [hmod]; omega
        simp only [hpar, ↓reduceIte]
        split_ifs
        · exact hv0
        · exact hv1
        · intro hsum
          apply hv01
          ext r
          have hr := congrFun hsum r
          simp only [Pi.add_apply, Pi.zero_apply] at hr
          rcases f2_eq_zero_or_one (v 0 r) with h0 | h1 <;>
            rcases f2_eq_zero_or_one (v 1 r) with h0' | h1' <;> simp_all
    have hb := (sum_inKer_pair_bound t m ht hm v shift (fun _ => true) hmiss).2
    simp only [↓reduceIte, matProd_const] at hb
    have htr := trace_matT2_pow_le q (by linarith) (3 * t) (by omega)
    linarith
  -- Bound each v in B1 using period-3 M6^t
  have hperB1 : ∀ v ∈ B1,
      (∑ S ∈ ((Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))).erase (laneSet shift)),
        (q - 1) ^ (inKer v S)) ≤ 2 * (q + 6) ^ (3 * t) := by
    intro v hv
    simp only [B1, Bset, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    -- Determine which residue mod 3 is NOT missed
    have hex_c : ∃ c : Fin 3, ∀ j : Fin (3 * t), j.val % 3 ≠ c.val →
        (∑ b : Fin 4, hMat (idxShift t ht shift (2 * j.val + 1)) b • v b) ≠ 0 := by
      rcases fin2_cases shift with rfl | rfl
      · simp only [↓reduceIte] at hv
        rcases hv with ⟨⟨hvne, hv0, hv1⟩, hcase⟩
        have hnotboth : ¬ (v 2 = 0 ∧ v 3 = 0) := by
          rintro ⟨h2, h3⟩; apply hvne; ext b j; fin_cases b <;> simp [hv0, hv1, h2, h3]
        have hpos : ∀ j : Fin (3 * t),
            (idxShift t ht 0 (2 * j.val + 1)).val % 2 = 1 ∧
            (idxShift t ht 0 (2 * j.val + 1)).val / 2 % 3 = j.val % 3 := by
          intro j
          simp only [idxShift, Fin.val_zero, add_zero, Nat.mod_eq_of_lt (by omega : 2 * j.val + 1 < 6 * t)]
          omega
        rcases hcase with hv2 | hv3 | hv23
        · refine ⟨0, fun j hj => ?_⟩
          have hv3ne : v 3 ≠ 0 := fun h => hnotboth ⟨hv2, h⟩
          rw [hMat_eval_sum, (hpos j).1, (hpos j).2]
          simp only [one_ne_zero, ↓reduceIte, Fin.val_zero] at hj ⊢
          rw [if_neg hj]
          split_ifs
          · exact hv3ne
          · simpa [hv2] using hv3ne
        · refine ⟨1, fun j hj => ?_⟩
          have hv2ne : v 2 ≠ 0 := fun h => hnotboth ⟨h, hv3⟩
          rw [hMat_eval_sum, (hpos j).1, (hpos j).2]
          simp only [one_ne_zero, ↓reduceIte, Fin.val_one] at hj ⊢
          rw [if_neg hj]
          split_ifs
          · exact hv2ne
          · simpa [hv3] using hv2ne
        · refine ⟨2, fun j hj => ?_⟩
          have hv2ne : v 2 ≠ 0 := fun h => hnotboth ⟨h, hv23.symm.trans h⟩
          have hv3ne : v 3 ≠ 0 := fun h => hnotboth ⟨hv23.trans h, h⟩
          rw [hMat_eval_sum, (hpos j).1, (hpos j).2]
          simp only [one_ne_zero, ↓reduceIte, Fin.val_two] at hj ⊢
          have h01 : j.val % 3 = 0 ∨ j.val % 3 = 1 := by omega
          rcases h01 with h0 | h1
          · simp [h0, hv2ne]
          · simp [h1, hv3ne]
      · simp only [Fin.isValue, Fin.one_eq_zero_iff, OfNat.ofNat_ne_zero, ↓reduceIte] at hv
        rcases hv with ⟨⟨hvne, hv2, hv3⟩, hcase⟩
        have hnotboth : ¬ (v 0 = 0 ∧ v 1 = 0) := by
          rintro ⟨h0, h1⟩; apply hvne; ext b j; fin_cases b <;> simp [hv2, hv3, h0, h1]
        have hpos : ∀ j : Fin (3 * t),
            (idxShift t ht 1 (2 * j.val + 1)).val % 2 = 0 ∧
            (idxShift t ht 1 (2 * j.val + 1)).val / 2 % 3 = (j.val + 1) % 3 := by
          intro j
          simp only [idxShift, Fin.val_one]
          by_cases hlast : j.val + 1 = 3 * t
          · have h6 : 2 * j.val + 1 + 1 = 6 * t := by omega
            rw [h6, Nat.mod_self]; omega
          · rw [Nat.mod_eq_of_lt (by omega : 2 * j.val + 1 + 1 < 6 * t)]; omega
        rcases hcase with hv0 | hv1 | hv01
        · refine ⟨2, fun j hj => ?_⟩
          have hv1ne : v 1 ≠ 0 := fun h => hnotboth ⟨hv0, h⟩
          rw [hMat_eval_sum, (hpos j).1, (hpos j).2]
          simp only [↓reduceIte, Fin.val_two] at hj ⊢
          have hne0 : (j.val + 1) % 3 ≠ 0 := by omega
          rw [if_neg hne0]
          split_ifs
          · exact hv1ne
          · simpa [hv0] using hv1ne
        · refine ⟨0, fun j hj => ?_⟩
          have hv0ne : v 0 ≠ 0 := fun h => hnotboth ⟨h, hv1⟩
          rw [hMat_eval_sum, (hpos j).1, (hpos j).2]
          simp only [↓reduceIte, Fin.val_zero] at hj ⊢
          have hne1 : (j.val + 1) % 3 ≠ 1 := by omega
          rw [if_neg hne1]
          split_ifs
          · exact hv0ne
          · simpa [hv1] using hv0ne
        · refine ⟨1, fun j hj => ?_⟩
          have hv0ne : v 0 ≠ 0 := fun h => hnotboth ⟨h, hv01.symm.trans h⟩
          have hv1ne : v 1 ≠ 0 := fun h => hnotboth ⟨hv01.trans h, h⟩
          rw [hMat_eval_sum, (hpos j).1, (hpos j).2]
          simp only [↓reduceIte, Fin.val_one] at hj ⊢
          have h01 : (j.val + 1) % 3 = 0 ∨ (j.val + 1) % 3 = 1 := by omega
          rcases h01 with h0 | h1
          · simp [h0, hv0ne]
          · simp [h1, hv1ne]
    obtain ⟨c, hc⟩ := hex_c
    let miss : Fin (3 * t) → Bool := fun j => decide (j.val % 3 ≠ c.val)
    have hmiss : ∀ j : Fin (3 * t), miss j = true →
        (∑ b : Fin 4, hMat (idxShift t ht shift (2 * j.val + 1)) b • v b) ≠ 0 := by
      intro j hj
      exact hc j (of_decide_eq_true hj)
    have hb := (sum_inKer_pair_bound t m ht hm v shift miss hmiss).1
    have hsub_sum :
        (∑ S ∈ ((Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))).erase (laneSet shift)),
          (q - 1) ^ (inKer v S)) ≤
        ∑ S ∈ (Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))),
          (q - 1) ^ (inKer v S) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun _ _ _ => by
        exact pow_nonneg (by linarith) _)
    have htr_eq : (matProd (3 * t) (fun j => if miss j then matT2 q else matA2 q)).trace =
        (matM6 q ^ t).trace := by
      rcases c with ⟨cv, hcv⟩
      interval_cases cv
      · rw [matProd_period3 (matA2 q) (matT2 q) (matT2 q) t _ (fun j => by
          dsimp only [miss]
          have h3 : j.val % 3 = 0 ∨ j.val % 3 = 1 ∨ j.val % 3 = 2 := by omega
          rcases h3 with h | h | h <;> simp [h])]
        have h1 : matA2 q * matT2 q * matT2 q = matA2 q * (matT2 q * matT2 q) := Matrix.mul_assoc _ _ _
        rw [h1, trace_pow_mul_comm]
        rfl
      · rw [matProd_period3 (matT2 q) (matA2 q) (matT2 q) t _ (fun j => by
          dsimp only [miss]
          have h3 : j.val % 3 = 0 ∨ j.val % 3 = 1 ∨ j.val % 3 = 2 := by omega
          rcases h3 with h | h | h <;> simp [h])]
        rw [trace_pow_mul_comm (matT2 q * matA2 q) (matT2 q)]
        have h1 : matT2 q * (matT2 q * matA2 q) = matM6 q := by
          simp [matM6, Matrix.mul_assoc]
        rw [h1]
      · rw [matProd_period3 (matT2 q) (matT2 q) (matA2 q) t _ (fun j => by
          dsimp only [miss]
          have h3 : j.val % 3 = 0 ∨ j.val % 3 = 1 ∨ j.val % 3 = 2 := by omega
          rcases h3 with h | h | h <;> simp [h])]
        rfl
    exact le_trans hsub_sum (le_trans hb (by rw [htr_eq]; exact trace_matM6_pow_le q (by linarith) t))
  have hB2_nn : 0 ≤ (q + 4) ^ (3 * t) + 4 * (q + 4) ^ (3 * t - 1) - (q - 1) ^ (3 * t) := by
    have h1 : (q - 1) ^ (3 * t) ≤ (q + 4) ^ (3 * t) :=
      pow_le_pow_left₀ (by linarith) (by linarith) (3 * t)
    have h2 : 0 ≤ 4 * (q + 4) ^ (3 * t - 1) := by positivity
    linarith
  have hsumB2 : (1 / q ^ 4) * ∑ v ∈ B2,
      ∑ S ∈ ((Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))).erase (laneSet shift)),
        (q - 1) ^ (inKer v S) ≤
      ((q + 4) ^ (3 * t) + 4 * (q + 4) ^ (3 * t - 1) - (q - 1) ^ (3 * t)) / q ^ 2 := by
    calc (1 / q ^ 4) * ∑ v ∈ B2,
          ∑ S ∈ ((Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))).erase (laneSet shift)),
            (q - 1) ^ (inKer v S)
        ≤ (1 / q ^ 4) * ∑ _v ∈ B2,
          ((q + 4) ^ (3 * t) + 4 * (q + 4) ^ (3 * t - 1) - (q - 1) ^ (3 * t)) := by
          gcongr with v hv; exact hperB2 v hv
      _ = (1 / q ^ 4) * ((B2.card : ℝ) *
          ((q + 4) ^ (3 * t) + 4 * (q + 4) ^ (3 * t - 1) - (q - 1) ^ (3 * t))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (1 / q ^ 4) * (q ^ 2 *
          ((q + 4) ^ (3 * t) + 4 * (q + 4) ^ (3 * t - 1) - (q - 1) ^ (3 * t))) := by
          gcongr
      _ = ((q + 4) ^ (3 * t) + 4 * (q + 4) ^ (3 * t - 1) - (q - 1) ^ (3 * t)) / q ^ 2 := by
          field_simp [ne_of_gt hqpos]
  have hsumB1 : (1 / q ^ 4) * ∑ v ∈ B1,
      ∑ S ∈ ((Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))).erase (laneSet shift)),
        (q - 1) ^ (inKer v S) ≤
      6 * (q + 6) ^ (3 * t) / q ^ 3 := by
    calc (1 / q ^ 4) * ∑ v ∈ B1,
          ∑ S ∈ ((Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))).erase (laneSet shift)),
            (q - 1) ^ (inKer v S)
        ≤ (1 / q ^ 4) * ∑ _v ∈ B1, (2 * (q + 6) ^ (3 * t)) := by
          gcongr with v hv; exact hperB1 v hv
      _ = (1 / q ^ 4) * ((B1.card : ℝ) * (2 * (q + 6) ^ (3 * t))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (1 / q ^ 4) * ((3 * q) * (2 * (q + 6) ^ (3 * t))) := by
          gcongr
      _ = 6 * (q + 6) ^ (3 * t) / q ^ 3 := by
          field_simp [ne_of_gt hqpos]; ring
  linarith

lemma sum_bucket_R (t m : ℕ) (ht : 1 ≤ t) (hm : 1 ≤ m) :
    let q : ℝ := (2 : ℝ) ^ m
    let Rset : Finset (Fin 4 → Fin m → F2) :=
      Finset.univ.filter (fun v => (v 0 ≠ 0 ∨ v 1 ≠ 0) ∧ (v 2 ≠ 0 ∨ v 3 ≠ 0))
    (1 / q ^ 4) * ∑ v ∈ Rset,
      ∑ S ∈ (Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))),
        (q - 1) ^ (inKer v S) ≤
      (2 : ℝ) ^ (6 * t) * q ^ (3 * t - t / 3) := by
  intro q Rset
  have hq2 : (2 : ℝ) ≤ q := by
    have : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ m := pow_le_pow_right₀ (by norm_num) hm
    simpa [q] using this
  have hqpos : (0 : ℝ) < q := by linarith
  have hR_card : (Rset.card : ℝ) ≤ q ^ 4 := by
    have h1 : Rset.card ≤ Fintype.card (Fin 4 → Fin m → F2) := Finset.card_le_univ _
    have h2 : Fintype.card (Fin 4 → Fin m → F2) = (2 ^ m) ^ 4 := by
      simp [Fintype.card_pi, ZMod.card]
    rw [h2] at h1
    dsimp only [q]
    exact_mod_cast h1
  have hS_card : ((Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))).card : ℝ) ≤ (2 : ℝ) ^ (6 * t) := by
    have h1 : (Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))).card ≤
        Fintype.card (Finset (Fin (6 * t))) := Finset.card_le_univ _
    have h2 : Fintype.card (Finset (Fin (6 * t))) = 2 ^ (6 * t) := by simp
    rw [h2] at h1
    exact_mod_cast h1
  have hper : ∀ v ∈ Rset, ∀ S ∈ (Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))),
      (q - 1) ^ (inKer v S) ≤ q ^ (3 * t - t / 3) := by
    intro v hv S hS
    simp only [Rset, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    have h3 := bucket_R_inKer_le t m ht v hv.1 hv.2 S (Finset.mem_erase.mp hS).1
    have hle : inKer v S ≤ 3 * t - t / 3 := by omega
    calc (q - 1) ^ (inKer v S)
        ≤ q ^ (inKer v S) := pow_le_pow_left₀ (by linarith) (by linarith) _
      _ ≤ q ^ (3 * t - t / 3) := pow_le_pow_right₀ (by linarith) hle
  calc (1 / q ^ 4) * ∑ v ∈ Rset,
        ∑ S ∈ (Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))), (q - 1) ^ (inKer v S)
      ≤ (1 / q ^ 4) * ∑ _v ∈ Rset,
        ∑ _S ∈ (Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))), q ^ (3 * t - t / 3) := by
        gcongr with v hv S hS; exact hper v hv S hS
    _ = (1 / q ^ 4) * ((Rset.card : ℝ) * (((Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))).card : ℝ) *
          q ^ (3 * t - t / 3))) := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (1 / q ^ 4) * (q ^ 4 * ((2 : ℝ) ^ (6 * t) * q ^ (3 * t - t / 3))) := by
        gcongr
    _ = (2 : ℝ) ^ (6 * t) * q ^ (3 * t - t / 3) := by
        field_simp [ne_of_gt hqpos]

lemma validCols_fourier_diff_sum (t m : ℕ) (ht : 1 ≤ t) (hm : 1 ≤ m) :
    let q : ℝ := (2 : ℝ) ^ m
    let modelM : Finset (Fin (6 * t)) → ℝ := fun S =>
      (if S = laneSet 0 then q ^ (3 * t - 2) else 0) +
      (if S = laneSet 1 then q ^ (3 * t - 2) else 0) +
      (q - 1) ^ (runsCard S) / q ^ 4
    (∑ S ∈ (Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))),
        |((validCols (6 * t) m S).card : ℝ) - modelM S|) ≤
      2 * (q ^ (3 * t - 2) * ((3 * (t : ℝ)) / q + 1 / q ^ 2) + q ^ t) +
      2 * (((q + 4) ^ (3 * t) + 4 * (q + 4) ^ (3 * t - 1) - (q - 1) ^ (3 * t)) / q ^ 2 +
        6 * (q + 6) ^ (3 * t) / q ^ 3) +
      (2 : ℝ) ^ (6 * t) * q ^ (3 * t - t / 3) := by
  intro q modelM
  have hq2 : (2 : ℝ) ≤ q := by
    have : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ m := pow_le_pow_right₀ (by norm_num) hm
    simpa [q] using this
  have hqpos : (0 : ℝ) < q := by linarith
  have hlane_ne0 : laneSet (0 : Fin 2) ≠ (Finset.univ : Finset (Fin (6 * t))) := by
    intro h
    have hmem : (⟨1, by omega⟩ : Fin (6 * t)) ∈ laneSet 0 := by rw [h]; exact Finset.mem_univ _
    simp [laneSet] at hmem
  have hlane_ne1 : laneSet (1 : Fin 2) ≠ (Finset.univ : Finset (Fin (6 * t))) := by
    intro h
    have hmem : (⟨0, by omega⟩ : Fin (6 * t)) ∈ laneSet 1 := by rw [h]; exact Finset.mem_univ _
    simp [laneSet] at hmem
  have hlane01 : (laneSet (0 : Fin 2) : Finset (Fin (6 * t))) ≠ laneSet (1 : Fin 2) := by
    intro h
    have hmem : (⟨0, by omega⟩ : Fin (6 * t)) ∈ (laneSet (1 : Fin 2) : Finset (Fin (6 * t))) := by
      rw [← h]; simp [laneSet]
    simp [laneSet] at hmem
  let Eset : Finset (Fin 4 → Fin m → F2) :=
    Finset.univ.filter (fun v => v ≠ 0 ∧ v 0 = 0 ∧ v 1 = 0)
  let Oset : Finset (Fin 4 → Fin m → F2) :=
    Finset.univ.filter (fun v => v ≠ 0 ∧ v 2 = 0 ∧ v 3 = 0)
  let Rset : Finset (Fin 4 → Fin m → F2) :=
    Finset.univ.filter (fun v => (v 0 ≠ 0 ∨ v 1 ≠ 0) ∧ (v 2 ≠ 0 ∨ v 3 ≠ 0))
  have hpartV : ∀ f : (Fin 4 → Fin m → F2) → ℝ,
      (∑ v : Fin 4 → Fin m → F2, f v) =
        f 0 + (∑ v ∈ Eset, f v) + (∑ v ∈ Oset, f v) + (∑ v ∈ Rset, f v) := by
    intro f
    have hd0E : Disjoint ({0} : Finset (Fin 4 → Fin m → F2)) Eset := by
      simp [Eset]
    have hd0O : Disjoint ({0} : Finset (Fin 4 → Fin m → F2)) Oset := by
      simp [Oset]
    have hd0R : Disjoint ({0} : Finset (Fin 4 → Fin m → F2)) Rset := by
      simp [Rset]
    have hdEO : Disjoint Eset Oset := by
      rw [Finset.disjoint_left]
      intro v hE hO
      simp only [Eset, Oset, Finset.mem_filter, Finset.mem_univ, true_and] at hE hO
      apply hE.1; ext b j; fin_cases b <;> simp [hE.2.1, hE.2.2, hO.2.1, hO.2.2]
    have hdER : Disjoint Eset Rset := by
      rw [Finset.disjoint_left]
      intro v hE hR
      simp only [Eset, Rset, Finset.mem_filter, Finset.mem_univ, true_and] at hE hR
      rcases hR.1 with h | h
      · exact h hE.2.1
      · exact h hE.2.2
    have hdOR : Disjoint Oset Rset := by
      rw [Finset.disjoint_left]
      intro v hO hR
      simp only [Oset, Rset, Finset.mem_filter, Finset.mem_univ, true_and] at hO hR
      rcases hR.2 with h | h
      · exact h hO.2.1
      · exact h hO.2.2
    have huniv : ({0} : Finset (Fin 4 → Fin m → F2)) ∪ Eset ∪ Oset ∪ Rset = Finset.univ := by
      ext v
      simp only [Finset.mem_union, Finset.mem_singleton, Eset, Oset, Rset, Finset.mem_filter,
        Finset.mem_univ, true_and, iff_true]
      by_cases h0 : v = 0
      · exact Or.inl (Or.inl (Or.inl h0))
      · by_cases hE : v 0 = 0 ∧ v 1 = 0
        · exact Or.inl (Or.inl (Or.inr ⟨h0, hE⟩))
        · by_cases hO : v 2 = 0 ∧ v 3 = 0
          · exact Or.inl (Or.inr ⟨h0, hO⟩)
          · rw [not_and_or] at hE hO
            exact Or.inr ⟨hE, hO⟩
    rw [← huniv,
      Finset.sum_union (Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨hd0R, hdER⟩, hdOR⟩),
      Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hd0O, hdEO⟩),
      Finset.sum_union hd0E, Finset.sum_singleton]
  let FT : (Fin 4 → Fin m → F2) → Finset (Fin (6 * t)) → ℝ := fun v S =>
    ∏ e ∈ endsSet S,
      if (∑ b : Fin 4, runParity S e b • v b) = 0 then (q - 1) else (-1 : ℝ)
  have hFT0 : ∀ S, FT 0 S = (q - 1) ^ (runsCard S) := by
    intro S; simp [FT, runsCard]
  have hFT_abs : ∀ v S, |FT v S| = (q - 1) ^ (inKer v S) :=
    fun v S => abs_fourier_term_eq (6 * t) m hm v S
  -- Lane 0 and Lane 1 exact bounds
  have hlane_err : ∀ shift : Fin 2,
      |((validCols (6 * t) m (laneSet shift)).card : ℝ) - modelM (laneSet shift)| ≤
        q ^ (3 * t - 2) * ((3 * (t : ℝ)) / q + 1 / q ^ 2) + q ^ t := by
    intro shift
    have hne : (laneSet shift : Finset (Fin (6 * t))) ≠ Finset.univ := by
      rcases fin2_cases shift with rfl | rfl
      · exact hlane_ne0
      · exact hlane_ne1
    rw [validCols_card_eq_fourier (6 * t) m (laneSet shift) hne]
    change |(1 / q ^ 4) * (∑ v : Fin 4 → Fin m → F2, FT v (laneSet shift)) - modelM (laneSet shift)| ≤ _
    have hends : endsSet (laneSet shift : Finset (Fin (6 * t))) = laneSet shift := by
      ext i
      simp only [endsSet, laneSet, Finset.mem_filter, Finset.mem_univ, true_and, and_iff_left_iff_imp]
      intro hi; simp only [nextIdx]
      rw [Nat.mod_mod_of_dvd _ ⟨3 * t, by ring⟩]; omega
    have hruns : runsCard (laneSet shift : Finset (Fin (6 * t))) = 3 * t := by
      rw [runsCard, hends]
      let eL : Fin (3 * t) ≃ {i : Fin (6 * t) // i ∈ laneSet shift} :=
        { toFun := fun j => ⟨⟨2 * j.val + shift.val, by omega⟩, by simp [laneSet]; omega⟩
          invFun := fun i => ⟨i.1.val / 2, by omega⟩
          left_inv := fun j => by ext; simp; omega
          right_inv := fun ⟨i, hi⟩ => by
            have hpar : i.val % 2 = shift.val := (Finset.mem_filter.mp hi).2
            ext; simp; omega }
      rw [← Fintype.card_coe, ← Fintype.card_congr eL, Fintype.card_fin]
    have hpar_lane : ∀ i ∈ (laneSet shift : Finset (Fin (6 * t))), ∀ b,
        runParity (laneSet shift : Finset (Fin (6 * t))) i b = hMat i b := by
      intro i hi b
      have hprev : prevIdx i ∉ laneSet shift := by
        simp only [laneSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        simp only [prevIdx]
        rw [Nat.mod_mod_of_dvd _ ⟨3 * t, by ring⟩]; omega
      have hsing := runEnd_singleton (laneSet shift) hne i (by rw [hends]; exact hi) hprev
      simp [runParity, hsing]
    let mainV := Finset.univ.filter (fun v : Fin 4 → Fin m → F2 =>
      if shift = 0 then (v 0 = 0 ∧ v 1 = 0) else (v 2 = 0 ∧ v 3 = 0))
    let restV := Finset.univ.filter (fun v : Fin 4 → Fin m → F2 =>
      ¬ (if shift = 0 then (v 0 = 0 ∧ v 1 = 0) else (v 2 = 0 ∧ v 3 = 0)))
    have hsplitV : (∑ v : Fin 4 → Fin m → F2, FT v (laneSet shift)) =
        (∑ v ∈ mainV, FT v (laneSet shift)) + (∑ v ∈ restV, FT v (laneSet shift)) :=
      (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun v : Fin 4 → Fin m → F2 => if shift = 0 then (v 0 = 0 ∧ v 1 = 0) else (v 2 = 0 ∧ v 3 = 0))
        (fun v => FT v (laneSet shift))).symm
    have hmain_val : (∑ v ∈ mainV, FT v (laneSet shift)) = q ^ 2 * (q - 1) ^ (3 * t) := by
      have hconst : ∀ v ∈ mainV, FT v (laneSet shift) = (q - 1) ^ (3 * t) := by
        intro v hv
        simp only [mainV, Finset.mem_filter, Finset.mem_univ, true_and] at hv
        dsimp only [FT]
        have hzero : ∀ e ∈ endsSet (laneSet shift : Finset (Fin (6 * t))),
            (∑ b : Fin 4, runParity (laneSet shift : Finset (Fin (6 * t))) e b • v b) = 0 := by
          intro e he
          have heL : e ∈ (laneSet shift : Finset (Fin (6 * t))) := by rw [← hends]; exact he
          simp_rw [hpar_lane e heL]
          rw [hMat_eval_sum]
          have hpar := (Finset.mem_filter.mp heL).2
          rcases fin2_cases shift with rfl | rfl
          · simp only [Fin.val_zero, ↓reduceIte] at hpar hv ⊢
            rw [if_pos hpar]; split_ifs <;> simp [hv.1, hv.2]
          · have h10 : (1 : Fin 2) ≠ 0 := by decide
            simp only [Fin.val_one, h10, ↓reduceIte] at hpar hv ⊢
            rw [if_neg (by omega : e.val % 2 ≠ 0)]; split_ifs <;> simp [hv.1, hv.2]
        have hprod : (∏ e ∈ endsSet (laneSet shift : Finset (Fin (6 * t))),
            if (∑ b : Fin 4, runParity (laneSet shift : Finset (Fin (6 * t))) e b • v b) = 0 then (q - 1) else (-1 : ℝ)) =
            ∏ _e ∈ endsSet (laneSet shift : Finset (Fin (6 * t))), (q - 1) :=
          Finset.prod_congr rfl (fun e he => by rw [if_pos (hzero e he)])
        rw [hprod, Finset.prod_const, ← runsCard, hruns]
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
      have hcard_main : mainV.card = (2 ^ m) ^ 2 := by
        have hcard_bij : mainV.card = (Finset.univ : Finset ((Fin m → F2) × (Fin m → F2))).card := by
          refine Finset.card_bij
            (fun v _ => if shift = 0 then (v 2, v 3) else (v 0, v 1)) ?_ ?_ ?_
          · intro _ _; exact Finset.mem_univ _
          · intro v₁ hv₁ v₂ hv₂ heq
            simp only [mainV, Finset.mem_filter, Finset.mem_univ, true_and] at hv₁ hv₂
            rcases fin2_cases shift with rfl | rfl
            · simp only [↓reduceIte, Prod.mk.injEq] at hv₁ hv₂ heq
              ext b j; fin_cases b <;> dsimp only
              · simp [hv₁.1, hv₂.1]
              · simp [hv₁.2, hv₂.2]
              · exact congrFun heq.1 j
              · exact congrFun heq.2 j
            · have h10 : (1 : Fin 2) ≠ 0 := by decide
              simp only [h10, ↓reduceIte, Prod.mk.injEq] at hv₁ hv₂ heq
              ext b j; fin_cases b <;> dsimp only
              · exact congrFun heq.1 j
              · exact congrFun heq.2 j
              · simp [hv₁.1, hv₂.1]
              · simp [hv₁.2, hv₂.2]
          · intro ⟨u1, u2⟩ _
            rcases fin2_cases shift with rfl | rfl
            · refine ⟨fun b => if b = 2 then u1 else if b = 3 then u2 else 0, by simp [mainV], by simp⟩
            · have h10 : (1 : Fin 2) ≠ 0 := by decide
              refine ⟨fun b => if b = 0 then u1 else if b = 1 then u2 else 0,
                by simp [mainV, h10], by simp [h10]⟩
        rw [hcard_bij]
        simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_pi, Fintype.card_fin, ZMod.card,
          Finset.prod_const, sq]
      have hcast : (mainV.card : ℝ) = q ^ 2 := by rw [hcard_main]; push_cast; rfl
      rw [hcast]
    have hrest_le : |(1 / q ^ 4) * ∑ v ∈ restV, FT v (laneSet shift)| ≤ q ^ t := by
      have hcard_rest : (restV.card : ℝ) ≤ q ^ 4 := by
        have h1 : restV.card ≤ Fintype.card (Fin 4 → Fin m → F2) := Finset.card_le_univ _
        have h2 : Fintype.card (Fin 4 → Fin m → F2) = (2 ^ m) ^ 4 := by
          simp [Fintype.card_pi, ZMod.card]
        rw [h2] at h1
        have h1r : (restV.card : ℝ) ≤ ((2 : ℝ) ^ m) ^ 4 := by exact_mod_cast h1
        exact h1r
      have hper : ∀ v ∈ restV, |FT v (laneSet shift)| ≤ q ^ t := by
        intro v hv
        rw [hFT_abs]
        simp only [restV, Finset.mem_filter, Finset.mem_univ, true_and] at hv
        have hneV : if shift = 0 then (v 0 ≠ 0 ∨ v 1 ≠ 0) else (v 2 ≠ 0 ∨ v 3 ≠ 0) := by
          rcases fin2_cases shift with rfl | rfl
          · simp only [↓reduceIte, not_and_or] at hv ⊢; exact hv
          · have h10 : (1 : Fin 2) ≠ 0 := by decide
            simp only [h10, ↓reduceIte, not_and_or] at hv ⊢; exact hv
        have hle := inKer_lane_le t m ht v shift hneV
        calc (q - 1) ^ inKer v (laneSet shift)
            ≤ q ^ inKer v (laneSet shift) := pow_le_pow_left₀ (by linarith) (by linarith) _
          _ ≤ q ^ t := pow_le_pow_right₀ (by linarith) hle
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / q ^ 4)]
      calc (1 / q ^ 4) * |∑ v ∈ restV, FT v (laneSet shift)|
          ≤ (1 / q ^ 4) * ∑ v ∈ restV, |FT v (laneSet shift)| := by
            gcongr; exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ (1 / q ^ 4) * ∑ _v ∈ restV, q ^ t := by
            gcongr with v hv; exact hper v hv
        _ = (1 / q ^ 4) * ((restV.card : ℝ) * q ^ t) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (1 / q ^ 4) * (q ^ 4 * q ^ t) := by gcongr
        _ = q ^ t := by field_simp [ne_of_gt hqpos]
    have hmod_val : modelM (laneSet shift) = q ^ (3 * t - 2) + (q - 1) ^ (3 * t) / q ^ 4 := by
      dsimp only [modelM]
      rw [hruns]
      rcases fin2_cases shift with rfl | rfl
      · simp [hlane01]
      · simp [hlane01.symm]
    rw [hsplitV, hmain_val, mul_add, hmod_val]
    have hpow_diff : q ^ (3 * t) - (q - 1) ^ (3 * t) ≤ (3 * (t : ℝ)) * q ^ (3 * t - 1) := by
      have hgen : ∀ k : ℕ, 1 ≤ k → q ^ k - (q - 1) ^ k ≤ (k : ℝ) * q ^ (k - 1) := by
        intro k hk
        induction k with
        | zero => omega
        | succ k ih =>
          cases k with
          | zero => simp
          | succ k =>
            have hih := ih (by omega)
            have h1 : q ^ (k + 2) - (q - 1) ^ (k + 2) =
                q * (q ^ (k + 1) - (q - 1) ^ (k + 1)) + (q - 1) ^ (k + 1) := by ring
            have h2 : (q - 1) ^ (k + 1) ≤ q ^ (k + 1) :=
              pow_le_pow_left₀ (by linarith) (by linarith) (k + 1)
            have h3 : q * ((k + 1 : ℕ) * q ^ k) = (k + 1 : ℕ) * q ^ (k + 1) := by
              rw [pow_succ']; ring
            have h4 : (k + 1 : ℕ) * q ^ (k + 1) + q ^ (k + 1) = ((k + 2 : ℕ) : ℝ) * q ^ (k + 1) := by
              push_cast; ring
            simp only [Nat.add_sub_cancel] at hih ⊢
            nlinarith
      have h := hgen (3 * t) (by omega)
      push_cast at h
      exact h
    have hpow_le : (q - 1) ^ (3 * t) ≤ q ^ (3 * t) :=
      pow_le_pow_left₀ (by linarith) (by linarith) (3 * t)
    have hpow_eq1 : q ^ (3 * t - 2) * q ^ 2 = q ^ (3 * t) := by
      rw [← pow_add]; congr 1; omega
    have hpow_eq2 : q ^ (3 * t - 2) * q = q ^ (3 * t - 1) := by
      rw [← pow_succ]; congr 1; omega
    have hmain_diff : |(1 / q ^ 4) * (q ^ 2 * (q - 1) ^ (3 * t)) -
        (q ^ (3 * t - 2) + (q - 1) ^ (3 * t) / q ^ 4)| ≤
        q ^ (3 * t - 2) * ((3 * (t : ℝ)) / q + 1 / q ^ 2) := by
      have h1 : (1 / q ^ 4) * (q ^ 2 * (q - 1) ^ (3 * t)) = (q - 1) ^ (3 * t) / q ^ 2 := by
        field_simp [ne_of_gt hqpos]
      rw [h1]
      have hneg : (q - 1) ^ (3 * t) / q ^ 2 - (q ^ (3 * t - 2) + (q - 1) ^ (3 * t) / q ^ 4) ≤ 0 := by
        have hle1 : (q - 1) ^ (3 * t) / q ^ 2 ≤ q ^ (3 * t - 2) := by
          rw [div_le_iff₀ (by positivity : (0 : ℝ) < q ^ 2), hpow_eq1]; exact hpow_le
        have hnn2 : 0 ≤ (q - 1) ^ (3 * t) / q ^ 4 :=
          div_nonneg (pow_nonneg (by linarith only [hq2]) _) (by positivity)
        linarith
      rw [abs_of_nonpos hneg]
      have hpart1 : q ^ (3 * t - 2) - (q - 1) ^ (3 * t) / q ^ 2 ≤ q ^ (3 * t - 2) * ((3 * (t : ℝ)) / q) := by
        have h := div_le_div_of_nonneg_right hpow_diff (by positivity : (0 : ℝ) ≤ q ^ 2)
        have hL : (q ^ (3 * t) - (q - 1) ^ (3 * t)) / q ^ 2 =
            q ^ (3 * t - 2) - (q - 1) ^ (3 * t) / q ^ 2 := by
          rw [← hpow_eq1]; field_simp [ne_of_gt hqpos]
        have hR : (3 * (t : ℝ) * q ^ (3 * t - 1)) / q ^ 2 = q ^ (3 * t - 2) * ((3 * (t : ℝ)) / q) := by
          rw [← hpow_eq2]; field_simp [ne_of_gt hqpos]
        linarith
      have hpart2 : (q - 1) ^ (3 * t) / q ^ 4 ≤ q ^ (3 * t - 2) * (1 / q ^ 2) := by
        have h := div_le_div_of_nonneg_right hpow_le (by positivity : (0 : ℝ) ≤ q ^ 4)
        have hR : q ^ (3 * t) / q ^ 4 = q ^ (3 * t - 2) * (1 / q ^ 2) := by
          rw [← hpow_eq1]; field_simp [ne_of_gt hqpos]
        linarith
      linarith
    have htri := abs_add_le
      ((1 / q ^ 4) * (q ^ 2 * (q - 1) ^ (3 * t)) - (q ^ (3 * t - 2) + (q - 1) ^ (3 * t) / q ^ 4))
      ((1 / q ^ 4) * ∑ v ∈ restV, FT v (laneSet shift))
    have hrew : (1 / q ^ 4) * (q ^ 2 * (q - 1) ^ (3 * t)) + (1 / q ^ 4) * ∑ v ∈ restV, FT v (laneSet shift) -
        (q ^ (3 * t - 2) + (q - 1) ^ (3 * t) / q ^ 4) =
        ((1 / q ^ 4) * (q ^ 2 * (q - 1) ^ (3 * t)) - (q ^ (3 * t - 2) + (q - 1) ^ (3 * t) / q ^ 4)) +
        (1 / q ^ 4) * ∑ v ∈ restV, FT v (laneSet shift) := by ring
    rw [hrew]
    linarith
  -- Split the sum over S into lane 0, lane 1, and the rest Srest
  let SnonU := Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))
  let Srest := (SnonU.erase (laneSet 0)).erase (laneSet 1)
  have hS_split :
      (∑ S ∈ SnonU, |((validCols (6 * t) m S).card : ℝ) - modelM S|) =
        |((validCols (6 * t) m (laneSet 0)).card : ℝ) - modelM (laneSet 0)| +
        |((validCols (6 * t) m (laneSet 1)).card : ℝ) - modelM (laneSet 1)| +
        ∑ S ∈ Srest, |((validCols (6 * t) m S).card : ℝ) - modelM S| := by
    have hmem0 : laneSet 0 ∈ SnonU := Finset.mem_erase.mpr ⟨hlane_ne0, Finset.mem_univ _⟩
    have hmem1 : laneSet 1 ∈ SnonU.erase (laneSet 0) :=
      Finset.mem_erase.mpr ⟨hlane01.symm, Finset.mem_erase.mpr ⟨hlane_ne1, Finset.mem_univ _⟩⟩
    rw [← Finset.add_sum_erase SnonU _ hmem0,
      ← Finset.add_sum_erase (SnonU.erase (laneSet 0)) _ hmem1, add_assoc]
  rw [hS_split]
  -- Bound Srest using Eset, Oset, Rset
  have hrest_per : ∀ S ∈ Srest,
      |((validCols (6 * t) m S).card : ℝ) - modelM S| ≤
        (1 / q ^ 4) * (∑ v ∈ Eset, (q - 1) ^ inKer v S) +
        (1 / q ^ 4) * (∑ v ∈ Oset, (q - 1) ^ inKer v S) +
        (1 / q ^ 4) * (∑ v ∈ Rset, (q - 1) ^ inKer v S) := by
    intro S hS
    have hne1 : S ≠ laneSet 1 := (Finset.mem_erase.mp hS).1
    have hS1 := (Finset.mem_erase.mp hS).2
    have hne0 : S ≠ laneSet 0 := (Finset.mem_erase.mp hS1).1
    have hneU : S ≠ Finset.univ := (Finset.mem_erase.mp (Finset.mem_erase.mp hS1).2).1
    rw [validCols_card_eq_fourier (6 * t) m S hneU]
    change |(1 / q ^ 4) * (∑ v : Fin 4 → Fin m → F2, FT v S) - modelM S| ≤ _
    rw [hpartV (fun v => FT v S), hFT0 S]
    have hmod : modelM S = (1 / q ^ 4) * (q - 1) ^ (runsCard S) := by
      simp [modelM, hne0, hne1]; ring
    rw [hmod]
    have hsimp : (1 / q ^ 4) * ((q - 1) ^ runsCard S + (∑ v ∈ Eset, FT v S) + (∑ v ∈ Oset, FT v S) +
          (∑ v ∈ Rset, FT v S)) - (1 / q ^ 4) * (q - 1) ^ runsCard S =
        (1 / q ^ 4) * ((∑ v ∈ Eset, FT v S) + (∑ v ∈ Oset, FT v S) + (∑ v ∈ Rset, FT v S)) := by ring
    rw [hsimp, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / q ^ 4)]
    have h1 := abs_add_le ((∑ v ∈ Eset, FT v S) + (∑ v ∈ Oset, FT v S)) (∑ v ∈ Rset, FT v S)
    have h2 := abs_add_le (∑ v ∈ Eset, FT v S) (∑ v ∈ Oset, FT v S)
    have hE : |∑ v ∈ Eset, FT v S| ≤ ∑ v ∈ Eset, (q - 1) ^ inKer v S := by
      calc |∑ v ∈ Eset, FT v S| ≤ ∑ v ∈ Eset, |FT v S| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ v ∈ Eset, (q - 1) ^ inKer v S := Finset.sum_congr rfl (fun v _ => hFT_abs v S)
    have hO : |∑ v ∈ Oset, FT v S| ≤ ∑ v ∈ Oset, (q - 1) ^ inKer v S := by
      calc |∑ v ∈ Oset, FT v S| ≤ ∑ v ∈ Oset, |FT v S| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ v ∈ Oset, (q - 1) ^ inKer v S := Finset.sum_congr rfl (fun v _ => hFT_abs v S)
    have hR : |∑ v ∈ Rset, FT v S| ≤ ∑ v ∈ Rset, (q - 1) ^ inKer v S := by
      calc |∑ v ∈ Rset, FT v S| ≤ ∑ v ∈ Rset, |FT v S| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ v ∈ Rset, (q - 1) ^ inKer v S := Finset.sum_congr rfl (fun v _ => hFT_abs v S)
    have hq4pos : (0 : ℝ) ≤ 1 / q ^ 4 := by positivity
    nlinarith
  have hSrest_sum :
      (∑ S ∈ Srest, |((validCols (6 * t) m S).card : ℝ) - modelM S|) ≤
        2 * (((q + 4) ^ (3 * t) + 4 * (q + 4) ^ (3 * t - 1) - (q - 1) ^ (3 * t)) / q ^ 2 +
          6 * (q + 6) ^ (3 * t) / q ^ 3) +
        (2 : ℝ) ^ (6 * t) * q ^ (3 * t - t / 3) := by
    calc ∑ S ∈ Srest, |((validCols (6 * t) m S).card : ℝ) - modelM S|
        ≤ ∑ S ∈ Srest, ((1 / q ^ 4) * (∑ v ∈ Eset, (q - 1) ^ inKer v S) +
            (1 / q ^ 4) * (∑ v ∈ Oset, (q - 1) ^ inKer v S) +
            (1 / q ^ 4) * (∑ v ∈ Rset, (q - 1) ^ inKer v S)) :=
          Finset.sum_le_sum hrest_per
      _ = (1 / q ^ 4) * (∑ v ∈ Eset, ∑ S ∈ Srest, (q - 1) ^ inKer v S) +
          (1 / q ^ 4) * (∑ v ∈ Oset, ∑ S ∈ Srest, (q - 1) ^ inKer v S) +
          (1 / q ^ 4) * (∑ v ∈ Rset, ∑ S ∈ Srest, (q - 1) ^ inKer v S) := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
          congr 1; congr 1
          · congr 1; exact Finset.sum_comm
          · congr 1; exact Finset.sum_comm
          · congr 1; exact Finset.sum_comm
      _ ≤ (((q + 4) ^ (3 * t) + 4 * (q + 4) ^ (3 * t - 1) - (q - 1) ^ (3 * t)) / q ^ 2 +
            6 * (q + 6) ^ (3 * t) / q ^ 3) +
          (((q + 4) ^ (3 * t) + 4 * (q + 4) ^ (3 * t - 1) - (q - 1) ^ (3 * t)) / q ^ 2 +
            6 * (q + 6) ^ (3 * t) / q ^ 3) +
          (2 : ℝ) ^ (6 * t) * q ^ (3 * t - t / 3) := by
          have hsub0 : Srest ⊆ SnonU.erase (laneSet 0) := Finset.erase_subset _ _
          have hsub1 : Srest ⊆ SnonU.erase (laneSet 1) := by
            intro S hS
            exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hS).1,
              (Finset.mem_erase.mp (Finset.mem_erase.mp hS).2).2⟩
          have hsubU : Srest ⊆ SnonU := subset_trans hsub0 (Finset.erase_subset _ _)
          have hE0 := sum_bucket_E_or_O_nonlane t m ht hm 0
          have hO1 := sum_bucket_E_or_O_nonlane t m ht hm 1
          have hR0 := sum_bucket_R t m ht hm
          have hq1_nn : (0 : ℝ) ≤ q - 1 := by linarith only [hq2]
          have hE_le : (1 / q ^ 4) * (∑ v ∈ Eset, ∑ S ∈ Srest, (q - 1) ^ inKer v S) ≤
              (1 / q ^ 4) * (∑ v ∈ Eset, ∑ S ∈ SnonU.erase (laneSet 0), (q - 1) ^ inKer v S) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun v _ =>
              Finset.sum_le_sum_of_subset_of_nonneg hsub0 (fun _ _ _ => pow_nonneg hq1_nn _)) (by positivity)
          have hO_le : (1 / q ^ 4) * (∑ v ∈ Oset, ∑ S ∈ Srest, (q - 1) ^ inKer v S) ≤
              (1 / q ^ 4) * (∑ v ∈ Oset, ∑ S ∈ SnonU.erase (laneSet 1), (q - 1) ^ inKer v S) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun v _ =>
              Finset.sum_le_sum_of_subset_of_nonneg hsub1 (fun _ _ _ => pow_nonneg hq1_nn _)) (by positivity)
          have hR_le : (1 / q ^ 4) * (∑ v ∈ Rset, ∑ S ∈ Srest, (q - 1) ^ inKer v S) ≤
              (1 / q ^ 4) * (∑ v ∈ Rset, ∑ S ∈ SnonU, (q - 1) ^ inKer v S) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun v _ =>
              Finset.sum_le_sum_of_subset_of_nonneg hsubU (fun _ _ _ => pow_nonneg hq1_nn _)) (by positivity)
          simp only [↓reduceIte] at hE0
          have h10 : (1 : Fin 2) ≠ 0 := by decide
          simp only [h10, ↓reduceIte] at hO1
          linarith only [hE_le, hO_le, hR_le, hE0, hO1, hR0]
      _ = _ := by ring
  have h0 := hlane_err 0
  have h1 := hlane_err 1
  linarith

-- Section 6: Elementary analytic inequalities and final asymptotic ratio bound

lemma pow_one_add_le_two {x : ℝ} {k : ℕ} (hx : 0 ≤ x) (hkx : (k : ℝ) * x ≤ 1 / 2) :
    (1 + x) ^ k ≤ 2 := by
  cases k with
  | zero => norm_num
  | succ k =>
    have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
    have hx1 : x ≤ 1 / 2 := by nlinarith
    have hsub_pos : (0 : ℝ) < 1 - x := by linarith
    have hinv : 1 + x ≤ 1 / (1 - x) := by
      rw [le_div_iff₀ hsub_pos]
      nlinarith [sq_nonneg x]
    have hpow1 : (1 + x) ^ (k + 1) ≤ 1 / (1 - x) ^ (k + 1) := by
      calc (1 + x) ^ (k + 1) ≤ (1 / (1 - x)) ^ (k + 1) :=
            pow_le_pow_left₀ (by linarith) hinv (k + 1)
        _ = 1 / (1 - x) ^ (k + 1) := by rw [div_pow, one_pow]
    have hbern : 1 - ((k + 1 : ℕ) : ℝ) * x ≤ (1 - x) ^ (k + 1) := by
      have h := one_add_mul_le_pow (a := -x) (by linarith) (k + 1)
      have h1 : 1 + -x = 1 - x := by ring
      rw [h1] at h
      linarith
    have hhalf : (1 / 2 : ℝ) ≤ (1 - x) ^ (k + 1) := by linarith
    have hpow2 : 1 / (1 - x) ^ (k + 1) ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    exact le_trans hpow1 hpow2

lemma sqrt_ratio_le_five_sixths {s : ℝ} (hs : 64 ≤ s) :
    (1 + Real.sqrt (s / 2 - 1)) / (1 + Real.sqrt (s - 1)) ≤ 5 / 6 := by
  have hden : 0 < 1 + Real.sqrt (s - 1) := by
    have : 0 ≤ Real.sqrt (s - 1) := Real.sqrt_nonneg _
    linarith
  rw [div_le_iff₀ hden]
  have hr1 : 0 ≤ Real.sqrt (s / 2 - 1) := Real.sqrt_nonneg _
  have hr2 : 0 ≤ Real.sqrt (s - 1) := Real.sqrt_nonneg _
  have hsq1 : Real.sqrt (s / 2 - 1) ^ 2 = s / 2 - 1 := Real.sq_sqrt (by linarith)
  have hsq2 : Real.sqrt (s - 1) ^ 2 = s - 1 := Real.sq_sqrt (by linarith)
  have hr1_le : Real.sqrt (s / 2 - 1) ≤ s / 4 := by
    nlinarith [sq_nonneg (s / 4 - Real.sqrt (s / 2 - 1)), hsq1]
  have hgoal_sq : (1 + 6 * Real.sqrt (s / 2 - 1)) ^ 2 ≤ (5 * Real.sqrt (s - 1)) ^ 2 := by
    nlinarith [hsq1, hsq2, hr1_le]
  have hgoal : 1 + 6 * Real.sqrt (s / 2 - 1) ≤ 5 * Real.sqrt (s - 1) := by
    nlinarith [hr1, hr2, hgoal_sq]
  linarith

lemma main_partA_bound (t d : ℕ) (ht : 10 ≤ t) (hd : 40 ≤ d)
    (hds : 6 * (t : ℝ) ≤ (2 : ℝ) ^ d / 100) (hdt : 12 * d ≤ t) :
    let s : ℝ := (2 : ℝ) ^ d
    let model : Finset (Fin (6 * t)) → ℝ := fun S =>
      (if S = laneSet 0 then s ^ (3 * t - 2) else 0) +
      (if S = laneSet 1 then s ^ (3 * t - 2) else 0) +
      (s - 1) ^ (runsCard S) / s ^ 4
    let SnonU := Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))
    (∑ S ∈ SnonU, |((validCols (6 * t) d S).card : ℝ) - model S|) ≤
      2 * s ^ (3 * t - 2) * (20 * ((6 * (t : ℝ)) / s) + 25 / s + ((1 : ℝ) / 2) ^ t) := by
  intro s model SnonU
  have hs64 : (64 : ℝ) ≤ s := by
    calc (64 : ℝ) = (2 : ℝ) ^ 6 := by norm_num
      _ ≤ (2 : ℝ) ^ d := pow_le_pow_right₀ (by norm_num) (by omega)
  have hspos : (0 : ℝ) < s := by linarith only [hs64]
  have hfd_d : (∑ S ∈ SnonU, |((validCols (6 * t) d S).card : ℝ) - model S|) ≤
      2 * (s ^ (3 * t - 2) * ((3 * (t : ℝ)) / s + 1 / s ^ 2) + s ^ t) +
      2 * (((s + 4) ^ (3 * t) + 4 * (s + 4) ^ (3 * t - 1) - (s - 1) ^ (3 * t)) / s ^ 2 +
        6 * (s + 6) ^ (3 * t) / s ^ 3) +
      (2 : ℝ) ^ (6 * t) * s ^ (3 * t - t / 3) :=
    validCols_fourier_diff_sum t d (by omega) (by omega)
  have hpow_1add4 : (s + 4) ^ (3 * t) ≤ 2 * s ^ (3 * t) := by
    have h1 : (1 + 4 / s) ^ (3 * t) ≤ 2 :=
      pow_one_add_le_two (by positivity) (by
        have h : ((3 * t : ℕ) : ℝ) * (4 / s) = 2 * (6 * (t : ℝ)) / s := by push_cast; ring
        rw [h, div_le_iff₀ hspos]; linarith only [hds])
    have h2 : (s + 4) ^ (3 * t) = s ^ (3 * t) * (1 + 4 / s) ^ (3 * t) := by
      rw [← mul_pow]; congr 1; field_simp [ne_of_gt hspos]
    rw [h2]; nlinarith only [h1, pow_nonneg (le_of_lt hspos) (3 * t)]
  have hpow_1add6 : (s + 6) ^ (3 * t) ≤ 2 * s ^ (3 * t) := by
    have h1 : (1 + 6 / s) ^ (3 * t) ≤ 2 :=
      pow_one_add_le_two (by positivity) (by
        have h : ((3 * t : ℕ) : ℝ) * (6 / s) = 3 * (6 * (t : ℝ)) / s := by push_cast; ring
        rw [h, div_le_iff₀ hspos]; linarith only [hds])
    have h2 : (s + 6) ^ (3 * t) = s ^ (3 * t) * (1 + 6 / s) ^ (3 * t) := by
      rw [← mul_pow]; congr 1; field_simp [ne_of_gt hspos]
    rw [h2]; nlinarith only [h1, pow_nonneg (le_of_lt hspos) (3 * t)]
  have hdiff_s4 : (s + 4) ^ (3 * t) - (s - 1) ^ (3 * t) ≤ (15 * (t : ℝ)) * (s + 4) ^ (3 * t - 1) := by
    have hgen : ∀ k : ℕ, 1 ≤ k → (s + 4) ^ k - (s - 1) ^ k ≤ 5 * (k : ℝ) * (s + 4) ^ (k - 1) := by
      intro k hk
      induction k with
      | zero => omega
      | succ k ih =>
        cases k with
        | zero => simp; linarith only [hspos]
        | succ k =>
          have hih := ih (by omega)
          have h1 : (s + 4) ^ (k + 2) - (s - 1) ^ (k + 2) =
              (s + 4) * ((s + 4) ^ (k + 1) - (s - 1) ^ (k + 1)) + 5 * (s - 1) ^ (k + 1) := by ring
          have h2 : (s - 1) ^ (k + 1) ≤ (s + 4) ^ (k + 1) :=
            pow_le_pow_left₀ (by linarith only [hs64]) (by linarith only [hs64]) (k + 1)
          have h3 : (s + 4) * (5 * ((k + 1 : ℕ) : ℝ) * (s + 4) ^ k) =
              5 * ((k + 1 : ℕ) : ℝ) * (s + 4) ^ (k + 1) := by rw [pow_succ']; ring
          have h4 : 5 * ((k + 1 : ℕ) : ℝ) * (s + 4) ^ (k + 1) + 5 * (s + 4) ^ (k + 1) =
              5 * ((k + 2 : ℕ) : ℝ) * (s + 4) ^ (k + 1) := by push_cast; ring
          simp only [Nat.add_sub_cancel] at hih ⊢
          have hs4_nn : (0 : ℝ) ≤ s + 4 := by linarith only [hs64]
          have hm := mul_le_mul_of_nonneg_left hih hs4_nn
          linarith only [h1, h2, h3, h4, hm]
    have h := hgen (3 * t) (by omega)
    have hcast : 5 * ((3 * t : ℕ) : ℝ) = 15 * (t : ℝ) := by push_cast; ring
    rw [hcast] at h
    exact h
  have hpow_1add4_m1 : (s + 4) ^ (3 * t - 1) ≤ 2 * s ^ (3 * t - 1) := by
    have h1 : (s + 4) ^ (3 * t - 1) * (s + 4) = (s + 4) ^ (3 * t) := by
      rw [← pow_succ]; congr 1; omega
    have h2 : s ^ (3 * t - 1) * s = s ^ (3 * t) := by
      rw [← pow_succ]; congr 1; omega
    have hnn : 0 ≤ (s + 4) ^ (3 * t - 1) := by positivity
    nlinarith only [hpow_1add4, h1, h2, hnn, hspos]
  have hpow_eq_s2 : s ^ (3 * t - 2) * s ^ 2 = s ^ (3 * t) := by
    rw [← pow_add]; congr 1; omega
  have hpow_eq_s1 : s ^ (3 * t - 2) * s = s ^ (3 * t - 1) := by
    rw [← pow_succ]; congr 1; omega
  have hterm5 : (2 : ℝ) ^ (6 * t) * s ^ (3 * t - t / 3) ≤
      2 * s ^ (3 * t - 2) * ((1 : ℝ) / 2) ^ t := by
    have hexp : 6 * t + d * (3 * t - t / 3) + t ≤ d * (3 * t - 2) := by
      have h1 : d * (3 * t - 2) - d * (3 * t - t / 3) = d * (t / 3 - 2) := by
        rw [← Nat.mul_sub]; congr 1; omega
      have h2 : d * (t / 3 - 2) ≥ 40 * (t / 3 - 2) := Nat.mul_le_mul_right _ hd
      have h3 : 7 * t ≤ 40 * (t / 3 - 2) := by omega
      omega
    have hpow_nat : (2 : ℝ) ^ (6 * t) * ((2 : ℝ) ^ d) ^ (3 * t - t / 3) * (2 : ℝ) ^ t ≤
        ((2 : ℝ) ^ d) ^ (3 * t - 2) := by
      simp only [← pow_mul, ← pow_add]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have h12 : ((1 : ℝ) / 2) ^ t = ((2 : ℝ) ^ t)⁻¹ := by rw [one_div, inv_pow]
    rw [h12]
    have h2tpos : (0 : ℝ) < (2 : ℝ) ^ t := by positivity
    have hmul := mul_le_mul_of_nonneg_right hpow_nat (by positivity : (0 : ℝ) ≤ ((2 : ℝ) ^ t)⁻¹)
    have hL : (2 : ℝ) ^ (6 * t) * s ^ (3 * t - t / 3) * (2 : ℝ) ^ t * ((2 : ℝ) ^ t)⁻¹ =
        (2 : ℝ) ^ (6 * t) * s ^ (3 * t - t / 3) := by
      dsimp only [s]; field_simp [ne_of_gt h2tpos]
    rw [hL] at hmul
    have hR : s ^ (3 * t - 2) * ((2 : ℝ) ^ t)⁻¹ ≤ 2 * s ^ (3 * t - 2) * ((2 : ℝ) ^ t)⁻¹ := by
      have hnn : 0 ≤ s ^ (3 * t - 2) * ((2 : ℝ) ^ t)⁻¹ := by positivity
      linarith only [hnn]
    exact le_trans hmul hR
  have hterm1 : s ^ t ≤ s ^ (3 * t - 2) * (1 / s) := by
    have h1 : s ^ (3 * t - 2) * (1 / s) = s ^ (3 * t - 3) := by
      have hsub : s ^ (3 * t - 3) * s = s ^ (3 * t - 2) := by rw [← pow_succ]; congr 1; omega
      field_simp [ne_of_gt hspos]; linarith only [hsub]
    rw [h1]
    exact pow_le_pow_right₀ (by linarith only [hs64]) (by omega)
  have hterm2 : 1 / s ^ 2 ≤ 1 / s := by
    rw [div_le_div_iff₀ (by positivity) hspos]
    nlinarith only [hs64]
  have hterm3 : ((s + 4) ^ (3 * t) + 4 * (s + 4) ^ (3 * t - 1) - (s - 1) ^ (3 * t)) / s ^ 2 ≤
      s ^ (3 * t - 2) * (5 * ((6 * (t : ℝ)) / s) + 8 / s) := by
    have h1 : (s + 4) ^ (3 * t) + 4 * (s + 4) ^ (3 * t - 1) - (s - 1) ^ (3 * t) ≤
        (15 * (t : ℝ) + 4) * (2 * s ^ (3 * t - 1)) := by
      have hnn : (0 : ℝ) ≤ 15 * (t : ℝ) + 4 := by positivity
      nlinarith only [hdiff_s4, hpow_1add4_m1, hnn]
    have h2 := div_le_div_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ s ^ 2)
    have hR : ((15 * (t : ℝ) + 4) * (2 * s ^ (3 * t - 1))) / s ^ 2 =
        s ^ (3 * t - 2) * (5 * ((6 * (t : ℝ)) / s) + 8 / s) := by
      rw [← hpow_eq_s1]; field_simp [ne_of_gt hspos]; ring
    linarith only [h2, hR]
  have hterm4 : 6 * (s + 6) ^ (3 * t) / s ^ 3 ≤ s ^ (3 * t - 2) * (12 / s) := by
    have h1 : 6 * (s + 6) ^ (3 * t) ≤ 12 * s ^ (3 * t) := by linarith only [hpow_1add6]
    have h2 := div_le_div_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ s ^ 3)
    have hR : (12 * s ^ (3 * t)) / s ^ 3 = s ^ (3 * t - 2) * (12 / s) := by
      rw [← hpow_eq_s2]; field_simp [ne_of_gt hspos]
    linarith only [h2, hR]
  have h3t : (3 * (t : ℝ)) / s = (1 / 2) * ((6 * (t : ℝ)) / s) := by ring
  have hs_nn : 0 ≤ s ^ (3 * t - 2) := by positivity
  have hterm0 : s ^ (3 * t - 2) * ((3 * (t : ℝ)) / s + 1 / s ^ 2) ≤
      s ^ (3 * t - 2) * ((1 / 2) * ((6 * (t : ℝ)) / s) + 1 / s) :=
    mul_le_mul_of_nonneg_left (by linarith only [h3t, hterm2]) hs_nn
  have hA_nn : 0 ≤ s ^ (3 * t - 2) * ((6 * (t : ℝ)) / s) := by positivity
  have hB_nn : 0 ≤ s ^ (3 * t - 2) * (1 / s) := by positivity
  have hterm3' : ((s + 4) ^ (3 * t) + 4 * (s + 4) ^ (3 * t - 1) - (s - 1) ^ (3 * t)) / s ^ 2 ≤
      5 * (s ^ (3 * t - 2) * ((6 * (t : ℝ)) / s)) + 8 * (s ^ (3 * t - 2) * (1 / s)) := by
    have hr : s ^ (3 * t - 2) * (5 * ((6 * (t : ℝ)) / s) + 8 / s) =
        5 * (s ^ (3 * t - 2) * ((6 * (t : ℝ)) / s)) + 8 * (s ^ (3 * t - 2) * (1 / s)) := by ring
    linarith only [hterm3, hr]
  have hterm4' : 6 * (s + 6) ^ (3 * t) / s ^ 3 ≤ 12 * (s ^ (3 * t - 2) * (1 / s)) := by
    have hr : s ^ (3 * t - 2) * (12 / s) = 12 * (s ^ (3 * t - 2) * (1 / s)) := by ring
    linarith only [hterm4, hr]
  have hterm0' : s ^ (3 * t - 2) * ((3 * (t : ℝ)) / s + 1 / s ^ 2) ≤
      (1 / 2) * (s ^ (3 * t - 2) * ((6 * (t : ℝ)) / s)) + s ^ (3 * t - 2) * (1 / s) := by
    have hr : s ^ (3 * t - 2) * ((1 / 2) * ((6 * (t : ℝ)) / s) + 1 / s) =
        (1 / 2) * (s ^ (3 * t - 2) * ((6 * (t : ℝ)) / s)) + s ^ (3 * t - 2) * (1 / s) := by ring
    linarith only [hterm0, hr]
  have hrhs : 2 * s ^ (3 * t - 2) * (20 * ((6 * (t : ℝ)) / s) + 25 / s + ((1 : ℝ) / 2) ^ t) =
      40 * (s ^ (3 * t - 2) * ((6 * (t : ℝ)) / s)) + 50 * (s ^ (3 * t - 2) * (1 / s)) +
      2 * s ^ (3 * t - 2) * ((1 : ℝ) / 2) ^ t := by ring
  linarith only [hfd_d, hterm0', hterm1, hterm3', hterm4', hterm5, hA_nn, hB_nn, hrhs]

lemma main_partB_bound (t d : ℕ) (ht : 10 ≤ t) (hd : 40 ≤ d)
    (hds : 6 * (t : ℝ) ≤ (2 : ℝ) ^ d / 100) (hdt : 12 * d ≤ t)
    (Z : ℝ) (hZ_pos : 0 < Z)
    (hZ_ge1 : 2 * ((2 : ℝ) ^ d) ^ (3 * t - 2) ≤ Z)
    (hZ_ge2 : (1 + Real.sqrt ((2 : ℝ) ^ d - 1)) ^ (6 * t) / ((2 : ℝ) ^ d) ^ 4 ≤ Z) :
    let s : ℝ := (2 : ℝ) ^ d
    let SnonU := Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))
    s * (∑ S ∈ SnonU, ((validCols (6 * t) (d - 1) S).card : ℝ)) / Z ≤
      250 * ((1 : ℝ) / 2) ^ t := by
  intro s SnonU
  have hs64 : (64 : ℝ) ≤ s := by
    calc (64 : ℝ) = (2 : ℝ) ^ 6 := by norm_num
      _ ≤ (2 : ℝ) ^ d := pow_le_pow_right₀ (by norm_num) (by omega)
  have hspos : (0 : ℝ) < s := by linarith only [hs64]
  let q : ℝ := (2 : ℝ) ^ (d - 1)
  have hq_val : q = s / 2 := by
    have hd1 : d = (d - 1) + 1 := by omega
    dsimp only [s, q]
    conv_rhs => rw [hd1, pow_succ]
    ring
  have hq32 : (32 : ℝ) ≤ q := by linarith only [hs64, hq_val]
  have hqpos : (0 : ℝ) < q := by linarith only [hq32]
  let modelQ : Finset (Fin (6 * t)) → ℝ := fun S =>
    (if S = laneSet 0 then q ^ (3 * t - 2) else 0) +
    (if S = laneSet 1 then q ^ (3 * t - 2) else 0) +
    (q - 1) ^ (runsCard S) / q ^ 4
  have hfd_q : (∑ S ∈ SnonU, |((validCols (6 * t) (d - 1) S).card : ℝ) - modelQ S|) ≤
      2 * (q ^ (3 * t - 2) * ((3 * (t : ℝ)) / q + 1 / q ^ 2) + q ^ t) +
      2 * (((q + 4) ^ (3 * t) + 4 * (q + 4) ^ (3 * t - 1) - (q - 1) ^ (3 * t)) / q ^ 2 +
        6 * (q + 6) ^ (3 * t) / q ^ 3) +
      (2 : ℝ) ^ (6 * t) * q ^ (3 * t - t / 3) :=
    validCols_fourier_diff_sum t (d - 1) (by omega) (by omega)
  have hsum_val_le : (∑ S ∈ SnonU, ((validCols (6 * t) (d - 1) S).card : ℝ)) ≤
      (∑ S ∈ SnonU, modelQ S) + (∑ S ∈ SnonU, |((validCols (6 * t) (d - 1) S).card : ℝ) - modelQ S|) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun S _ => ?_)
    have hle := le_abs_self (((validCols (6 * t) (d - 1) S).card : ℝ) - modelQ S)
    linarith only [hle]
  have hsum_modelQ : (∑ S ∈ SnonU, modelQ S) ≤
      2 * q ^ (3 * t - 2) + 2 * (1 + Real.sqrt (q - 1)) ^ (6 * t) / q ^ 4 := by
    have hnn : ∀ S, 0 ≤ modelQ S := fun S => by
      dsimp only [modelQ]
      have h1 : (0 : ℝ) ≤ if S = laneSet 0 then q ^ (3 * t - 2) else 0 := by split_ifs <;> positivity
      have h2 : (0 : ℝ) ≤ if S = laneSet 1 then q ^ (3 * t - 2) else 0 := by split_ifs <;> positivity
      have h3 : (0 : ℝ) ≤ (q - 1) ^ (runsCard S) / q ^ 4 :=
        div_nonneg (pow_nonneg (by linarith only [hq32]) _) (by positivity)
      linarith only [h1, h2, h3]
    calc ∑ S ∈ SnonU, modelQ S
        ≤ ∑ S : Finset (Fin (6 * t)), modelQ S := Finset.sum_le_univ_sum_of_nonneg hnn
      _ = 2 * q ^ (3 * t - 2) + (matA q ^ (6 * t)).trace / q ^ 4 := by
          dsimp only [modelQ]
          simp only [Finset.sum_add_distrib, ← Finset.sum_div]
          have h0 : (∑ S : Finset (Fin (6 * t)), if S = laneSet 0 then q ^ (3 * t - 2) else 0) =
              q ^ (3 * t - 2) := by simp
          have h1 : (∑ S : Finset (Fin (6 * t)), if S = laneSet 1 then q ^ (3 * t - 2) else 0) =
              q ^ (3 * t - 2) := by simp
          have h2 := sum_runs_eq_trace_A (6 * t) (by omega) q
          rw [h0, h1, h2]; ring
      _ ≤ 2 * q ^ (3 * t - 2) + 2 * (1 + Real.sqrt (q - 1)) ^ (6 * t) / q ^ 4 := by
          have htr := trace_matA_pow_le_even q (by linarith only [hq32]) (3 * t)
          have h6 : 2 * (3 * t) = 6 * t := by ring
          rw [h6] at htr
          have hdiv := div_le_div_of_nonneg_right htr (by positivity : (0 : ℝ) ≤ q ^ 4)
          linarith only [hdiv]
  have hq_1add4 : (q + 4) ^ (3 * t) ≤ 2 * q ^ (3 * t) := by
    have h1 : (1 + 4 / q) ^ (3 * t) ≤ 2 :=
      pow_one_add_le_two (by positivity) (by
        have h : ((3 * t : ℕ) : ℝ) * (4 / q) = 4 * (6 * (t : ℝ)) / s := by
          rw [hq_val]; push_cast; field_simp [ne_of_gt hspos]; ring
        rw [h, div_le_iff₀ hspos]; linarith only [hds])
    have h2 : (q + 4) ^ (3 * t) = q ^ (3 * t) * (1 + 4 / q) ^ (3 * t) := by
      rw [← mul_pow]; congr 1; field_simp [ne_of_gt hqpos]
    rw [h2]; nlinarith only [h1, pow_nonneg (le_of_lt hqpos) (3 * t)]
  have hq_1add6 : (q + 6) ^ (3 * t) ≤ 2 * q ^ (3 * t) := by
    have h1 : (1 + 6 / q) ^ (3 * t) ≤ 2 :=
      pow_one_add_le_two (by positivity) (by
        have h : ((3 * t : ℕ) : ℝ) * (6 / q) = 6 * (6 * (t : ℝ)) / s := by
          rw [hq_val]; push_cast; field_simp [ne_of_gt hspos]; ring
        rw [h, div_le_iff₀ hspos]; linarith only [hds])
    have h2 : (q + 6) ^ (3 * t) = q ^ (3 * t) * (1 + 6 / q) ^ (3 * t) := by
      rw [← mul_pow]; congr 1; field_simp [ne_of_gt hqpos]
    rw [h2]; nlinarith only [h1, pow_nonneg (le_of_lt hqpos) (3 * t)]
  have hq_eq2 : q ^ (3 * t - 2) * q ^ 2 = q ^ (3 * t) := by
    rw [← pow_add]; congr 1; omega
  have hdiff_q_crude : (∑ S ∈ SnonU, |((validCols (6 * t) (d - 1) S).card : ℝ) - modelQ S|) ≤
      40 * q ^ (3 * t - 2) + (2 : ℝ) ^ (6 * t) * q ^ (3 * t - t / 3) := by
    have h1 : (3 * (t : ℝ)) / q + 1 / q ^ 2 ≤ 1 := by
      have ha : (3 * (t : ℝ)) / q = 6 * (t : ℝ) / s := by
        rw [hq_val]; field_simp [ne_of_gt hspos]; ring
      have hb : 6 * (t : ℝ) / s ≤ 1 / 100 := by rw [div_le_iff₀ hspos]; linarith only [hds]
      have hc : 1 / q ^ 2 ≤ 1 / 100 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith only [hq32]
      linarith only [ha, hb, hc]
    have h2 : q ^ t ≤ q ^ (3 * t - 2) := pow_le_pow_right₀ (by linarith only [hq32]) (by omega)
    have h3 : ((q + 4) ^ (3 * t) + 4 * (q + 4) ^ (3 * t - 1) - (q - 1) ^ (3 * t)) / q ^ 2 ≤
        10 * q ^ (3 * t - 2) := by
      have ha : (q + 4) ^ (3 * t - 1) ≤ (q + 4) ^ (3 * t) :=
        pow_le_pow_right₀ (by linarith only [hq32]) (by omega)
      have hb : (0 : ℝ) ≤ (q - 1) ^ (3 * t) := pow_nonneg (by linarith only [hq32]) _
      have hc : (q + 4) ^ (3 * t) + 4 * (q + 4) ^ (3 * t - 1) - (q - 1) ^ (3 * t) ≤ 10 * q ^ (3 * t) := by
        linarith only [hq_1add4, ha, hb]
      have hd' := div_le_div_of_nonneg_right hc (by positivity : (0 : ℝ) ≤ q ^ 2)
      have hR : 10 * q ^ (3 * t) / q ^ 2 = 10 * q ^ (3 * t - 2) := by
        rw [← hq_eq2]; field_simp [ne_of_gt hqpos]
      linarith only [hd', hR]
    have h4 : 6 * (q + 6) ^ (3 * t) / q ^ 3 ≤ 1 * q ^ (3 * t - 2) := by
      have hc : 6 * (q + 6) ^ (3 * t) ≤ 12 * q ^ (3 * t) := by linarith only [hq_1add6]
      have hd' := div_le_div_of_nonneg_right hc (by positivity : (0 : ℝ) ≤ q ^ 3)
      have hR : 12 * q ^ (3 * t) / q ^ 3 = (12 / q) * q ^ (3 * t - 2) := by
        rw [← hq_eq2]; field_simp [ne_of_gt hqpos]
      have h12 : 12 / q ≤ 1 := by rw [div_le_iff₀ hqpos]; linarith only [hq32]
      have hqnn := pow_nonneg (le_of_lt hqpos) (3 * t - 2)
      nlinarith only [hd', hR, h12, hqnn]
    have hqnn := pow_nonneg (le_of_lt hqpos) (3 * t - 2)
    have h1m : q ^ (3 * t - 2) * ((3 * (t : ℝ)) / q + 1 / q ^ 2) ≤ q ^ (3 * t - 2) := by
      nlinarith only [h1, hqnn]
    linarith only [hfd_q, h1m, h2, h3, h4, hqnn]
  have hPiece1 : s * (42 * q ^ (3 * t - 2)) / Z ≤ 100 * ((1 : ℝ) / 2) ^ t := by
    have hpow_q : q ^ (3 * t - 2) = s ^ (3 * t - 2) / (2 : ℝ) ^ (3 * t - 2) := by
      rw [hq_val, div_pow]
    have hratio : s * (42 * q ^ (3 * t - 2)) / (2 * s ^ (3 * t - 2)) =
        21 * s / (2 : ℝ) ^ (3 * t - 2) := by
      rw [hpow_q]; field_simp [ne_of_gt hspos]; ring
    have hpow2 : 21 * s / (2 : ℝ) ^ (3 * t - 2) ≤ 100 * ((1 : ℝ) / 2) ^ t := by
      have h21 : 21 * (2 : ℝ) ^ d * (2 : ℝ) ^ t ≤ 100 * (2 : ℝ) ^ (3 * t - 2) := by
        have hexp : d + t ≤ 3 * t - 2 := by omega
        have hp : (2 : ℝ) ^ d * (2 : ℝ) ^ t ≤ (2 : ℝ) ^ (3 * t - 2) := by
          rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) hexp
        have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ (3 * t - 2) := by positivity
        linarith only [hp, hnn]
      have h12 : ((1 : ℝ) / 2) ^ t = 1 / (2 : ℝ) ^ t := by rw [div_pow, one_pow]
      rw [h12, div_le_iff₀ (by positivity)]
      dsimp only [s]
      have h2t : (0 : ℝ) < (2 : ℝ) ^ t := by positivity
      have hR : 100 * (1 / (2 : ℝ) ^ t) * (2 : ℝ) ^ (3 * t - 2) =
          (100 * (2 : ℝ) ^ (3 * t - 2)) / (2 : ℝ) ^ t := by ring
      rw [hR, le_div_iff₀ h2t]
      linarith only [h21]
    calc s * (42 * q ^ (3 * t - 2)) / Z
        ≤ s * (42 * q ^ (3 * t - 2)) / (2 * s ^ (3 * t - 2)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hZ_ge1
      _ = 21 * s / (2 : ℝ) ^ (3 * t - 2) := hratio
      _ ≤ 100 * ((1 : ℝ) / 2) ^ t := hpow2
  have hPiece2 : s * (2 * (1 + Real.sqrt (q - 1)) ^ (6 * t) / q ^ 4) / Z ≤
      100 * ((1 : ℝ) / 2) ^ t := by
    have hsr := sqrt_ratio_le_five_sixths hs64
    have hpow6 : ((1 + Real.sqrt (s / 2 - 1)) / (1 + Real.sqrt (s - 1))) ^ (6 * t) ≤
        ((3 : ℝ) / 8) ^ t := by
      have h1 : ((5 : ℝ) / 6) ^ 6 ≤ (3 : ℝ) / 8 := by norm_num
      have h2 : ((1 + Real.sqrt (s / 2 - 1)) / (1 + Real.sqrt (s - 1))) ^ (6 * t) ≤
          ((5 : ℝ) / 6) ^ (6 * t) :=
        pow_le_pow_left₀ (by positivity) hsr (6 * t)
      have h3 : ((5 : ℝ) / 6) ^ (6 * t) ≤ ((3 : ℝ) / 8) ^ t := by
        rw [pow_mul]
        exact pow_le_pow_left₀ (by positivity) h1 t
      exact le_trans h2 h3
    have hden_pos : 0 < (1 + Real.sqrt (s - 1)) ^ (6 * t) / s ^ 4 := by positivity
    have hsimp : s * (2 * (1 + Real.sqrt (q - 1)) ^ (6 * t) / q ^ 4) /
        ((1 + Real.sqrt (s - 1)) ^ (6 * t) / s ^ 4) =
        32 * s * ((1 + Real.sqrt (s / 2 - 1)) / (1 + Real.sqrt (s - 1))) ^ (6 * t) := by
      rw [hq_val, div_pow, div_pow]
      have hden1 : (1 + Real.sqrt (s - 1)) ^ (6 * t) ≠ 0 := by positivity
      field_simp [ne_of_gt hspos, hden1]
      ring
    have h32 : 32 * s * ((3 : ℝ) / 8) ^ t ≤ 100 * ((1 : ℝ) / 2) ^ t := by
      have h34 : ((3 : ℝ) / 4) ^ t ≤ ((1 : ℝ) / 2) ^ d := by
        have hstep1 : ((3 : ℝ) / 4) ^ t ≤ ((3 : ℝ) / 4) ^ (3 * d) :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        have hstep2 : ((3 : ℝ) / 4) ^ (3 * d) ≤ ((1 : ℝ) / 2) ^ d := by
          rw [pow_mul]
          exact pow_le_pow_left₀ (by positivity) (by norm_num : ((3 : ℝ) / 4) ^ 3 ≤ 1 / 2) d
        exact le_trans hstep1 hstep2
      have hp : s * ((3 : ℝ) / 4) ^ t ≤ 1 := by
        have hm := mul_le_mul_of_nonneg_left h34 (le_of_lt hspos)
        have h1 : s * ((1 : ℝ) / 2) ^ d = 1 := by
          dsimp only [s]; rw [← mul_pow]; norm_num
        linarith only [hm, h1]
      have hsplit : ((3 : ℝ) / 8) ^ t = ((3 : ℝ) / 4) ^ t * ((1 : ℝ) / 2) ^ t := by
        rw [← mul_pow]; norm_num
      rw [hsplit]
      have hnn := pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) t
      nlinarith only [hp, hnn]
    calc s * (2 * (1 + Real.sqrt (q - 1)) ^ (6 * t) / q ^ 4) / Z
        ≤ s * (2 * (1 + Real.sqrt (q - 1)) ^ (6 * t) / q ^ 4) /
          ((1 + Real.sqrt (s - 1)) ^ (6 * t) / s ^ 4) :=
          div_le_div_of_nonneg_left (by positivity) hden_pos hZ_ge2
      _ = 32 * s * ((1 + Real.sqrt (s / 2 - 1)) / (1 + Real.sqrt (s - 1))) ^ (6 * t) := hsimp
      _ ≤ 32 * s * ((3 : ℝ) / 8) ^ t := by gcongr
      _ ≤ 100 * ((1 : ℝ) / 2) ^ t := h32
  have hPiece3 : s * ((2 : ℝ) ^ (6 * t) * q ^ (3 * t - t / 3)) / Z ≤ 50 * ((1 : ℝ) / 2) ^ t := by
    have hexp : d + 6 * t + (d - 1) * (3 * t - t / 3) + t ≤ d * (3 * t - 2) := by
      have h1 : (d - 1) * (3 * t - t / 3) ≤ d * (3 * t - t / 3) :=
        Nat.mul_le_mul_right _ (Nat.sub_le d 1)
      have h2 : d * (3 * t - 2) - d * (3 * t - t / 3) = d * (t / 3 - 2) := by
        rw [← Nat.mul_sub]; congr 1; omega
      have h3 : d * (t / 3 - 2) ≥ 40 * (t / 3 - 2) := Nat.mul_le_mul_right _ hd
      have h4 : d + 7 * t ≤ 40 * (t / 3 - 2) := by omega
      omega
    have hpow_nat : s * ((2 : ℝ) ^ (6 * t) * q ^ (3 * t - t / 3)) * (2 : ℝ) ^ t ≤
        s ^ (3 * t - 2) := by
      dsimp only [s, q]
      simp only [← pow_mul, ← pow_add]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    calc s * ((2 : ℝ) ^ (6 * t) * q ^ (3 * t - t / 3)) / Z
        ≤ s * ((2 : ℝ) ^ (6 * t) * q ^ (3 * t - t / 3)) / (2 * s ^ (3 * t - 2)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hZ_ge1
      _ ≤ ((1 : ℝ) / 2) ^ t := by
          rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * s ^ (3 * t - 2))]
          have h12 : ((1 : ℝ) / 2) ^ t = ((2 : ℝ) ^ t)⁻¹ := by rw [one_div, inv_pow]
          rw [h12]
          have h2tpos : (0 : ℝ) < (2 : ℝ) ^ t := by positivity
          have hmul := mul_le_mul_of_nonneg_right hpow_nat (by positivity : (0 : ℝ) ≤ ((2 : ℝ) ^ t)⁻¹)
          have hL : s * ((2 : ℝ) ^ (6 * t) * q ^ (3 * t - t / 3)) * (2 : ℝ) ^ t * ((2 : ℝ) ^ t)⁻¹ =
              s * ((2 : ℝ) ^ (6 * t) * q ^ (3 * t - t / 3)) := by field_simp [ne_of_gt h2tpos]
          rw [hL] at hmul
          have hR : s ^ (3 * t - 2) * ((2 : ℝ) ^ t)⁻¹ ≤ ((2 : ℝ) ^ t)⁻¹ * (2 * s ^ (3 * t - 2)) := by
            have hnn : 0 ≤ s ^ (3 * t - 2) * ((2 : ℝ) ^ t)⁻¹ := by positivity
            linarith only [hnn]
          exact le_trans hmul hR
      _ ≤ 50 * ((1 : ℝ) / 2) ^ t := by
          have hnn : (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ t := by positivity
          linarith only [hnn]
  have htotB : s * (∑ S ∈ SnonU, ((validCols (6 * t) (d - 1) S).card : ℝ)) ≤
      s * (42 * q ^ (3 * t - 2)) +
      s * (2 * (1 + Real.sqrt (q - 1)) ^ (6 * t) / q ^ 4) +
      s * ((2 : ℝ) ^ (6 * t) * q ^ (3 * t - t / 3)) := by
    have hsum_le : (∑ S ∈ SnonU, ((validCols (6 * t) (d - 1) S).card : ℝ)) ≤
        42 * q ^ (3 * t - 2) + 2 * (1 + Real.sqrt (q - 1)) ^ (6 * t) / q ^ 4 +
        (2 : ℝ) ^ (6 * t) * q ^ (3 * t - t / 3) := by
      linarith only [hsum_val_le, hsum_modelQ, hdiff_q_crude]
    have hmul := mul_le_mul_of_nonneg_left hsum_le (le_of_lt hspos)
    linarith only [hmul]
  have hdivB := div_le_div_of_nonneg_right htotB (le_of_lt hZ_pos)
  rw [add_div, add_div] at hdivB
  linarith only [hdivB, hPiece1, hPiece2, hPiece3]

lemma main_ratio_bound_core (t d : ℕ) (ht : 10 ≤ t) (hd : 40 ≤ d)
    (hds : 6 * (t : ℝ) ≤ (2 : ℝ) ^ d / 100) (hdt : 12 * d ≤ t)
    (actual : Finset (Fin (6 * t)) → ℝ)
    (hact_eq : ∀ S : Finset (Fin (6 * t)), actual S = ((fullCols (6 * t) d S).card : ℝ)) :
    let s : ℝ := (2 : ℝ) ^ d
    let model : Finset (Fin (6 * t)) → ℝ := fun S =>
      (if S = laneSet 0 then s ^ (3 * t - 2) else 0) +
      (if S = laneSet 1 then s ^ (3 * t - 2) else 0) +
      (s - 1) ^ (runsCard S) / s ^ 4
    (∑ S : Finset (Fin (6 * t)), |actual S - model S|) / (∑ S : Finset (Fin (6 * t)), model S) ≤
      60 * ((6 * (t : ℝ)) / s) + 40 / s + 300 * ((1 : ℝ) / 2) ^ t := by
  intro s model
  have hs64 : (64 : ℝ) ≤ s := by
    calc (64 : ℝ) = (2 : ℝ) ^ 6 := by norm_num
      _ ≤ (2 : ℝ) ^ d := pow_le_pow_right₀ (by norm_num) (by omega)
  have hspos : (0 : ℝ) < s := by linarith only [hs64]
  have hZ_eq : (∑ S : Finset (Fin (6 * t)), model S) =
      2 * s ^ (3 * t - 2) + (matA s ^ (6 * t)).trace / s ^ 4 := by
    dsimp only [model]
    simp only [Finset.sum_add_distrib, ← Finset.sum_div]
    have h0 : (∑ S : Finset (Fin (6 * t)), if S = laneSet 0 then s ^ (3 * t - 2) else 0) =
        s ^ (3 * t - 2) := by simp
    have h1 : (∑ S : Finset (Fin (6 * t)), if S = laneSet 1 then s ^ (3 * t - 2) else 0) =
        s ^ (3 * t - 2) := by simp
    have h2 : (∑ S : Finset (Fin (6 * t)), (s - 1) ^ (runsCard S)) = (matA s ^ (6 * t)).trace :=
      sum_runs_eq_trace_A (6 * t) (by omega) s
    rw [h0, h1, h2]
    ring
  have hZ_ge1 : 2 * s ^ (3 * t - 2) ≤ ∑ S : Finset (Fin (6 * t)), model S := by
    rw [hZ_eq]
    have htr : 0 ≤ (matA s ^ (6 * t)).trace := by
      have h := trace_matA_pow_ge_even s (by linarith only [hs64]) (3 * t)
      have h6 : 2 * (3 * t) = 6 * t := by ring
      rw [h6] at h
      have hnn : 0 ≤ (1 + Real.sqrt (s - 1)) ^ (6 * t) := by positivity
      linarith only [h, hnn]
    have hdiv : 0 ≤ (matA s ^ (6 * t)).trace / s ^ 4 := div_nonneg htr (by positivity)
    linarith only [hdiv]
  have hZ_ge2 : (1 + Real.sqrt (s - 1)) ^ (6 * t) / s ^ 4 ≤ ∑ S : Finset (Fin (6 * t)), model S := by
    rw [hZ_eq]
    have htr := trace_matA_pow_ge_even s (by linarith only [hs64]) (3 * t)
    have h6 : 2 * (3 * t) = 6 * t := by ring
    rw [h6] at htr
    have hnn : 0 ≤ 2 * s ^ (3 * t - 2) := by positivity
    have hdiv : (1 + Real.sqrt (s - 1)) ^ (6 * t) / s ^ 4 ≤ (matA s ^ (6 * t)).trace / s ^ 4 :=
      div_le_div_of_nonneg_right htr (by positivity)
    linarith only [hnn, hdiv]
  have hZ_pos : 0 < ∑ S : Finset (Fin (6 * t)), model S := by
    have hpos : 0 < 2 * s ^ (3 * t - 2) := by positivity
    linarith only [hpos, hZ_ge1]
  let SnonU := Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))
  have hnum_split : (∑ S : Finset (Fin (6 * t)), |actual S - model S|) =
      |actual Finset.univ - model Finset.univ| + ∑ S ∈ SnonU, |actual S - model S| :=
    (Finset.add_sum_erase Finset.univ (fun S => |actual S - model S|) (Finset.mem_univ _)).symm
  have huniv_err : |actual Finset.univ - model Finset.univ| = 1 / s ^ 4 := by
    rw [hact_eq, fullCols_univ (6 * t) d (by omega) (by omega)]
    have hne0 : (Finset.univ : Finset (Fin (6 * t))) ≠ laneSet 0 := by
      intro heq
      have hmem : (⟨1, by omega⟩ : Fin (6 * t)) ∈ laneSet 0 := by rw [← heq]; exact Finset.mem_univ _
      simp [laneSet] at hmem
    have hne1 : (Finset.univ : Finset (Fin (6 * t))) ≠ laneSet 1 := by
      intro heq
      have hmem : (⟨0, by omega⟩ : Fin (6 * t)) ∈ laneSet 1 := by rw [← heq]; exact Finset.mem_univ _
      simp [laneSet] at hmem
    have hrunsU : runsCard (Finset.univ : Finset (Fin (6 * t))) = 0 := by simp [runsCard, endsSet]
    simp only [Nat.cast_zero, zero_sub, abs_neg, model, hne0, hne1, ↓reduceIte, add_zero, zero_add,
      hrunsU, pow_zero]
    exact abs_of_nonneg (by positivity)
  have hnonU_tri : (∑ S ∈ SnonU, |actual S - model S|) ≤
      (∑ S ∈ SnonU, |((validCols (6 * t) d S).card : ℝ) - model S|) +
      s * (∑ S ∈ SnonU, ((validCols (6 * t) (d - 1) S).card : ℝ)) := by
    have hper : ∀ S ∈ SnonU,
        |actual S - model S| ≤ |((validCols (6 * t) d S).card : ℝ) - model S| +
          s * ((validCols (6 * t) (d - 1) S).card : ℝ) := by
      intro S _
      rw [hact_eq S]
      have hsub : fullCols (6 * t) d S ⊆ validCols (6 * t) d S := Finset.filter_subset _ _
      have hle_c : (fullCols (6 * t) d S).card ≤ (validCols (6 * t) d S).card :=
        Finset.card_le_card hsub
      have hdiff_nat := fullCols_diff_le (6 * t) d (by omega) S
      have hdiff_r : ((validCols (6 * t) d S).card : ℝ) - ((fullCols (6 * t) d S).card : ℝ) ≤
          s * ((validCols (6 * t) (d - 1) S).card : ℝ) := by
        have h1 : (((validCols (6 * t) d S).card - (fullCols (6 * t) d S).card : ℕ) : ℝ) ≤
            ((2 ^ d - 1 : ℕ) : ℝ) * ((validCols (6 * t) (d - 1) S).card : ℝ) := by
          exact_mod_cast hdiff_nat
        rw [Nat.cast_sub hle_c] at h1
        have h2 : ((2 ^ d - 1 : ℕ) : ℝ) ≤ s := by
          have : 2 ^ d - 1 ≤ 2 ^ d := Nat.sub_le _ _
          dsimp only [s]
          exact_mod_cast this
        have hnn : (0 : ℝ) ≤ ((validCols (6 * t) (d - 1) S).card : ℝ) := Nat.cast_nonneg _
        nlinarith only [h1, h2, hnn]
      have hnn_diff : 0 ≤ ((validCols (6 * t) d S).card : ℝ) - ((fullCols (6 * t) d S).card : ℝ) := by
        have hle : ((fullCols (6 * t) d S).card : ℝ) ≤ ((validCols (6 * t) d S).card : ℝ) :=
          Nat.cast_le.mpr hle_c
        linarith only [hle]
      have htri := abs_add_le (((validCols (6 * t) d S).card : ℝ) - model S)
        (-(((validCols (6 * t) d S).card : ℝ) - ((fullCols (6 * t) d S).card : ℝ)))
      have hrew : ((fullCols (6 * t) d S).card : ℝ) - model S =
          (((validCols (6 * t) d S).card : ℝ) - model S) +
          (-(((validCols (6 * t) d S).card : ℝ) - ((fullCols (6 * t) d S).card : ℝ))) := by ring
      rw [hrew]
      rw [abs_neg, abs_of_nonneg hnn_diff] at htri
      linarith only [htri, hdiff_r]
    calc ∑ S ∈ SnonU, |actual S - model S|
        ≤ ∑ S ∈ SnonU, (|((validCols (6 * t) d S).card : ℝ) - model S| +
            s * ((validCols (6 * t) (d - 1) S).card : ℝ)) := Finset.sum_le_sum hper
      _ = (∑ S ∈ SnonU, |((validCols (6 * t) d S).card : ℝ) - model S|) +
          s * (∑ S ∈ SnonU, ((validCols (6 * t) (d - 1) S).card : ℝ)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hPartA : (∑ S ∈ SnonU, |((validCols (6 * t) d S).card : ℝ) - model S|) /
      (∑ S : Finset (Fin (6 * t)), model S) ≤
      20 * ((6 * (t : ℝ)) / s) + 25 / s + ((1 : ℝ) / 2) ^ t := by
    have hnum_le : (∑ S ∈ SnonU, |((validCols (6 * t) d S).card : ℝ) - model S|) ≤
        2 * s ^ (3 * t - 2) * (20 * ((6 * (t : ℝ)) / s) + 25 / s + ((1 : ℝ) / 2) ^ t) :=
      main_partA_bound t d ht hd hds hdt
    calc (∑ S ∈ SnonU, |((validCols (6 * t) d S).card : ℝ) - model S|) /
          (∑ S : Finset (Fin (6 * t)), model S)
        ≤ (2 * s ^ (3 * t - 2) * (20 * ((6 * (t : ℝ)) / s) + 25 / s + ((1 : ℝ) / 2) ^ t)) /
          (∑ S : Finset (Fin (6 * t)), model S) := div_le_div_of_nonneg_right hnum_le (le_of_lt hZ_pos)
      _ ≤ (2 * s ^ (3 * t - 2) * (20 * ((6 * (t : ℝ)) / s) + 25 / s + ((1 : ℝ) / 2) ^ t)) /
          (2 * s ^ (3 * t - 2)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hZ_ge1
      _ = 20 * ((6 * (t : ℝ)) / s) + 25 / s + ((1 : ℝ) / 2) ^ t := by
          field_simp [ne_of_gt (by positivity : (0 : ℝ) < 2 * s ^ (3 * t - 2))]
  have hPartB : s * (∑ S ∈ SnonU, ((validCols (6 * t) (d - 1) S).card : ℝ)) /
      (∑ S : Finset (Fin (6 * t)), model S) ≤ 250 * ((1 : ℝ) / 2) ^ t :=
    main_partB_bound t d ht hd hds hdt (∑ S : Finset (Fin (6 * t)), model S) hZ_pos hZ_ge1 hZ_ge2
  have huniv_ratio : (1 / s ^ 4) / (∑ S : Finset (Fin (6 * t)), model S) ≤ 1 / s := by
    calc (1 / s ^ 4) / (∑ S : Finset (Fin (6 * t)), model S)
        ≤ (1 / s ^ 4) / (2 * s ^ (3 * t - 2)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hZ_ge1
      _ ≤ 1 / s := by
          rw [div_div, div_le_div_iff₀ (by positivity) hspos]
          have h1 : 1 ≤ s ^ (3 * t - 2) := one_le_pow₀ (by linarith only [hs64])
          have h2 : s ≤ s ^ 4 := by
            have hs1 : 1 ≤ s := by linarith only [hs64]
            calc s = s ^ 1 := (pow_one s).symm
              _ ≤ s ^ 4 := pow_le_pow_right₀ hs1 (by omega)
          nlinarith only [h1, h2, hspos]
  rw [hnum_split, huniv_err]
  have hcomb : (1 / s ^ 4 + ∑ S ∈ SnonU, |actual S - model S|) / (∑ S : Finset (Fin (6 * t)), model S) ≤
      (1 / s ^ 4) / (∑ S : Finset (Fin (6 * t)), model S) +
      (∑ S ∈ SnonU, |((validCols (6 * t) d S).card : ℝ) - model S|) / (∑ S : Finset (Fin (6 * t)), model S) +
      s * (∑ S ∈ SnonU, ((validCols (6 * t) (d - 1) S).card : ℝ)) / (∑ S : Finset (Fin (6 * t)), model S) := by
    have hnum_le : 1 / s ^ 4 + ∑ S ∈ SnonU, |actual S - model S| ≤
        1 / s ^ 4 + ((∑ S ∈ SnonU, |((validCols (6 * t) d S).card : ℝ) - model S|) +
          s * (∑ S ∈ SnonU, ((validCols (6 * t) (d - 1) S).card : ℝ))) := by
      linarith only [hnonU_tri]
    calc (1 / s ^ 4 + ∑ S ∈ SnonU, |actual S - model S|) / (∑ S : Finset (Fin (6 * t)), model S)
        ≤ (1 / s ^ 4 + ((∑ S ∈ SnonU, |((validCols (6 * t) d S).card : ℝ) - model S|) +
            s * (∑ S ∈ SnonU, ((validCols (6 * t) (d - 1) S).card : ℝ)))) / (∑ S : Finset (Fin (6 * t)), model S) :=
          div_le_div_of_nonneg_right hnum_le (le_of_lt hZ_pos)
      _ = (1 / s ^ 4) / (∑ S : Finset (Fin (6 * t)), model S) +
          (∑ S ∈ SnonU, |((validCols (6 * t) d S).card : ℝ) - model S|) / (∑ S : Finset (Fin (6 * t)), model S) +
          s * (∑ S ∈ SnonU, ((validCols (6 * t) (d - 1) S).card : ℝ)) / (∑ S : Finset (Fin (6 * t)), model S) := by ring
  have hgt : 0 ≤ (6 * (t : ℝ)) / s := by positivity
  have hinv_nn : 0 ≤ 1 / s := by positivity
  have hhalf_nn : 0 ≤ ((1 : ℝ) / 2) ^ t := by positivity
  have h25 : (25 : ℝ) / s = 25 * (1 / s) := by ring
  have h40 : (40 : ℝ) / s = 40 * (1 / s) := by ring
  linarith only [hcomb, huniv_ratio, hPartA, hPartB, hgt, hinv_nn, hhalf_nn, h25, h40]

lemma main_ratio_bound (t d : ℕ) (ht : 10 ≤ t) (hd : 40 ≤ d)
    (hds : 6 * (t : ℝ) ≤ (2 : ℝ) ^ d / 100) (hdt : 12 * d ≤ t)
    [Fintype (Submodule (ZMod 2) (Fin (6 * t) → ZMod 2))] :
    let F := ZMod 2
    let n := 6 * t
    let a := 3 * t
    let W := Fin n → F
    let next := fun i : Fin n =>
      (⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩ : Fin n)
    let h := fun (i : Fin n) (b : Fin 4) =>
      if i.val % 2 = b.val / 2 ∧ (i.val / 2 % 3 = b.val % 2 ∨ i.val / 2 % 3 = 2)
      then (1 : F) else 0
    let good := fun U : Submodule F W =>
      (∀ x ∈ U, ∀ b : Fin 4, (∑ i, h i b * x i) = 0) ∧
      (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next i) = x (next i) * y i)
    let supp := fun U : Submodule F W =>
      Finset.univ.filter (fun i : Fin n => ∃ x ∈ U, x i ≠ 0)
    let spaces := (Finset.univ : Finset (Submodule F W)).filter good
    let layer := spaces.filter (fun U : Submodule F W => Module.finrank F U = d)
    let B := ∏ i ∈ Finset.range d, (2 ^ d - 2 ^ i : ℕ)
    let s := (2 : ℝ) ^ d
    let lane := fun b : Fin 2 => Finset.univ.filter (fun i : Fin n => i.val % 2 = b.val)
    let runs := fun S : Finset (Fin n) => (S.filter (fun i => next i ∉ S)).card
    let model := fun S : Finset (Fin n) =>
      (if S = lane 0 then s ^ (a - 2) else 0) + (if S = lane 1 then s ^ (a - 2) else 0) +
      (s - 1) ^ (runs S) / s ^ 4
    let actual := fun S : Finset (Fin n) => (B : ℝ) *
      ((layer.filter (fun U => supp U = S)).card : ℝ)
    (∑ S : Finset (Fin n), |actual S - model S|) / (∑ S : Finset (Fin n), model S) ≤
      60 * ((6 * (t : ℝ)) / (2 : ℝ) ^ d) + 40 / (2 : ℝ) ^ d + 300 * ((1 : ℝ) / 2) ^ t := by
  intro F n a W next h good supp spaces layer B s lane runs model actual
  exact main_ratio_bound_core t d ht hd hds hdt actual (fun S => by
    have hnat := actual_eq_fullCols_card (6 * t) d S
    dsimp only at hnat
    change (B : ℝ) * ((layer.filter (fun U => supp U = S)).card : ℝ) = ((fullCols (6 * t) d S).card : ℝ)
    exact_mod_cast hnat)

lemma main_ratio_bound_exact (t d : ℕ) (ht : 10 ≤ t) (hd : 40 ≤ d)
    (hds : 6 * (t : ℝ) ≤ (2 : ℝ) ^ d / 100) (hdt : 12 * d ≤ t) :
    (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
     let F := ZMod 2
     let n := 6*t
     let a := 3*t
     let W := Fin n → F
     letI : Fintype (Submodule F W) := Fintype.ofFinite _
     let next := fun i : Fin n =>
       (⟨(i.val+1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩ : Fin n)
     let h := fun (i : Fin n) (b : Fin 4) =>
       if i.val % 2 = b.val / 2 ∧ (i.val / 2 % 3 = b.val % 2 ∨ i.val / 2 % 3 = 2)
       then (1:F) else 0
     let good := fun U : Submodule F W =>
       (∀ x ∈ U, ∀ b : Fin 4, (∑ i, h i b * x i) = 0) ∧
       (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next i) = x (next i) * y i)
     let supp := fun U : Submodule F W =>
       Finset.univ.filter (fun i : Fin n => ∃ x ∈ U, x i ≠ 0)
     let spaces := (Finset.univ : Finset (Submodule F W)).filter good
     let layer := spaces.filter (fun U : Submodule F W => Module.finrank F U = d)
     let B := ∏ i ∈ Finset.range d, (2^d-2^i : ℕ)
     let s := (2 : ℝ)^d
     let lane := fun b : Fin 2 => Finset.univ.filter (fun i : Fin n => i.val % 2 = b.val)
     let runs := fun S : Finset (Fin n) => (S.filter (fun i => next i ∉ S)).card
     let model := fun S : Finset (Fin n) =>
       (if S = lane 0 then s^(a-2) else 0) + (if S = lane 1 then s^(a-2) else 0) +
       (s-1)^(runs S)/s^4
     let actual := fun S : Finset (Fin n) => (B : ℝ) *
       ((layer.filter (fun U => supp U = S)).card : ℝ)
     (∑ S : Finset (Fin n), |actual S - model S|)/(∑ S : Finset (Fin n), model S)) ≤
      60 * ((6 * (t : ℝ)) / (2 : ℝ) ^ d) + 40 / (2 : ℝ) ^ d + 300 * ((1 : ℝ) / 2) ^ t := by
  let instF : Fintype (Submodule (ZMod 2) (Fin (6 * t) → ZMod 2)) := Fintype.ofFinite _
  have hmain := @main_ratio_bound t d ht hd hds hdt instF
  have hbridge : ∀ (instF' : Fintype (Submodule (ZMod 2) (Fin (6 * t) → ZMod 2))),
      (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
       let F := ZMod 2; let n := 6*t; let a := 3*t; let W := Fin n → F
       letI : Fintype (Submodule F W) := instF'
       let next := fun i : Fin n => (⟨(i.val+1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩ : Fin n)
       let h := fun (i : Fin n) (b : Fin 4) => if i.val % 2 = b.val / 2 ∧ (i.val / 2 % 3 = b.val % 2 ∨ i.val / 2 % 3 = 2) then (1:F) else 0
       let good := fun U : Submodule F W => (∀ x ∈ U, ∀ b : Fin 4, (∑ i, h i b * x i) = 0) ∧ (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next i) = x (next i) * y i)
       let supp := fun U : Submodule F W => Finset.univ.filter (fun i : Fin n => ∃ x ∈ U, x i ≠ 0)
       let spaces := (Finset.univ : Finset (Submodule F W)).filter good
       let layer := spaces.filter (fun U : Submodule F W => Module.finrank F U = d)
       let B := ∏ i ∈ Finset.range d, (2^d-2^i : ℕ); let s := (2 : ℝ)^d
       let lane := fun b : Fin 2 => Finset.univ.filter (fun i : Fin n => i.val % 2 = b.val)
       let runs := fun S : Finset (Fin n) => (S.filter (fun i => next i ∉ S)).card
       let model := fun S : Finset (Fin n) => (if S = lane 0 then s^(a-2) else 0) + (if S = lane 1 then s^(a-2) else 0) + (s-1)^(runs S)/s^4
       let actual := fun S : Finset (Fin n) => (B : ℝ) * ((layer.filter (fun U => supp U = S)).card : ℝ)
       (∑ S : Finset (Fin n), |actual S - model S|)/(∑ S : Finset (Fin n), model S)) =
      (letI : Fintype (Submodule (ZMod 2) (Fin (6 * t) → ZMod 2)) := instF'
       let F := ZMod 2; let n := 6*t; let a := 3*t; let W := Fin n → F
       let next := fun i : Fin n => (⟨(i.val+1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩ : Fin n)
       let h := fun (i : Fin n) (b : Fin 4) => if i.val % 2 = b.val / 2 ∧ (i.val / 2 % 3 = b.val % 2 ∨ i.val / 2 % 3 = 2) then (1:F) else 0
       let good := fun U : Submodule F W => (∀ x ∈ U, ∀ b : Fin 4, (∑ i, h i b * x i) = 0) ∧ (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next i) = x (next i) * y i)
       let supp := fun U : Submodule F W => Finset.univ.filter (fun i : Fin n => ∃ x ∈ U, x i ≠ 0)
       let spaces := (Finset.univ : Finset (Submodule F W)).filter good
       let layer := spaces.filter (fun U : Submodule F W => Module.finrank F U = d)
       let B := ∏ i ∈ Finset.range d, (2^d-2^i : ℕ); let s := (2 : ℝ)^d
       let lane := fun b : Fin 2 => Finset.univ.filter (fun i : Fin n => i.val % 2 = b.val)
       let runs := fun S : Finset (Fin n) => (S.filter (fun i => next i ∉ S)).card
       let model := fun S : Finset (Fin n) => (if S = lane 0 then s^(a-2) else 0) + (if S = lane 1 then s^(a-2) else 0) + (s-1)^(runs S)/s^4
       let actual := fun S : Finset (Fin n) => (B : ℝ) * ((layer.filter (fun U => supp U = S)).card : ℝ)
       (∑ S : Finset (Fin n), |actual S - model S|)/(∑ S : Finset (Fin n), model S)) := by
    intro instF'
    have hfilt2 : ∀ {α : Type} {s₁ s₂ : Finset α} {p q : α → Prop}
        {d₁ : DecidablePred p} {d₂ : DecidablePred q},
        s₁ = s₂ → (∀ x, p x ↔ q x) → @Finset.filter α p d₁ s₁ = @Finset.filter α q d₂ s₂ := by
      intro α s₁ s₂ p q d₁ d₂ hs hpq
      subst hs; ext x; simp only [Finset.mem_filter, hpq]
    have hite : ∀ {α : Type} {p q : Prop} {d₁ : Decidable p} {d₂ : Decidable q} {x y : α},
        (p ↔ q) → @ite α p d₁ x y = @ite α q d₂ x y := by
      intro α p q d₁ d₂ x y hpq
      by_cases hp : p
      · have hq : q := hpq.mp hp; rw [if_pos hp, if_pos hq]
      · have hq : ¬ q := fun h => hp (hpq.mpr h); rw [if_neg hp, if_neg hq]
    dsimp only
    refine congrArg₂ (· / ·) (Finset.sum_congr rfl fun S _ => ?_) (Finset.sum_congr rfl fun S _ => ?_)
    · congr 1
      refine congrArg₂ (· - ·) ?_ ?_
      · congr 2
        refine congrArg Finset.card ?_
        refine hfilt2 (hfilt2 (hfilt2 rfl fun U => ?_) fun _ => Iff.rfl) fun U => ?_
        · constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨fun x hx b => ?_, h2⟩
          · exact (Finset.sum_congr rfl fun i _ => congrArg (· * x i) (hite Iff.rfl)).trans (h1 x hx b)
          · exact (Finset.sum_congr rfl fun i _ => congrArg (· * x i) (hite Iff.rfl)).trans (h1 x hx b)
        · exact iff_of_eq (congrArg (· = S) (hfilt2 rfl fun _ => Iff.rfl))
      · refine congrArg₂ (· + ·) (congrArg₂ (· + ·)
          (hite (iff_of_eq (congrArg (S = ·) (hfilt2 rfl fun _ => Iff.rfl))))
          (hite (iff_of_eq (congrArg (S = ·) (hfilt2 rfl fun _ => Iff.rfl)))))
          (congrArg (fun k => ((2 : ℝ) ^ d - 1) ^ k / ((2 : ℝ) ^ d) ^ 4)
            (congrArg Finset.card (hfilt2 rfl fun _ => Iff.rfl)))
    · refine congrArg₂ (· + ·) (congrArg₂ (· + ·)
        (hite (iff_of_eq (congrArg (S = ·) (hfilt2 rfl fun _ => Iff.rfl))))
        (hite (iff_of_eq (congrArg (S = ·) (hfilt2 rfl fun _ => Iff.rfl)))))
        (congrArg (fun k => ((2 : ℝ) ^ d - 1) ^ k / ((2 : ℝ) ^ d) ^ 4)
          (congrArg Finset.card (hfilt2 rfl fun _ => Iff.rfl)))
  exact (hbridge instF).trans_le hmain

end PEqualNP.Outside.L_lib_940

theorem PEqualNP.Outside.L_lib_940 : ∀ T D : ℕ → ℕ, Filter.Tendsto T Filter.atTop Filter.atTop →
  (∀ k, 2 ≤ D k) →
  Filter.Tendsto (fun k => (6*(T k : ℝ))/(2 : ℝ)^(D k)) Filter.atTop (nhds 0) →
  Filter.Tendsto (fun k => (D k : ℝ)/(6*(T k : ℝ))) Filter.atTop (nhds 0) →
  Filter.Tendsto (fun k : ℕ =>
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let t := T k
  let d := D k
  let F := ZMod 2
  let n := 6*t
  let a := 3*t
  let W := Fin n → F
  letI : Fintype (Submodule F W) := Fintype.ofFinite _
  let next := fun i : Fin n =>
    (⟨(i.val+1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩ : Fin n)
  let h := fun (i : Fin n) (b : Fin 4) =>
    if i.val % 2 = b.val / 2 ∧ (i.val / 2 % 3 = b.val % 2 ∨ i.val / 2 % 3 = 2)
    then (1:F) else 0
  let good := fun U : Submodule F W =>
    (∀ x ∈ U, ∀ b : Fin 4, (∑ i, h i b * x i) = 0) ∧
    (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next i) = x (next i) * y i)
  let supp := fun U : Submodule F W =>
    Finset.univ.filter (fun i : Fin n => ∃ x ∈ U, x i ≠ 0)
  let spaces := (Finset.univ : Finset (Submodule F W)).filter good
  let layer := spaces.filter (fun U : Submodule F W => Module.finrank F U = d)
  let B := ∏ i ∈ Finset.range d, (2^d-2^i : ℕ)
  let s := (2 : ℝ)^d
  let lane := fun b : Fin 2 => Finset.univ.filter (fun i : Fin n => i.val % 2 = b.val)
  let runs := fun S : Finset (Fin n) => (S.filter (fun i => next i ∉ S)).card
  let model := fun S : Finset (Fin n) =>
    (if S = lane 0 then s^(a-2) else 0) + (if S = lane 1 then s^(a-2) else 0) +
    (s-1)^(runs S)/s^4
  let actual := fun S : Finset (Fin n) => (B : ℝ) *
    ((layer.filter (fun U => supp U = S)).card : ℝ)
  (∑ S : Finset (Fin n), |actual S - model S|)/(∑ S : Finset (Fin n), model S))
    Filter.atTop (nhds 0) := by
  intro T D hT hD2 hSmall hDsmall
  have hT_ev10 : ∀ᶠ k in Filter.atTop, 10 ≤ T k :=
    hT.eventually (Filter.eventually_ge_atTop 10)
  have hSmall_ev : ∀ᶠ k in Filter.atTop, (6 * (T k : ℝ)) / (2 : ℝ) ^ (D k) < 1 / 100 :=
    hSmall.eventually (gt_mem_nhds (by norm_num))
  have hDsmall_ev : ∀ᶠ k in Filter.atTop, (D k : ℝ) / (6 * (T k : ℝ)) < 1 / 72 :=
    hDsmall.eventually (gt_mem_nhds (by norm_num))
  have hD_tendsto : Filter.Tendsto (fun k => (1 : ℝ) / (2 : ℝ) ^ (D k)) Filter.atTop (nhds 0) := by
    have hle : ∀ᶠ k in Filter.atTop, (1 : ℝ) / (2 : ℝ) ^ (D k) ≤ (6 * (T k : ℝ)) / (2 : ℝ) ^ (D k) := by
      filter_upwards [hT_ev10] with k hk
      have h1 : (1 : ℝ) ≤ 6 * (T k : ℝ) := by
        have : (10 : ℝ) ≤ (T k : ℝ) := by exact_mod_cast hk
        linarith
      exact div_le_div_of_nonneg_right h1 (by positivity)
    exact squeeze_zero' (Filter.Eventually.of_forall (fun _ => by positivity)) hle hSmall
  have hD_ev40 : ∀ᶠ k in Filter.atTop, 40 ≤ D k := by
    have hlt : ∀ᶠ k in Filter.atTop, (1 : ℝ) / (2 : ℝ) ^ (D k) < (1 : ℝ) / (2 : ℝ) ^ 40 :=
      hD_tendsto.eventually (gt_mem_nhds (by positivity))
    filter_upwards [hlt] with k hk
    by_contra hlt40
    push_neg at hlt40
    have hpow : (2 : ℝ) ^ (D k) ≤ (2 : ℝ) ^ 40 := pow_le_pow_right₀ (by norm_num) (le_of_lt hlt40)
    have hge : (1 : ℝ) / (2 : ℝ) ^ 40 ≤ (1 : ℝ) / (2 : ℝ) ^ (D k) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hpow
    linarith
  have hHalf_tendsto : Filter.Tendsto (fun k => ((1 : ℝ) / 2) ^ (T k)) Filter.atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp hT
  have hRHS_tendsto : Filter.Tendsto (fun k =>
      60 * ((6 * (T k : ℝ)) / (2 : ℝ) ^ (D k)) + 40 * ((1 : ℝ) / (2 : ℝ) ^ (D k)) +
        300 * ((1 : ℝ) / 2) ^ (T k)) Filter.atTop (nhds 0) := by
    have h1 := hSmall.const_mul (60 : ℝ)
    have h2 := hD_tendsto.const_mul (40 : ℝ)
    have h3 := hHalf_tendsto.const_mul (300 : ℝ)
    simpa using (h1.add h2).add h3
  refine squeeze_zero' ?_ ?_ hRHS_tendsto
  · filter_upwards [hT_ev10] with k hk
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    letI : Fintype (Submodule (ZMod 2) (Fin (6 * T k) → ZMod 2)) := Fintype.ofFinite _
    apply div_nonneg
    · exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    · exact Finset.sum_nonneg (fun S _ => by
        have h1 : (0 : ℝ) ≤ if S = Finset.univ.filter (fun i : Fin (6 * T k) => i.val % 2 = (0 : Fin 2).val)
            then ((2 : ℝ) ^ D k) ^ (3 * T k - 2) else 0 := by split_ifs <;> positivity
        have h2 : (0 : ℝ) ≤ if S = Finset.univ.filter (fun i : Fin (6 * T k) => i.val % 2 = (1 : Fin 2).val)
            then ((2 : ℝ) ^ D k) ^ (3 * T k - 2) else 0 := by split_ifs <;> positivity
        have h3 : (0 : ℝ) ≤ ((2 : ℝ) ^ D k - 1) ^ ((S.filter (fun i =>
            (⟨(i.val + 1) % (6 * T k), Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩ : Fin (6 * T k)) ∉ S)).card) /
            ((2 : ℝ) ^ D k) ^ 4 := by
          have hs1 : (1 : ℝ) ≤ (2 : ℝ) ^ D k := one_le_pow₀ (by norm_num)
          exact div_nonneg (pow_nonneg (by linarith) _) (by positivity)
        linarith)
  · filter_upwards [hT_ev10, hD_ev40, hSmall_ev, hDsmall_ev] with k ht10 hd40 hsm hdsm
    have hds : 6 * (T k : ℝ) ≤ (2 : ℝ) ^ (D k) / 100 := by
      have hspos : (0 : ℝ) < (2 : ℝ) ^ (D k) := by positivity
      rw [div_lt_iff₀ hspos] at hsm
      linarith
    have hdt : 12 * D k ≤ T k := by
      have htpos : (0 : ℝ) < 6 * (T k : ℝ) := by
        have : (10 : ℝ) ≤ (T k : ℝ) := by exact_mod_cast ht10
        linarith
      rw [div_lt_iff₀ htpos] at hdsm
      have hreal : (12 * D k : ℝ) ≤ (T k : ℝ) := by linarith
      exact_mod_cast hreal
    have h40 : 40 / (2 : ℝ) ^ (D k) = 40 * ((1 : ℝ) / (2 : ℝ) ^ (D k)) := by ring
    rw [← h40]
    exact PEqualNP.Outside.L_lib_940.main_ratio_bound_exact (T k) (D k) ht10 hd40 hds hdt

