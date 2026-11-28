import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1074

open Finset Module Submodule
open scoped Matrix

open Classical in
lemma count_bound {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (d : ℕ) (S : ℕ → Set V) (hS : ∀ u v, u ≤ v → S v ⊆ S u) (D : Fin d → Submodule (ZMod 2) V)
    (hD : ∀ v w, w ∈ S v → v ≤ (univ.filter (fun z => w ∈ D z)).card) :
    ∑ v : Fin d, finrank (ZMod 2) (span (ZMod 2) (S (v.val + 1))) ≤
      ∑ z, finrank (ZMod 2) (D z) := by
  classical
  have hbig : ∀ v, d < v → S v = ∅ := by
    intro v hv
    ext w
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hw
    have h1 := hD v w hw
    have h2 := card_le_univ (univ.filter fun z => w ∈ D z)
    simp only [Fintype.card_fin] at h2
    omega
  have hP : ∀ i, ∃ b ⊆ S (d + 1 - i), LinearIndepOn (ZMod 2) id b ∧
      ∀ v, d + 1 - i ≤ v → S v ⊆ span (ZMod 2) (b ∩ S v) := by
    intro i
    induction i with
    | zero =>
      refine ⟨∅, by simp, linearIndepOn_empty _ _, fun v hv => ?_⟩
      rw [hbig v (by omega)]
      simp
    | succ i ih =>
      obtain ⟨b, hbS, hb, hspan⟩ := ih
      have hsub : b ⊆ S (d + 1 - (i + 1)) := hbS.trans (hS _ _ (by omega))
      obtain ⟨b', hb't, hbb', hspan', hli'⟩ := exists_linearIndepOn_extension hb hsub
      refine ⟨b', hb't, hli', fun v hv => ?_⟩
      by_cases h : d + 1 - i ≤ v
      · exact (hspan v h).trans (span_mono (Set.inter_subset_inter_left _ hbb'))
      · have hv' : v = d + 1 - (i + 1) := by omega
        rw [hv', Set.inter_eq_left.mpr hb't]
        simpa using hspan'
  obtain ⟨b, -, hli, hspan⟩ := hP d
  have hfin : b.Finite := hli.linearIndependent.setFinite
  set bs := hfin.toFinset with hbs
  have hcoe : ∀ p : V → Prop, b ∩ {w | p w} = ((bs.filter p : Finset V) : Set V) := by
    intro p
    ext w
    simp [hbs]
  have step1 : ∀ v : Fin d, finrank (ZMod 2) (span (ZMod 2) (S (v.val + 1))) ≤
      (bs.filter (fun w => w ∈ S (v.val + 1))).card := by
    intro v
    refine (Submodule.finrank_mono (span_le.mpr (hspan _ (by omega)))).trans ?_
    have := hcoe (fun w => w ∈ S (v.val + 1))
    simp only [Set.ofPred_mem_eq] at this
    rw [this]
    exact finrank_span_finset_le_card _
  have step3 : ∀ w ∈ bs, (univ.filter (fun v : Fin d => w ∈ S (v.val + 1))).card ≤
      (univ.filter (fun z => w ∈ D z)).card := by
    intro w _
    set T := univ.filter (fun v : Fin d => w ∈ S (v.val + 1))
    rcases T.eq_empty_or_nonempty with he | hne
    · rw [he]; simp
    · have hsubT : T ⊆ Iic (T.max' hne) := fun x hx => mem_Iic.mpr (le_max' _ _ hx)
      have h1 := card_le_card hsubT
      rw [Fin.card_Iic] at h1
      have hm := max'_mem T hne
      have h2 := hD _ w (mem_filter.mp hm).2
      omega
  have step5 : ∀ z, (bs.filter (fun w => w ∈ D z)).card ≤ finrank (ZMod 2) (D z) := by
    intro z
    have hli' : LinearIndepOn (ZMod 2) id ((bs.filter (fun w => w ∈ D z) : Finset V) : Set V) := by
      refine hli.mono ?_
      intro w hw
      simp [hbs] at hw
      exact hw.1
    rw [← finrank_span_finset_eq_card hli']
    exact Submodule.finrank_mono (span_le.mpr (fun w hw => by simp at hw; exact hw.2))
  calc ∑ v : Fin d, finrank (ZMod 2) (span (ZMod 2) (S (v.val + 1)))
      ≤ ∑ v : Fin d, (bs.filter (fun w => w ∈ S (v.val + 1))).card := sum_le_sum fun v _ => step1 v
    _ = ∑ w ∈ bs, (univ.filter (fun v : Fin d => w ∈ S (v.val + 1))).card := by
        simp only [card_filter]
        exact sum_comm
    _ ≤ ∑ w ∈ bs, (univ.filter (fun z => w ∈ D z)).card := sum_le_sum step3
    _ = ∑ z, (bs.filter (fun w => w ∈ D z)).card := by
        simp only [card_filter]
        exact sum_comm
    _ ≤ ∑ z, finrank (ZMod 2) (D z) := sum_le_sum fun z _ => step5 z

lemma key {M P Q W Y : Type} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]
    [AddCommGroup P] [Module (ZMod 2) P] [AddCommGroup Q] [Module (ZMod 2) Q]
    [AddCommGroup W] [Module (ZMod 2) W] [AddCommGroup Y] [Module (ZMod 2) Y]
    (U : M →ₗ[ZMod 2] P) (V : Q →ₗ[ZMod 2] M) (A : P →ₗ[ZMod 2] W) (B : Y →ₗ[ZMod 2] Q)
    (hA : ∀ y, A (U (V y)) = 0) (hB : ∀ y, U (V (B y)) = 0) :
    finrank (ZMod 2) (LinearMap.range (A ∘ₗ U)) + finrank (ZMod 2) (LinearMap.range (V ∘ₗ B)) +
      finrank (ZMod 2) (LinearMap.range (U ∘ₗ V)) ≤ finrank (ZMod 2) M := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (A ∘ₗ U)
  have h2 : LinearMap.range V ⊔ LinearMap.ker U ≤ LinearMap.ker (A ∘ₗ U) := by
    refine sup_le ?_ ?_
    · rintro _ ⟨y, rfl⟩
      simp [hA y]
    · intro x hx
      simp [LinearMap.mem_ker.mp hx]
  have h3 : LinearMap.range (V ∘ₗ B) ≤ LinearMap.range V ⊓ LinearMap.ker U := by
    refine le_inf (LinearMap.range_comp_le_range _ _) ?_
    rintro _ ⟨y, rfl⟩
    simp [hB y]
  have h4 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range V) (LinearMap.ker U)
  have h5 : finrank (ZMod 2) (LinearMap.range (U ∘ₗ V)) +
      finrank (ZMod 2) ↥(LinearMap.range V ⊓ LinearMap.ker U) ≤
      finrank (ZMod 2) (LinearMap.range V) := by
    have e := LinearMap.finrank_range_add_finrank_ker (U.domRestrict (LinearMap.range V))
    rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, ← LinearMap.range_comp] at e
    have : finrank (ZMod 2) ↥(LinearMap.range V ⊓ LinearMap.ker U) ≤
        finrank (ZMod 2) ↥((LinearMap.ker U).comap (LinearMap.range V).subtype) := by
      rw [← Submodule.map_comap_subtype]
      exact Submodule.finrank_map_le _ _
    omega
  have h6 := Submodule.finrank_mono h2
  have h7 := Submodule.finrank_mono h3
  have h8 := Submodule.finrank_mono (inf_le_right : LinearMap.range V ⊓ LinearMap.ker U ≤ _)
  omega

lemma per_test {m n h k t : ℕ} (R : Fin t → Matrix (Fin m) (Fin n) (ZMod 2))
    (A : Matrix (Fin h) (Fin m) (ZMod 2)) (B : Matrix (Fin n) (Fin k) (ZMod 2))
    (s : Finset (Fin t)) (hA : A * (∑ j ∈ s, R j) = 0) (hB : (∑ j ∈ s, R j) * B = 0) :
    finrank (ZMod 2) (span (ZMod 2) {w : Fin h → ZMod 2 |
        ∃ j ∈ s, ∃ y : Fin n, w = fun x => (A * R j) x y}) +
      finrank (ZMod 2) (span (ZMod 2) {w : Fin k → ZMod 2 |
        ∃ j ∈ s, ∃ x : Fin m, w = fun y => (R j * B) x y}) +
      (∑ j ∈ s, R j).rank ≤ ∑ j ∈ s, (R j).rank := by
  classical
  let Mi := fun j : s => LinearMap.range (R j.1).mulVecLin
  let V : (Fin n → ZMod 2) →ₗ[ZMod 2] ((j : s) → Mi j) :=
    LinearMap.pi (fun j : s => (R j.1).mulVecLin.rangeRestrict)
  let U : ((j : s) → Mi j) →ₗ[ZMod 2] (Fin m → ZMod 2) :=
    ∑ j : s, (Mi j).subtype ∘ₗ LinearMap.proj j
  have hU : ∀ f : (j : s) → Mi j, U f = ∑ j : s, (f j : Fin m → ZMod 2) := by
    intro f
    simp [U]
  have hUV : ∀ x, U (V x) = (∑ j ∈ s, R j) *ᵥ x := by
    intro x
    rw [hU, Matrix.sum_mulVec, ← Finset.sum_coe_sort s]
    rfl
  have hdim : finrank (ZMod 2) ((j : s) → Mi j) = ∑ j ∈ s, (R j).rank := by
    rw [Module.finrank_pi_fintype, ← Finset.sum_coe_sort s]
    rfl
  have hk := key U V A.mulVecLin B.mulVecLin
    (fun y => by
      rw [hUV, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hA, Matrix.zero_mulVec])
    (fun y => by
      rw [hUV, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hB, Matrix.zero_mulVec])
  have hX : LinearMap.range (U ∘ₗ V) = LinearMap.range (∑ j ∈ s, R j).mulVecLin := by
    congr 1
    exact LinearMap.ext fun x => hUV x
  rw [hX, hdim] at hk
  -- columns
  have hc : span (ZMod 2) {w : Fin h → ZMod 2 |
      ∃ j ∈ s, ∃ y : Fin n, w = fun x => (A * R j) x y} ≤ LinearMap.range (A.mulVecLin ∘ₗ U) := by
    rw [span_le]
    rintro w ⟨j, hj, y, rfl⟩
    refine ⟨Pi.single (⟨j, hj⟩ : s) ((R j).mulVecLin.rangeRestrict (Pi.single y 1)), ?_⟩
    rw [LinearMap.comp_apply, hU, Finset.sum_eq_single (⟨j, hj⟩ : s)]
    · funext x
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb]
      rfl
    · simp
  -- rows
  let N : Matrix (s × Fin m) (Fin k) (ZMod 2) := fun p y => (R p.1.1 * B) p.2 y
  have hr1 : span (ZMod 2) {w : Fin k → ZMod 2 |
      ∃ j ∈ s, ∃ x : Fin m, w = fun y => (R j * B) x y} ≤ span (ZMod 2) (Set.range N.row) := by
    apply span_mono
    rintro w ⟨j, hj, x, rfl⟩
    exact ⟨(⟨j, hj⟩, x), rfl⟩
  have hr2 : N.rank ≤ finrank (ZMod 2) (LinearMap.range (V ∘ₗ B.mulVecLin)) := by
    have e1 := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
    have e2 := LinearMap.finrank_range_add_finrank_ker (V ∘ₗ B.mulVecLin)
    have hker : LinearMap.ker (V ∘ₗ B.mulVecLin) ≤ LinearMap.ker N.mulVecLin := by
      intro y hy
      rw [LinearMap.mem_ker] at hy ⊢
      rw [Matrix.mulVecLin_apply]
      funext p
      have := congrArg (fun f => ((f p.1 : Mi p.1) : Fin m → ZMod 2) p.2) hy
      simp only [LinearMap.comp_apply, V, LinearMap.pi_apply, LinearMap.codRestrict_apply,
        Matrix.mulVecLin_apply, Pi.zero_apply, ZeroMemClass.coe_zero] at this
      rw [Matrix.mulVec_mulVec] at this
      simpa [N, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] using this
    have := Submodule.finrank_mono hker
    unfold Matrix.rank
    omega
  have hr : finrank (ZMod 2) (span (ZMod 2) {w : Fin k → ZMod 2 |
      ∃ j ∈ s, ∃ x : Fin m, w = fun y => (R j * B) x y}) ≤
      finrank (ZMod 2) (LinearMap.range (V ∘ₗ B.mulVecLin)) := by
    refine (Submodule.finrank_mono hr1).trans ?_
    rw [← Matrix.rank_eq_finrank_span_row]
    exact hr2
  have := Submodule.finrank_mono hc
  have hxr : (∑ j ∈ s, R j).rank =
      finrank (ZMod 2) (LinearMap.range (∑ j ∈ s, R j).mulVecLin) := rfl
  omega

end PEqualNP.Outside.L_lib_1074

open PEqualNP.Outside.L_lib_1074 Finset Module Submodule in
theorem PEqualNP.Outside.L_lib_1074 :
    let F := ZMod 2
    ∀ (m n h k t d : ℕ) (R : Fin t → Matrix (Fin m) (Fin n) F)
      (A : Matrix (Fin h) (Fin m) F) (B : Matrix (Fin n) (Fin k) F)
      (on : Fin d → Finset (Fin t)),
      let X := fun z : Fin d => ∑ j ∈ on z, R j
      let freq := fun j : Fin t => (Finset.univ.filter (fun z => j ∈ on z)).card
      let cols := fun v : ℕ => Submodule.span F {w : Fin h → F |
        ∃ j : Fin t, v ≤ freq j ∧ ∃ y : Fin n, w = fun x => (A * R j) x y}
      let rows := fun v : ℕ => Submodule.span F {w : Fin k → F |
        ∃ j : Fin t, v ≤ freq j ∧ ∃ x : Fin m, w = fun y => (R j * B) x y}
      (∀ z, A * X z = 0 ∧ X z * B = 0) →
        (∑ v : Fin d, (Module.finrank F (cols (v.val+1)) +
          Module.finrank F (rows (v.val+1)))) ≤
          ∑ z : Fin d, ((∑ j ∈ on z, (R j).rank) - (X z).rank) := by
  intro F m n h k t d R A B on X freq cols rows hz
  classical
  let C := fun z : Fin d => span (ZMod 2) {w : Fin h → ZMod 2 |
    ∃ j ∈ on z, ∃ y : Fin n, w = fun x => (A * R j) x y}
  let Rw := fun z : Fin d => span (ZMod 2) {w : Fin k → ZMod 2 |
    ∃ j ∈ on z, ∃ x : Fin m, w = fun y => (R j * B) x y}
  have hc : ∑ v : Fin d, finrank F (cols (v.val + 1)) ≤ ∑ z, finrank (ZMod 2) (C z) := by
    refine count_bound d (fun v => {w : Fin h → F |
      ∃ j : Fin t, v ≤ freq j ∧ ∃ y : Fin n, w = fun x => (A * R j) x y}) ?_ C ?_
    · rintro u v huv w ⟨j, hj, y, rfl⟩
      exact ⟨j, huv.trans hj, y, rfl⟩
    · rintro v w ⟨j, hj, y, rfl⟩
      refine hj.trans (card_le_card ?_)
      intro z hzm
      simp only [mem_filter, mem_univ, true_and] at hzm ⊢
      exact subset_span ⟨j, hzm, y, rfl⟩
  have hr : ∑ v : Fin d, finrank F (rows (v.val + 1)) ≤ ∑ z, finrank (ZMod 2) (Rw z) := by
    refine count_bound d (fun v => {w : Fin k → F |
      ∃ j : Fin t, v ≤ freq j ∧ ∃ x : Fin m, w = fun y => (R j * B) x y}) ?_ Rw ?_
    · rintro u v huv w ⟨j, hj, x, rfl⟩
      exact ⟨j, huv.trans hj, x, rfl⟩
    · rintro v w ⟨j, hj, x, rfl⟩
      refine hj.trans (card_le_card ?_)
      intro z hzm
      simp only [mem_filter, mem_univ, true_and] at hzm ⊢
      exact subset_span ⟨j, hzm, x, rfl⟩
  have ht : ∀ z, finrank (ZMod 2) (C z) + finrank (ZMod 2) (Rw z) ≤
      (∑ j ∈ on z, (R j).rank) - (X z).rank := by
    intro z
    have := per_test R A B (on z) (hz z).1 (hz z).2
    change finrank (ZMod 2) (span (ZMod 2) _) + finrank (ZMod 2) (span (ZMod 2) _) ≤
      (∑ j ∈ on z, (R j).rank) - (∑ j ∈ on z, R j).rank
    omega
  rw [sum_add_distrib]
  calc _ ≤ ∑ z, finrank (ZMod 2) (C z) + ∑ z, finrank (ZMod 2) (Rw z) := add_le_add hc hr
    _ = ∑ z, (finrank (ZMod 2) (C z) + finrank (ZMod 2) (Rw z)) := sum_add_distrib.symm
    _ ≤ _ := sum_le_sum fun z _ => ht z
