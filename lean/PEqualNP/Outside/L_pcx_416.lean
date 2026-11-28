import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_416_aux
open scoped BigOperators
noncomputable section

-- Section 1: Bilinear factorization rank over Q.

def HasRankLe {α β : Type*} (M : α → β → ℚ) (d : ℕ) : Prop :=
  ∃ f : Fin d → α → ℚ, ∃ g : Fin d → β → ℚ, ∀ a b, M a b = ∑ j : Fin d, f j a * g j b

def rowRank {α β : Type*} (M : α → β → ℚ) : ℕ :=
  Module.finrank ℚ (Submodule.span ℚ (Set.range M))

lemma finrank_span_range_le {ι β : Type*} [Fintype ι] [Finite β] (g : ι → β → ℚ) :
    Module.finrank ℚ (Submodule.span ℚ (Set.range g)) ≤ Fintype.card ι := by
  classical
  let L : (ι → ℚ) →ₗ[ℚ] (β → ℚ) :=
    { toFun := fun c => ∑ j : ι, c j • g j
      map_add' := fun c₁ c₂ => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun r c => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply] }
  have hle : Submodule.span ℚ (Set.range g) ≤ LinearMap.range L := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    refine ⟨fun i => if i = j then 1 else 0, ?_⟩
    dsimp [L]
    rw [Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (fun h => absurd (Finset.mem_univ j) h)]
    simp
  calc Module.finrank ℚ (Submodule.span ℚ (Set.range g))
      ≤ Module.finrank ℚ (LinearMap.range L) := Submodule.finrank_mono hle
    _ ≤ Module.finrank ℚ (ι → ℚ) := LinearMap.finrank_range_le L
    _ = Fintype.card ι := Module.finrank_pi ℚ

lemma hasRankLe_iff_rowRank_le {α β : Type*} [Finite α] [Finite β]
    (M : α → β → ℚ) (d : ℕ) : HasRankLe M d ↔ rowRank M ≤ d := by
  classical
  constructor
  · rintro ⟨f, g, hfg⟩
    have hle : Submodule.span ℚ (Set.range M) ≤ Submodule.span ℚ (Set.range g) := by
      rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      have hEq : M a = ∑ j : Fin d, f j a • g j := by
        ext b; simp [hfg a b]
      rw [hEq]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    calc rowRank M ≤ Module.finrank ℚ (Submodule.span ℚ (Set.range g)) := Submodule.finrank_mono hle
      _ ≤ Fintype.card (Fin d) := finrank_span_range_le g
      _ = d := Fintype.card_fin d
  · intro hd
    let S := Submodule.span ℚ (Set.range M)
    let r := Module.finrank ℚ S
    have hr : r ≤ d := hd
    let b : Module.Basis (Fin r) ℚ S := Module.finBasis ℚ S
    refine ⟨fun j a => if h : j.val < r then b.repr ⟨M a, Submodule.subset_span ⟨a, rfl⟩⟩ ⟨j.val, h⟩ else 0,
            fun j x => if h : j.val < r then (b ⟨j.val, h⟩).1 x else 0, ?_⟩
    intro a x
    have hsum : (∑ k : Fin r, (b.repr ⟨M a, Submodule.subset_span ⟨a, rfl⟩⟩ k) * (b k).1 x) = M a x := by
      have h1 := b.sum_repr ⟨M a, Submodule.subset_span ⟨a, rfl⟩⟩
      have h2 := congrFun (congrArg Subtype.val h1) x
      have h3 : (↑(∑ k : Fin r, (b.repr ⟨M a, Submodule.subset_span ⟨a, rfl⟩⟩ k) • b k) : β → ℚ) x =
          ∑ k : Fin r, (b.repr ⟨M a, Submodule.subset_span ⟨a, rfl⟩⟩ k) * (b k).1 x := by
        rw [Submodule.coe_sum, Finset.sum_apply]
        refine Finset.sum_congr rfl fun k _ => by simp
      rw [← h3]
      exact h2
    rw [← hsum]
    have hsplit : (∑ j : Fin d,
        (if h : j.val < r then b.repr ⟨M a, Submodule.subset_span ⟨a, rfl⟩⟩ ⟨j.val, h⟩ else 0) *
        (if h : j.val < r then (b ⟨j.val, h⟩).1 x else 0)) =
        ∑ j ∈ (Finset.univ : Finset (Fin d)).filter (fun j => j.val < r),
          (if h : j.val < r then b.repr ⟨M a, Submodule.subset_span ⟨a, rfl⟩⟩ ⟨j.val, h⟩ * (b ⟨j.val, h⟩).1 x else 0) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases h : j.val < r <;> simp [h]
    rw [hsplit]
    refine Finset.sum_nbij (fun k : Fin r => (⟨k.val, Nat.lt_of_lt_of_le k.isLt hr⟩ : Fin d))
      ?_ ?_ ?_ ?_
    · intro k _; simp [k.isLt]
    · intro k1 _ k2 _ h; dsimp only at h; have hv := congrArg Fin.val h; exact Fin.ext hv
    · intro j hj
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact ⟨⟨j.val, hj⟩, Finset.mem_coe.mpr (Finset.mem_univ _), Fin.ext rfl⟩
    · intro k _; simp [k.isLt]

lemma rowRank_le_iff {α β : Type*} [Finite α] [Finite β]
    (M : α → β → ℚ) (d : ℕ) : rowRank M ≤ d ↔ HasRankLe M d :=
  (hasRankLe_iff_rowRank_le M d).symm

lemma rowRank_eq_of_iff {α₁ β₁ α₂ β₂ : Type*} [Finite α₁] [Finite β₁] [Finite α₂] [Finite β₂]
    (M₁ : α₁ → β₁ → ℚ) (M₂ : α₂ → β₂ → ℚ)
    (h : ∀ d, HasRankLe M₁ d ↔ HasRankLe M₂ d) : rowRank M₁ = rowRank M₂ := by
  have h1 : rowRank M₁ ≤ rowRank M₂ := (hasRankLe_iff_rowRank_le M₁ _).mp ((h _).mpr ((hasRankLe_iff_rowRank_le M₂ _).mpr le_rfl))
  have h2 : rowRank M₂ ≤ rowRank M₁ := (hasRankLe_iff_rowRank_le M₂ _).mp ((h _).mp ((hasRankLe_iff_rowRank_le M₁ _).mpr le_rfl))
  exact le_antisymm h1 h2

lemma rowRank_transpose {α β : Type*} [Finite α] [Finite β] (M : α → β → ℚ) :
    rowRank (fun b a => M a b) = rowRank M := by
  apply rowRank_eq_of_iff
  intro d
  constructor
  · rintro ⟨f, g, h⟩
    exact ⟨g, f, fun a b => by rw [show M a b = ∑ j, f j b * g j a from h b a]; refine Finset.sum_congr rfl fun j _ => mul_comm _ _⟩
  · rintro ⟨f, g, h⟩
    exact ⟨g, f, fun a b => by dsimp only; rw [h b a]; refine Finset.sum_congr rfl fun j _ => mul_comm _ _⟩

lemma hasRankLe_reindex {α₁ β₁ α₂ β₂ : Type*} (e1 : α₁ ≃ α₂) (e2 : β₁ ≃ β₂)
    (M : α₂ → β₂ → ℚ) (d : ℕ) :
    HasRankLe (fun a b => M (e1 a) (e2 b)) d ↔ HasRankLe M d := by
  constructor
  · rintro ⟨f, g, h⟩
    exact ⟨fun j a => f j (e1.symm a), fun j b => g j (e2.symm b), fun a b => by simpa using h (e1.symm a) (e2.symm b)⟩
  · rintro ⟨f, g, h⟩
    exact ⟨fun j a => f j (e1 a), fun j b => g j (e2 b), fun a b => h (e1 a) (e2 b)⟩

lemma rowRank_reindex {α₁ β₁ α₂ β₂ : Type*} [Finite α₁] [Finite β₁] [Finite α₂] [Finite β₂]
    (e1 : α₁ ≃ α₂) (e2 : β₁ ≃ β₂) (M : α₂ → β₂ → ℚ) :
    rowRank (fun a b => M (e1 a) (e2 b)) = rowRank M :=
  rowRank_eq_of_iff _ _ (hasRankLe_reindex e1 e2 M)

lemma hasRankLe_mul_left {α α' β : Type*} [Fintype α]
    (P : α' → α → ℚ) (M : α → β → ℚ) {d : ℕ} (h : HasRankLe M d) :
    HasRankLe (fun a' b => ∑ a, P a' a * M a b) d := by
  rcases h with ⟨f, g, hfg⟩
  refine ⟨fun j a' => ∑ a, P a' a * f j a, g, fun a' b => ?_⟩
  simp_rw [hfg, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => by ring

lemma hasRankLe_mul_right {α β β' : Type*} [Fintype β]
    (M : α → β → ℚ) (Q : β → β' → ℚ) {d : ℕ} (h : HasRankLe M d) :
    HasRankLe (fun a b' => ∑ b, M a b * Q b b') d := by
  rcases h with ⟨f, g, hfg⟩
  refine ⟨f, fun j b' => ∑ b, g j b * Q b b', fun a b' => ?_⟩
  simp_rw [hfg, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => by ring

lemma rowRank_diag_left {α β : Type*} [Finite α] [Finite β]
    (c : α → ℚ) (hc : ∀ a, c a ≠ 0) (M : α → β → ℚ) :
    rowRank (fun a b => c a * M a b) = rowRank M := by
  apply rowRank_eq_of_iff
  intro d
  constructor
  · rintro ⟨f, g, h⟩
    refine ⟨fun j a => (c a)⁻¹ * f j a, g, fun a b => ?_⟩
    have h1 : c a * M a b = ∑ j, f j a * g j b := h a b
    calc M a b = (c a)⁻¹ * (c a * M a b) := by rw [← mul_assoc, inv_mul_cancel₀ (hc a), one_mul]
      _ = (c a)⁻¹ * ∑ j, f j a * g j b := by rw [h1]
      _ = ∑ j, ((c a)⁻¹ * f j a) * g j b := by rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
  · rintro ⟨f, g, h⟩
    refine ⟨fun j a => c a * f j a, g, fun a b => ?_⟩
    dsimp only
    rw [h a b, Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring

lemma rowRank_diag_right {α β : Type*} [Finite α] [Finite β]
    (c : β → ℚ) (hc : ∀ b, c b ≠ 0) (M : α → β → ℚ) :
    rowRank (fun a b => M a b * c b) = rowRank M := by
  rw [← rowRank_transpose (fun a b => M a b * c b), ← rowRank_transpose M]
  have hEq : (fun b a => M a b * c b) = (fun b a => c b * M a b) := by ext b a; ring
  rw [hEq]
  exact rowRank_diag_left c hc (fun b a => M a b)

lemma exists_li_rows {α β : Type*} [Finite α] [Finite β] (M : α → β → ℚ) :
    ∃ (r : ℕ) (idx : Fin r → α), r = rowRank M ∧ LinearIndependent ℚ (fun i => M (idx i)) := by
  classical
  obtain ⟨s, hs_sub, hs_span, hs_li⟩ := exists_linearIndependent ℚ (Set.range M)
  have hfin_s : s.Finite := (Set.finite_range M).subset hs_sub
  letI : Fintype s := hfin_s.fintype
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  have hcard : Fintype.card s = rowRank M := by
    unfold rowRank
    rw [← hs_span]
    have h1 := finrank_span_eq_card hs_li
    rw [Subtype.range_coe] at h1
    exact h1.symm
  have hchoose : ∀ i : Fin (Fintype.card s), ∃ a : α, M a = (e i).1 := fun i => hs_sub (e i).2
  choose idx hidx using hchoose
  refine ⟨Fintype.card s, idx, hcard, ?_⟩
  have hfun : (fun i => M (idx i)) = (fun i => (e i).1) := funext hidx
  rw [hfun]
  exact hs_li.comp e e.injective

lemma rowRank_ge_of_li {α β : Type*} [Finite α] [Finite β] {r : ℕ}
    (M : α → β → ℚ) (idx : Fin r → α) (hli : LinearIndependent ℚ (fun i => M (idx i))) :
    r ≤ rowRank M := by
  have hsub : Submodule.span ℚ (Set.range (fun i => M (idx i))) ≤ Submodule.span ℚ (Set.range M) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨idx i, rfl⟩
  calc r = Fintype.card (Fin r) := (Fintype.card_fin r).symm
    _ = Module.finrank ℚ (Submodule.span ℚ (Set.range (fun i => M (idx i)))) := (finrank_span_eq_card hli).symm
    _ ≤ rowRank M := Submodule.finrank_mono hsub

lemma rowRank_kronecker {α₁ β₁ α₂ β₂ : Type*} [Finite α₁] [Finite β₁] [Finite α₂] [Finite β₂]
    (M₁ : α₁ → β₁ → ℚ) (M₂ : α₂ → β₂ → ℚ) :
    rowRank (fun (p : α₁ × α₂) (q : β₁ × β₂) => M₁ p.1 q.1 * M₂ p.2 q.2) = rowRank M₁ * rowRank M₂ := by
  classical
  apply le_antisymm
  · rw [rowRank_le_iff]
    obtain ⟨f₁, g₁, h1⟩ := (hasRankLe_iff_rowRank_le M₁ _).mpr le_rfl
    obtain ⟨f₂, g₂, h2⟩ := (hasRankLe_iff_rowRank_le M₂ _).mpr le_rfl
    let e : Fin (rowRank M₁) × Fin (rowRank M₂) ≃ Fin (rowRank M₁ * rowRank M₂) := finProdFinEquiv
    refine ⟨fun j p => f₁ (e.symm j).1 p.1 * f₂ (e.symm j).2 p.2,
            fun j q => g₁ (e.symm j).1 q.1 * g₂ (e.symm j).2 q.2, ?_⟩
    intro p q
    dsimp only
    rw [h1 p.1 q.1, h2 p.2 q.2, Finset.sum_mul_sum, ← Fintype.sum_prod_type']
    rw [← Equiv.sum_comp e.symm]
    refine Finset.sum_congr rfl fun j _ => by ring
  · obtain ⟨r₁, idx₁, hr₁, hli₁⟩ := exists_li_rows M₁
    obtain ⟨r₂, idx₂, hr₂, hli₂⟩ := exists_li_rows M₂
    let e : Fin (r₁ * r₂) ≃ Fin r₁ × Fin r₂ := finProdFinEquiv.symm
    let idx : Fin (r₁ * r₂) → α₁ × α₂ := fun k => (idx₁ (e k).1, idx₂ (e k).2)
    have hli : LinearIndependent ℚ (fun k : Fin (r₁ * r₂) =>
        (fun q : β₁ × β₂ => M₁ (idx k).1 q.1 * M₂ (idx k).2 q.2)) := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      have hpt : ∀ (b₁ : β₁) (b₂ : β₂),
          ∑ i : Fin r₁, (∑ j : Fin r₂, c (e.symm (i, j)) * M₂ (idx₂ j) b₂) * M₁ (idx₁ i) b₁ = 0 := by
        intro b₁ b₂
        have h0 := congrFun hc (b₁, b₂)
        simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at h0
        rw [← Equiv.sum_comp e.symm] at h0
        rw [Fintype.sum_prod_type] at h0
        rw [← h0]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => by simp [idx]; ring
      have h1 : ∀ (b₂ : β₂) (i : Fin r₁), ∑ j : Fin r₂, c (e.symm (i, j)) * M₂ (idx₂ j) b₂ = 0 := by
        intro b₂
        have hlin : ∑ i : Fin r₁, (∑ j : Fin r₂, c (e.symm (i, j)) * M₂ (idx₂ j) b₂) • M₁ (idx₁ i) = 0 := by
          ext b₁; simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]; exact hpt b₁ b₂
        exact Fintype.linearIndependent_iff.mp hli₁ _ hlin
      have h2 : ∀ (i : Fin r₁) (j : Fin r₂), c (e.symm (i, j)) = 0 := by
        intro i
        have hlin : ∑ j : Fin r₂, c (e.symm (i, j)) • M₂ (idx₂ j) = 0 := by
          ext b₂; simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]; exact h1 b₂ i
        exact Fintype.linearIndependent_iff.mp hli₂ _ hlin
      intro k
      have hk := h2 (e k).1 (e k).2
      simpa using hk
    rw [← hr₁, ← hr₂]
    exact rowRank_ge_of_li _ idx hli

lemma rowRank_blockDiag_bool {α β : Type*} [Finite α] [Finite β]
    (N0 N1 : α → β → ℚ) :
    rowRank (fun (p : Bool × α) (q : Bool × β) =>
      if p.1 = q.1 then (if p.1 then N1 p.2 q.2 else N0 p.2 q.2) else 0) =
      rowRank N0 + rowRank N1 := by
  classical
  let M : Bool × α → Bool × β → ℚ := fun p q =>
    if p.1 = q.1 then (if p.1 then N1 p.2 q.2 else N0 p.2 q.2) else 0
  apply le_antisymm
  · rw [rowRank_le_iff]
    obtain ⟨f0, g0, h0⟩ := (hasRankLe_iff_rowRank_le N0 _).mpr le_rfl
    obtain ⟨f1, g1, h1⟩ := (hasRankLe_iff_rowRank_le N1 _).mpr le_rfl
    let r0 := rowRank N0
    let r1 := rowRank N1
    let e : Fin r0 ⊕ Fin r1 ≃ Fin (r0 + r1) := finSumFinEquiv
    refine ⟨fun j p => match e.symm j with
              | Sum.inl k => if p.1 = false then f0 k p.2 else 0
              | Sum.inr k => if p.1 = true then f1 k p.2 else 0,
            fun j q => match e.symm j with
              | Sum.inl k => if q.1 = false then g0 k q.2 else 0
              | Sum.inr k => if q.1 = true then g1 k q.2 else 0, ?_⟩
    intro p q
    dsimp only [M]
    rw [← Equiv.sum_comp e]
    simp only [Equiv.symm_apply_apply, Fintype.sum_sum_type]
    rcases p with ⟨bp, a⟩; rcases q with ⟨bq, b⟩
    cases bp <;> cases bq <;> simp [h0, h1, r0, r1]
  · obtain ⟨r0, idx0, hr0, hli0⟩ := exists_li_rows N0
    obtain ⟨r1, idx1, hr1, hli1⟩ := exists_li_rows N1
    let e : Fin (r0 + r1) ≃ Fin r0 ⊕ Fin r1 := finSumFinEquiv.symm
    let idx : Fin (r0 + r1) → Bool × α := fun k =>
      match e k with
      | Sum.inl i => (false, idx0 i)
      | Sum.inr j => (true, idx1 j)
    have hli : LinearIndependent ℚ (fun k : Fin (r0 + r1) => M (idx k)) := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      have h0 : ∀ i : Fin r0, c (e.symm (Sum.inl i)) = 0 := by
        have hlin : ∑ i : Fin r0, c (e.symm (Sum.inl i)) • N0 (idx0 i) = 0 := by
          ext b
          have := congrFun hc (false, b)
          simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at this ⊢
          rw [← Equiv.sum_comp e.symm, Fintype.sum_sum_type] at this
          simpa [idx, M] using this
        exact Fintype.linearIndependent_iff.mp hli0 _ hlin
      have h1 : ∀ j : Fin r1, c (e.symm (Sum.inr j)) = 0 := by
        have hlin : ∑ j : Fin r1, c (e.symm (Sum.inr j)) • N1 (idx1 j) = 0 := by
          ext b
          have := congrFun hc (true, b)
          simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at this ⊢
          rw [← Equiv.sum_comp e.symm, Fintype.sum_sum_type] at this
          simpa [idx, M] using this
        exact Fintype.linearIndependent_iff.mp hli1 _ hlin
      intro k
      cases h : e k with
      | inl i => have := h0 i; rw [← h, Equiv.symm_apply_apply] at this; exact this
      | inr j => have := h1 j; rw [← h, Equiv.symm_apply_apply] at this; exact this
    rw [← hr0, ← hr1]
    exact rowRank_ge_of_li M idx hli

-- Lower-triangular nonzero diagonal on Finset subtypes gives full row rank.
lemma li_lower_tri_finset {γ : Type*} [DecidableEq γ] {P : Finset γ → Prop} [Fintype {s : Finset γ // P s}]
    (M : {s : Finset γ // P s} → {s : Finset γ // P s} → ℚ)
    (htri : ∀ x y, M x y ≠ 0 → y.1 ⊆ x.1)
    (hdiag : ∀ x, M x x ≠ 0) :
    LinearIndependent ℚ M := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra hne
  push_neg at hne
  let supp := Finset.univ.filter (fun x => c x ≠ 0)
  have hne_supp : supp.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩
  obtain ⟨m, hm_mem, hm_max⟩ := Finset.exists_max_image supp (fun x => x.1.card) hne_supp
  have hm_ne : c m ≠ 0 := (Finset.mem_filter.mp hm_mem).2
  have hval := congrFun hc m
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hval
  have honly : ∀ x : {s : Finset γ // P s}, x ≠ m → c x * M x m = 0 := by
    intro x hxm
    by_cases hcx : c x = 0
    · rw [hcx, zero_mul]
    · by_contra hmul
      have hM : M x m ≠ 0 := right_ne_zero_of_mul hmul
      have hsub : m.1 ⊆ x.1 := htri x m hM
      have hle : x.1.card ≤ m.1.card := hm_max x (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hcx⟩)
      have heq : m.1 = x.1 := Finset.eq_of_subset_of_card_le hsub hle
      exact hxm (Subtype.ext heq.symm)
  rw [Finset.sum_eq_single m (fun x _ hxm => honly x hxm) (fun hm => absurd (Finset.mem_univ m) hm)] at hval
  exact mul_ne_zero hm_ne (hdiag m) hval

lemma rowRank_const_one {α β : Type*} [Finite α] [Finite β] [Nonempty α] [Nonempty β] :
    rowRank (fun (_ : α) (_ : β) => (1 : ℚ)) = 1 := by
  apply le_antisymm
  · rw [rowRank_le_iff]
    exact ⟨fun _ _ => 1, fun _ _ => 1, fun _ _ => by simp⟩
  · obtain ⟨a0⟩ := ‹Nonempty α›
    obtain ⟨b0⟩ := ‹Nonempty β›
    have hli : LinearIndependent ℚ (fun (_ : Fin 1) => (fun (_ : β) => (1 : ℚ))) := by
      rw [Fintype.linearIndependent_iff]
      intro c hc i
      have h0 := congrFun hc b0
      fin_cases i
      simpa using h0
    exact rowRank_ge_of_li (fun (_ : α) (_ : β) => (1 : ℚ)) (fun _ => a0) hli

-- Section 2: Path matrix rank = 2^(m/2) for all m.

def edgeW (z : ℚ) (isSigma : Bool) (a b : Bool) : ℚ :=
  if isSigma then (if a ≠ b then z else 1) else (if a = b then z else 1)

lemma edgeW_ne_zero {z : ℚ} (hz : 0 < z) (isSigma a b : Bool) : edgeW z isSigma a b ≠ 0 := by
  unfold edgeW; split_ifs <;> linarith

lemma edgeW_comm (z : ℚ) (isSigma a b : Bool) : edgeW z isSigma a b = edgeW z isSigma b a := by
  unfold edgeW; cases isSigma <;> cases a <;> cases b <;> rfl

lemma edgeW_inv_exists {z : ℚ} (hz : 0 < z) (hz1 : z ≠ 1) (isSigma : Bool) :
    ∃ Winv : Bool → Bool → ℚ, ∀ a b : Bool, ∑ c : Bool, Winv a c * edgeW z isSigma c b = if a = b then 1 else 0 := by
  have hd : 1 - z ^ 2 ≠ 0 := by
    intro h
    have hfac : (1 - z) * (1 + z) = 0 := by linear_combination h
    rcases mul_eq_zero.mp hfac with h1 | h2
    · exact hz1 (by linarith)
    · linarith
  cases isSigma
  · refine ⟨fun a c => (if a = c then -z else 1) / (1 - z ^ 2), ?_⟩
    intro a b; cases a <;> cases b <;> simp [edgeW] <;> field_simp [hd] <;> ring
  · refine ⟨fun a c => (if a = c then 1 else -z) / (1 - z ^ 2), ?_⟩
    intro a b; cases a <;> cases b <;> simp [edgeW] <;> field_simp [hd] <;> ring

-- Canonical path matrix on m vertices: vertices 0..m-1 with alternating sides (even -> left, odd -> right)
-- and edge color at index t being (xor c0 (decide (t % 2 = 1))).
def pathVal {m : ℕ} (x : {t : Fin m // t.val % 2 = 0} → Bool)
    (w : {t : Fin m // t.val % 2 = 1} → Bool) (t : Fin m) : Bool :=
  if h : t.val % 2 = 0 then x ⟨t, h⟩ else w ⟨t, by omega⟩

def pathMat (m : ℕ) (c0 : Bool) (z : ℚ)
    (x : {t : Fin m // t.val % 2 = 0} → Bool)
    (w : {t : Fin m // t.val % 2 = 1} → Bool) : ℚ :=
  ∏ t : Fin m, if h : t.val + 1 < m then
    edgeW z (xor c0 (decide (t.val % 2 = 1))) (pathVal x w t) (pathVal x w ⟨t.val + 1, h⟩)
  else 1

lemma rowRank_pathMat (z : ℚ) (hz : 0 < z) (hz1 : z ≠ 1) :
    ∀ (m : ℕ) (c0 : Bool), rowRank (pathMat m c0 z) = 2 ^ (m / 2) := by
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro c0
    match m with
    | 0 =>
      have hconst : pathMat 0 c0 z = fun _ _ => (1 : ℚ) := by
        ext x w; unfold pathMat; simp
      rw [hconst, rowRank_const_one]; rfl
    | 1 =>
      have hconst : pathMat 1 c0 z = fun _ _ => (1 : ℚ) := by
        ext x w; unfold pathMat; rw [Fin.prod_univ_one]; simp
      rw [hconst, rowRank_const_one]; rfl
    | m' + 2 =>
      -- Peel vertices 0 (left) and 1 (right).
      let L' := {t : Fin m' // t.val % 2 = 0} → Bool
      let R' := {t : Fin m' // t.val % 2 = 1} → Bool
      let eL : Bool × L' ≃ ({t : Fin (m' + 2) // t.val % 2 = 0} → Bool) :=
        { toFun := fun p t => if h : t.1.val = 0 then p.1
            else p.2 ⟨⟨t.1.val - 2, by have := t.1.isLt; have := t.2; omega⟩, by dsimp; have := t.2; omega⟩
          invFun := fun x => (x ⟨⟨0, by omega⟩, by simp⟩,
            fun t => x ⟨⟨t.1.val + 2, by have := t.1.isLt; omega⟩, by dsimp; have := t.2; omega⟩)
          left_inv := fun ⟨a, x'⟩ => by
            ext
            · simp
            · rename_i t; simp
          right_inv := fun x => by
            ext ⟨⟨t, ht⟩, hmod⟩
            by_cases h0 : t = 0
            · subst h0; simp
            · simp only [h0, ↓reduceDIte]
              congr 1; apply Subtype.ext; apply Fin.ext; dsimp at hmod ⊢; omega }
      let eR : Bool × R' ≃ ({t : Fin (m' + 2) // t.val % 2 = 1} → Bool) :=
        { toFun := fun p t => if h : t.1.val = 1 then p.1
            else p.2 ⟨⟨t.1.val - 2, by have := t.1.isLt; have := t.2; omega⟩, by dsimp; have := t.2; omega⟩
          invFun := fun w => (w ⟨⟨1, by omega⟩, by simp⟩,
            fun t => w ⟨⟨t.1.val + 2, by have := t.1.isLt; omega⟩, by dsimp; have := t.2; omega⟩)
          left_inv := fun ⟨b, w'⟩ => by
            ext
            · simp
            · rename_i t
              have hne : t.1.val + 2 ≠ 1 := by omega
              simp [hne]
          right_inv := fun w => by
            ext ⟨⟨t, ht⟩, hmod⟩
            by_cases h1 : t = 1
            · subst h1; simp
            · simp only [h1, ↓reduceDIte]
              congr 1; apply Subtype.ext; apply Fin.ext; dsimp at hmod ⊢; omega }
      let bridge : Bool → L' → ℚ := fun b x' =>
        if h : 0 < m' then edgeW z (!c0) b (x' ⟨⟨0, h⟩, by simp⟩) else 1
      have hbridge_ne : ∀ b x', bridge b x' ≠ 0 := fun b x' => by
        dsimp [bridge]; split_ifs; exact edgeW_ne_zero hz _ _ _; exact one_ne_zero
      let M1 : Bool × L' → Bool × R' → ℚ := fun p q =>
        edgeW z c0 p.1 q.1 * bridge q.1 p.2 * pathMat m' c0 z p.2 q.2
      have hM1_eq : (fun p q => pathMat (m' + 2) c0 z (eL p) (eR q)) = M1 := by
        ext ⟨a, x'⟩ ⟨b, w'⟩
        unfold pathMat M1
        have hsplit : ∀ f : Fin (m' + 2) → ℚ,
            (∏ t : Fin (m' + 2), f t) = f ⟨0, by omega⟩ * (f ⟨1, by omega⟩ * ∏ t : Fin m', f ⟨t.val + 2, by omega⟩) := by
          intro f
          rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
          rfl
        rw [hsplit]
        have hf0 : (if h : (0 : ℕ) + 1 < m' + 2 then
            edgeW z (xor c0 (decide (0 % 2 = 1))) (pathVal (eL (a, x')) (eR (b, w')) ⟨0, by omega⟩)
              (pathVal (eL (a, x')) (eR (b, w')) ⟨0 + 1, h⟩) else 1) = edgeW z c0 a b := by
          have hlt : 0 + 1 < m' + 2 := by omega
          rw [dif_pos hlt]
          have h0 : pathVal (eL (a, x')) (eR (b, w')) ⟨0, by omega⟩ = a := by simp [pathVal, eL]
          have h1 : pathVal (eL (a, x')) (eR (b, w')) ⟨0 + 1, hlt⟩ = b := by simp [pathVal, eR]
          rw [h0, h1]; simp
        have hf1 : (if h : (1 : ℕ) + 1 < m' + 2 then
            edgeW z (xor c0 (decide (1 % 2 = 1))) (pathVal (eL (a, x')) (eR (b, w')) ⟨1, by omega⟩)
              (pathVal (eL (a, x')) (eR (b, w')) ⟨1 + 1, h⟩) else 1) = bridge b x' := by
          dsimp [bridge]
          by_cases hm' : 0 < m'
          · have hlt : 1 + 1 < m' + 2 := by omega
            rw [dif_pos hlt, dif_pos hm']
            have h1 : pathVal (eL (a, x')) (eR (b, w')) ⟨1, by omega⟩ = b := by simp [pathVal, eR]
            have h2 : pathVal (eL (a, x')) (eR (b, w')) ⟨2, hlt⟩ = x' ⟨⟨0, hm'⟩, by simp⟩ := by
              simp [pathVal, eL]
            change edgeW z _ (pathVal (eL (a, x')) (eR (b, w')) ⟨1, by omega⟩) (pathVal (eL (a, x')) (eR (b, w')) ⟨2, hlt⟩) = _
            rw [h1, h2]; simp
          · rw [dif_neg (by omega), dif_neg hm']
        have htail : (∏ t : Fin m', if h : (t.val + 2) + 1 < m' + 2 then
            edgeW z (xor c0 (decide ((t.val + 2) % 2 = 1)))
              (pathVal (eL (a, x')) (eR (b, w')) ⟨t.val + 2, by omega⟩)
              (pathVal (eL (a, x')) (eR (b, w')) ⟨(t.val + 2) + 1, h⟩) else 1) =
            ∏ t : Fin m', if h : t.val + 1 < m' then
              edgeW z (xor c0 (decide (t.val % 2 = 1)))
                (pathVal x' w' t) (pathVal x' w' ⟨t.val + 1, h⟩) else 1 := by
          refine Finset.prod_congr rfl fun t _ => ?_
          have hval : ∀ (k : ℕ) (hk : k < m'),
              pathVal (eL (a, x')) (eR (b, w')) ⟨k + 2, by omega⟩ = pathVal x' w' ⟨k, hk⟩ := by
            intro k hk
            unfold pathVal
            by_cases hmod : k % 2 = 0
            · have hmod2 : (k + 2) % 2 = 0 := by omega
              rw [dif_pos hmod2, dif_pos hmod]
              simp [eL]
            · have hmod2 : ¬ ((k + 2) % 2 = 0) := by omega
              rw [dif_neg hmod2, dif_neg hmod]
              have hne1 : k + 2 ≠ 1 := by omega
              simp [eR, hne1]
          by_cases hlt : t.val + 1 < m'
          · rw [dif_pos (by omega), dif_pos hlt]
            have hmod : (t.val + 2) % 2 = t.val % 2 := by omega
            rw [hmod, hval t.val t.isLt, hval (t.val + 1) hlt]
          · rw [dif_neg (by omega), dif_neg hlt]
        rw [hf0, hf1, htail, ← mul_assoc]; rfl
      rw [← rowRank_reindex eL eR (pathMat (m' + 2) c0 z), hM1_eq]
      -- Multiply M1 on left by Winv ⊗ I to get block diagonal!
      obtain ⟨Winv, hWinv⟩ := edgeW_inv_exists hz hz1 c0
      let M2 : Bool × L' → Bool × R' → ℚ := fun p q =>
        if p.1 = q.1 then bridge q.1 p.2 * pathMat m' c0 z p.2 q.2 else 0
      have hM1_eq_M2 : rowRank M1 = rowRank M2 := by
        apply rowRank_eq_of_iff
        intro d
        constructor
        · intro h
          have hmul := hasRankLe_mul_left (fun (p' p : Bool × L') => if p'.2 = p.2 then Winv p'.1 p.1 else 0) M1 h
          have hEq : (fun (p' : Bool × L') (q : Bool × R') =>
              ∑ p : Bool × L', (if p'.2 = p.2 then Winv p'.1 p.1 else 0) * M1 p q) = M2 := by
            ext ⟨a, x'⟩ ⟨b, w'⟩
            rw [Fintype.sum_prod_type]
            simp only [M1, M2]
            have hinner : ∀ c : Bool,
                (∑ x : L', (if x' = x then Winv a c else 0) * (edgeW z c0 c b * bridge b x * pathMat m' c0 z x w')) =
                Winv a c * edgeW z c0 c b * (bridge b x' * pathMat m' c0 z x' w') := by
              intro c
              rw [Finset.sum_eq_single x' (fun x _ hx => by simp [hx.symm]) (fun h => absurd (Finset.mem_univ x') h)]
              simp; ring
            simp_rw [hinner, ← Finset.sum_mul, hWinv a b]
            split_ifs <;> ring
          rwa [hEq] at hmul
        · intro h
          have hmul := hasRankLe_mul_left (fun (p' p : Bool × L') => if p'.2 = p.2 then edgeW z c0 p'.1 p.1 else 0) M2 h
          have hEq : (fun (p' : Bool × L') (q : Bool × R') =>
              ∑ p : Bool × L', (if p'.2 = p.2 then edgeW z c0 p'.1 p.1 else 0) * M2 p q) = M1 := by
            ext ⟨a, x'⟩ ⟨b, w'⟩
            rw [Fintype.sum_prod_type]
            simp only [M1, M2]
            have hinner : ∀ c : Bool,
                (∑ x : L', (if x' = x then edgeW z c0 a c else 0) * (if c = b then bridge b x * pathMat m' c0 z x w' else 0)) =
                if c = b then edgeW z c0 a c * bridge b x' * pathMat m' c0 z x' w' else 0 := by
              intro c
              rw [Finset.sum_eq_single x' (fun x _ hx => by simp [hx.symm]) (fun h => absurd (Finset.mem_univ x') h)]
              simp only [↓reduceIte]; split_ifs <;> ring
            simp_rw [hinner]
            simp
          rwa [hEq] at hmul
      rw [hM1_eq_M2]
      have hM2_form : M2 = (fun (p : Bool × L') (q : Bool × R') =>
          if p.1 = q.1 then (if p.1 then bridge true p.2 * pathMat m' c0 z p.2 q.2
            else bridge false p.2 * pathMat m' c0 z p.2 q.2) else 0) := by
        ext ⟨a, x'⟩ ⟨b, w'⟩; cases a <;> cases b <;> simp [M2]
      rw [hM2_form,
          rowRank_blockDiag_bool (fun x' w' => bridge false x' * pathMat m' c0 z x' w')
            (fun x' w' => bridge true x' * pathMat m' c0 z x' w'),
          rowRank_diag_left (bridge false) (hbridge_ne false),
          rowRank_diag_left (bridge true) (hbridge_ne true),
          ih m' (by omega) c0]
      have hdiv : (m' + 2) / 2 = m' / 2 + 1 := by omega
      rw [hdiv, pow_succ]; omega

-- Section 3: Cycle matrix rank = 3 * 2^(k - 2) for k ≥ 2.

def nextFin {k : ℕ} (hk : 0 < k) (j : Fin k) : Fin k :=
  ⟨(j.val + 1) % k, Nat.mod_lt _ hk⟩

def cycleMat (k : ℕ) (hk : 0 < k) (z : ℚ) (x w : Fin k → Bool) : ℚ :=
  ∏ j : Fin k, edgeW z true (x j) (w j) * edgeW z false (w j) (x (nextFin hk j))

def transSet {k : ℕ} (hk : 0 < k) (x : Fin k → Bool) : Finset (Fin k) :=
  Finset.univ.filter (fun j => x j ≠ x (nextFin hk j))

def signBool (b : Bool) : ℚ := if b then -1 else 1

def whEntry {k : ℕ} (w : Fin k → Bool) (S : Finset (Fin k)) : ℚ :=
  ∏ j ∈ S, signBool (w j)

lemma wh_orth {k : ℕ} (w₁ w₂ : Fin k → Bool) :
    (∑ S : Finset (Fin k), whEntry w₁ S * whEntry w₂ S) = if w₁ = w₂ then (2 : ℚ) ^ k else 0 := by
  have h1 : ∀ S : Finset (Fin k), whEntry w₁ S * whEntry w₂ S = ∏ j ∈ S, signBool (w₁ j) * signBool (w₂ j) :=
    fun S => by unfold whEntry; rw [Finset.prod_mul_distrib]
  simp_rw [h1]
  have h2 : (∑ S : Finset (Fin k), ∏ j ∈ S, signBool (w₁ j) * signBool (w₂ j)) =
      ∏ j : Fin k, (1 + signBool (w₁ j) * signBool (w₂ j)) := by
    rw [show (∏ j : Fin k, (1 + signBool (w₁ j) * signBool (w₂ j))) =
        ∏ j : Fin k, (signBool (w₁ j) * signBool (w₂ j) + 1) from
        Finset.prod_congr rfl fun j _ => add_comm _ _, Finset.prod_add]
    have hpow : (Finset.univ : Finset (Fin k)).powerset = Finset.univ := by ext S; simp
    rw [hpow]
    refine Finset.sum_congr rfl fun S _ => ?_
    simp
  rw [h2]
  by_cases hEq : w₁ = w₂
  · subst hEq; rw [if_pos rfl]
    have hpt : ∀ j : Fin k, (1 + signBool (w₁ j) * signBool (w₁ j)) = 2 := by
      intro j; cases w₁ j <;> norm_num [signBool]
    simp [hpt]
  · rw [if_neg hEq]
    obtain ⟨j0, hj0⟩ := Function.ne_iff.mp hEq
    refine Finset.prod_eq_zero (Finset.mem_univ j0) ?_
    cases h1 : w₁ j0 <;> cases h2 : w₂ j0 <;> simp_all [signBool]

lemma wh_transform_cycle {k : ℕ} (hk : 0 < k) (z : ℚ) (x : Fin k → Bool) (S : Finset (Fin k)) :
    (∑ w : Fin k → Bool, cycleMat k hk z x w * whEntry w S) =
    if S ⊆ transSet hk x then
      (2 * z) ^ (k - (transSet hk x).card) * (1 + z ^ 2) ^ ((transSet hk x).card - S.card) *
      (1 - z ^ 2) ^ S.card * ∏ j ∈ S, signBool (x j)
    else 0 := by
  have hprod : ∀ w : Fin k → Bool,
      cycleMat k hk z x w * whEntry w S =
      ∏ j : Fin k, edgeW z true (x j) (w j) * edgeW z false (w j) (x (nextFin hk j)) *
        (if j ∈ S then signBool (w j) else 1) := by
    intro w
    unfold cycleMat whEntry
    have h1 : (∏ j ∈ Finset.univ.filter (· ∈ S), if j ∈ S then signBool (w j) else 1) = ∏ j ∈ S, signBool (w j) := by
      rw [show Finset.univ.filter (· ∈ S) = S by ext j; simp]
      exact Finset.prod_congr rfl fun j hj => if_pos hj
    have h2 : (∏ j ∈ Finset.univ.filter (· ∉ S), if j ∈ S then signBool (w j) else 1) = 1 :=
      Finset.prod_eq_one fun j hj => if_neg (Finset.mem_filter.mp hj).2
    have h3 : (∏ j : Fin k, if j ∈ S then signBool (w j) else 1) = ∏ j ∈ S, signBool (w j) := by
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ S) (fun j => if j ∈ S then signBool (w j) else 1), h1, h2, mul_one]
    rw [← h3, ← Finset.prod_mul_distrib]
  simp_rw [hprod]
  rw [← Fintype.prod_sum (fun j b => edgeW z true (x j) b * edgeW z false b (x (nextFin hk j)) *
        (if j ∈ S then signBool b else 1))]
  have hfac : ∀ j : Fin k,
      (∑ b : Bool, edgeW z true (x j) b * edgeW z false b (x (nextFin hk j)) *
        (if j ∈ S then signBool b else 1)) =
      if j ∈ transSet hk x then
        if j ∈ S then (1 - z ^ 2) * signBool (x j) else 1 + z ^ 2
      else
        if j ∈ S then 0 else 2 * z := by
    intro j
    rw [Fintype.sum_bool]
    unfold transSet edgeW signBool
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    cases x j <;> cases x (nextFin hk j) <;> by_cases hj : j ∈ S <;> simp [hj] <;> ring
  simp_rw [hfac]
  by_cases hsub : S ⊆ transSet hk x
  · rw [if_pos hsub]
    let T := transSet hk x
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ T)]
    have hT : Finset.univ.filter (· ∈ T) = T := by ext j; simp
    have hTc : Finset.univ.filter (· ∉ T) = Finset.univ \ T := by ext j; simp
    rw [hT, hTc]
    have hpart1 : (∏ j ∈ Finset.univ \ T, if j ∈ T then
        (if j ∈ S then (1 - z ^ 2) * signBool (x j) else 1 + z ^ 2) else if j ∈ S then 0 else 2 * z) =
        (2 * z) ^ (k - T.card) := by
      have hpt : ∀ j ∈ Finset.univ \ T, (if j ∈ T then
          (if j ∈ S then (1 - z ^ 2) * signBool (x j) else 1 + z ^ 2) else if j ∈ S then 0 else 2 * z) = 2 * z := by
        intro j hj
        have hjT : j ∉ T := (Finset.mem_sdiff.mp hj).2
        have hjS : j ∉ S := fun h => hjT (hsub h)
        simp [hjT, hjS]
      rw [Finset.prod_congr rfl hpt, Finset.prod_const, Finset.card_sdiff, Finset.inter_univ,
          Finset.card_univ, Fintype.card_fin]
    have hpart2 : (∏ j ∈ T, if j ∈ T then
        (if j ∈ S then (1 - z ^ 2) * signBool (x j) else 1 + z ^ 2) else if j ∈ S then 0 else 2 * z) =
        (1 + z ^ 2) ^ (T.card - S.card) * (1 - z ^ 2) ^ S.card * ∏ j ∈ S, signBool (x j) := by
      have hpt : ∀ j ∈ T, (if j ∈ T then
          (if j ∈ S then (1 - z ^ 2) * signBool (x j) else 1 + z ^ 2) else if j ∈ S then 0 else 2 * z) =
          if j ∈ S then (1 - z ^ 2) * signBool (x j) else 1 + z ^ 2 := fun j hj => if_pos hj
      rw [Finset.prod_congr rfl hpt, ← Finset.prod_filter_mul_prod_filter_not T (· ∈ S)]
      have hTS : T.filter (· ∈ S) = S := by ext j; simp only [Finset.mem_filter, and_iff_right_iff_imp]; exact fun h => hsub h
      have hTSc : T.filter (· ∉ S) = T \ S := by ext j; simp
      rw [hTS, hTSc]
      have ha : (∏ j ∈ S, if j ∈ S then (1 - z ^ 2) * signBool (x j) else 1 + z ^ 2) =
          (1 - z ^ 2) ^ S.card * ∏ j ∈ S, signBool (x j) := by
        rw [Finset.prod_congr rfl fun j hj => if_pos hj, Finset.prod_mul_distrib, Finset.prod_const]
      have hb : (∏ j ∈ T \ S, if j ∈ S then (1 - z ^ 2) * signBool (x j) else 1 + z ^ 2) =
          (1 + z ^ 2) ^ (T.card - S.card) := by
        rw [Finset.prod_congr rfl fun j hj => if_neg (Finset.mem_sdiff.mp hj).2, Finset.prod_const,
            Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]
      rw [ha, hb]; ring
    rw [hpart1, hpart2]; ring
  · rw [if_neg hsub]
    rw [Finset.not_subset] at hsub
    obtain ⟨j0, hj0S, hj0T⟩ := hsub
    refine Finset.prod_eq_zero (Finset.mem_univ j0) ?_
    simp [hj0S, hj0T]

-- Sign of x at r when x 0 = false equals (-1)^|{t ∈ transSet x | t < r}|.
lemma signBool_of_transSet {k : ℕ} (hk : 0 < k) (x : Fin k → Bool) (hx0 : x ⟨0, hk⟩ = false) :
    ∀ r : Fin k, signBool (x r) = (-1 : ℚ) ^ ((transSet hk x).filter (· < r)).card := by
  intro ⟨r, hr⟩
  induction r with
  | zero =>
    have hempty : (transSet hk x).filter (· < ⟨0, hr⟩) = ∅ := by
      ext j; simp [Fin.lt_def]
    rw [hempty, Finset.card_empty, pow_zero]
    simp [hx0, signBool]
  | succ r ih =>
    have hr' : r < k := by omega
    have hprev := ih hr'
    have hfilt : (transSet hk x).filter (· < ⟨r + 1, hr⟩) =
        if ⟨r, hr'⟩ ∈ transSet hk x then insert ⟨r, hr'⟩ ((transSet hk x).filter (· < ⟨r, hr'⟩))
        else (transSet hk x).filter (· < ⟨r, hr'⟩) := by
      split_ifs with hmem
      · ext j; simp only [Finset.mem_filter, Finset.mem_insert, Fin.lt_def, Fin.ext_iff]
        constructor
        · rintro ⟨hjT, hjlt⟩
          by_cases heq : j.val = r
          · exact Or.inl heq
          · exact Or.inr ⟨hjT, by omega⟩
        · rintro (heq | ⟨hjT, hjlt⟩)
          · have : j = ⟨r, hr'⟩ := Fin.ext heq; rw [this]; exact ⟨hmem, by omega⟩
          · exact ⟨hjT, by omega⟩
      · ext j; simp only [Finset.mem_filter, Fin.lt_def]
        constructor
        · rintro ⟨hjT, hjlt⟩
          refine ⟨hjT, ?_⟩
          by_contra hge
          have heq : j = ⟨r, hr'⟩ := Fin.ext (by dsimp at hjlt hge ⊢; omega)
          rw [heq] at hjT; exact hmem hjT
        · rintro ⟨hjT, hjlt⟩; exact ⟨hjT, by omega⟩
    have hnext : nextFin hk ⟨r, hr'⟩ = ⟨r + 1, hr⟩ := by
      ext; simp [nextFin, Nat.mod_eq_of_lt hr]
    rw [hfilt]
    by_cases hmem : ⟨r, hr'⟩ ∈ transSet hk x
    · rw [if_pos hmem]
      have hnot : ⟨r, hr'⟩ ∉ (transSet hk x).filter (· < ⟨r, hr'⟩) := by simp
      rw [Finset.card_insert_of_notMem hnot, pow_succ, ← hprev]
      have hdiff : x ⟨r, hr'⟩ ≠ x ⟨r + 1, hr⟩ := by
        have := (Finset.mem_filter.mp hmem).2; rwa [hnext] at this
      cases h1 : x ⟨r, hr'⟩ <;> cases h2 : x ⟨r + 1, hr⟩
      · exact absurd (h1.trans h2.symm) hdiff
      · norm_num [signBool]
      · norm_num [signBool]
      · exact absurd (h1.trans h2.symm) hdiff
    · rw [if_neg hmem, ← hprev]
      have heq : x ⟨r, hr'⟩ = x ⟨r + 1, hr⟩ := by
        by_contra hne
        exact hmem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [hnext]⟩)
      rw [heq]

lemma even_transSet {k : ℕ} (hk : 0 < k) (x : Fin k → Bool) : Even (transSet hk x).card := by
  -- Flip x if x 0 = true (transSet is invariant under negation).
  have hneg : ∀ y : Fin k → Bool, transSet hk (fun j => !y j) = transSet hk y := by
    intro y; ext j; simp [transSet]
  suffices ∀ y : Fin k → Bool, y ⟨0, hk⟩ = false → Even (transSet hk y).card by
    cases h0 : x ⟨0, hk⟩
    · exact this x h0
    · rw [← hneg x]; exact this (fun j => !x j) (by simp [h0])
  intro y hy0
  let last : Fin k := ⟨k - 1, by omega⟩
  have hsign := signBool_of_transSet hk y hy0 last
  have hnext : nextFin hk last = ⟨0, hk⟩ := by
    ext; dsimp [nextFin, last]; rw [Nat.sub_add_cancel hk, Nat.mod_self]
  have hsplit : (transSet hk y).card =
      ((transSet hk y).filter (· < last)).card + (if last ∈ transSet hk y then 1 else 0) := by
    have hunion : transSet hk y = (transSet hk y).filter (· < last) ∪
        (if last ∈ transSet hk y then {last} else ∅) := by
      ext j
      split_ifs with hl
      · simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_singleton, Fin.lt_def, Fin.ext_iff]
        constructor
        · intro hj
          by_cases heq : j.val = k - 1
          · exact Or.inr heq
          · exact Or.inl ⟨hj, by have := j.isLt; dsimp [last]; omega⟩
        · rintro (⟨hj, _⟩ | heq)
          · exact hj
          · have : j = last := Fin.ext heq; rwa [this]
      · simp only [Finset.union_empty, Finset.mem_filter, iff_self_and, Fin.lt_def]
        intro hj
        by_contra hge
        have : j = last := Fin.ext (by have := j.isLt; dsimp [last] at hge ⊢; omega)
        exact hl (this ▸ hj)
    have hdisj : Disjoint ((transSet hk y).filter (· < last)) (if last ∈ transSet hk y then {last} else ∅) := by
      split_ifs <;> simp
    conv_lhs => rw [hunion]
    rw [Finset.card_union_of_disjoint hdisj]
    split_ifs <;> simp
  have hmem_last : last ∈ transSet hk y ↔ y last = true := by
    simp [transSet, hnext, hy0]
  rw [hsplit]
  cases hyl : y last
  · have hnl : last ∉ transSet hk y := by simp [hmem_last, hyl]
    rw [if_neg hnl, add_zero]
    rw [hyl] at hsign; simp only [signBool] at hsign
    have hne : (-1 : ℚ) ^ ((transSet hk y).filter (· < last)).card = 1 := hsign.symm
    rcases Nat.even_or_odd ((transSet hk y).filter (· < last)).card with he | ho
    · exact he
    · rw [Odd.neg_one_pow ho] at hne; norm_num at hne
  · have hl : last ∈ transSet hk y := by simp [hmem_last, hyl]
    rw [if_pos hl]
    rw [hyl] at hsign; simp only [signBool] at hsign
    have hne : (-1 : ℚ) ^ ((transSet hk y).filter (· < last)).card = -1 := hsign.symm
    rcases Nat.even_or_odd ((transSet hk y).filter (· < last)).card with he | ho
    · rw [Even.neg_one_pow he] at hne; norm_num at hne
    · exact ho.add_one

-- Bijection between {x : Fin k → Bool // x 0 = false} and {T : Finset (Fin k) // Even T.card}.
def transEquiv {k : ℕ} (hk : 0 < k) :
    {x : Fin k → Bool // x ⟨0, hk⟩ = false} ≃ {T : Finset (Fin k) // Even T.card} where
  toFun x := ⟨transSet hk x.1, even_transSet hk x.1⟩
  invFun T := ⟨fun r => decide (Odd (T.1.filter (· < r)).card), by
    have : T.1.filter (· < ⟨0, hk⟩) = ∅ := by ext j; simp [Fin.lt_def]
    simp [this]⟩
  left_inv := fun ⟨x, hx0⟩ => by
    apply Subtype.ext; ext r
    have hsign := signBool_of_transSet hk x hx0 r
    cases hxr : x r
    · rw [hxr] at hsign; simp only [signBool] at hsign
      have : ¬ Odd ((transSet hk x).filter (· < r)).card := by
        intro ho; rw [Odd.neg_one_pow ho] at hsign; norm_num at hsign
      simp [this, hxr]
    · rw [hxr] at hsign; simp only [signBool] at hsign
      have : Odd ((transSet hk x).filter (· < r)).card := by
        rcases Nat.even_or_odd ((transSet hk x).filter (· < r)).card with he | ho
        · rw [Even.neg_one_pow he] at hsign; norm_num at hsign
        · exact ho
      simp [this, hxr]
  right_inv := fun ⟨T, hTeven⟩ => by
    apply Subtype.ext; ext j
    simp only [transSet, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hlt : j.val + 1 < k
    · have hnext : nextFin hk j = ⟨j.val + 1, hlt⟩ := by ext; simp [nextFin, Nat.mod_eq_of_lt hlt]
      rw [hnext]
      have hcard : (T.filter (· < ⟨j.val + 1, hlt⟩)).card =
          (T.filter (· < j)).card + (if j ∈ T then 1 else 0) := by
        have hstep : T.filter (· < ⟨j.val + 1, hlt⟩) =
            if j ∈ T then insert j (T.filter (· < j)) else T.filter (· < j) := by
          split_ifs with hj
          · ext t; simp only [Finset.mem_filter, Finset.mem_insert, Fin.lt_def, Fin.ext_iff]
            constructor
            · rintro ⟨htT, htlt⟩
              by_cases heq : t.val = j.val
              · exact Or.inl heq
              · exact Or.inr ⟨htT, by omega⟩
            · rintro (heq | ⟨htT, htlt⟩)
              · have : t = j := Fin.ext heq; rw [this]; exact ⟨hj, by omega⟩
              · exact ⟨htT, by omega⟩
          · ext t; simp only [Finset.mem_filter, Fin.lt_def]
            constructor
            · rintro ⟨htT, htlt⟩
              refine ⟨htT, ?_⟩
              by_contra hge
              exact hj ((Fin.ext (by omega) : t = j) ▸ htT)
            · rintro ⟨htT, htlt⟩; exact ⟨htT, by omega⟩
        rw [hstep]
        split_ifs with hj
        · rw [Finset.card_insert_of_notMem (by simp)]
        · simp
      rw [hcard]
      by_cases hj : j ∈ T
      · simp only [hj, ↓reduceIte, iff_true]
        intro hEq
        have hiff : Odd (T.filter (· < j)).card ↔ Odd ((T.filter (· < j)).card + 1) := by
          simpa using congrArg (· = true) hEq
        rcases Nat.even_or_odd (T.filter (· < j)).card with he | ho
        · exact (Nat.not_odd_iff_even.mpr he) (hiff.mpr he.add_one)
        · exact (Nat.not_odd_iff_even.mpr ho.add_one) (hiff.mp ho)
      · simp [hj]
    · have hj_last : j = ⟨k - 1, by omega⟩ := Fin.ext (by have := j.isLt; dsimp; omega)
      have hnext : nextFin hk j = ⟨0, hk⟩ := by
        ext; rw [hj_last]; dsimp [nextFin]; rw [Nat.sub_add_cancel hk, Nat.mod_self]
      rw [hnext]
      have h0 : T.filter (· < ⟨0, hk⟩) = ∅ := by ext t; simp [Fin.lt_def]
      rw [h0, Finset.card_empty]
      have hcard : T.card = (T.filter (· < j)).card + (if j ∈ T then 1 else 0) := by
        have hunion : T = T.filter (· < j) ∪ (if j ∈ T then {j} else ∅) := by
          ext t; rw [hj_last]
          split_ifs with hj
          · simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_singleton, Fin.lt_def, Fin.ext_iff]
            constructor
            · intro ht
              by_cases heq : t.val = k - 1
              · exact Or.inr heq
              · exact Or.inl ⟨ht, by have := t.isLt; omega⟩
            · rintro (⟨ht, _⟩ | heq)
              · exact ht
              · exact (Fin.ext heq : t = ⟨k - 1, by omega⟩) ▸ hj
          · simp only [Finset.union_empty, Finset.mem_filter, iff_self_and, Fin.lt_def]
            intro ht
            by_contra hge
            exact hj ((Fin.ext (by have := t.isLt; dsimp at hge ⊢; omega) : t = ⟨k - 1, by omega⟩) ▸ ht)
        have hdisj : Disjoint (T.filter (· < j)) (if j ∈ T then {j} else ∅) := by split_ifs <;> simp
        conv_lhs => rw [hunion]
        rw [Finset.card_union_of_disjoint hdisj]; split_ifs <;> simp
      by_cases hj : j ∈ T
      · rw [if_pos hj] at hcard
        have hodd : Odd (T.filter (· < j)).card := by
          rcases hTeven with ⟨m, hm⟩; exact ⟨m - 1, by omega⟩
        simp [hj, hodd]
      · rw [if_neg hj, add_zero] at hcard
        have heven : ¬ Odd (T.filter (· < j)).card := by
          rw [← hcard]; exact Nat.not_odd_iff_even.mpr hTeven
        simp [hj, heven]

-- Alternating sum over an even-cardinality Finset (Fin k) is 0.
lemma alt_sum_even_finset {k : ℕ} (U : Finset (Fin k)) (hU : Even U.card) :
    (∑ r ∈ U, (-1 : ℚ) ^ (U.filter (· < r)).card) = 0 := by
  let f : Fin U.card ≃o U := U.orderIsoOfFin rfl
  have hcard : ∀ i : Fin U.card, (U.filter (· < (f i).1)).card = i.val := by
    intro i
    have hset : U.filter (· < (f i).1) = (Finset.univ.filter (· < i)).image (fun j => (f j).1) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hrU, hrlt⟩
        refine ⟨f.symm ⟨r, hrU⟩, ?_, by simp⟩
        have hlt : f (f.symm ⟨r, hrU⟩) < f i := by
          rw [f.apply_symm_apply]
          exact Subtype.mk_lt_mk.mpr hrlt
        exact (f.lt_iff_lt).mp hlt
      · rintro ⟨j, hjlt, rfl⟩
        exact ⟨(f j).2, (f.lt_iff_lt).mpr hjlt⟩
    rw [hset, Finset.card_image_of_injective _ (fun a b hab => f.injective (Subtype.ext hab))]
    have : (Finset.univ.filter (fun j : Fin U.card => j < i)).card = i.val := by
      have hbi : (Finset.univ.filter (fun j : Fin U.card => j < i)).card = (Finset.range i.val).card := by
        refine Finset.card_nbij (fun j => j.val) ?_ ?_ ?_
        · intro j hj; simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at hj; exact Finset.mem_coe.mpr (Finset.mem_range.mpr hj)
        · intro a _ b _ h; exact Fin.ext h
        · intro m hm
          have hmlt : m < i.val := Finset.mem_range.mp (Finset.mem_coe.mp hm)
          exact ⟨⟨m, Nat.lt_trans hmlt i.isLt⟩,
            Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.lt_def.mpr hmlt⟩), rfl⟩
      rw [hbi, Finset.card_range]
    exact this
  have hsum : (∑ r ∈ U, (-1 : ℚ) ^ (U.filter (· < r)).card) = ∑ i : Fin U.card, (-1 : ℚ) ^ i.val := by
    refine (Finset.sum_nbij (fun i : Fin U.card => (f i).1) ?_ ?_ ?_ ?_).symm
    · intro i _; exact (f i).2
    · intro a _ b _ h; exact f.injective (Subtype.ext h)
    · intro r hr; exact ⟨f.symm ⟨r, hr⟩, Finset.mem_coe.mpr (Finset.mem_univ _), by simp⟩
    · intro i _; rw [hcard i]
  rw [hsum, Fin.sum_univ_eq_sum_range (fun n => (-1 : ℚ) ^ n) U.card]
  rcases hU with ⟨m, hm⟩
  rw [hm]
  clear hm hsum hcard f U
  induction m with
  | zero => simp
  | succ m ih =>
    have h2 : m + 1 + (m + 1) = (m + m) + 2 := by omega
    rw [h2, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have hev : Even (m + m) := ⟨m, rfl⟩
    rw [Even.neg_one_pow hev, Odd.neg_one_pow hev.add_one]
    ring

lemma card_even_finset (k : ℕ) (hk : 1 ≤ k) :
    Fintype.card {T : Finset (Fin k) // Even T.card} = 2 ^ (k - 1) := by
  have hk0 : 0 < k := by omega
  rw [← Fintype.card_congr (transEquiv hk0)]
  let e : {x : Fin k → Bool // x ⟨0, hk0⟩ = false} ≃ (Fin (k - 1) → Bool) :=
    { toFun := fun x i => x.1 ⟨i.val + 1, by omega⟩
      invFun := fun y => ⟨fun j => if h : j.val = 0 then false else y ⟨j.val - 1, by omega⟩, by simp⟩
      left_inv := fun ⟨x, hx0⟩ => by
        apply Subtype.ext; ext j
        dsimp only
        by_cases hj : j.val = 0
        · have h0 : j = ⟨0, hk0⟩ := Fin.ext hj
          rw [h0, dif_pos rfl, hx0]
        · simp only [hj, ↓reduceDIte]
          congr 1; ext; dsimp; omega
      right_inv := fun y => by ext i; simp }
  rw [Fintype.card_congr e]
  simp

lemma card_odd_finset_no_last (k : ℕ) (hk : 2 ≤ k) :
    Fintype.card {S : Finset (Fin k) // Odd S.card ∧ (⟨k - 1, by omega⟩ : Fin k) ∉ S} = 2 ^ (k - 2) := by
  let last : Fin k := ⟨k - 1, by omega⟩
  let emb : Fin (k - 1) → Fin k := fun j => ⟨j.val, by omega⟩
  have hemb_inj : Function.Injective emb := fun a b h => by have hv := congrArg Fin.val h; exact Fin.ext hv
  let e1 : {S : Finset (Fin k) // Odd S.card ∧ last ∉ S} ≃ {S : Finset (Fin (k - 1)) // Odd S.card} :=
    { toFun := fun S => ⟨Finset.univ.filter (fun j : Fin (k - 1) => emb j ∈ S.1), by
        have himg : (Finset.univ.filter (fun j : Fin (k - 1) => emb j ∈ S.1)).image emb = S.1 := by
          ext x
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨j, hj, rfl⟩; exact hj
          · intro hx
            have hne : x ≠ last := fun h => S.2.2 (h ▸ hx)
            have hlt : x.val < k - 1 := by have := x.isLt; have : x.val ≠ k - 1 := fun hv => hne (Fin.ext hv); omega
            exact ⟨⟨x.val, hlt⟩, by simpa [emb] using hx, Fin.ext rfl⟩
        have hcard : (Finset.univ.filter (fun j : Fin (k - 1) => emb j ∈ S.1)).card = S.1.card := by
          rw [← Finset.card_image_of_injective _ hemb_inj, himg]
        rw [hcard]; exact S.2.1⟩
      invFun := fun S => ⟨S.1.image emb, by
        refine ⟨by rw [Finset.card_image_of_injective _ hemb_inj]; exact S.2, ?_⟩
        simp only [Finset.mem_image, not_exists, not_and]
        intro j _ hEq
        have := congrArg Fin.val hEq; dsimp [emb, last] at this; omega⟩
      left_inv := fun ⟨S, hodd, hnl⟩ => by
        apply Subtype.ext; ext x
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨j, hj, rfl⟩; exact hj
        · intro hx
          have hne : x ≠ last := fun h => hnl (h ▸ hx)
          have hlt : x.val < k - 1 := by have := x.isLt; have : x.val ≠ k - 1 := fun hv => hne (Fin.ext hv); omega
          exact ⟨⟨x.val, hlt⟩, by simpa [emb] using hx, Fin.ext rfl⟩
      right_inv := fun ⟨S, hodd⟩ => by
        apply Subtype.ext; ext j
        simp [hemb_inj.eq_iff] }
  rw [Fintype.card_congr e1]
  -- Bijection between odd subsets and even subsets of Fin (k - 1) by toggling 0!
  let z0 : Fin (k - 1) := ⟨0, by omega⟩
  let e2 : {S : Finset (Fin (k - 1)) // Odd S.card} ≃ {S : Finset (Fin (k - 1)) // Even S.card} :=
    { toFun := fun S => ⟨if z0 ∈ S.1 then S.1.erase z0 else insert z0 S.1, by
        split_ifs with h0
        · rw [Finset.card_erase_of_mem h0]; rcases S.2 with ⟨m, hm⟩; exact ⟨m, by omega⟩
        · rw [Finset.card_insert_of_notMem h0]; exact S.2.add_one⟩
      invFun := fun S => ⟨if z0 ∈ S.1 then S.1.erase z0 else insert z0 S.1, by
        split_ifs with h0
        · rw [Finset.card_erase_of_mem h0]; rcases S.2 with ⟨m, hm⟩
          have hpos : 0 < S.1.card := Finset.card_pos.mpr ⟨z0, h0⟩
          exact ⟨m - 1, by omega⟩
        · rw [Finset.card_insert_of_notMem h0]; exact S.2.add_one⟩
      left_inv := fun ⟨S, _⟩ => by
        apply Subtype.ext; dsimp
        by_cases h1 : z0 ∈ S
        · simp [h1, Finset.insert_erase h1]
        · simp [h1, Finset.erase_insert h1]
      right_inv := fun ⟨S, _⟩ => by
        apply Subtype.ext; dsimp
        by_cases h1 : z0 ∈ S
        · simp [h1, Finset.insert_erase h1]
        · simp [h1, Finset.erase_insert h1] }
  rw [Fintype.card_congr e2, card_even_finset (k - 1) (by omega)]
  exact congrArg (2 ^ ·) (by omega)

set_option maxHeartbeats 800000 in
lemma rowRank_cycleMat (k : ℕ) (hk : 2 ≤ k) (z : ℚ) (hz : 0 < z) (hz1 : z ≠ 1) :
    rowRank (cycleMat k (by omega) z) = 3 * 2 ^ (k - 2) := by
  classical
  have hk0 : 0 < k := by omega
  have hz_ne : z ≠ 0 := ne_of_gt hz
  have h2z_ne : 2 * z ≠ 0 := mul_ne_zero (by norm_num) hz_ne
  have h1pz2_ne : 1 + z ^ 2 ≠ 0 := by nlinarith
  have h1mz2_ne : 1 - z ^ 2 ≠ 0 := by
    intro h
    have : (1 - z) * (1 + z) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h1 | h2 <;> [exact hz1 (by linarith); linarith]
  -- Step 1: Walsh-Hadamard transform on columns gives A(x, S) with rowRank (cycleMat) = rowRank A.
  let A : (Fin k → Bool) → Finset (Fin k) → ℚ := fun x S =>
    ∑ w : Fin k → Bool, cycleMat k hk0 z x w * whEntry w S
  have hrank_A : rowRank (cycleMat k hk0 z) = rowRank A := by
    apply rowRank_eq_of_iff
    intro d
    constructor
    · intro h; exact hasRankLe_mul_right (cycleMat k hk0 z) whEntry h
    · intro h
      have hmul := hasRankLe_mul_right A (fun S w => whEntry w S / (2 : ℚ) ^ k) h
      have hEq : (fun x w => ∑ S : Finset (Fin k), A x S * (whEntry w S / (2 : ℚ) ^ k)) = cycleMat k hk0 z := by
        ext x w
        simp only [A, Finset.sum_mul]
        rw [Finset.sum_comm]
        have hinner : ∀ w' : Fin k → Bool,
            (∑ S : Finset (Fin k), cycleMat k hk0 z x w' * whEntry w' S * (whEntry w S / (2 : ℚ) ^ k)) =
            if w' = w then cycleMat k hk0 z x w' else 0 := by
          intro w'
          have hrw : ∀ S, cycleMat k hk0 z x w' * whEntry w' S * (whEntry w S / (2 : ℚ) ^ k) =
              (cycleMat k hk0 z x w' / (2 : ℚ) ^ k) * (whEntry w' S * whEntry w S) := fun S => by ring
          simp_rw [hrw, ← Finset.mul_sum, wh_orth w' w]
          split_ifs
          · have h2k : (2 : ℚ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
            field_simp [h2k]
          · simp
        simp_rw [hinner]
        simp
      rwa [hEq] at hmul
  rw [hrank_A]
  -- Step 2: Pair rows (x, ¬x) with x 0 = false and split columns into Even |S| and Odd |S|.
  let X0 := {x : Fin k → Bool // x ⟨0, hk0⟩ = false}
  let eRow : Bool × X0 ≃ (Fin k → Bool) :=
    { toFun := fun p => if p.1 then (fun j => !(p.2.1 j)) else p.2.1
      invFun := fun x => if h : x ⟨0, hk0⟩ = false then (false, ⟨x, h⟩)
        else (true, ⟨fun j => !x j, by cases h0 : x ⟨0, hk0⟩ <;> simp_all⟩)
      left_inv := fun ⟨b, ⟨x, hx0⟩⟩ => by cases b <;> simp [hx0]
      right_inv := fun x => by
        by_cases h0 : x ⟨0, hk0⟩ = false
        · simp [h0]
        · ext j; simp [h0] }
  -- Directly define Aeven and Aodd on X0 → Finset (Fin k) → ℚ!
  let Aeven : X0 → Finset (Fin k) → ℚ := fun x S => if Even S.card then A x.1 S else 0
  let Aodd : X0 → Finset (Fin k) → ℚ := fun x S => if Odd S.card then A x.1 S else 0
  let Ablock : Bool × X0 → Bool × Finset (Fin k) → ℚ := fun p q =>
    if p.1 = q.1 then (if p.1 then Aodd p.2 q.2 else Aeven p.2 q.2) else 0
  have hA_neg : ∀ (x : Fin k → Bool) (S : Finset (Fin k)),
      A (fun j => !x j) S = (-1 : ℚ) ^ S.card * A x S := by
    intro x S
    simp only [A, wh_transform_cycle]
    have hT : transSet hk0 (fun j => !x j) = transSet hk0 x := by ext j; simp [transSet]
    rw [hT]
    split_ifs with hsub
    · have hsgn : (∏ j ∈ S, signBool (!x j)) = (-1 : ℚ) ^ S.card * ∏ j ∈ S, signBool (x j) := by
        have hpt : ∀ j ∈ S, signBool (!x j) = (-1 : ℚ) * signBool (x j) := fun j _ => by
          cases x j <;> norm_num [signBool]
        rw [Finset.prod_congr rfl hpt, Finset.prod_mul_distrib, Finset.prod_const]
      rw [hsgn]; ring
    · simp
  have hrank_split : rowRank A = rowRank Aeven + rowRank Aodd := by
    rw [← rowRank_blockDiag_bool Aeven Aodd, ← rowRank_reindex eRow (Equiv.refl _) A]
    apply rowRank_eq_of_iff
    intro d
    let A1 : Bool × X0 → Finset (Fin k) → ℚ := fun p S => A (eRow p) S
    constructor
    · intro h
      -- Multiply A1 on left by (1/2) [[1, 1], [1, -1]] and split columns by parity of S.card!
      rcases h with ⟨f, g, hfg⟩
      refine ⟨fun j p => if p.1 then (f j (false, p.2) - f j (true, p.2)) / 2
                else (f j (false, p.2) + f j (true, p.2)) / 2,
              fun j q => if q.1 then (if Odd q.2.card then g j q.2 else 0)
                else (if Even q.2.card then g j q.2 else 0), ?_⟩
      intro ⟨bp, x⟩ ⟨bq, S⟩
      have hF : A1 (false, x) S = ∑ j, f j (false, x) * g j S := hfg (false, x) S
      have hT : A1 (true, x) S = ∑ j, f j (true, x) * g j S := hfg (true, x) S
      have hF' : A1 (false, x) S = A x.1 S := rfl
      have hT' : A1 (true, x) S = (-1 : ℚ) ^ S.card * A x.1 S := hA_neg x.1 S
      cases bp <;> cases bq
      · simp only [↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Aeven]
        by_cases he : Even S.card
        · rw [if_pos he]
          have hsum : (∑ j, (f j (false, x) + f j (true, x)) / 2 * (if Even S.card then g j S else 0)) =
              (A1 (false, x) S + A1 (true, x) S) / 2 := by
            simp only [he, ↓reduceIte]
            rw [hF, hT, ← Finset.sum_add_distrib, Finset.sum_div]
            refine Finset.sum_congr rfl fun j _ => by ring
          rw [hsum, hF', hT', Even.neg_one_pow he]; ring
        · simp [he]
      · simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
        by_cases ho : Odd S.card
        · have hsum : (∑ j, (f j (false, x) + f j (true, x)) / 2 * (if Odd S.card then g j S else 0)) =
              (A1 (false, x) S + A1 (true, x) S) / 2 := by
            simp only [ho, ↓reduceIte]
            rw [hF, hT, ← Finset.sum_add_distrib, Finset.sum_div]
            refine Finset.sum_congr rfl fun j _ => by ring
          rw [hsum, hF', hT', Odd.neg_one_pow ho]; ring
        · simp [ho]
      · simp only [Bool.true_eq_false, Bool.false_eq_true, ↓reduceIte]
        by_cases he : Even S.card
        · have hsum : (∑ j, (f j (false, x) - f j (true, x)) / 2 * (if Even S.card then g j S else 0)) =
              (A1 (false, x) S - A1 (true, x) S) / 2 := by
            simp only [he, ↓reduceIte]
            rw [hF, hT, ← Finset.sum_sub_distrib, Finset.sum_div]
            refine Finset.sum_congr rfl fun j _ => by ring
          rw [hsum, hF', hT', Even.neg_one_pow he]; ring
        · simp [he]
      · simp only [↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Aodd]
        by_cases ho : Odd S.card
        · rw [if_pos ho]
          have hsum : (∑ j, (f j (false, x) - f j (true, x)) / 2 * (if Odd S.card then g j S else 0)) =
              (A1 (false, x) S - A1 (true, x) S) / 2 := by
            simp only [ho, ↓reduceIte]
            rw [hF, hT, ← Finset.sum_sub_distrib, Finset.sum_div]
            refine Finset.sum_congr rfl fun j _ => by ring
          rw [hsum, hF', hT', Odd.neg_one_pow ho]; ring
        · simp [ho]
    · intro h
      rcases h with ⟨f, g, hfg⟩
      refine ⟨fun j p => if p.1 then f j (false, p.2) - f j (true, p.2) else f j (false, p.2) + f j (true, p.2),
              fun j S => g j (false, S) + g j (true, S), ?_⟩
      intro ⟨bp, x⟩ S
      have h00 := hfg (false, x) (false, S)
      have h01 := hfg (false, x) (true, S)
      have h10 := hfg (true, x) (false, S)
      have h11 := hfg (true, x) (true, S)
      simp only [↓reduceIte, Bool.false_eq_true, Bool.true_eq_false] at h00 h01 h10 h11
      have hF' : A1 (false, x) S = A x.1 S := rfl
      have hT' : A1 (true, x) S = (-1 : ℚ) ^ S.card * A x.1 S := hA_neg x.1 S
      have hdecomp : A x.1 S = Aeven x S + Aodd x S := by
        dsimp [Aeven, Aodd]
        rcases Nat.even_or_odd S.card with he | ho
        · rw [if_pos he, if_neg (Nat.not_odd_iff_even.mpr he), add_zero]
        · rw [if_neg (Nat.not_even_iff_odd.mpr ho), if_pos ho, zero_add]
      have hdecomp_neg : (-1 : ℚ) ^ S.card * A x.1 S = Aeven x S - Aodd x S := by
        dsimp [Aeven, Aodd]
        rcases Nat.even_or_odd S.card with he | ho
        · rw [Even.neg_one_pow he, if_pos he, if_neg (Nat.not_odd_iff_even.mpr he)]; ring
        · rw [Odd.neg_one_pow ho, if_neg (Nat.not_even_iff_odd.mpr ho), if_pos ho]; ring
      cases bp
      · simp only [Bool.false_eq_true, ↓reduceIte, Equiv.refl_apply]
        change A1 (false, x) S = _
        rw [hF', hdecomp]
        have : (∑ j, (f j (false, x) + f j (true, x)) * (g j (false, S) + g j (true, S))) =
            (∑ j, f j (false, x) * g j (false, S)) + (∑ j, f j (false, x) * g j (true, S)) +
            (∑ j, f j (true, x) * g j (false, S)) + (∑ j, f j (true, x) * g j (true, S)) := by
          simp only [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun j _ => by ring
        rw [this, ← h00, ← h01, ← h10, ← h11]; ring
      · simp only [↓reduceIte, Equiv.refl_apply]
        change A1 (true, x) S = _
        rw [hT', hdecomp_neg]
        have : (∑ j, (f j (false, x) - f j (true, x)) * (g j (false, S) + g j (true, S))) =
            (∑ j, f j (false, x) * g j (false, S)) + (∑ j, f j (false, x) * g j (true, S)) -
            (∑ j, f j (true, x) * g j (false, S)) - (∑ j, f j (true, x) * g j (true, S)) := by
          simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun j _ => by ring
        rw [this, ← h00, ← h01, ← h10, ← h11]; ring
  rw [hrank_split]
  -- Step 3: rowRank Aeven = 2^(k - 1).
  have hrank_even : rowRank Aeven = 2 ^ (k - 1) := by
    let EvenSub := {T : Finset (Fin k) // Even T.card}
    let M_ev : EvenSub → EvenSub → ℚ := fun T S => Aeven ((transEquiv hk0).symm T) S.1
    have hle : rowRank Aeven ≤ 2 ^ (k - 1) := by
      have hcard : Fintype.card X0 = 2 ^ (k - 1) := by
        rw [Fintype.card_congr (transEquiv hk0), card_even_finset k (by omega)]
      rw [← hcard, rowRank_le_iff]
      let eX : Fin (Fintype.card X0) ≃ X0 := (Fintype.equivFin X0).symm
      exact ⟨fun j x => if eX j = x then 1 else 0, fun j S => Aeven (eX j) S, fun x S => by
        rw [Finset.sum_eq_single (eX.symm x) (fun j _ hj => by simp [show eX j ≠ x from fun h => hj (by rw [← h]; simp)]) (fun h => absurd (Finset.mem_univ _) h)]
        simp⟩
    have hge : 2 ^ (k - 1) ≤ rowRank Aeven := by
      have hli_sub : LinearIndependent ℚ M_ev := by
        apply li_lower_tri_finset M_ev
        · intro T S hne
          dsimp [M_ev, Aeven, A] at hne
          rw [if_pos S.2, wh_transform_cycle] at hne
          have hT : transSet hk0 ((transEquiv hk0).symm T).1 = T.1 := by
            have := (transEquiv hk0).apply_symm_apply T
            exact congrArg Subtype.val this
          rw [hT] at hne
          by_contra hns; rw [if_neg hns] at hne; exact hne rfl
        · intro T
          dsimp [M_ev, Aeven, A]
          rw [if_pos T.2, wh_transform_cycle]
          have hT : transSet hk0 ((transEquiv hk0).symm T).1 = T.1 :=
            congrArg Subtype.val ((transEquiv hk0).apply_symm_apply T)
          rw [hT, if_pos (Finset.Subset.refl T.1)]
          refine mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ h2z_ne) (pow_ne_zero _ h1pz2_ne)) (pow_ne_zero _ h1mz2_ne)) ?_
          exact Finset.prod_ne_zero_iff.mpr fun j _ => by cases ((transEquiv hk0).symm T).1 j <;> norm_num [signBool]
      -- Lift linear independence from M_ev (restricted cols) to Aeven (all cols).
      let eE : Fin (Fintype.card EvenSub) ≃ EvenSub := (Fintype.equivFin EvenSub).symm
      have hli : LinearIndependent ℚ (fun i : Fin (Fintype.card EvenSub) => Aeven ((transEquiv hk0).symm (eE i))) := by
        rw [Fintype.linearIndependent_iff]
        intro c hc
        have hlin : ∑ T : EvenSub, c (eE.symm T) • M_ev T = 0 := by
          ext S
          have h0 := congrFun hc S.1
          simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at h0 ⊢
          rw [← Equiv.sum_comp eE.symm] at h0
          simpa [M_ev] using h0
        intro i
        have := Fintype.linearIndependent_iff.mp hli_sub _ hlin (eE i)
        simpa using this
      calc 2 ^ (k - 1) = Fintype.card EvenSub := (card_even_finset k (by omega)).symm
        _ ≤ rowRank Aeven := rowRank_ge_of_li Aeven (fun i => (transEquiv hk0).symm (eE i)) hli
    exact le_antisymm hle hge
  -- Step 4: rowRank Aodd = 2^(k - 2).
  have hrank_odd : rowRank Aodd = 2 ^ (k - 2) := by
    let last : Fin k := ⟨k - 1, by omega⟩
    let OddNL := {S : Finset (Fin k) // Odd S.card ∧ last ∉ S}
    -- Lower bound: 2^(k - 2) ≤ rowRank Aodd via rows T_S = insert last S and cols S ∈ OddNL.
    have hge : 2 ^ (k - 2) ≤ rowRank Aodd := by
      let rowOf : OddNL → X0 := fun S => (transEquiv hk0).symm ⟨insert last S.1, by
        rw [Finset.card_insert_of_notMem S.2.2]; exact S.2.1.add_one⟩
      let M_odd : OddNL → OddNL → ℚ := fun S' S => Aodd (rowOf S') S.1
      have hli_sub : LinearIndependent ℚ M_odd := by
        apply li_lower_tri_finset M_odd
        · intro S' S hne
          dsimp [M_odd, Aodd, A] at hne
          rw [if_pos S.2.1, wh_transform_cycle] at hne
          have hT : transSet hk0 (rowOf S').1 = insert last S'.1 :=
            congrArg Subtype.val ((transEquiv hk0).apply_symm_apply _)
          rw [hT] at hne
          have hsub : S.1 ⊆ insert last S'.1 := by
            by_contra hns; rw [if_neg hns] at hne; exact hne rfl
          intro j hj
          rcases Finset.mem_insert.mp (hsub hj) with rfl | hmem
          · exact absurd hj S.2.2
          · exact hmem
        · intro S
          dsimp [M_odd, Aodd, A]
          rw [if_pos S.2.1, wh_transform_cycle]
          have hT : transSet hk0 (rowOf S).1 = insert last S.1 :=
            congrArg Subtype.val ((transEquiv hk0).apply_symm_apply _)
          rw [hT, if_pos (Finset.subset_insert last S.1)]
          refine mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ h2z_ne) (pow_ne_zero _ h1pz2_ne)) (pow_ne_zero _ h1mz2_ne)) ?_
          exact Finset.prod_ne_zero_iff.mpr fun j _ => by cases (rowOf S).1 j <;> norm_num [signBool]
      let eO : Fin (Fintype.card OddNL) ≃ OddNL := (Fintype.equivFin OddNL).symm
      have hli : LinearIndependent ℚ (fun i : Fin (Fintype.card OddNL) => Aodd (rowOf (eO i))) := by
        rw [Fintype.linearIndependent_iff]
        intro c hc
        have hlin : ∑ S' : OddNL, c (eO.symm S') • M_odd S' = 0 := by
          ext S
          have h0 := congrFun hc S.1
          simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at h0 ⊢
          rw [← Equiv.sum_comp eO.symm] at h0
          simpa [M_odd] using h0
        intro i
        have := Fintype.linearIndependent_iff.mp hli_sub _ hlin (eO i)
        simpa using this
      calc 2 ^ (k - 2) = Fintype.card OddNL := (card_odd_finset_no_last k hk).symm
        _ ≤ rowRank Aodd := rowRank_ge_of_li Aodd (fun i => rowOf (eO i)) hli
    -- Upper bound: every column S of Aodd lies in the span of columns OddNL!
    have hle : rowRank Aodd ≤ 2 ^ (k - 2) := by
      rw [← rowRank_transpose Aodd, ← card_odd_finset_no_last k hk]
      have hspan : Submodule.span ℚ (Set.range (fun S x => Aodd x S)) ≤
          Submodule.span ℚ (Set.range (fun (S : OddNL) x => Aodd x S.1)) := by
        rw [Submodule.span_le]
        rintro _ ⟨S, rfl⟩
        by_cases hodd : Odd S.card
        · by_cases hlast : last ∈ S
          · let E := S.erase last
            have hE_nl : last ∉ E := Finset.notMem_erase last S
            have hE_even : Even E.card := by
              rw [Finset.card_erase_of_mem hlast]; rcases hodd with ⟨m, hm⟩; exact ⟨m, by omega⟩
            have hS_eq : S = insert last E := (Finset.insert_erase hlast).symm
            -- Express col S as - ∑ r ∈ (univ.erase last) \ E, (-1)^(E.filter (< r)).card * col (insert r E)
            have hcol_eq : (fun x : X0 => Aodd x S) =
                ∑ r ∈ (Finset.univ.erase last) \ E,
                  (-((-1 : ℚ) ^ (E.filter (· < r)).card)) • (fun x : X0 => Aodd x (insert r E)) := by
              ext x
              simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
              -- Equivalent to: ∑ r ∈ univ \ E, (-1)^(E.filter (< r)).card * A x (insert r E) = 0!
              have htot : (∑ r ∈ Finset.univ \ E, (-1 : ℚ) ^ (E.filter (· < r)).card * A x.1 (insert r E)) = 0 := by
                let T := transSet hk0 x.1
                by_cases hET : E ⊆ T
                · have hpt : ∀ r ∈ Finset.univ \ E,
                      (-1 : ℚ) ^ (E.filter (· < r)).card * A x.1 (insert r E) =
                      if r ∈ T \ E then
                        ((2 * z) ^ (k - T.card) * (1 + z ^ 2) ^ (T.card - (E.card + 1)) *
                         (1 - z ^ 2) ^ (E.card + 1) * ∏ e ∈ E, signBool (x.1 e)) *
                        (-1 : ℚ) ^ ((T \ E).filter (· < r)).card
                      else 0 := by
                    intro r hr
                    have hrE : r ∉ E := (Finset.mem_sdiff.mp hr).2
                    simp only [A, wh_transform_cycle]
                    by_cases hrT : r ∈ T
                    · have hrTE : r ∈ T \ E := Finset.mem_sdiff.mpr ⟨hrT, hrE⟩
                      have hsub : insert r E ⊆ T := Finset.insert_subset_iff.mpr ⟨hrT, hET⟩
                      rw [if_pos hsub, if_pos hrTE, Finset.card_insert_of_notMem hrE,
                          Finset.prod_insert hrE, signBool_of_transSet hk0 x.1 x.2 r]
                      have hdisj : Disjoint (E.filter (· < r)) ((T \ E).filter (· < r)) :=
                        Finset.disjoint_left.mpr fun t h1 h2 =>
                          (Finset.mem_sdiff.mp (Finset.mem_filter.mp h2).1).2 (Finset.mem_filter.mp h1).1
                      have hunion : T.filter (· < r) = E.filter (· < r) ∪ (T \ E).filter (· < r) := by
                        ext t; simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]
                        constructor
                        · rintro ⟨htT, htl⟩
                          by_cases htE : t ∈ E
                          · exact Or.inl ⟨htE, htl⟩
                          · exact Or.inr ⟨⟨htT, htE⟩, htl⟩
                        · rintro (⟨htE, htl⟩ | ⟨⟨htT, _⟩, htl⟩)
                          · exact ⟨hET htE, htl⟩
                          · exact ⟨htT, htl⟩
                      have hpow : (-1 : ℚ) ^ (E.filter (· < r)).card * (-1 : ℚ) ^ (T.filter (· < r)).card =
                          (-1 : ℚ) ^ ((T \ E).filter (· < r)).card := by
                        rw [hunion, Finset.card_union_of_disjoint hdisj, pow_add, ← mul_assoc,
                            ← pow_add, show (E.filter (· < r)).card + (E.filter (· < r)).card = 2 * (E.filter (· < r)).card by omega,
                            pow_mul, neg_one_sq, one_pow, one_mul]
                      calc (-1 : ℚ) ^ (E.filter (· < r)).card *
                            ((2 * z) ^ (k - T.card) * (1 + z ^ 2) ^ (T.card - (E.card + 1)) *
                             (1 - z ^ 2) ^ (E.card + 1) * ((-1 : ℚ) ^ (T.filter (· < r)).card * ∏ e ∈ E, signBool (x.1 e)))
                          = ((2 * z) ^ (k - T.card) * (1 + z ^ 2) ^ (T.card - (E.card + 1)) *
                             (1 - z ^ 2) ^ (E.card + 1) * ∏ e ∈ E, signBool (x.1 e)) *
                            ((-1 : ℚ) ^ (E.filter (· < r)).card * (-1 : ℚ) ^ (T.filter (· < r)).card) := by ring
                        _ = _ := by rw [hpow]
                    · have hrTE : r ∉ T \ E := fun h => hrT (Finset.mem_sdiff.mp h).1
                      have hnsub : ¬ (insert r E ⊆ T) := fun h => hrT (h (Finset.mem_insert_self r E))
                      rw [if_neg hnsub, if_neg hrTE, mul_zero]
                  rw [Finset.sum_congr rfl hpt, ← Finset.sum_filter]
                  have hfilt : (Finset.univ \ E).filter (· ∈ T \ E) = T \ E := by
                    ext r; simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
                    exact ⟨fun h => h.2, fun h => ⟨h.2, h⟩⟩
                  rw [hfilt, ← Finset.mul_sum]
                  have hTE_even : Even (T \ E).card := by
                    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hET]
                    rcases even_transSet hk0 x.1 with ⟨a, ha⟩
                    change T.card = a + a at ha
                    rcases hE_even with ⟨b, hb⟩
                    have hle : E.card ≤ T.card := Finset.card_le_card hET
                    exact ⟨a - b, by omega⟩
                  rw [alt_sum_even_finset (T \ E) hTE_even, mul_zero]
                · refine Finset.sum_eq_zero fun r _ => ?_
                  simp only [A, wh_transform_cycle]
                  have hnsub : ¬ (insert r E ⊆ T) := fun h => hET ((Finset.subset_insert r E).trans h)
                  rw [if_neg hnsub, mul_zero]
              have hsplit_last : Finset.univ \ E = insert last ((Finset.univ.erase last) \ E) := by
                ext r; simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_erase]
                constructor
                · intro hrE
                  by_cases hrl : r = last
                  · exact Or.inl hrl
                  · exact Or.inr ⟨⟨hrl, trivial⟩, hrE⟩
                · rintro (rfl | ⟨_, hrE⟩)
                  · exact hE_nl
                  · exact hrE
              have hnot_in : last ∉ (Finset.univ.erase last) \ E := by simp
              rw [hsplit_last, Finset.sum_insert hnot_in] at htot
              have hlast_filt : E.filter (· < last) = E := by
                ext e; simp only [Finset.mem_filter, and_iff_left_iff_imp]
                intro he
                have hne : e ≠ last := fun h => hE_nl (h ▸ he)
                exact Fin.lt_def.mpr (by have := e.isLt; have : e.val ≠ k - 1 := fun hv => hne (Fin.ext hv); dsimp [last]; omega)
              rw [hlast_filt, Even.neg_one_pow hE_even, one_mul, ← hS_eq] at htot
              have hodd_S : Aodd x S = A x.1 S := if_pos hodd
              have hodd_ins : ∀ r ∈ (Finset.univ.erase last) \ E, Aodd x (insert r E) = A x.1 (insert r E) := by
                intro r hr
                have hrE : r ∉ E := (Finset.mem_sdiff.mp hr).2
                exact if_pos (by rw [Finset.card_insert_of_notMem hrE]; exact hE_even.add_one)
              rw [hodd_S]
              have hsum_eq : (∑ r ∈ (Finset.univ.erase last) \ E, -(-1 : ℚ) ^ (E.filter (· < r)).card * Aodd x (insert r E)) =
                  -(∑ r ∈ (Finset.univ.erase last) \ E, (-1 : ℚ) ^ (E.filter (· < r)).card * A x.1 (insert r E)) := by
                rw [← Finset.sum_neg_distrib]
                refine Finset.sum_congr rfl fun r hr => by rw [hodd_ins r hr]; ring
              rw [hsum_eq]
              linear_combination htot
            dsimp only
            rw [hcol_eq]
            refine Submodule.sum_mem _ fun r hr => Submodule.smul_mem _ _ ?_
            have hrE : r ∉ E := (Finset.mem_sdiff.mp hr).2
            have hrne : r ≠ last := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hr).1).1
            exact Submodule.subset_span ⟨⟨insert r E, by
              rw [Finset.card_insert_of_notMem hrE]; exact hE_even.add_one,
              fun h => (Finset.mem_insert.mp h).elim (fun h1 => hrne h1.symm) hE_nl⟩, rfl⟩
          · exact Submodule.subset_span ⟨⟨S, hodd, hlast⟩, rfl⟩
        · have h0 : (fun x : X0 => Aodd x S) = 0 := by ext x; simp [Aodd, hodd]
          dsimp only
          rw [h0]; exact Submodule.zero_mem _
      calc rowRank (fun S x => Aodd x S)
          ≤ Module.finrank ℚ (Submodule.span ℚ (Set.range (fun (S : OddNL) x => Aodd x S.1))) :=
            Submodule.finrank_mono hspan
        _ ≤ Fintype.card OddNL := finrank_span_range_le (fun (S : OddNL) x => Aodd x S.1)
    exact le_antisymm hle hge
  rw [hrank_even, hrank_odd]
  have h1 : k - 1 = (k - 2) + 1 := by omega
  rw [h1, pow_succ]; omega

-- Section 4: Graph decomposition and full theorem for L-pcx-416.

section MainProof

variable (n : ℕ) (σ τ : Equiv.Perm (Fin n)) (A : Finset (Fin n)) (z : ℚ)

abbrev V (n : ℕ) := Bool × Fin n

abbrev arc (u v : V n) : Prop :=
  u.1 = false ∧ v.1 = true ∧ (u.2 ∈ A ↔ v.2 ∉ A) ∧
  σ u.2 ≠ τ u.2 ∧ (v.2 = σ u.2 ∨ v.2 = τ u.2)

abbrev adj (u v : V n) : Prop := arc n σ τ A u v ∨ arc n σ τ A v u

def nbrS (u : V n) : Option (V n) :=
  match u with
  | (false, i) => if (i ∈ A ↔ σ i ∉ A) ∧ σ i ≠ τ i then some (true, σ i) else none
  | (true, j) => if (σ.symm j ∈ A ↔ j ∉ A) ∧ j ≠ τ (σ.symm j) then some (false, σ.symm j) else none

def nbrT (u : V n) : Option (V n) :=
  match u with
  | (false, i) => if (i ∈ A ↔ τ i ∉ A) ∧ σ i ≠ τ i then some (true, τ i) else none
  | (true, j) => if (τ.symm j ∈ A ↔ j ∉ A) ∧ σ (τ.symm j) ≠ j then some (false, τ.symm j) else none

def stepC (c : Bool) (u : V n) : Option (V n) :=
  if c then nbrS n σ τ A u else nbrT n σ τ A u

lemma nbrS_symm (u v : V n) : nbrS n σ τ A u = some v ↔ nbrS n σ τ A v = some u := by
  rcases u with ⟨bu, iu⟩; rcases v with ⟨bv, iv⟩
  cases bu <;> cases bv <;> simp only [nbrS]
  · split_ifs <;> simp
  · constructor
    · intro h; split_ifs at h with h1
      injection h with h2
      have hiv : iv = σ iu := congrArg Prod.snd h2.symm
      subst hiv; simp [h1]
    · intro h; split_ifs at h with h1
      injection h with h2
      have hiu : iu = σ.symm iv := congrArg Prod.snd h2.symm
      subst hiu; simp [h1]
  · constructor
    · intro h; split_ifs at h with h1
      injection h with h2
      have hiv : iv = σ.symm iu := congrArg Prod.snd h2.symm
      subst hiv; simp [h1]
    · intro h; split_ifs at h with h1
      injection h with h2
      have hiu : iu = σ iv := congrArg Prod.snd h2.symm
      subst hiu; simp [h1]
  · split_ifs <;> simp

lemma nbrT_symm (u v : V n) : nbrT n σ τ A u = some v ↔ nbrT n σ τ A v = some u := by
  rcases u with ⟨bu, iu⟩; rcases v with ⟨bv, iv⟩
  cases bu <;> cases bv <;> simp only [nbrT]
  · split_ifs <;> simp
  · constructor
    · intro h; split_ifs at h with h1
      injection h with h2
      have hiv : iv = τ iu := congrArg Prod.snd h2.symm
      subst hiv; simp [h1]
    · intro h; split_ifs at h with h1
      injection h with h2
      have hiu : iu = τ.symm iv := congrArg Prod.snd h2.symm
      subst hiu; simp [h1]
  · constructor
    · intro h; split_ifs at h with h1
      injection h with h2
      have hiv : iv = τ.symm iu := congrArg Prod.snd h2.symm
      subst hiv; simp [h1]
    · intro h; split_ifs at h with h1
      injection h with h2
      have hiu : iu = τ iv := congrArg Prod.snd h2.symm
      subst hiu; simp [h1]
  · split_ifs <;> simp

lemma stepC_symm (c : Bool) (u v : V n) : stepC n σ τ A c u = some v ↔ stepC n σ τ A c v = some u := by
  cases c <;> simp [stepC, nbrS_symm, nbrT_symm]

lemma nbrS_ne_nbrT (u v : V n) (hS : nbrS n σ τ A u = some v) : nbrT n σ τ A u ≠ some v := by
  intro hT
  rcases u with ⟨bu, iu⟩; rcases v with ⟨bv, iv⟩
  cases bu
  · simp only [nbrS] at hS; simp only [nbrT] at hT
    split_ifs at hS with h1; split_ifs at hT with h2
    injection hS with e1; injection hT with e2
    have : σ iu = τ iu := (congrArg Prod.snd e1).trans (congrArg Prod.snd e2).symm
    exact h1.2 this
  · simp only [nbrS] at hS; simp only [nbrT] at hT
    split_ifs at hS with h1; split_ifs at hT with h2
    injection hS with e1; injection hT with e2
    have hEq : σ.symm iu = τ.symm iu := (congrArg Prod.snd e1).trans (congrArg Prod.snd e2).symm
    have : τ (σ.symm iu) = iu := by rw [hEq, Equiv.apply_symm_apply]
    exact h1.2 this.symm

lemma adj_iff_nbr (u v : V n) : adj n σ τ A u v ↔ nbrS n σ τ A u = some v ∨ nbrT n σ τ A u = some v := by
  rcases u with ⟨bu, iu⟩; rcases v with ⟨bv, iv⟩
  constructor
  · rintro (⟨h1, h2, h3, h4, h5 | h5⟩ | ⟨h1, h2, h3, h4, h5 | h5⟩)
    · subst h1; subst h2; subst h5; left; simp [nbrS, h3, h4]
    · subst h1; subst h2; subst h5; right; simp [nbrT, h3, h4]
    · subst h1; subst h2; subst h5; left; simp [nbrS, h3, h4]
    · subst h1; subst h2; subst h5; right; simp [nbrT, h3, h4]
  · rintro (hS | hT)
    · cases bu
      · simp only [nbrS] at hS; split_ifs at hS with h1
        injection hS with h2; rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩
        exact Or.inl ⟨rfl, rfl, h1.1, h1.2, Or.inl rfl⟩
      · simp only [nbrS] at hS; split_ifs at hS with h1
        injection hS with h2; rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩
        exact Or.inr ⟨rfl, rfl, h1.1, by simpa using h1.2, Or.inl (by simp)⟩
    · cases bu
      · simp only [nbrT] at hT; split_ifs at hT with h1
        injection hT with h2; rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩
        exact Or.inl ⟨rfl, rfl, h1.1, h1.2, Or.inr rfl⟩
      · simp only [nbrT] at hT; split_ifs at hT with h1
        injection hT with h2; rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩
        exact Or.inr ⟨rfl, rfl, h1.1, by simpa using h1.2, Or.inr (by simp)⟩

lemma stepC_flips (c : Bool) (u v : V n) (h : stepC n σ τ A c u = some v) :
    v.1 = !u.1 ∧ (u.2 ∈ A ↔ v.2 ∉ A) := by
  have hadj : adj n σ τ A u v := (adj_iff_nbr n σ τ A u v).mpr (by cases c <;> simp_all [stepC])
  rcases hadj with ⟨h1, h2, h3, _, _⟩ | ⟨h1, h2, h3, _, _⟩
  · exact ⟨by rw [h1, h2]; rfl, h3⟩
  · exact ⟨by rw [h1, h2]; rfl, by tauto⟩

lemma adj_symm : Symmetric (adj n σ τ A) := fun _ _ h => h.elim Or.inr Or.inl

lemma rtg_symm (u v : V n) (h : Relation.ReflTransGen (adj n σ τ A) u v) :
    Relation.ReflTransGen (adj n σ τ A) v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.head (adj_symm n σ τ A hstep) ih

lemma deg_eq_isSome (u : V n) :
    (Finset.univ.filter (fun v : V n => adj n σ τ A u v)).card =
      (if (nbrS n σ τ A u).isSome then 1 else 0) + (if (nbrT n σ τ A u).isSome then 1 else 0) := by
  classical
  have hset : Finset.univ.filter (fun v : V n => adj n σ τ A u v) =
      (nbrS n σ τ A u).toFinset ∪ (nbrT n σ τ A u).toFinset := by
    ext v; simp [adj_iff_nbr]
  have hdisj : Disjoint (nbrS n σ τ A u).toFinset (nbrT n σ τ A u).toFinset := by
    rw [Finset.disjoint_left]
    intro v hvS hvT
    exact nbrS_ne_nbrT n σ τ A u v (Option.mem_toFinset.mp hvS) (Option.mem_toFinset.mp hvT)
  rw [hset, Finset.card_union_of_disjoint hdisj]
  cases nbrS n σ τ A u <;> cases nbrT n σ τ A u <;> simp

-- Iterative alternating walk starting at u0 with first color c0.
def walkOpt (u0 : V n) (c0 : Bool) : ℕ → Option (V n)
  | 0 => some u0
  | k + 1 => (walkOpt u0 c0 k).bind (stepC n σ τ A (xor c0 (decide (k % 2 = 1))))

lemma walkOpt_step (u0 : V n) (c0 : Bool) (k : ℕ) (u v : V n)
    (hu : walkOpt n σ τ A u0 c0 k = some u)
    (hstep : stepC n σ τ A (xor c0 (decide (k % 2 = 1))) u = some v) :
    walkOpt n σ τ A u0 c0 (k + 1) = some v := by
  simp [walkOpt, hu, hstep]

lemma walkOpt_in_comp (u0 : V n) (c0 : Bool) :
    ∀ k u, walkOpt n σ τ A u0 c0 k = some u → Relation.ReflTransGen (adj n σ τ A) u0 u
  | 0, u, h => by injection h with h; subst h; exact Relation.ReflTransGen.refl
  | k + 1, u, h => by
      simp only [walkOpt] at h
      cases hk : walkOpt n σ τ A u0 c0 k with
      | none => simp [hk] at h
      | some w =>
        simp only [hk, Option.bind_some] at h
        have hadj : adj n σ τ A w u := (adj_iff_nbr n σ τ A w u).mpr (by
          cases hc : xor c0 (decide (k % 2 = 1)) <;> rw [hc] at h <;> simp [stepC] at h
          · exact Or.inr h
          · exact Or.inl h)
        exact Relation.ReflTransGen.tail (walkOpt_in_comp u0 c0 k w hk) hadj

lemma walkOpt_parity (u0 : V n) (c0 : Bool) :
    ∀ k u, walkOpt n σ τ A u0 c0 k = some u →
      u.1 = xor u0.1 (decide (k % 2 = 1)) ∧ (u.2 ∈ A ↔ (u0.2 ∈ A ↔ k % 2 = 0))
  | 0, u, h => by injection h with h; subst h; simp
  | k + 1, u, h => by
      simp only [walkOpt] at h
      cases hk : walkOpt n σ τ A u0 c0 k with
      | none => simp [hk] at h
      | some w =>
        simp only [hk, Option.bind_some] at h
        obtain ⟨h1, h2⟩ := walkOpt_parity u0 c0 k w hk
        obtain ⟨hf1, hf2⟩ := stepC_flips n σ τ A _ w u h
        refine ⟨?_, ?_⟩
        · rw [hf1, h1]
          by_cases hp : k % 2 = 1
          · have hp1 : ¬ ((k + 1) % 2 = 1) := by omega
            cases u0.1 <;> simp [hp, hp1]
          · have hp1 : (k + 1) % 2 = 1 := by omega
            cases u0.1 <;> simp [hp, hp1]
        · have hmod : (k + 1) % 2 = 0 ↔ ¬ (k % 2 = 0) := by omega
          tauto

lemma walkOpt_pullback (u0 : V n) (c0 : Bool) (k₁ k₂ : ℕ) (u : V n)
    (h1 : walkOpt n σ τ A u0 c0 (k₁ + 1) = some u)
    (h2 : walkOpt n σ τ A u0 c0 (k₂ + 1) = some u) :
    ∃ w, walkOpt n σ τ A u0 c0 k₁ = some w ∧ walkOpt n σ τ A u0 c0 k₂ = some w := by
  have hp1 := (walkOpt_parity n σ τ A u0 c0 (k₁ + 1) u h1).1
  have hp2 := (walkOpt_parity n σ τ A u0 c0 (k₂ + 1) u h2).1
  have hsame : k₁ % 2 = k₂ % 2 := by
    have hxor : xor u0.1 (decide ((k₁ + 1) % 2 = 1)) = xor u0.1 (decide ((k₂ + 1) % 2 = 1)) := hp1.symm.trans hp2
    cases u0.1 <;> by_cases a : k₁ % 2 = 1 <;> by_cases b : k₂ % 2 = 1 <;>
      simp [show (k₁ + 1) % 2 = 1 ↔ ¬ (k₁ % 2 = 1) by omega,
            show (k₂ + 1) % 2 = 1 ↔ ¬ (k₂ % 2 = 1) by omega, a, b] at hxor <;> omega
  simp only [walkOpt] at h1 h2
  cases hw1 : walkOpt n σ τ A u0 c0 k₁ with
  | none => simp [hw1] at h1
  | some w1 =>
    cases hw2 : walkOpt n σ τ A u0 c0 k₂ with
    | none => simp [hw2] at h2
    | some w2 =>
      simp only [hw1, Option.bind_some] at h1
      simp only [hw2, Option.bind_some] at h2
      rw [hsame] at h1
      have hb1 := (stepC_symm n σ τ A _ w1 u).mp h1
      have hb2 := (stepC_symm n σ τ A _ w2 u).mp h2
      have hw_eq : w1 = w2 := Option.some.inj (hb1.symm.trans hb2)
      subst hw_eq
      exact ⟨w1, rfl, rfl⟩

lemma walk_from_endpoint (u0 : V n) (c0 : Bool) (hno : stepC n σ τ A (!c0) u0 = none) :
    ∃ (m : ℕ) (f : Fin m ≃ {u : V n // Relation.ReflTransGen (adj n σ τ A) u0 u}),
      (∀ t : Fin m, (f t).1.2 ∈ A ↔ (u0.2 ∈ A ↔ t.val % 2 = 0)) ∧
      (∀ t : Fin m, ∀ h : t.val + 1 < m,
        stepC n σ τ A (xor c0 (decide (t.val % 2 = 1))) (f t).1 = some (f ⟨t.val + 1, h⟩).1) ∧
      (∀ i : Fin n, Relation.ReflTransGen (adj n σ τ A) u0 (false, i) →
        ((i ∈ A ↔ σ i ∉ A) ∧ σ i ≠ τ i →
          ∃ t : Fin m, ∃ h : t.val + 1 < m,
            xor c0 (decide (t.val % 2 = 1)) = true ∧
            (((f t).1 = (false, i) ∧ (f ⟨t.val + 1, h⟩).1 = (true, σ i)) ∨
             ((f t).1 = (true, σ i) ∧ (f ⟨t.val + 1, h⟩).1 = (false, i)))) ∧
        ((i ∈ A ↔ τ i ∉ A) ∧ σ i ≠ τ i →
          ∃ t : Fin m, ∃ h : t.val + 1 < m,
            xor c0 (decide (t.val % 2 = 1)) = false ∧
            (((f t).1 = (false, i) ∧ (f ⟨t.val + 1, h⟩).1 = (true, τ i)) ∨
             ((f t).1 = (true, τ i) ∧ (f ⟨t.val + 1, h⟩).1 = (false, i))))) := by
  classical
  have hinj : ∀ k₁ k₂ u, k₁ < k₂ →
      walkOpt n σ τ A u0 c0 k₁ = some u → walkOpt n σ τ A u0 c0 k₂ ≠ some u := by
    intro k₁
    induction k₁ with
    | zero =>
      intro k₂ u hlt h0 hk2
      injection h0 with hu; subst hu
      obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k₂ ≠ 0)
      have hpar := (walkOpt_parity n σ τ A u0 c0 (k' + 1) u0 hk2).1
      have hk'_odd : k' % 2 = 1 := by
        cases h0 : u0.1 <;> by_cases hp : (k' + 1) % 2 = 1 <;> simp [h0, hp] at hpar <;> omega
      simp only [walkOpt] at hk2
      cases hv : walkOpt n σ τ A u0 c0 k' with
      | none => simp [hv] at hk2
      | some v =>
        simp only [hv, Option.bind_some] at hk2
        have hback := (stepC_symm n σ τ A _ v u0).mp hk2
        have hc : xor c0 (decide (k' % 2 = 1)) = !c0 := by simp [hk'_odd]
        rw [hc, hno] at hback; cases hback
    | succ k₁ ih =>
      intro k₂ u hlt h1 h2
      obtain ⟨k₂', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k₂ ≠ 0)
      obtain ⟨w, hw1, hw2⟩ := walkOpt_pullback n σ τ A u0 c0 k₁ k₂' u h1 h2
      exact ih k₂' w (by omega) hw1 hw2
  have hex_none : ∃ k : ℕ, walkOpt n σ τ A u0 c0 k = none := by
    by_contra hall
    push_neg at hall
    have hsome : ∀ k : Fin (Fintype.card (V n) + 1), ∃ u, walkOpt n σ τ A u0 c0 k.val = some u :=
      fun k => Option.ne_none_iff_exists'.mp (hall k.val)
    choose g hg using hsome
    have hginj : Function.Injective g := by
      intro a b hab
      by_contra hne
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
      · exact hinj a.val b.val (g a) hlt (hg a) (hab ▸ hg b)
      · exact hinj b.val a.val (g b) hgt (hg b) (hab.symm ▸ hg a)
    have hcard := Fintype.card_le_of_injective g hginj
    simp at hcard
  let m := Nat.find hex_none
  have hm_none : walkOpt n σ τ A u0 c0 m = none := Nat.find_spec hex_none
  have hm_some : ∀ t : Fin m, ∃ u, walkOpt n σ τ A u0 c0 t.val = some u := fun t =>
    Option.ne_none_iff_exists'.mp (Nat.find_min hex_none t.isLt)
  choose g hg using hm_some
  have hginj : Function.Injective g := by
    intro a b hab
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
    · exact hinj a.val b.val (g a) hlt (hg a) (hab ▸ hg b)
    · exact hinj b.val a.val (g b) hgt (hg b) (hab.symm ▸ hg a)
  have hstep_fwd : ∀ t : Fin m, ∀ h : t.val + 1 < m,
      stepC n σ τ A (xor c0 (decide (t.val % 2 = 1))) (g t) = some (g ⟨t.val + 1, h⟩) := by
    intro t h
    have h1 := hg ⟨t.val + 1, h⟩
    simp only [walkOpt, hg t, Option.bind_some] at h1
    exact h1
  -- Edge closure: any stepC from g t hits g (t ± 1).
  have hedge_hit : ∀ (t : Fin m) (c : Bool) (v : V n), stepC n σ τ A c (g t) = some v →
      ∃ t' : Fin m, ∃ h : t'.val + 1 < m,
        c = xor c0 (decide (t'.val % 2 = 1)) ∧
        ((g t' = g t ∧ g ⟨t'.val + 1, h⟩ = v) ∨ (g t' = v ∧ g ⟨t'.val + 1, h⟩ = g t)) := by
    intro t c v hst
    by_cases hc : c = xor c0 (decide (t.val % 2 = 1))
    · have hnext : walkOpt n σ τ A u0 c0 (t.val + 1) = some v := by
        simp [walkOpt, hg t, ← hc, hst]
      have hne_m : t.val + 1 ≠ m := fun hEq => by rw [hEq, hm_none] at hnext; cases hnext
      have hlt : t.val + 1 < m := by have := t.isLt; omega
      have hgv : g ⟨t.val + 1, hlt⟩ = v := Option.some.inj ((hg ⟨t.val + 1, hlt⟩).symm.trans hnext)
      exact ⟨t, hlt, hc, Or.inl ⟨rfl, hgv⟩⟩
    · -- Opposite color: must be the backward edge (so t.val > 0)!
      have hc_opp : c = !xor c0 (decide (t.val % 2 = 1)) := by
        cases hc1 : c <;> cases hc2 : xor c0 (decide (t.val % 2 = 1)) <;> simp_all
      by_cases ht0 : t.val = 0
      · have hgu : g t = u0 := by
          have := hg t; rw [ht0] at this; injection this with hEq; exact hEq.symm
        rw [ht0] at hc_opp; simp at hc_opp
        rw [hgu, hc_opp, hno] at hst; cases hst
      · obtain ⟨t', ht'⟩ := Nat.exists_eq_succ_of_ne_zero ht0
        have ht'_lt : t' < m := by have := t.isLt; omega
        have ht'_succ_lt : t' + 1 < m := by have := t.isLt; omega
        have hstep_prev := hstep_fwd ⟨t', ht'_lt⟩ ht'_succ_lt
        have hcol_eq : xor c0 (decide (t' % 2 = 1)) = c := by
          rw [hc_opp, ht']
          have : (t' + 1) % 2 = 1 ↔ ¬ (t' % 2 = 1) := by omega
          cases c0 <;> by_cases hp : t' % 2 = 1 <;> simp [this, hp]
        have hgt_eq : g ⟨t' + 1, ht'_succ_lt⟩ = g t := congrArg g (Fin.ext ht'.symm)
        rw [hcol_eq, hgt_eq] at hstep_prev
        have hback := (stepC_symm n σ τ A c (g ⟨t', ht'_lt⟩) (g t)).mp hstep_prev
        have hgv : g ⟨t', ht'_lt⟩ = v := Option.some.inj (hback.symm.trans hst)
        exact ⟨⟨t', ht'_lt⟩, ht'_succ_lt, hcol_eq.symm, Or.inr ⟨hgv, hgt_eq⟩⟩
  have hsurj : ∀ u : V n, Relation.ReflTransGen (adj n σ τ A) u0 u → ∃ t : Fin m, g t = u := by
    intro u hu
    induction hu with
    | refl =>
      have hm_pos : 0 < m := by
        by_contra h0; have : m = 0 := by omega
        rw [this] at hm_none; simp [walkOpt] at hm_none
      refine ⟨⟨0, hm_pos⟩, ?_⟩
      have := hg ⟨0, hm_pos⟩; simp [walkOpt] at this; exact this.symm
    | @tail w v _ hadj ih =>
      obtain ⟨t, rfl⟩ := ih
      rcases (adj_iff_nbr n σ τ A (g t) v).mp hadj with hS | hT
      · obtain ⟨t', h, _, ⟨_, h2⟩ | ⟨h1, _⟩⟩ := hedge_hit t true v (by simpa [stepC] using hS)
        · exact ⟨⟨t'.val + 1, h⟩, h2⟩
        · exact ⟨t', h1⟩
      · obtain ⟨t', h, _, ⟨_, h2⟩ | ⟨h1, _⟩⟩ := hedge_hit t false v (by simpa [stepC] using hT)
        · exact ⟨⟨t'.val + 1, h⟩, h2⟩
        · exact ⟨t', h1⟩
  let gSub : Fin m → {u : V n // Relation.ReflTransGen (adj n σ τ A) u0 u} :=
    fun t => ⟨g t, walkOpt_in_comp n σ τ A u0 c0 t.val (g t) (hg t)⟩
  have hbij : Function.Bijective gSub := by
    refine ⟨fun a b h => hginj (congrArg Subtype.val h), fun ⟨u, hu⟩ => ?_⟩
    obtain ⟨t, rfl⟩ := hsurj u hu
    exact ⟨t, rfl⟩
  let f := Equiv.ofBijective gSub hbij
  refine ⟨m, f, ?_, ?_, ?_⟩
  · intro t; exact (walkOpt_parity n σ τ A u0 c0 t.val (g t) (hg t)).2
  · intro t h; exact hstep_fwd t h
  · intro i hi
    obtain ⟨t, ht⟩ := hsurj (false, i) hi
    constructor
    · intro hS
      have hst : stepC n σ τ A true (g t) = some (true, σ i) := by rw [ht]; simp [stepC, nbrS, hS]
      obtain ⟨t', h, hc, hcases⟩ := hedge_hit t true (true, σ i) hst
      rw [ht] at hcases
      exact ⟨t', h, hc.symm, hcases⟩
    · intro hT
      have hst : stepC n σ τ A false (g t) = some (true, τ i) := by rw [ht]; simp [stepC, nbrT, hT]
      obtain ⟨t', h, hc, hcases⟩ := hedge_hit t false (true, τ i) hst
      rw [ht] at hcases
      exact ⟨t', h, hc.symm, hcases⟩

lemma walk_cycle (u0 : V n) (hu0_f : u0.1 = false)
    (hdeg2 : ∀ u : V n, Relation.ReflTransGen (adj n σ τ A) u0 u →
      (nbrS n σ τ A u).isSome ∧ (nbrT n σ τ A u).isSome) :
    ∃ (k : ℕ) (hk : 2 ≤ k)
      (f : Fin (2 * k) ≃ {u : V n // Relation.ReflTransGen (adj n σ τ A) u0 u}),
      (∀ t : Fin (2 * k), (f t).1.1 = decide (t.val % 2 = 1) ∧ ((f t).1.2 ∈ A ↔ (u0.2 ∈ A ↔ t.val % 2 = 0))) ∧
      (∀ j : Fin k,
        nbrS n σ τ A (f ⟨2 * j.val, by omega⟩).1 = some (f ⟨2 * j.val + 1, by omega⟩).1 ∧
        nbrT n σ τ A (f ⟨2 * j.val + 1, by omega⟩).1 = some (f ⟨2 * ((j.val + 1) % k), by
          have := Nat.mod_lt (j.val + 1) (by omega : 0 < k); omega⟩).1) ∧
      (∀ i : Fin n, Relation.ReflTransGen (adj n σ τ A) u0 (false, i) →
        ∃ j : Fin k, (f ⟨2 * j.val, by omega⟩).1 = (false, i)) := by
  classical
  have hall_some : ∀ t : ℕ, ∃ u, walkOpt n σ τ A u0 true t = some u := by
    intro t
    induction t with
    | zero => exact ⟨u0, rfl⟩
    | succ t ih =>
      obtain ⟨u, hu⟩ := ih
      have hreach := walkOpt_in_comp n σ τ A u0 true t u hu
      obtain ⟨hS, hT⟩ := hdeg2 u hreach
      have hstep : (stepC n σ τ A (xor true (decide (t % 2 = 1))) u).isSome := by
        cases xor true (decide (t % 2 = 1)) <;> simp [stepC, hS, hT]
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hstep
      exact ⟨v, by unfold walkOpt; rw [hu, Option.bind_some]; exact hv⟩
  choose w hw using hall_some
  have hw_pull : ∀ a b, w (a + 1) = w (b + 1) → w a = w b := by
    intro a b hab
    obtain ⟨u, h1, h2⟩ := walkOpt_pullback n σ τ A u0 true a b (w (a + 1)) (hw (a + 1)) (hab ▸ hw (b + 1))
    exact Option.some.inj ((hw a).symm.trans h1) |> fun e1 => e1.trans (Option.some.inj (h2.symm.trans (hw b)))
  have hw_sub : ∀ a b, a ≤ b → w a = w b → w (b - a) = u0 := by
    intro a
    induction a with
    | zero => intro b _ h; simp; exact h.symm.trans (Option.some.inj ((hw 0).symm))
    | succ a ih =>
      intro b hle h
      obtain ⟨b', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
      have hprev := hw_pull a b' h
      simpa [Nat.succ_sub_succ] using ih b' (by omega) hprev
  have hex_ret : ∃ L : ℕ, 0 < L ∧ w L = u0 := by
    have hnotinj : ¬ Function.Injective (fun t : Fin (Fintype.card (V n) + 1) => w t.val) := by
      intro hinj
      have hle := Fintype.card_le_of_injective _ hinj
      simp at hle
    unfold Function.Injective at hnotinj
    push_neg at hnotinj
    obtain ⟨a, b, hab, hne⟩ := hnotinj
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
    · exact ⟨b.val - a.val, by omega, hw_sub a.val b.val (by omega) hab⟩
    · exact ⟨a.val - b.val, by omega, hw_sub b.val a.val (by omega) hab.symm⟩
  let L := Nat.find hex_ret
  obtain ⟨hL_pos, hL_eq⟩ := Nat.find_spec hex_ret
  have hL_min : ∀ t, 0 < t → t < L → w t ≠ u0 := fun t ht hlt =>
    fun h => Nat.find_min hex_ret hlt ⟨ht, h⟩
  have hL_even : L % 2 = 0 := by
    have hp := (walkOpt_parity n σ τ A u0 true L u0 (hL_eq ▸ hw L)).1
    rw [hu0_f] at hp
    by_cases h1 : L % 2 = 1
    · simp [h1] at hp
    · omega
  let k := L / 2
  have hL_eq_2k : L = 2 * k := by omega
  have hk_ge2 : 2 ≤ k := by
    by_contra hlt
    have hk1 : k = 1 := by omega
    have hL2 : L = 2 := by omega
    have hw2 : walkOpt n σ τ A u0 true 2 = some u0 := by
      have h := hw L; rw [hL_eq, hL2] at h; exact h
    have h1 := hw 1
    simp only [walkOpt] at h1
    have hS : nbrS n σ τ A u0 = some (w 1) := by simpa [stepC] using h1
    have hT : nbrT n σ τ A (w 1) = some u0 := by
      have h2 : (walkOpt n σ τ A u0 true 1).bind (stepC n σ τ A (xor true (decide (1 % 2 = 1)))) = some u0 := hw2
      rw [hw 1, Option.bind_some] at h2
      simpa [stepC] using h2
    exact nbrS_ne_nbrT n σ τ A u0 (w 1) hS ((nbrT_symm n σ τ A (w 1) u0).mp hT)
  have hw_period : ∀ t, w (t + L) = w t := by
    intro t
    induction t with
    | zero => simpa using hL_eq.trans (Option.some.inj (hw 0).symm).symm
    | succ t ih =>
      have h1 := hw (t + L + 1)
      have h2 := hw (t + 1)
      have hpar : (t + L) % 2 = t % 2 := by omega
      simp only [walkOpt, hw (t + L), ih, hpar, Option.bind_some] at h1
      simp only [walkOpt, hw t, Option.bind_some] at h2
      rw [show t + 1 + L = t + L + 1 by omega]
      exact Option.some.inj (h1.symm.trans h2)
  have hw_mod : ∀ t, w (t % L) = w t := by
    intro t
    have hdiv : ∀ q r, w (r + q * L) = w r := by
      intro q
      induction q with
      | zero => intro r; simp
      | succ q ih => intro r; rw [show r + (q + 1) * L = (r + q * L) + L by ring, hw_period, ih]
    conv_rhs => rw [← Nat.mod_add_div t L, Nat.mul_comm]
    exact (hdiv (t / L) (t % L)).symm
  have hwinj : Function.Injective (fun t : Fin (2 * k) => w t.val) := by
    intro a b hab
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
    · exact hL_min (b.val - a.val) (by omega) (by omega) (hw_sub a.val b.val (by omega) hab)
    · exact hL_min (a.val - b.val) (by omega) (by omega) (hw_sub b.val a.val (by omega) hab.symm)
  have hstep_w : ∀ t : ℕ, stepC n σ τ A (xor true (decide (t % 2 = 1))) (w t) = some (w (t + 1)) := by
    intro t; have h := hw (t + 1); simp only [walkOpt, hw t, Option.bind_some] at h; exact h
  have hsurj : ∀ u : V n, Relation.ReflTransGen (adj n σ τ A) u0 u → ∃ t : Fin (2 * k), w t.val = u := by
    intro u hu
    induction hu with
    | refl => exact ⟨⟨0, by omega⟩, Option.some.inj (hw 0).symm⟩
    | @tail x y _ hadj ih =>
      obtain ⟨t, rfl⟩ := ih
      rcases (adj_iff_nbr n σ τ A (w t.val) y).mp hadj with hS | hT
      · by_cases hp : t.val % 2 = 0
        · have hf := hstep_w t.val
          have hc : xor true (decide (t.val % 2 = 1)) = true := by simp [show ¬(t.val % 2 = 1) by omega]
          rw [hc] at hf; simp only [stepC, ↓reduceIte] at hf
          have hy : w (t.val + 1) = y := Option.some.inj (hf.symm.trans hS)
          exact ⟨⟨(t.val + 1) % L, Nat.lt_of_lt_of_eq (Nat.mod_lt _ hL_pos) hL_eq_2k⟩, by rw [hw_mod, hy]⟩
        · have hb := hstep_w (t.val + L - 1)
          have hpar' : (t.val + L - 1) % 2 = 0 := by omega
          have hc : xor true (decide ((t.val + L - 1) % 2 = 1)) = true := by simp [show ¬((t.val + L - 1) % 2 = 1) by omega]
          rw [hc] at hb; simp only [stepC, ↓reduceIte] at hb
          have hnext : w (t.val + L - 1 + 1) = w t.val := by
            rw [show t.val + L - 1 + 1 = t.val + L by omega, hw_period]
          rw [hnext] at hb
          have hsym := (nbrS_symm n σ τ A (w (t.val + L - 1)) (w t.val)).mp hb
          have hy : w (t.val + L - 1) = y := Option.some.inj (hsym.symm.trans hS)
          exact ⟨⟨(t.val + L - 1) % L, Nat.lt_of_lt_of_eq (Nat.mod_lt _ hL_pos) hL_eq_2k⟩, by rw [hw_mod, hy]⟩
      · by_cases hp : t.val % 2 = 1
        · have hf := hstep_w t.val
          have hc : xor true (decide (t.val % 2 = 1)) = false := by simp [hp]
          rw [hc] at hf; simp only [stepC, Bool.false_eq_true, ↓reduceIte] at hf
          have hy : w (t.val + 1) = y := Option.some.inj (hf.symm.trans hT)
          exact ⟨⟨(t.val + 1) % L, Nat.lt_of_lt_of_eq (Nat.mod_lt _ hL_pos) hL_eq_2k⟩, by rw [hw_mod, hy]⟩
        · have hb := hstep_w (t.val + L - 1)
          have hpar' : (t.val + L - 1) % 2 = 1 := by omega
          have hc : xor true (decide ((t.val + L - 1) % 2 = 1)) = false := by simp [hpar']
          rw [hc] at hb; simp only [stepC, Bool.false_eq_true, ↓reduceIte] at hb
          have hnext : w (t.val + L - 1 + 1) = w t.val := by
            rw [show t.val + L - 1 + 1 = t.val + L by omega, hw_period]
          rw [hnext] at hb
          have hsym := (nbrT_symm n σ τ A (w (t.val + L - 1)) (w t.val)).mp hb
          have hy : w (t.val + L - 1) = y := Option.some.inj (hsym.symm.trans hT)
          exact ⟨⟨(t.val + L - 1) % L, Nat.lt_of_lt_of_eq (Nat.mod_lt _ hL_pos) hL_eq_2k⟩, by rw [hw_mod, hy]⟩
  let gSub : Fin (2 * k) → {u : V n // Relation.ReflTransGen (adj n σ τ A) u0 u} :=
    fun t => ⟨w t.val, walkOpt_in_comp n σ τ A u0 true t.val (w t.val) (hw t.val)⟩
  have hbij : Function.Bijective gSub :=
    ⟨fun a b h => hwinj (congrArg Subtype.val h), fun ⟨u, hu⟩ => by obtain ⟨t, rfl⟩ := hsurj u hu; exact ⟨t, rfl⟩⟩
  let f := Equiv.ofBijective gSub hbij
  refine ⟨k, hk_ge2, f, ?_, ?_, ?_⟩
  · intro t
    obtain ⟨h1, h2⟩ := walkOpt_parity n σ τ A u0 true t.val (w t.val) (hw t.val)
    rw [hu0_f] at h1
    exact ⟨by simpa [f, gSub] using h1, h2⟩
  · intro j
    constructor
    · have h := hstep_w (2 * j.val)
      have hc : xor true (decide ((2 * j.val) % 2 = 1)) = true := by simp [show ¬((2 * j.val) % 2 = 1) by omega]
      rw [hc] at h; simpa [stepC, f, gSub] using h
    · have h := hstep_w (2 * j.val + 1)
      have hc : xor true (decide ((2 * j.val + 1) % 2 = 1)) = false := by simp [show (2 * j.val + 1) % 2 = 1 by omega]
      rw [hc] at h; simp only [stepC, Bool.false_eq_true, ↓reduceIte] at h
      have hmod_eq : (2 * j.val + 1 + 1) % L = 2 * ((j.val + 1) % k) := by
        rw [hL_eq_2k, show 2 * j.val + 1 + 1 = 2 * (j.val + 1) by ring, Nat.mul_mod_mul_left]
      have hw_eq : w (2 * j.val + 1 + 1) = w (2 * ((j.val + 1) % k)) := by
        rw [← hw_mod (2 * j.val + 1 + 1), hmod_eq]
      rw [hw_eq] at h
      exact h
  · intro i hi
    obtain ⟨t, ht⟩ := hsurj (false, i) hi
    have hpar := (walkOpt_parity n σ τ A u0 true t.val (false, i) (ht ▸ hw t.val)).1
    rw [hu0_f] at hpar
    have hev : t.val % 2 = 0 := by by_cases h1 : t.val % 2 = 1 <;> simp [h1] at hpar <;> omega
    refine ⟨⟨t.val / 2, by omega⟩, ?_⟩
    have h2 : 2 * (t.val / 2) = t.val := by omega
    simpa [f, gSub, h2] using ht

-- Component matrix M_comp D and its exact rank = factor D.
abbrev LeftD (D : Finset (V n)) := {u : V n // u ∈ D ∧ u.2 ∈ A} → Bool
abbrev RightD (D : Finset (V n)) := {u : V n // u ∈ D ∧ u.2 ∉ A} → Bool

def valD (D : Finset (V n)) (x : LeftD n A D) (w : RightD n A D) (u : V n) : Bool :=
  if h : u ∈ D then (if hA : u.2 ∈ A then x ⟨u, h, hA⟩ else w ⟨u, h, hA⟩) else false

def Mcomp (D : Finset (V n)) (x : LeftD n A D) (w : RightD n A D) : ℚ :=
  (∏ i ∈ Finset.univ.filter (fun i : Fin n => (false, i) ∈ D ∧ (i ∈ A ↔ σ i ∉ A) ∧ σ i ≠ τ i),
    edgeW z true (valD n A D x w (false, i)) (valD n A D x w (true, σ i))) *
  (∏ i ∈ Finset.univ.filter (fun i : Fin n => (false, i) ∈ D ∧ (i ∈ A ↔ τ i ∉ A) ∧ σ i ≠ τ i),
    edgeW z false (valD n A D x w (false, i)) (valD n A D x w (true, τ i)))

-- Exact rank of Mcomp D for every connected component D.
set_option maxHeartbeats 1000000 in
lemma rowRank_Mcomp (hz : 0 < z) (hz1 : z ≠ 1) (u0 : V n) :
    let D := (Finset.univ : Finset (V n)).filter (fun v =>
      @decide (Relation.ReflTransGen (adj n σ τ A) u0 v) (Classical.propDecidable _))
    let deg := fun u : V n => (Finset.univ.filter (fun v : V n => adj n σ τ A u v)).card
    rowRank (Mcomp n σ τ A z D) =
      if (∀ u ∈ D, deg u = 2) then 3 * 2 ^ (D.card / 2 - 2) else 2 ^ (D.card / 2) := by
  classical
  intro D deg
  have hmemD : ∀ v, v ∈ D ↔ Relation.ReflTransGen (adj n σ τ A) u0 v := by
    intro v; simp [D]
  have hcomp_eq : ∀ u ∈ D, (Finset.univ : Finset (V n)).filter (fun v =>
      @decide (Relation.ReflTransGen (adj n σ τ A) u v) (Classical.propDecidable _)) = D := by
    intro u hu
    ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq, hmemD]
    exact ⟨fun h => (hmemD u).mp hu |>.trans h, fun h => (rtg_symm n σ τ A u0 u ((hmemD u).mp hu)).trans h⟩
  by_cases hall2 : ∀ u ∈ D, deg u = 2
  · rw [if_pos hall2]
    -- Find u1 ∈ D with u1.1 = false.
    have hex_f : ∃ u1 ∈ D, u1.1 = false := by
      by_cases h0 : u0.1 = false
      · exact ⟨u0, (hmemD u0).mpr Relation.ReflTransGen.refl, h0⟩
      · have hdeg0 := hall2 u0 ((hmemD u0).mpr Relation.ReflTransGen.refl)
        dsimp only [deg] at hdeg0
        rw [deg_eq_isSome] at hdeg0
        have hS : (nbrS n σ τ A u0).isSome := by
          cases h1 : nbrS n σ τ A u0 <;> cases h2 : nbrT n σ τ A u0 <;> simp_all
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hS
        have hvD : v ∈ D := (hmemD v).mpr (Relation.ReflTransGen.single ((adj_iff_nbr n σ τ A u0 v).mpr (Or.inl hv)))
        have hvf : v.1 = false := by
          have := (stepC_flips n σ τ A true u0 v (by simpa [stepC] using hv)).1
          cases h1 : u0.1 <;> simp_all
        exact ⟨v, hvD, hvf⟩
    obtain ⟨u1, hu1D, hu1f⟩ := hex_f
    have hD_eq : ∀ v, v ∈ D ↔ Relation.ReflTransGen (adj n σ τ A) u1 v := by
      intro v; rw [← hcomp_eq u1 hu1D]; simp
    have hdeg2' : ∀ u, Relation.ReflTransGen (adj n σ τ A) u1 u → (nbrS n σ τ A u).isSome ∧ (nbrT n σ τ A u).isSome := by
      intro u hu
      have hd := hall2 u ((hD_eq u).mpr hu)
      dsimp only [deg] at hd
      rw [deg_eq_isSome] at hd
      cases h1 : nbrS n σ τ A u <;> cases h2 : nbrT n σ τ A u <;> simp_all
    obtain ⟨k, hk, f, hpar, hedg, hfalse⟩ := walk_cycle n σ τ A u1 hu1f hdeg2'
    have hDcard : D.card = 2 * k := by
      have h1 : D.card = Fintype.card {u : V n // Relation.ReflTransGen (adj n σ τ A) u1 u} := by
        rw [← Fintype.card_coe]; apply Fintype.card_congr
        exact Equiv.subtypeEquivRight hD_eq
      rw [h1, ← Fintype.card_congr f, Fintype.card_fin]
    rw [hDcard, Nat.mul_div_right k (by omega : 0 < 2)]
    have hk0 : 0 < k := by omega
    have h_even_f : ∀ j : Fin k, (f ⟨2 * j.val, by omega⟩).1.1 = false := by
      intro j; have := (hpar ⟨2 * j.val, by omega⟩).1; simp at this; exact this
    have h_odd_t : ∀ j : Fin k, (f ⟨2 * j.val + 1, by omega⟩).1.1 = true := by
      intro j; have := (hpar ⟨2 * j.val + 1, by omega⟩).1; simp [show (2 * j.val + 1) % 2 = 1 by omega] at this; exact this
    have h_even_side : ∀ j : Fin k, (f ⟨2 * j.val, by omega⟩).1.2 ∈ A ↔ u1.2 ∈ A := by
      intro j; simpa using (hpar ⟨2 * j.val, by omega⟩).2
    have h_odd_side : ∀ j : Fin k, (f ⟨2 * j.val + 1, by omega⟩).1.2 ∈ A ↔ u1.2 ∉ A := by
      intro j
      have hp := (hpar ⟨2 * j.val + 1, by omega⟩).2
      simp only [show ¬ ((2 * j.val + 1) % 2 = 0) by omega, iff_false] at hp
      exact hp
    -- Every even index j gives a unique (false, i) in D, with BOTH σ-edge and τ-edge in D!
    have h_idx_S : ∀ j : Fin k,
        let i := (f ⟨2 * j.val, by omega⟩).1.2
        (false, i) = (f ⟨2 * j.val, by omega⟩).1 ∧
        (true, σ i) = (f ⟨2 * j.val + 1, by omega⟩).1 ∧
        (i ∈ A ↔ σ i ∉ A) ∧ σ i ≠ τ i := by
      intro j
      have hf0 : (false, (f ⟨2 * j.val, by omega⟩).1.2) = (f ⟨2 * j.val, by omega⟩).1 :=
        Prod.ext (h_even_f j).symm rfl
      have hS := (hedg j).1
      rw [← hf0] at hS
      simp only [nbrS] at hS
      split_ifs at hS with hcond
      injection hS with hEq
      exact ⟨hf0, hEq, hcond.1, hcond.2⟩
    have h_idx_T : ∀ j : Fin k,
        let i := (f ⟨2 * ((j.val + 1) % k), by have := Nat.mod_lt (j.val + 1) hk0; omega⟩).1.2
        (false, i) = (f ⟨2 * ((j.val + 1) % k), by have := Nat.mod_lt (j.val + 1) hk0; omega⟩).1 ∧
        (true, τ i) = (f ⟨2 * j.val + 1, by omega⟩).1 ∧
        (i ∈ A ↔ τ i ∉ A) ∧ σ i ≠ τ i := by
      intro j
      let j' : Fin k := nextFin hk0 j
      have hf0 : (false, (f ⟨2 * j'.val, by omega⟩).1.2) = (f ⟨2 * j'.val, by omega⟩).1 :=
        Prod.ext (h_even_f j').symm rfl
      have hT := (nbrT_symm n σ τ A _ _).mp (hedg j).2
      change nbrT n σ τ A (f ⟨2 * j'.val, by omega⟩).1 = some (f ⟨2 * j.val + 1, by omega⟩).1 at hT
      rw [← hf0] at hT
      simp only [nbrT] at hT
      split_ifs at hT with hcond
      injection hT with hEq
      exact ⟨hf0, hEq, hcond.1, hcond.2⟩
    -- Evaluate Mcomp D in terms of spins at f(2j) and f(2j+1)!
    have hMcomp_eval : ∀ (x : LeftD n A D) (w : RightD n A D),
        Mcomp n σ τ A z D x w =
          cycleMat k hk0 z (fun j => valD n A D x w (f ⟨2 * j.val, by omega⟩).1)
                           (fun j => valD n A D x w (f ⟨2 * j.val + 1, by omega⟩).1) := by
      intro x w
      unfold Mcomp cycleMat
      have hprod1 : (∏ i ∈ Finset.univ.filter (fun i : Fin n => (false, i) ∈ D ∧ (i ∈ A ↔ σ i ∉ A) ∧ σ i ≠ τ i),
          edgeW z true (valD n A D x w (false, i)) (valD n A D x w (true, σ i))) =
          ∏ j : Fin k, edgeW z true (valD n A D x w (f ⟨2 * j.val, by omega⟩).1)
            (valD n A D x w (f ⟨2 * j.val + 1, by omega⟩).1) := by
        refine (Finset.prod_nbij (fun j : Fin k => (f ⟨2 * j.val, by omega⟩).1.2) ?_ ?_ ?_ ?_).symm
        · intro j _
          obtain ⟨hf0, _, h1, h2⟩ := h_idx_S j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hf0.symm ▸ (hD_eq _).mpr (f ⟨2 * j.val, by omega⟩).2, h1, h2⟩
        · intro j1 _ j2 _ hEq
          have h1 : (f ⟨2 * j1.val, by omega⟩).1 = (f ⟨2 * j2.val, by omega⟩).1 :=
            Prod.ext ((h_even_f j1).trans (h_even_f j2).symm) hEq
          have h2 := congrArg Fin.val (f.injective (Subtype.ext h1))
          dsimp at h2
          exact Fin.ext (by omega)
        · intro i hi
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi
          obtain ⟨j, hj⟩ := hfalse i ((hD_eq (false, i)).mp hi.1)
          exact ⟨j, Finset.mem_coe.mpr (Finset.mem_univ j), by dsimp only; rw [hj]⟩
        · intro j _
          obtain ⟨hf0, hS1, _, _⟩ := h_idx_S j
          rw [hf0, hS1]
      have hprod2 : (∏ i ∈ Finset.univ.filter (fun i : Fin n => (false, i) ∈ D ∧ (i ∈ A ↔ τ i ∉ A) ∧ σ i ≠ τ i),
          edgeW z false (valD n A D x w (false, i)) (valD n A D x w (true, τ i))) =
          ∏ j : Fin k, edgeW z false (valD n A D x w (f ⟨2 * j.val + 1, by omega⟩).1)
            (valD n A D x w (f ⟨2 * (nextFin hk0 j).val, by omega⟩).1) := by
        refine (Finset.prod_nbij (fun j : Fin k => (f ⟨2 * (nextFin hk0 j).val, by omega⟩).1.2) ?_ ?_ ?_ ?_).symm
        · intro j _
          obtain ⟨hf0, _, h1, h2⟩ := h_idx_T j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hf0.symm ▸ (hD_eq _).mpr (f ⟨2 * (nextFin hk0 j).val, by omega⟩).2, h1, h2⟩
        · intro j1 _ j2 _ hEq
          have h1 : (f ⟨2 * (nextFin hk0 j1).val, by omega⟩).1 = (f ⟨2 * (nextFin hk0 j2).val, by omega⟩).1 :=
            Prod.ext ((h_even_f (nextFin hk0 j1)).trans (h_even_f (nextFin hk0 j2)).symm) hEq
          have h2 := congrArg Fin.val (f.injective (Subtype.ext h1))
          have hmod : (j1.val + 1) % k = (j2.val + 1) % k := by dsimp [nextFin] at h2; omega
          -- Since j1, j2 < k, (j1+1)%k = (j2+1)%k implies j1 = j2!
          have hj : j1.val = j2.val := by
            by_cases hlt1 : j1.val + 1 < k <;> by_cases hlt2 : j2.val + 1 < k
            · rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hmod; omega
            · have : j2.val + 1 = k := by omega
              rw [Nat.mod_eq_of_lt hlt1, this, Nat.mod_self] at hmod; omega
            · have : j1.val + 1 = k := by omega
              rw [this, Nat.mod_self, Nat.mod_eq_of_lt hlt2] at hmod; omega
            · omega
          exact Fin.ext hj
        · intro i hi
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi
          obtain ⟨j', hj'⟩ := hfalse i ((hD_eq (false, i)).mp hi.1)
          let j : Fin k := ⟨(j'.val + k - 1) % k, Nat.mod_lt _ hk0⟩
          have hnj : nextFin hk0 j = j' := by
            ext; dsimp [nextFin, j]
            by_cases h0 : j'.val = 0
            · rw [h0]; simp [show (k - 1) % k = k - 1 from Nat.mod_eq_of_lt (by omega), Nat.sub_add_cancel hk0]
            · have hlt : j'.val + k - 1 = k + (j'.val - 1) := by omega
              have hlt1 : j'.val - 1 < k := by have := j'.isLt; omega
              rw [hlt, Nat.add_mod_left, Nat.mod_eq_of_lt hlt1, show j'.val - 1 + 1 = j'.val by omega, Nat.mod_eq_of_lt j'.isLt]
          have hidx : (⟨2 * (nextFin hk0 j).val, by omega⟩ : Fin (2 * k)) = ⟨2 * j'.val, by omega⟩ :=
            Fin.ext (by dsimp; rw [hnj])
          exact ⟨j, Finset.mem_coe.mpr (Finset.mem_univ j), by dsimp only; rw [hidx, hj']⟩
        · intro j _
          obtain ⟨hf0, hT1, _, _⟩ := h_idx_T j
          dsimp only [nextFin]
          rw [hf0, hT1, edgeW_comm]
      rw [hprod1, hprod2, Finset.prod_mul_distrib]
    -- Reindex LeftD / RightD to (Fin k → Bool) depending on whether u1.2 ∈ A!
    by_cases hu1A : u1.2 ∈ A
    · let eL : (Fin k → Bool) ≃ LeftD n A D :=
        { toFun := fun x u => x ⟨(f.symm ⟨u.1, (hD_eq u.1).mp u.2.1⟩).val / 2, by omega⟩
          invFun := fun x j => x ⟨(f ⟨2 * j.val, by omega⟩).1, (hD_eq _).mpr (f _).2, (h_even_side j).mpr hu1A⟩
          left_inv := fun x => by
            ext j
            have : (f.symm (f ⟨2 * j.val, by omega⟩)).val = 2 * j.val := by simp
            simp [this]
          right_inv := fun x => by
            ext ⟨u, huD, huA⟩
            dsimp only
            set t := f.symm ⟨u, (hD_eq u).mp huD⟩
            have htu : (f t).1 = u := congrArg Subtype.val (f.apply_symm_apply ⟨u, (hD_eq u).mp huD⟩)
            have ht_even : t.val % 2 = 0 := by
              have hp := (hpar t).2; rw [htu] at hp; exact hp.mp huA |>.mp hu1A
            have h2t : (⟨2 * (t.val / 2), by omega⟩ : Fin (2 * k)) = t := Fin.ext (by dsimp; omega)
            congr 1; apply Subtype.ext; dsimp only; rw [h2t, htu] }
      let eR : (Fin k → Bool) ≃ RightD n A D :=
        { toFun := fun w u => w ⟨(f.symm ⟨u.1, (hD_eq u.1).mp u.2.1⟩).val / 2, by omega⟩
          invFun := fun w j => w ⟨(f ⟨2 * j.val + 1, by omega⟩).1, (hD_eq _).mpr (f _).2,
            fun h => ((h_odd_side j).mp h) hu1A⟩
          left_inv := fun w => by
            ext j
            have : (f.symm (f ⟨2 * j.val + 1, by omega⟩)).val = 2 * j.val + 1 := by simp
            have hdiv : (2 * j.val + 1) / 2 = j.val := by omega
            simp [this, hdiv]
          right_inv := fun w => by
            ext ⟨u, huD, huA⟩
            dsimp only
            set t := f.symm ⟨u, (hD_eq u).mp huD⟩
            have htu : (f t).1 = u := congrArg Subtype.val (f.apply_symm_apply ⟨u, (hD_eq u).mp huD⟩)
            have ht_odd : t.val % 2 = 1 := by
              have hp := (hpar t).2; rw [htu] at hp
              have hne : ¬ (t.val % 2 = 0) := fun h => huA (hp.mpr (by tauto))
              omega
            have h2t : (⟨2 * (t.val / 2) + 1, by omega⟩ : Fin (2 * k)) = t := Fin.ext (by dsimp; omega)
            congr 1; apply Subtype.ext; dsimp only; rw [h2t, htu] }
      rw [← rowRank_reindex eL eR (Mcomp n σ τ A z D)]
      have hEq : (fun x w => Mcomp n σ τ A z D (eL x) (eR w)) = cycleMat k hk0 z := by
        ext x w; rw [hMcomp_eval]
        have hx : ∀ j : Fin k, valD n A D (eL x) (eR w) (f ⟨2 * j.val, by omega⟩).1 = x j := by
          intro j; unfold valD
          rw [dif_pos ((hD_eq _).mpr (f _).2), dif_pos ((h_even_side j).mpr hu1A)]
          dsimp [eL]
          have : (f.symm (f ⟨2 * j.val, by omega⟩)).val = 2 * j.val := by simp
          simp [this]
        have hw : ∀ j : Fin k, valD n A D (eL x) (eR w) (f ⟨2 * j.val + 1, by omega⟩).1 = w j := by
          intro j; unfold valD
          rw [dif_pos ((hD_eq _).mpr (f _).2), dif_neg (fun h => ((h_odd_side j).mp h) hu1A)]
          dsimp [eR]
          have : (f.symm (f ⟨2 * j.val + 1, by omega⟩)).val = 2 * j.val + 1 := by simp
          have hdiv : (2 * j.val + 1) / 2 = j.val := by omega
          simp [this, hdiv]
        simp_rw [hx, hw]
      rw [hEq]
      exact rowRank_cycleMat k hk z hz hz1
    · -- Opposite side: u1.2 ∉ A, so even vertices are RightD and odd vertices are LeftD (transpose!).
      let eL : (Fin k → Bool) ≃ LeftD n A D :=
        { toFun := fun w u => w ⟨(f.symm ⟨u.1, (hD_eq u.1).mp u.2.1⟩).val / 2, by omega⟩
          invFun := fun w j => w ⟨(f ⟨2 * j.val + 1, by omega⟩).1, (hD_eq _).mpr (f _).2, by
            have := (h_odd_side j); tauto⟩
          left_inv := fun w => by
            ext j
            have : (f.symm (f ⟨2 * j.val + 1, by omega⟩)).val = 2 * j.val + 1 := by simp
            have hdiv : (2 * j.val + 1) / 2 = j.val := by omega
            simp [this, hdiv]
          right_inv := fun w => by
            ext ⟨u, huD, huA⟩
            dsimp only
            set t := f.symm ⟨u, (hD_eq u).mp huD⟩
            have htu : (f t).1 = u := congrArg Subtype.val (f.apply_symm_apply ⟨u, (hD_eq u).mp huD⟩)
            have ht_odd : t.val % 2 = 1 := by
              have hp := (hpar t).2; rw [htu] at hp
              have hne : ¬ (t.val % 2 = 0) := fun h => hu1A ((hp.mp huA).mpr h)
              omega
            have h2t : (⟨2 * (t.val / 2) + 1, by omega⟩ : Fin (2 * k)) = t := Fin.ext (by dsimp; omega)
            congr 1; apply Subtype.ext; dsimp only; rw [h2t, htu] }
      let eR : (Fin k → Bool) ≃ RightD n A D :=
        { toFun := fun x u => x ⟨(f.symm ⟨u.1, (hD_eq u.1).mp u.2.1⟩).val / 2, by omega⟩
          invFun := fun x j => x ⟨(f ⟨2 * j.val, by omega⟩).1, (hD_eq _).mpr (f _).2, by
            have := (h_even_side j); tauto⟩
          left_inv := fun x => by
            ext j
            have : (f.symm (f ⟨2 * j.val, by omega⟩)).val = 2 * j.val := by simp
            simp [this]
          right_inv := fun x => by
            ext ⟨u, huD, huA⟩
            dsimp only
            set t := f.symm ⟨u, (hD_eq u).mp huD⟩
            have htu : (f t).1 = u := congrArg Subtype.val (f.apply_symm_apply ⟨u, (hD_eq u).mp huD⟩)
            have ht_even : t.val % 2 = 0 := by
              have hp := (hpar t).2; rw [htu] at hp
              by_contra hne; exact huA (hp.mpr (by tauto))
            have h2t : (⟨2 * (t.val / 2), by omega⟩ : Fin (2 * k)) = t := Fin.ext (by dsimp; omega)
            congr 1; apply Subtype.ext; dsimp only; rw [h2t, htu] }
      rw [← rowRank_reindex eL eR (Mcomp n σ τ A z D)]
      have hEq : (fun w x => Mcomp n σ τ A z D (eL w) (eR x)) = fun w x => cycleMat k hk0 z x w := by
        ext w x; rw [hMcomp_eval]
        have hx : ∀ j : Fin k, valD n A D (eL w) (eR x) (f ⟨2 * j.val, by omega⟩).1 = x j := by
          intro j; unfold valD
          rw [dif_pos ((hD_eq _).mpr (f _).2), dif_neg (by have := h_even_side j; tauto)]
          dsimp [eR]
          have : (f.symm (f ⟨2 * j.val, by omega⟩)).val = 2 * j.val := by simp
          simp [this]
        have hw : ∀ j : Fin k, valD n A D (eL w) (eR x) (f ⟨2 * j.val + 1, by omega⟩).1 = w j := by
          intro j; unfold valD
          rw [dif_pos ((hD_eq _).mpr (f _).2), dif_pos (by have := h_odd_side j; tauto)]
          dsimp [eL]
          have : (f.symm (f ⟨2 * j.val + 1, by omega⟩)).val = 2 * j.val + 1 := by simp
          have hdiv : (2 * j.val + 1) / 2 = j.val := by omega
          simp [this, hdiv]
        simp_rw [hx, hw]
      rw [hEq, rowRank_transpose]
      exact rowRank_cycleMat k hk z hz hz1
  · -- Case 2: some vertex u1 ∈ D has deg u1 < 2 -> path (or isolated vertex)!
    rw [if_neg hall2]
    push_neg at hall2
    obtain ⟨u1, hu1D, hu1_ne2⟩ := hall2
    have hD_eq : ∀ v, v ∈ D ↔ Relation.ReflTransGen (adj n σ τ A) u1 v := by
      intro v; rw [← hcomp_eq u1 hu1D]; simp
    have hex_c0 : ∃ c0 : Bool, stepC n σ τ A (!c0) u1 = none := by
      dsimp only [deg] at hu1_ne2
      rw [deg_eq_isSome] at hu1_ne2
      cases hS : nbrS n σ τ A u1
      · exact ⟨false, by simp [stepC, hS]⟩
      · cases hT : nbrT n σ τ A u1
        · exact ⟨true, by simp [stepC, hT]⟩
        · simp [hS, hT] at hu1_ne2
    obtain ⟨c0, hc0⟩ := hex_c0
    obtain ⟨m, f, hpar, hstep, hedge⟩ := walk_from_endpoint n σ τ A u1 c0 hc0
    have hDcard : D.card = m := by
      have h1 : D.card = Fintype.card {u : V n // Relation.ReflTransGen (adj n σ τ A) u1 u} := by
        rw [← Fintype.card_coe]; exact Fintype.card_congr (Equiv.subtypeEquivRight hD_eq)
      rw [h1, ← Fintype.card_congr f, Fintype.card_fin]
    rw [hDcard]
    -- Show Mcomp D = pathMat m c0 z (possibly transposed)!
    have hMcomp_path : ∀ (x : LeftD n A D) (w : RightD n A D),
        Mcomp n σ τ A z D x w =
          ∏ t : Fin m, if h : t.val + 1 < m then
            edgeW z (xor c0 (decide (t.val % 2 = 1)))
              (valD n A D x w (f t).1) (valD n A D x w (f ⟨t.val + 1, h⟩).1)
          else 1 := by
      intro x w
      unfold Mcomp
      -- Split Fin m edges into S-edges (color true) and T-edges (color false)!
      let Sidx := (Finset.univ : Finset (Fin m)).filter (fun t => t.val + 1 < m ∧ xor c0 (decide (t.val % 2 = 1)) = true)
      let Tidx := (Finset.univ : Finset (Fin m)).filter (fun t => t.val + 1 < m ∧ xor c0 (decide (t.val % 2 = 1)) = false)
      have hprod_split : (∏ t : Fin m, if h : t.val + 1 < m then
            edgeW z (xor c0 (decide (t.val % 2 = 1)))
              (valD n A D x w (f t).1) (valD n A D x w (f ⟨t.val + 1, h⟩).1) else 1) =
          (∏ t ∈ Sidx, if h : t.val + 1 < m then
            edgeW z true (valD n A D x w (f t).1) (valD n A D x w (f ⟨t.val + 1, h⟩).1) else 1) *
          (∏ t ∈ Tidx, if h : t.val + 1 < m then
            edgeW z false (valD n A D x w (f t).1) (valD n A D x w (f ⟨t.val + 1, h⟩).1) else 1) := by
        have hdisj : Disjoint Sidx Tidx := Finset.disjoint_filter.mpr fun t _ h1 h2 => by rw [h1.2] at h2; cases h2.2
        have hrest : ∀ t : Fin m, t ∉ Sidx ∪ Tidx →
            (if h : t.val + 1 < m then edgeW z (xor c0 (decide (t.val % 2 = 1)))
              (valD n A D x w (f t).1) (valD n A D x w (f ⟨t.val + 1, h⟩).1) else 1) = 1 := by
          intro t ht
          have hnot : ¬ (t.val + 1 < m) := by
            intro hlt
            cases hc : xor c0 (decide (t.val % 2 = 1))
            · exact ht (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ t, hlt, hc⟩))
            · exact ht (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ t, hlt, hc⟩))
          rw [dif_neg hnot]
        rw [← Finset.prod_subset (Finset.subset_univ (Sidx ∪ Tidx)) (fun t _ ht => hrest t ht),
            Finset.prod_union hdisj]
        congr 1
        · refine Finset.prod_congr rfl fun t ht => ?_
          have hc := (Finset.mem_filter.mp ht).2.2; rw [hc]
        · refine Finset.prod_congr rfl fun t ht => ?_
          have hc := (Finset.mem_filter.mp ht).2.2; rw [hc]
      rw [hprod_split]
      -- Each Sidx edge corresponds uniquely to an i with (false, i) ∈ D ∧ (i ∈ A ↔ σ i ∉ A) ∧ σ i ≠ τ i!
      have hS_eq : (∏ i ∈ Finset.univ.filter (fun i : Fin n => (false, i) ∈ D ∧ (i ∈ A ↔ σ i ∉ A) ∧ σ i ≠ τ i),
          edgeW z true (valD n A D x w (false, i)) (valD n A D x w (true, σ i))) =
          ∏ t ∈ Sidx, if h : t.val + 1 < m then
            edgeW z true (valD n A D x w (f t).1) (valD n A D x w (f ⟨t.val + 1, h⟩).1) else 1 := by
        let keyS : Fin m → Fin n := fun t =>
          if h : t.val + 1 < m then
            if (f t).1.1 = false then (f t).1.2 else (f ⟨t.val + 1, h⟩).1.2
          else ⟨0, by
            -- Only evaluated for t ∈ Sidx where t.val + 1 < m (so V n is nonempty, hence n > 0)!
            by_contra h0; have : n = 0 := by omega
            subst this; exact Fin.elim0 (f t).1.2⟩
        have hS_info : ∀ t ∈ Sidx, ∃ h : t.val + 1 < m,
            let i := keyS t
            ((false, i) = (f t).1 ∧ (true, σ i) = (f ⟨t.val + 1, h⟩).1 ∨
             (false, i) = (f ⟨t.val + 1, h⟩).1 ∧ (true, σ i) = (f t).1) ∧
            (false, i) ∈ D ∧ (i ∈ A ↔ σ i ∉ A) ∧ σ i ≠ τ i := by
          intro t ht
          obtain ⟨_, hlt, hc⟩ := Finset.mem_filter.mp ht
          have hst := hstep t hlt
          rw [hc] at hst; simp only [stepC, ↓reduceIte] at hst
          cases hft : (f t).1 with
          | mk bt it =>
            cases bt
            · rw [hft] at hst; simp only [nbrS] at hst
              split_ifs at hst with hcond
              injection hst with hEq
              have hk : keyS t = it := by simp [keyS, hlt, hft]
              refine ⟨hlt, ?_⟩
              dsimp only; rw [hk]
              exact ⟨Or.inl ⟨rfl, hEq⟩, by rw [← hft]; exact (hD_eq _).mpr (f t).2, hcond.1, hcond.2⟩
            · have hsym := (nbrS_symm n σ τ A _ _).mp hst
              have hfl := (stepC_flips n σ τ A true _ _ (by simpa [stepC] using hst)).1
              rw [hft] at hfl; simp at hfl
              cases hft1 : (f ⟨t.val + 1, hlt⟩).1 with
              | mk bt1 it1 =>
                rw [hft1] at hfl; simp at hfl; subst hfl
                rw [hft1] at hsym; simp only [nbrS] at hsym
                split_ifs at hsym with hcond
                injection hsym with hEq
                have hk : keyS t = it1 := by simp [keyS, hlt, hft, hft1]
                refine ⟨hlt, ?_⟩
                dsimp only; rw [hk]
                exact ⟨Or.inr ⟨hft1.symm, hEq.trans hft⟩, by rw [← hft1]; exact (hD_eq _).mpr (f ⟨t.val + 1, hlt⟩).2, hcond.1, hcond.2⟩
        refine (Finset.prod_nbij keyS ?_ ?_ ?_ ?_).symm
        · intro t ht
          obtain ⟨_, _, h1, h2, h3⟩ := hS_info t ht
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2, h3⟩
        · intro t1 ht1 t2 ht2 hEq
          obtain ⟨h1, hc1, _, _, _⟩ := hS_info t1 ht1
          obtain ⟨h2, hc2, _, _, _⟩ := hS_info t2 ht2
          rw [hEq] at hc1
          have hpair : ({(f t1).1, (f ⟨t1.val + 1, h1⟩).1} : Set (V n)) = {(f t2).1, (f ⟨t2.val + 1, h2⟩).1} := by
            rcases hc1 with ⟨a1, b1⟩ | ⟨a1, b1⟩ <;> rcases hc2 with ⟨a2, b2⟩ | ⟨a2, b2⟩ <;>
              rw [← a1, ← b1, ← a2, ← b2]
            all_goals first | rfl | exact Set.pair_comm _ _
          -- Since f is injective, {t1, t1+1} = {t2, t2+1} in Fin m forces t1 = t2!
          have hmem1 : (f t1).1 ∈ ({(f t2).1, (f ⟨t2.val + 1, h2⟩).1} : Set (V n)) := by rw [← hpair]; exact Or.inl rfl
          have hmem2 : (f ⟨t1.val + 1, h1⟩).1 ∈ ({(f t2).1, (f ⟨t2.val + 1, h2⟩).1} : Set (V n)) := by rw [← hpair]; exact Or.inr rfl
          rcases hmem1 with e1 | e1 <;> rcases hmem2 with e2 | e2
          · exact f.injective (Subtype.ext e1)
          · exact f.injective (Subtype.ext e1)
          · have v1 := congrArg Fin.val (f.injective (Subtype.ext e1))
            have v2 := congrArg Fin.val (f.injective (Subtype.ext e2))
            dsimp at v1 v2; omega
          · have v1 := congrArg Fin.val (f.injective (Subtype.ext e1))
            have v2 := congrArg Fin.val (f.injective (Subtype.ext e2))
            dsimp at v1 v2; omega
        · intro i hi
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi
          obtain ⟨t, hlt, hc, hpair⟩ := (hedge i ((hD_eq _).mp hi.1)).1 ⟨hi.2.1, hi.2.2⟩
          have htS : t ∈ Sidx := Finset.mem_filter.mpr ⟨Finset.mem_univ t, hlt, hc⟩
          refine ⟨t, Finset.mem_coe.mpr htS, ?_⟩
          rcases hpair with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> simp [keyS, hlt, ha, hb]
        · intro t ht
          obtain ⟨hlt, hc, _, _, _⟩ := hS_info t ht
          rw [dif_pos hlt]
          rcases hc with ⟨ha, hb⟩ | ⟨ha, hb⟩
          · rw [← ha, ← hb]
          · rw [← ha, ← hb, edgeW_comm]
      have hT_eq : (∏ i ∈ Finset.univ.filter (fun i : Fin n => (false, i) ∈ D ∧ (i ∈ A ↔ τ i ∉ A) ∧ σ i ≠ τ i),
          edgeW z false (valD n A D x w (false, i)) (valD n A D x w (true, τ i))) =
          ∏ t ∈ Tidx, if h : t.val + 1 < m then
            edgeW z false (valD n A D x w (f t).1) (valD n A D x w (f ⟨t.val + 1, h⟩).1) else 1 := by
        let keyT : Fin m → Fin n := fun t =>
          if h : t.val + 1 < m then
            if (f t).1.1 = false then (f t).1.2 else (f ⟨t.val + 1, h⟩).1.2
          else ⟨0, by
            by_contra h0; have : n = 0 := by omega
            subst this; exact Fin.elim0 (f t).1.2⟩
        have hT_info : ∀ t ∈ Tidx, ∃ h : t.val + 1 < m,
            let i := keyT t
            ((false, i) = (f t).1 ∧ (true, τ i) = (f ⟨t.val + 1, h⟩).1 ∨
             (false, i) = (f ⟨t.val + 1, h⟩).1 ∧ (true, τ i) = (f t).1) ∧
            (false, i) ∈ D ∧ (i ∈ A ↔ τ i ∉ A) ∧ σ i ≠ τ i := by
          intro t ht
          obtain ⟨_, hlt, hc⟩ := Finset.mem_filter.mp ht
          have hst := hstep t hlt
          rw [hc] at hst; simp only [stepC, Bool.false_eq_true, ↓reduceIte] at hst
          cases hft : (f t).1 with
          | mk bt it =>
            cases bt
            · rw [hft] at hst; simp only [nbrT] at hst
              split_ifs at hst with hcond
              injection hst with hEq
              have hk : keyT t = it := by simp [keyT, hlt, hft]
              refine ⟨hlt, ?_⟩
              dsimp only; rw [hk]
              exact ⟨Or.inl ⟨rfl, hEq⟩, by rw [← hft]; exact (hD_eq _).mpr (f t).2, hcond.1, hcond.2⟩
            · have hsym := (nbrT_symm n σ τ A _ _).mp hst
              have hfl := (stepC_flips n σ τ A false _ _ (by simpa [stepC] using hst)).1
              rw [hft] at hfl; simp at hfl
              cases hft1 : (f ⟨t.val + 1, hlt⟩).1 with
              | mk bt1 it1 =>
                rw [hft1] at hfl; simp at hfl; subst hfl
                rw [hft1] at hsym; simp only [nbrT] at hsym
                split_ifs at hsym with hcond
                injection hsym with hEq
                have hk : keyT t = it1 := by simp [keyT, hlt, hft, hft1]
                refine ⟨hlt, ?_⟩
                dsimp only; rw [hk]
                exact ⟨Or.inr ⟨hft1.symm, hEq.trans hft⟩, by rw [← hft1]; exact (hD_eq _).mpr (f ⟨t.val + 1, hlt⟩).2, hcond.1, hcond.2⟩
        refine (Finset.prod_nbij keyT ?_ ?_ ?_ ?_).symm
        · intro t ht
          obtain ⟨_, _, h1, h2, h3⟩ := hT_info t ht
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2, h3⟩
        · intro t1 ht1 t2 ht2 hEq
          obtain ⟨h1, hc1, _, _, _⟩ := hT_info t1 ht1
          obtain ⟨h2, hc2, _, _, _⟩ := hT_info t2 ht2
          rw [hEq] at hc1
          have hpair : ({(f t1).1, (f ⟨t1.val + 1, h1⟩).1} : Set (V n)) = {(f t2).1, (f ⟨t2.val + 1, h2⟩).1} := by
            rcases hc1 with ⟨a1, b1⟩ | ⟨a1, b1⟩ <;> rcases hc2 with ⟨a2, b2⟩ | ⟨a2, b2⟩ <;>
              rw [← a1, ← b1, ← a2, ← b2]
            all_goals first | rfl | exact Set.pair_comm _ _
          have hmem1 : (f t1).1 ∈ ({(f t2).1, (f ⟨t2.val + 1, h2⟩).1} : Set (V n)) := by rw [← hpair]; exact Or.inl rfl
          have hmem2 : (f ⟨t1.val + 1, h1⟩).1 ∈ ({(f t2).1, (f ⟨t2.val + 1, h2⟩).1} : Set (V n)) := by rw [← hpair]; exact Or.inr rfl
          rcases hmem1 with e1 | e1 <;> rcases hmem2 with e2 | e2
          · exact f.injective (Subtype.ext e1)
          · exact f.injective (Subtype.ext e1)
          · have v1 := congrArg Fin.val (f.injective (Subtype.ext e1))
            have v2 := congrArg Fin.val (f.injective (Subtype.ext e2))
            dsimp at v1 v2; omega
          · have v1 := congrArg Fin.val (f.injective (Subtype.ext e1))
            have v2 := congrArg Fin.val (f.injective (Subtype.ext e2))
            dsimp at v1 v2; omega
        · intro i hi
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi
          obtain ⟨t, hlt, hc, hpair⟩ := (hedge i ((hD_eq _).mp hi.1)).2 ⟨hi.2.1, hi.2.2⟩
          have htT : t ∈ Tidx := Finset.mem_filter.mpr ⟨Finset.mem_univ t, hlt, hc⟩
          refine ⟨t, Finset.mem_coe.mpr htT, ?_⟩
          rcases hpair with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> simp [keyT, hlt, ha, hb]
        · intro t ht
          obtain ⟨hlt, hc, _, _, _⟩ := hT_info t ht
          rw [dif_pos hlt]
          rcases hc with ⟨ha, hb⟩ | ⟨ha, hb⟩
          · rw [← ha, ← hb]
          · rw [← ha, ← hb, edgeW_comm]
      rw [hS_eq, hT_eq]
    -- Reindex LeftD / RightD to pathMat m c0 z (or its transpose)!
    by_cases hu1A : u1.2 ∈ A
    · let eL : ({t : Fin m // t.val % 2 = 0} → Bool) ≃ LeftD n A D :=
        { toFun := fun x u => x ⟨f.symm ⟨u.1, (hD_eq u.1).mp u.2.1⟩, by
            set t := f.symm ⟨u.1, (hD_eq u.1).mp u.2.1⟩
            have htu : (f t).1 = u.1 := congrArg Subtype.val (f.apply_symm_apply ⟨u.1, (hD_eq u.1).mp u.2.1⟩)
            have hp := hpar t; rw [htu] at hp; exact (hp.mp u.2.2).mp hu1A⟩
          invFun := fun x t => x ⟨(f t.1).1, (hD_eq _).mpr (f t.1).2, (hpar t.1).mpr ⟨fun _ => t.2, fun _ => hu1A⟩⟩
          left_inv := fun x => by ext ⟨t, ht⟩; simp
          right_inv := fun x => by
            ext ⟨u, huD, huA⟩
            dsimp
            congr 1; apply Subtype.ext
            have h := f.apply_symm_apply ⟨u, (hD_eq u).mp huD⟩
            have hv := congrArg Subtype.val h
            exact hv }
      let eR : ({t : Fin m // t.val % 2 = 1} → Bool) ≃ RightD n A D :=
        { toFun := fun w u => w ⟨f.symm ⟨u.1, (hD_eq u.1).mp u.2.1⟩, by
            set t := f.symm ⟨u.1, (hD_eq u.1).mp u.2.1⟩
            have htu : (f t).1 = u.1 := congrArg Subtype.val (f.apply_symm_apply ⟨u.1, (hD_eq u.1).mp u.2.1⟩)
            have hp := hpar t; rw [htu] at hp
            have hne : ¬ (t.val % 2 = 0) := fun h => u.2.2 (hp.mpr (by tauto))
            omega⟩
          invFun := fun w t => w ⟨(f t.1).1, (hD_eq _).mpr (f t.1).2, fun h => by
            have := ((hpar t.1).mp h).mp hu1A; have := t.2; omega⟩
          left_inv := fun w => by ext ⟨t, ht⟩; simp
          right_inv := fun w => by
            ext ⟨u, huD, huA⟩
            dsimp
            congr 1; apply Subtype.ext
            have h := f.apply_symm_apply ⟨u, (hD_eq u).mp huD⟩
            have hv := congrArg Subtype.val h
            exact hv }
      rw [← rowRank_reindex eL eR (Mcomp n σ τ A z D)]
      have hEq : (fun x w => Mcomp n σ τ A z D (eL x) (eR w)) = pathMat m c0 z := by
        ext x w; rw [hMcomp_path]; unfold pathMat
        have hv : ∀ t : Fin m, valD n A D (eL x) (eR w) (f t).1 = pathVal x w t := by
          intro t; unfold valD pathVal
          rw [dif_pos ((hD_eq _).mpr (f t).2)]
          by_cases hev : t.val % 2 = 0
          · rw [dif_pos ((hpar t).mpr (by tauto)), dif_pos hev]; simp [eL]
          · rw [dif_neg (fun h => hev (((hpar t).mp h).mp hu1A)), dif_neg hev]; simp [eR]
        simp_rw [hv]
      rw [hEq]
      exact rowRank_pathMat z hz hz1 m c0
    · let eL : ({t : Fin m // t.val % 2 = 1} → Bool) ≃ LeftD n A D :=
        { toFun := fun w u => w ⟨f.symm ⟨u.1, (hD_eq u.1).mp u.2.1⟩, by
            set t := f.symm ⟨u.1, (hD_eq u.1).mp u.2.1⟩
            have htu : (f t).1 = u.1 := congrArg Subtype.val (f.apply_symm_apply ⟨u.1, (hD_eq u.1).mp u.2.1⟩)
            have hp := hpar t; rw [htu] at hp
            have hne : ¬ (t.val % 2 = 0) := fun h => hu1A ((hp.mp u.2.2).mpr h)
            omega⟩
          invFun := fun w t => w ⟨(f t.1).1, (hD_eq _).mpr (f t.1).2, (hpar t.1).mpr (by
            have := t.2; constructor <;> intro h <;> [exact absurd h hu1A; omega])⟩
          left_inv := fun w => by ext ⟨t, ht⟩; simp
          right_inv := fun w => by
            ext ⟨u, huD, huA⟩
            dsimp
            congr 1; apply Subtype.ext
            have h := f.apply_symm_apply ⟨u, (hD_eq u).mp huD⟩
            have hv := congrArg Subtype.val h
            exact hv }
      let eR : ({t : Fin m // t.val % 2 = 0} → Bool) ≃ RightD n A D :=
        { toFun := fun x u => x ⟨f.symm ⟨u.1, (hD_eq u.1).mp u.2.1⟩, by
            set t := f.symm ⟨u.1, (hD_eq u.1).mp u.2.1⟩
            have htu : (f t).1 = u.1 := congrArg Subtype.val (f.apply_symm_apply ⟨u.1, (hD_eq u.1).mp u.2.1⟩)
            have hp := hpar t; rw [htu] at hp
            by_contra hne; exact u.2.2 (hp.mpr (by tauto))⟩
          invFun := fun x t => x ⟨(f t.1).1, (hD_eq _).mpr (f t.1).2, fun h => hu1A (((hpar t.1).mp h).mpr t.2)⟩
          left_inv := fun x => by ext ⟨t, ht⟩; simp
          right_inv := fun x => by
            ext ⟨u, huD, huA⟩
            dsimp
            congr 1; apply Subtype.ext
            have h := f.apply_symm_apply ⟨u, (hD_eq u).mp huD⟩
            have hv := congrArg Subtype.val h
            exact hv }
      rw [← rowRank_reindex eL eR (Mcomp n σ τ A z D)]
      have hEq : (fun w x => Mcomp n σ τ A z D (eL w) (eR x)) = fun w x => pathMat m c0 z x w := by
        ext w x; rw [hMcomp_path]; unfold pathMat
        have hv : ∀ t : Fin m, valD n A D (eL w) (eR x) (f t).1 = pathVal x w t := by
          intro t; unfold valD pathVal
          rw [dif_pos ((hD_eq _).mpr (f t).2)]
          by_cases hev : t.val % 2 = 0
          · rw [dif_neg (fun h => hu1A (((hpar t).mp h).mpr hev)), dif_pos hev]; simp [eR]
          · rw [dif_pos ((hpar t).mpr (by tauto)), dif_neg hev]; simp [eL]
        simp_rw [hv]
      rw [hEq, rowRank_transpose]
      exact rowRank_pathMat z hz hz1 m c0

-- Section 5: Finset-indexed Kronecker product and reduction from Z to comps.

lemma rowRank_finset_kronecker {ι : Type*} [DecidableEq ι]
    (α β : ι → Type*) [∀ i, Finite (α i)] [∀ i, Finite (β i)]
    (M : ∀ i, α i → β i → ℚ) :
    ∀ (s : Finset ι),
      rowRank (fun (x : (i : {j // j ∈ s}) → α i.1) (y : (i : {j // j ∈ s}) → β i.1) =>
        ∏ i : {j // j ∈ s}, M i.1 (x i) (y i)) = ∏ i ∈ s, rowRank (M i) := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    have h1 : (fun (x : (i : {j // j ∈ (∅ : Finset ι)}) → α i.1)
                   (y : (i : {j // j ∈ (∅ : Finset ι)}) → β i.1) =>
        ∏ i : {j // j ∈ (∅ : Finset ι)}, M i.1 (x i) (y i)) = fun _ _ => (1 : ℚ) := by
      ext x y; simp
    rw [h1, Finset.prod_empty]
    exact rowRank_const_one
  | @insert a s ha ih =>
    let eA : (α a × ((i : {j // j ∈ s}) → α i.1)) ≃ ((i : {j // j ∈ insert a s}) → α i.1) :=
      { toFun := fun p i => if h : i.1 = a then cast (congrArg α h.symm) p.1 else p.2 ⟨i.1, (Finset.mem_insert.mp i.2).resolve_left h⟩
        invFun := fun x => (x ⟨a, Finset.mem_insert_self a s⟩, fun i => x ⟨i.1, Finset.mem_insert_of_mem i.2⟩)
        left_inv := fun ⟨xa, xs⟩ => by
          ext
          · simp
          · rename_i i
            have hne : i.1 ≠ a := fun h => ha (h ▸ i.2)
            simp [hne]
        right_inv := fun x => by
          ext ⟨j, hj⟩
          by_cases hja : j = a
          · subst hja; simp
          · simp [hja] }
    let eB : (β a × ((i : {j // j ∈ s}) → β i.1)) ≃ ((i : {j // j ∈ insert a s}) → β i.1) :=
      { toFun := fun p i => if h : i.1 = a then cast (congrArg β h.symm) p.1 else p.2 ⟨i.1, (Finset.mem_insert.mp i.2).resolve_left h⟩
        invFun := fun y => (y ⟨a, Finset.mem_insert_self a s⟩, fun i => y ⟨i.1, Finset.mem_insert_of_mem i.2⟩)
        left_inv := fun ⟨ya, ys⟩ => by
          ext
          · simp
          · rename_i i
            have hne : i.1 ≠ a := fun h => ha (h ▸ i.2)
            simp [hne]
        right_inv := fun y => by
          ext ⟨j, hj⟩
          by_cases hja : j = a
          · subst hja; simp
          · simp [hja] }
    rw [← rowRank_reindex eA eB, Finset.prod_insert ha, ← ih, ← rowRank_kronecker]
    congr 1
    ext ⟨xa, xs⟩ ⟨ya, ys⟩
    have hsplit : (∏ i : {j // j ∈ insert a s}, M i.1 (eA (xa, xs) i) (eB (ya, ys) i)) =
        M a xa ya * ∏ i : {j // j ∈ s}, M i.1 (xs i) (ys i) := by
      have h1 : (∏ i : {j // j ∈ insert a s}, M i.1 (eA (xa, xs) i) (eB (ya, ys) i)) =
          ∏ j ∈ (insert a s).attach, M j.1 (eA (xa, xs) j) (eB (ya, ys) j) := rfl
      rw [h1]
      have hmem : (⟨a, Finset.mem_insert_self a s⟩ : {j // j ∈ insert a s}) ∈ (insert a s).attach :=
        Finset.mem_attach _ _
      rw [← Finset.mul_prod_erase _ _ hmem]
      congr 1
      · simp [eA, eB]
      · refine (Finset.prod_nbij (fun i : {j // j ∈ s} => (⟨i.1, Finset.mem_insert_of_mem i.2⟩ : {j // j ∈ insert a s}))
          ?_ ?_ ?_ ?_).symm
        · intro i _
          have hne : i.1 ≠ a := fun h => ha (h ▸ i.2)
          exact Finset.mem_erase.mpr ⟨fun h => hne (congrArg Subtype.val h), Finset.mem_attach _ _⟩
        · intro i1 _ i2 _ h; dsimp only at h; have hv := congrArg Subtype.val h; exact Subtype.ext hv
        · intro j hj
          have hjne : j.1 ≠ a := fun h => (Finset.mem_erase.mp (Finset.mem_coe.mp hj)).1 (Subtype.ext h)
          have hjs : j.1 ∈ s := (Finset.mem_insert.mp j.2).resolve_left hjne
          exact ⟨⟨j.1, hjs⟩, Finset.mem_coe.mpr (Finset.mem_univ _), Subtype.ext rfl⟩
        · intro i _
          have hne : i.1 ≠ a := fun h => ha (h ▸ i.2)
          simp [eA, eB, hne]
    exact hsplit

-- Main theorem proof inside MainProof section!
set_option maxHeartbeats 1200000 in
theorem main (hz : 0 < z) (hz1 : z ≠ 1) :
    let comps := (Finset.univ : Finset (V n)).image (fun u =>
      (Finset.univ : Finset (V n)).filter (fun v =>
        @decide (Relation.ReflTransGen (adj n σ τ A) u v) (Classical.propDecidable _)))
    let deg := fun u : V n => (Finset.univ.filter (fun v : V n => adj n σ τ A u v)).card
    let factor := fun D : Finset (V n) =>
      if (∀ u ∈ D, deg u = 2) then 3 * 2 ^ (D.card / 2 - 2) else 2 ^ (D.card / 2)
    let energy := fun y : V n → Bool =>
      (Finset.univ.filter (fun i : Fin n => y (false, i) ≠ y (true, i))).card +
      (Finset.univ.filter (fun i : Fin n => y (false, i) ≠ y (true, σ i))).card +
      (Finset.univ.filter (fun i : Fin n => y (false, i) = y (true, τ i))).card
    let Z := fun (P Q : Finset (V n)) =>
      ∑ y : V n → Bool, if (∀ u ∈ P, u.2 ∈ A → y u = false) ∧
        (∀ v ∈ Q, v.2 ∉ A → y v = false) then z ^ (energy y) else 0
    ∀ d : ℕ, (∃ f g : Fin d → Finset (V n) → ℚ,
      ∀ P Q, Z P Q = ∑ j : Fin d, f j P * g j Q) ↔ (∏ D ∈ comps, factor D) ≤ d := by
  classical
  intro comps deg factor energy Z d
  rw [show (∃ f g : Fin d → Finset (V n) → ℚ, ∀ P Q, Z P Q = ∑ j : Fin d, f j P * g j Q) ↔
      HasRankLe Z d from Iff.rfl, hasRankLe_iff_rowRank_le]
  suffices hrank : rowRank Z = ∏ D ∈ comps, factor D by rw [hrank]
  -- Step 1: Spin matrix M_spin on LeftCfg × RightCfg, show rowRank Z = rowRank M_spin via Möbius inversion!
  let LeftCfg := {u : V n // u.2 ∈ A} → Bool
  let RightCfg := {u : V n // u.2 ∉ A} → Bool
  let comb : LeftCfg → RightCfg → (V n → Bool) :=
    fun x w u => if h : u.2 ∈ A then x ⟨u, h⟩ else w ⟨u, h⟩
  let eCfg : LeftCfg × RightCfg ≃ (V n → Bool) :=
    { toFun := fun p => comb p.1 p.2
      invFun := fun y => (fun u => y u.1, fun u => y u.1)
      left_inv := fun ⟨x, w⟩ => by
        ext ⟨u, hu⟩
        · simp [comb, hu]
        · simp [comb, hu]
      right_inv := fun y => by
        ext u; by_cases hu : u.2 ∈ A <;> simp [comb, hu] }
  let Mspin : LeftCfg → RightCfg → ℚ := fun x w => z ^ energy (comb x w)
  let VA : Finset (V n) := Finset.univ.filter (fun u : V n => u.2 ∈ A)
  let VB : Finset (V n) := Finset.univ.filter (fun u : V n => u.2 ∉ A)
  let IL : Finset (V n) → LeftCfg → ℚ :=
    fun P x => if ∀ u ∈ P, ∀ h : u.2 ∈ A, x ⟨u, h⟩ = false then 1 else 0
  let IR : Finset (V n) → RightCfg → ℚ :=
    fun Q w => if ∀ v ∈ Q, ∀ h : v.2 ∉ A, w ⟨v, h⟩ = false then 1 else 0
  have hZ_eq : ∀ P Q : Finset (V n), Z P Q = ∑ x : LeftCfg, ∑ w : RightCfg, IL P x * Mspin x w * IR Q w := by
    intro P Q
    dsimp [Z]
    rw [← Equiv.sum_comp eCfg, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun w _ => ?_
    have hL_iff : (∀ u ∈ P, u.2 ∈ A → comb x w u = false) ↔ (∀ u ∈ P, ∀ h : u.2 ∈ A, x ⟨u, h⟩ = false) := by
      constructor <;> intro h u hu huA <;> simpa [comb, huA] using h u hu huA
    have hR_iff : (∀ v ∈ Q, v.2 ∉ A → comb x w v = false) ↔ (∀ v ∈ Q, ∀ h : v.2 ∉ A, w ⟨v, h⟩ = false) := by
      constructor <;> intro h v hv hvA <;> simpa [comb, hvA] using h v hv hvA
    change (if (∀ u ∈ P, u.2 ∈ A → comb x w u = false) ∧ (∀ v ∈ Q, v.2 ∉ A → comb x w v = false)
            then z ^ energy (comb x w) else 0) =
      (if ∀ u ∈ P, ∀ h : u.2 ∈ A, x ⟨u, h⟩ = false then (1 : ℚ) else 0) * z ^ energy (comb x w) *
      (if ∀ v ∈ Q, ∀ h : v.2 ∉ A, w ⟨v, h⟩ = false then (1 : ℚ) else 0)
    by_cases h1 : ∀ u ∈ P, ∀ h : u.2 ∈ A, x ⟨u, h⟩ = false <;>
      by_cases h2 : ∀ v ∈ Q, ∀ h : v.2 ∉ A, w ⟨v, h⟩ = false
    · rw [if_pos ⟨hL_iff.mpr h1, hR_iff.mpr h2⟩, if_pos h1, if_pos h2]; ring
    · rw [if_neg (fun h => h2 (hR_iff.mp h.2)), if_pos h1, if_neg h2]; ring
    · rw [if_neg (fun h => h1 (hL_iff.mp h.1)), if_neg h1, if_pos h2]; ring
    · rw [if_neg (fun h => h1 (hL_iff.mp h.1)), if_neg h1, if_neg h2]; ring
  -- Möbius inverses on VA and VB!
  let SL : LeftCfg → Finset (V n) := fun x => Finset.univ.filter (fun u : V n => ∃ h : u.2 ∈ A, x ⟨u, h⟩ = false)
  let SR : RightCfg → Finset (V n) := fun w => Finset.univ.filter (fun v : V n => ∃ h : v.2 ∉ A, w ⟨v, h⟩ = false)
  let MobL : LeftCfg → Finset (V n) → ℚ := fun x0 P =>
    if SL x0 ⊆ P ∧ P ⊆ VA then (-1 : ℚ) ^ (P.card - (SL x0).card) else 0
  let MobR : RightCfg → Finset (V n) → ℚ := fun w0 Q =>
    if SR w0 ⊆ Q ∧ Q ⊆ VB then (-1 : ℚ) ^ (Q.card - (SR w0).card) else 0
  have hmob_aux : ∀ (S0 S1 : Finset (V n)),
      (∑ P ∈ Finset.univ.filter (fun P : Finset (V n) => S0 ⊆ P ∧ P ⊆ S1),
        (-1 : ℚ) ^ (P.card - S0.card)) = if S0 = S1 then 1 else 0 := by
    intro S0 S1
    by_cases hsub : S0 ⊆ S1
    · have hbij : (∑ P ∈ Finset.univ.filter (fun P : Finset (V n) => S0 ⊆ P ∧ P ⊆ S1),
          (-1 : ℚ) ^ (P.card - S0.card)) = ∑ R ∈ (S1 \ S0).powerset, (-1 : ℚ) ^ R.card := by
        refine (Finset.sum_nbij (fun R : Finset (V n) => S0 ∪ R) ?_ ?_ ?_ ?_).symm
        · intro R hR
          have hRs : R ⊆ S1 \ S0 := Finset.mem_powerset.mp hR
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.subset_union_left,
            Finset.union_subset hsub (hRs.trans Finset.sdiff_subset)⟩
        · intro R1 hR1 R2 hR2 hEq
          have hd1 : Disjoint S0 R1 := Finset.disjoint_sdiff.mono_right (Finset.mem_powerset.mp hR1)
          have hd2 : Disjoint S0 R2 := Finset.disjoint_sdiff.mono_right (Finset.mem_powerset.mp hR2)
          have h1 : (S0 ∪ R1) \ S0 = R1 := Finset.union_sdiff_cancel_left hd1
          have h2 : (S0 ∪ R2) \ S0 = R2 := Finset.union_sdiff_cancel_left hd2
          dsimp only at hEq
          rw [← h1, ← h2, hEq]
        · intro P hP
          obtain ⟨_, h0P, hP1⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hP)
          refine ⟨P \ S0, Finset.mem_coe.mpr (Finset.mem_powerset.mpr (Finset.sdiff_subset_sdiff hP1 (Finset.Subset.refl S0))), ?_⟩
          exact Finset.union_sdiff_of_subset h0P
        · intro R hR
          have hd : Disjoint S0 R := Finset.disjoint_sdiff.mono_right (Finset.mem_powerset.mp hR)
          rw [Finset.card_union_of_disjoint hd, Nat.add_sub_cancel_left]
      rw [hbij]
      have hpow : (∑ R ∈ (S1 \ S0).powerset, (-1 : ℚ) ^ R.card) = ((-1 : ℚ) + 1) ^ (S1 \ S0).card := by
        have h1 := Finset.prod_add (fun _ : V n => (-1 : ℚ)) (fun _ : V n => (1 : ℚ)) (S1 \ S0)
        simpa [Finset.prod_const] using h1.symm
      rw [hpow]
      by_cases hEq : S0 = S1
      · subst hEq; simp
      · rw [if_neg hEq]
        have hpos : 0 < (S1 \ S0).card := Finset.card_pos.mpr (Finset.sdiff_nonempty.mpr (fun h => hEq (Finset.Subset.antisymm hsub h)))
        rw [show (-1 : ℚ) + 1 = 0 by ring, zero_pow (by omega)]
    · have hne : S0 ≠ S1 := fun h => hsub (h ▸ Finset.Subset.refl _)
      rw [if_neg hne]
      refine Finset.sum_eq_zero fun P hP => ?_
      obtain ⟨_, h0P, hP1⟩ := Finset.mem_filter.mp hP
      exact absurd (h0P.trans hP1) hsub
  have hMobL : ∀ x0 x : LeftCfg, ∑ P : Finset (V n), MobL x0 P * IL P x = if x = x0 then 1 else 0 := by
    intro x0 x
    have hfilt : (∑ P : Finset (V n), MobL x0 P * IL P x) =
        ∑ P ∈ Finset.univ.filter (fun P : Finset (V n) => SL x0 ⊆ P ∧ P ⊆ SL x), (-1 : ℚ) ^ (P.card - (SL x0).card) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun P _ => ?_
      dsimp [MobL, IL]
      have hSL_sub : SL x ⊆ VA := fun u hu => Finset.mem_filter.mpr ⟨Finset.mem_univ u, (Finset.mem_filter.mp hu).2.1⟩
      by_cases h1 : SL x0 ⊆ P ∧ P ⊆ VA
      · rw [if_pos h1]
        have hP_SL : (∀ u ∈ P, ∀ h : u.2 ∈ A, x ⟨u, h⟩ = false) ↔ P ⊆ SL x := by
          constructor
          · intro h u hu
            have huA : u.2 ∈ A := (Finset.mem_filter.mp (h1.2 hu)).2
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, huA, h u hu huA⟩
          · intro h u hu huA
            obtain ⟨_, _, hx⟩ := Finset.mem_filter.mp (h hu)
            exact hx
        by_cases h2 : P ⊆ SL x
        · rw [if_pos (hP_SL.mpr h2), if_pos ⟨h1.1, h2⟩, mul_one]
        · rw [if_neg (fun h => h2 (hP_SL.mp h)), if_neg (fun h => h2 h.2), mul_zero]
      · rw [if_neg h1, zero_mul]
        have hnot : ¬ (SL x0 ⊆ P ∧ P ⊆ SL x) := fun ⟨a, b⟩ => h1 ⟨a, b.trans hSL_sub⟩
        rw [if_neg hnot]
    rw [hfilt, hmob_aux]
    have hiff : SL x0 = SL x ↔ x = x0 := by
      constructor
      · intro hEq; ext ⟨u, huA⟩
        have hm : u ∈ SL x0 ↔ u ∈ SL x := by rw [hEq]
        simp only [SL, Finset.mem_filter, Finset.mem_univ, true_and] at hm
        cases h1 : x ⟨u, huA⟩ <;> cases h2 : x0 ⟨u, huA⟩ <;> simp_all
      · rintro rfl; rfl
    by_cases h : x = x0 <;> simp [h, hiff]
  have hMobR : ∀ w0 w : RightCfg, ∑ Q : Finset (V n), MobR w0 Q * IR Q w = if w = w0 then 1 else 0 := by
    intro w0 w
    have hfilt : (∑ Q : Finset (V n), MobR w0 Q * IR Q w) =
        ∑ Q ∈ Finset.univ.filter (fun Q : Finset (V n) => SR w0 ⊆ Q ∧ Q ⊆ SR w), (-1 : ℚ) ^ (Q.card - (SR w0).card) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun Q _ => ?_
      dsimp [MobR, IR]
      have hSR_sub : SR w ⊆ VB := fun v hv => Finset.mem_filter.mpr ⟨Finset.mem_univ v, (Finset.mem_filter.mp hv).2.1⟩
      by_cases h1 : SR w0 ⊆ Q ∧ Q ⊆ VB
      · rw [if_pos h1]
        have hQ_SR : (∀ v ∈ Q, ∀ h : v.2 ∉ A, w ⟨v, h⟩ = false) ↔ Q ⊆ SR w := by
          constructor
          · intro h v hv
            have hvA : v.2 ∉ A := (Finset.mem_filter.mp (h1.2 hv)).2
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, hvA, h v hv hvA⟩
          · intro h v hv hvA
            obtain ⟨_, _, hw⟩ := Finset.mem_filter.mp (h hv)
            exact hw
        by_cases h2 : Q ⊆ SR w
        · rw [if_pos (hQ_SR.mpr h2), if_pos ⟨h1.1, h2⟩, mul_one]
        · rw [if_neg (fun h => h2 (hQ_SR.mp h)), if_neg (fun h => h2 h.2), mul_zero]
      · rw [if_neg h1, zero_mul]
        have hnot : ¬ (SR w0 ⊆ Q ∧ Q ⊆ SR w) := fun ⟨a, b⟩ => h1 ⟨a, b.trans hSR_sub⟩
        rw [if_neg hnot]
    rw [hfilt, hmob_aux]
    have hiff : SR w0 = SR w ↔ w = w0 := by
      constructor
      · intro hEq; ext ⟨v, hvA⟩
        have hm : v ∈ SR w0 ↔ v ∈ SR w := by rw [hEq]
        simp only [SR, Finset.mem_filter, Finset.mem_univ, true_and] at hm
        cases h1 : w ⟨v, hvA⟩ <;> cases h2 : w0 ⟨v, hvA⟩ <;> simp_all
      · rintro rfl; rfl
    by_cases h : w = w0 <;> simp [h, hiff]
  have hrank_Z_spin : rowRank Z = rowRank Mspin := by
    apply rowRank_eq_of_iff
    intro k
    constructor
    · intro h
      have h1 := hasRankLe_mul_left MobL Z h
      have h2 := hasRankLe_mul_right _ (fun Q w0 => MobR w0 Q) h1
      have hEq : (fun x0 w0 => ∑ Q : Finset (V n), (∑ P : Finset (V n), MobL x0 P * Z P Q) * MobR w0 Q) = Mspin := by
        ext x0 w0
        simp_rw [hZ_eq]
        have hinner : ∀ Q : Finset (V n),
            (∑ P : Finset (V n), MobL x0 P * ∑ x : LeftCfg, ∑ w : RightCfg, IL P x * Mspin x w * IR Q w) =
            ∑ w : RightCfg, Mspin x0 w * IR Q w := by
          intro Q
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          have h1' : ∀ x : LeftCfg,
              (∑ P : Finset (V n), ∑ w : RightCfg, MobL x0 P * (IL P x * Mspin x w * IR Q w)) =
              (∑ P : Finset (V n), MobL x0 P * IL P x) * ∑ w : RightCfg, Mspin x w * IR Q w := by
            intro x
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun P _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun w _ => by ring
          simp_rw [h1', hMobL x0]
          simp
        simp_rw [hinner, Finset.sum_mul]
        rw [Finset.sum_comm]
        have h2' : ∀ w : RightCfg,
            (∑ Q : Finset (V n), Mspin x0 w * IR Q w * MobR w0 Q) =
            Mspin x0 w * ∑ Q : Finset (V n), MobR w0 Q * IR Q w := by
          intro w; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun Q _ => by ring
        simp_rw [h2', hMobR w0]
        simp
      rwa [hEq] at h2
    · intro h
      have h1 := hasRankLe_mul_left IL Mspin h
      have h2 := hasRankLe_mul_right _ (fun w Q => IR Q w) h1
      have hEq : (fun P Q => ∑ w : RightCfg, (∑ x : LeftCfg, IL P x * Mspin x w) * IR Q w) = Z := by
        ext P Q; rw [hZ_eq, Finset.sum_comm]
        refine Finset.sum_congr rfl fun w _ => by rw [Finset.sum_mul]
      rwa [hEq] at h2
  rw [hrank_Z_spin]
  -- Step 2: Factor out internal edges & coincident crossing edges -> M_cross!
  let M_cross : LeftCfg → RightCfg → ℚ := fun x w =>
    (∏ i ∈ Finset.univ.filter (fun i : Fin n => (i ∈ A ↔ σ i ∉ A) ∧ σ i ≠ τ i),
      edgeW z true (comb x w (false, i)) (comb x w (true, σ i))) *
    (∏ i ∈ Finset.univ.filter (fun i : Fin n => (i ∈ A ↔ τ i ∉ A) ∧ σ i ≠ τ i),
      edgeW z false (comb x w (false, i)) (comb x w (true, τ i)))
  let cL : LeftCfg → ℚ := fun x =>
    z ^ ((Finset.univ.filter (fun i : Fin n => ∃ h : i ∈ A, x ⟨(false, i), h⟩ ≠ x ⟨(true, i), h⟩)).card +
         (Finset.univ.filter (fun i : Fin n => ∃ h1 : i ∈ A, ∃ h2 : σ i ∈ A, x ⟨(false, i), h1⟩ ≠ x ⟨(true, σ i), h2⟩)).card +
         (Finset.univ.filter (fun i : Fin n => ∃ h1 : i ∈ A, ∃ h2 : τ i ∈ A, x ⟨(false, i), h1⟩ = x ⟨(true, τ i), h2⟩)).card +
         (Finset.univ.filter (fun i : Fin n => (i ∈ A ↔ σ i ∉ A) ∧ σ i = τ i)).card)
  let cR : RightCfg → ℚ := fun w =>
    z ^ ((Finset.univ.filter (fun i : Fin n => ∃ h : i ∉ A, w ⟨(false, i), h⟩ ≠ w ⟨(true, i), h⟩)).card +
         (Finset.univ.filter (fun i : Fin n => ∃ h1 : i ∉ A, ∃ h2 : σ i ∉ A, w ⟨(false, i), h1⟩ ≠ w ⟨(true, σ i), h2⟩)).card +
         (Finset.univ.filter (fun i : Fin n => ∃ h1 : i ∉ A, ∃ h2 : τ i ∉ A, w ⟨(false, i), h1⟩ = w ⟨(true, τ i), h2⟩)).card)
  have hMspin_eq : Mspin = fun x w => cL x * (M_cross x w * cR w) := by
    ext x w
    have hprod_card : ∀ (s : Finset (Fin n)) (P : Fin n → Prop) [DecidablePred P],
        (∏ i ∈ s, if P i then z else 1) = z ^ (s.filter P).card := by
      intro s P _
      rw [← Finset.prod_filter_mul_prod_filter_not s P,
          Finset.prod_congr rfl (fun i hi => if_pos (Finset.mem_filter.mp hi).2),
          Finset.prod_congr rfl (fun i hi => if_neg (Finset.mem_filter.mp hi).2),
          Finset.prod_const, Finset.prod_const, one_pow, mul_one]
    have hcross_pow : M_cross x w =
        z ^ ((Finset.univ.filter (fun i : Fin n => (i ∈ A ↔ σ i ∉ A) ∧ σ i ≠ τ i ∧ comb x w (false, i) ≠ comb x w (true, σ i))).card +
             (Finset.univ.filter (fun i : Fin n => (i ∈ A ↔ τ i ∉ A) ∧ σ i ≠ τ i ∧ comb x w (false, i) = comb x w (true, τ i))).card) := by
      dsimp [M_cross, edgeW]
      rw [hprod_card, hprod_card, ← pow_add, Finset.filter_filter, Finset.filter_filter]
      refine congrArg (z ^ ·) (congrArg₂ (· + ·) (congrArg Finset.card ?_) (congrArg Finset.card ?_)) <;>
        (ext i; simp [and_assoc])
    dsimp [Mspin, cL, cR]
    rw [hcross_pow, ← pow_add, ← pow_add]
    congr 1
    dsimp [energy]
    -- Count each of the 3 edge families pointwise over i : Fin n!
    have hsum_card : ∀ (P : Fin n → Prop) [DecidablePred P],
        (Finset.univ.filter P).card = ∑ i : Fin n, if P i then 1 else 0 :=
      fun P _ => Finset.card_filter P Finset.univ
    simp_rw [hsum_card, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hL1 : (∃ h : i ∈ A, x ⟨(false, i), h⟩ ≠ x ⟨(true, i), h⟩) ↔
        i ∈ A ∧ comb x w (false, i) ≠ comb x w (true, i) := by
      constructor
      · rintro ⟨h, hne⟩; exact ⟨h, by simpa [comb, h] using hne⟩
      · rintro ⟨h, hne⟩; exact ⟨h, by simpa [comb, h] using hne⟩
    have hL2 : (∃ h1 : i ∈ A, ∃ h2 : σ i ∈ A, x ⟨(false, i), h1⟩ ≠ x ⟨(true, σ i), h2⟩) ↔
        i ∈ A ∧ σ i ∈ A ∧ comb x w (false, i) ≠ comb x w (true, σ i) := by
      constructor
      · rintro ⟨h1, h2, hne⟩; exact ⟨h1, h2, by simpa [comb, h1, h2] using hne⟩
      · rintro ⟨h1, h2, hne⟩; exact ⟨h1, h2, by simpa [comb, h1, h2] using hne⟩
    have hL3 : (∃ h1 : i ∈ A, ∃ h2 : τ i ∈ A, x ⟨(false, i), h1⟩ = x ⟨(true, τ i), h2⟩) ↔
        i ∈ A ∧ τ i ∈ A ∧ comb x w (false, i) = comb x w (true, τ i) := by
      constructor
      · rintro ⟨h1, h2, heq⟩; exact ⟨h1, h2, by simpa [comb, h1, h2] using heq⟩
      · rintro ⟨h1, h2, heq⟩; exact ⟨h1, h2, by simpa [comb, h1, h2] using heq⟩
    have hR1 : (∃ h : i ∉ A, w ⟨(false, i), h⟩ ≠ w ⟨(true, i), h⟩) ↔
        i ∉ A ∧ comb x w (false, i) ≠ comb x w (true, i) := by
      constructor
      · rintro ⟨h, hne⟩; exact ⟨h, by simpa [comb, h] using hne⟩
      · rintro ⟨h, hne⟩; exact ⟨h, by simpa [comb, h] using hne⟩
    have hR2 : (∃ h1 : i ∉ A, ∃ h2 : σ i ∉ A, w ⟨(false, i), h1⟩ ≠ w ⟨(true, σ i), h2⟩) ↔
        i ∉ A ∧ σ i ∉ A ∧ comb x w (false, i) ≠ comb x w (true, σ i) := by
      constructor
      · rintro ⟨h1, h2, hne⟩; exact ⟨h1, h2, by simpa [comb, h1, h2] using hne⟩
      · rintro ⟨h1, h2, hne⟩; exact ⟨h1, h2, by simpa [comb, h1, h2] using hne⟩
    have hR3 : (∃ h1 : i ∉ A, ∃ h2 : τ i ∉ A, w ⟨(false, i), h1⟩ = w ⟨(true, τ i), h2⟩) ↔
        i ∉ A ∧ τ i ∉ A ∧ comb x w (false, i) = comb x w (true, τ i) := by
      constructor
      · rintro ⟨h1, h2, heq⟩; exact ⟨h1, h2, by simpa [comb, h1, h2] using heq⟩
      · rintro ⟨h1, h2, heq⟩; exact ⟨h1, h2, by simpa [comb, h1, h2] using heq⟩
    simp_rw [hL1, hL2, hL3, hR1, hR2, hR3]
    by_cases hst : σ i = τ i
    · rw [hst]
      by_cases hi : i ∈ A <;> by_cases hti : τ i ∈ A <;>
        cases comb x w (false, i) <;> cases comb x w (true, i) <;> cases comb x w (true, τ i) <;>
        simp [hi, hti]
    · by_cases hi : i ∈ A <;> by_cases hsi : σ i ∈ A <;> by_cases hti : τ i ∈ A <;>
        cases comb x w (false, i) <;> cases comb x w (true, i) <;>
        cases comb x w (true, σ i) <;> cases comb x w (true, τ i) <;>
        simp [hst, hi, hsi, hti]
  have hz_ne : z ≠ 0 := ne_of_gt hz
  rw [hMspin_eq, rowRank_diag_left cL (fun _ => pow_ne_zero _ hz_ne),
      rowRank_diag_right cR (fun _ => pow_ne_zero _ hz_ne)]
  -- Step 3: Partition V n by comps and apply rowRank_finset_kronecker!
  have hcomp_of : ∀ u : V n, (Finset.univ : Finset (V n)).filter (fun v =>
      @decide (Relation.ReflTransGen (adj n σ τ A) u v) (Classical.propDecidable _)) ∈ comps :=
    fun u => Finset.mem_image.mpr ⟨u, Finset.mem_univ u, rfl⟩
  let compOf : V n → {D : Finset (V n) // D ∈ comps} := fun u =>
    ⟨(Finset.univ : Finset (V n)).filter (fun v =>
      @decide (Relation.ReflTransGen (adj n σ τ A) u v) (Classical.propDecidable _)), hcomp_of u⟩
  have hmem_compOf : ∀ u : V n, u ∈ (compOf u).1 := fun u => by simp [compOf, Relation.ReflTransGen.refl]
  have hcomp_uniq : ∀ (D : Finset (V n)) (hD : D ∈ comps) (u : V n), u ∈ D → compOf u = ⟨D, hD⟩ := by
    intro D hD u hu
    obtain ⟨u0, _, rfl⟩ := Finset.mem_image.mp hD
    apply Subtype.ext; ext v
    simp only [compOf, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hu ⊢
    exact ⟨fun h => hu.trans h, fun h => (rtg_symm n σ τ A u0 u hu).trans h⟩
  let eL_prod : ((D : {D // D ∈ comps}) → LeftD n A D.1) ≃ LeftCfg :=
    { toFun := fun xs u => xs (compOf u.1) ⟨u.1, hmem_compOf u.1, u.2⟩
      invFun := fun x D u => x ⟨u.1, u.2.2⟩
      left_inv := fun xs => by
        ext ⟨D, hD⟩ ⟨u, huD, huA⟩
        have hEq : compOf u = ⟨D, hD⟩ := hcomp_uniq D hD u huD
        cases hEq; rfl
      right_inv := fun x => by ext ⟨u, huA⟩; rfl }
  let eR_prod : ((D : {D // D ∈ comps}) → RightD n A D.1) ≃ RightCfg :=
    { toFun := fun ws u => ws (compOf u.1) ⟨u.1, hmem_compOf u.1, u.2⟩
      invFun := fun w D u => w ⟨u.1, u.2.2⟩
      left_inv := fun ws => by
        ext ⟨D, hD⟩ ⟨u, huD, huA⟩
        have hEq : compOf u = ⟨D, hD⟩ := hcomp_uniq D hD u huD
        cases hEq; rfl
      right_inv := fun w => by ext ⟨u, huA⟩; rfl }
  rw [← rowRank_reindex eL_prod eR_prod M_cross]
  have hMcross_prod : (fun xs ws => M_cross (eL_prod xs) (eR_prod ws)) =
      fun xs ws => ∏ D : {D // D ∈ comps}, Mcomp n σ τ A z D.1 (xs D) (ws D) := by
    ext xs ws
    dsimp only [M_cross]
    unfold Mcomp
    rw [Finset.prod_mul_distrib]
    have hval_eq : ∀ (D : {D // D ∈ comps}) (u : V n), u ∈ D.1 →
        valD n A D.1 (xs D) (ws D) u = comb (eL_prod xs) (eR_prod ws) u := by
      intro D u huD
      unfold valD
      dsimp only [comb]
      rw [dif_pos huD]
      have hEq : compOf u = D := hcomp_uniq D.1 D.2 u huD
      by_cases huA : u.2 ∈ A
      · rw [dif_pos huA, dif_pos huA]; dsimp [eL_prod]; cases hEq; rfl
      · rw [dif_neg huA, dif_neg huA]; dsimp [eR_prod]; cases hEq; rfl
    have hpart_prod : ∀ (P : Fin n → Prop) [DecidablePred P] (g : Fin n → ℚ),
        (∏ i ∈ Finset.univ.filter P, g i) =
        ∏ D : {D // D ∈ comps}, ∏ i ∈ Finset.univ.filter (fun i : Fin n => (false, i) ∈ D.1 ∧ P i), g i := by
      intro P _ g
      rw [← Finset.prod_biUnion]
      · refine Finset.prod_congr ?_ fun _ _ => rfl
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
        exact ⟨fun hP => ⟨compOf (false, i), hmem_compOf (false, i), hP⟩, fun ⟨_, _, hP⟩ => hP⟩
      · intro D1 _ D2 _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro i hi1 hi2
        have h1 := (Finset.mem_filter.mp hi1).2.1
        have h2 := (Finset.mem_filter.mp hi2).2.1
        exact hne ((hcomp_uniq D1.1 D1.2 (false, i) h1).symm.trans (hcomp_uniq D2.1 D2.2 (false, i) h2))
    congr 1
    · rw [hpart_prod (fun i : Fin n => (i ∈ A ↔ σ i ∉ A) ∧ σ i ≠ τ i)]
      refine Finset.prod_congr rfl fun D _ => Finset.prod_congr (by ext i; simp) fun i hi => ?_
      obtain ⟨_, hiD, h1, h2⟩ := Finset.mem_filter.mp hi
      have hsiD : (true, σ i) ∈ D.1 := by
        obtain ⟨u0, _, hDeq⟩ := Finset.mem_image.mp D.2
        have hreach : Relation.ReflTransGen (adj n σ τ A) u0 (false, i) := by
          have := hiD; rw [← hDeq] at this; exact (Finset.mem_filter.mp this).2 |> of_decide_eq_true
        have hadj : adj n σ τ A (false, i) (true, σ i) := Or.inl ⟨rfl, rfl, h1, h2, Or.inl rfl⟩
        rw [← hDeq]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, decide_eq_true (hreach.tail hadj)⟩
      rw [hval_eq D (false, i) hiD, hval_eq D (true, σ i) hsiD]
    · rw [hpart_prod (fun i : Fin n => (i ∈ A ↔ τ i ∉ A) ∧ σ i ≠ τ i)]
      refine Finset.prod_congr rfl fun D _ => Finset.prod_congr (by ext i; simp) fun i hi => ?_
      obtain ⟨_, hiD, h1, h2⟩ := Finset.mem_filter.mp hi
      have htiD : (true, τ i) ∈ D.1 := by
        obtain ⟨u0, _, hDeq⟩ := Finset.mem_image.mp D.2
        have hreach : Relation.ReflTransGen (adj n σ τ A) u0 (false, i) := by
          have := hiD; rw [← hDeq] at this; exact (Finset.mem_filter.mp this).2 |> of_decide_eq_true
        have hadj : adj n σ τ A (false, i) (true, τ i) := Or.inl ⟨rfl, rfl, h1, h2, Or.inr rfl⟩
        rw [← hDeq]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, decide_eq_true (hreach.tail hadj)⟩
      rw [hval_eq D (false, i) hiD, hval_eq D (true, τ i) htiD]
  rw [hMcross_prod, rowRank_finset_kronecker (LeftD n A) (RightD n A) (Mcomp n σ τ A z) comps]
  refine Finset.prod_congr rfl fun D hD => ?_
  obtain ⟨u0, _, rfl⟩ := Finset.mem_image.mp hD
  exact rowRank_Mcomp n σ τ A z hz hz1 u0

end MainProof

end
end PEqualNP.Outside.L_pcx_416_aux

theorem PEqualNP.Outside.L_pcx_416 : ∀ (n : ℕ) (σ τ : Equiv.Perm (Fin n)) (A : Finset (Fin n)) (z : ℚ),
  0 < z → z ≠ 1 →
  let V := Bool × Fin n
  let X := V → Bool
  let arc := fun (u v : V) =>
    u.1 = false ∧ v.1 = true ∧ (u.2 ∈ A ↔ v.2 ∉ A) ∧
    σ u.2 ≠ τ u.2 ∧ (v.2 = σ u.2 ∨ v.2 = τ u.2)
  let adj := fun (u v : V) => arc u v ∨ arc v u
  let comps := (Finset.univ : Finset V).image (fun u =>
    (Finset.univ : Finset V).filter (fun v =>
      @decide (Relation.ReflTransGen adj u v) (Classical.propDecidable _)))
  let deg := fun u : V => (Finset.univ.filter (fun v : V => adj u v)).card
  let factor := fun D : Finset V =>
    if (∀ u ∈ D, deg u = 2) then 3 * 2^(D.card/2-2) else 2^(D.card/2)
  let energy := fun y : X =>
    (Finset.univ.filter (fun i : Fin n => y (false,i) ≠ y (true,i))).card +
    (Finset.univ.filter (fun i : Fin n => y (false,i) ≠ y (true,σ i))).card +
    (Finset.univ.filter (fun i : Fin n => y (false,i) = y (true,τ i))).card
  let Z := fun (P Q : Finset V) =>
    ∑ y : X, if (∀ u ∈ P, u.2 ∈ A → y u = false) ∧
      (∀ v ∈ Q, v.2 ∉ A → y v = false) then z^(energy y) else 0
  ∀ d : ℕ, (∃ f g : Fin d → Finset V → ℚ,
    ∀ P Q, Z P Q = ∑ j : Fin d, f j P * g j Q) ↔ (∏ D ∈ comps, factor D) ≤ d :=
  fun n σ τ A z hz hz1 => PEqualNP.Outside.L_pcx_416_aux.main n σ τ A z hz hz1


