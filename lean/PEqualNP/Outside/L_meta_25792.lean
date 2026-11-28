import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25792

abbrev Vec (n : ℕ) := Fin n → ZMod 2

def capFun (r s : ℕ) : ℕ :=
  2 ^ (min s (r - 1)) * (r - min s (r - 1))

lemma capFun_zero (s : ℕ) : capFun 0 s = 0 := by
  simp [capFun]

lemma capFun_step_mono_aux {r a b : ℕ} (hab : a ≤ b) (hbr : b ≤ r - 1) :
    2 ^ a * (r - a) ≤ 2 ^ b * (r - b) := by
  induction b with
  | zero =>
    have ha : a = 0 := Nat.eq_zero_of_le_zero hab
    subst ha; exact le_rfl
  | succ b ih =>
    rcases Nat.eq_or_lt_of_le hab with rfl | hlt
    · exact le_rfl
    · have hab' : a ≤ b := Nat.lt_succ_iff.mp hlt
      have hbr' : b ≤ r - 1 := by omega
      calc
        2 ^ a * (r - a) ≤ 2 ^ b * (r - b) := ih hab' hbr'
        _ ≤ 2 ^ (b + 1) * (r - (b + 1)) := by
          rw [pow_succ, mul_assoc]
          apply Nat.mul_le_mul_left
          omega

lemma capFun_mono_s {r s₁ s₂ : ℕ} (hs : s₁ ≤ s₂) : capFun r s₁ ≤ capFun r s₂ := by
  unfold capFun
  exact capFun_step_mono_aux (min_le_min_right (r - 1) hs) (min_le_right _ _)

lemma capFun_forced (r s : ℕ) : 1 + capFun r s ≤ capFun (r + 1) s := by
  unfold capFun
  cases r with
  | zero =>
    simp
  | succ r =>
    simp only [Nat.add_sub_cancel]
    by_cases hs : s ≤ r
    · have h1 : min s r = s := min_eq_left hs
      have h2 : min s (r + 1) = s := min_eq_left (by omega)
      rw [h1, h2]
      have hpos : 1 ≤ 2 ^ s := Nat.one_le_two_pow
      have hsub : r + 2 - s = (r + 1 - s) + 1 := by omega
      rw [hsub, Nat.mul_add, Nat.mul_one]
      omega
    · have h1 : min s r = r := min_eq_right (by omega)
      have h2 : min s (r + 1) = r + 1 := min_eq_right (by omega)
      rw [h1, h2]
      have hsub1 : r + 1 - r = 1 := by omega
      have hsub2 : r + 2 - (r + 1) = 1 := by omega
      rw [hsub1, hsub2, mul_one, mul_one, pow_succ]
      have hpos : 1 ≤ 2 ^ r := Nat.one_le_two_pow
      omega

lemma capFun_split {r s : ℕ} (hs : 1 ≤ s) :
    2 * capFun r (s - 1) ≤ capFun (r + 1) s := by
  unfold capFun
  cases r with
  | zero =>
    simp
  | succ r =>
    simp only [Nat.add_sub_cancel]
    have hmin : min s (r + 1) = min (s - 1) r + 1 := by omega
    rw [hmin, pow_succ]
    have hsub : r + 2 - (min (s - 1) r + 1) = r + 1 - min (s - 1) r := by omega
    rw [hsub]
    have hcomm : 2 * (2 ^ min (s - 1) r * (r + 1 - min (s - 1) r)) =
        2 ^ min (s - 1) r * 2 * (r + 1 - min (s - 1) r) := by ring
    exact le_of_eq hcomm

lemma zmod2_eq_zero_or_one (b : ZMod 2) : b = 0 ∨ b = 1 := by
  fin_cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma zmod2_eq_one_of_ne_zero {b : ZMod 2} (hb : b ≠ 0) : b = 1 := by
  rcases zmod2_eq_zero_or_one b with rfl | rfl
  · exact absurd rfl hb
  · rfl

lemma exists_ker_and_eq_one {h k : ℕ}
    (φ : Fin k → (Vec h →ₗ[ZMod 2] ZMod 2))
    (ψ : Vec h →ₗ[ZMod 2] ZMod 2)
    (hnot : ψ ∉ Submodule.span (ZMod 2) (Set.range φ)) :
    ∃ δ : Vec h, (∀ i, φ i δ = 0) ∧ ψ δ = 1 := by
  by_contra hno
  push Not at hno
  have hker : ∀ δ : Vec h, (∀ i, φ i δ = 0) → ψ δ = 0 := by
    intro δ hδ
    by_contra hne
    exact hno δ hδ (zmod2_eq_one_of_ne_zero hne)
  let T : Vec h →ₗ[ZMod 2] Vec k :=
    { toFun := fun u i => φ i u
      map_add' := fun u₁ u₂ => by ext i; exact map_add (φ i) u₁ u₂
      map_smul' := fun c u => by ext i; exact map_smul (φ i) c u }
  have hle : LinearMap.ker T ≤ LinearMap.ker ψ := by
    intro u hu
    rw [LinearMap.mem_ker] at hu ⊢
    apply hker u
    intro i
    have := congr_fun hu i
    exact this
  let R := LinearMap.range T
  rcases Submodule.exists_isCompl R with ⟨Q, hcompl⟩
  let g₀ : R →ₗ[ZMod 2] ZMod 2 :=
    ((LinearMap.ker T).liftQ ψ hle).comp T.quotKerEquivRange.symm.toLinearMap
  let g : Vec k →ₗ[ZMod 2] ZMod 2 := g₀.comp (R.projectionOnto Q hcompl)
  have hgT : ∀ u : Vec h, g (T u) = ψ u := by
    intro u
    have hmem : T u ∈ R := LinearMap.mem_range_self T u
    have hproj : R.projectionOnto Q hcompl (T u) = ⟨T u, hmem⟩ :=
      Submodule.projectionOnto_apply_left hcompl ⟨T u, hmem⟩
    have hsymm : T.quotKerEquivRange.symm ⟨T u, hmem⟩ = Submodule.Quotient.mk u := by
      apply T.quotKerEquivRange.injective
      rw [LinearEquiv.apply_symm_apply]
      rfl
    change g₀ (R.projectionOnto Q hcompl (T u)) = ψ u
    rw [hproj]
    change (LinearMap.ker T).liftQ ψ hle (T.quotKerEquivRange.symm ⟨T u, hmem⟩) = ψ u
    rw [hsymm]
    rfl
  have hdecomp : ψ = ∑ i : Fin k, (g (Pi.single i 1)) • φ i := by
    apply LinearMap.ext
    intro u
    rw [← hgT u]
    have hTu : T u = ∑ i : Fin k, (φ i u) • Pi.single i (1 : ZMod 2) := by
      ext j
      simp [T, Finset.sum_apply, Pi.single_apply]
    rw [hTu, map_sum]
    simp [LinearMap.sum_apply, mul_comm]
  apply hnot
  rw [hdecomp]
  refine Submodule.sum_mem _ fun i _ => ?_
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

def prefixOf {q : ℕ} (ans : Fin q → ZMod 2) (k : ℕ) (hk : k ≤ q) : Fin k → ZMod 2 :=
  fun i => ans ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩

def snocVec {k : ℕ} (π : Fin k → ZMod 2) (b : ZMod 2) : Fin (k + 1) → ZMod 2 :=
  fun i => if hi : i.val < k then π ⟨i.val, hi⟩ else b

lemma snocVec_castSucc {k : ℕ} (π : Fin k → ZMod 2) (b : ZMod 2) (i : Fin k) :
    snocVec π b ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ = π i := by
  simp [snocVec, i.isLt]

lemma snocVec_last {k : ℕ} (π : Fin k → ZMod 2) (b : ZMod 2) :
    snocVec π b ⟨k, Nat.lt_succ_self k⟩ = b := by
  simp [snocVec]

lemma prefixOf_succ_eq_snoc {q k : ℕ} (ans : Fin q → ZMod 2) (hk : k + 1 ≤ q)
    (π : Fin k → ZMod 2) (hpref : prefixOf ans k (by omega) = π) :
    prefixOf ans (k + 1) hk = snocVec π (ans ⟨k, by omega⟩) := by
  ext i
  by_cases hi : i.val < k
  · have := congr_fun hpref ⟨i.val, hi⟩
    simpa [prefixOf, snocVec, hi] using this
  · have hieq : i.val = k := by omega
    simp only [prefixOf, snocVec, hi, ↓reduceDIte]
    congr 1
    exact Fin.ext hieq

def queryAt {m h q : ℕ}
    (ask : (j : Fin q) → (Fin j.val → ZMod 2) → ((Vec h × Vec m) →ₗ[ZMod 2] ZMod 2))
    (k : ℕ) (hk : k ≤ q) (π : Fin k → ZMod 2) (i : Fin k) :
    (Vec h × Vec m) →ₗ[ZMod 2] ZMod 2 :=
  ask ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ (fun j => π ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩)

def uPart {m h q : ℕ}
    (ask : (j : Fin q) → (Fin j.val → ZMod 2) → ((Vec h × Vec m) →ₗ[ZMod 2] ZMod 2))
    (k : ℕ) (hk : k ≤ q) (π : Fin k → ZMod 2) (i : Fin k) :
    Vec h →ₗ[ZMod 2] ZMod 2 :=
  (queryAt ask k hk π i).comp (LinearMap.inl (ZMod 2) (Vec h) (Vec m))

def vPart {m h q : ℕ}
    (ask : (j : Fin q) → (Fin j.val → ZMod 2) → ((Vec h × Vec m) →ₗ[ZMod 2] ZMod 2))
    (k : ℕ) (hk : k ≤ q) (π : Fin k → ZMod 2) (i : Fin k) :
    Vec m →ₗ[ZMod 2] ZMod 2 :=
  (queryAt ask k hk π i).comp (LinearMap.inr (ZMod 2) (Vec h) (Vec m))

def uSpan {m h q : ℕ}
    (ask : (j : Fin q) → (Fin j.val → ZMod 2) → ((Vec h × Vec m) →ₗ[ZMod 2] ZMod 2))
    (k : ℕ) (hk : k ≤ q) (π : Fin k → ZMod 2) :
    Submodule (ZMod 2) (Vec h →ₗ[ZMod 2] ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range (uPart ask k hk π))

lemma linearMap_prod_split {m h : ℕ} (L : (Vec h × Vec m) →ₗ[ZMod 2] ZMod 2)
    (u : Vec h) (x : Vec m) :
    L (u, x) = L.comp (LinearMap.inl (ZMod 2) (Vec h) (Vec m)) u +
      L.comp (LinearMap.inr (ZMod 2) (Vec h) (Vec m)) x := by
  have hpair : (u, x) = LinearMap.inl (ZMod 2) (Vec h) (Vec m) u +
      LinearMap.inr (ZMod 2) (Vec h) (Vec m) x := by
    ext <;> simp
  conv_lhs => rw [hpair]
  rw [map_add]
  rfl

lemma answers_prefix_eq_uPart_add_vPart {m h q : ℕ}
    (ask : (j : Fin q) → (Fin j.val → ZMod 2) → ((Vec h × Vec m) →ₗ[ZMod 2] ZMod 2))
    (answers : Vec h → Vec m → Fin q → ZMod 2)
    (hans : ∀ u x (j : Fin q),
      answers u x j = ask j (fun i => answers u x ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩) (u, x))
    {k : ℕ} (hk : k ≤ q) (π : Fin k → ZMod 2) (u : Vec h) (x : Vec m)
    (hpref : prefixOf (answers u x) k hk = π) (i : Fin k) :
    uPart ask k hk π i u + vPart ask k hk π i x = π i := by
  have hi : answers u x ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ = π i := congr_fun hpref i
  rw [← hi, hans u x ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩]
  have harg : (fun j : Fin i.val => answers u x ⟨j.val, Nat.lt_trans j.isLt (Nat.lt_of_lt_of_le i.isLt hk)⟩) =
      (fun j : Fin i.val => π ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩) := by
    ext j
    exact congr_fun hpref ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩
  rw [harg]
  exact (linearMap_prod_split (queryAt ask k hk π i) u x).symm

lemma prefixOf_eq_of_uPart {m h q : ℕ}
    (ask : (j : Fin q) → (Fin j.val → ZMod 2) → ((Vec h × Vec m) →ₗ[ZMod 2] ZMod 2))
    (answers : Vec h → Vec m → Fin q → ZMod 2)
    (hans : ∀ u x (j : Fin q),
      answers u x j = ask j (fun i => answers u x ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩) (u, x))
    {k : ℕ} (hk : k ≤ q) (π : Fin k → ZMod 2) (u : Vec h)
    (hmatch : ∀ i : Fin k, uPart ask k hk π i u = π i) :
    prefixOf (answers u 0) k hk = π := by
  ext ⟨idx, hidx⟩
  induction idx using Nat.strong_induction_on with
  | ind idx ih =>
    change answers u 0 ⟨idx, Nat.lt_of_lt_of_le hidx hk⟩ = π ⟨idx, hidx⟩
    rw [hans u 0 ⟨idx, Nat.lt_of_lt_of_le hidx hk⟩]
    have harg : (fun j : Fin idx => answers u 0 ⟨j.val, Nat.lt_trans j.isLt (Nat.lt_of_lt_of_le hidx hk)⟩) =
        (fun j : Fin idx => π ⟨j.val, Nat.lt_trans j.isLt hidx⟩) := by
      ext ⟨j, hj⟩
      exact ih j hj (Nat.lt_trans hj hidx)
    rw [harg]
    have hsplit := linearMap_prod_split (queryAt ask k hk π ⟨idx, hidx⟩) u 0
    rw [map_zero, add_zero] at hsplit
    exact hsplit.trans (hmatch ⟨idx, hidx⟩)

lemma uPart_snoc_lt {m h q : ℕ}
    (ask : (j : Fin q) → (Fin j.val → ZMod 2) → ((Vec h × Vec m) →ₗ[ZMod 2] ZMod 2))
    {k : ℕ} (hk : k + 1 ≤ q) (π : Fin k → ZMod 2) (b : ZMod 2)
    (i : Fin (k + 1)) (hi : i.val < k) :
    uPart ask (k + 1) hk (snocVec π b) i = uPart ask k (by omega) π ⟨i.val, hi⟩ := by
  unfold uPart queryAt
  congr 1
  have harg : (fun j : Fin i.val => snocVec π b ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩) =
      (fun j : Fin i.val => π ⟨j.val, Nat.lt_trans j.isLt hi⟩) := by
    ext j
    simp [snocVec, Nat.lt_trans j.isLt hi]
  rw [harg]

lemma uPart_snoc_last {m h q : ℕ}
    (ask : (j : Fin q) → (Fin j.val → ZMod 2) → ((Vec h × Vec m) →ₗ[ZMod 2] ZMod 2))
    {k : ℕ} (hk : k + 1 ≤ q) (π : Fin k → ZMod 2) (b : ZMod 2) :
    uPart ask (k + 1) hk (snocVec π b) ⟨k, Nat.lt_succ_self k⟩ =
      (ask ⟨k, by omega⟩ π).comp (LinearMap.inl (ZMod 2) (Vec h) (Vec m)) := by
  unfold uPart queryAt
  congr 1
  have harg : (fun j : Fin k => snocVec π b ⟨j.val, Nat.lt_trans j.isLt (Nat.lt_succ_self k)⟩) = π := by
    ext j
    simp [snocVec, j.isLt]
  rw [harg]

lemma uSpan_snoc {m h q : ℕ}
    (ask : (j : Fin q) → (Fin j.val → ZMod 2) → ((Vec h × Vec m) →ₗ[ZMod 2] ZMod 2))
    {k : ℕ} (hk : k + 1 ≤ q) (π : Fin k → ZMod 2) (b : ZMod 2) :
    uSpan ask (k + 1) hk (snocVec π b) =
      uSpan ask k (by omega) π ⊔
        Submodule.span (ZMod 2)
          {(ask ⟨k, by omega⟩ π).comp (LinearMap.inl (ZMod 2) (Vec h) (Vec m))} := by
  unfold uSpan
  rw [← Submodule.span_union]
  congr 1
  ext f
  simp only [Set.mem_range, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    by_cases hi : i.val < k
    · left
      exact ⟨⟨i.val, hi⟩, (uPart_snoc_lt ask hk π b i hi).symm⟩
    · right
      have hval : i.val = k := by have := i.isLt; omega
      have hieq : i = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext hval
      rw [hieq, uPart_snoc_last]
  · rintro (⟨i, rfl⟩ | rfl)
    · exact ⟨⟨i.val, Nat.lt_succ_of_lt i.isLt⟩, uPart_snoc_lt ask hk π b ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ i.isLt⟩
    · exact ⟨⟨k, Nat.lt_succ_self k⟩, uPart_snoc_last ask hk π b⟩

lemma finrank_dual_vec (h : ℕ) :
    Module.finrank (ZMod 2) (Vec h →ₗ[ZMod 2] ZMod 2) = h := by
  rw [Module.finrank_linearMap, Module.finrank_fin_fun, Module.finrank_self, mul_one]

lemma exists_forcing_list {m h q : ℕ}
    (ask : (j : Fin q) → (Fin j.val → ZMod 2) → ((Vec h × Vec m) →ₗ[ZMod 2] ZMod 2))
    (answers : Vec h → Vec m → Fin q → ZMod 2)
    (hans : ∀ u x (j : Fin q),
      answers u x j = ask j (fun i => answers u x ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩) (u, x)) :
    ∀ (r k : ℕ) (hkr : k + r = q) (π : Fin k → ZMod 2),
      (∃ u₀ : Vec h, prefixOf (answers u₀ 0) k (by omega) = π) →
      ∃ L : List (Vec m →ₗ[ZMod 2] ZMod 2),
        L.length ≤ capFun r (h - Module.finrank (ZMod 2) (uSpan ask k (by omega) π)) ∧
        ∀ (u : Vec h) (x : Vec m),
          prefixOf (answers u x) k (by omega) = π →
          (∀ f ∈ L, f x = 0) →
          ∃ u' : Vec h, answers u' 0 = answers u x := by
  intro r
  induction r with
  | zero =>
    intro k hkr π ⟨u₀, hu₀⟩
    refine ⟨[], by simp [capFun_zero], ?_⟩
    intro u x hpref _
    refine ⟨u₀, ?_⟩
    ext ⟨j, hj⟩
    have h1 := congr_fun hu₀ ⟨j, by omega⟩
    have h2 := congr_fun hpref ⟨j, by omega⟩
    exact h1.trans h2.symm
  | succ r ih =>
    intro k hkr π ⟨u₀, hu₀⟩
    have hk_le : k ≤ q := by omega
    have hk1_le : k + 1 ≤ q := by omega
    have hk_lt : k < q := by omega
    let W := uSpan ask k hk_le π
    let d := Module.finrank (ZMod 2) W
    let Lk := ask ⟨k, hk_lt⟩ π
    let φk : Vec h →ₗ[ZMod 2] ZMod 2 := Lk.comp (LinearMap.inl (ZMod 2) (Vec h) (Vec m))
    let ψk : Vec m →ₗ[ZMod 2] ZMod 2 := Lk.comp (LinearMap.inr (ZMod 2) (Vec h) (Vec m))
    by_cases hmem : φk ∈ W
    · have hspan : φk ∈ Submodule.span (ZMod 2) (Set.range (uPart ask k hk_le π)) := hmem
      rcases Finsupp.mem_span_range_iff_exists_finsupp.mp hspan with ⟨c, hc⟩
      have hcomb : ∑ i : Fin k, c i • uPart ask k hk_le π i = φk := by
        rw [← hc, Finsupp.sum_fintype]
        intro i; simp
      let f : Vec m →ₗ[ZMod 2] ZMod 2 := ψk - ∑ i : Fin k, c i • vPart ask k hk_le π i
      let b₀ : ZMod 2 := ∑ i : Fin k, c i * π i
      have hu0_k : answers u₀ 0 ⟨k, hk_lt⟩ = b₀ := by
        rw [hans u₀ 0 ⟨k, hk_lt⟩]
        have harg : (fun i : Fin k => answers u₀ 0 ⟨i.val, Nat.lt_trans i.isLt hk_lt⟩) = π := hu₀
        rw [harg]
        have hsplit := linearMap_prod_split Lk u₀ 0
        rw [map_zero, add_zero] at hsplit
        change Lk (u₀, 0) = b₀
        rw [hsplit]
        change φk u₀ = b₀
        rw [← hcomb, LinearMap.sum_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hi := answers_prefix_eq_uPart_add_vPart ask answers hans hk_le π u₀ 0 hu₀ i
        rw [map_zero, add_zero] at hi
        simp [hi]
      have hreach0 : ∃ u₁ : Vec h, prefixOf (answers u₁ 0) (k + 1) hk1_le = snocVec π b₀ := by
        refine ⟨u₀, ?_⟩
        rw [prefixOf_succ_eq_snoc (answers u₀ 0) hk1_le π hu₀, hu0_k]
      have hW_eq : uSpan ask (k + 1) hk1_le (snocVec π b₀) = W := by
        rw [uSpan_snoc]
        exact sup_eq_left.mpr (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hmem))
      rcases ih (k + 1) (by omega) (snocVec π b₀) hreach0 with ⟨L₁, hL₁len, hL₁prop⟩
      rw [hW_eq] at hL₁len
      refine ⟨f :: L₁, ?_, ?_⟩
      · calc
          (f :: L₁).length = 1 + L₁.length := by simp [Nat.add_comm]
          _ ≤ 1 + capFun r (h - d) := Nat.add_le_add_left hL₁len 1
          _ ≤ capFun (r + 1) (h - d) := capFun_forced r (h - d)
      · intro u x hpref hall
        have hfx : f x = 0 := hall f (List.mem_cons_self)
        have hψx : ψk x = ∑ i : Fin k, c i * vPart ask k hk_le π i x := by
          have : ψk x - (∑ i : Fin k, c i • vPart ask k hk_le π i) x = 0 := hfx
          rw [sub_eq_zero] at this
          simpa [LinearMap.sum_apply] using this
        have hux_k : answers u x ⟨k, hk_lt⟩ = b₀ := by
          rw [hans u x ⟨k, hk_lt⟩]
          have harg : (fun i : Fin k => answers u x ⟨i.val, Nat.lt_trans i.isLt hk_lt⟩) = π := hpref
          rw [harg]
          change Lk (u, x) = b₀
          rw [linearMap_prod_split Lk u x]
          change φk u + ψk x = b₀
          rw [← hcomb, hψx, LinearMap.sum_apply, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          have hi := answers_prefix_eq_uPart_add_vPart ask answers hans hk_le π u x hpref i
          simp only [LinearMap.smul_apply, smul_eq_mul]
          rw [← mul_add, hi]
        have hpref1 : prefixOf (answers u x) (k + 1) hk1_le = snocVec π b₀ := by
          rw [prefixOf_succ_eq_snoc (answers u x) hk1_le π hpref, hux_k]
        exact hL₁prop u x hpref1 (fun g hg => hall g (List.mem_cons_of_mem f hg))
    · rcases exists_ker_and_eq_one (uPart ask k hk_le π) φk hmem with ⟨δ, hδker, hδ1⟩
      have hreach_b : ∀ b : ZMod 2,
          ∃ u₁ : Vec h, prefixOf (answers u₁ 0) (k + 1) hk1_le = snocVec π b := by
        intro b
        let u₁ : Vec h := u₀ + (b - φk u₀) • δ
        have hu1_pref : prefixOf (answers u₁ 0) k hk_le = π := by
          apply prefixOf_eq_of_uPart ask answers hans hk_le π u₁
          intro i
          have hi0 := answers_prefix_eq_uPart_add_vPart ask answers hans hk_le π u₀ 0 hu₀ i
          rw [map_zero, add_zero] at hi0
          rw [map_add, map_smul, hδker i, smul_zero, add_zero, hi0]
        have hu1_k : answers u₁ 0 ⟨k, hk_lt⟩ = b := by
          rw [hans u₁ 0 ⟨k, hk_lt⟩]
          have harg : (fun i : Fin k => answers u₁ 0 ⟨i.val, Nat.lt_trans i.isLt hk_lt⟩) = π := hu1_pref
          rw [harg]
          have hsplit := linearMap_prod_split Lk u₁ 0
          rw [map_zero, add_zero] at hsplit
          change Lk (u₁, 0) = b
          rw [hsplit]
          change φk (u₀ + (b - φk u₀) • δ) = b
          rw [map_add, map_smul, hδ1, smul_eq_mul, mul_one]
          ring
        refine ⟨u₁, ?_⟩
        rw [prefixOf_succ_eq_snoc (answers u₁ 0) hk1_le π hu1_pref, hu1_k]
      have hW_lt : ∀ b : ZMod 2, W < uSpan ask (k + 1) hk1_le (snocVec π b) := by
        intro b
        rw [uSpan_snoc]
        refine lt_of_le_of_ne le_sup_left ?_
        intro heq
        apply hmem
        rw [heq]
        exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton φk))
      have hd_lt : ∀ b : ZMod 2,
          d < Module.finrank (ZMod 2) (uSpan ask (k + 1) hk1_le (snocVec π b)) :=
        fun b => Submodule.finrank_lt_finrank_of_lt (hW_lt b)
      have hd'_le : ∀ b : ZMod 2,
          Module.finrank (ZMod 2) (uSpan ask (k + 1) hk1_le (snocVec π b)) ≤ h := by
        intro b
        have := Submodule.finrank_le (uSpan ask (k + 1) hk1_le (snocVec π b))
        rwa [finrank_dual_vec] at this
      have h1_le : 1 ≤ h - d := by
        have hlt := hd_lt 0
        have hle := hd'_le 0
        omega
      rcases ih (k + 1) (by omega) (snocVec π 0) (hreach_b 0) with ⟨L₀, hL₀len, hL₀prop⟩
      rcases ih (k + 1) (by omega) (snocVec π 1) (hreach_b 1) with ⟨L₁, hL₁len, hL₁prop⟩
      have hL₀' : L₀.length ≤ capFun r (h - d - 1) := by
        have hs : h - Module.finrank (ZMod 2) (uSpan ask (k + 1) hk1_le (snocVec π 0)) ≤ h - d - 1 := by
          have := hd_lt 0
          omega
        exact le_trans hL₀len (capFun_mono_s hs)
      have hL₁' : L₁.length ≤ capFun r (h - d - 1) := by
        have hs : h - Module.finrank (ZMod 2) (uSpan ask (k + 1) hk1_le (snocVec π 1)) ≤ h - d - 1 := by
          have := hd_lt 1
          omega
        exact le_trans hL₁len (capFun_mono_s hs)
      refine ⟨L₀ ++ L₁, ?_, ?_⟩
      · calc
          (L₀ ++ L₁).length = L₀.length + L₁.length := List.length_append
          _ ≤ capFun r (h - d - 1) + capFun r (h - d - 1) := Nat.add_le_add hL₀' hL₁'
          _ = 2 * capFun r (h - d - 1) := by ring
          _ ≤ capFun (r + 1) (h - d) := capFun_split h1_le
      · intro u x hpref hall
        have hall0 : ∀ g ∈ L₀, g x = 0 := fun g hg => hall g (List.mem_append_left L₁ hg)
        have hall1 : ∀ g ∈ L₁, g x = 0 := fun g hg => hall g (List.mem_append_right L₀ hg)
        rcases zmod2_eq_zero_or_one (answers u x ⟨k, hk_lt⟩) with hb | hb
        · have hpref1 : prefixOf (answers u x) (k + 1) hk1_le = snocVec π 0 := by
            rw [prefixOf_succ_eq_snoc (answers u x) hk1_le π hpref, hb]
          exact hL₀prop u x hpref1 hall0
        · have hpref1 : prefixOf (answers u x) (k + 1) hk1_le = snocVec π 1 := by
            rw [prefixOf_succ_eq_snoc (answers u x) hk1_le π hpref, hb]
          exact hL₁prop u x hpref1 hall1

lemma part1 {m h q : ℕ}
    (label : Vec h → Vec m → Bool)
    (hfeas : ∃ (ask : (j : Fin q) → (Fin j.val → ZMod 2) → ((Vec h × Vec m) →ₗ[ZMod 2] ZMod 2))
      (answers : Vec h → Vec m → Fin q → ZMod 2) (leaf : (Fin q → ZMod 2) → Bool),
      (∀ (u : Vec h) (x : Vec m) (j : Fin q), answers u x j =
        ask j (fun i => answers u x ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩) (u, x)) ∧
      ∀ (u : Vec h) (x : Vec m), label u x = leaf (answers u x))
    (hzero : ∀ u, label u 0 = false) :
    ∃ A : Vec m →ₗ[ZMod 2] (Fin (2 ^ min h (q - 1) * (q - min h (q - 1))) → ZMod 2),
      ∀ (u : Vec h) (x : Vec m), label u x = true → A x ≠ 0 := by
  rcases hfeas with ⟨ask, answers, leaf, hans, hlabel⟩
  have hreach0 : ∃ u₀ : Vec h, prefixOf (answers u₀ 0) 0 (Nat.zero_le q) = Fin.elim0 := by
    refine ⟨0, ?_⟩
    ext i
    exact Fin.elim0 i
  rcases exists_forcing_list ask answers hans q 0 (Nat.zero_add q) Fin.elim0 hreach0 with
    ⟨L, hLlen, hLprop⟩
  have hspan0 : uSpan ask 0 (Nat.zero_le q) Fin.elim0 = ⊥ := by
    unfold uSpan
    have : Set.range (uPart ask 0 (Nat.zero_le q) Fin.elim0) = ∅ := by
      ext f; simp
    rw [this, Submodule.span_empty]
  rw [hspan0, finrank_bot, Nat.sub_zero] at hLlen
  let cap := 2 ^ min h (q - 1) * (q - min h (q - 1))
  have hLcap : L.length ≤ cap := hLlen
  let A : Vec m →ₗ[ZMod 2] (Fin cap → ZMod 2) :=
    { toFun := fun x i => if hi : i.val < L.length then (L.get ⟨i.val, hi⟩) x else 0
      map_add' := fun x₁ x₂ => by
        ext i
        by_cases hi : i.val < L.length
        · simp [hi]
        · simp [hi]
      map_smul' := fun c x => by
        ext i
        by_cases hi : i.val < L.length
        · simp [hi]
        · simp [hi] }
  refine ⟨A, ?_⟩
  intro u x htrue hAx0
  have hall : ∀ f ∈ L, f x = 0 := by
    intro f hf
    rcases List.mem_iff_get.mp hf with ⟨idx, rfl⟩
    have hlt : idx.val < cap := Nat.lt_of_lt_of_le idx.isLt hLcap
    have := congr_fun hAx0 ⟨idx.val, hlt⟩
    simpa [A, idx.isLt] using this
  have hpref0 : prefixOf (answers u x) 0 (Nat.zero_le q) = Fin.elim0 := by
    ext i; exact Fin.elim0 i
  rcases hLprop u x hpref0 hall with ⟨u', hu'⟩
  have hfalse : label u x = false := by
    rw [hlabel u x, ← hu', ← hlabel u' 0, hzero u']
  rw [htrue] at hfalse
  exact Bool.noConfusion hfalse

lemma part2 {m h q : ℕ}
    (A : Vec m →ₗ[ZMod 2] (Fin (2 ^ min h (q - 1) * (q - min h (q - 1))) → ZMod 2)) :
    ∃ label : Vec h → Vec m → Bool,
      (∃ (ask : (j : Fin q) → (Fin j.val → ZMod 2) → ((Vec h × Vec m) →ₗ[ZMod 2] ZMod 2))
        (answers : Vec h → Vec m → Fin q → ZMod 2) (leaf : (Fin q → ZMod 2) → Bool),
        (∀ (u : Vec h) (x : Vec m) (j : Fin q), answers u x j =
          ask j (fun i => answers u x ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩) (u, x)) ∧
        ∀ (u : Vec h) (x : Vec m), label u x = leaf (answers u x)) ∧
      ∀ x : Vec m, (∃ u : Vec h, label u x = true) ↔ A x ≠ 0 := by
  by_cases hq : q = 0
  · subst hq
    refine ⟨fun _ _ => false, ⟨fun j => Fin.elim0 j, fun _ _ => Fin.elim0, fun _ => false, ?_, ?_⟩, ?_⟩
    · intro u x j; exact Fin.elim0 j
    · intro u x; rfl
    · intro x
      constructor
      · rintro ⟨_, h⟩; exact Bool.noConfusion h
      · intro hne
        exfalso
        apply hne
        ext i
        exact absurd i.isLt (by simp)
  · let t := min h (q - 1)
    let cap := 2 ^ t * (q - t)
    have ht_le_h : t ≤ h := min_le_left _ _
    have ht_lt_q : t < q := by
      have : t ≤ q - 1 := min_le_right _ _
      omega
    have hcard : Fintype.card (Fin t → ZMod 2) = 2 ^ t := by
      simp
    let e₁ : (Fin t → ZMod 2) ≃ Fin (2 ^ t) :=
      (Fintype.equivFin (Fin t → ZMod 2)).trans (finCongr hcard)
    let e : (Fin t → ZMod 2) × Fin (q - t) ≃ Fin cap :=
      (Equiv.prodCongrLeft (fun _ => e₁)).trans finProdFinEquiv
    let ask : (j : Fin q) → (Fin j.val → ZMod 2) → ((Vec h × Vec m) →ₗ[ZMod 2] ZMod 2) :=
      fun j prev =>
        if hj : j.val < t then
          (LinearMap.proj ⟨j.val, Nat.lt_of_lt_of_le hj ht_le_h⟩).comp
            (LinearMap.fst (ZMod 2) (Vec h) (Vec m))
        else
          let addr : Fin t → ZMod 2 := fun i => prev ⟨i.val, by omega⟩
          let k : Fin (q - t) := ⟨j.val - t, by omega⟩
          (LinearMap.proj (e (addr, k))).comp
            (A.comp (LinearMap.snd (ZMod 2) (Vec h) (Vec m)))
    let answers : Vec h → Vec m → Fin q → ZMod 2 :=
      fun u x j =>
        if hj : j.val < t then
          u ⟨j.val, Nat.lt_of_lt_of_le hj ht_le_h⟩
        else
          let addr : Fin t → ZMod 2 := fun i => u ⟨i.val, Nat.lt_of_lt_of_le i.isLt ht_le_h⟩
          let k : Fin (q - t) := ⟨j.val - t, by omega⟩
          A x (e (addr, k))
    let leaf : (Fin q → ZMod 2) → Bool :=
      fun ans => decide (∃ k : Fin (q - t), ans ⟨t + k.val, by omega⟩ ≠ 0)
    let label : Vec h → Vec m → Bool := fun u x => leaf (answers u x)
    refine ⟨label, ⟨ask, answers, leaf, ?_, fun _ _ => rfl⟩, ?_⟩
    · intro u x j
      by_cases hj : j.val < t
      · simp [ask, answers, hj]
      · simp only [ask, answers, hj, ↓reduceDIte, LinearMap.comp_apply, LinearMap.snd_apply,
          LinearMap.proj_apply]
        refine congrArg (A x) (congrArg e (Prod.ext ?_ rfl))
        ext i
        simp [i.isLt]
    · intro x
      constructor
      · rintro ⟨u, hu⟩
        have hex : ∃ k : Fin (q - t), answers u x ⟨t + k.val, by omega⟩ ≠ 0 :=
          of_decide_eq_true hu
        rcases hex with ⟨k, hk⟩
        have hnotlt : ¬ (t + k.val < t) := by omega
        simp only [answers, hnotlt, ↓reduceDIte] at hk
        intro hAx0
        rw [hAx0] at hk
        exact hk rfl
      · intro hAx
        have hex : ∃ idx : Fin cap, A x idx ≠ 0 := by
          by_contra hall
          push Not at hall
          apply hAx
          ext idx
          exact hall idx
        rcases hex with ⟨idx, hidx⟩
        let a : Fin t → ZMod 2 := (e.symm idx).1
        let k : Fin (q - t) := (e.symm idx).2
        let u : Vec h := fun i => if hi : i.val < t then a ⟨i.val, hi⟩ else 0
        refine ⟨u, ?_⟩
        change decide (∃ k' : Fin (q - t), answers u x ⟨t + k'.val, by omega⟩ ≠ 0) = true
        rw [decide_eq_true_eq]
        refine ⟨k, ?_⟩
        have hnotlt : ¬ (t + k.val < t) := by omega
        simp only [answers, hnotlt, ↓reduceDIte]
        have haddr : (fun i : Fin t => u ⟨i.val, Nat.lt_of_lt_of_le i.isLt ht_le_h⟩) = a := by
          ext i
          simp [u, i.isLt]
        have hk' : (⟨t + k.val - t, by omega⟩ : Fin (q - t)) = k := Fin.ext (by simp)
        rw [haddr, hk']
        have heq : e (a, k) = idx := e.apply_symm_apply idx
        rwa [heq]

theorem lib660 : (∀ (m h q : Nat),
  let U := Fin h → ZMod 2
  let V := Fin m → ZMod 2
  let moves := min h (q-1)
  let cap := 2^moves * (q-moves)
  let feasible := fun (label : U → V → Bool) =>
    ∃ (ask : (j : Fin q) → (Fin j.val → ZMod 2) → ((U × V) →ₗ[ZMod 2] ZMod 2))
      (answers : U → V → Fin q → ZMod 2) (leaf : (Fin q → ZMod 2) → Bool),
      (∀ (u : U) (x : V) (j : Fin q), answers u x j =
        ask j (fun i => answers u x ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩) (u,x)) ∧
      ∀ (u : U) (x : V), label u x = leaf (answers u x)
  (∀ label : U → V → Bool, feasible label → (∀ u, label u 0 = false) →
    ∃ A : V →ₗ[ZMod 2] (Fin cap → ZMod 2),
      ∀ (u : U) (x : V), label u x = true → A x ≠ 0) ∧
  (∀ A : V →ₗ[ZMod 2] (Fin cap → ZMod 2),
    ∃ label : U → V → Bool, feasible label ∧
      ∀ x : V, (∃ u : U, label u x = true) ↔ A x ≠ 0)) := by
  intro m h q
  exact ⟨part1, part2⟩

lemma fwdA_prod_le_card_sub {m : ℕ} (K : Submodule (ZMod 2) (Vec m)) (d : ℕ) :
    ∏ i ∈ Finset.range d, (2 ^ Module.finrank (ZMod 2) K - 2 ^ i) ≤
      Nat.card {g : Fin d → K // LinearIndependent (ZMod 2) g} := by
  by_cases hdk : d ≤ Module.finrank (ZMod 2) K
  · rw [card_linearIndependent hdk, ZMod.card,
      Fin.prod_univ_eq_prod_range (fun i => 2 ^ Module.finrank (ZMod 2) K - 2 ^ i)]
  · have h0 : ∏ i ∈ Finset.range d, (2 ^ Module.finrank (ZMod 2) K - 2 ^ i) = 0 := by
      apply Finset.prod_eq_zero (i := Module.finrank (ZMod 2) K)
      · simp only [Finset.mem_range]; omega
      · simp
    rw [h0]; exact Nat.zero_le _

lemma fwdA_finrank_ker {m cap : ℕ} (A : Vec m →ₗ[ZMod 2] (Fin cap → ZMod 2)) :
    m - cap ≤ Module.finrank (ZMod 2) (LinearMap.ker A) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker A
  have h2 : Module.finrank (ZMod 2) (LinearMap.range A) ≤ cap := by
    have := Submodule.finrank_le (LinearMap.range A)
    simpa using this
  rw [Module.finrank_fin_fun] at h1
  omega

lemma fwdA_blind_le_prod {m cap d k : ℕ} (hk : m - cap ≤ k) :
    ∏ i ∈ Finset.range d, (2 ^ (m - cap) - 2 ^ i) ≤ ∏ i ∈ Finset.range d, (2 ^ k - 2 ^ i) := by
  apply Finset.prod_le_prod
  intro i _
  apply Nat.sub_le_sub_right
  exact Nat.pow_le_pow_right (by norm_num) hk

open Classical in
lemma fwdA_blind_le_missed {m h cap d : ℕ} (lab : Vec h → Vec m → Bool)
    (A : Vec m →ₗ[ZMod 2] (Fin cap → ZMod 2)) (hA : ∀ u x, lab u x = true → A x ≠ 0) :
    ∏ i ∈ Finset.range d, (2 ^ (m - cap) - 2 ^ i) ≤
      (((Finset.univ : Finset (Fin d → Vec m)).filter (fun f => LinearIndependent (ZMod 2) f)).filter
        (fun f => ((Finset.univ : Finset (Fin d × Vec h)).filter
          (fun iu => lab iu.2 (f iu.1) = true)).card = 0)).card := by
  set K := LinearMap.ker A with hK
  refine le_trans (fwdA_blind_le_prod (fwdA_finrank_ker A)) ?_
  refine le_trans (fwdA_prod_le_card_sub K d) ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  apply Finset.card_le_card_of_injOn (fun (g : Fin d → K) (i : Fin d) => (g i : Vec m))
  · intro g hg
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hg
    simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    refine ⟨?_, ?_⟩
    · exact hg.map' K.subtype (Submodule.ker_subtype K)
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro iu _ htrue
      have hmem : ((g iu.1 : K) : Vec m) ∈ K := (g iu.1).2
      exact hA iu.2 _ htrue (LinearMap.mem_ker.mp hmem)
  · intro g₁ _ g₂ _ heq
    funext i
    exact Subtype.ext (congrFun heq i)

lemma fwdA_card_frames {m d : ℕ} (hdm : d ≤ m) :
    Nat.card {f : Fin d → Vec m // LinearIndependent (ZMod 2) f} =
      ∏ i ∈ Finset.range d, (2 ^ m - 2 ^ i) := by
  have hd : d ≤ Module.finrank (ZMod 2) (Vec m) := by
    rw [Module.finrank_fin_fun]; exact hdm
  rw [card_linearIndependent hd, ZMod.card, Module.finrank_fin_fun,
    Fin.prod_univ_eq_prod_range (fun i => 2 ^ m - 2 ^ i)]

lemma fwdA_good_iff {h m H : ℕ} (lab : Fin H → Vec h → Vec m → Bool) (seed : Fin H)
    (hs : ¬ 0 < ((Finset.univ : Finset (Vec h)).filter (fun copyBit => lab seed copyBit 0 = true)).card) :
    ∀ u, lab seed u 0 = false := by
  intro u
  have h0 : ((Finset.univ : Finset (Vec h)).filter (fun copyBit => lab seed copyBit 0 = true)).card = 0 := by
    omega
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
  have := h0 (Finset.mem_univ u)
  simpa using this

theorem fwd {m h cap d : ℕ} (P : (Vec h → Vec m → Bool) → Prop)
    (hker : ∀ label : Vec h → Vec m → Bool, P label → (∀ u, label u 0 = false) →
      ∃ A : Vec m →ₗ[ZMod 2] (Fin cap → ZMod 2), ∀ (u : Vec h) (x : Vec m), label u x = true → A x ≠ 0)
    (hd : 0 < d) (hdm : d ≤ m) (den fp fnBudget : ℕ) (hden : 0 < den) (hfp : fp ≤ den)
    (H : ℕ) (hH : 0 < H) (lab : Fin H → Vec h → Vec m → Bool) (hfeas : ∀ s, P (lab s))
    (hfpc : den * (Finset.univ.filter (fun seed : Fin H =>
          0 < ((Finset.univ : Finset (Vec h)).filter (fun copyBit => lab seed copyBit 0 = true)).card)).card ≤ fp * H)
    (hmiss : ∀ frame : Fin d → Vec m, LinearIndependent (ZMod 2) frame →
          den * (Finset.univ.filter (fun seed : Fin H =>
            ((Finset.univ : Finset (Fin d × Vec h)).filter
              (fun iu => lab seed iu.2 (frame iu.1) = true)).card = 0)).card ≤ fnBudget * H) :
    (den - fp) * (∏ i ∈ Finset.range d, (2 ^ (m - cap) - 2 ^ i)) ≤
      fnBudget * (∏ i ∈ Finset.range d, (2 ^ m - 2 ^ i)) := by
  classical
  set blind := ∏ i ∈ Finset.range d, (2 ^ (m - cap) - 2 ^ i) with hblind
  set total := ∏ i ∈ Finset.range d, (2 ^ m - 2 ^ i) with htotal
  let r : (Fin d → Vec m) → Fin H → Prop := fun f seed =>
    ((Finset.univ : Finset (Fin d × Vec h)).filter (fun iu => lab seed iu.2 (f iu.1) = true)).card = 0
  let S : Finset (Fin d → Vec m) :=
    (Finset.univ : Finset (Fin d → Vec m)).filter (fun f => LinearIndependent (ZMod 2) f)
  have hS : S.card = total := by
    rw [htotal, ← fwdA_card_frames hdm, Nat.card_eq_fintype_card, Fintype.card_subtype]
  let bad : Finset (Fin H) := Finset.univ.filter (fun seed : Fin H =>
    0 < ((Finset.univ : Finset (Vec h)).filter (fun copyBit => lab seed copyBit 0 = true)).card)
  let G : Finset (Fin H) := Finset.univ.filter (fun seed : Fin H =>
    ¬ 0 < ((Finset.univ : Finset (Vec h)).filter (fun copyBit => lab seed copyBit 0 = true)).card)
  have hGbad : bad.card + G.card = H := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin H)))
      (fun seed : Fin H =>
        0 < ((Finset.univ : Finset (Vec h)).filter (fun copyBit => lab seed copyBit 0 = true)).card)
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact this
  have h1 : (den - fp) * H ≤ den * G.card := by
    have e1 : (den - fp) * H + fp * H = den * H := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hfp]
    have e2 : den * G.card + den * bad.card = den * H := by
      rw [← Nat.mul_add, Nat.add_comm, hGbad]
    have hb : den * bad.card ≤ fp * H := hfpc
    omega
  have h2 : ∀ seed ∈ G, blind ≤ (S.bipartiteBelow r seed).card := by
    intro seed hseed
    have hg : ∀ u, lab seed u 0 = false :=
      fwdA_good_iff lab seed (Finset.mem_filter.mp hseed).2
    obtain ⟨A, hA⟩ := hker (lab seed) (hfeas seed) hg
    have := fwdA_blind_le_missed (d := d) (lab seed) A hA
    exact this
  have h3 : ∀ f ∈ S, den * (Finset.univ.bipartiteAbove r f).card ≤ fnBudget * H := by
    intro f hf
    exact hmiss f (Finset.mem_filter.mp hf).2
  have hdc : ∑ f ∈ S, (Finset.univ.bipartiteAbove r f).card =
      ∑ seed, (S.bipartiteBelow r seed).card :=
    Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow r
  have h4 : G.card * blind ≤ ∑ seed, (S.bipartiteBelow r seed).card := by
    calc G.card * blind = ∑ _seed ∈ G, blind := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ seed ∈ G, (S.bipartiteBelow r seed).card := Finset.sum_le_sum h2
      _ ≤ ∑ seed, (S.bipartiteBelow r seed).card :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ G)
  have h5 : den * ∑ f ∈ S, (Finset.univ.bipartiteAbove r f).card ≤ total * (fnBudget * H) := by
    rw [Finset.mul_sum, ← hS, ← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum h3
  have key : (den - fp) * blind * H ≤ fnBudget * total * H := by
    calc (den - fp) * blind * H = (den - fp) * H * blind := by ring
      _ ≤ den * G.card * blind := Nat.mul_le_mul_right _ h1
      _ = den * (G.card * blind) := by ring
      _ ≤ den * ∑ seed, (S.bipartiteBelow r seed).card := Nat.mul_le_mul_left _ h4
      _ = den * ∑ f ∈ S, (Finset.univ.bipartiteAbove r f).card := by rw [hdc]
      _ ≤ total * (fnBudget * H) := h5
      _ = fnBudget * total * H := by ring
  exact Nat.le_of_mul_le_mul_right key hH

lemma bwdA_pow_mul_sub {n b i : ℕ} (hb : b ≤ n) :
    2 ^ b * (2 ^ (n - b) - 2 ^ i) = 2 ^ n - 2 ^ (b + i) := by
  rw [Nat.mul_sub, ← pow_add, ← pow_add, Nat.add_sub_cancel' hb]

lemma bwdA_prod_shift (n a b : ℕ) (hb : b ≤ n) :
    2 ^ (a * b) * (∏ i ∈ Finset.range a, (2 ^ (n - b) - 2 ^ i)) *
        ∏ i ∈ Finset.range b, (2 ^ n - 2 ^ i) =
      ∏ i ∈ Finset.range (b + a), (2 ^ n - 2 ^ i) := by
  have h1 : (2 : ℕ) ^ (a * b) = ∏ _i ∈ Finset.range a, 2 ^ b := by
    rw [Finset.prod_const, Finset.card_range, ← pow_mul, mul_comm]
  rw [Finset.prod_range_add, h1, ← Finset.prod_mul_distrib, mul_comm]
  congr 1
  exact Finset.prod_congr rfl (fun i _ => bwdA_pow_mul_sub hb)

lemma bwdA_identity {m c d : ℕ} (hc : c ≤ m) (hd : d ≤ m) :
    (∏ i ∈ Finset.range c, (2 ^ (m - d) - 2 ^ i)) * (∏ i ∈ Finset.range d, (2 ^ m - 2 ^ i)) =
      (∏ i ∈ Finset.range c, (2 ^ m - 2 ^ i)) * ∏ i ∈ Finset.range d, (2 ^ (m - c) - 2 ^ i) := by
  have h1 := bwdA_prod_shift m c d hd
  have h2 := bwdA_prod_shift m d c hc
  rw [add_comm c d, ← h1, mul_comm d c, mul_assoc, mul_assoc] at h2
  have hpos : 0 < 2 ^ (c * d) := by positivity
  have h3 := Nat.eq_of_mul_eq_mul_left hpos h2
  rw [mul_comm] at h3
  exact h3.symm

lemma bwdA_finite_dual (m : ℕ) : Finite (Module.Dual (ZMod 2) (Vec m)) :=
  Module.finite_of_finite (ZMod 2)

lemma bwdA_card_keys {m c : ℕ} (hc : c ≤ m) :
    Nat.card {φ : Fin c → Module.Dual (ZMod 2) (Vec m) // LinearIndependent (ZMod 2) φ} =
      ∏ i ∈ Finset.range c, (2 ^ m - 2 ^ i) := by
  have := bwdA_finite_dual m
  have hr : Module.finrank (ZMod 2) (Module.Dual (ZMod 2) (Vec m)) = m := finrank_dual_vec m
  rw [card_linearIndependent (by rw [hr]; exact hc), hr, ZMod.card,
    Fin.prod_univ_eq_prod_range (fun i => 2 ^ m - 2 ^ i) c]

lemma bwdA_card_vanish {m c d : ℕ} (f : Fin d → Vec m) (hf : LinearIndependent (ZMod 2) f) :
    Nat.card {φ : {φ : Fin c → Module.Dual (ZMod 2) (Vec m) // LinearIndependent (ZMod 2) φ} //
       ∀ k i, φ.1 k (f i) = 0} ≤ ∏ i ∈ Finset.range c, (2 ^ (m - d) - 2 ^ i) := by
  have := bwdA_finite_dual m
  set W := (Submodule.span (ZMod 2) (Set.range f)).dualAnnihilator with hW
  have hrW : Module.finrank (ZMod 2) W = m - d := by
    have := Subspace.finrank_add_finrank_dualAnnihilator_eq (Submodule.span (ZMod 2) (Set.range f))
    rw [finrank_span_eq_card hf, Fintype.card_fin, Module.finrank_fin_fun, ← hW] at this
    omega
  have hmem : ∀ ψ : Module.Dual (ZMod 2) (Vec m), (∀ i, ψ (f i) = 0) → ψ ∈ W := by
    intro ψ hψ
    rw [hW, Submodule.mem_dualAnnihilator]
    intro w hw
    have hle : Submodule.span (ZMod 2) (Set.range f) ≤ LinearMap.ker ψ :=
      Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hψ i)
    exact hle hw
  let g : {φ : {φ : Fin c → Module.Dual (ZMod 2) (Vec m) // LinearIndependent (ZMod 2) φ} //
       ∀ k i, φ.1 k (f i) = 0} → {ψ : Fin c → W // LinearIndependent (ZMod 2) ψ} :=
    fun φ => ⟨fun k => ⟨φ.1.1 k, hmem _ (fun i => φ.2 k i)⟩,
      LinearIndependent.of_comp W.subtype φ.1.2⟩
  have hg : Function.Injective g := by
    intro φ φ' hφ
    have h1 : φ.1.1 = φ'.1.1 := by
      funext k
      have := congrArg (fun ψ : {ψ : Fin c → W // LinearIndependent (ZMod 2) ψ} => (ψ.1 k : Module.Dual (ZMod 2) (Vec m))) hφ
      simpa [g] using this
    exact Subtype.ext (Subtype.ext h1)
  have hle := Nat.card_le_card_of_injective g hg
  by_cases hcd : c ≤ m - d
  · have hcard := card_linearIndependent (K := ZMod 2) (V := W) (k := c) (by rw [hrW]; exact hcd)
    rw [hrW, ZMod.card, Fin.prod_univ_eq_prod_range (fun i => 2 ^ (m - d) - 2 ^ i) c] at hcard
    rw [hcard] at hle
    exact hle
  · have hemp : IsEmpty {ψ : Fin c → W // LinearIndependent (ZMod 2) ψ} := by
      refine ⟨fun ψ => hcd ?_⟩
      have := ψ.2.fintype_card_le_finrank
      rw [Fintype.card_fin, hrW] at this
      exact this
    have h0 : Nat.card {ψ : Fin c → W // LinearIndependent (ZMod 2) ψ} = 0 := Nat.card_of_isEmpty
    omega

theorem bwd {m h cap d : ℕ} (P : (Vec h → Vec m → Bool) → Prop)
    (hreal : ∀ A : Vec m →ₗ[ZMod 2] (Fin cap → ZMod 2),
      ∃ label : Vec h → Vec m → Bool, P label ∧ ∀ x : Vec m, (∃ u : Vec h, label u x = true) ↔ A x ≠ 0)
    (hconst : P (fun _ _ => true))
    (hd : 0 < d) (hdm : d ≤ m) (den fp fnBudget : ℕ) (hden : 0 < den) (hfp : fp ≤ den)
    (hR : (den - fp) * (∏ i ∈ Finset.range d, (2 ^ (m - cap) - 2 ^ i)) ≤
      fnBudget * (∏ i ∈ Finset.range d, (2 ^ m - 2 ^ i))) :
    ∃ H : Nat, 0 < H ∧ ∃ lab : Fin H → Vec h → Vec m → Bool,
        (∀ seed : Fin H, P (lab seed)) ∧
        den * (Finset.univ.filter (fun seed : Fin H =>
          0 < ((Finset.univ : Finset (Vec h)).filter (fun copyBit => lab seed copyBit 0 = true)).card)).card ≤ fp * H ∧
        ∀ frame : Fin d → Vec m, LinearIndependent (ZMod 2) frame →
          den * (Finset.univ.filter (fun seed : Fin H =>
            ((Finset.univ : Finset (Fin d × Vec h)).filter
              (fun iu => lab seed iu.2 (frame iu.1) = true)).card = 0)).card ≤ fnBudget * H := by
  classical
  obtain ⟨c, hcm, hccap, hmc⟩ : ∃ c, c ≤ m ∧ c ≤ cap ∧ m - cap = m - c :=
    ⟨min m cap, min_le_left _ _, min_le_right _ _, by omega⟩
  rw [hmc] at hR
  have := bwdA_finite_dual m
  let Keys := {φ : Fin c → Module.Dual (ZMod 2) (Vec m) // LinearIndependent (ZMod 2) φ}
  let _ : Fintype Keys := Fintype.ofFinite Keys
  have hNF : Nat.card Keys = ∏ i ∈ Finset.range c, (2 ^ m - 2 ^ i) := bwdA_card_keys hcm
  have hNFpos : 0 < Nat.card Keys := by
    rw [hNF]
    exact Finset.prod_pos (fun i hi =>
      Nat.sub_pos_of_lt (Nat.pow_lt_pow_right (by norm_num) (by simp at hi; omega)))
  have htotpos : 0 < ∏ i ∈ Finset.range d, (2 ^ m - 2 ^ i) :=
    Finset.prod_pos (fun i hi =>
      Nat.sub_pos_of_lt (Nat.pow_lt_pow_right (by norm_num) (by simp at hi; omega)))
  let Amap : Keys → (Vec m →ₗ[ZMod 2] (Fin cap → ZMod 2)) := fun φ =>
    LinearMap.pi (fun j : Fin cap => if hj : j.val < c then φ.1 ⟨j.val, hj⟩ else 0)
  have hA : ∀ (φ : Keys) (x : Vec m), Amap φ x = 0 ↔ ∀ k, φ.1 k x = 0 := by
    intro φ x
    constructor
    · intro hx k
      have := congrFun hx ⟨k.val, by omega⟩
      simpa [Amap, k.isLt] using this
    · intro hx
      funext j
      by_cases hj : j.val < c
      · simp [Amap, hj, hx]
      · simp [Amap, hj]
  choose L hLP hLiff using fun φ : Keys => hreal (Amap φ)
  let e : Fin (den * Nat.card Keys) ≃ Fin den × Keys :=
    finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl _) (Finite.equivFin Keys).symm)
  let lab : Fin (den * Nat.card Keys) → Vec h → Vec m → Bool := fun s =>
    if ((e s).1 : ℕ) < fp then (fun _ _ => true) else L (e s).2
  have hlab_lt : ∀ s, ((e s).1 : ℕ) < fp → lab s = fun _ _ => true := fun s hs => by simp [lab, hs]
  have hlab_ge : ∀ s, ¬ ((e s).1 : ℕ) < fp → lab s = L (e s).2 := fun s hs => by simp [lab, hs]
  refine ⟨den * Nat.card Keys, Nat.mul_pos hden hNFpos, lab, ?_, ?_, ?_⟩
  · intro s
    by_cases hs : ((e s).1 : ℕ) < fp
    · rw [hlab_lt s hs]; exact hconst
    · rw [hlab_ge s hs]; exact hLP _
  · have hcard : (Finset.univ.filter (fun seed : Fin (den * Nat.card Keys) =>
          0 < ((Finset.univ : Finset (Vec h)).filter
            (fun copyBit => lab seed copyBit 0 = true)).card)).card ≤ fp * Nat.card Keys := by
      calc _ ≤ ((Finset.univ.filter (fun a : Fin den => (a : ℕ) < fp)) ×ˢ
              (Finset.univ : Finset Keys)).card := by
            apply Finset.card_le_card_of_injOn e
            · intro s hs
              rw [Finset.mem_coe, Finset.mem_filter] at hs
              rw [Finset.mem_coe, Finset.mem_product, Finset.mem_filter]
              refine ⟨⟨Finset.mem_univ _, ?_⟩, Finset.mem_univ _⟩
              by_contra hge
              rw [hlab_ge s hge] at hs
              obtain ⟨u, hu⟩ := Finset.card_pos.mp hs.2
              rw [Finset.mem_filter] at hu
              have h1 : Amap (e s).2 0 ≠ 0 := (hLiff (e s).2 0).mp ⟨u, hu.2⟩
              exact h1 (map_zero _)
            · exact e.injective.injOn
        _ = fp * Nat.card Keys := by
            rw [Finset.card_product, Fin.card_filter_val_lt, Finset.card_univ,
              ← Nat.card_eq_fintype_card, min_eq_right hfp]
    calc _ ≤ den * (fp * Nat.card Keys) := Nat.mul_le_mul_left _ hcard
      _ = fp * (den * Nat.card Keys) := by ring
  · intro f hf
    have hNf := bwdA_card_vanish (c := c) f hf
    have hid := bwdA_identity hcm hdm
    have hkey : (den - fp) * (∏ i ∈ Finset.range c, (2 ^ (m - d) - 2 ^ i)) ≤
        fnBudget * Nat.card Keys := by
      refine Nat.le_of_mul_le_mul_right ?_ htotpos
      calc (den - fp) * (∏ i ∈ Finset.range c, (2 ^ (m - d) - 2 ^ i)) *
              (∏ i ∈ Finset.range d, (2 ^ m - 2 ^ i))
            = Nat.card Keys * ((den - fp) * ∏ i ∈ Finset.range d, (2 ^ (m - c) - 2 ^ i)) := by
              rw [mul_assoc (den - fp), hid, hNF]; ring
          _ ≤ Nat.card Keys * (fnBudget * ∏ i ∈ Finset.range d, (2 ^ m - 2 ^ i)) :=
              Nat.mul_le_mul_left _ hR
          _ = fnBudget * Nat.card Keys * ∏ i ∈ Finset.range d, (2 ^ m - 2 ^ i) := by ring
    have hcard : (Finset.univ.filter (fun seed : Fin (den * Nat.card Keys) =>
            ((Finset.univ : Finset (Fin d × Vec h)).filter
              (fun iu => lab seed iu.2 (f iu.1) = true)).card = 0)).card ≤
          (den - fp) * Nat.card {φ : Keys // ∀ k i, φ.1 k (f i) = 0} := by
      calc _ ≤ ((Finset.univ.filter (fun a : Fin den => ¬ (a : ℕ) < fp)) ×ˢ
              (Finset.univ.filter (fun φ : Keys => ∀ k i, φ.1 k (f i) = 0))).card := by
            apply Finset.card_le_card_of_injOn e
            · intro s hs
              rw [Finset.mem_coe, Finset.mem_filter] at hs
              rw [Finset.mem_coe, Finset.mem_product, Finset.mem_filter, Finset.mem_filter]
              have hlt : ¬ ((e s).1 : ℕ) < fp := by
                intro hlt
                rw [hlab_lt s hlt] at hs
                have h2 := Finset.filter_eq_empty_iff.mp (Finset.card_eq_zero.mp hs.2)
                exact h2 (Finset.mem_univ ((⟨0, hd⟩ : Fin d), (0 : Vec h))) rfl
              refine ⟨⟨Finset.mem_univ _, hlt⟩, Finset.mem_univ _, ?_⟩
              rw [hlab_ge s hlt] at hs
              have h2 := Finset.filter_eq_empty_iff.mp (Finset.card_eq_zero.mp hs.2)
              intro k i
              have hA0 : Amap (e s).2 (f i) = 0 := by
                by_contra hne
                obtain ⟨u, hu⟩ := (hLiff (e s).2 (f i)).mpr hne
                exact h2 (Finset.mem_univ (i, u)) hu
              exact (hA (e s).2 (f i)).mp hA0 k
            · exact e.injective.injOn
        _ = (den - fp) * Nat.card {φ : Keys // ∀ k i, φ.1 k (f i) = 0} := by
            rw [Finset.card_product, Nat.card_eq_fintype_card, Fintype.card_subtype]
            congr 1
            have h1 := Finset.card_filter_add_card_filter_not
              (s := (Finset.univ : Finset (Fin den))) (fun a : Fin den => (a : ℕ) < fp)
            rw [Fin.card_filter_val_lt, Finset.card_univ, Fintype.card_fin, min_eq_right hfp] at h1
            omega
    calc _ ≤ den * ((den - fp) * Nat.card {φ : Keys // ∀ k i, φ.1 k (f i) = 0}) :=
          Nat.mul_le_mul_left _ hcard
      _ ≤ den * ((den - fp) * ∏ i ∈ Finset.range c, (2 ^ (m - d) - 2 ^ i)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hNf)
      _ ≤ den * (fnBudget * Nat.card Keys) := Nat.mul_le_mul_left _ hkey
      _ = fnBudget * (den * Nat.card Keys) := by ring

end PEqualNP.Outside.L_meta_25792

theorem PEqualNP.Outside.L_meta_25792 : (∀ (m h q : Nat),
  let U := Fin h → ZMod 2
  let V := Fin m → ZMod 2
  let moves := min h (q-1)
  let cap := 2^moves * (q-moves)
  let feasible := fun (label : U → V → Bool) =>
    ∃ (ask : (j : Fin q) → (Fin j.val → ZMod 2) → ((U × V) →ₗ[ZMod 2] ZMod 2))
      (answers : U → V → Fin q → ZMod 2) (leaf : (Fin q → ZMod 2) → Bool),
      (∀ (u : U) (x : V) (j : Fin q), answers u x j =
        ask j (fun i => answers u x ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩) (u,x)) ∧
      ∀ (u : U) (x : V), label u x = leaf (answers u x)
  ∀ d : Nat, 0 < d → d ≤ m →
    let total : Nat := ∏ i ∈ Finset.range d, (2^m - 2^i)
    let blind : Nat := ∏ i ∈ Finset.range d, (2^(m-cap) - 2^i)
    ∀ (den fp fnBudget : Nat), 0 < den → fp ≤ den → fnBudget ≤ den →
      ((∃ H : Nat, 0 < H ∧ ∃ lab : Fin H → U → V → Bool,
        (∀ seed : Fin H, feasible (lab seed)) ∧
        den * (Finset.univ.filter (fun seed : Fin H =>
          0 < ((Finset.univ : Finset U).filter (fun copyBit => lab seed copyBit 0 = true)).card)).card ≤ fp * H ∧
        ∀ frame : Fin d → V, LinearIndependent (ZMod 2) frame →
          den * (Finset.univ.filter (fun seed : Fin H =>
            ((Finset.univ : Finset (Fin d × U)).filter
              (fun iu => lab seed iu.2 (frame iu.1) = true)).card = 0)).card ≤ fnBudget * H) ↔
      (den-fp) * blind ≤ fnBudget * total)) := by
  intro m h q U V moves cap feasible d hd hdm total blind den fp fnBudget hden hfp hfn
  obtain ⟨L1, L2⟩ := PEqualNP.Outside.L_meta_25792.lib660 m h q
  have hconst : feasible (fun _ _ => true) :=
    ⟨fun _ _ => 0, fun _ _ _ => 0, fun _ => true, fun _ _ _ => rfl, fun _ _ => rfl⟩
  constructor
  · rintro ⟨H, hH, lab, hfeas, hfpc, hmiss⟩
    exact PEqualNP.Outside.L_meta_25792.fwd feasible L1 hd hdm den fp fnBudget hden hfp H hH lab hfeas hfpc hmiss
  · intro hR
    exact PEqualNP.Outside.L_meta_25792.bwd feasible L2 hconst hd hdm den fp fnBudget hden hfp hR
