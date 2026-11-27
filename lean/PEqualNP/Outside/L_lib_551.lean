import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_551 : (∀ (K : Type) [Field K] (q : ℕ) (f : List (Fin q) → K),
  let R := Submodule.span K (Set.range (fun u : List (Fin q) => fun v : List (Fin q) => f (u ++ v)))
  ∀ (r : ℕ) (U V : Fin r → List (Fin q)),
    Module.Finite K R → Module.finrank K R = r →
    let H := Matrix.of (fun i j : Fin r => f (U i ++ V j))
    H.det ≠ 0 →
    let B := fun a : Fin q =>
      Matrix.of (fun i j : Fin r => f (U i ++ [a] ++ V j)) * H⁻¹
    ∀ w : List (Fin q), f w =
      dotProduct (Matrix.vecMul (fun j => f (V j)) H⁻¹)
        (Matrix.mulVec ((w.map B).prod) (fun i => f (U i)))) := by
  intro K _ q f R r U V hfin hrank H hdet B w
  have hρ : ∀ u : List (Fin q), (fun v => f (u ++ v)) ∈ R := fun u => Submodule.subset_span ⟨u, rfl⟩
  have hHunit : IsUnit H.det := isUnit_iff_ne_zero.mpr hdet
  have hHH : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv H hHunit
  let b : Fin r → R := fun i => ⟨fun v => f (U i ++ v), hρ (U i)⟩
  have hli : LinearIndependent K b := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h1 : ∀ v, ∑ k, c k * f (U k ++ v) = 0 := by
      intro v
      have h0 := congrArg (fun x : R => (x : List (Fin q) → K) v) hc
      simpa [b, Finset.sum_apply] using h0
    have h2 : Matrix.vecMul c H = 0 := by
      funext j
      simpa [Matrix.vecMul, dotProduct, H] using h1 (V j)
    have h3 : c = 0 := by
      have h4 := congrArg (fun x => Matrix.vecMul x H⁻¹) h2
      simpa [Matrix.vecMul_vecMul, hHH] using h4
    simpa using congrFun h3 i
  have hspan : Submodule.span K (Set.range b) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simpa using hrank.symm)
  have L1 : ∀ g ∈ R, ∃ c : Fin r → K, ∀ v, g v = ∑ i, c i * f (U i ++ v) := by
    intro g hg
    have hm : (⟨g, hg⟩ : R) ∈ Submodule.span K (Set.range b) := by
      rw [hspan]
      trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hm
    refine ⟨c, fun v => ?_⟩
    have h0 := congrArg (fun x : R => (x : List (Fin q) → K) v) hc
    simpa [b, Finset.sum_apply] using h0.symm
  have L2 : ∀ g ∈ R, ∀ v, g v = ∑ i, (Matrix.vecMul (fun j => g (V j)) H⁻¹) i * f (U i ++ v) := by
    intro g hg v
    obtain ⟨c, hc⟩ := L1 g hg
    have hE : (fun j => g (V j)) = Matrix.vecMul c H := by
      funext j
      rw [hc (V j)]
      simp [Matrix.vecMul, dotProduct, H]
    have hcc : Matrix.vecMul (fun j => g (V j)) H⁻¹ = c := by
      rw [hE, Matrix.vecMul_vecMul, hHH, Matrix.vecMul_one]
    rw [hcc]
    exact hc v
  let cd : List (Fin q) → Fin r → K := fun u => Matrix.vecMul (fun j => f (u ++ V j)) H⁻¹
  have L3 : ∀ u a, cd (u ++ [a]) = Matrix.vecMul (cd u) (B a) := by
    intro u a
    have hE : (fun j => f (u ++ [a] ++ V j)) =
        Matrix.vecMul (cd u) (Matrix.of (fun i j : Fin r => f (U i ++ [a] ++ V j))) := by
      funext j
      have h0 := L2 _ (hρ u) ([a] ++ V j)
      simpa [cd, Matrix.vecMul, dotProduct, List.append_assoc] using h0
    show Matrix.vecMul (fun j => f (u ++ [a] ++ V j)) H⁻¹ = _
    rw [hE, Matrix.vecMul_vecMul]
  have L4 : ∀ w : List (Fin q), cd w = Matrix.vecMul (cd []) (w.map B).prod := by
    intro w
    induction w using List.reverseRecOn with
    | nil => simp
    | append_singleton w a ih =>
      rw [L3, ih, List.map_append, List.prod_append, Matrix.vecMul_vecMul]
      simp
  have hlast := L2 _ (hρ w) []
  have hfw : f w = dotProduct (cd w) (fun i => f (U i)) := by
    simpa [cd, dotProduct] using hlast
  rw [hfw, L4 w, Matrix.dotProduct_mulVec]
  simp [cd]
