import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_499

lemma zmod2_two : (2 : ZMod 2) = 0 := rfl

lemma zmod2_three : (3 : ZMod 2) = 1 := rfl

lemma zmod2_four : (4 : ZMod 2) = 0 := rfl

lemma zmod2_add_self (z : ZMod 2) : z + z = 0 := by
  fin_cases z <;> rfl

lemma zmod2_vec_add_self {n : ℕ} (x : Fin n → ZMod 2) : x + x = 0 := by
  ext i
  exact zmod2_add_self (x i)

lemma rank_eq_finrank_range_mulVecLin {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2)) :
    M.rank = Module.finrank (ZMod 2) (LinearMap.range M.mulVecLin) := by
  have hlin : Matrix.toLin (Pi.basisFun (ZMod 2) (Fin n)) (Pi.basisFun (ZMod 2) (Fin n)) M =
      M.mulVecLin := by
    apply (Pi.basisFun (ZMod 2) (Fin n)).ext
    intro i
    rw [Matrix.toLin_self]
    ext j
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, eq_comm]
  rw [Matrix.rank_eq_finrank_range_toLin M (Pi.basisFun (ZMod 2) (Fin n)) (Pi.basisFun (ZMod 2) (Fin n)), hlin]

lemma bil_self_zero {n : ℕ} (f : (Fin n → ZMod 2) → ZMod 2)
    (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (hf : ∀ x y : Fin n → ZMod 2, f (x + y) + f x + f y + f 0 = dotProduct x (M.mulVec y))
    (x : Fin n → ZMod 2) : dotProduct x (M.mulVec x) = 0 := by
  rw [← hf x x, zmod2_vec_add_self x]
  ring_nf
  simp [zmod2_two]

lemma bil_symm {n : ℕ} (f : (Fin n → ZMod 2) → ZMod 2)
    (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (hf : ∀ x y : Fin n → ZMod 2, f (x + y) + f x + f y + f 0 = dotProduct x (M.mulVec y))
    (x y : Fin n → ZMod 2) : dotProduct x (M.mulVec y) = dotProduct y (M.mulVec x) := by
  rw [← hf x y, ← hf y x, add_comm x y]
  ring

lemma bil_swap {n : ℕ} (f : (Fin n → ZMod 2) → ZMod 2)
    (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (hf : ∀ x y : Fin n → ZMod 2, f (x + y) + f x + f y + f 0 = dotProduct x (M.mulVec y))
    (u v : Fin n → ZMod 2) : dotProduct (M.mulVec u) v = dotProduct u (M.mulVec v) := by
  rw [dotProduct_comm, bil_symm f M hf v u]

def evalOnSub {n : ℕ} (S : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    (Fin n → ZMod 2) →ₗ[ZMod 2] Module.Dual (ZMod 2) ↥S where
  toFun w :=
    { toFun := fun u => dotProduct u.1 w
      map_add' := fun u₁ u₂ => by simp [add_dotProduct]
      map_smul' := fun c u => by simp [smul_dotProduct] }
  map_add' w₁ w₂ := by
    ext u
    simp [dotProduct_add]
  map_smul' c w := by
    ext u
    simp [dotProduct_smul]

lemma linearMap_dot_rep {n : ℕ} (ψ : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) :
    ∀ z : Fin n → ZMod 2, ψ z = dotProduct (fun i => ψ (Pi.single i 1)) z := by
  intro z
  conv_lhs => rw [pi_eq_sum_univ z]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hpi : (fun j => if i = j then (1 : ZMod 2) else 0) = Pi.single i 1 := by
    ext j
    simp [Pi.single_apply, eq_comm]
  rw [hpi, mul_comm]

lemma evalOnSub_range_top {n : ℕ} (S : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    LinearMap.range (evalOnSub S) = ⊤ := by
  rw [eq_top_iff]
  intro φ _
  obtain ⟨W, hSW⟩ := Submodule.exists_isCompl S
  let ψ : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 := φ.comp (S.projectionOnto W hSW)
  refine ⟨fun i => ψ (Pi.single i 1), ?_⟩
  ext u
  change dotProduct u.1 (fun i => ψ (Pi.single i 1)) = φ u
  rw [dotProduct_comm, ← linearMap_dot_rep ψ u.1]
  change φ (S.projectionOnto W hSW u.1) = φ u
  rw [Submodule.projectionOnto_apply_left hSW u]

lemma forward_dir {n : ℕ} (f : (Fin n → ZMod 2) → ZMod 2)
    (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (hf : ∀ x y : Fin n → ZMod 2, f (x + y) + f x + f y + f 0 = dotProduct x (M.mulVec y))
    (d : ℕ) (U : Submodule (ZMod 2) (Fin n → ZMod 2)) (p a : Fin n → ZMod 2) (b : ZMod 2)
    (hd : d ≤ Module.finrank (ZMod 2) U)
    (hlin : ∀ x ∈ U, f (p + x) = dotProduct a (p + x) + b) :
    2 * d + M.rank ≤ 2 * n := by
  have hiso : ∀ x ∈ U, ∀ y ∈ U, dotProduct x (M.mulVec y) = 0 := by
    intro x hx y hy
    have hxy := hlin (x + y) (U.add_mem hx hy)
    have hx0 := hlin x hx
    have hy0 := hlin y hy
    have h00 := hlin 0 U.zero_mem
    rw [add_zero] at h00
    have h1 := hf p (x + y)
    have h2 := hf p x
    have h3 := hf p y
    have h4 := hf x y
    have hlhs : f (p + (x + y)) + f (p + x) + f (p + y) + f p =
        dotProduct x (M.mulVec y) := by
      calc
        f (p + (x + y)) + f (p + x) + f (p + y) + f p
            = (f (p + (x + y)) + f p + f (x + y) + f 0) +
              (f (p + x) + f p + f x + f 0) +
              (f (p + y) + f p + f y + f 0) +
              (f (x + y) + f x + f y + f 0) := by
                ring_nf
                simp [zmod2_two, zmod2_three, zmod2_four]
        _ = dotProduct p (M.mulVec (x + y)) + dotProduct p (M.mulVec x) +
              dotProduct p (M.mulVec y) + dotProduct x (M.mulVec y) := by
                rw [h1, h2, h3, h4]
        _ = dotProduct x (M.mulVec y) := by
                rw [Matrix.mulVec_add, dotProduct_add]
                ring_nf
                simp [zmod2_two]
    have hrhs : f (p + (x + y)) + f (p + x) + f (p + y) + f p = 0 := by
      rw [hxy, hx0, hy0, h00, dotProduct_add, dotProduct_add, dotProduct_add, dotProduct_add]
      ring_nf
      simp [zmod2_two, zmod2_four]
    rw [← hlhs, hrhs]
  set L := M.mulVecLin
  set res := L.domRestrict U
  have hrank : M.rank + Module.finrank (ZMod 2) (LinearMap.ker L) = n := by
    rw [rank_eq_finrank_range_mulVecLin M, LinearMap.finrank_range_add_finrank_ker L,
      Module.finrank_fin_fun]
  have hres_rn : Module.finrank (ZMod 2) (LinearMap.range res) +
      Module.finrank (ZMod 2) (LinearMap.ker res) = Module.finrank (ZMod 2) U :=
    LinearMap.finrank_range_add_finrank_ker res
  have hker_le : Module.finrank (ZMod 2) (LinearMap.ker res) ≤
      Module.finrank (ZMod 2) (LinearMap.ker L) := by
    rw [← Submodule.finrank_map_subtype_eq U (LinearMap.ker res)]
    refine Submodule.finrank_mono ?_
    intro x hx
    rw [Submodule.mem_map] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    exact hu
  have hrng_le : Module.finrank (ZMod 2) (LinearMap.range res) ≤
      Module.finrank (ZMod 2) (LinearMap.ker (evalOnSub U)) := by
    refine Submodule.finrank_mono ?_
    intro w hw
    rw [LinearMap.mem_range] at hw
    obtain ⟨u, rfl⟩ := hw
    rw [LinearMap.mem_ker]
    ext x
    exact hiso x.1 x.2 u.1 u.2
  have heval_rn : Module.finrank (ZMod 2) (LinearMap.range (evalOnSub U)) +
      Module.finrank (ZMod 2) (LinearMap.ker (evalOnSub U)) = n := by
    rw [LinearMap.finrank_range_add_finrank_ker (evalOnSub U), Module.finrank_fin_fun]
  have heval_rng : Module.finrank (ZMod 2) (LinearMap.range (evalOnSub U)) =
      Module.finrank (ZMod 2) U := by
    rw [evalOnSub_range_top U, finrank_top, Subspace.dual_finrank_eq]
  omega

lemma extend_isotropic {n : ℕ} (f : (Fin n → ZMod 2) → ZMod 2)
    (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (hf : ∀ x y : Fin n → ZMod 2, f (x + y) + f x + f y + f 0 = dotProduct x (M.mulVec y))
    (U : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hiso : ∀ x ∈ U, ∀ y ∈ U, dotProduct x (M.mulVec y) = 0) :
    ∃ a : Fin n → ZMod 2, ∀ x ∈ U, f (0 + x) = dotProduct a (0 + x) + f 0 := by
  let φ : ↥U →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun x => f x.1 + f 0
      map_add' := fun x y => by
        have h := hf x.1 y.1
        rw [hiso x.1 x.2 y.1 y.2] at h
        calc
          f (x.1 + y.1) + f 0
              = (f (x.1 + y.1) + f x.1 + f y.1 + f 0) + (f x.1 + f 0) + (f y.1 + f 0) := by
                  ring_nf
                  simp [zmod2_two, zmod2_three]
          _ = 0 + (f x.1 + f 0) + (f y.1 + f 0) := by rw [h]
          _ = (f x.1 + f 0) + (f y.1 + f 0) := by ring
      map_smul' := fun c x => by
        rcases (by fin_cases c; exact Or.inl rfl; exact Or.inr rfl : c = 0 ∨ c = 1) with rfl | rfl
        · dsimp
          simp [zmod2_add_self]
        · dsimp
          simp }
  obtain ⟨W, hUW⟩ := Submodule.exists_isCompl U
  let ψ : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 := φ.comp (U.projectionOnto W hUW)
  refine ⟨fun i => ψ (Pi.single i 1), fun x hx => ?_⟩
  have hψx : ψ x = f x + f 0 := by
    change φ (U.projectionOnto W hUW x) = f x + f 0
    have hproj : U.projectionOnto W hUW (⟨x, hx⟩ : ↥U) = ⟨x, hx⟩ :=
      Submodule.projectionOnto_apply_left hUW ⟨x, hx⟩
    rw [hproj]
    rfl
  rw [zero_add, ← linearMap_dot_rep ψ x, hψx]
  ring_nf
  simp [zmod2_two]

lemma isotropic_step {n : ℕ} (f : (Fin n → ZMod 2) → ZMod 2)
    (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (hf : ∀ x y : Fin n → ZMod 2, f (x + y) + f x + f y + f 0 = dotProduct x (M.mulVec y))
    (d : ℕ) (h_rank : 2 * d + M.rank ≤ 2 * n)
    (U : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hK : LinearMap.ker M.mulVecLin ≤ U)
    (hiso : ∀ x ∈ U, ∀ y ∈ U, dotProduct x (M.mulVec y) = 0)
    (hlt : Module.finrank (ZMod 2) U < d) :
    ∃ U' : Submodule (ZMod 2) (Fin n → ZMod 2),
      LinearMap.ker M.mulVecLin ≤ U' ∧
      (∀ x ∈ U', ∀ y ∈ U', dotProduct x (M.mulVec y) = 0) ∧
      Module.finrank (ZMod 2) U' = Module.finrank (ZMod 2) U + 1 := by
  set L := M.mulVecLin
  set W := U.map L
  set res := L.domRestrict U
  have hres_rng : LinearMap.range res = W := by
    ext y
    simp [res, W, Submodule.mem_map]
  have hres_ker : (LinearMap.ker res).map U.subtype = LinearMap.ker L := by
    apply le_antisymm
    · intro x hx
      rw [Submodule.mem_map] at hx
      obtain ⟨u, hu, rfl⟩ := hx
      exact hu
    · intro x hx
      rw [Submodule.mem_map]
      exact ⟨⟨x, hK hx⟩, hx, rfl⟩
  have hW_fin : Module.finrank (ZMod 2) W + Module.finrank (ZMod 2) (LinearMap.ker L) =
      Module.finrank (ZMod 2) U := by
    rw [← hres_rng, ← hres_ker, Submodule.finrank_map_subtype_eq U (LinearMap.ker res)]
    exact LinearMap.finrank_range_add_finrank_ker res
  have hrank : M.rank + Module.finrank (ZMod 2) (LinearMap.ker L) = n := by
    rw [rank_eq_finrank_range_mulVecLin M, LinearMap.finrank_range_add_finrank_ker L,
      Module.finrank_fin_fun]
  set Ψ := evalOnSub W
  have hΨ_rn : Module.finrank (ZMod 2) (LinearMap.range Ψ) +
      Module.finrank (ZMod 2) (LinearMap.ker Ψ) = n := by
    rw [LinearMap.finrank_range_add_finrank_ker Ψ, Module.finrank_fin_fun]
  have hΨ_rng : Module.finrank (ZMod 2) (LinearMap.range Ψ) ≤ Module.finrank (ZMod 2) W := by
    calc
      Module.finrank (ZMod 2) (LinearMap.range Ψ) ≤
          Module.finrank (ZMod 2) (Module.Dual (ZMod 2) ↥W) :=
        Submodule.finrank_le (LinearMap.range Ψ)
      _ = Module.finrank (ZMod 2) W := Subspace.dual_finrank_eq
  have hlt_ker : Module.finrank (ZMod 2) U < Module.finrank (ZMod 2) (LinearMap.ker Ψ) := by
    omega
  have hnot_le : ¬ LinearMap.ker Ψ ≤ U := by
    intro hle
    have hmono := Submodule.finrank_mono hle
    omega
  rw [IsConcreteLE.not_le_iff_exists] at hnot_le
  obtain ⟨v, hv_ker, hv_notU⟩ := hnot_le
  refine ⟨U ⊔ Submodule.span (ZMod 2) {v}, le_trans hK le_sup_left, ?_, ?_⟩
  · intro x hx y hy
    rw [Submodule.mem_sup] at hx hy
    obtain ⟨u₁, hu₁, w₁, hw₁, rfl⟩ := hx
    obtain ⟨u₂, hu₂, w₂, hw₂, rfl⟩ := hy
    rw [Submodule.mem_span_singleton] at hw₁ hw₂
    obtain ⟨c₁, rfl⟩ := hw₁
    obtain ⟨c₂, rfl⟩ := hw₂
    have hv_ann : ∀ u ∈ U, dotProduct u (M.mulVec v) = 0 := by
      intro u hu
      have hLu : M.mulVec u ∈ W := ⟨u, hu, rfl⟩
      have h0 : (Ψ v) ⟨M.mulVec u, hLu⟩ = 0 := by
        rw [LinearMap.mem_ker] at hv_ker
        rw [hv_ker]
        rfl
      change dotProduct (M.mulVec u) v = 0 at h0
      rw [← bil_swap f M hf u v, h0]
    have hv_ann' : ∀ u ∈ U, dotProduct v (M.mulVec u) = 0 := by
      intro u hu
      rw [bil_symm f M hf v u]
      exact hv_ann u hu
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul, add_dotProduct, smul_dotProduct]
    rw [hiso u₁ hu₁ u₂ hu₂, hv_ann u₁ hu₁, hv_ann' u₂ hu₂, bil_self_zero f M hf v]
    simp
  · have hv0 : v ≠ 0 := by
      intro h0
      rw [h0] at hv_notU
      exact hv_notU U.zero_mem
    have hinf : U ⊓ Submodule.span (ZMod 2) {v} = ⊥ := by
      rw [eq_bot_iff]
      intro z ⟨hzU, hzspan⟩
      change z ∈ U at hzU
      change z ∈ Submodule.span (ZMod 2) {v} at hzspan
      rw [Submodule.mem_span_singleton] at hzspan
      obtain ⟨c, rfl⟩ := hzspan
      rcases (by fin_cases c; exact Or.inl rfl; exact Or.inr rfl : c = 0 ∨ c = 1) with rfl | rfl
      · simp
      · rw [one_smul] at hzU
        exact absurd hzU hv_notU
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq U (Submodule.span (ZMod 2) {v})
    rw [hinf, finrank_bot, add_zero, finrank_span_singleton hv0] at hsup
    exact hsup

lemma exists_isotropic_of_le {n : ℕ} (f : (Fin n → ZMod 2) → ZMod 2)
    (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (hf : ∀ x y : Fin n → ZMod 2, f (x + y) + f x + f y + f 0 = dotProduct x (M.mulVec y))
    (d : ℕ) (h_rank : 2 * d + M.rank ≤ 2 * n) :
    ∀ k : ℕ, ∀ U : Submodule (ZMod 2) (Fin n → ZMod 2),
      LinearMap.ker M.mulVecLin ≤ U →
      (∀ x ∈ U, ∀ y ∈ U, dotProduct x (M.mulVec y) = 0) →
      d ≤ Module.finrank (ZMod 2) U + k →
      ∃ U' : Submodule (ZMod 2) (Fin n → ZMod 2),
        d ≤ Module.finrank (ZMod 2) U' ∧
        ∀ x ∈ U', ∀ y ∈ U', dotProduct x (M.mulVec y) = 0 := by
  intro k
  induction k with
  | zero =>
    intro U _ hiso hle
    exact ⟨U, by omega, hiso⟩
  | succ k ih =>
    intro U hK hiso hle
    by_cases hd : d ≤ Module.finrank (ZMod 2) U
    · exact ⟨U, hd, hiso⟩
    · have hlt : Module.finrank (ZMod 2) U < d := by omega
      obtain ⟨U', hK', hiso', hfin'⟩ := isotropic_step f M hf d h_rank U hK hiso hlt
      exact ih U' hK' hiso' (by omega)

lemma backward_dir {n : ℕ} (f : (Fin n → ZMod 2) → ZMod 2)
    (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (hf : ∀ x y : Fin n → ZMod 2, f (x + y) + f x + f y + f 0 = dotProduct x (M.mulVec y))
    (d : ℕ) (h_rank : 2 * d + M.rank ≤ 2 * n) :
    ∃ (U : Submodule (ZMod 2) (Fin n → ZMod 2)) (p a : Fin n → ZMod 2) (b : ZMod 2),
      d ≤ Module.finrank (ZMod 2) U ∧
      ∀ x ∈ U, f (p + x) = dotProduct a (p + x) + b := by
  have hiso0 : ∀ x ∈ LinearMap.ker M.mulVecLin, ∀ y ∈ LinearMap.ker M.mulVecLin,
      dotProduct x (M.mulVec y) = 0 := by
    intro x _ y hy
    rw [LinearMap.mem_ker] at hy
    change M.mulVec y = 0 at hy
    rw [hy, dotProduct_zero]
  obtain ⟨U, hdU, hisoU⟩ := exists_isotropic_of_le f M hf d h_rank d (LinearMap.ker M.mulVecLin)
    le_rfl hiso0 (by omega)
  obtain ⟨a, ha⟩ := extend_isotropic f M hf U hisoU
  exact ⟨U, 0, a, f 0, hdU, ha⟩

end PEqualNP.Outside.L_lib_499

theorem PEqualNP.Outside.L_lib_499 : (∀ n : ℕ,
  let V := Fin n → ZMod 2
  ∀ (f : V → ZMod 2) (M : Matrix (Fin n) (Fin n) (ZMod 2)),
    (∀ x y : V, f (x+y) + f x + f y + f 0 = dotProduct x (M.mulVec y)) →
    ∀ d : ℕ, (∃ (U : Submodule (ZMod 2) V) (p a : V) (b : ZMod 2),
        d ≤ Module.finrank (ZMod 2) U ∧
        ∀ x ∈ U, f (p+x) = dotProduct a (p+x) + b) ↔ 2*d + M.rank ≤ 2*n) := by
  intro n V f M hf d
  constructor
  · rintro ⟨U, p, a, b, hd, hlin⟩
    exact PEqualNP.Outside.L_lib_499.forward_dir f M hf d U p a b hd hlin
  · intro h_rank
    exact PEqualNP.Outside.L_lib_499.backward_dir f M hf d h_rank
