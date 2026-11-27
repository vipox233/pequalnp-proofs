import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_873

private theorem rank_inter_sup {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (U V B : Submodule K W) :
    Module.finrank K ((U ⊔ V) ⊓ B : Submodule K W) =
      Module.finrank K ((U ⊓ B) ⊔ (V ⊓ B) : Submodule K W) +
      (Module.finrank K ((U ⊔ B) ⊓ (V ⊔ B) : Submodule K W) -
       Module.finrank K ((U ⊓ V) ⊔ B : Submodule K W)) := by
  have h₁ := Submodule.finrank_sup_add_finrank_inf_eq U V
  have h₂ := Submodule.finrank_sup_add_finrank_inf_eq U B
  have h₃ := Submodule.finrank_sup_add_finrank_inf_eq V B
  have h₄ := Submodule.finrank_sup_add_finrank_inf_eq (U ⊓ V) B
  have h₅ := Submodule.finrank_sup_add_finrank_inf_eq (U ⊔ V) B
  have h₆ := Submodule.finrank_sup_add_finrank_inf_eq (U ⊓ B) (V ⊓ B)
  have h₇ := Submodule.finrank_sup_add_finrank_inf_eq (U ⊔ B) (V ⊔ B)
  have hm : (U ⊓ B) ⊓ (V ⊓ B) = (U ⊓ V) ⊓ B := by
    simp [inf_comm, inf_left_comm]
  have hj : (U ⊔ B) ⊔ (V ⊔ B) = (U ⊔ V) ⊔ B := by
    simp [sup_comm, sup_left_comm]
  rw [hm] at h₆
  rw [hj] at h₇
  have hle : (U ⊓ V) ⊔ B ≤ (U ⊔ B) ⊓ (V ⊔ B) :=
    le_inf (sup_le_sup_right inf_le_left _) (sup_le_sup_right inf_le_right _)
  have := Submodule.finrank_mono hle
  omega

private theorem memJoint {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    {u v m n : ℕ} (i₀ : Fin u) (j₀ : Fin v)
    (a : Fin u → Fin m → W) (b : Fin v → Fin n → W) (w : W) :
    (∃ (c : Fin u → Fin m → K) (t : Fin v → Fin n → K), ∀ i j,
      Fintype.linearCombination K (a i) (c i) + Fintype.linearCombination K (b j) (t j) = w) ↔
    w ∈ (⨅ i, Submodule.span K (Set.range (a i))) ⊔
      (⨅ j, Submodule.span K (Set.range (b j))) := by
  constructor
  · rintro ⟨c, t, h⟩
    refine Submodule.mem_sup.mpr ⟨_, ?_, _, ?_, h i₀ j₀⟩
    · apply (Submodule.mem_iInf _).mpr
      intro i
      rw [← Fintype.range_linearCombination]
      exact ⟨c i, add_right_cancel ((h i j₀).trans (h i₀ j₀).symm)⟩
    · apply (Submodule.mem_iInf _).mpr
      intro j
      rw [← Fintype.range_linearCombination]
      exact ⟨t j, add_left_cancel ((h i₀ j).trans (h i₀ j₀).symm)⟩
  · intro hw
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hw
    have yc (i : Fin u) : ∃ c, Fintype.linearCombination K (a i) c = y := by
      have hi := (Submodule.mem_iInf _).mp hy i
      rwa [← Fintype.range_linearCombination] at hi
    have zt (j : Fin v) : ∃ t, Fintype.linearCombination K (b j) t = z := by
      have hj := (Submodule.mem_iInf _).mp hz j
      rwa [← Fintype.range_linearCombination] at hj
    choose c hc using yc
    choose t ht using zt
    exact ⟨c, t, fun i j => congrArg₂ (· + ·) (hc i) (ht j)⟩

end PEqualNP.Outside.L_lib_873

theorem PEqualNP.Outside.L_lib_873 : (∀ (f s u v m n : ℕ), 0 < f → 0 < u → 0 < v →
  let F := ZMod 2
  let P := Fin s → F
  let E := Fin f × P
  let W := E → F
  ∀ (row : Fin u → Fin f → P → Fin m → F)
    (col : Fin v → Fin f → P → Fin n → F),
    let a := fun (i : Fin u) (j : Fin m) (e : E) =>
      row i e.1 e.2 j - row i e.1 0 j
    let b := fun (i : Fin v) (j : Fin n) (e : E) =>
      col i e.1 e.2 j - col i e.1 0 j
    let U : Submodule F W := ⨅ i : Fin u, Submodule.span F (Set.range (a i))
    let V : Submodule F W := ⨅ i : Fin v, Submodule.span F (Set.range (b i))
    let B : Submodule F W := Submodule.span F (Set.range (fun j : Fin s => fun e : E => e.2 j))
    let solo := Module.finrank F (((U ⊓ B) ⊔ (V ⊓ B)) : Submodule F W)
    let extra := Module.finrank F (((U ⊔ B) ⊓ (V ⊔ B)) : Submodule F W) -
      Module.finrank F (((U ⊓ V) ⊔ B) : Submodule F W)
    Nat.card {mask : P //
      ∃ (c : Fin u → Fin m → F) (t : Fin v → Fin n → F),
        ∀ (i : Fin u) (j : Fin v) (e : E),
          (∑ h : Fin m, c i h * a i h e) + (∑ h : Fin n, t j h * b j h e) =
            ∑ h : Fin s, mask h * e.2 h} = 2 ^ (solo + extra)) := by
  classical
  intro f s u v m n hf hu hv F P E W row col a b U V B solo extra
  let L := Fintype.linearCombination F (fun j : Fin s => fun e : E => e.2 j)
  have hB : LinearMap.range L = B := Fintype.range_linearCombination _ _
  have point {k : ℕ} (g : Fin k → W) (c : Fin k → F) (e : E) :
      Fintype.linearCombination F g c e = ∑ h, c h * g h e := by
    change (∑ i, c i • (g i : E → F)) e = _
    rw [Finset.sum_apply]
    rfl
  have hinj : Function.Injective L := by
    intro x y h
    funext k
    have he := congrFun h (⟨0,hf⟩, Pi.single k 1)
    simpa [L, point, Pi.single_apply, mul_ite] using he
  let valid (mask : P) := ∃ (c : Fin u → Fin m → F) (t : Fin v → Fin n → F),
    ∀ i j (e : E),
      (∑ h : Fin m, c i h * a i h e) + (∑ h : Fin n, t j h * b j h e) =
        ∑ h : Fin s, mask h * e.2 h
  have hvalid (mask : P) : valid mask ↔ L mask ∈ U ⊔ V := by
    rw [← PEqualNP.Outside.L_lib_873.memJoint (K := F) ⟨0,hu⟩ ⟨0,hv⟩ a b]
    constructor
    · rintro ⟨c,t,h⟩
      refine ⟨c,t,fun i j => funext fun e => ?_⟩
      simpa only [Pi.add_apply, L, point] using h i j e
    · rintro ⟨c,t,h⟩
      refine ⟨c,t,fun i j e => ?_⟩
      simpa only [Pi.add_apply, L, point] using congrFun (h i j) e
  let D : Submodule F W := (U ⊔ V) ⊓ B
  let recover (x : {mask : P // valid mask}) : D :=
    ⟨L x.val, (hvalid x.val).mp x.property, hB ▸ LinearMap.mem_range_self L x.val⟩
  have bij : Function.Bijective recover := by
    constructor
    · intro x y h
      exact Subtype.ext (hinj (congrArg Subtype.val h))
    · rintro ⟨w, hw⟩
      obtain ⟨mask, hm⟩ := hB.symm ▸ hw.2
      exact ⟨⟨mask, (hvalid mask).mpr (hm ▸ hw.1)⟩, Subtype.ext hm⟩
  change Nat.card {mask : P // valid mask} = _
  calc
    _ = Nat.card D := Nat.card_congr (Equiv.ofBijective recover bij)
    _ = 2 ^ Module.finrank F D := by
      rw [Module.natCard_eq_pow_finrank (K := F), show Nat.card F = 2 from Nat.card_zmod 2]
    _ = 2 ^ (solo + extra) := congrArg (2 ^ ·) (PEqualNP.Outside.L_lib_873.rank_inter_sup U V B)
