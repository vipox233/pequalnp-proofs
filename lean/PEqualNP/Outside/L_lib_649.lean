import Mathlib

theorem PEqualNP.Outside.L_lib_649 : ∀ (E K : Type) [Field E] [Field K] [Algebra E K] [FiniteDimensional E K]
    (S : Finset K), (0 : K) ∉ S →
  ((∃ C : K →ₗ[E] K, Module.finrank E (LinearMap.range C) ≤ 1 ∧
    ∀ z ∈ S, ∃ x : K, x ≠ 0 ∧ C x = z*x) ↔
    (0 : K) ∉ affineSpan E ((fun z : K => z⁻¹) '' (↑S : Set K))) := by
  classical
  intro E K _ _ _ _ S nozero
  rcases S.eq_empty_or_nonempty with empty|⟨z₀,hz₀⟩
  · subst S
    constructor
    · intro _
      simp only [Finset.coe_empty,Set.image_empty,AffineSubspace.span_empty]
      exact fun h => h
    · intro _
      refine ⟨(0 : K →ₗ[E] K),?_,by simp⟩
      rw [LinearMap.range_zero,finrank_bot]
      decide
  let A := affineSpan E ((fun z : K => z⁻¹) '' (↑S : Set K))
  have inside {z : K} (hz : z ∈ S) : z⁻¹ ∈ A :=
    subset_affineSpan E _ ⟨z,hz,rfl⟩
  have nz {z : K} (hz : z ∈ S) : z ≠ 0 := fun eq => nozero (eq ▸ hz)
  constructor
  · rintro ⟨C,dim,eigen⟩ zero
    obtain ⟨x₀,hx₀,k₀⟩ := eigen z₀ hz₀
    let y := C x₀
    have ny : y ≠ 0 := by simpa [y,k₀] using mul_ne_zero (nz hz₀) hx₀
    have line : Submodule.span E {y} = LinearMap.range C := by
      apply Submodule.eq_of_le_of_finrank_le
      · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr ⟨x₀,rfl⟩)
      · rwa [finrank_span_singleton ny]
    let L : K →ₗ[E] K :=
      { toFun := fun a => C (a*y)
        map_add' := fun a b => by simp [add_mul]
        map_smul' := fun a b => by simp [smul_mul_assoc] }
    have eqn (z : K) (hz : z ∈ S) : L z⁻¹ = y := by
      obtain ⟨x,hx,hc⟩ := eigen z hz
      have member : C x ∈ Submodule.span E {y} := line ▸ (show C x ∈ LinearMap.range C from ⟨x,rfl⟩)
      obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp member
      have an : a ≠ 0 := by
        intro eq
        rw [eq,zero_smul,hc] at ha
        exact mul_ne_zero (nz hz) hx ha.symm
      have em : a • (z⁻¹*y) = x := by
        rw [← mul_smul_comm,ha,hc,← mul_assoc,inv_mul_cancel₀ (nz hz),one_mul]
      have h := congrArg C em
      rw [map_smul,← ha] at h
      exact (smul_right_injective _ an) h
    let T := (affineSpan E ({y} : Set K)).comap L.toAffineMap
    have subset : A ≤ T := by
      apply affineSpan_le.mpr
      rintro _ ⟨z,hz,rfl⟩
      change L z⁻¹ ∈ affineSpan E {y}
      rw [eqn _ hz]
      exact subset_affineSpan E _ (Set.mem_singleton _)
    have zero' := subset zero
    change L 0 ∈ affineSpan E ({y} : Set K) at zero'
    simpa [ny.symm] using zero'
  · intro avoid
    change (0:K) ∉ A at avoid
    have p := inside hz₀
    have outside : z₀⁻¹ ∉ A.direction := by
      intro mem
      have h := A.vadd_mem_of_mem_direction (A.direction.neg_mem mem) p
      exact avoid (by simpa using h)
    obtain ⟨f,hn,hker⟩ := Submodule.exists_le_ker_of_notMem outside
    let l : K →ₗ[E] E := (f (z₀⁻¹))⁻¹ • f
    have eqn (z : K) (hz : z ∈ S) : l z⁻¹ = 1 := by
      have sub := A.vsub_mem_direction (inside hz) p
      have h : f (z⁻¹-z₀⁻¹)=0 := hker sub
      rw [map_sub,sub_eq_zero] at h
      simp [l,h,hn]
    let C := l.smulRight (1:K)
    refine ⟨C,?_,?_⟩
    · have le : LinearMap.range C ≤ Submodule.span E {(1:K)} := by
        rintro _ ⟨x,rfl⟩
        exact Submodule.mem_span_singleton.mpr ⟨l x,rfl⟩
      simpa [finrank_span_singleton (one_ne_zero : (1:K) ≠ 0)] using Submodule.finrank_mono le
    · intro z hz
      refine ⟨z⁻¹,inv_ne_zero (nz hz),?_⟩
      simp [C,eqn _ hz,nz hz]
