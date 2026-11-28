import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_300

open Finset Polynomial Module

private def triplePairEquiv : (Fin 5 × Fin 5 × Fin 5 × Fin 5) ≃ (Fin 4 → Fin 5) :=
  ⟨fun entries => ![entries.1, entries.2.1, entries.2.2.1, entries.2.2.2],
    fun columns => (columns 0, columns 1, columns 2, columns 3),
    fun _ => rfl, fun columns => by ext index; fin_cases index <;> rfl⟩

private lemma triplePairEquiv_injective (first second third fourth : Fin 5) :
    Function.Injective (triplePairEquiv (first, second, third, fourth)) ↔
      first ≠ second ∧ first ≠ third ∧ first ≠ fourth ∧
        second ≠ third ∧ second ≠ fourth ∧ third ≠ fourth := by
  refine ⟨fun hinj => ?_, fun ⟨h12, h13, h14, h23, h24, h34⟩ left right heq => ?_⟩
  · have distinct (left right : Fin 4) (hne : left ≠ right := by decide) :
        triplePairEquiv (first, second, third, fourth) left ≠
          triplePairEquiv (first, second, third, fourth) right := fun heq => hne (hinj heq)
    exact ⟨distinct 0 1, distinct 0 2, distinct 0 3, distinct 1 2, distinct 1 3, distinct 2 3⟩
  · change ![first, second, third, fourth] left = ![first, second, third, fourth] right at heq
    fin_cases left <;> fin_cases right <;> simp_all [Ne.symm]

private lemma sum_injections (term : (Fin 4 → Fin 5) → ℂ) :
    (∑ f : Fin 4 ↪ Fin 5, term f) =
      ∑ first : Fin 5, ∑ second : Fin 5, ∑ third : Fin 5, ∑ fourth : Fin 5,
        if first ≠ second ∧ first ≠ third ∧ first ≠ fourth ∧
            second ≠ third ∧ second ≠ fourth ∧ third ≠ fourth then
          term ![first, second, third, fourth] else 0 := by
  classical
  calc
    _ = ∑ columns : Fin 4 → Fin 5, if Function.Injective columns then term columns else 0 := by
      rw [← (Equiv.subtypeInjectiveEquivEmbedding (Fin 4) (Fin 5)).sum_comp,
        ← sum_filter (p := Function.Injective)]
      exact (sum_subtype _ (fun _ => by simp) term).symm
    _ = _ := by
      rw [← triplePairEquiv.sum_comp]
      simp only [Fintype.sum_prod_type, triplePairEquiv_injective]
      rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private lemma permanent_expand (x y : Fin 5 → ℂ) (t : ℂ) :
    let sx := ∑ i, x i
    let sy := ∑ i, y i
    let qx := ∑ i, (x i)^2
    let qy := ∑ i, (y i)^2
    let dot := ∑ i, x i * y i
    let rows : Fin 4 → Fin 5 → ℂ := ![x, -x, t • y, -(t • y)]
    (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4, (1 + rows i (f i))) =
      120 + 6 * (qx - sx^2) + t^2 * (6 * (qy - sy^2) +
        (sx^2 - qx) * (sy^2 - qy) - 4 * dot * sx * sy + 2 * dot^2 +
          4 * sy * (∑ i, (x i)^2 * y i) + 4 * sx * (∑ i, x i * (y i)^2) -
            6 * (∑ i, (x i)^2 * (y i)^2)) := by
  dsimp only
  rw [sum_injections (fun columns => ∏ i : Fin 4,
    (1 + (![x, -x, t • y, -(t • y)] : Fin 4 → Fin 5 → ℂ) i (columns i)))]
  simp (config := {decide := true}) only [Fin.prod_univ_four, Fin.sum_univ_five,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons,
    Pi.neg_apply, Pi.smul_apply, smul_eq_mul, ne_eq, and_true, true_and, and_false,
    false_and, ite_true, ite_false]
  ring

private lemma permanent_iff (x y : Fin 5 → ℂ) (hx : (∑ i, x i) = 0)
    (hy : (∑ i, y i) = 0) (hyq : (∑ i, (y i)^2) = 0) :
    (∀ t : ℂ, let rows : Fin 4 → Fin 5 → ℂ := ![x, -x, t • y, -(t • y)]
      (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4, (1 + rows i (f i))) = 120) ↔
      (∑ i, (x i)^2) = 0 ∧ 3 * (∑ i, (x i)^2 * (y i)^2) = (∑ i, x i * y i)^2 := by
  have expansion (t : ℂ) :
      (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4,
        (1 + (![x, -x, t • y, -(t • y)] : Fin 4 → Fin 5 → ℂ) i (f i))) =
        120 + 6 * (∑ i, (x i)^2) +
          t^2 * (2 * (∑ i, x i * y i)^2 - 6 * (∑ i, (x i)^2 * (y i)^2)) := by
    have he := permanent_expand x y t
    dsimp only at he
    rw [he, hx, hy, hyq]
    ring
  constructor
  · intro hlevel
    have hzero := (expansion 0).symm.trans (hlevel 0)
    have hone := (expansion 1).symm.trans (hlevel 1)
    have hqx : (∑ i, (x i)^2) = 0 := by linear_combination hzero / 6
    exact ⟨hqx, by linear_combination (hzero - hone) / 2⟩
  · rintro ⟨hqx, hxy⟩ t
    refine (expansion t).trans ?_
    rw [hqx, ← hxy]
    ring

private lemma charpoly_factor {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (operator : Module.End ℂ V) (space : Submodule ℂ V)
    (stable : space ≤ space.comap operator) :
    operator.charpoly = (operator.restrict stable).charpoly *
      (space.mapQ space operator stable).charpoly := by
  apply Polynomial.funext
  intro value
  simp only [eval_mul, LinearMap.eval_charpoly]
  let shift := algebraMap ℂ (Module.End ℂ V) value - operator
  have hshift : space ≤ space.comap shift := fun vector hvector => by
    change value • vector - operator vector ∈ space
    exact space.sub_mem (space.smul_mem _ hvector) (stable hvector)
  have hrest : shift.restrict hshift = algebraMap ℂ (Module.End ℂ space) value -
      operator.restrict stable := by
    ext vector : 1
    apply Subtype.ext
    rfl
  have hquot : space.mapQ space shift hshift =
      algebraMap ℂ (Module.End ℂ (V ⧸ space)) value - space.mapQ space operator stable := by
    apply LinearMap.ext
    intro vector
    obtain ⟨source, rfl⟩ := space.mkQ_surjective vector
    change space.mkQ (value • source - operator source) =
      value • space.mkQ source - space.mkQ (operator source)
    rw [map_sub, map_smul]
  exact (LinearMap.det_eq_det_mul_det space shift hshift).trans (by rw [hrest, hquot])

private lemma charpoly_dual {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (operator : Module.End ℂ V) :
    operator.dualMap.charpoly = operator.charpoly := by
  apply Polynomial.funext
  intro value
  rw [LinearMap.eval_charpoly, LinearMap.eval_charpoly,
    ← LinearMap.det_dualMap (algebraMap ℂ (Module.End ℂ V) value - operator)]
  congr 1
  ext vector source : 2
  simp [LinearMap.dualMap_apply]

private lemma orthogonal_stable {V : Type*} [AddCommGroup V] [Module ℂ V]
    (form : LinearMap.BilinForm ℂ V) (operator : Module.End ℂ V)
    (adjoint : ∀ left right, form (operator left) right = form left (operator right))
    (space : Submodule ℂ V) (stable : space ≤ space.comap operator) :
    form.orthogonal space ≤ (form.orthogonal space).comap operator := by
  intro vector hvector
  change operator vector ∈ form.orthogonal space
  intro source hsource
  rw [← adjoint]
  exact hvector (operator source) (stable hsource)

private lemma charpoly_orthogonal_quotient {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (form : LinearMap.BilinForm ℂ V)
    (symmetric : form.IsSymm) (nondegenerate : form.Nondegenerate)
    (operator : Module.End ℂ V)
    (adjoint : ∀ left right, form (operator left) right = form left (operator right))
    (space : Submodule ℂ V) (stable : space ≤ space.comap operator) :
    ((form.orthogonal space).mapQ (form.orthogonal space) operator
      (orthogonal_stable form operator adjoint space stable)).charpoly =
        (operator.restrict stable).charpoly := by
  let orth := form.orthogonal space
  let pairing : V →ₗ[ℂ] Module.Dual ℂ space := space.dualRestrict.comp form
  have hsurj : Function.Surjective pairing :=
    Subspace.dualRestrict_surjective.comp (form.toDual nondegenerate).surjective
  have hker : orth = LinearMap.ker pairing := by
    ext vector
    rw [LinearMap.mem_ker]
    exact ⟨fun h => LinearMap.ext fun source =>
        (symmetric.eq vector source).trans (h source source.property),
      fun h source hsource =>
        (symmetric.eq source vector).trans (LinearMap.congr_fun h ⟨source, hsource⟩)⟩
  let quotientEquiv : (V ⧸ orth) ≃ₗ[ℂ] Module.Dual ℂ space :=
    (Submodule.quotEquivOfEq orth (LinearMap.ker pairing) hker).trans
      (pairing.quotKerEquivOfSurjective hsurj)
  have hpair (vector : V) : quotientEquiv (orth.mkQ vector) = pairing vector := by
    simp [quotientEquiv, Submodule.mkQ_apply]
  let quotientOperator := orth.mapQ orth operator
    (orthogonal_stable form operator adjoint space stable)
  have hconj : quotientEquiv.conj quotientOperator = (operator.restrict stable).dualMap := by
    ext function source : 2
    obtain ⟨vector, rfl⟩ := quotientEquiv.surjective function
    obtain ⟨vector, rfl⟩ := orth.mkQ_surjective vector
    change quotientEquiv (quotientOperator (quotientEquiv.symm (quotientEquiv (orth.mkQ vector))))
      source = _
    rw [quotientEquiv.symm_apply_apply]
    change quotientEquiv (orth.mkQ (operator vector)) source = _
    rw [hpair, hpair]
    exact adjoint vector source
  exact (quotientEquiv.charpoly_conj quotientOperator).symm.trans
    ((congrArg LinearMap.charpoly hconj).trans (charpoly_dual _))

private lemma stable_line {V : Type*} [AddCommGroup V] [Module ℂ V]
    (operator : Module.End ℂ V) {vector : V} {value : ℂ} (heig : operator vector = value • vector) :
    (ℂ ∙ vector) ≤ (ℂ ∙ vector).comap operator := by
  intro source hsource
  obtain ⟨scalar, rfl⟩ := Submodule.mem_span_singleton.mp hsource
  change operator (scalar • vector) ∈ ℂ ∙ vector
  rw [map_smul, heig, smul_smul]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

private lemma scalar_charpoly {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (value : ℂ) : (algebraMap ℂ (Module.End ℂ V) value).charpoly =
      (X - C value) ^ finrank ℂ V := by
  apply Polynomial.funext
  intro point
  rw [LinearMap.eval_charpoly, ← map_sub, Algebra.algebraMap_eq_smul_one, LinearMap.det_smul]
  simp

private lemma line_charpoly {V : Type*} [AddCommGroup V] [Module ℂ V]
    (operator : Module.End ℂ V) {vector : V} (hnz : vector ≠ 0) {value : ℂ}
    (heig : operator vector = value • vector) :
    (operator.restrict (stable_line operator heig)).charpoly = X - C value := by
  have hscalar : operator.restrict (stable_line operator heig) =
      algebraMap ℂ (Module.End ℂ (ℂ ∙ vector)) value := by
    apply LinearMap.ext
    rintro ⟨source, hsource⟩
    obtain ⟨scalar, rfl⟩ := Submodule.mem_span_singleton.mp hsource
    apply Subtype.ext
    change operator (scalar • vector) = value • (scalar • vector)
    rw [map_smul, heig, smul_smul, smul_smul, mul_comm]
  rw [hscalar, scalar_charpoly, finrank_span_singleton hnz, pow_one]

private lemma linear_factor_of_square {value : ℂ} {root other : ℂ[X]}
    (hf : root ^ 2 = (X - C value) * other) :
    ∃ factor : ℂ[X], root = (X - C value) * factor ∧
      other = (X - C value) * factor ^ 2 := by
  have hzero := congrArg (Polynomial.eval value) hf
  have heval : root.eval value = 0 := by
    simp only [eval_pow, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul,
      pow_eq_zero_iff (by decide : 2 ≠ 0)] at hzero
    exact hzero
  obtain ⟨factor, hfactor⟩ := (dvd_iff_isRoot.mpr heval : X - C value ∣ root)
  refine ⟨factor, hfactor, ?_⟩
  apply mul_left_cancel₀ (X_sub_C_ne_zero value)
  calc
    _ = root ^ 2 := hf.symm
    _ = _ := by rw [hfactor]; ring

private lemma isotropic_eigenvector {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [Nontrivial V] (form : LinearMap.BilinForm ℂ V)
    (symmetric : form.IsSymm) (nondegenerate : form.Nondegenerate)
    (operator : Module.End ℂ V)
    (adjoint : ∀ left right, form (operator left) right = form left (operator right))
    {root : ℂ[X]} (hsquare : operator.charpoly = root ^ 2) :
    ∃ value : ℂ, ∃ vector : V, vector ≠ 0 ∧ operator vector = value • vector ∧ form vector vector = 0 := by
  obtain ⟨value, hvalue⟩ := operator.exists_eigenvalue
  obtain ⟨vector, hvector, hnz⟩ := hvalue.exists_hasEigenvector
  have heig := Module.End.mem_eigenspace_iff.mp hvector
  by_cases hnorm : form vector vector = 0
  · exact ⟨value, vector, hnz, heig, hnorm⟩
  let line := ℂ ∙ vector
  let orth := form.orthogonal line
  have hline := stable_line operator heig
  have horth := orthogonal_stable form operator adjoint line hline
  let restricted : Module.End ℂ orth := operator.restrict (p := orth) (q := orth) horth
  have hfactor : root ^ 2 = (X - C value) * restricted.charpoly := by
    rw [← hsquare, charpoly_factor operator orth horth,
      charpoly_orthogonal_quotient form symmetric nondegenerate operator adjoint line hline,
      line_charpoly operator hnz heig, mul_comm]
  obtain ⟨factor, _, hfactor⟩ := linear_factor_of_square hfactor
  have hvalue' : restricted.HasEigenvalue value := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, hfactor]
    simp [Polynomial.IsRoot]
  obtain ⟨other, hother, hothernz⟩ := hvalue'.exists_hasEigenvector
  have hothereig : operator (other : V) = value • (other : V) :=
    congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp hother)
  have horthog : form vector (other : V) = 0 := other.property vector (Submodule.mem_span_singleton_self _)
  obtain ⟨coef, hcoef⟩ := IsAlgClosed.exists_pow_nat_eq
    (-(form (other : V) (other : V)) / form vector vector) (by decide : 0 < 2)
  refine ⟨value, coef • vector + (other : V), ?_, ?_, ?_⟩
  · intro hzero
    have hcoefzero : coef * form vector vector = 0 := by
      simpa [map_add, map_smul, horthog] using congrArg (form vector) hzero
    have hcz := (mul_eq_zero.mp hcoefzero).resolve_right hnorm
    apply hothernz
    apply Subtype.ext
    simpa [hcz] using hzero
  · simp only [map_add, map_smul, heig, hothereig, smul_add, smul_smul]
    rw [mul_comm coef value]
  · have horthog' : form (other : V) vector = 0 := (symmetric.eq _ _).trans horthog
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      horthog, horthog', mul_zero, add_zero, zero_add]
    have hc := (eq_div_iff hnorm).mp hcoef
    linear_combination hc

private lemma square_of_plane {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (dimension : finrank ℂ V = 4) (form : LinearMap.BilinForm ℂ V)
    (symmetric : form.IsSymm) (nondegenerate : form.Nondegenerate)
    (operator : Module.End ℂ V)
    (adjoint : ∀ left right, form (operator left) right = form left (operator right))
    (plane : Submodule ℂ V) (rank : finrank ℂ plane = 2)
    (isotropic : plane ≤ form.orthogonal plane) (stable : plane ≤ plane.comap operator) :
    ∃ root : ℂ[X], operator.charpoly = root ^ 2 := by
  have horth : form.orthogonal plane = plane := by
    symm
    apply Submodule.eq_of_le_of_finrank_le isotropic
    rw [form.finrank_orthogonal nondegenerate, dimension, rank]
  have hstable := orthogonal_stable form operator adjoint plane stable
  have hquot := charpoly_orthogonal_quotient form symmetric nondegenerate operator adjoint plane stable
  have hfact := charpoly_factor operator (form.orthogonal plane) hstable
  rw [hquot] at hfact
  have hrest : (operator.restrict hstable).charpoly = (operator.restrict stable).charpoly := by
    have same (other : Submodule ℂ V) (hother : other ≤ other.comap operator) (heq : other = plane) :
        (operator.restrict hother).charpoly = (operator.restrict stable).charpoly := by
      subst other
      rfl
    exact same _ hstable horth
  exact ⟨_, by rw [hfact, hrest, pow_two]⟩

private lemma plane_of_square {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (dimension : finrank ℂ V = 4) (form : LinearMap.BilinForm ℂ V)
    (symmetric : form.IsSymm) (nondegenerate : form.Nondegenerate)
    (operator : Module.End ℂ V)
    (adjoint : ∀ left right, form (operator left) right = form left (operator right))
    {root : ℂ[X]} (hsquare : operator.charpoly = root ^ 2) :
    ∃ plane : Submodule ℂ V, finrank ℂ plane = 2 ∧
      plane ≤ form.orthogonal plane ∧ plane ≤ plane.comap operator := by
  let : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℂ) (by rw [dimension]; decide)
  obtain ⟨value, vector, hnz, heig, hiso⟩ :=
    isotropic_eigenvector form symmetric nondegenerate operator adjoint hsquare
  let line := ℂ ∙ vector
  let orth := form.orthogonal line
  let hline := stable_line operator heig
  let horth := orthogonal_stable form operator adjoint line hline
  have hsub : line ≤ orth := by
    intro left hleft right hright
    obtain ⟨scalarLeft, rfl⟩ := Submodule.mem_span_singleton.mp hleft
    obtain ⟨scalarRight, rfl⟩ := Submodule.mem_span_singleton.mp hright
    simp [hiso]
  let line' := line.comap orth.subtype
  let restrictOp := operator.restrict (p := orth) (q := orth) horth
  have hline' : line' ≤ line'.comap restrictOp := fun elem helem => hline helem
  let quotientOp := line'.mapQ line' restrictOp hline'
  have hlineRank : finrank ℂ line' = 1 :=
    (Submodule.comapSubtypeEquivOfLe hsub).finrank_eq.trans (finrank_span_singleton hnz)
  have hOrthRank : finrank ℂ orth = 3 := by
    change finrank ℂ (form.orthogonal line) = 3
    rw [form.finrank_orthogonal nondegenerate, dimension, finrank_span_singleton hnz]
  have hQuotientRank : finrank ℂ (orth ⧸ line') = 2 := by
    have hd := line'.finrank_quotient_add_finrank
    rw [hlineRank, hOrthRank] at hd
    omega
  have hlineChar : (restrictOp.restrict hline').charpoly = X - C value := by
    have hscalar : restrictOp.restrict hline' = algebraMap ℂ (Module.End ℂ line') value := by
      apply LinearMap.ext
      rintro ⟨⟨source, hsource⟩, hsource'⟩
      obtain ⟨coef, heq⟩ := Submodule.mem_span_singleton.mp (show source ∈ line from hsource')
      apply Subtype.ext
      apply Subtype.ext
      change operator source = value • source
      rw [← heq, map_smul, heig, smul_smul, smul_smul, mul_comm]
    rw [hscalar, scalar_charpoly, hlineRank, pow_one]
  have hfactor : root ^ 2 = (X - C value) ^ 2 * quotientOp.charpoly := by
    have hquot := charpoly_orthogonal_quotient form symmetric nondegenerate operator adjoint line hline
    have houter := charpoly_factor operator orth horth
    have hinner := charpoly_factor restrictOp line' hline'
    rw [← hsquare, houter, hquot, line_charpoly operator hnz heig, hinner, hlineChar]
    change ((X - C value) * quotientOp.charpoly) * (X - C value) = _
    ring
  obtain ⟨quotientRoot, _, hroot⟩ := linear_factor_of_square (value := value)
    (other := (X - C value) * quotientOp.charpoly) (by rw [hfactor, pow_two, mul_assoc])
  have hsquareQuotient : quotientOp.charpoly = quotientRoot ^ 2 :=
    mul_left_cancel₀ (X_sub_C_ne_zero value) hroot
  let restrictForm := form.restrict orth
  have hrad : line' ≤ restrictForm.ker := by
    intro left hleft
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro right
    exact right.property left hleft
  have hrad' : line' ≤ restrictForm.flip.ker := by
    intro left hleft
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro right
    exact (symmetric.eq right left).trans (right.property left hleft)
  let quotientForm : LinearMap.BilinForm ℂ (orth ⧸ line') := restrictForm.liftQ₂ line' line' hrad hrad'
  have hsymm : quotientForm.IsSymm := by
    constructor
    intro left right
    obtain ⟨left, rfl⟩ := line'.mkQ_surjective left
    obtain ⟨right, rfl⟩ := line'.mkQ_surjective right
    exact symmetric.eq left right
  have hnondeg : quotientForm.Nondegenerate := hsymm.isRefl.nondegenerate_iff_separatingLeft.mpr (by
    intro left hleft
    obtain ⟨left, rfl⟩ := line'.mkQ_surjective left
    apply (Submodule.Quotient.mk_eq_zero line').mpr
    change (left : V) ∈ line
    rw [← form.orthogonal_orthogonal nondegenerate symmetric.isRefl line]
    intro source hsource
    exact (symmetric.eq source left).trans (hleft (line'.mkQ ⟨source, hsource⟩)))
  have hadjoint : ∀ left right, quotientForm (quotientOp left) right =
      quotientForm left (quotientOp right) := by
    intro left right
    obtain ⟨left, rfl⟩ := line'.mkQ_surjective left
    obtain ⟨right, rfl⟩ := line'.mkQ_surjective right
    exact adjoint left right
  let : Nontrivial (orth ⧸ line') := Module.nontrivial_of_finrank_pos (R := ℂ) (by rw [hQuotientRank]; decide)
  obtain ⟨otherValue, other, honz, hoeig, hoiso⟩ :=
    isotropic_eigenvector quotientForm hsymm hnondeg quotientOp hadjoint hsquareQuotient
  let otherLine := ℂ ∙ other
  let lifted := otherLine.comap line'.mkQ
  let projected : lifted →ₗ[ℂ] otherLine := LinearMap.codRestrict otherLine
    (line'.mkQ.comp lifted.subtype) (fun elem => elem.property)
  have hsurj : Function.Surjective projected := by
    rintro ⟨elem, helem⟩
    obtain ⟨source, rfl⟩ := line'.mkQ_surjective elem
    exact ⟨⟨source, helem⟩, rfl⟩
  have hcontained : line' ≤ lifted := by
    intro elem helem
    change line'.mkQ elem ∈ otherLine
    have hzero : line'.mkQ elem = 0 := (Submodule.Quotient.mk_eq_zero line').mpr helem
    simp [hzero]
  have hker : LinearMap.ker projected = line'.comap lifted.subtype := by
    ext elem
    rw [LinearMap.mem_ker, Subtype.ext_iff]
    exact Submodule.Quotient.mk_eq_zero line'
  have hliftRank : finrank ℂ lifted = 2 := by
    rw [← LinearMap.finrank_range_add_finrank_ker projected,
      LinearMap.range_eq_top.mpr hsurj, finrank_top, hker,
      (Submodule.comapSubtypeEquivOfLe hcontained).finrank_eq, hlineRank,
      finrank_span_singleton honz]
  refine ⟨lifted.map orth.subtype, (Submodule.finrank_map_subtype_eq _ _).trans hliftRank, ?_, ?_⟩
  · rintro left ⟨left, hleft, rfl⟩ right ⟨right, hright, rfl⟩
    change quotientForm (line'.mkQ right) (line'.mkQ left) = 0
    obtain ⟨coefLeft, heqLeft⟩ := Submodule.mem_span_singleton.mp
      (show line'.mkQ left ∈ otherLine from hleft)
    obtain ⟨coefRight, heqRight⟩ := Submodule.mem_span_singleton.mp
      (show line'.mkQ right ∈ otherLine from hright)
    rw [← heqLeft, ← heqRight]
    simp [hoiso]
  · rintro elem ⟨elem, helem, rfl⟩
    refine ⟨restrictOp elem, ?_, rfl⟩
    change quotientOp (line'.mkQ elem) ∈ otherLine
    exact stable_line quotientOp hoeig helem

private abbrev Column := Fin 5 → ℂ

private noncomputable def dotForm : LinearMap.BilinForm ℂ Column := dotProductBilin ℂ ℂ

private noncomputable def columnSum : Column →ₗ[ℂ] ℂ := dotForm (fun _ => 1)

private noncomputable abbrev Center := columnSum.ker

private lemma sum_eq (vector : Column) : columnSum vector = ∑ i, vector i := by
  change (∑ i, 1 * vector i) = _
  simp

private lemma mem_center (vector : Column) : vector ∈ Center ↔ (∑ i, vector i) = 0 := by
  rw [LinearMap.mem_ker, sum_eq]

private lemma centered_last (vector : Center) : (vector : Column) (Fin.last 4) =
    -∑ i : Fin 4, (vector : Column) i.castSucc := by
  have h := (mem_center _).mp vector.property
  rw [Fin.sum_univ_castSucc, add_comm, add_eq_zero_iff_eq_neg] at h
  exact h

private noncomputable def centerCoords : Center ≃ₗ[ℂ] (Fin 4 → ℂ) where
  toFun vector := Fin.init (vector : Column)
  invFun coords := ⟨Fin.snoc coords (-∑ i, coords i), by
    rw [mem_center, Fin.sum_univ_castSucc]
    change (∑ i : Fin 4, @Fin.snoc 4 (fun _ => ℂ) coords (-∑ j, coords j) i.castSucc) +
      @Fin.snoc 4 (fun _ => ℂ) coords (-∑ j, coords j) (Fin.last 4) = 0
    simp only [Fin.snoc_castSucc, Fin.snoc_last, add_neg_cancel]⟩
  left_inv vector := by
    apply Subtype.ext
    change Fin.snoc (Fin.init (vector : Column)) (-∑ i : Fin 4, (vector : Column) i.castSucc) = vector.val
    rw [← centered_last vector, Fin.snoc_init_self]
  right_inv coords := Fin.init_snoc _ _
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma centerDim : finrank ℂ Center = 4 := by
  rw [centerCoords.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

private lemma basisVector_cast (col idx : Fin 4) :
    (centerCoords.symm (Pi.single col 1) : Column) idx.castSucc = (Pi.single col 1 : Fin 4 → ℂ) idx := by
  change @Fin.snoc 4 (fun _ => ℂ) (Pi.single col 1 : Fin 4 → ℂ)
    (-∑ i, (Pi.single col 1 : Fin 4 → ℂ) i) idx.castSucc = _
  exact Fin.snoc_castSucc _ _ _

private lemma basisVector_last (col : Fin 4) :
    (centerCoords.symm (Pi.single col 1) : Column) (Fin.last 4) = -1 := by
  change @Fin.snoc 4 (fun _ => ℂ) (Pi.single col 1 : Fin 4 → ℂ)
    (-∑ i, (Pi.single col 1 : Fin 4 → ℂ) i) (Fin.last 4) = _
  rw [Fin.snoc_last]
  simp

private lemma basisVector_sum (weight : Column) (col : Fin 4) :
    (∑ i, weight i * (centerCoords.symm (Pi.single col 1) : Column) i) =
      weight col.castSucc - weight (Fin.last 4) := by
  rw [Fin.sum_univ_castSucc]
  change (∑ i : Fin 4, weight i.castSucc * (centerCoords.symm (Pi.single col 1) : Column) i.castSucc) +
    weight (Fin.last 4) * (centerCoords.symm (Pi.single col 1) : Column) (Fin.last 4) = _
  simp only [basisVector_cast, basisVector_last, mul_neg, mul_one, sub_eq_add_neg]
  congr 1
  rw [Finset.sum_eq_single col]
  · simp
  · intro index _ hne
    simp [Pi.single_eq_of_ne hne]
  · simp

private noncomputable def centerForm : LinearMap.BilinForm ℂ Center := dotForm.restrict Center

private lemma centerForm_apply (left right : Center) :
    centerForm left right = ∑ i, (left : Column) i * (right : Column) i := rfl

private lemma centerForm_symm : centerForm.IsSymm := by
  constructor
  intro left right
  simp only [centerForm_apply, mul_comm]

set_option maxHeartbeats 1200000 in
private lemma centerForm_nondeg : centerForm.Nondegenerate :=
  centerForm_symm.isRefl.nondegenerate_iff_separatingLeft.mpr (by
    intro vector hvector
    have heq (index : Fin 4) : (vector : Column) index.castSucc = (vector : Column) (Fin.last 4) := by
      have he := hvector (centerCoords.symm (Pi.single index 1))
      rw [centerForm_apply, basisVector_sum] at he
      exact sub_eq_zero.mp he
    have hlast := centered_last vector
    have hsum : (∑ i : Fin 4, (vector : Column) i.castSucc) = 4 * (vector : Column) (Fin.last 4) := by
      simp only [heq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
    rw [hsum] at hlast
    have hzero : (vector : Column) (Fin.last 4) = 0 := by linear_combination hlast / 5
    apply Subtype.ext
    funext index
    cases index using Fin.lastCases with
    | last => exact hzero
    | cast index => exact (heq index).trans hzero)

private noncomputable def projectCenter : Column →ₗ[ℂ] Column :=
  LinearMap.id - (1 / 5 : ℂ) • columnSum.smulRight (fun _ => 1)

private lemma projectCenter_apply (vector : Column) (i : Fin 5) :
    projectCenter vector i = vector i - (∑ j, vector j) / 5 := by
  simp [projectCenter, sum_eq, div_eq_mul_inv, mul_comm]

private lemma projectCenter_mem (vector : Column) : projectCenter vector ∈ Center := by
  rw [mem_center]
  simp_rw [projectCenter_apply, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

private noncomputable def rawOperator (profile : Column) : Column →ₗ[ℂ] Column :=
  (Matrix.diagonal fun i => (profile i)^2).mulVecLin -
    (1 / 3 : ℂ) • (dotForm profile).smulRight profile

private lemma rawOperator_apply (profile vector : Column) (i : Fin 5) :
    rawOperator profile vector i = (profile i)^2 * vector i -
      profile i * (∑ j, profile j * vector j) / 3 := by
  simp [rawOperator, dotForm, dotProductBilin, dotProduct, Matrix.mulVec_diagonal, div_eq_mul_inv]
  ring

private noncomputable def centerOperator (profile : Column) : Module.End ℂ Center :=
  ((projectCenter.comp (rawOperator profile)).comp Center.subtype).codRestrict Center
    (fun vector => projectCenter_mem (rawOperator profile vector))

private lemma centerOperator_apply (profile : Column) (vector : Center) (i : Fin 5) :
    (centerOperator profile vector : Column) i =
      rawOperator profile vector i - (∑ j, rawOperator profile vector j) / 5 :=
  projectCenter_apply (rawOperator profile vector) i

private lemma centerOperator_form (profile : Column) (left right : Center) :
    centerForm (centerOperator profile left) right =
      (∑ i, (profile i)^2 * (left : Column) i * (right : Column) i) -
        (∑ i, profile i * (left : Column) i) * (∑ i, profile i * (right : Column) i) / 3 := by
  rw [centerForm_apply]
  simp_rw [centerOperator_apply, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum,
    (mem_center _).mp right.property, mul_zero, sub_zero, rawOperator_apply]
  simp_rw [sub_mul, Finset.sum_sub_distrib, div_eq_mul_inv,
    show ∀ i : Fin 5, profile i * (∑ j, profile j * (left : Column) j) * 3⁻¹ * (right : Column) i =
      ((∑ j, profile j * (left : Column) j) * 3⁻¹) * (profile i * (right : Column) i) by
        intro i; ring, ← Finset.mul_sum]
  ring

private lemma centerOperator_adjoint (profile : Column) (left right : Center) :
    centerForm (centerOperator profile left) right = centerForm left (centerOperator profile right) := by
  rw [centerForm_symm.eq left (centerOperator profile right), centerOperator_form, centerOperator_form]
  congr 1
  · apply Finset.sum_congr rfl
    intro index _
    ring
  · ring

private noncomputable def profileMatrix (profile : Column) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun row col => (if row = col then (profile row.castSucc)^2 else 0) -
    ((profile col.castSucc)^2 - (profile (Fin.last 4))^2) / 5 -
    profile row.castSucc * (profile col.castSucc - profile (Fin.last 4)) / 3

private lemma rawOperator_sum (profile vector : Column) (hprofile : (∑ i, profile i) = 0) :
    (∑ i, rawOperator profile vector i) = ∑ i, (profile i)^2 * vector i := by
  simp_rw [rawOperator_apply, Finset.sum_sub_distrib, div_eq_mul_inv,
    mul_assoc, ← Finset.sum_mul, hprofile, zero_mul, sub_zero]

set_option maxHeartbeats 1200000 in
private lemma centerChar_eq_matrix (profile : Column) (hprofile : (∑ i, profile i) = 0) :
    (centerOperator profile).charpoly = (profileMatrix profile).charpoly := by
  let basis := (Pi.basisFun ℂ (Fin 4)).map centerCoords.symm
  rw [← LinearMap.charpoly_toMatrix _ basis]
  congr 1
  ext row col
  have coordinate (vector : Center) : basis.repr vector row = (vector : Column) row.castSucc := by
    change (Pi.basisFun ℂ (Fin 4)).repr (centerCoords vector) row = _
    rw [Pi.basisFun_repr]
    rfl
  rw [LinearMap.toMatrix_apply, coordinate, centerOperator_apply, rawOperator_sum _ _ hprofile,
    rawOperator_apply]
  have hb : basis col = centerCoords.symm (Pi.single col 1) := by
    rw [Basis.map_apply, Pi.basisFun_apply]
  rw [hb, basisVector_cast, basisVector_sum, basisVector_sum]
  simp only [Pi.single_apply, profileMatrix, Matrix.of_apply]
  by_cases h : row = col <;> simp [h] <;> ring

private def elementaryFive (profile : Column) (degree : ℕ) : ℂ :=
  ∑ subset ∈ (Finset.univ : Finset (Fin 5)).powersetCard degree, ∏ index ∈ subset, profile index

private lemma elementaryThree (profile : Column) : elementaryFive profile 3 =
    profile 0 * profile 1 * profile 2 + profile 0 * profile 1 * profile 3 +
    profile 0 * profile 1 * profile 4 + profile 0 * profile 2 * profile 3 +
    profile 0 * profile 2 * profile 4 + profile 0 * profile 3 * profile 4 +
    profile 1 * profile 2 * profile 3 + profile 1 * profile 2 * profile 4 +
    profile 1 * profile 3 * profile 4 + profile 2 * profile 3 * profile 4 := by
  have henumerate : (Finset.univ : Finset (Fin 5)).powersetCard 3 =
      {{0, 1, 2}, {0, 1, 3}, {0, 1, 4}, {0, 2, 3}, {0, 2, 4}, {0, 3, 4},
       {1, 2, 3}, {1, 2, 4}, {1, 3, 4}, {2, 3, 4}} := by decide
  rw [elementaryFive, henumerate]
  simp (disch := decide) only [Finset.sum_insert, Finset.prod_insert,
    Finset.sum_singleton, Finset.prod_singleton]
  ring

private lemma elementaryFour (profile : Column) : elementaryFive profile 4 =
    profile 0 * profile 1 * profile 2 * profile 3 + profile 0 * profile 1 * profile 2 * profile 4 +
    profile 0 * profile 1 * profile 3 * profile 4 + profile 0 * profile 2 * profile 3 * profile 4 +
    profile 1 * profile 2 * profile 3 * profile 4 := by
  have henumerate : (Finset.univ : Finset (Fin 5)).powersetCard 4 =
    {{0, 1, 2, 3}, {0, 1, 2, 4}, {0, 1, 3, 4}, {0, 2, 3, 4}, {1, 2, 3, 4}} := by decide
  rw [elementaryFive, henumerate]
  simp (disch := decide) only [Finset.sum_insert, Finset.prod_insert,
    Finset.sum_singleton, Finset.prod_singleton]
  ring

private lemma elementaryFive_apply (profile : Column) : elementaryFive profile 5 =
    profile 0 * profile 1 * profile 2 * profile 3 * profile 4 := by
  have henumerate : (Finset.univ : Finset (Fin 5)).powersetCard 5 =
      {{0, 1, 2, 3, 4}} := by decide
  rw [elementaryFive, henumerate, Finset.sum_singleton]
  simp (disch := decide) only [Finset.prod_insert, Finset.prod_singleton]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6000000 in
private lemma profileChar_eval (profile : Column) (hprofile : (∑ i, profile i) = 0)
    (hnorm : (∑ i, (profile i)^2) = 0) (point : ℂ) :
    (profileMatrix profile).charpoly.eval point = point^4 - 2 * elementaryFive profile 4 / 15 * point^2 +
      (4 * elementaryFive profile 3 * elementaryFive profile 5 - (elementaryFive profile 4)^2) / 15 := by
  have hlast : profile 4 = -(profile 0 + profile 1 + profile 2 + profile 3) := by
    rw [Fin.sum_univ_five] at hprofile
    linear_combination hprofile
  have determinant : (profileMatrix profile).charpoly.eval point =
      point^4 - 2 * elementaryFive profile 4 / 15 * point^2 +
        (4 * elementaryFive profile 3 * elementaryFive profile 5 - (elementaryFive profile 4)^2) / 15 +
        (∑ i, (profile i)^2) * (elementaryFive profile 4 / 15 * point +
          (∑ i, (profile i)^2) / 20 * point^2 - 7 / 15 * point^3) := by
    rw [Matrix.eval_charpoly, Matrix.det_succ_row_zero, Fin.sum_univ_four]
    simp only [Matrix.det_succ_row_zero (n := 2), Fin.sum_univ_three, Matrix.det_fin_two,
      Matrix.submatrix_apply, Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
      profileMatrix, Matrix.of_apply, Fin.sum_univ_five, elementaryThree,
      elementaryFour, elementaryFive_apply]
    norm_num [Fin.succAbove, Fin.lt_def, Fin.castSucc, Fin.succ, Fin.last, Fin.val_eq_val]
    rw [hlast]
    ring
  rw [determinant, hnorm, zero_mul, add_zero]

private lemma centerChar_formula (profile : Column) (hprofile : (∑ i, profile i) = 0)
    (hnorm : (∑ i, (profile i)^2) = 0) :
    (centerOperator profile).charpoly = X^4 + C (-2 * elementaryFive profile 4 / 15) * X^2 +
      C ((4 * elementaryFive profile 3 * elementaryFive profile 5 - (elementaryFive profile 4)^2) / 15) := by
  rw [centerChar_eq_matrix profile hprofile]
  apply Polynomial.funext
  intro point
  rw [profileChar_eval profile hprofile hnorm]
  simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C]
  ring

private lemma centerChar_square (profile : Column) (hprofile : (∑ i, profile i) = 0)
    (hnorm : (∑ i, (profile i)^2) = 0) :
    (∃ root : ℂ[X], (centerOperator profile).charpoly = root^2) ↔
      15 * elementaryFive profile 3 * elementaryFive profile 5 = 4 * (elementaryFive profile 4)^2 := by
  let cubic := elementaryFive profile 3
  let quartic := elementaryFive profile 4
  let quintic := elementaryFive profile 5
  have hchar : (centerOperator profile).charpoly =
      X^4 + C (-2 * quartic / 15) * X^2 + C ((4 * cubic * quintic - quartic^2) / 15) :=
    centerChar_formula profile hprofile hnorm
  constructor
  · rintro ⟨root, hsquare⟩
    have hdegree := congrArg Polynomial.natDegree hsquare
    rw [LinearMap.charpoly_natDegree, centerDim, Polynomial.natDegree_pow] at hdegree
    have hrootDegree : root.natDegree = 2 := by omega
    have hshape : root = C (root.coeff 2) * X^2 + C (root.coeff 1) * X + C (root.coeff 0) := by
      conv_lhs => rw [root.as_sum_range_C_mul_X_pow, hrootDegree]
      norm_num [Finset.sum_range_succ]
      ring
    let lead := root.coeff 2
    let middle := root.coeff 1
    let constant := root.coeff 0
    have hsquareShape : root^2 = C (lead^2) * X^4 + C (2 * lead * middle) * X^3 +
        C (middle^2 + 2 * lead * constant) * X^2 + C (2 * middle * constant) * X + C (constant^2) := by
      conv_lhs => rw [hshape]
      apply Polynomial.funext
      intro point
      simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C, lead, middle, constant]
      ring
    rw [hchar, hsquareShape] at hsquare
    have hlead := congrArg (fun poly : ℂ[X] => poly.coeff 4) hsquare
    have hmiddle := congrArg (fun poly : ℂ[X] => poly.coeff 3) hsquare
    have hcross := congrArg (fun poly : ℂ[X] => poly.coeff 2) hsquare
    have hconstant := congrArg (fun poly : ℂ[X] => poly.coeff 0) hsquare
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
      at hlead hmiddle hcross hconstant
    norm_num at hlead hmiddle hcross hconstant
    have hlead' : lead^2 = 1 := hlead.symm
    have hnonzero : lead ≠ 0 := by intro hzero; simp [hzero] at hlead'
    have hmiddle' : middle = 0 := by
      exact hmiddle.resolve_left hnonzero
    rw [hmiddle'] at hcross
    have hmultiply : lead * constant = -quartic / 15 := by linear_combination -hcross / 2
    have hsquareMul := congrArg (fun elem : ℂ => elem^2) hmultiply
    change 15 * cubic * quintic = 4 * quartic^2
    linear_combination (225 / 4 : ℂ) * (hsquareMul - constant^2 * hlead' + hconstant)
  · intro heq
    refine ⟨X^2 - C (quartic / 15), ?_⟩
    rw [hchar]
    apply Polynomial.funext
    intro point
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
    change 15 * cubic * quintic = 4 * quartic^2 at heq
    linear_combination (4 / 225 : ℂ) * heq

private lemma level_center (vector : Center) (profile : Column) (hprofile : (∑ i, profile i) = 0)
    (hnorm : (∑ i, (profile i)^2) = 0) :
    (∀ t : ℂ, let rows : Fin 4 → Fin 5 → ℂ := ![(vector : Column), -(vector : Column), t • profile, -(t • profile)]
      (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4, (1 + rows i (f i))) = 120) ↔
      centerForm vector vector = 0 ∧ centerForm (centerOperator profile vector) vector = 0 := by
  rw [permanent_iff _ _ ((mem_center _).mp vector.property) hprofile hnorm,
    centerForm_apply, centerOperator_form]
  simp only [← pow_two]
  have hsum : (∑ i, (profile i)^2 * (vector : Column) i * (vector : Column) i) =
      ∑ i, ((vector : Column) i)^2 * (profile i)^2 := by
    apply Finset.sum_congr rfl
    intro index _
    ring
  have hdot : (∑ i, profile i * (vector : Column) i) = ∑ i, (vector : Column) i * profile i :=
    Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  rw [hsum, hdot]
  constructor
  · rintro ⟨hfirst, hsecond⟩
    exact ⟨hfirst, by linear_combination hsecond / 3⟩
  · rintro ⟨hfirst, hsecond⟩
    exact ⟨hfirst, by linear_combination 3 * hsecond⟩

private lemma plane_square_of_level (profile : Column) (plane : Submodule ℂ Center)
    (hrank : finrank ℂ plane = 2)
    (hlevel : ∀ vector ∈ plane, centerForm vector vector = 0 ∧
      centerForm (centerOperator profile vector) vector = 0) :
    ∃ root : ℂ[X], (centerOperator profile).charpoly = root^2 := by
  have hiso : plane ≤ centerForm.orthogonal plane := by
    intro right hright left hleft
    have hsum := (hlevel (left + right) (plane.add_mem hleft hright)).1
    simp only [map_add, LinearMap.add_apply, centerForm_symm.eq right left] at hsum
    exact (show centerForm left right = 0 by
      linear_combination (hsum - (hlevel left hleft).1 - (hlevel right hright).1) / 2)
  have hself : centerForm.orthogonal plane = plane := by
    symm
    apply Submodule.eq_of_le_of_finrank_le hiso
    rw [centerForm.finrank_orthogonal centerForm_nondeg, centerDim, hrank]
  have hstable : plane ≤ plane.comap (centerOperator profile) := by
    intro right hright
    change centerOperator profile right ∈ plane
    rw [← hself]
    intro left hleft
    have hsum := (hlevel (left + right) (plane.add_mem hleft hright)).2
    have heq : centerForm (centerOperator profile right) left =
        centerForm (centerOperator profile left) right :=
      (centerForm_symm.eq _ _).trans (centerOperator_adjoint profile left right).symm
    simp only [map_add, LinearMap.add_apply, heq] at hsum
    rw [← centerOperator_adjoint]
    linear_combination (hsum - (hlevel left hleft).2 - (hlevel right hright).2) / 2
  exact square_of_plane centerDim centerForm centerForm_symm centerForm_nondeg
    (centerOperator profile) (centerOperator_adjoint profile) plane hrank hiso hstable

end PEqualNP.Outside.L_gct_300

open PEqualNP.Outside.L_gct_300 Module

theorem PEqualNP.Outside.L_gct_300 : (∀ (y : Fin 5 → ℂ), (∑ i, y i) = 0 → (∑ i, (y i)^2) = 0 →
  let e := fun k : ℕ =>
    ∑ s ∈ (Finset.univ : Finset (Fin 5)).powersetCard k, ∏ i ∈ s, y i
  (∃ K : Submodule ℂ (Fin 5 → ℂ), Module.finrank ℂ K = 2 ∧
    ∀ x ∈ K, (∑ j, x j) = 0 ∧ ∀ t : ℂ,
      let rows : Fin 4 → Fin 5 → ℂ := ![x, -x, t • y, -(t • y)]
      (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4, (1 + rows i (f i))) = 120) ↔
    15 * e 3 * e 5 = 4 * (e 4)^2) := by
  intro profile hprofile hnorm
  change (∃ K : Submodule ℂ Column, finrank ℂ K = 2 ∧
    ∀ vector ∈ K, (∑ i, vector i) = 0 ∧ ∀ t : ℂ,
      let rows : Fin 4 → Column := ![vector, -vector, t • profile, -(t • profile)]
      (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4, (1 + rows i (f i))) = 120) ↔
      15 * elementaryFive profile 3 * elementaryFive profile 5 = 4 * (elementaryFive profile 4)^2
  rw [← centerChar_square profile hprofile hnorm]
  constructor
  · rintro ⟨K, hrank, hK⟩
    have hsub : K ≤ Center := fun vector hvector => (mem_center vector).mpr (hK vector hvector).1
    let plane := K.comap Center.subtype
    have hplaneRank : finrank ℂ plane = 2 :=
      (Submodule.comapSubtypeEquivOfLe hsub).finrank_eq.trans hrank
    exact plane_square_of_level profile plane hplaneRank (fun vector hvector =>
      (level_center vector profile hprofile hnorm).mp (hK vector hvector).2)
  · rintro ⟨root, hsquare⟩
    obtain ⟨plane, hrank, hiso, hstable⟩ := plane_of_square centerDim centerForm centerForm_symm
      centerForm_nondeg (centerOperator profile) (centerOperator_adjoint profile) hsquare
    refine ⟨plane.map Center.subtype, (Submodule.finrank_map_subtype_eq _ _).trans hrank, ?_⟩
    rintro vector ⟨source, hsource, rfl⟩
    refine ⟨(mem_center _).mp source.property, (level_center source profile hprofile hnorm).mpr ?_⟩
    exact ⟨hiso hsource source hsource, hiso hsource (centerOperator profile source) (hstable hsource)⟩
