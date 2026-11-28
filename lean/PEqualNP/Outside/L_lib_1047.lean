import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1047_aux

open scoped Topology

noncomputable def run {X : Type} (q : ℕ → List ℝ → X → ℝ) (t : ℕ) (x : X) : List ℝ :=
  (List.range t).foldl (fun hist k => q k hist x :: hist) []

theorem run_succ_last {X : Type} (q : ℕ → List ℝ → X → ℝ) (t : ℕ) (x : X) :
    run q (t + 1) x = q t (run q t x) x :: run q t x := by
  simp [run, List.range_succ]

theorem run_shift {X : Type} (q : ℕ → List ℝ → X → ℝ) (c : ℝ) (x : X) (hc : q 0 [] x = c) :
    ∀ t, run q (t + 1) x = run (fun k h => q (k + 1) (h ++ [c])) t x ++ [c] := by
  intro t
  induction t with
  | zero => simp [run, hc]
  | succ t ih =>
    rw [run_succ_last, ih, run_succ_last]
    rfl

theorem two_points {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    (U : Set E) (hU : IsOpen U) (hne : U.Nonempty) : ∃ x ∈ U, ∃ y ∈ U, x ≠ y := by
  obtain ⟨p, hp⟩ := hne
  have : (𝓝[≠] p).NeBot := Module.punctured_nhds_neBot ℝ E p
  obtain ⟨y, hy⟩ := (𝓝[≠] p).nonempty_of_mem
    (Filter.inter_mem (mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hp)) self_mem_nhdsWithin)
  exact ⟨p, hp, y, hy.1, fun h => hy.2 h.symm⟩

theorem range_top {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (L : E →L[ℝ] ℝ)
    (hL : L ≠ 0) : L.range = ⊤ := by
  obtain ⟨v, hv⟩ : ∃ v, L v ≠ 0 := by
    by_contra h
    push Not at h
    exact hL (ContinuousLinearMap.ext h)
  rw [LinearMap.range_eq_top]
  intro r
  refine ⟨(r / L v) • v, ?_⟩
  show L ((r / L v) • v) = r
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hv]

theorem level_chart {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (g : E → ℝ) (p : E) (U : Set E) (hU : IsOpen U) (hp : p ∈ U)
    (hg : ContDiffAt ℝ 1 g p) (hne : fderiv ℝ g p ≠ 0) :
    ∃ (ψ : (fderiv ℝ g p).ker → E) (U' : Set (fderiv ℝ g p).ker),
      IsOpen U' ∧ U'.Nonempty ∧ Set.InjOn ψ U' ∧ Set.MapsTo ψ U' U ∧
      ContDiffOn ℝ 1 ψ U' ∧ ∀ y ∈ U', g (ψ y) = g p := by
  have hsd : HasStrictFDerivAt g (fderiv ℝ g p) p := hg.hasStrictFDerivAt_fderiv one_ne_zero
  have hrange : (fderiv ℝ g p).range = ⊤ := range_top _ hne
  have hker : (fderiv ℝ g p).ker.ClosedComplemented :=
    (fderiv ℝ g p).ker_closedComplemented_of_finiteDimensional_range
  let φ := HasStrictFDerivAt.implicitFunctionDataOfComplemented g (fderiv ℝ g p) hsd hrange hker
  let Φ := φ.toOpenPartialHomeomorph
  have hΦapp : ∀ z, Φ z = (g z, Classical.choose hker (z - p)) := fun z => rfl
  have hΦp : Φ p = (g p, 0) := by rw [hΦapp, sub_self, map_zero]
  have hpsrc : p ∈ Φ.source := φ.pt_mem_toOpenPartialHomeomorph_source
  have h0 : (g p, (0 : (fderiv ℝ g p).ker)) ∈ Φ.target := by
    rw [← hΦp]; exact Φ.map_source hpsrc
  let ψ : (fderiv ℝ g p).ker → E := fun y => Φ.symm (g p, y)
  have hψ0 : ψ 0 = p := by
    show Φ.symm (g p, 0) = p
    rw [← hΦp]; exact Φ.left_inv hpsrc
  have hr : ContDiffAt ℝ 1 φ.rightFun φ.pt :=
    ((Classical.choose hker).contDiff.comp (contDiff_id.sub contDiff_const)).contDiffAt
  have hcd0 : ContDiffAt ℝ 1 (Function.uncurry φ.implicitFunction) (φ.prodFun φ.pt) :=
    φ.contDiffAt_implicitFunction hg hr one_ne_zero
  have hcd1 : ContDiffAt ℝ 1 Φ.symm (Φ p) := hcd0
  rw [hΦp] at hcd1
  have hcd : ContDiffAt ℝ 1 ψ 0 :=
    hcd1.comp (0 : (fderiv ℝ g p).ker) (contDiffAt_const.prodMk contDiffAt_id)
  have hev1 : ∀ᶠ y in 𝓝 (0 : (fderiv ℝ g p).ker), ContDiffAt ℝ 1 ψ y :=
    hcd.eventually (by simp)
  have hev2 : ∀ᶠ y in 𝓝 (0 : (fderiv ℝ g p).ker), (g p, y) ∈ Φ.target :=
    (Continuous.prodMk continuous_const continuous_id).continuousAt.eventually
      (Φ.open_target.mem_nhds h0)
  have hev3 : ∀ᶠ y in 𝓝 (0 : (fderiv ℝ g p).ker), ψ y ∈ U :=
    hcd.continuousAt.eventually (hU.mem_nhds (by rw [hψ0]; exact hp))
  obtain ⟨U', hU'sub, hU'open, h0U'⟩ := eventually_nhds_iff.mp (hev1.and (hev2.and hev3))
  refine ⟨ψ, U', hU'open, ⟨0, h0U'⟩, ?_, ?_, ?_, ?_⟩
  · intro y hy y' hy' hyy'
    have h1 := (hU'sub y hy).2.1
    have h2 := (hU'sub y' hy').2.1
    have h3 := Φ.symm.injOn h1 h2 hyy'
    exact (Prod.mk.inj h3).2
  · intro y hy
    exact (hU'sub y hy).2.2
  · intro y hy
    exact (hU'sub y hy).1.contDiffWithinAt
  · intro y hy
    have h1 := (hU'sub y hy).2.1
    have h2 : Φ (ψ y) = (g p, y) := Φ.right_inv h1
    have h3 : (Φ (ψ y)).1 = g (ψ y) := rfl
    rw [← h3, h2]

theorem core : ∀ (t : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (U : Set E), IsOpen U → U.Nonempty → t < Module.finrank ℝ E →
    ∀ (q : ℕ → List ℝ → E → ℝ), (∀ k h, ContDiffOn ℝ 1 (q k h) U) →
    ∃ x ∈ U, ∃ y ∈ U, x ≠ y ∧ run q t x = run q t y := by
  intro t
  induction t with
  | zero =>
    intro E _ _ _ U hU hne hd q hq
    have : Nontrivial E := Module.finrank_pos_iff.mp hd
    obtain ⟨x, hx, y, hy, hxy⟩ := two_points U hU hne
    exact ⟨x, hx, y, hy, hxy, rfl⟩
  | succ t ih =>
    intro E _ _ _ U hU hne hd q hq
    by_cases hconst : ∀ p ∈ U, fderiv ℝ (q 0 []) p = 0
    · obtain ⟨p, hp⟩ := hne
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU p hp
      have hc : ∀ x ∈ Metric.ball p r, q 0 [] x = q 0 [] p := fun x hx =>
        Metric.isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball p r).isPreconnected
          (((hq 0 []).mono hball).differentiableOn one_ne_zero)
          (fun z hz => hconst z (hball hz)) hx (Metric.mem_ball_self hr)
      obtain ⟨x, hx, y, hy, hxy, hrun⟩ := ih E (Metric.ball p r) Metric.isOpen_ball
        ⟨p, Metric.mem_ball_self hr⟩ (by omega)
        (fun k h => q (k + 1) (h ++ [q 0 [] p])) (fun k h => (hq _ _).mono hball)
      exact ⟨x, hball hx, y, hball hy, hxy, by
        rw [run_shift q _ x (hc x hx), run_shift q _ y (hc y hy), hrun]⟩
    · push Not at hconst
      obtain ⟨p, hp, hne'⟩ := hconst
      obtain ⟨ψ, U', hU', hne'', hinj, hmaps, hψ, hc⟩ :=
        level_chart (q 0 []) p U hU hp ((hq 0 []).contDiffAt (hU.mem_nhds hp)) hne'
      have hfr : Module.finrank ℝ (fderiv ℝ (q 0 []) p).ker + 1 = Module.finrank ℝ E := by
        have h1 := LinearMap.finrank_range_add_finrank_ker
          (fderiv ℝ (q 0 []) p : E →ₗ[ℝ] ℝ)
        rw [range_top _ hne', finrank_top, Module.finrank_self] at h1
        omega
      obtain ⟨x, hx, y, hy, hxy, hrun⟩ := ih (fderiv ℝ (q 0 []) p).ker U' hU' hne'' (by omega)
        (fun k h => fun z => q (k + 1) (h ++ [q 0 [] p]) (ψ z))
        (fun k h => (hq _ _).comp hψ hmaps)
      refine ⟨ψ x, hmaps hx, ψ y, hmaps hy, fun h => hxy (hinj hx hy h), ?_⟩
      rw [run_shift q _ (ψ x) (hc x hx), run_shift q _ (ψ y) (hc y hy)]
      have e : ∀ z, run (fun k h => q (k + 1) (h ++ [q 0 [] p])) t (ψ z) =
          run (fun k h z => q (k + 1) (h ++ [q 0 [] p]) (ψ z)) t z := fun z => rfl
      rw [e, e, hrun]

theorem main (n : ℕ) (H : Fin n → Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (t : ℕ)
    (hA : ∀ i j, (H i j = true → 0 < A i j) ∧ (H i j = false → A i j = 0)) (hε : 0 < ε)
    (ht : t < Module.finrank ℝ (Submodule.span ℝ {v : Fin n × Fin n → ℝ |
      ∃ π : Equiv.Perm (Fin n), (∀ j, H (π j) j = true) ∧
        v = fun e => if π e.2 = e.1 then (1 : ℝ) else 0}))
    (ask : ℕ → List ℝ → Fin n × Fin n → Bool) :
    ∃ B C : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, (H i j = true → 0 < B i j) ∧ (H i j = false → B i j = 0)) ∧
      (∀ i j, (H i j = true → 0 < C i j) ∧ (H i j = false → C i j = 0)) ∧
      (∀ i j, |B i j - A i j| < ε ∧ |C i j - A i j| < ε) ∧
      (List.range t).foldl (fun hist k =>
        (Matrix.det (fun i j => if ask k hist (i, j) then -B i j else B i j :
          Matrix (Fin n) (Fin n) ℝ)) :: hist) ([] : List ℝ) =
      (List.range t).foldl (fun hist k =>
        (Matrix.det (fun i j => if ask k hist (i, j) then -C i j else C i j :
          Matrix (Fin n) (Fin n) ℝ)) :: hist) ([] : List ℝ) ∧
      ∃ π : Equiv.Perm (Fin n), ∏ j, B (π j) j ≠ ∏ j, C (π j) j := by
  set V := Submodule.span ℝ {v : Fin n × Fin n → ℝ |
      ∃ π : Equiv.Perm (Fin n), (∀ j, H (π j) j = true) ∧
        v = fun e => if π e.2 = e.1 then (1 : ℝ) else 0} with hV
  let Mx : V → Fin n → Fin n → ℝ :=
    fun x i j => A i j * Real.exp ((x : Fin n × Fin n → ℝ) (i, j))
  have hentry : ∀ i j, ContDiff ℝ 1 (fun x : V => Mx x i j) := by
    intro i j
    have h1 : ContDiff ℝ 1 (fun x : V => (x : Fin n × Fin n → ℝ) (i, j)) :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n × Fin n => ℝ) (i, j)).comp
        V.subtypeL).contDiff
    exact contDiff_const.mul (Real.contDiff_exp.comp h1)
  let U : Set V := {x | ∀ i j, |Mx x i j - A i j| < ε}
  have hUo : IsOpen U := by
    have hU : U = ⋂ i, ⋂ j, {x : V | |Mx x i j - A i j| < ε} := by
      ext x
      simp [U]
    rw [hU]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_lt ((hentry i j).continuous.sub continuous_const).abs continuous_const
  have h0 : (0 : V) ∈ U := by
    intro i j
    simp [Mx, hε]
  let q : ℕ → List ℝ → V → ℝ := fun k h x =>
    Matrix.det (fun i j => if ask k h (i, j) then -Mx x i j else Mx x i j :
      Matrix (Fin n) (Fin n) ℝ)
  have hq : ∀ k h, ContDiff ℝ 1 (q k h) := by
    intro k h
    have hdet : q k h = fun x : V => ∑ σ : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∏ i, (if ask k h (σ i, i) = true then -Mx x (σ i) i else Mx x (σ i) i) := by
      funext x
      exact Matrix.det_apply' _
    rw [hdet]
    refine ContDiff.sum fun σ _ => ?_
    refine contDiff_const.mul ?_
    refine contDiff_prod fun i _ => ?_
    have hsplit : ∀ (b : Bool) (i j : Fin n),
        ContDiff ℝ 1 (fun x : V => if b = true then -Mx x i j else Mx x i j) := by
      intro b i j
      cases b
      · simpa using hentry i j
      · simpa using (hentry i j).neg
    exact hsplit _ _ _
  obtain ⟨x, hx, y, hy, hxy, hrun⟩ :=
    core t V U hUo ⟨0, h0⟩ ht q (fun k h => (hq k h).contDiffOn)
  have hfit : ∀ z : V, ∀ i j, (H i j = true → 0 < Mx z i j) ∧ (H i j = false → Mx z i j = 0) := by
    intro z i j
    refine ⟨fun h => mul_pos ((hA i j).1 h) (Real.exp_pos _), fun h => ?_⟩
    show A i j * _ = 0
    rw [(hA i j).2 h, zero_mul]
  have hprod : ∀ (z : V) (π : Equiv.Perm (Fin n)), ∏ j, Mx z (π j) j =
      (∏ j, A (π j) j) * Real.exp (∑ j, (z : Fin n × Fin n → ℝ) (π j, j)) := by
    intro z π
    rw [Real.exp_sum, ← Finset.prod_mul_distrib]
  refine ⟨Mx x, Mx y, hfit x, hfit y, fun i j => ⟨hx i j, hy i j⟩, hrun, ?_⟩
  by_contra hall
  push Not at hall
  apply hxy
  have hsum : ∀ π : Equiv.Perm (Fin n), (∀ j, H (π j) j = true) →
      ∑ j, ((x : Fin n × Fin n → ℝ) (π j, j) - (y : Fin n × Fin n → ℝ) (π j, j)) = 0 := by
    intro π hπ
    have h1 := hall π
    rw [hprod, hprod] at h1
    have hpos : 0 < ∏ j, A (π j) j := Finset.prod_pos fun j _ => (hA (π j) j).1 (hπ j)
    have h2 := Real.exp_injective (mul_left_cancel₀ hpos.ne' h1)
    rw [Finset.sum_sub_distrib, h2, sub_self]
  have horth : ∀ v ∈ V, ∑ e, ((x : Fin n × Fin n → ℝ) e - (y : Fin n × Fin n → ℝ) e) * v e = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨π, hπ, rfl⟩ := hv
      have h5 : ∑ e : Fin n × Fin n,
          ((x : Fin n × Fin n → ℝ) e - (y : Fin n × Fin n → ℝ) e) *
            (if π e.2 = e.1 then (1 : ℝ) else 0) =
          ∑ j, ((x : Fin n × Fin n → ℝ) (π j, j) - (y : Fin n × Fin n → ℝ) (π j, j)) := by
        rw [Fintype.sum_prod_type, Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp
      exact h5.trans (hsum π hπ)
    | zero => simp
    | add u v _ _ hu hv =>
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hu, hv, add_zero]
    | smul a v _ hv =>
      have h3 : ∀ e, ((x : Fin n × Fin n → ℝ) e - (y : Fin n × Fin n → ℝ) e) * (a • v) e =
          a * (((x : Fin n × Fin n → ℝ) e - (y : Fin n × Fin n → ℝ) e) * v e) := by
        intro e
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      simp only [h3, ← Finset.mul_sum, hv, mul_zero]
  have hz := horth _ (V.sub_mem x.2 y.2)
  have hz' : ∀ e, (x : Fin n × Fin n → ℝ) e - (y : Fin n × Fin n → ℝ) e = 0 := by
    intro e
    have h4 := (Finset.sum_eq_zero_iff_of_nonneg (fun e _ => mul_self_nonneg _)).mp hz e
      (Finset.mem_univ e)
    exact mul_self_eq_zero.mp h4
  exact Subtype.ext (funext fun e => sub_eq_zero.mp (hz' e))

end PEqualNP.Outside.L_lib_1047_aux

theorem PEqualNP.Outside.L_lib_1047 : (∀ (n : ℕ) (H : Fin n → Fin n → Bool),
  let I := Fin n
  let E := I × I
  let S := E → Bool
  let vec := fun (π : Equiv.Perm I) (e : E) => if π e.2 = e.1 then (1 : ℝ) else 0
  let V := Submodule.span ℝ {v : E → ℝ | ∃ π : Equiv.Perm I, (∀ j, H (π j) j = true) ∧ v = vec π}
  let w := fun (M : Matrix I I ℝ) (π : Equiv.Perm I) => ∏ j : I, M (π j) j
  let fits := fun M : Matrix I I ℝ =>
    ∀ i j, (H i j = true → 0 < M i j) ∧ (H i j = false → M i j = 0)
  ∀ (A : Matrix I I ℝ) (ε : ℝ) (t : ℕ), fits A → 0 < ε → t < Module.finrank ℝ V →
    ∀ ask : ℕ → List ℝ → S,
      let run := fun M : Matrix I I ℝ => (List.range t).foldl (fun hist k =>
        (Matrix.det (fun i j => if ask k hist (i,j) then -M i j else M i j : Matrix I I ℝ)) :: hist) ([] : List ℝ)
      ∃ B C : Matrix I I ℝ, fits B ∧ fits C ∧
        (∀ i j, |B i j - A i j| < ε ∧ |C i j - A i j| < ε) ∧ run B = run C ∧
        ∃ π : Equiv.Perm I, w B π ≠ w C π) := by
  intro n H I E S vec V w fits A ε t hA hε ht ask run
  exact PEqualNP.Outside.L_lib_1047_aux.main n H A ε t hA hε ht ask
