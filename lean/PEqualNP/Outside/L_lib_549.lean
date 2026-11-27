import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_549_aux

theorem stab {K : Type} [Field K] {E : Type} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    {q : ℕ} (g : Fin q → E →ₗ[K] E) (e : E) (d : ℕ) (hd : Module.finrank K E ≤ d)
    (w : List (Fin q)) :
    w.foldl (fun x a => g a x) e ∈ Submodule.span K
      ((fun u : List (Fin q) => u.foldl (fun x a => g a x) e) '' {u | u.length < d}) := by
  let orb : List (Fin q) → E := fun u => u.foldl (fun x a => g a x) e
  let S : ℕ → Submodule K E := fun k => Submodule.span K (orb '' {u | u.length < k})
  have hmono : Monotone S := by
    intro a b hab
    apply Submodule.span_mono
    apply Set.image_mono
    intro u hu
    exact lt_of_lt_of_le hu hab
  have hstep : ∀ k a, (S k).map (g a) ≤ S (k+1) := by
    intro k a
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨u ++ [a], ?_, ?_⟩
    · have hu' : u.length < k := hu
      show (u ++ [a]).length < k + 1
      simp
      omega
    · simp [orb, List.foldl_append]
  have hex : ∃ k, k ≤ d ∧ S (k+1) ≤ S k := by
    by_contra hcon
    push_neg at hcon
    have hlt : ∀ k, k ≤ d → S k < S (k+1) := fun k hk =>
      lt_of_le_not_ge (hmono (Nat.le_succ k)) (hcon k hk)
    have hfr : ∀ k, k ≤ d + 1 → k ≤ Module.finrank K (S k) := by
      intro k
      induction k with
      | zero => intro _; exact Nat.zero_le _
      | succ k ih =>
        intro hk
        have h1 := ih (by omega)
        have h2 := Submodule.finrank_lt_finrank_of_lt (hlt k (by omega))
        omega
    have h3 := hfr (d+1) le_rfl
    have h4 := Submodule.finrank_le (S (d+1))
    omega
  obtain ⟨k, hkd, hk⟩ := hex
  have hinv : ∀ u, orb u ∈ S k := by
    intro u
    induction u using List.reverseRecOn with
    | nil =>
      apply hk
      apply Submodule.subset_span
      exact ⟨[], by simp, rfl⟩
    | append_singleton u a ih =>
      apply hk
      apply hstep k a
      refine ⟨orb u, ih, ?_⟩
      simp [orb, List.foldl_append]
  exact hmono hkd (hinv w)

theorem pick {K : Type} [Field K] {M : Type*} [AddCommGroup M] [Module K M] (S : Set M)
    [Module.Finite K (Submodule.span K S)] (n : ℕ)
    (hn : Module.finrank K (Submodule.span K S) = n) :
    ∃ f : Fin n → M, (∀ i, f i ∈ S) ∧ LinearIndependent K f := by
  subst hn
  obtain ⟨f, h1, -, h3⟩ := Submodule.exists_fun_fin_finrank_span_eq K S
  exact ⟨f, h1, h3⟩

theorem main {K : Type} [Field K] (q d : ℕ) (s : Fin d → K)
    (A : Fin q → (Fin d → K) →ₗ[K] (Fin d → K)) (f : (Fin d → K) →ₗ[K] K) (r : ℕ)
    (hr : r = Module.finrank K (Submodule.span K (Set.range (fun u : List (Fin q) =>
      fun v : List (Fin q) => f ((u ++ v).foldl (fun x a => A a x) s))))) :
    ∃ U W : Fin r → List (Fin q), (∀ i, (U i).length < d ∧ (W i).length < d) ∧
      (Matrix.of (fun i j : Fin r => f ((U i ++ W j).foldl (fun x a => A a x) s))).det ≠ 0 := by
  classical
  let run : List (Fin q) → (Fin d → K) := fun w => w.foldl (fun x a => A a x) s
  let psi : List (Fin q) → Module.Dual K (Fin d → K) :=
    fun w => w.foldl (fun θ a => (A a).dualMap θ) f
  have hpsi : ∀ w x, psi w x = f (w.reverse.foldl (fun x a => A a x) x) := by
    intro w
    induction w using List.reverseRecOn with
    | nil => intro x; rfl
    | append_singleton w a ih =>
      intro x
      have := ih (A a x)
      simp only [psi, List.foldl_append, List.foldl_cons, List.foldl_nil, List.reverse_append,
        List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
        LinearMap.dualMap_apply] at this ⊢
      exact this
  have hB1 : ∀ w, run w ∈ Submodule.span K (run '' {u | u.length < d}) :=
    fun w => stab A s d (by simp) w
  have hB2 : ∀ w, psi w ∈ Submodule.span K (psi '' {u | u.length < d}) :=
    fun w => stab (fun a => (A a).dualMap) f d (by rw [Subspace.dual_finrank_eq]; simp) w
  let φ : (Fin d → K) →ₗ[K] (List (Fin q) → K) := LinearMap.pi (fun v => psi v.reverse)
  have hrow : ∀ u v, φ (run u) v = f ((u ++ v).foldl (fun x a => A a x) s) := by
    intro u v
    show psi v.reverse (run u) = _
    rw [hpsi, List.reverse_reverse, List.foldl_append]
  have hrange : (fun u : List (Fin q) => fun v : List (Fin q) =>
      f ((u ++ v).foldl (fun x a => A a x) s)) = fun u => φ (run u) := by
    funext u v; exact (hrow u v).symm
  rw [hrange] at hr
  have hR : Submodule.span K (Set.range (fun u => φ (run u))) =
      Submodule.span K ((fun u => φ (run u)) '' {u | u.length < d}) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨u, rfl⟩
      have := Submodule.mem_map_of_mem (f := φ) (hB1 u)
      rw [Submodule.map_span, Set.image_image] at this
      exact this
    · exact Submodule.span_mono (Set.image_subset_range _ _)
  have hfin := List.finite_length_lt (Fin q) d
  haveI : Module.Finite K (Submodule.span K ((fun u => φ (run u)) '' {u | u.length < d})) :=
    FiniteDimensional.span_of_finite K (hfin.image _)
  obtain ⟨ρ, hρS, hρli⟩ := pick (K := K) ((fun u => φ (run u)) '' {u | u.length < d}) r
    (by rw [hr, hR])
  choose U hU hUρ using hρS
  haveI : Fintype ↥{u : List (Fin q) | u.length < d} := hfin.fintype
  let M : Matrix (Fin r) ↥{u : List (Fin q) | u.length < d} K := fun i v => φ (run (U i)) v.1
  have hMli : LinearIndependent K M.row := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    refine Fintype.linearIndependent_iff.mp hρli c ?_
    let y : Fin d → K := ∑ i, c i • run (U i)
    have hφy : φ y = ∑ i, c i • ρ i := by
      simp [y, map_sum, hUρ]
    rw [← hφy]
    have key : Submodule.span K (psi '' {u | u.length < d}) ≤
        LinearMap.ker (Module.Dual.eval K (Fin d → K) y) := by
      rw [Submodule.span_le]
      rintro _ ⟨w, hw, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, Module.Dual.eval_apply]
      have hw' : w.reverse.length < d := by simpa using hw
      have h1 := congrFun hc ⟨w.reverse, hw'⟩
      simp only [Finset.sum_apply, Pi.smul_apply, Matrix.row, M, φ, LinearMap.pi_apply,
        List.reverse_reverse, Pi.zero_apply, smul_eq_mul] at h1
      simp only [y, map_sum, map_smul, smul_eq_mul]
      exact h1
    funext v
    have h2 := key (hB2 v.reverse)
    rw [LinearMap.mem_ker, Module.Dual.eval_apply] at h2
    exact h2
  have hrank : Module.finrank K (Submodule.span K (Set.range M.col)) = r := by
    rw [← Matrix.rank_eq_finrank_span_cols, hMli.rank_matrix, Fintype.card_fin]
  haveI : Module.Finite K (Submodule.span K (Set.range M.col)) :=
    FiniteDimensional.span_of_finite K (Set.finite_range _)
  obtain ⟨c, hcS, hcli⟩ := pick (K := K) (Set.range M.col) r hrank
  choose W hW using hcS
  refine ⟨U, fun j => (W j).1, fun i => ⟨hU i, (W i).2⟩, ?_⟩
  have hN : (Matrix.of (fun i j : Fin r =>
      f ((U i ++ (W j).1).foldl (fun x a => A a x) s))).col = c := by
    funext j i
    rw [← hW j]
    show f ((U i ++ (W j).1).foldl (fun x a => A a x) s) = φ (run (U i)) (W j).1
    rw [hrow]
  have hunit := Matrix.linearIndependent_col_iff_isUnit.mp (hN ▸ hcli)
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero

end PEqualNP.Outside.L_lib_549_aux

theorem PEqualNP.Outside.L_lib_549 : (∀ (K : Type) [Field K] (q d : ℕ),
  let V := Fin d → K
  ∀ (s : V) (A : Fin q → V →ₗ[K] V),
    let run := fun (w : List (Fin q)) => w.foldl (fun x a => A a x) s
    ∀ f : V →ₗ[K] K,
      let val := fun w => f (run w)
      let R := Submodule.span K (Set.range (fun u : List (Fin q) => fun v : List (Fin q) => val (u ++ v)))
      let r := Module.finrank K R
      ∃ U W : Fin r → List (Fin q),
        (∀ i, (U i).length < d ∧ (W i).length < d) ∧
        (Matrix.of (fun i j : Fin r => val (U i ++ W j))).det ≠ 0) := by
  intro K _ q d V s A run f val R r
  exact PEqualNP.Outside.L_lib_549_aux.main q d s A f r rfl
