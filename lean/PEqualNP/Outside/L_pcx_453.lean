import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_453

theorem z2 (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c; decide

theorem lin_fwd (k m : ℕ) (α : Fin m → ZMod 2) (β : Fin m → Fin k → ZMod 2)
    (u : Fin k → ZMod 2) (hu : ∀ i, α i = ∑ j, u j * β i j) (S : Finset (Fin m)) :
    (∑ i ∈ S, α i) * ∏ j, (1 + ∑ i ∈ S, β i j) = 0 := by
  by_cases hz : ∀ j, ∑ i ∈ S, β i j = 0
  · have : ∑ i ∈ S, α i = 0 := by
      calc ∑ i ∈ S, α i = ∑ i ∈ S, ∑ j, u j * β i j := Finset.sum_congr rfl (fun i _ => hu i)
        _ = ∑ j, ∑ i ∈ S, u j * β i j := Finset.sum_comm
        _ = ∑ j, u j * ∑ i ∈ S, β i j := by simp only [Finset.mul_sum]
        _ = 0 := by simp [hz]
    rw [this, zero_mul]
  · obtain ⟨j, hj⟩ := not_forall.1 hz
    have h1 : ∑ i ∈ S, β i j = 1 := (z2 _).resolve_left hj
    have : ∏ j, (1 + ∑ i ∈ S, β i j) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      rw [h1]; decide
    rw [this, mul_zero]

theorem shrink (k m : ℕ) (v : Fin m → (Fin k → ZMod 2) × ZMod 2)
    (e : (Fin k → ZMod 2) × ZMod 2) (he : e ∈ Submodule.span (ZMod 2) (Set.range v)) :
    ∃ S : Finset (Fin m), S.card ≤ k + 1 ∧ ∑ i ∈ S, v i = e := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).1 he
  have hne : (Finset.univ.filter (fun S : Finset (Fin m) => ∑ i ∈ S, v i = e)).Nonempty := by
    refine ⟨Finset.univ.filter (fun i => c i ≠ 0), ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hc, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rcases z2 (c i) with h | h <;> simp [h]
  obtain ⟨S, hS, hmin⟩ := Finset.exists_min_image _ Finset.card hne
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS hmin
  refine ⟨S, ?_, hS⟩
  by_contra hcard
  have hnli : ¬ LinearIndependent (ZMod 2) (fun i : S => v i) := by
    intro hli
    have := hli.fintype_card_le_finrank
    simp at this
    omega
  obtain ⟨g, hg, i0, hi0⟩ := Fintype.not_linearIndependent_iff.1 hnli
  let g' : Fin m → ZMod 2 := fun i => if h : i ∈ S then g ⟨i, h⟩ else 0
  have hg' : ∑ i ∈ S, g' i • v i = 0 := by
    rw [← hg, ← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [g']
  let T := S.filter (fun i => g' i ≠ 0)
  have hT : ∑ i ∈ T, v i = 0 := by
    rw [← hg', Finset.sum_filter]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rcases z2 (g' i) with h | h <;> simp [h]
  have hTS : T ⊆ S := Finset.filter_subset _ _
  have hTne : T.Nonempty := by
    refine ⟨i0.1, ?_⟩
    simp only [T, Finset.mem_filter]
    refine ⟨i0.2, ?_⟩
    simpa [g'] using hi0
  have hsum : ∑ i ∈ S \ T, v i = e := by
    have := Finset.sum_sdiff (f := v) hTS
    rw [hT, add_zero] at this
    rw [this, hS]
  have h1 := hmin (S \ T) hsum
  have h2 := Finset.card_lt_card (Finset.sdiff_ssubset hTS hTne)
  omega

theorem lin_back (k m : ℕ) (α : Fin m → ZMod 2) (β : Fin m → Fin k → ZMod 2)
    (h : ∀ S : Finset (Fin m), S.card ≤ k + 1 →
      (∑ i ∈ S, α i) * ∏ j, (1 + ∑ i ∈ S, β i j) = 0) :
    ∃ u : Fin k → ZMod 2, ∀ i, α i = ∑ j, u j * β i j := by
  classical
  let v : Fin m → (Fin k → ZMod 2) × ZMod 2 := fun i => (β i, α i)
  let e : (Fin k → ZMod 2) × ZMod 2 := (0, 1)
  by_cases he : e ∈ Submodule.span (ZMod 2) (Set.range v)
  · exfalso
    obtain ⟨S, hc, hS⟩ := shrink k m v e he
    have h1 : ∑ i ∈ S, α i = 1 := by
      have := congrArg Prod.snd hS
      simpa [v, e, Prod.snd_sum] using this
    have h2 : ∀ j, ∑ i ∈ S, β i j = 0 := by
      intro j
      have := congrFun (congrArg Prod.fst hS) j
      simpa [v, e, Prod.fst_sum, Finset.sum_apply] using this
    have := h S hc
    simp [h1, h2] at this
  · obtain ⟨φ, hφ, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem he inferInstance
    have hφe : φ e = 1 := (z2 _).resolve_left hφ
    have hv : ∀ i, φ (v i) = 0 := by
      intro i
      have : φ (v i) ∈ (Submodule.span (ZMod 2) (Set.range v)).map φ :=
        Submodule.mem_map_of_mem (Submodule.subset_span ⟨i, rfl⟩)
      rw [hmap] at this
      exact (Submodule.mem_bot (ZMod 2)).1 this
    let ψ : (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2 := φ.comp (LinearMap.inl _ _ _)
    refine ⟨fun j => ψ (fun j' => if j = j' then 1 else 0), fun i => ?_⟩
    have hdec : v i = (β i, 0) + α i • e := by
      simp [v, e]
    have h3 := hv i
    rw [hdec, map_add, map_smul, hφe] at h3
    have h4 : φ (β i, 0) = ψ (β i) := rfl
    rw [h4, LinearMap.pi_apply_eq_sum_univ ψ (β i)] at h3
    simp only [smul_eq_mul, mul_one] at h3
    have h5 : α i = ∑ j, β i j * ψ (fun j' => if j = j' then 1 else 0) := by
      have : ∀ a b : ZMod 2, a + b = 0 → b = a := by decide
      exact this _ _ h3
    rw [h5]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

theorem deg_test (n m k p : ℕ) (q : Fin k → ℕ) (a : Fin m → MvPolynomial (Fin n) (ZMod 2))
    (b : Fin m → Fin k → MvPolynomial (Fin n) (ZMod 2))
    (ha : ∀ i, (a i).totalDegree ≤ p) (hb : ∀ i j, (b i j).totalDegree ≤ q j)
    (S : Finset (Fin m)) :
    ((∑ i ∈ S, a i) * ∏ j, (1 + ∑ i ∈ S, b i j)).totalDegree ≤ p + ∑ j, q j := by
  refine (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add ?_ ?_)
  · exact (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le (fun i _ => ha i))
  · refine (MvPolynomial.totalDegree_finsetProd _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
    refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
    · simp
    · exact (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le (fun i _ => hb i j))

theorem cube_sum (n : ℕ) (f : MvPolynomial (Fin n) (ZMod 2)) (hf : f.totalDegree < n) :
    ∑ x : Fin n → ZMod 2, MvPolynomial.eval x f = 0 := by
  classical
  simp only [MvPolynomial.eval_eq']
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun d hd => ?_)
  rw [← Finset.mul_sum]
  have hprod : ∑ x : Fin n → ZMod 2, ∏ i, x i ^ d i = ∏ i, ∑ c : ZMod 2, c ^ d i := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  have hex : ∃ i, d i = 0 := by
    by_contra hno
    have hpos : ∀ i, 1 ≤ d i := fun i => Nat.one_le_iff_ne_zero.2 (fun h => hno ⟨i, h⟩)
    have h1 := MvPolynomial.le_totalDegree hd
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at h1
    have h2 : ∑ _i : Fin n, 1 ≤ ∑ i, d i := Finset.sum_le_sum (fun i _ => hpos i)
    simp at h2
    omega
  obtain ⟨i, hi⟩ := hex
  rw [hprod, Finset.prod_eq_zero (Finset.mem_univ i), mul_zero]
  rw [hi]
  decide

def E (k p : ℕ) (q : Fin k → ℕ) : Fin p ⊕ ((j : Fin k) × Fin (q j)) ≃ Fin (p + ∑ j, q j) :=
  (Equiv.sumCongr (Equiv.refl _) finSigmaFinEquiv).trans finSumFinEquiv

noncomputable def sa (k p : ℕ) (q : Fin k → ℕ) : MvPolynomial (Fin (p + ∑ j, q j)) (ZMod 2) :=
  ∏ t : Fin p, MvPolynomial.X (E k p q (Sum.inl t))

noncomputable def sb (k p : ℕ) (q : Fin k → ℕ) (j : Fin k) :
    MvPolynomial (Fin (p + ∑ j, q j)) (ZMod 2) :=
  1 + ∏ t : Fin (q j), MvPolynomial.X (E k p q (Sum.inr ⟨j, t⟩))

theorem sa_deg (k p : ℕ) (q : Fin k → ℕ) : (sa k p q).totalDegree ≤ p := by
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  simp

theorem sb_deg (k p : ℕ) (q : Fin k → ℕ) (j : Fin k) : (sb k p q j).totalDegree ≤ q j := by
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le (by simp) ?_)
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  simp

theorem feas (k p : ℕ) (q : Fin k → ℕ) (x : Fin (p + ∑ j, q j) → ZMod 2) :
    (∃ u : Fin k → ZMod 2, MvPolynomial.eval x (sa k p q) =
      ∑ j, u j * MvPolynomial.eval x (sb k p q j)) ↔ ∃ i, x i = 0 := by
  classical
  constructor
  · rintro ⟨u, hu⟩
    by_contra hno
    have h1 : ∀ i, x i = 1 := fun i => (z2 _).resolve_left (fun h => hno ⟨i, h⟩)
    have hb : ∀ j, MvPolynomial.eval x (sb k p q j) = 0 := by
      intro j
      simp only [sb, map_add, map_one, map_prod, MvPolynomial.eval_X, h1, Finset.prod_const_one]
      decide
    simp [sa, h1, hb] at hu
  · rintro ⟨i, hi⟩
    obtain ⟨s, rfl⟩ := (E k p q).surjective i
    rcases s with t | ⟨j, t⟩
    · refine ⟨0, ?_⟩
      have : MvPolynomial.eval x (sa k p q) = 0 := by
        simp only [sa, map_prod, MvPolynomial.eval_X]
        exact Finset.prod_eq_zero (Finset.mem_univ t) hi
      simp [this]
    · have hb : MvPolynomial.eval x (sb k p q j) = 1 := by
        simp only [sb, map_add, map_one, map_prod, MvPolynomial.eval_X]
        rw [Finset.prod_eq_zero (Finset.mem_univ t) hi, add_zero]
      refine ⟨Pi.single j (MvPolynomial.eval x (sa k p q)), ?_⟩
      refine Eq.trans ?_ (Finset.sum_eq_single j ?_ ?_).symm
      · simp [hb]
      · intro j' _ hj'
        simp [Pi.single_eq_of_ne hj']
      · intro h; exact absurd (Finset.mem_univ j) h

theorem sharp (n : ℕ) (G : Finset (MvPolynomial (Fin n) (ZMod 2)))
    (hG : ∀ x : Fin n → ZMod 2, (∃ i, x i = 0) ↔ ∀ g ∈ G, MvPolynomial.eval x g = 0) :
    ∃ g ∈ G, n ≤ g.totalDegree := by
  classical
  have h1 : ¬ ∀ g ∈ G, MvPolynomial.eval (fun _ => (1 : ZMod 2)) g = 0 := by
    intro h
    obtain ⟨i, hi⟩ := (hG _).2 h
    exact one_ne_zero hi
  simp only [not_forall] at h1
  obtain ⟨g, hg, hg1⟩ := h1
  refine ⟨g, hg, ?_⟩
  by_contra hlt
  have hs := cube_sum n g (by omega)
  rw [Finset.sum_eq_single (fun _ => (1 : ZMod 2))] at hs
  · exact hg1 hs
  · intro x _ hx
    have : ∃ i, x i = 0 := by
      by_contra hno
      apply hx
      funext i
      exact (z2 _).resolve_left (fun h => hno ⟨i, h⟩)
    exact (hG x).1 this g hg
  · intro h; exact absurd (Finset.mem_univ _) h

end PEqualNP.Outside.L_pcx_453

theorem PEqualNP.Outside.L_pcx_453 : (∀ (k p : ℕ) (q : Fin k → ℕ),
  let K := ZMod 2
  let bound := p + ∑ j, q j
  (∀ n m : ℕ,
    let P := MvPolynomial (Fin n) K
    ∀ (a : Fin m → P) (b : Fin m → Fin k → P),
      (∀ i, (a i).totalDegree ≤ p) → (∀ i j, (b i j).totalDegree ≤ q j) →
      let test := fun (S : Finset (Fin m)) =>
        (∑ i ∈ S, a i) * ∏ j, (1 + ∑ i ∈ S, b i j)
      (∀ S, (test S).totalDegree ≤ bound) ∧
      ∀ x : Fin n → K,
        (∃ u : Fin k → K, ∀ i, MvPolynomial.eval x (a i) =
          ∑ j, u j * MvPolynomial.eval x (b i j)) ↔
        ∀ S : Finset (Fin m), S.card ≤ k+1 → MvPolynomial.eval x (test S) = 0) ∧
  (let P := MvPolynomial (Fin bound) K
   ∃ (a : P) (b : Fin k → P),
    a.totalDegree ≤ p ∧ (∀ j, (b j).totalDegree ≤ q j) ∧
    (∀ x : Fin bound → K,
      (∃ u : Fin k → K, MvPolynomial.eval x a = ∑ j, u j * MvPolynomial.eval x (b j)) ↔
      ∃ i, x i = 0) ∧
    ∀ G : Finset P, (∀ x : Fin bound → K,
      (∃ u : Fin k → K, MvPolynomial.eval x a = ∑ j, u j * MvPolynomial.eval x (b j)) ↔
      ∀ g ∈ G, MvPolynomial.eval x g = 0) →
      ∃ g ∈ G, bound ≤ g.totalDegree)) := by
  intro k p q K bound
  refine ⟨?_, ?_⟩
  · intro n m P a b ha hb test
    refine ⟨fun S => PEqualNP.Outside.L_pcx_453.deg_test n m k p q a b ha hb S, fun x => ?_⟩
    constructor
    · rintro ⟨u, hu⟩ S _
      have := PEqualNP.Outside.L_pcx_453.lin_fwd k m (fun i => MvPolynomial.eval x (a i))
        (fun i j => MvPolynomial.eval x (b i j)) u hu S
      simpa [test, map_sum, map_prod] using this
    · intro h
      refine PEqualNP.Outside.L_pcx_453.lin_back k m (fun i => MvPolynomial.eval x (a i))
        (fun i j => MvPolynomial.eval x (b i j)) (fun S hS => ?_)
      have := h S hS
      simpa [test, map_sum, map_prod] using this
  · intro P
    refine ⟨PEqualNP.Outside.L_pcx_453.sa k p q, PEqualNP.Outside.L_pcx_453.sb k p q,
      PEqualNP.Outside.L_pcx_453.sa_deg k p q, PEqualNP.Outside.L_pcx_453.sb_deg k p q,
      PEqualNP.Outside.L_pcx_453.feas k p q, fun G hG => ?_⟩
    exact PEqualNP.Outside.L_pcx_453.sharp _ G
      (fun x => (PEqualNP.Outside.L_pcx_453.feas k p q x).symm.trans (hG x))
