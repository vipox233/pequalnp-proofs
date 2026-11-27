import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_785_aux

private lemma card_tri (r : ℕ) :
    2 * Fintype.card { p : Fin r × Fin r // p.1 ≤ p.2 } = r * (r + 1) := by
  let A : Finset (Fin r × Fin r) := Finset.univ.filter (fun p => p.1 ≤ p.2)
  let B : Finset (Fin r × Fin r) := Finset.univ.filter (fun p => p.2 ≤ p.1)
  have hcardA : Fintype.card { p : Fin r × Fin r // p.1 ≤ p.2 } = A.card := by
    rw [Fintype.card_subtype]
  have hAB : A.card = B.card := by
    apply Finset.card_bij (fun p _ => (p.2, p.1))
    · intro p hp
      simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact hp
    · intro p1 _ p2 _ h
      exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
    · intro q hq
      refine ⟨(q.2, q.1), ?_, rfl⟩
      simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      exact hq
  have hunion : A ∪ B = Finset.univ := by
    ext p
    simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact le_total p.1 p.2
  have hinter : (A ∩ B).card = r := by
    have hbij : (A ∩ B).card = (Finset.univ : Finset (Fin r)).card := by
      apply Finset.card_bij (fun p _ => p.1)
      · intro _ _; exact Finset.mem_univ _
      · intro p1 hp1 p2 hp2 h
        simp only [A, B, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
        have heq1 : p1.1 = p1.2 := le_antisymm hp1.1 hp1.2
        have heq2 : p2.1 = p2.2 := le_antisymm hp2.1 hp2.2
        exact Prod.ext h (heq1.symm.trans (h.trans heq2))
      · intro i _
        refine ⟨(i, i), ?_, rfl⟩
        simp only [A, B, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨le_rfl, le_rfl⟩
    rw [hbij, Finset.card_univ, Fintype.card_fin]
  have hsum := Finset.card_union_add_card_inter A B
  rw [hunion, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, hinter, ← hAB] at hsum
  rw [hcardA]
  linarith

end PEqualNP.Outside.L_lib_785_aux

open PEqualNP.Outside.L_lib_785_aux

theorem PEqualNP.Outside.L_lib_785 :
    (let F := ZMod 2
∀ (K : Type) [Field K] [Algebra F K] [FiniteDimensional F K]
    (g : ℕ) (D : Fin g → (K →ₗ[F] K)),
  let r := ∑ i, Module.finrank F (LinearMap.range (D i))
  ∃ V : Submodule F K,
    2 * Module.finrank F K ≤ 2 * Module.finrank F V + r*(r+1) ∧
    ∀ w ∈ V, ∀ (S : Finset (Fin g)) (x : K),
      x = w * ∑ i ∈ S, D i x → x = 0) := by
  dsimp only
  intro K _ _ _ g D
  let F := ZMod 2
  let r : ℕ := ∑ i : Fin g, Module.finrank F (LinearMap.range (D i))
  let b : (i : Fin g) → Module.Basis (Fin (Module.finrank F (LinearMap.range (D i)))) F (LinearMap.range (D i)) :=
    fun i => Module.finBasis F (LinearMap.range (D i))
  let u : (i : Fin g) → Fin (Module.finrank F (LinearMap.range (D i))) → K :=
    fun i k => (b i k).val
  let f : (i : Fin g) → Fin (Module.finrank F (LinearMap.range (D i))) → (K →ₗ[F] F) :=
    fun i k =>
      { toFun := fun x => (b i).repr ⟨D i x, LinearMap.mem_range_self (D i) x⟩ k
        map_add' := fun x y => by
          have h : (⟨D i (x + y), LinearMap.mem_range_self (D i) (x + y)⟩ : LinearMap.range (D i)) =
              ⟨D i x, LinearMap.mem_range_self (D i) x⟩ + ⟨D i y, LinearMap.mem_range_self (D i) y⟩ := by
            ext; exact map_add (D i) x y
          rw [h, map_add, Finsupp.add_apply]
        map_smul' := fun c x => by
          have h : (⟨D i (c • x), LinearMap.mem_range_self (D i) (c • x)⟩ : LinearMap.range (D i)) =
              c • ⟨D i x, LinearMap.mem_range_self (D i) x⟩ := by
            ext; exact map_smul (D i) c x
          rw [h, map_smul, Finsupp.smul_apply, RingHom.id_apply] }
  have hD_decomp : ∀ (i : Fin g) (x : K),
      D i x = ∑ k : Fin (Module.finrank F (LinearMap.range (D i))), (f i k x) • (u i k) := by
    intro i x
    have hrepr := (b i).sum_repr ⟨D i x, LinearMap.mem_range_self (D i) x⟩
    have hval := congrArg (LinearMap.range (D i)).subtype hrepr
    simpa only [map_sum, map_smul, Submodule.coe_subtype, f, u,
      LinearMap.coe_mk, AddHom.coe_mk] using hval.symm
  let Idx := Σ i : Fin g, Fin (Module.finrank F (LinearMap.range (D i)))
  have hcardIdx : Fintype.card Idx = r := by
    simp only [Idx, Fintype.card_sigma, Fintype.card_fin, r]
  let e : Idx ≃ Fin r := Fintype.equivFinOfCardEq hcardIdx
  let U : Fin r → K := fun a => u (e.symm a).1 (e.symm a).2
  let Φ : Fin r → (K →ₗ[F] F) := fun a => f (e.symm a).1 (e.symm a).2
  let grp : Fin r → Fin g := fun a => (e.symm a).1
  let Tri := { p : Fin r × Fin r // p.1 ≤ p.2 }
  let Ψ : K →ₗ[F] (Tri → F) :=
    { toFun := fun w p => Φ p.1.1 (w * U p.1.2)
      map_add' := fun w1 w2 => by
        funext p
        simp only [add_mul, map_add, Pi.add_apply]
      map_smul' := fun c w => by
        funext p
        simp only [smul_mul_assoc, map_smul, RingHom.id_apply, Pi.smul_apply] }
  refine ⟨LinearMap.ker Ψ, ?_, ?_⟩
  · have hrk := LinearMap.finrank_range_add_finrank_ker Ψ
    have hle : Module.finrank F (LinearMap.range Ψ) ≤ Module.finrank F (Tri → F) :=
      Submodule.finrank_le (LinearMap.range Ψ)
    have hpi : Module.finrank F (Tri → F) = Fintype.card Tri :=
      Module.finrank_pi F
    have htri : 2 * Fintype.card Tri = r * (r + 1) := card_tri r
    change 2 * Module.finrank F K ≤ 2 * Module.finrank F (LinearMap.ker Ψ) + r * (r + 1)
    linarith
  · intro w hw S x hx
    have hw0 : ∀ a b : Fin r, a ≤ b → Φ a (w * U b) = 0 := by
      intro a b hab
      have hPsi : Ψ w = 0 := LinearMap.mem_ker.mp hw
      exact congrFun hPsi ⟨(a, b), hab⟩
    let J : Finset (Fin r) := Finset.univ.filter (fun a => grp a ∈ S)
    have hsum_eq : ∑ i ∈ S, D i x = ∑ a ∈ J, (Φ a x) • (U a) := by
      calc ∑ i ∈ S, D i x
          = ∑ i ∈ S, ∑ k : Fin (Module.finrank F (LinearMap.range (D i))), (f i k x) • (u i k) := by
              refine Finset.sum_congr rfl (fun i _ => hD_decomp i x)
        _ = ∑ p ∈ S.sigma (fun i => (Finset.univ : Finset (Fin (Module.finrank F (LinearMap.range (D i)))))),
              (f p.1 p.2 x) • (u p.1 p.2) := by
              rw [Finset.sum_sigma]
        _ = ∑ a ∈ J, (Φ a x) • (U a) := by
              apply Finset.sum_bij (fun p _ => e p)
              · intro p hp
                rw [Finset.mem_sigma] at hp
                simp only [J, grp, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]
                exact hp.1
              · intro p1 _ p2 _ h
                exact e.injective h
              · intro a ha
                simp only [J, grp, Finset.mem_filter, Finset.mem_univ, true_and] at ha
                refine ⟨e.symm a, ?_, e.apply_symm_apply a⟩
                rw [Finset.mem_sigma]
                exact ⟨ha, Finset.mem_univ _⟩
              · intro p _
                exact congrArg (fun q : Idx => (f q.1 q.2) x • u q.1 q.2) (e.symm_apply_apply p).symm
    have hx_expand : x = ∑ a ∈ J, (Φ a x) • (w * U a) := by
      conv_lhs => rw [hx, hsum_eq, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      exact mul_smul_comm (Φ a x) w (U a)
    have hPhi_zero : ∀ k : ℕ, ∀ (hk : k < r), Φ ⟨k, hk⟩ x = 0 := by
      intro k
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        intro hk
        rw [hx_expand, map_sum]
        refine Finset.sum_eq_zero (fun b _ => ?_)
        rw [map_smul]
        by_cases hlt : b.val < k
        · have hb0 : Φ b x = 0 := ih b.val hlt b.isLt
          rw [hb0, zero_smul]
        · have hle : (⟨k, hk⟩ : Fin r) ≤ b := Nat.le_of_not_lt hlt
          have hwab : Φ ⟨k, hk⟩ (w * U b) = 0 := hw0 ⟨k, hk⟩ b hle
          rw [hwab, smul_zero]
    rw [hx_expand]
    refine Finset.sum_eq_zero (fun a _ => ?_)
    have ha0 : Φ a x = 0 := hPhi_zero a.val a.isLt
    rw [ha0, zero_smul]
