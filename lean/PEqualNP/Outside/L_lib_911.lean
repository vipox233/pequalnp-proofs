import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_911

noncomputable section

open Classical

lemma zmod2_eq_one_of_ne_zero (a : ZMod 2) (ha : a ≠ 0) : a = 1 := by
  revert a ha; decide

lemma card_vec_zmod2 (k : ℕ) : Fintype.card (Fin k → ZMod 2) = 2 ^ k := by
  simp [ZMod.card]

def fintypeLinVec (k D : ℕ) : Fintype ((Fin k → ZMod 2) →ₗ[ZMod 2] (Fin D → ZMod 2)) :=
  @Fintype.ofFinite _
    (Finite.of_injective (fun f : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin D → ZMod 2) => (f : (Fin k → ZMod 2) → (Fin D → ZMod 2)))
      DFunLike.coe_injective)

lemma card_inj_lin_vec (D : ℕ) : ∀ k : ℕ,
    letI : Fintype ((Fin k → ZMod 2) →ₗ[ZMod 2] (Fin D → ZMod 2)) := fintypeLinVec k D
    (Finset.univ.filter fun f : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin D → ZMod 2) =>
      Function.Injective f).card =
    ∏ i : Fin k, (2 ^ D - 2 ^ i.val) := by
  intro k
  induction k with
  | zero =>
    letI : Fintype ((Fin 0 → ZMod 2) →ₗ[ZMod 2] (Fin D → ZMod 2)) := fintypeLinVec 0 D
    rw [Finset.prod_eq_one (fun i _ => Fin.elim0 i)]
    have huniq : (Finset.univ.filter fun f : (Fin 0 → ZMod 2) →ₗ[ZMod 2] (Fin D → ZMod 2) =>
        Function.Injective f) = {0} := by
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro _
        apply LinearMap.ext
        intro x
        have hx : x = 0 := by ext i; exact Fin.elim0 i
        rw [hx, map_zero, LinearMap.zero_apply]
      · rintro rfl a b _
        ext i
        exact Fin.elim0 i
    change (Finset.univ.filter fun f : (Fin 0 → ZMod 2) →ₗ[ZMod 2] (Fin D → ZMod 2) =>
        Function.Injective f).card = 1
    rw [huniq, Finset.card_singleton]
  | succ k ih =>
    letI : Fintype ((Fin (k + 1) → ZMod 2) →ₗ[ZMod 2] (Fin D → ZMod 2)) := fintypeLinVec (k + 1) D
    letI : Fintype ((Fin k → ZMod 2) →ₗ[ZMod 2] (Fin D → ZMod 2)) := fintypeLinVec k D
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [← ih]
    let embedCast : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin (k + 1) → ZMod 2) :=
      { toFun := fun y i => if h : i.val < k then y ⟨i.val, h⟩ else 0
        map_add' := fun y1 y2 => by ext i; by_cases h : i.val < k <;> simp [h]
        map_smul' := fun c y => by ext i; by_cases h : i.val < k <;> simp [h] }
    let res : ((Fin (k + 1) → ZMod 2) →ₗ[ZMod 2] (Fin D → ZMod 2)) →
        ((Fin k → ZMod 2) →ₗ[ZMod 2] (Fin D → ZMod 2)) :=
      fun f => f.comp embedCast
    let evalLast : ((Fin (k + 1) → ZMod 2) →ₗ[ZMod 2] (Fin D → ZMod 2)) → (Fin D → ZMod 2) :=
      fun f => f (Pi.single (Fin.last k) 1)
    let S := Finset.univ.filter fun f : (Fin (k + 1) → ZMod 2) →ₗ[ZMod 2] (Fin D → ZMod 2) =>
      Function.Injective f
    let T := Finset.univ.filter fun g : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin D → ZMod 2) =>
      Function.Injective g
    have hsplit : ∀ f : (Fin (k + 1) → ZMod 2) →ₗ[ZMod 2] (Fin D → ZMod 2),
        Function.Injective f ↔
          Function.Injective (res f) ∧ evalLast f ∉ LinearMap.range (res f) := by
      intro f
      constructor
      · intro hf
        refine ⟨?_, ?_⟩
        · intro y1 y2 hy
          have h1 : f (embedCast y1) = f (embedCast y2) := hy
          have h2 := hf h1
          ext i
          have := congrFun h2 i.castSucc
          simpa [embedCast, i.isLt] using this
        · rintro ⟨y, hy⟩
          have h1 : f (embedCast y) = f (Pi.single (Fin.last k) 1) := hy
          have h2 := hf h1
          have hlast := congrFun h2 (Fin.last k)
          simp [embedCast] at hlast
      · rintro ⟨hres, hnot⟩
        rw [injective_iff_map_eq_zero]
        intro x hx
        let y : Fin k → ZMod 2 := fun i => x i.castSucc
        have hxdecomp : x = embedCast y + x (Fin.last k) • Pi.single (Fin.last k) 1 := by
          ext i
          by_cases hi : i.val < k
          · have hne : i ≠ Fin.last k := fun h => by rw [h] at hi; exact Nat.lt_irrefl k hi
            simp [y, embedCast, hi, Pi.single_eq_of_ne hne]
          · have heq : i = Fin.last k := Fin.ext (by simp only [Fin.val_last]; have := i.isLt; omega)
            subst heq
            simp [embedCast]
        rw [hxdecomp, map_add, map_smul] at hx
        have hlast0 : x (Fin.last k) = 0 := by
          by_contra hne
          have h1 : x (Fin.last k) = 1 := zmod2_eq_one_of_ne_zero _ hne
          rw [h1, one_smul] at hx
          apply hnot
          refine ⟨-y, ?_⟩
          change res f (-y) = f (Pi.single (Fin.last k) 1)
          rw [map_neg]
          exact eq_of_sub_eq_zero (by
            have hadd : res f y + f (Pi.single (Fin.last k) 1) = 0 := hx
            calc -res f y - f (Pi.single (Fin.last k) 1)
                = -(res f y + f (Pi.single (Fin.last k) 1)) := by abel
              _ = 0 := by rw [hadd, neg_zero])
        rw [hlast0, zero_smul, add_zero] at hx hxdecomp
        have hy0 : y = 0 := hres (by simpa [res] using hx)
        rw [hxdecomp, hy0, map_zero]
    have hfiber : ∀ g ∈ T, (S.filter fun f => res f = g).card = 2 ^ D - 2 ^ k := by
      intro g hg
      have hginj : Function.Injective g := (Finset.mem_filter.1 hg).2
      let R : Finset (Fin D → ZMod 2) := Finset.univ.filter fun v => v ∈ LinearMap.range g
      have hRcard : R.card = 2 ^ k := by
        have hbij : R.card = (Finset.univ : Finset (Fin k → ZMod 2)).card := by
          refine Finset.card_bij (fun v hv => Classical.choose (Finset.mem_filter.1 hv).2) ?_ ?_ ?_
          · intro _ _; exact Finset.mem_univ _
          · intro v1 hv1 v2 hv2 heq
            have h1 := Classical.choose_spec (Finset.mem_filter.1 hv1).2
            have h2 := Classical.choose_spec (Finset.mem_filter.1 hv2).2
            rw [← h1, ← h2, heq]
          · intro y _
            refine ⟨g y, Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨y, rfl⟩⟩, ?_⟩
            exact hginj (Classical.choose_spec (⟨y, rfl⟩ : g y ∈ LinearMap.range g))
        rw [hbij, Finset.card_univ, card_vec_zmod2]
      let avail : Finset (Fin D → ZMod 2) := Finset.univ \ R
      have havail : avail.card = 2 ^ D - 2 ^ k := by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, card_vec_zmod2, hRcard]
      rw [← havail]
      refine Finset.card_bij (fun f _ => evalLast f) ?_ ?_ ?_
      · intro f hf
        have hfS := (Finset.mem_filter.1 hf).1
        have hfg := (Finset.mem_filter.1 hf).2
        have hfinj := (Finset.mem_filter.1 hfS).2
        have hsp := (hsplit f).1 hfinj
        rw [hfg] at hsp
        simp only [avail, Finset.mem_sdiff, Finset.mem_univ, true_and, R, Finset.mem_filter]
        exact hsp.2
      · intro f1 hf1 f2 hf2 hev
        have hfg1 := (Finset.mem_filter.1 hf1).2
        have hfg2 := (Finset.mem_filter.1 hf2).2
        apply LinearMap.ext
        intro x
        let y : Fin k → ZMod 2 := fun i => x i.castSucc
        have hxdecomp : x = embedCast y + x (Fin.last k) • Pi.single (Fin.last k) 1 := by
          ext i
          by_cases hi : i.val < k
          · have hne : i ≠ Fin.last k := fun h => by rw [h] at hi; exact Nat.lt_irrefl k hi
            simp [y, embedCast, hi, Pi.single_eq_of_ne hne]
          · have heq : i = Fin.last k := Fin.ext (by simp only [Fin.val_last]; have := i.isLt; omega)
            subst heq
            simp [embedCast]
        rw [hxdecomp, map_add, map_add, map_smul, map_smul]
        have h1 : f1 (embedCast y) = res f1 y := rfl
        have h2 : f2 (embedCast y) = res f2 y := rfl
        rw [h1, h2, hfg1, hfg2]
        exact congrArg (g y + x (Fin.last k) • ·) hev
      · intro v hv
        simp only [avail, Finset.mem_sdiff, Finset.mem_univ, true_and, R, Finset.mem_filter] at hv
        let f : (Fin (k + 1) → ZMod 2) →ₗ[ZMod 2] (Fin D → ZMod 2) :=
          { toFun := fun x => g (fun i => x i.castSucc) + x (Fin.last k) • v
            map_add' := fun x1 x2 => by
              have h1 : (fun i : Fin k => (x1 + x2) i.castSucc) =
                  (fun i => x1 i.castSucc) + (fun i => x2 i.castSucc) := rfl
              rw [h1, map_add, Pi.add_apply, add_smul]
              abel
            map_smul' := fun c x => by
              have h1 : (fun i : Fin k => (c • x) i.castSucc) = c • (fun i => x i.castSucc) := rfl
              rw [h1, map_smul, Pi.smul_apply, smul_eq_mul, mul_smul, smul_add, RingHom.id_apply] }
        have hresf : res f = g := by
          apply LinearMap.ext
          intro y
          ext j
          have hy : (fun i : Fin k => embedCast y i.castSucc) = y := by
            ext i; simp [embedCast, i.isLt]
          have hlast : embedCast y (Fin.last k) = 0 := by simp [embedCast]
          change (g (fun i => embedCast y i.castSucc) + embedCast y (Fin.last k) • v) j = g y j
          rw [hy, hlast, zero_smul, add_zero]
        have hevf : evalLast f = v := by
          simp [evalLast, f]
          have h0 : (fun _ : Fin k => (0 : ZMod 2)) = 0 := rfl
          rw [h0, map_zero]
        refine ⟨f, ?_, hevf⟩
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, (hsplit f).2 ?_⟩, hresf⟩
        rw [hresf, hevf]
        exact ⟨hginj, hv⟩
    have hcard : S.card = ∑ g ∈ T, (S.filter fun f => res f = g).card := by
      rw [← Finset.card_biUnion]
      · congr 1
        ext f
        simp only [Finset.mem_biUnion, Finset.mem_filter, S, T, Finset.mem_univ, true_and]
        constructor
        · intro hf
          exact ⟨res f, ((hsplit f).1 hf).1, hf, rfl⟩
        · rintro ⟨_, _, hf, _⟩
          exact hf
      · intro g1 _ g2 _ hne
        simp only [Function.onFun, Finset.disjoint_left]
        intro f h1 h2
        exact hne ((Finset.mem_filter.1 h1).2.symm.trans (Finset.mem_filter.1 h2).2)
    rw [hcard, Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul, mul_comm]

lemma card_submodules_finrank_eq (D k : ℕ) :
    (Finset.univ.filter fun U : Submodule (ZMod 2) (Fin D → ZMod 2) =>
      Module.finrank (ZMod 2) U = k).card * ∏ i : Fin k, (2 ^ k - 2 ^ i.val) =
    ∏ i : Fin k, (2 ^ D - 2 ^ i.val) := by
  letI : Fintype ((Fin k → ZMod 2) →ₗ[ZMod 2] (Fin D → ZMod 2)) := fintypeLinVec k D
  letI : Fintype ((Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2)) := fintypeLinVec k k
  let S := Finset.univ.filter fun f : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin D → ZMod 2) =>
    Function.Injective f
  let Ts := Finset.univ.filter fun U : Submodule (ZMod 2) (Fin D → ZMod 2) =>
    Module.finrank (ZMod 2) U = k
  have hS : S.card = ∏ i : Fin k, (2 ^ D - 2 ^ i.val) := card_inj_lin_vec D k
  rw [← hS]
  have hpart : S.card = ∑ U ∈ Ts, (S.filter fun f => LinearMap.range f = U).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext f
      simp only [Finset.mem_biUnion, Finset.mem_filter, S, Ts, Finset.mem_univ, true_and]
      constructor
      · intro hf
        refine ⟨LinearMap.range f, ?_, hf, rfl⟩
        rw [LinearMap.finrank_range_of_inj hf, Module.finrank_fin_fun]
      · rintro ⟨_, _, hf, _⟩
        exact hf
    · intro U1 _ U2 _ hne
      simp only [Function.onFun, Finset.disjoint_left]
      intro f h1 h2
      exact hne ((Finset.mem_filter.1 h1).2.symm.trans (Finset.mem_filter.1 h2).2)
  have hfib : ∀ U ∈ Ts, (S.filter fun f => LinearMap.range f = U).card =
      ∏ i : Fin k, (2 ^ k - 2 ^ i.val) := by
    intro U hU
    have hdim : Module.finrank (ZMod 2) U = k := (Finset.mem_filter.1 hU).2
    let e : (Fin k → ZMod 2) ≃ₗ[ZMod 2] U :=
      LinearEquiv.ofFinrankEq (Fin k → ZMod 2) U (by rw [Module.finrank_fin_fun, hdim])
    rw [← card_inj_lin_vec k k]
    refine Finset.card_bij
      (fun f hf => e.symm.toLinearMap.comp (f.codRestrict U fun x => by
        rw [← (Finset.mem_filter.1 hf).2]; exact ⟨x, rfl⟩)) ?_ ?_ ?_
    · intro f hf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hfinj : Function.Injective f := (Finset.mem_filter.1 (Finset.mem_filter.1 hf).1).2
      intro a b hab
      have h1 := e.symm.injective hab
      have h2 := congrArg Subtype.val h1
      exact hfinj h2
    · intro f1 hf1 f2 hf2 hab
      apply LinearMap.ext
      intro x
      have h1 := LinearMap.congr_fun hab x
      have h2 := e.symm.injective h1
      exact congrArg Subtype.val h2
    · intro g hg
      have hginj : Function.Injective g := (Finset.mem_filter.1 hg).2
      let f : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin D → ZMod 2) := U.subtype.comp (e.toLinearMap.comp g)
      have hfinj : Function.Injective f :=
        U.injective_subtype.comp (e.injective.comp hginj)
      have hfrange : LinearMap.range f = U := by
        apply Submodule.eq_of_le_of_finrank_eq
        · rintro _ ⟨x, rfl⟩; exact (e (g x)).2
        · rw [LinearMap.finrank_range_of_inj hfinj, Module.finrank_fin_fun, hdim]
      refine ⟨f, Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hfinj⟩, hfrange⟩, ?_⟩
      apply LinearMap.ext
      intro x
      change e.symm ⟨f x, _⟩ = g x
      have hfx : (⟨f x, (e (g x)).2⟩ : U) = e (g x) := Subtype.ext rfl
      rw [hfx, e.symm_apply_apply]
  rw [hpart, Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]

def perpSub {D : ℕ} (U : Submodule (ZMod 2) (Fin D → ZMod 2)) :
    Submodule (ZMod 2) (Fin D → ZMod 2) :=
  { carrier := {v | ∀ u ∈ U, ∑ i : Fin D, u i * v i = 0}
    zero_mem' := fun _ _ => by simp
    smul_mem' := fun c _ ha u hu => by
      simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm, ← Finset.mul_sum, ha u hu, mul_zero]
    , add_mem' := fun ha hb u hu => by
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, ha u hu, hb u hu, add_zero] }

lemma finrank_perpSub {D : ℕ} (U : Submodule (ZMod 2) (Fin D → ZMod 2)) :
    Module.finrank (ZMod 2) (perpSub U) = D - Module.finrank (ZMod 2) U := by
  let Φ : (Fin D → ZMod 2) →ₗ[ZMod 2] (U →ₗ[ZMod 2] ZMod 2) :=
    { toFun := fun v =>
        { toFun := fun u => ∑ i : Fin D, u.1 i * v i
          map_add' := fun u1 u2 => by
            simp only [Submodule.coe_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
          map_smul' := fun c u => by
            simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum,
              RingHom.id_apply] }
      map_add' := fun v1 v2 => by
        ext u
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, Pi.add_apply, mul_add,
          Finset.sum_add_distrib]
      map_smul' := fun c v => by
        ext u
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, Pi.smul_apply,
          smul_eq_mul, mul_left_comm, ← Finset.mul_sum, RingHom.id_apply] }
  have hker : LinearMap.ker Φ = perpSub U := by
    ext v
    simp only [LinearMap.mem_ker, perpSub, Submodule.mem_mk, AddSubmonoid.mem_mk,
      AddSubsemigroup.mem_mk, Set.mem_setOf_eq, LinearMap.ext_iff, LinearMap.zero_apply]
    exact ⟨fun h u hu => h ⟨u, hu⟩, fun h ⟨u, hu⟩ => h u hu⟩
  have hsurj : Function.Surjective Φ := by
    intro φ
    obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend (p := U) φ
    refine ⟨fun i => ψ (Pi.single i 1), ?_⟩
    ext ⟨u, hu⟩
    have hu_sum : u = ∑ i : Fin D, u i • Pi.single i 1 := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    calc (Φ (fun i => ψ (Pi.single i 1))) ⟨u, hu⟩
        = ∑ i : Fin D, u i * ψ (Pi.single i 1) := rfl
      _ = ψ (∑ i : Fin D, u i • Pi.single i 1) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_smul, smul_eq_mul]
      _ = ψ u := by rw [← hu_sum]
      _ = φ ⟨u, hu⟩ := by
          have := LinearMap.congr_fun hψ ⟨u, hu⟩
          simpa using this
  have hrn := LinearMap.finrank_range_add_finrank_ker Φ
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, hker, Module.finrank_fin_fun,
    Subspace.dual_finrank_eq] at hrn
  omega

lemma perpSub_perpSub {D : ℕ} (U : Submodule (ZMod 2) (Fin D → ZMod 2)) :
    perpSub (perpSub U) = U := by
  have hle : U ≤ perpSub (perpSub U) := by
    intro u hu v hv
    rw [Finset.sum_congr rfl (fun i _ => mul_comm (v i) (u i))]
    exact hv u hu
  exact (Submodule.eq_of_le_of_finrank_eq hle (by
    rw [finrank_perpSub, finrank_perpSub]
    have hU : Module.finrank (ZMod 2) U ≤ D := by
      simpa [Module.finrank_fin_fun] using Submodule.finrank_le U
    omega)).symm

lemma card_submodules_codim (D d : ℕ) (hd : d ≤ D) :
    (Finset.univ.filter fun U : Submodule (ZMod 2) (Fin D → ZMod 2) =>
      Module.finrank (ZMod 2) U = d).card =
    (Finset.univ.filter fun U : Submodule (ZMod 2) (Fin D → ZMod 2) =>
      Module.finrank (ZMod 2) U = D - d).card := by
  refine Finset.card_bij (fun U _ => perpSub U) ?_ ?_ ?_
  · intro U hU
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU ⊢
    rw [finrank_perpSub, hU]
  · intro U1 _ U2 _ heq
    have := congrArg perpSub heq
    rwa [perpSub_perpSub, perpSub_perpSub] at this
  · intro V hV
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hV
    refine ⟨perpSub V, ?_, perpSub_perpSub V⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [finrank_perpSub, hV]
    omega

lemma card_submodules_le_eq_codim {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] [Fintype (Submodule (ZMod 2) W)]
    (V : Submodule (ZMod 2) W) (d : ℕ) (hd : d ≤ Module.finrank (ZMod 2) V) :
    let D := Module.finrank (ZMod 2) V
    let c := D - d
    (((Finset.univ.filter fun U : Submodule (ZMod 2) W =>
      U ≤ V ∧ Module.finrank (ZMod 2) U = d).card : ℕ) : ℚ) =
    ∏ i : Fin c, (((2 : ℚ) ^ D - (2 : ℚ) ^ i.val) / ((2 : ℚ) ^ c - (2 : ℚ) ^ i.val)) := by
  intro D c
  let e : V ≃ₗ[ZMod 2] (Fin D → ZMod 2) :=
    LinearEquiv.ofFinrankEq V (Fin D → ZMod 2) (by rw [Module.finrank_fin_fun])
  have hbij : (Finset.univ.filter fun U : Submodule (ZMod 2) W =>
      U ≤ V ∧ Module.finrank (ZMod 2) U = d).card =
      (Finset.univ.filter fun U : Submodule (ZMod 2) (Fin D → ZMod 2) =>
        Module.finrank (ZMod 2) U = d).card := by
    refine Finset.card_bij (fun U _ => (U.comap V.subtype).map e.toLinearMap) ?_ ?_ ?_
    · intro U hU
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU ⊢
      have h1 : Module.finrank (ZMod 2) ((U.comap V.subtype).map e.toLinearMap) =
          Module.finrank (ZMod 2) (U.comap V.subtype) :=
        LinearEquiv.finrank_map_eq e (U.comap V.subtype)
      have h2 : (U.comap V.subtype).map V.subtype = U := by
        rw [Submodule.map_comap_subtype, inf_eq_right.2 hU.1]
      rw [h1, ← Submodule.finrank_map_subtype_eq V (U.comap V.subtype), h2, hU.2]
    · intro U1 hU1 U2 hU2 heq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU1 hU2
      have h1 : U1.comap V.subtype = U2.comap V.subtype :=
        Submodule.map_injective_of_injective e.injective heq
      have h2 := congrArg (Submodule.map V.subtype) h1
      rwa [Submodule.map_comap_subtype, Submodule.map_comap_subtype,
        inf_eq_right.2 hU1.1, inf_eq_right.2 hU2.1] at h2
    · intro U' hU'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU'
      let U0 : Submodule (ZMod 2) V := U'.map e.symm.toLinearMap
      let U : Submodule (ZMod 2) W := U0.map V.subtype
      refine ⟨U, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, ?_⟩
        · rintro _ ⟨v, _, rfl⟩; exact v.2
        · rw [Submodule.finrank_map_subtype_eq, LinearEquiv.finrank_map_eq, hU']
      · have hcomap : U.comap V.subtype = U0 :=
          Submodule.comap_map_eq_of_injective V.injective_subtype U0
        rw [hcomap]
        dsimp only [U0]
        rw [← Submodule.map_comp]
        have heid : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by ext x; simp
        rw [heid, Submodule.map_id]
  rw [hbij, card_submodules_codim D d hd]
  have hmul := card_submodules_finrank_eq D c
  have hmulQ : (((Finset.univ.filter fun U : Submodule (ZMod 2) (Fin D → ZMod 2) =>
      Module.finrank (ZMod 2) U = c).card : ℕ) : ℚ) *
      ∏ i : Fin c, ((2 : ℚ) ^ c - (2 : ℚ) ^ i.val) =
      ∏ i : Fin c, ((2 : ℚ) ^ D - (2 : ℚ) ^ i.val) := by
    have hq := congrArg (Nat.cast (R := ℚ)) hmul
    push_cast at hq
    have hcast : ∀ (M : ℕ) (i : Fin c), i.val < M →
        (((2 ^ M - 2 ^ i.val : ℕ) : ℚ)) = (2 : ℚ) ^ M - (2 : ℚ) ^ i.val := by
      intro M i hi
      have hle : 2 ^ i.val ≤ 2 ^ M := Nat.pow_le_pow_right (by omega) (le_of_lt hi)
      rw [Nat.cast_sub hle]
      push_cast
      rfl
    have h1 : ∏ i : Fin c, (((2 ^ c - 2 ^ i.val : ℕ) : ℚ)) =
        ∏ i : Fin c, ((2 : ℚ) ^ c - (2 : ℚ) ^ i.val) :=
      Finset.prod_congr rfl fun i _ => hcast c i i.isLt
    have h2 : ∏ i : Fin c, (((2 ^ D - 2 ^ i.val : ℕ) : ℚ)) =
        ∏ i : Fin c, ((2 : ℚ) ^ D - (2 : ℚ) ^ i.val) :=
      Finset.prod_congr rfl fun i _ => hcast D i (lt_of_lt_of_le i.isLt (Nat.sub_le D d))
    rwa [h1, h2] at hq
  have hne : ∏ i : Fin c, ((2 : ℚ) ^ c - (2 : ℚ) ^ i.val) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i _
    have hlt : (2 : ℚ) ^ i.val < (2 : ℚ) ^ c :=
      pow_lt_pow_right₀ (by norm_num) i.isLt
    linarith
  rw [Finset.prod_div_distrib, eq_div_iff hne]
  exact hmulQ

def qBinPoly (a c : ℕ) : Polynomial ℚ :=
  ∏ i : Fin c, Polynomial.C (((2 : ℚ) ^ c - (2 : ℚ) ^ i.val)⁻¹) *
    (Polynomial.C (((2 : ℚ) ^ a)⁻¹) * Polynomial.X - Polynomial.C ((2 : ℚ) ^ i.val))

lemma qBinPoly_natDegree_le (a c : ℕ) : (qBinPoly a c).natDegree ≤ c := by
  unfold qBinPoly
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  have h1 : ∀ i ∈ (Finset.univ : Finset (Fin c)),
      (Polynomial.C (((2 : ℚ) ^ c - (2 : ℚ) ^ i.val)⁻¹) *
        (Polynomial.C (((2 : ℚ) ^ a)⁻¹) * Polynomial.X - Polynomial.C ((2 : ℚ) ^ i.val))).natDegree ≤ 1 := by
    intro i _
    refine Polynomial.natDegree_mul_le.trans ?_
    rw [Polynomial.natDegree_C, zero_add]
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ (by rw [Polynomial.natDegree_C]; omega))
    exact Polynomial.natDegree_mul_le.trans (by rw [Polynomial.natDegree_C, Polynomial.natDegree_X])
  exact (Finset.sum_le_sum h1).trans (by simp)

lemma qBinPoly_eval (a c N : ℕ) (ha : a ≤ N) :
    (qBinPoly a c).eval ((2 : ℚ) ^ N) =
    ∏ i : Fin c, (((2 : ℚ) ^ (N - a) - (2 : ℚ) ^ i.val) / ((2 : ℚ) ^ c - (2 : ℚ) ^ i.val)) := by
  unfold qBinPoly
  rw [Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X]
  have hpow : ((2 : ℚ) ^ a)⁻¹ * (2 : ℚ) ^ N = (2 : ℚ) ^ (N - a) := by
    have hsplit : (2 : ℚ) ^ N = (2 : ℚ) ^ a * (2 : ℚ) ^ (N - a) := by
      rw [← pow_add, Nat.add_sub_of_le ha]
    rw [hsplit, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  rw [hpow, div_eq_inv_mul]

def choosePoly (C d : ℕ) : Polynomial ℚ :=
  Polynomial.C ((d.factorial : ℚ)⁻¹) *
    ∏ i : Fin d, (Polynomial.X - Polynomial.C ((C + i.val : ℕ) : ℚ))

lemma choosePoly_natDegree_le (C d : ℕ) : (choosePoly C d).natDegree ≤ d := by
  unfold choosePoly
  calc (Polynomial.C ((d.factorial : ℚ)⁻¹) *
          ∏ i : Fin d, (Polynomial.X - Polynomial.C ((C + i.val : ℕ) : ℚ))).natDegree
      ≤ (Polynomial.C ((d.factorial : ℚ)⁻¹)).natDegree +
        (∏ i : Fin d, (Polynomial.X - Polynomial.C ((C + i.val : ℕ) : ℚ))).natDegree :=
        Polynomial.natDegree_mul_le
    _ ≤ 0 + ∑ i : Fin d, (Polynomial.X - Polynomial.C ((C + i.val : ℕ) : ℚ)).natDegree := by
        rw [Polynomial.natDegree_C]
        exact Nat.add_le_add_left (Polynomial.natDegree_prod_le _ _) 0
    _ ≤ ∑ _i : Fin d, 1 := by
        rw [zero_add]
        exact Finset.sum_le_sum fun i _ => by
          calc (Polynomial.X - Polynomial.C ((C + i.val : ℕ) : ℚ)).natDegree
              ≤ max Polynomial.X.natDegree (Polynomial.C ((C + i.val : ℕ) : ℚ)).natDegree :=
                Polynomial.natDegree_sub_le _ _
            _ ≤ 1 := by rw [Polynomial.natDegree_X, Polynomial.natDegree_C]; omega
    _ = d := by simp

lemma choosePoly_eval (C d t : ℕ) (hCt : C ≤ t) :
    (choosePoly C d).eval (t : ℚ) = (Nat.choose (t - C) d : ℚ) := by
  unfold choosePoly
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
  have hprod : ∏ i : Fin d, (Polynomial.X - Polynomial.C ((C + i.val : ℕ) : ℚ)).eval (t : ℚ) =
      ((t - C).descFactorial d : ℚ) := by
    induction d with
    | zero => simp
    | succ d ih =>
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih, Nat.descFactorial_succ]
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      by_cases hlt : t - C < d
      · have h0 : (t - C).descFactorial d = 0 := Nat.descFactorial_eq_zero_iff_lt.2 hlt
        simp [h0]
      · have hle : C + d ≤ t := by omega
        push_cast
        have hsub : (t : ℚ) - ((C : ℚ) + (d : ℚ)) = ((t - C - d : ℕ) : ℚ) := by
          rw [Nat.cast_sub (by omega), Nat.cast_sub hCt]
          ring
        rw [hsub]
        ring
  rw [hprod, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  have hfac : (d.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero d)
  field_simp [hfac]

lemma stars_bars_card : ∀ (k M : ℕ),
    (Finset.univ.filter fun g : Fin (k + 1) → Fin (M + 1) =>
      ∑ i : Fin (k + 1), (g i).val = M).card = Nat.choose (M + k) k := by
  intro k
  induction k with
  | zero =>
    intro M
    rw [Nat.add_zero, Nat.choose_zero_right]
    have huniq : (Finset.univ.filter fun g : Fin 1 → Fin (M + 1) =>
        ∑ i : Fin 1, (g i).val = M) = {fun _ => ⟨M, Nat.lt_succ_self M⟩} := by
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        Fin.sum_univ_one]
      constructor
      · intro h
        ext i
        rw [Fin.eq_zero i]
        exact h
      · rintro rfl; rfl
    rw [huniq, Finset.card_singleton]
  | succ k ih =>
    intro M
    have hpart : (Finset.univ.filter fun g : Fin (k + 2) → Fin (M + 1) =>
        ∑ i : Fin (k + 2), (g i).val = M).card =
        ∑ r : Fin (M + 1),
          (Finset.univ.filter fun g : Fin (k + 2) → Fin (M + 1) =>
            g (Fin.last (k + 1)) = r ∧ ∑ i : Fin (k + 2), (g i).val = M).card := by
      rw [← Finset.card_biUnion]
      · congr 1
        ext g
        simp
      · intro r1 _ r2 _ hne
        simp only [Function.onFun, Finset.disjoint_left]
        intro g h1 h2
        exact hne ((Finset.mem_filter.1 h1).2.1.symm.trans (Finset.mem_filter.1 h2).2.1)
    rw [hpart]
    have hfib : ∀ r : Fin (M + 1),
        (Finset.univ.filter fun g : Fin (k + 2) → Fin (M + 1) =>
          g (Fin.last (k + 1)) = r ∧ ∑ i : Fin (k + 2), (g i).val = M).card =
        Nat.choose ((M - r.val) + k) k := by
      intro r
      rw [← ih (M - r.val)]
      refine Finset.card_bij
        (fun g hg i => ⟨(g i.castSucc).val, by
          have hsum := (Finset.mem_filter.1 hg).2.2
          have hr := (Finset.mem_filter.1 hg).2.1
          rw [Fin.sum_univ_castSucc, hr] at hsum
          have hle : (g i.castSucc).val ≤ ∑ j : Fin (k + 1), (g j.castSucc).val :=
            Finset.single_le_sum (f := fun j : Fin (k + 1) => (g j.castSucc).val)
              (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
          omega⟩) ?_ ?_ ?_
      · intro g hg
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
        rw [Fin.sum_univ_castSucc, hg.1] at hg
        omega
      · intro g1 hg1 g2 hg2 heq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg1 hg2
        ext i
        by_cases hi : i.val < k + 1
        · have h1 := congrFun heq ⟨i.val, hi⟩
          simpa using congrArg Fin.val h1
        · have he : i = Fin.last (k + 1) := Fin.ext (by simp only [Fin.val_last]; have := i.isLt; omega)
          subst he
          rw [hg1.1, hg2.1]
      · intro f hf
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
        let g : Fin (k + 2) → Fin (M + 1) := fun i =>
          if hi : i.val < k + 1 then ⟨(f ⟨i.val, hi⟩).val, by have := (f ⟨i.val, hi⟩).isLt; omega⟩
          else r
        refine ⟨g, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨by simp [g], ?_⟩
          rw [Fin.sum_univ_castSucc]
          have h1 : ∑ i : Fin (k + 1), (g i.castSucc).val = ∑ i : Fin (k + 1), (f i).val := by
            refine Finset.sum_congr rfl fun i _ => ?_
            simp only [g, Fin.val_castSucc, i.isLt, ↓reduceDIte]
          have h2 : (g (Fin.last (k + 1))).val = r.val := by simp [g]
          rw [h1, h2, hf]
          omega
        · ext i
          simp only [g, Fin.val_castSucc, i.isLt, ↓reduceDIte]
    rw [Finset.sum_congr rfl fun r _ => hfib r]
    have hrev : ∑ r : Fin (M + 1), Nat.choose ((M - r.val) + k) k =
        ∑ m ∈ Finset.range (M + 1), Nat.choose (m + k) k := by
      rw [← Fin.sum_univ_eq_sum_range (fun m => Nat.choose (m + k) k) (M + 1)]
      refine Finset.sum_bij (fun r _ => ⟨M - r.val, by omega⟩) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro r1 _ r2 _ h
        ext
        have := congrArg Fin.val h
        dsimp at this
        omega
      · intro m _
        exact ⟨⟨M - m.val, by omega⟩, Finset.mem_univ _, Fin.ext (by dsimp; omega)⟩
      · intro r _; rfl
    rw [hrev]
    clear hpart hfib hrev ih
    induction M with
    | zero => simp
    | succ M ihM =>
      rw [Finset.sum_range_succ, ihM]
      have h1 : M + 1 + k = (M + k) + 1 := by omega
      have h2 : M + 1 + (k + 1) = (M + k + 1) + 1 := by omega
      have h3 : M + (k + 1) = M + k + 1 := by omega
      rw [h1, h2, h3, Nat.choose_succ_succ (M + k + 1) k, add_comm]

def nextIdx {n : ℕ} (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩

def prevIdx {n : ℕ} (i : Fin n) : Fin n :=
  ⟨(i.val + (n - 1)) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩

lemma nextIdx_prevIdx {n : ℕ} (i : Fin n) : nextIdx (prevIdx i) = i := by
  ext
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  simp only [nextIdx, prevIdx]
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  have h : i.val + (n - 1) + 1 = i.val + n := by omega
  rw [h, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

lemma prevIdx_nextIdx {n : ℕ} (i : Fin n) : prevIdx (nextIdx i) = i := by
  ext
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  simp only [nextIdx, prevIdx]
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  have h : i.val + 1 + (n - 1) = i.val + n := by omega
  rw [h, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

lemma nextIdx_bijective (n : ℕ) : Function.Bijective (@nextIdx n) :=
  Function.bijective_iff_has_inverse.2 ⟨prevIdx, prevIdx_nextIdx, nextIdx_prevIdx⟩

lemma iso_const_on_adj {n : ℕ} (U : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hiso : ∀ x ∈ U, ∀ y ∈ U, ∀ i : Fin n, x i * y (nextIdx i) = x (nextIdx i) * y i)
    (i : Fin n) (h1 : ∃ x ∈ U, x i ≠ 0) (h2 : ∃ y ∈ U, y (nextIdx i) ≠ 0) :
    ∀ x ∈ U, x i = x (nextIdx i) := by
  obtain ⟨y, hyU, hyi⟩ := h1
  obtain ⟨z, hzU, hzn⟩ := h2
  have hy1 : y i = 1 := zmod2_eq_one_of_ne_zero _ hyi
  have hz1 : z (nextIdx i) = 1 := zmod2_eq_one_of_ne_zero _ hzn
  have hyn : y (nextIdx i) = 1 := by
    have heq := hiso y hyU z hzU i
    rw [hy1, hz1, one_mul] at heq
    by_contra hne
    have h0 : y (nextIdx i) = 0 := by
      by_contra hne0
      exact hne (zmod2_eq_one_of_ne_zero _ hne0)
    rw [h0, zero_mul] at heq
    exact absurd heq (by decide)
  intro x hxU
  have heq := hiso x hxU y hyU i
  rw [hy1, hyn, mul_one, mul_one] at heq
  exact heq

lemma supp_ne_all {n : ℕ} (hn : 0 < n) (U : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hiso : ∀ x ∈ U, ∀ y ∈ U, ∀ i : Fin n, x i * y (nextIdx i) = x (nextIdx i) * y i)
    (hdim : 2 ≤ Module.finrank (ZMod 2) U) :
    ∃ i : Fin n, ∀ x ∈ U, x i = 0 := by
  by_contra hall
  push Not at hall
  have hadj : ∀ x ∈ U, ∀ i : Fin n, x i = x (nextIdx i) := fun x hx i =>
    iso_const_on_adj U hiso i (hall i) (hall (nextIdx i)) x hx
  have hconst : ∀ x ∈ U, ∀ k : ℕ, (hk : k < n) → x ⟨k, hk⟩ = x ⟨0, hn⟩ := by
    intro x hx k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      have h1 := hadj x hx ⟨k, Nat.lt_of_succ_lt hk⟩
      have hnext : nextIdx ⟨k, Nat.lt_of_succ_lt hk⟩ = ⟨k + 1, hk⟩ := by
        ext
        simp [nextIdx, Nat.mod_eq_of_lt hk]
      rw [hnext] at h1
      rw [← h1, ih (Nat.lt_of_succ_lt hk)]
  have hle : U ≤ Submodule.span (ZMod 2) {(fun _ : Fin n => (1 : ZMod 2))} := by
    intro x hx
    have hxeq : x = x ⟨0, hn⟩ • (fun _ : Fin n => (1 : ZMod 2)) := by
      ext i
      simp [hconst x hx i.val i.isLt]
    rw [hxeq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  have hfr : Module.finrank (ZMod 2) U ≤ 1 := by
    calc Module.finrank (ZMod 2) U
        ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {(fun _ : Fin n => (1 : ZMod 2))}) :=
          Submodule.finrank_mono hle
      _ ≤ 1 := (finrank_span_le_card _).trans (by simp)
  omega

def isStart {n : ℕ} (s : Fin n → Bool) (i : Fin n) : Bool :=
  s i && !(s (prevIdx i))

def runStarts {n : ℕ} (s : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => isStart s i = true

def defectSet {n : ℕ} (s : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => s (prevIdx i) = s i

lemma two_mul_starts_add_defects {n : ℕ} (s : Fin n → Bool) :
    2 * (runStarts s).card + (defectSet s).card = n := by
  let S01 := Finset.univ.filter fun i : Fin n => s (prevIdx i) = false ∧ s i = true
  let S10 := Finset.univ.filter fun i : Fin n => s (prevIdx i) = true ∧ s i = false
  let S00 := Finset.univ.filter fun i : Fin n => s (prevIdx i) = false ∧ s i = false
  let S11 := Finset.univ.filter fun i : Fin n => s (prevIdx i) = true ∧ s i = true
  have hS01 : S01 = runStarts s := by
    ext i
    simp [S01, runStarts, isStart, and_comm]
  have hdef : defectSet s = S00 ∪ S11 := by
    ext i
    simp only [defectSet, S00, S11, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    cases s (prevIdx i) <;> cases s i <;> simp
  have hdef_card : (defectSet s).card = S00.card + S11.card := by
    rw [hdef, Finset.card_union_of_disjoint]
    rw [Finset.disjoint_left]
    intro i h1 h2
    simp only [S00, S11, Finset.mem_filter] at h1 h2
    exact Bool.noConfusion (h1.2.1.symm.trans h2.2.1)
  have hsum_all : S01.card + S10.card + (S00.card + S11.card) = n := by
    have hdisj1 : Disjoint S01 S10 := by
      rw [Finset.disjoint_left]; intro i h1 h2
      simp only [S01, S10, Finset.mem_filter] at h1 h2
      exact Bool.noConfusion (h1.2.1.symm.trans h2.2.1)
    have hdisj2 : Disjoint S00 S11 := by
      rw [Finset.disjoint_left]; intro i h1 h2
      simp only [S00, S11, Finset.mem_filter] at h1 h2
      exact Bool.noConfusion (h1.2.1.symm.trans h2.2.1)
    have hdisj12 : Disjoint (S01 ∪ S10) (S00 ∪ S11) := by
      rw [Finset.disjoint_left]; intro i h1 h2
      simp only [Finset.mem_union, S01, S10, S00, S11, Finset.mem_filter] at h1 h2
      rcases h1 with ⟨_, a, b⟩ | ⟨_, a, b⟩ <;> rcases h2 with ⟨_, c, d⟩ | ⟨_, c, d⟩ <;>
        simp_all
    have hunion : (S01 ∪ S10) ∪ (S00 ∪ S11) = Finset.univ := by
      ext i
      simp only [Finset.mem_union, Finset.mem_univ, iff_true, S01, S10, S00, S11,
        Finset.mem_filter, true_and]
      cases s (prevIdx i) <;> cases s i <;> simp
    rw [← Finset.card_union_of_disjoint hdisj1, ← Finset.card_union_of_disjoint hdisj2,
      ← Finset.card_union_of_disjoint hdisj12, hunion, Finset.card_univ, Fintype.card_fin]
  have heq01 : S01.card = S10.card := by
    have hsum_eq : ∑ i : Fin n, (if s (prevIdx i) = true then (1 : ℤ) else 0) =
        ∑ i : Fin n, (if s i = true then (1 : ℤ) else 0) := by
      refine Finset.sum_bij (fun i _ => prevIdx i) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro a _ b _ h; exact by rw [← nextIdx_prevIdx a, ← nextIdx_prevIdx b, h]
      · intro j _; exact ⟨nextIdx j, Finset.mem_univ _, prevIdx_nextIdx j⟩
      · intro _ _; rfl
    have hdiff : ∑ i : Fin n, ((if s (prevIdx i) = true then (1 : ℤ) else 0) -
        (if s i = true then (1 : ℤ) else 0)) = 0 := by
      rw [Finset.sum_sub_distrib, hsum_eq, sub_self]
    have hval : ∑ i : Fin n, ((if s (prevIdx i) = true then (1 : ℤ) else 0) -
        (if s i = true then (1 : ℤ) else 0)) = (S10.card : ℤ) - (S01.card : ℤ) := by
      have hterm : ∀ i : Fin n,
          ((if s (prevIdx i) = true then (1 : ℤ) else 0) -
            (if s i = true then (1 : ℤ) else 0)) =
          (if i ∈ S10 then (1 : ℤ) else 0) - (if i ∈ S01 then (1 : ℤ) else 0) := by
        intro i
        simp only [S10, S01, Finset.mem_filter, Finset.mem_univ, true_and]
        cases s (prevIdx i) <;> cases s i <;> simp
      simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_boole, Finset.filter_mem_eq_inter,
        Finset.univ_inter]
    rw [hval] at hdiff
    omega
  rw [hdef_card, ← hS01]
  omega

def runSpace {n : ℕ} (s : Fin n → Bool) : Submodule (ZMod 2) (Fin n → ZMod 2) :=
  { carrier := {x | (∀ i, s i = false → x i = 0) ∧
      (∀ i, s i = true → s (nextIdx i) = true → x i = x (nextIdx i))}
    zero_mem' := ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩, add_mem' := fun ha hb =>
      ⟨fun i hi => by simp [ha.1 i hi, hb.1 i hi],
       fun i h1 h2 => by simp [ha.2 i h1 h2, hb.2 i h1 h2]⟩
    smul_mem' := fun c _ ha =>
      ⟨fun i hi => by simp [ha.1 i hi],
       fun i h1 h2 => by simp [ha.2 i h1 h2]⟩ }

def runSpaceErased {n : ℕ} (s : Fin n → Bool) (K : Finset (Fin n)) :
    Submodule (ZMod 2) (Fin n → ZMod 2) :=
  { carrier := {x | x ∈ runSpace s ∧ ∀ j ∈ K, x j = 0}
    zero_mem' := ⟨(runSpace s).zero_mem, fun _ _ => rfl⟩, add_mem' := fun ha hb =>
      ⟨(runSpace s).add_mem ha.1 hb.1, fun j hj => by simp [ha.2 j hj, hb.2 j hj]⟩
    smul_mem' := fun c _ ha =>
      ⟨(runSpace s).smul_mem c ha.1, fun j hj => by simp [ha.2 j hj]⟩ }

def walkBack {n : ℕ} (s : Fin n → Bool) : ℕ → Fin n → Fin n
  | 0, i => i
  | k + 1, i => if s (prevIdx i) = true then walkBack s k (prevIdx i) else i

lemma walkBack_mem {n : ℕ} (s : Fin n → Bool) (k : ℕ) (i : Fin n) (hi : s i = true) :
    s (walkBack s k i) = true := by
  induction k generalizing i with
  | zero => exact hi
  | succ k ih =>
    simp only [walkBack]
    split_ifs with hp
    · exact ih (prevIdx i) hp
    · exact hi

lemma walkBack_const {n : ℕ} (s : Fin n → Bool) (x : Fin n → ZMod 2) (hx : x ∈ runSpace s) :
    ∀ (k : ℕ) (i : Fin n), s i = true → x (walkBack s k i) = x i := by
  intro k
  induction k with
  | zero => intro i _; rfl
  | succ k ih =>
    intro i hi
    simp only [walkBack]
    split_ifs with hp
    · rw [ih (prevIdx i) hp]
      have h1 := hx.2 (prevIdx i) hp (by rwa [nextIdx_prevIdx])
      rw [nextIdx_prevIdx] at h1
      exact h1
    · rfl

lemma walkBack_isStart {n : ℕ} (s : Fin n → Bool) (hnotall : ∃ z : Fin n, s z = false)
    (i : Fin n) (hi : s i = true) :
    isStart s (walkBack s n i) = true := by
  have hstep : ∀ k (j : Fin n), s j = true →
      (∃ m ≤ k, s (prevIdx^[m + 1] j) = false) → isStart s (walkBack s k j) = true := by
    intro k
    induction k with
    | zero =>
      intro j hj ⟨m, hm, hfalse⟩
      have hm0 : m = 0 := by omega
      subst hm0
      simp only [walkBack, isStart, hj, Bool.true_and]
      simpa using hfalse
    | succ k ih =>
      intro j hj ⟨m, hm, hfalse⟩
      simp only [walkBack]
      split_ifs with hp
      · apply ih (prevIdx j) hp
        cases m with
        | zero =>
          rw [Function.iterate_one] at hfalse
          exact absurd (hp.symm.trans hfalse) (by decide)
        | succ m =>
          refine ⟨m, by omega, ?_⟩
          rwa [← Function.iterate_succ_apply prevIdx (m + 1) j]
      · simp only [isStart, hj, Bool.true_and]
        cases hsp : s (prevIdx j)
        · rfl
        · exact absurd hsp hp
  apply hstep n i hi
  obtain ⟨z, hz⟩ := hnotall
  let d : ℕ := (i.val + n - z.val) % n
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hd_lt : d < n := Nat.mod_lt _ hn
  have hiter : ∀ k (j : Fin n), (prevIdx^[k] j).val = (j.val + k * (n - 1)) % n := by
    intro k
    induction k with
    | zero => intro j; simp [Nat.mod_eq_of_lt j.isLt]
    | succ k ih =>
      intro j
      rw [Function.iterate_succ_apply']
      simp only [prevIdx]
      rw [ih]
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      congr 1
      ring
  have hd_pos : 0 < d := by
    by_contra h0
    have hd0 : d = 0 := by omega
    have hiz : i = z := by
      ext
      have hi_lt := i.isLt
      have hz_lt := z.isLt
      dsimp only [d] at hd0
      have hdiv : n ∣ i.val + n - z.val := Nat.dvd_of_mod_eq_zero hd0
      obtain ⟨q, hq⟩ := hdiv
      have hq1 : q = 1 := by
        rcases q with _ | _ | q
        · omega
        · rfl
        · have : n * (q + 1 + 1) = n * q + 2 * n := by ring
          omega
      rw [hq1, mul_one] at hq
      omega
    rw [hiz] at hi
    exact Bool.noConfusion (hi.symm.trans hz)
  refine ⟨d - 1, by omega, ?_⟩
  have hreach : prevIdx^[d - 1 + 1] i = z := by
    ext
    rw [Nat.sub_add_cancel hd_pos, hiter]
    have h1 : (i.val + d * (n - 1)) % n = z.val := by
      have hmod1 : (i.val + n - z.val) % n = d := rfl
      have hmod2 : (d + z.val) % n = i.val := by
        rw [← hmod1, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        have hsum : i.val + n - z.val + z.val = i.val + n := by have := z.isLt; omega
        rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
      have hsub : i.val + d * (n - 1) + d = i.val + d * n := by
        have : d * (n - 1) + d = d * n := by
          cases n with
          | zero => omega
          | succ m => simp [Nat.mul_succ]
        omega
      have h2 : (i.val + d * (n - 1) + d) % n = i.val := by
        rw [hsub, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt i.isLt]
      have h3 : ((i.val + d * (n - 1)) % n + d) % n = (z.val + d) % n := by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, h2, add_comm, hmod2]
      have hlt1 : (i.val + d * (n - 1)) % n < n := Nat.mod_lt _ hn
      have hlt2 : z.val < n := z.isLt
      have hq1 := Nat.div_add_mod ((i.val + d * (n - 1)) % n + d) n
      have hq2 := Nat.div_add_mod (z.val + d) n
      have hqeq : ((i.val + d * (n - 1)) % n + d) / n = (z.val + d) / n := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have : n * (((i.val + d * (n - 1)) % n + d) / n) + n ≤ n * ((z.val + d) / n) := by
            nlinarith
          omega
        · have : n * ((z.val + d) / n) + n ≤ n * (((i.val + d * (n - 1)) % n + d) / n) := by
            nlinarith
          omega
      have hmul : n * (((i.val + d * (n - 1)) % n + d) / n) = n * ((z.val + d) / n) :=
        congrArg (n * ·) hqeq
      omega
    exact h1
  rw [hreach, hz]

lemma walkBack_of_start {n : ℕ} (s : Fin n → Bool) (j : Fin n) (hj : isStart s j = true) :
    ∀ k, walkBack s k j = j := by
  intro k
  cases k with
  | zero => rfl
  | succ k =>
    simp only [isStart, Bool.and_eq_true, Bool.not_eq_true'] at hj
    simp [walkBack, hj.2]

lemma walkBack_next {n : ℕ} (s : Fin n → Bool) (hnotall : ∃ z : Fin n, s z = false)
    (i : Fin n) (h1 : s i = true) (h2 : s (nextIdx i) = true) :
    walkBack s n (nextIdx i) = walkBack s n i := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hst := walkBack_isStart s hnotall i h1
  have hiter : ∀ k (a : Fin n), walkBack s (k + 1) (nextIdx a) =
      if s a = true then walkBack s k a else nextIdx a := by
    intro k a
    simp [walkBack, prevIdx_nextIdx]
  have hwn : walkBack s n (nextIdx i) = walkBack s (n - 1) i := by
    cases n with
    | zero => omega
    | succ m =>
      rw [hiter m i, if_pos h1]
      rfl
  rw [hwn]
  have hstep : ∀ k (a : Fin n), isStart s (walkBack s k a) = true →
      walkBack s (k + 1) a = walkBack s k a := by
    intro k
    induction k with
    | zero =>
      intro a ha
      exact walkBack_of_start s a ha 1
    | succ k ih =>
      intro a ha
      change (if s (prevIdx a) = true then walkBack s (k + 1) (prevIdx a) else a) =
        (if s (prevIdx a) = true then walkBack s k (prevIdx a) else a)
      simp only [walkBack] at ha
      split_ifs with hp
      · rw [if_pos hp] at ha
        exact ih (prevIdx a) ha
      · rfl
  have hst' : isStart s (walkBack s (n - 1) i) = true := by
    have hnot : ∃ z, s z = false := hnotall
    obtain ⟨z, hz⟩ := hnot
    have hne : walkBack s (n - 1) i ≠ z := fun he => by
      have htrue := walkBack_mem s (n - 1) i h1
      rw [he, hz] at htrue
      exact Bool.noConfusion htrue
    have hstep2 : ∀ k (j : Fin n), s j = true →
        (∃ m ≤ k, s (prevIdx^[m + 1] j) = false) → isStart s (walkBack s k j) = true := by
      intro k
      induction k with
      | zero =>
        intro j hj ⟨m, hm, hfalse⟩
        have hm0 : m = 0 := by omega
        subst hm0
        simp only [walkBack, isStart, hj, Bool.true_and]
        simpa using hfalse
      | succ k ih =>
        intro j hj ⟨m, hm, hfalse⟩
        simp only [walkBack]
        split_ifs with hp
        · apply ih (prevIdx j) hp
          cases m with
          | zero =>
            rw [Function.iterate_one] at hfalse
            exact absurd (hp.symm.trans hfalse) (by decide)
          | succ m =>
            refine ⟨m, by omega, ?_⟩
            rwa [← Function.iterate_succ_apply prevIdx (m + 1) j]
        · simp only [isStart, hj, Bool.true_and]
          cases hsp : s (prevIdx j)
          · rfl
          · exact absurd hsp hp
    apply hstep2 (n - 1) i h1
    let d : ℕ := (i.val + n - z.val) % n
    have hd_lt : d < n := Nat.mod_lt _ hn
    have hd_pos : 0 < d := by
      by_contra h0
      have hd0 : d = 0 := by omega
      have hiz : i = z := by
        ext
        have hi_lt := i.isLt
        have hz_lt := z.isLt
        dsimp only [d] at hd0
        obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hd0
        have hq1 : q = 1 := by
          rcases q with _ | _ | q
          · omega
          · rfl
          · have : n * (q + 1 + 1) = n * q + 2 * n := by ring
            omega
        rw [hq1, mul_one] at hq
        omega
      rw [hiz] at h1
      exact Bool.noConfusion (h1.symm.trans hz)
    have hiter_val : ∀ k (j : Fin n), (prevIdx^[k] j).val = (j.val + k * (n - 1)) % n := by
      intro k
      induction k with
      | zero => intro j; simp [Nat.mod_eq_of_lt j.isLt]
      | succ k ih =>
        intro j
        rw [Function.iterate_succ_apply']
        simp only [prevIdx]
        rw [ih, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        congr 1; ring
    have hd_le : d - 1 ≤ n - 1 := by omega
    refine ⟨d - 1, hd_le, ?_⟩
    have hreach : prevIdx^[d - 1 + 1] i = z := by
      ext
      rw [Nat.sub_add_cancel hd_pos, hiter_val]
      have hmod1 : (i.val + n - z.val) % n = d := rfl
      have hmod2 : (d + z.val) % n = i.val := by
        rw [← hmod1, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        have hsum : i.val + n - z.val + z.val = i.val + n := by have := z.isLt; omega
        rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
      have hsub : i.val + d * (n - 1) + d = i.val + d * n := by
        cases n with
        | zero => omega
        | succ m => simp [Nat.mul_succ]; omega
      have h2 : (i.val + d * (n - 1) + d) % n = i.val := by
        rw [hsub, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt i.isLt]
      have h3 : ((i.val + d * (n - 1)) % n + d) % n = (z.val + d) % n := by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, h2, add_comm, hmod2]
      have hlt1 : (i.val + d * (n - 1)) % n < n := Nat.mod_lt _ hn
      have hlt2 : z.val < n := z.isLt
      have hq1 := Nat.div_add_mod ((i.val + d * (n - 1)) % n + d) n
      have hq2 := Nat.div_add_mod (z.val + d) n
      have hqeq : ((i.val + d * (n - 1)) % n + d) / n = (z.val + d) / n := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have : n * (((i.val + d * (n - 1)) % n + d) / n) + n ≤ n * ((z.val + d) / n) := by nlinarith
          omega
        · have : n * ((z.val + d) / n) + n ≤ n * (((i.val + d * (n - 1)) % n + d) / n) := by nlinarith
          omega
      have hmul : n * (((i.val + d * (n - 1)) % n + d) / n) = n * ((z.val + d) / n) :=
        congrArg (n * ·) hqeq
      omega
    rw [hreach, hz]
  have hback := hstep (n - 1) i hst'
  rw [Nat.sub_add_cancel hn] at hback
  exact hback.symm

def runSpaceEquiv {n : ℕ} (s : Fin n → Bool) (hnotall : ∃ z : Fin n, s z = false)
    (K : Finset (Fin n)) (hK : K ⊆ runStarts s) :
    runSpaceErased s K ≃ₗ[ZMod 2] ({j : Fin n // j ∈ runStarts s \ K} → ZMod 2) :=
  { toFun := fun x j => x.1 j.1
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    invFun := fun c =>
      ⟨fun i => if hi : s i = true then
        if hmem : walkBack s n i ∈ runStarts s \ K then c ⟨walkBack s n i, hmem⟩ else 0
        else 0,
       ⟨⟨fun i hi => by simp [hi],
         fun i h1 h2 => by
           simp only [h1, h2, ↓reduceDIte]
           rw [walkBack_next s hnotall i h1 h2]⟩,
        fun j hj => by
          have hjS : j ∈ runStarts s := hK hj
          have hst : isStart s j = true := (Finset.mem_filter.1 hjS).2
          have hjt : s j = true := by simp only [isStart, Bool.and_eq_true] at hst; exact hst.1
          simp [hjt, walkBack_of_start s j hst, hj]⟩⟩
    left_inv := fun ⟨x, hx⟩ => by
      apply Subtype.ext
      ext i
      by_cases hi : s i = true
      · simp only [hi, ↓reduceDIte]
        have hst : walkBack s n i ∈ runStarts s :=
          Finset.mem_filter.2 ⟨Finset.mem_univ _, walkBack_isStart s hnotall i hi⟩
        have hval := walkBack_const s x hx.1 n i hi
        by_cases hmem : walkBack s n i ∈ K
        · simp only [Finset.mem_sdiff, hmem, not_true_eq_false, and_false, ↓reduceDIte]
          rw [← hval, hx.2 _ hmem]
        · have hsm : walkBack s n i ∈ runStarts s \ K := Finset.mem_sdiff.2 ⟨hst, hmem⟩
          simp only [hsm, ↓reduceDIte]
          exact hval
      · have hif : s i = false := Bool.eq_false_iff.2 hi
        simp [hif, hx.1.1 i hif]
    right_inv := fun c => by
      ext ⟨j, hj⟩
      have hjS : j ∈ runStarts s := (Finset.mem_sdiff.1 hj).1
      have hst : isStart s j = true := (Finset.mem_filter.1 hjS).2
      have hjt : s j = true := by simp only [isStart, Bool.and_eq_true] at hst; exact hst.1
      simp only [hjt, ↓reduceDIte, walkBack_of_start s j hst, hj] }

def runCol {n m : ℕ} (col : Fin n → Fin m → ZMod 2) (s : Fin n → Bool) (j : Fin n) :
    Fin m → ZMod 2 :=
  fun b => ∑ i ∈ Finset.univ.filter (fun i : Fin n => s i = true ∧ walkBack s n i = j), col i b

def chkKernel {n m : ℕ} (col : Fin n → Fin m → ZMod 2) (s : Fin n → Bool) (K : Finset (Fin n)) :
    Submodule (ZMod 2) (Fin n → ZMod 2) :=
  { carrier := {x | x ∈ runSpaceErased s K ∧ ∀ b : Fin m, ∑ i : Fin n, col i b * x i = 0}
    zero_mem' := ⟨(runSpaceErased s K).zero_mem, fun _ => by simp⟩, add_mem' := fun ha hb =>
      ⟨(runSpaceErased s K).add_mem ha.1 hb.1, fun b => by
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, ha.2 b, hb.2 b, add_zero]⟩
    smul_mem' := fun c _ ha =>
      ⟨(runSpaceErased s K).smul_mem c ha.1, fun b => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm, ← Finset.mul_sum, ha.2 b,
          mul_zero]⟩ }

def runColSet {n m : ℕ} (col : Fin n → Fin m → ZMod 2) (s : Fin n → Bool) (K : Finset (Fin n)) :
    Set (Fin m → ZMod 2) :=
  (fun j => runCol col s j) '' ((runStarts s \ K : Finset (Fin n)) : Set (Fin n))

lemma finrank_chkKernel {n m : ℕ} (col : Fin n → Fin m → ZMod 2)
    (s : Fin n → Bool) (hnotall : ∃ z : Fin n, s z = false)
    (K : Finset (Fin n)) (hK : K ⊆ runStarts s) :
    Module.finrank (ZMod 2) (chkKernel col s K) +
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (runColSet col s K)) =
    (runStarts s \ K).card := by
  let A := {j : Fin n // j ∈ runStarts s \ K}
  let Φ : (A → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2) :=
    { toFun := fun c b => ∑ j : A, c j * runCol col s j.1 b
      map_add' := fun c1 c2 => by
        ext b
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun r c => by
        ext b
        simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, RingHom.id_apply] }
  have hrange : LinearMap.range Φ = Submodule.span (ZMod 2) (runColSet col s K) := by
    apply le_antisymm
    · rintro _ ⟨c, rfl⟩
      have hsum : Φ c = ∑ j : A, c j • runCol col s j.1 := by
        ext b
        simp [Φ, Finset.sum_apply]
      rw [hsum]
      exact Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨j.1, j.2, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨j, hj, rfl⟩
      refine ⟨Pi.single ⟨j, hj⟩ 1, ?_⟩
      ext b
      simp [Φ, Pi.single_apply]
  let e := runSpaceEquiv s hnotall K hK
  have hker_eq : (chkKernel col s K).comap (runSpaceErased s K).subtype =
      (LinearMap.ker Φ).comap e.toLinearMap := by
    ext ⟨x, hx⟩
    simp only [Submodule.mem_comap, Submodule.coe_subtype, chkKernel, Submodule.mem_mk,
      AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq, hx, true_and,
      LinearMap.mem_ker, funext_iff, Pi.zero_apply]
    refine forall_congr' fun b => ?_
    have hsum : ∑ i : Fin n, col i b * x i = Φ (e ⟨x, hx⟩) b := by
      have hzero : ∀ i : Fin n,
          col i b * x i =
            if s i = true ∧ walkBack s n i ∈ runStarts s \ K then
              x (walkBack s n i) * col i b
            else 0 := by
        intro i
        by_cases hi : s i = true
        · have hst : walkBack s n i ∈ runStarts s :=
            Finset.mem_filter.2 ⟨Finset.mem_univ _, walkBack_isStart s hnotall i hi⟩
          have hval := walkBack_const s x hx.1 n i hi
          by_cases hmem : walkBack s n i ∈ K
          · rw [if_neg (by simp [hmem]), ← hval, hx.2 _ hmem, mul_zero]
          · rw [if_pos ⟨hi, Finset.mem_sdiff.2 ⟨hst, hmem⟩⟩, hval, mul_comm]
        · have hif : s i = false := Bool.eq_false_iff.2 hi
          rw [if_neg (by simp [hif]), hx.1.1 i hif, mul_zero]
      simp_rw [hzero]
      rw [← Finset.sum_filter]
      have hbi : (Finset.univ.filter fun i : Fin n => s i = true ∧ walkBack s n i ∈ runStarts s \ K) =
          Finset.univ.biUnion (fun j : A =>
            Finset.univ.filter fun i : Fin n => s i = true ∧ walkBack s n i = j.1) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
        exact ⟨fun ⟨h1, h2⟩ => ⟨⟨walkBack s n i, h2⟩, h1, rfl⟩,
          fun ⟨j, h1, h2⟩ => ⟨h1, h2 ▸ j.2⟩⟩
      rw [hbi, Finset.sum_biUnion]
      · refine Finset.sum_congr rfl fun j _ => ?_
        dsimp only [runCol, e, runSpaceEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [(Finset.mem_filter.1 hi).2.2]
      · intro j1 _ j2 _ hne
        simp only [Function.onFun, Finset.disjoint_left]
        intro i h1 h2
        exact hne (Subtype.ext ((Finset.mem_filter.1 h1).2.2.symm.trans (Finset.mem_filter.1 h2).2.2))
    rw [hsum]
    exact Iff.rfl
  have hfr_ker : Module.finrank (ZMod 2) (chkKernel col s K) =
      Module.finrank (ZMod 2) (LinearMap.ker Φ) := by
    have hle : chkKernel col s K ≤ runSpaceErased s K := fun _ hx => hx.1
    have h1 : ((chkKernel col s K).comap (runSpaceErased s K).subtype).map
        (runSpaceErased s K).subtype = chkKernel col s K := by
      rw [Submodule.map_comap_subtype, inf_eq_right.2 hle]
    rw [← h1, Submodule.finrank_map_subtype_eq, hker_eq]
    have h2 : ((LinearMap.ker Φ).comap e.toLinearMap).map e.toLinearMap = LinearMap.ker Φ := by
      rw [Submodule.map_comap_eq_of_surjective e.surjective]
    conv_rhs => rw [← h2]
    exact (LinearEquiv.finrank_map_eq e ((LinearMap.ker Φ).comap e.toLinearMap)).symm
  have hrn := LinearMap.finrank_range_add_finrank_ker Φ
  rw [hrange, ← hfr_ker, Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hrn
  omega

def isMixed {n : ℕ} (s : Fin n → Bool) : Bool :=
  decide (∀ b : Fin 2, ∃ i : Fin n, i.val % 2 = b.val ∧ s i = true)

def validPair {n : ℕ} (h : ℕ) (mixedOnly : Bool) (cfg : Fin n → Bool × Bool) : Prop :=
  let s := fun i => (cfg i).1
  let e := fun i => (cfg i).2
  (∃ z : Fin n, s z = false) ∧
  (∀ i : Fin n, e i = true → isStart s i = true) ∧
  (defectSet s).card / 2 + (Finset.univ.filter fun i : Fin n => e i = true).card ≤ h ∧
  (mixedOnly = true → isMixed s = true)

lemma good_card_eq_ie (p m h t : ℕ) (hp : 0 < p) (ht : 10 * (h + 1) ≤ t)
    (H : Fin (2 * p) → Fin m → ZMod 2) (mixedOnly : Bool) :
    let n := 2 * p * t
    let W := Fin n → ZMod 2
    letI : Fintype (Submodule (ZMod 2) W) := Fintype.ofFinite _
    let col : Fin n → Fin m → ZMod 2 :=
      fun i => H ⟨i.val % (2 * p), Nat.mod_lt _ (Nat.mul_pos (Nat.succ_pos 1) hp)⟩
    let good : Submodule (ZMod 2) W → Prop := fun U =>
      Module.finrank (ZMod 2) U = p * t - h ∧
      (∀ x ∈ U, ∀ b : Fin m, (∑ i, col i b * x i) = 0) ∧
      (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (nextIdx i) = x (nextIdx i) * y i) ∧
      (mixedOnly = true → ∀ b : Fin 2, ∃ i : Fin n, i.val % 2 = b.val ∧ ∃ x ∈ U, x i ≠ 0)
    (((Finset.univ.filter good).card : ℕ) : ℚ) =
    ∑ cfg ∈ Finset.univ.filter (validPair (n := n) h mixedOnly),
      let s := fun i => (cfg i).1
      let K := Finset.univ.filter fun i : Fin n => (cfg i).2 = true
      let J := (defectSet s).card / 2
      let rk := Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (runColSet col s K))
      (-1 : ℚ) ^ K.card *
        (if J + K.card + rk ≤ h then
          (qBinPoly (J + K.card + rk) (h - (J + K.card + rk))).eval ((2 : ℚ) ^ (p * t))
        else 0) := by
  intro n W col good
  letI : Fintype (Submodule (ZMod 2) W) := Fintype.ofFinite _
  have hn : 0 < n := by
    have : 0 < t := by omega
    positivity
  have hpt : h + 2 ≤ p * t := by
    have : 10 * (h + 1) ≤ p * t := le_trans ht (Nat.le_mul_of_pos_left t hp)
    omega
  let suppOf : Submodule (ZMod 2) W → (Fin n → Bool) :=
    fun U i => decide (∃ x ∈ U, x i ≠ 0)
  let Sgood := Finset.univ.filter fun s : Fin n → Bool =>
    (∃ z : Fin n, s z = false) ∧ (defectSet s).card / 2 ≤ h ∧
    (mixedOnly = true → isMixed s = true)
  have hsupp_mem : ∀ U : Submodule (ZMod 2) W, good U → suppOf U ∈ Sgood := by
    intro U hU
    have hnotall : ∃ z : Fin n, suppOf U z = false := by
      obtain ⟨z, hz⟩ := supp_ne_all hn U hU.2.2.1 (by rw [hU.1]; omega)
      refine ⟨z, ?_⟩
      simp only [suppOf, decide_eq_false_iff_not, not_exists, not_and, not_not]
      exact hz
    have hUle : U ≤ runSpace (suppOf U) := by
      intro x hx
      refine ⟨fun i hi => ?_, fun i h1 h2 => ?_⟩
      · simp only [suppOf, decide_eq_false_iff_not, not_exists, not_and, not_not] at hi
        exact hi x hx
      · simp only [suppOf, decide_eq_true_eq] at h1 h2
        exact iso_const_on_adj U hU.2.2.1 i h1 h2 x hx
    have hfr_le : p * t - h ≤ (runStarts (suppOf U)).card := by
      rw [← hU.1]
      have h1 : Module.finrank (ZMod 2) U ≤ Module.finrank (ZMod 2) (runSpaceErased (suppOf U) ∅) :=
        Submodule.finrank_mono fun x hx => ⟨hUle hx, by simp⟩
      have h2 : Module.finrank (ZMod 2) (runSpaceErased (suppOf U) ∅) = (runStarts (suppOf U)).card := by
        rw [LinearEquiv.finrank_eq (runSpaceEquiv (suppOf U) hnotall ∅ (Finset.empty_subset _)),
          Module.finrank_fintype_fun_eq_card, Fintype.card_coe, Finset.sdiff_empty]
      omega
    have htd := two_mul_starts_add_defects (suppOf U)
    have hJle : (defectSet (suppOf U)).card / 2 ≤ h := by
      have hn_eq : n = 2 * (p * t) := by dsimp only [n]; ring
      omega
    have hmix : mixedOnly = true → isMixed (suppOf U) = true := by
      intro hm
      simp only [isMixed, decide_eq_true_eq]
      intro b
      obtain ⟨i, hi, x, hx, hxi⟩ := hU.2.2.2 hm b
      exact ⟨i, hi, by simp only [suppOf, decide_eq_true_eq]; exact ⟨x, hx, hxi⟩⟩
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hnotall, hJle, hmix⟩
  have hpartU : (Finset.univ.filter good).card =
      ∑ s ∈ Sgood, (Finset.univ.filter fun U : Submodule (ZMod 2) W =>
        good U ∧ suppOf U = s).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext U
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => ⟨suppOf U, hsupp_mem U h, h, rfl⟩, fun ⟨_, _, h, _⟩ => h⟩
    · intro s1 _ s2 _ hne
      simp only [Function.onFun, Finset.disjoint_left]
      intro U h1 h2
      exact hne ((Finset.mem_filter.1 h1).2.2.symm.trans (Finset.mem_filter.1 h2).2.2)
  change (((Finset.univ.filter good).card : ℕ) : ℚ) = _
  rw [hpartU, Nat.cast_sum]
  have hper_s : ∀ s ∈ Sgood,
      (((Finset.univ.filter fun U : Submodule (ZMod 2) W => good U ∧ suppOf U = s).card : ℕ) : ℚ) =
      ∑ K ∈ (runStarts s).powerset.filter (fun K => (defectSet s).card / 2 + K.card ≤ h),
        let J := (defectSet s).card / 2
        let rk := Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (runColSet col s K))
        (-1 : ℚ) ^ K.card *
          (if J + K.card + rk ≤ h then
            (qBinPoly (J + K.card + rk) (h - (J + K.card + rk))).eval ((2 : ℚ) ^ (p * t))
          else 0) := by
    intro s hs
    obtain ⟨hnotall, hJle, hmix⟩ := (Finset.mem_filter.1 hs).2
    let A0 := Finset.univ.filter fun U : Submodule (ZMod 2) W =>
      U ≤ chkKernel col s ∅ ∧ Module.finrank (ZMod 2) U = p * t - h
    have hchar : (Finset.univ.filter fun U : Submodule (ZMod 2) W => good U ∧ suppOf U = s) =
        A0.filter fun U => ∀ j ∈ runStarts s, ∃ x ∈ U, x j ≠ 0 := by
      ext U
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, A0]
      constructor
      · rintro ⟨hU, rfl⟩
        refine ⟨⟨fun x hx => ⟨⟨⟨fun i hi => ?_, fun i h1 h2 => ?_⟩, by simp⟩, hU.2.1 x hx⟩, hU.1⟩,
          fun j hj => ?_⟩
        · simp only [suppOf, decide_eq_false_iff_not, not_exists, not_and, not_not] at hi
          exact hi x hx
        · simp only [suppOf, decide_eq_true_eq] at h1 h2
          exact iso_const_on_adj U hU.2.2.1 i h1 h2 x hx
        · have hst := (Finset.mem_filter.1 hj).2
          have hjt : suppOf U j = true := (Eq.mp (Bool.and_eq_true _ _) hst).1
          simpa [suppOf] using hjt
      · rintro ⟨⟨hUle, hUdim⟩, hhit⟩
        have hsupp_eq : suppOf U = s := by
          ext i
          cases hsi : s i
          · simp only [suppOf, decide_eq_false_iff_not, not_exists, not_and, not_not]
            exact fun x hx => (hUle hx).1.1.1 i hsi
          · simp only [suppOf, decide_eq_true_eq]
            have hst : walkBack s n i ∈ runStarts s :=
              Finset.mem_filter.2 ⟨Finset.mem_univ _, walkBack_isStart s hnotall i hsi⟩
            obtain ⟨x, hx, hxj⟩ := hhit _ hst
            exact ⟨x, hx, by rwa [← walkBack_const s x (hUle hx).1.1 n i hsi]⟩
        refine ⟨⟨hUdim, fun x hx => (hUle hx).2, fun x hx y hy i => ?_, fun hm b => ?_⟩, hsupp_eq⟩
        · cases hsi : s i
          · rw [(hUle hx).1.1.1 i hsi, (hUle hy).1.1.1 i hsi]; simp
          · cases hsn : s (nextIdx i)
            · rw [(hUle hx).1.1.1 (nextIdx i) hsn, (hUle hy).1.1.1 (nextIdx i) hsn]; simp
            · rw [(hUle hx).1.1.2 i hsi hsn, (hUle hy).1.1.2 i hsi hsn, mul_comm]
        · have hm' := hmix hm
          simp only [isMixed, decide_eq_true_eq] at hm'
          obtain ⟨i, hi, hsi⟩ := hm' b
          rw [← hsupp_eq] at hsi
          simp only [suppOf, decide_eq_true_eq] at hsi
          exact ⟨i, hi, hsi⟩
    rw [hchar]
    have hie : (((A0.filter fun U => ∀ j ∈ runStarts s, ∃ x ∈ U, x j ≠ 0).card : ℕ) : ℚ) =
        ∑ K ∈ (runStarts s).powerset, (-1 : ℚ) ^ K.card *
          (((A0.filter fun U => ∀ j ∈ K, ∀ x ∈ U, x j = 0).card : ℕ) : ℚ) := by
      have h1 : (((A0.filter fun U => ∀ j ∈ runStarts s, ∃ x ∈ U, x j ≠ 0).card : ℕ) : ℚ) =
          ∑ U ∈ A0, ∏ j ∈ runStarts s, (1 - (if ∀ x ∈ U, x j = 0 then (1 : ℚ) else 0)) := by
        rw [Finset.card_filter, Nat.cast_sum]
        refine Finset.sum_congr rfl fun U _ => ?_
        by_cases hall : ∀ j ∈ runStarts s, ∃ x ∈ U, x j ≠ 0
        · rw [if_pos hall, Nat.cast_one]
          refine (Finset.prod_eq_one fun j hj => ?_).symm
          obtain ⟨x, hx, hxj⟩ := hall j hj
          rw [if_neg (fun h => hxj (h x hx)), sub_zero]
        · rw [if_neg hall, Nat.cast_zero]
          push Not at hall
          obtain ⟨j, hj, hxj⟩ := hall
          exact (Finset.prod_eq_zero hj (by rw [if_pos hxj, sub_self])).symm
      rw [h1]
      have hexp : ∀ U ∈ A0,
          ∏ j ∈ runStarts s, (1 - (if ∀ x ∈ U, x j = 0 then (1 : ℚ) else 0)) =
          ∑ K ∈ (runStarts s).powerset,
            (-1 : ℚ) ^ K.card * (if ∀ j ∈ K, ∀ x ∈ U, x j = 0 then (1 : ℚ) else 0) := by
        intro U _
        have hsub : ∀ j : Fin n,
            (1 - (if ∀ x ∈ U, x j = 0 then (1 : ℚ) else 0)) =
            (-(if ∀ x ∈ U, x j = 0 then (1 : ℚ) else 0)) + (1 : ℚ) := fun _ => by ring
        simp_rw [hsub]
        rw [Finset.prod_add]
        refine Finset.sum_congr rfl fun K _ => ?_
        rw [Finset.prod_const_one, mul_one, Finset.prod_neg]
        congr 1
        by_cases hK : ∀ j ∈ K, ∀ x ∈ U, x j = 0
        · rw [if_pos hK]
          exact Finset.prod_eq_one fun j hj => if_pos (hK j hj)
        · rw [if_neg hK]
          push Not at hK
          obtain ⟨j, hj, x, hx, hxj⟩ := hK
          exact Finset.prod_eq_zero hj (if_neg fun h => hxj (h x hx))
      rw [Finset.sum_congr rfl hexp, Finset.sum_comm]
      refine Finset.sum_congr rfl fun K _ => ?_
      rw [← Finset.mul_sum, Finset.sum_boole]
    rw [hie]
    have hK_eval : ∀ K ∈ (runStarts s).powerset,
        (((A0.filter fun U => ∀ j ∈ K, ∀ x ∈ U, x j = 0).card : ℕ) : ℚ) =
        let J := (defectSet s).card / 2
        let rk := Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (runColSet col s K))
        if J + K.card + rk ≤ h then
          (qBinPoly (J + K.card + rk) (h - (J + K.card + rk))).eval ((2 : ℚ) ^ (p * t))
        else 0 := by
      intro K hKmem
      have hKsub : K ⊆ runStarts s := Finset.mem_powerset.1 hKmem
      have hfilt : A0.filter (fun U => ∀ j ∈ K, ∀ x ∈ U, x j = 0) =
          Finset.univ.filter fun U : Submodule (ZMod 2) W =>
            U ≤ chkKernel col s K ∧ Module.finrank (ZMod 2) U = p * t - h := by
        ext U
        simp only [A0, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨⟨hUle, hUdim⟩, hzero⟩
          refine ⟨fun x hx => ⟨⟨(hUle hx).1.1, fun j hj => hzero j hj x hx⟩, (hUle hx).2⟩, hUdim⟩
        · rintro ⟨hUle, hUdim⟩
          refine ⟨⟨fun x hx => ⟨⟨(hUle hx).1.1, by simp⟩, (hUle hx).2⟩, hUdim⟩,
            fun j hj x hx => (hUle hx).1.2 j hj⟩
      rw [hfilt]
      have htd := two_mul_starts_add_defects s
      have hn_eq : n = 2 * (p * t) := by dsimp only [n]; ring
      have heven : 2 ∣ (defectSet s).card := ⟨p * t - (runStarts s).card, by omega⟩
      have hJeq : (runStarts s).card + (defectSet s).card / 2 = p * t := by omega
      have hsd : (runStarts s \ K).card = (runStarts s).card - K.card := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.2 hKsub]
      have hKle : K.card ≤ (runStarts s).card := Finset.card_le_card hKsub
      have hfr := finrank_chkKernel col s hnotall K hKsub
      rw [hsd] at hfr
      set J := (defectSet s).card / 2
      set rk := Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (runColSet col s K))
      by_cases hle : J + K.card + rk ≤ h
      · rw [if_pos hle]
        have hD : Module.finrank (ZMod 2) (chkKernel col s K) = p * t - (J + K.card + rk) := by omega
        have hdle : p * t - h ≤ Module.finrank (ZMod 2) (chkKernel col s K) := by omega
        have hc : Module.finrank (ZMod 2) (chkKernel col s K) - (p * t - h) = h - (J + K.card + rk) := by omega
        rw [card_submodules_le_eq_codim (chkKernel col s K) (p * t - h) hdle, hc, hD,
          qBinPoly_eval (J + K.card + rk) (h - (J + K.card + rk)) (p * t) (by omega)]
      · rw [if_neg hle]
        have hempty : (Finset.univ.filter fun U : Submodule (ZMod 2) W =>
            U ≤ chkKernel col s K ∧ Module.finrank (ZMod 2) U = p * t - h) = ∅ := by
          ext U
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          rintro ⟨hUle, hUdim⟩
          let dK := Module.finrank (ZMod 2) (chkKernel col s K)
          have hmono : p * t - h ≤ dK := hUdim ▸ Submodule.finrank_mono hUle
          have hfr' : dK + rk = (runStarts s).card - K.card := hfr
          have hJeq' : (runStarts s).card + J = p * t := hJeq
          have hpt : h ≤ p * t := by nlinarith
          omega
        simp [hempty]
    rw [Finset.sum_congr rfl fun K hK => by rw [hK_eval K hK]]
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) fun K hK hnot => ?_
    simp only [Finset.mem_filter] at hnot
    have hgt : h < (defectSet s).card / 2 + K.card := by
      have : ¬ ((defectSet s).card / 2 + K.card ≤ h) := fun h' => hnot ⟨hK, h'⟩
      omega
    have hgt2 : ¬ ((defectSet s).card / 2 + K.card +
        Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (runColSet col s K)) ≤ h) := by omega
    simp [hgt2]
  rw [Finset.sum_congr rfl hper_s, Finset.sum_sigma']
  refine Finset.sum_bij
    (fun sk _ i => (sk.1 i, decide (i ∈ sk.2))) ?_ ?_ ?_ ?_
  · intro ⟨s, K⟩ hsk
    simp only [Finset.mem_sigma, Sgood, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_powerset] at hsk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, validPair]
    have hKe : (Finset.univ.filter fun i : Fin n => decide (i ∈ K) = true) = K := by
      ext i; simp
    refine ⟨hsk.1.1, fun i hi => ?_, by rw [hKe]; exact hsk.2.2, hsk.1.2.2⟩
    have hiK : i ∈ K := by simpa using hi
    exact (Finset.mem_filter.1 (hsk.2.1 hiK)).2
  · intro ⟨s1, K1⟩ _ ⟨s2, K2⟩ _ heq
    have hs : s1 = s2 := by
      ext i
      exact congrArg Prod.fst (congrFun heq i)
    subst hs
    congr 1
    ext i
    have h2 := congrArg Prod.snd (congrFun heq i)
    simpa using h2
  · intro cfg hcfg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, validPair] at hcfg
    let s := fun i : Fin n => (cfg i).1
    let K := Finset.univ.filter fun i : Fin n => (cfg i).2 = true
    refine ⟨⟨s, K⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Sgood, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_powerset]
      have hJle : (defectSet s).card / 2 ≤ h := by
        have := hcfg.2.2.1; dsimp only [s]; omega
      refine ⟨⟨hcfg.1, hJle, hcfg.2.2.2⟩, fun i hi => ?_, hcfg.2.2.1⟩
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hcfg.2.1 i (Finset.mem_filter.1 hi).2⟩
    · ext i
      · rfl
      · simp [K]
  · intro ⟨s, K⟩ _
    have hKe : (Finset.univ.filter fun i : Fin n => decide (i ∈ K) = true) = K := by
      ext i; simp
    dsimp only
    rw [hKe]

def pureBlock (p : ℕ) (prevEnd : Bool) : Fin (2 * p) → Bool × Bool :=
  fun u => (if prevEnd then u.val % 2 = 1 else u.val % 2 = 0, false)

def blockIdx {p t : ℕ} (b : Fin t) (u : Fin (2 * p)) : Fin (2 * p * t) :=
  ⟨2 * p * b.val + u.val, by
    have hb : b.val + 1 ≤ t := b.isLt
    have hu : u.val < 2 * p := u.isLt
    have : 2 * p * b.val + 2 * p = 2 * p * (b.val + 1) := by ring
    have : 2 * p * (b.val + 1) ≤ 2 * p * t := Nat.mul_le_mul_left (2 * p) hb
    omega⟩

def blockOf {p t : ℕ} (cfg : Fin (2 * p * t) → Bool × Bool) (b : Fin t) :
    Fin (2 * p) → Bool × Bool :=
  fun u => cfg (blockIdx b u)

def isMarkedBlock {p t : ℕ} (cfg : Fin (2 * p * t) → Bool × Bool) (b : Fin t) : Bool :=
  decide (∃ u : Fin (2 * p),
    let i := blockIdx b u
    (cfg i).2 = true ∨ (cfg (prevIdx i)).1 = (cfg i).1)

lemma markedBlocks_card_le {p t : ℕ} (hp : 0 < p) (cfg : Fin (2 * p * t) → Bool × Bool) :
    (Finset.univ.filter fun b : Fin t => isMarkedBlock cfg b = true).card ≤
      (defectSet (fun i => (cfg i).1)).card +
      (Finset.univ.filter fun i : Fin (2 * p * t) => (cfg i).2 = true).card := by
  let S := defectSet (fun i => (cfg i).1) ∪
    (Finset.univ.filter fun i : Fin (2 * p * t) => (cfg i).2 = true)
  let proj : Fin (2 * p * t) → Fin t := fun i =>
    ⟨i.val / (2 * p), Nat.div_lt_of_lt_mul (by linarith [i.isLt])⟩
  have hsub : (Finset.univ.filter fun b : Fin t => isMarkedBlock cfg b = true) ⊆ S.image proj := by
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, isMarkedBlock,
      decide_eq_true_eq] at hb
    obtain ⟨u, hu⟩ := hb
    refine Finset.mem_image.2 ⟨blockIdx b u, ?_, ?_⟩
    · simp only [S, Finset.mem_union, defectSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hu.symm
    · ext
      simp only [proj, blockIdx]
      rw [Nat.mul_add_div (Nat.mul_pos (Nat.succ_pos 1) hp), Nat.div_eq_of_lt u.isLt, add_zero]
  calc (Finset.univ.filter fun b : Fin t => isMarkedBlock cfg b = true).card
      ≤ (S.image proj).card := Finset.card_le_card hsub
    _ ≤ S.card := Finset.card_image_le
    _ ≤ _ := Finset.card_union_le _ _

lemma unmarked_eq_pure {p t : ℕ} (hp : 0 < p) (ht : 0 < t)
    (cfg : Fin (2 * p * t) → Bool × Bool) (b : Fin t)
    (hu : isMarkedBlock cfg b = false) :
    blockOf cfg b = pureBlock p (cfg (prevIdx (blockIdx b ⟨0, by omega⟩))).1 := by
  have hnot : ∀ u : Fin (2 * p),
      (cfg (blockIdx b u)).2 = false ∧ (cfg (prevIdx (blockIdx b u))).1 ≠ (cfg (blockIdx b u)).1 := by
    intro u
    simp only [isMarkedBlock, decide_eq_false_iff_not, not_exists, not_or] at hu
    exact ⟨Bool.eq_false_iff.2 (hu u).1, (hu u).2⟩
  set pe := (cfg (prevIdx (blockIdx b ⟨0, by omega⟩))).1
  have hfst : ∀ k : ℕ, (hk : k < 2 * p) →
      (cfg (blockIdx b ⟨k, hk⟩)).1 = (if pe then decide (k % 2 = 1) else decide (k % 2 = 0)) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have h0 := (hnot ⟨0, hk⟩).2
      change pe ≠ (cfg (blockIdx b ⟨0, hk⟩)).1 at h0
      cases hpe : pe <;> cases h1 : (cfg (blockIdx b ⟨0, hk⟩)).1 <;> simp_all
    | succ k ih =>
      intro hk
      have hk' : k < 2 * p := Nat.lt_of_succ_lt hk
      have hprev : prevIdx (blockIdx b ⟨k + 1, hk⟩) = blockIdx b ⟨k, hk'⟩ := by
        ext
        have hn : 0 < 2 * p * t := by positivity
        simp only [prevIdx, blockIdx]
        have h1 : 2 * p * b.val + (k + 1) + (2 * p * t - 1) = (2 * p * b.val + k) + 2 * p * t := by
          omega
        have hlt : 2 * p * b.val + k < 2 * p * t := (blockIdx b ⟨k, hk'⟩).isLt
        rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
      have hne := (hnot ⟨k + 1, hk⟩).2
      rw [hprev, ih hk'] at hne
      cases hpe : pe <;> cases h1 : (cfg (blockIdx b ⟨k + 1, hk⟩)).1 <;> simp_all <;> omega
  ext u
  · exact hfst u.val u.isLt
  · exact (hnot u).1

def pureEnd (p : ℕ) (hp : 0 < p) (prevEnd : Bool) : Bool :=
  (pureBlock p prevEnd ⟨2 * p - 1, by omega⟩).1

lemma pureEnd_eq (p : ℕ) (hp : 0 < p) (prevEnd : Bool) :
    pureEnd p hp prevEnd = prevEnd := by
  unfold pureEnd pureBlock
  have hmod : (2 * p - 1) % 2 = 1 := by omega
  cases prevEnd <;> simp [hmod]

abbrev Template (p h : ℕ) :=
  Bool ⊕ Σ s : Fin (2 * h),
    (Fin (s.val + 1) → Fin (2 * p) → Bool × Bool) × (Fin (s.val + 1) → Fin 3)

def clamp3 (x : ℕ) : Fin 3 :=
  if h0 : x = 0 then ⟨0, by decide⟩
  else if h1 : x = 1 then ⟨1, by decide⟩
  else ⟨2, by decide⟩

lemma clamp3_val (x : ℕ) : (clamp3 x).val = min x 2 := by
  unfold clamp3
  split_ifs <;> simp <;> omega

def templateOf {p h t : ℕ} (hp : 0 < p) (ht : 0 < t)
    (cfg : Fin (2 * p * t) → Bool × Bool)
    (hM : (Finset.univ.filter fun b : Fin t => isMarkedBlock cfg b = true).card ≤ 2 * h) :
    Template p h :=
  let M := Finset.univ.filter fun b : Fin t => isMarkedBlock cfg b = true
  if h0 : M.card = 0 then
    Sum.inl (cfg ⟨0, by positivity⟩).1
  else
    let s := M.card
    let e : Fin s ≃o M := M.orderIsoOfFin rfl
    let blocks : Fin s → Fin (2 * p) → Bool × Bool := fun q => blockOf cfg (e q).1
    let gmode : Fin s → Fin 3 := fun q =>
      if hlt : q.val + 1 < s then
        clamp3 ((e ⟨q.val + 1, hlt⟩).1.val - (e q).1.val - 1)
      else
        clamp3 ((e ⟨0, Nat.pos_of_ne_zero h0⟩).1.val + (t - 1 - (e q).1.val))
    Sum.inr ⟨⟨s - 1, by have hM' : M.card ≤ 2 * h := hM; dsimp only [s]; omega⟩,
      (fun q => blocks ⟨q.val, by have := q.isLt; dsimp only [s] at *; omega⟩,
       fun q => gmode ⟨q.val, by have := q.isLt; dsimp only [s] at *; omega⟩)⟩

def templateMinT {p h : ℕ} : Template p h → ℕ
  | Sum.inl _ => 1
  | Sum.inr ⟨s', (_, gmode)⟩ => (s'.val + 1) + ∑ q : Fin (s'.val + 1), (gmode q).val

lemma templateMinT_le {p h : ℕ} (T : Template p h) : templateMinT T ≤ 6 * h + 1 := by
  cases T with
  | inl _ => simp [templateMinT]
  | inr P =>
    rcases P with ⟨s', blocks, gmode⟩
    simp only [templateMinT]
    have hsum : ∑ q : Fin (s'.val + 1), (gmode q).val ≤ ∑ _q : Fin (s'.val + 1), 2 :=
      Finset.sum_le_sum fun q _ => Nat.le_of_lt_succ (gmode q).isLt
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
    have hs : s'.val + 1 ≤ 2 * h := s'.isLt
    omega

lemma templateMinT_pos {p h : ℕ} (T : Template p h) : 0 < templateMinT T := by
  cases T with
  | inl _ => simp [templateMinT]
  | inr P =>
    rcases P with ⟨s', _, _⟩
    simp only [templateMinT]
    omega

def buildFromPos {p t s : ℕ} (hp : 0 < p) (hs : 0 < s)
    (blocks : Fin s → Fin (2 * p) → Bool × Bool)
    (pos : Fin s → Fin t)
    (hmono : StrictMono pos) : Fin (2 * p * t) → Bool × Bool :=
  fun i =>
    let b : Fin t := ⟨i.val / (2 * p), Nat.div_lt_of_lt_mul (by linarith [i.isLt])⟩
    let u : Fin (2 * p) := ⟨i.val % (2 * p), Nat.mod_lt _ (by omega)⟩
    if hmem : ∃ q : Fin s, pos q = b then
      blocks (Classical.choose hmem) u
    else
      let before := Finset.univ.filter fun q : Fin s => pos q < b
      let prevQ : Fin s :=
        if hne : before.Nonempty then
          before.max' hne
        else
          ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩
      pureBlock p (blocks prevQ ⟨2 * p - 1, by omega⟩).1 u

def validGapTuple {s t : ℕ} (gmode : Fin s → Fin 3) (pos : Fin s → Fin t) : Prop :=
  StrictMono pos ∧
  ∀ q : Fin s,
    if hlt : q.val + 1 < s then
      clamp3 ((pos ⟨q.val + 1, hlt⟩).val - (pos q).val - 1) = gmode q
    else
      clamp3 ((pos ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) q.isLt⟩).val + (t - 1 - (pos q).val)) = gmode q

def canonPos {s : ℕ} (gmode : Fin s → Fin 3) :
    Fin s → Fin (s + ∑ q : Fin s, (gmode q).val) :=
  fun q =>
    ⟨q.val + ∑ r ∈ Finset.univ.filter (fun r : Fin s => r.val < q.val), (gmode r).val, by
      have h1 : ∑ r ∈ Finset.univ.filter (fun r : Fin s => r.val < q.val), (gmode r).val ≤
          ∑ r : Fin s, (gmode r).val :=
        Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
      have h2 := q.isLt
      omega⟩

lemma canonPos_valid {s : ℕ} (hs : 0 < s) (gmode : Fin s → Fin 3) :
    validGapTuple gmode (canonPos gmode) := by
  have hmono : StrictMono (canonPos gmode) := by
    intro q1 q2 hlt
    change (canonPos gmode q1).val < (canonPos gmode q2).val
    simp only [canonPos]
    have hsub : (Finset.univ.filter fun r : Fin s => r.val < q1.val) ⊆
        (Finset.univ.filter fun r : Fin s => r.val < q2.val) := by
      intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
      exact lt_trans hr hlt
    have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := fun r : Fin s => (gmode r).val)
      hsub fun _ _ _ => Nat.zero_le _
    have : q1.val < q2.val := hlt
    omega
  refine ⟨hmono, fun q => ?_⟩
  split_ifs with hlt
  · have hdiff : (canonPos gmode ⟨q.val + 1, hlt⟩).val - (canonPos gmode q).val - 1 = (gmode q).val := by
      simp only [canonPos]
      have hfilt : (Finset.univ.filter fun r : Fin s => r.val < q.val + 1) =
          insert q (Finset.univ.filter fun r : Fin s => r.val < q.val) := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · intro h
          rcases Nat.lt_succ_iff_lt_or_eq.1 h with h1 | h2
          · exact Or.inr h1
          · exact Or.inl (Fin.ext h2)
        · rintro (rfl | h)
          · exact Nat.lt_succ_self _
          · exact Nat.lt_succ_of_lt h
      rw [hfilt, Finset.sum_insert (by simp)]
      omega
    rw [hdiff]
    ext
    rw [clamp3_val, Nat.min_eq_left (Nat.le_of_lt_succ (gmode q).isLt)]
  · have hlast : q.val = s - 1 := by have := q.isLt; omega
    have h0 : (canonPos gmode ⟨0, hs⟩).val = 0 := by simp [canonPos]
    have hq : (canonPos gmode q).val = (s - 1) +
        (∑ r : Fin s, (gmode r).val) - (gmode q).val := by
      simp only [canonPos, hlast]
      have hfilt : (Finset.univ.filter fun r : Fin s => r.val < s - 1) = Finset.univ.erase q := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
        constructor
        · intro h he; rw [he] at h; omega
        · intro hne; have := r.isLt
          have : r.val ≠ q.val := fun h => hne (Fin.ext h)
          omega
      have hadd := Finset.add_sum_erase Finset.univ (fun r : Fin s => (gmode r).val) (Finset.mem_univ q)
      rw [hfilt]
      omega
    have hdiff : (canonPos gmode ⟨0, hs⟩).val + ((s + ∑ r : Fin s, (gmode r).val) - 1 - (canonPos gmode q).val) =
        (gmode q).val := by
      rw [h0, hq]
      have hle : (gmode q).val ≤ ∑ r : Fin s, (gmode r).val :=
        Finset.single_le_sum (f := fun r : Fin s => (gmode r).val) (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
      omega
    rw [hdiff]
    ext
    rw [clamp3_val, Nat.min_eq_left (Nat.le_of_lt_succ (gmode q).isLt)]

def gapCountPoly {s : ℕ} (hs : 0 < s) (gmode : Fin s → Fin 3) : Polynomial ℚ :=
  let t0 := s + ∑ q : Fin s, (gmode q).val
  let lastQ : Fin s := ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩
  let fInt := (Finset.univ.filter fun q : Fin s => q.val + 1 < s ∧ (gmode q).val = 2).card
  if (gmode lastQ).val = 0 then
    if fInt = 0 then 0 else choosePoly (t0 + 1 - fInt) (fInt - 1)
  else if (gmode lastQ).val = 1 then
    if fInt = 0 then 0 else Polynomial.C 2 * choosePoly (t0 + 1 - fInt) (fInt - 1)
  else
    choosePoly (t0 - fInt - 1) (fInt + 1) + Polynomial.C 2 * choosePoly (t0 - fInt) fInt

lemma gapCountPoly_natDegree_le {s : ℕ} (hs : 0 < s) (gmode : Fin s → Fin 3) :
    (gapCountPoly hs gmode).natDegree ≤ s := by
  unfold gapCountPoly
  dsimp only
  set fInt := (Finset.univ.filter fun q : Fin s => q.val + 1 < s ∧ (gmode q).val = 2).card
  have hfInt_le : fInt ≤ s - 1 := by
    have hsub : (Finset.univ.filter fun q : Fin s => q.val + 1 < s ∧ (gmode q).val = 2) ⊆
        Finset.univ.erase ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩ := by
      intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      refine Finset.mem_erase.2 ⟨?_, Finset.mem_univ _⟩
      intro he
      have := congrArg Fin.val he
      dsimp at this
      omega
    calc fInt ≤ (Finset.univ.erase (⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩ : Fin s)).card :=
          Finset.card_le_card hsub
      _ = s - 1 := by simp [Finset.card_erase_of_mem]
  split_ifs with h0 h1 h2 h3
  · simp
  · exact (choosePoly_natDegree_le _ _).trans (by omega)
  · simp
  · calc (Polynomial.C (2 : ℚ) * choosePoly _ _).natDegree
        ≤ (Polynomial.C (2 : ℚ)).natDegree + (choosePoly _ _).natDegree := Polynomial.natDegree_mul_le
      _ ≤ 0 + (fInt - 1) := by rw [Polynomial.natDegree_C]; exact Nat.add_le_add_left (choosePoly_natDegree_le _ _) 0
      _ ≤ s := by omega
  · calc (choosePoly _ (fInt + 1) + Polynomial.C (2 : ℚ) * choosePoly _ fInt).natDegree
        ≤ max (choosePoly _ (fInt + 1)).natDegree (Polynomial.C (2 : ℚ) * choosePoly _ fInt).natDegree :=
          Polynomial.natDegree_add_le _ _
      _ ≤ max (fInt + 1) (0 + fInt) := by
          refine max_le_max (choosePoly_natDegree_le _ _) ?_
          calc (Polynomial.C (2 : ℚ) * choosePoly _ fInt).natDegree
              ≤ (Polynomial.C (2 : ℚ)).natDegree + (choosePoly _ fInt).natDegree := Polynomial.natDegree_mul_le
            _ ≤ 0 + fInt := by rw [Polynomial.natDegree_C]; exact Nat.add_le_add_left (choosePoly_natDegree_le _ _) 0
      _ ≤ s := by omega

lemma validGapTuple_card {s t : ℕ} (hs : 0 < s) (gmode : Fin s → Fin 3)
    (ht : s + ∑ q : Fin s, (gmode q).val < t) :
    (((Finset.univ.filter fun pos : Fin s → Fin t => validGapTuple gmode pos).card : ℕ) : ℚ) =
      (gapCountPoly hs gmode).eval (t : ℚ) := by
  let t0 := s + ∑ q : Fin s, (gmode q).val
  let M := t - t0
  have hMpos : 0 < M := by omega
  let lastQ : Fin s := ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩
  let I := Finset.univ.filter fun q : Fin s => q.val + 1 < s ∧ (gmode q).val = 2
  let fInt := I.card
  let eI : Fin fInt ≃ I := (Fintype.equivFinOfCardEq (Fintype.card_coe I)).symm
  have hpos_bij : (Finset.univ.filter fun pos : Fin s → Fin t => validGapTuple gmode pos).card =
      (Finset.univ.filter fun abg : Fin (t + 1) × Fin (t + 1) × (Fin fInt → Fin (M + 1)) =>
        clamp3 (abg.1.val + abg.2.1.val) = gmode lastQ ∧
        abg.1.val + abg.2.1.val + ∑ r : Fin fInt, (abg.2.2 r).val =
          (gmode lastQ).val + M).card := by
    refine Finset.card_bij
      (fun pos hpos =>
        (⟨(pos ⟨0, hs⟩).val, by have := (pos ⟨0, hs⟩).isLt; omega⟩,
         ⟨t - 1 - (pos lastQ).val, by omega⟩,
         fun r =>
           let q := (eI r).1
           have hq := (Finset.mem_filter.1 (eI r).2).2
           have hval := (Finset.mem_filter.1 hpos).2.2 q
           ⟨((pos ⟨q.val + 1, hq.1⟩).val - (pos q).val - 1) - 2, by
             have hmono := (Finset.mem_filter.1 hpos).2.1
             have hsum_le : ∀ (q' : Fin s) (hq' : q'.val + 1 < s),
                 (gmode q').val ≤ (pos ⟨q'.val + 1, hq'⟩).val - (pos q').val - 1 := by
               intro q' hq'
               have hv := (Finset.mem_filter.1 hpos).2.2 q'
               rw [dif_pos hq'] at hv
               have hc := congrArg Fin.val hv
               rw [clamp3_val] at hc
               omega
             have hwrap_le : (gmode lastQ).val ≤ (pos ⟨0, hs⟩).val + (t - 1 - (pos lastQ).val) := by
               have hv := (Finset.mem_filter.1 hpos).2.2 lastQ
               have hnl : ¬ (lastQ.val + 1 < s) := by dsimp [lastQ]; omega
               rw [dif_neg hnl] at hv
               have hc := congrArg Fin.val hv
               rw [clamp3_val] at hc
               omega
             have htele : (pos lastQ).val - (pos ⟨0, hs⟩).val =
                 ∑ j : Fin (s - 1), ((pos ⟨j.val + 1, by omega⟩).val - (pos ⟨j.val, by omega⟩).val) := by
               clear hval hsum_le hwrap_le
               have hgen : ∀ k (hk : k < s),
                   (pos ⟨k, hk⟩).val - (pos ⟨0, hs⟩).val =
                   ∑ j : Fin k, ((pos ⟨j.val + 1, by have := j.isLt; omega⟩).val -
                     (pos ⟨j.val, by have := j.isLt; omega⟩).val) := by
                 intro k
                 induction k with
                 | zero => intro _; simp
                 | succ k ih =>
                   intro hk
                   rw [Fin.sum_univ_castSucc]
                   simp only [Fin.val_castSucc, Fin.val_last]
                   rw [← ih (Nat.lt_of_succ_lt hk)]
                   have hle1 : (pos ⟨0, hs⟩).val ≤ (pos ⟨k, Nat.lt_of_succ_lt hk⟩).val :=
                     hmono.monotone (Fin.mk_le_mk.2 (Nat.zero_le k))
                   have hle2 : (pos ⟨k, Nat.lt_of_succ_lt hk⟩).val ≤ (pos ⟨k + 1, hk⟩).val :=
                     hmono.monotone (Fin.mk_le_mk.2 (Nat.le_succ k))
                   omega
               exact hgen (s - 1) (Nat.sub_lt hs (Nat.succ_pos 0))
             have hsum_all : (pos ⟨0, hs⟩).val + (t - 1 - (pos lastQ).val) +
                 ∑ j : Fin (s - 1), ((pos ⟨j.val + 1, by omega⟩).val - (pos ⟨j.val, by omega⟩).val - 1) =
                 t - s := by
               have hstep : ∀ j : Fin (s - 1),
                   (pos ⟨j.val + 1, by omega⟩).val - (pos ⟨j.val, by omega⟩).val =
                   ((pos ⟨j.val + 1, by omega⟩).val - (pos ⟨j.val, by omega⟩).val - 1) + 1 := by
                 intro j
                 have hlt : (pos ⟨j.val, by omega⟩).val < (pos ⟨j.val + 1, by omega⟩).val :=
                   hmono (Fin.mk_lt_mk.2 (Nat.lt_succ_self j.val))
                 omega
               have hsum1 : ∑ j : Fin (s - 1), ((pos ⟨j.val + 1, by omega⟩).val - (pos ⟨j.val, by omega⟩).val) =
                   (∑ j : Fin (s - 1), ((pos ⟨j.val + 1, by omega⟩).val - (pos ⟨j.val, by omega⟩).val - 1)) + (s - 1) := by
                 rw [Finset.sum_congr rfl fun j _ => hstep j, Finset.sum_add_distrib, Finset.sum_const,
                   Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
               have hle0 : (pos ⟨0, hs⟩).val ≤ (pos lastQ).val :=
                 hmono.monotone (Fin.mk_le_mk.2 (Nat.zero_le _))
               have hleL : (pos lastQ).val < t := (pos lastQ).isLt
               omega
             have hsum_ge : (gmode lastQ).val +
                 (∑ j : Fin (s - 1), (gmode ⟨j.val, by omega⟩).val) +
                 (((pos ⟨q.val + 1, hq.1⟩).val - (pos q).val - 1) - 2) ≤
                 (pos ⟨0, hs⟩).val + (t - 1 - (pos lastQ).val) +
                 ∑ j : Fin (s - 1), ((pos ⟨j.val + 1, by omega⟩).val - (pos ⟨j.val, by omega⟩).val - 1) := by
               have hqlt : q.val < s - 1 := by omega
               let jq : Fin (s - 1) := ⟨q.val, hqlt⟩
               have hterm : ∑ j : Fin (s - 1), (gmode ⟨j.val, by omega⟩).val +
                   (((pos ⟨q.val + 1, hq.1⟩).val - (pos q).val - 1) - 2) ≤
                   ∑ j : Fin (s - 1), ((pos ⟨j.val + 1, by omega⟩).val - (pos ⟨j.val, by omega⟩).val - 1) := by
                 rw [← Finset.add_sum_erase _ _ (Finset.mem_univ jq),
                   ← Finset.add_sum_erase _ (fun j : Fin (s - 1) =>
                     (pos ⟨j.val + 1, by omega⟩).val - (pos ⟨j.val, by omega⟩).val - 1) (Finset.mem_univ jq)]
                 have hrest := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ.erase jq) =>
                   hsum_le ⟨j.val, by have := j.isLt; omega⟩ (by dsimp only; have := j.isLt; omega)
                 have hq_eq : (gmode ⟨jq.val, by omega⟩).val = 2 := hq.2
                 have hq_le := hsum_le q hq.1
                 have hq_fin : (⟨jq.val, by omega⟩ : Fin s) = q := Fin.ext rfl
                 have hq_fin1 : (⟨jq.val + 1, by omega⟩ : Fin s) = ⟨q.val + 1, hq.1⟩ := Fin.ext rfl
                 have hrest' : ∑ x ∈ Finset.univ.erase jq, (gmode ⟨x.val, by omega⟩).val ≤
                     ∑ x ∈ Finset.univ.erase jq, ((pos ⟨x.val + 1, by omega⟩).val - (pos ⟨x.val, by omega⟩).val - 1) := hrest
                 rw [hq_fin] at hq_eq ⊢
                 rw [hq_fin1]
                 omega
               omega
             have hsum_g : (gmode lastQ).val + ∑ j : Fin (s - 1), (gmode ⟨j.val, by omega⟩).val =
                 ∑ q' : Fin s, (gmode q').val := by
               have hsplit : ∑ q' : Fin s, (gmode q').val =
                   (gmode lastQ).val + ∑ q' ∈ Finset.univ.erase lastQ, (gmode q').val :=
                 (Finset.add_sum_erase Finset.univ (fun q' : Fin s => (gmode q').val) (Finset.mem_univ lastQ)).symm
               rw [hsplit]
               congr 1
               refine Finset.sum_bij (fun j _ => ⟨j.val, by omega⟩) ?_ ?_ ?_ ?_
               · intro j _
                 refine Finset.mem_erase.2 ⟨fun he => ?_, Finset.mem_univ _⟩
                 have := congrArg Fin.val he; dsimp [lastQ] at this; have := j.isLt; omega
               · intro j1 _ j2 _ h; exact Fin.ext (by simpa using congrArg Fin.val h)
               · intro q' hq'
                 have hne : q'.val ≠ s - 1 := fun h => (Finset.mem_erase.1 hq').1 (Fin.ext h)
                 exact ⟨⟨q'.val, by have := q'.isLt; omega⟩, Finset.mem_univ _, Fin.ext rfl⟩
               · intro _ _; rfl
             omega⟩)) ?_ ?_ ?_
    · intro pos hpos
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hpos ⊢
      have hmono := hpos.1
      have hwrap := hpos.2 lastQ
      have hnl : ¬ (lastQ.val + 1 < s) := by dsimp [lastQ]; omega
      rw [dif_neg hnl] at hwrap
      refine ⟨hwrap, ?_⟩
      have htele : (pos lastQ).val - (pos ⟨0, hs⟩).val =
          ∑ j : Fin (s - 1), ((pos ⟨j.val + 1, by omega⟩).val - (pos ⟨j.val, by omega⟩).val) := by
        have hgen : ∀ k (hk : k < s),
            (pos ⟨k, hk⟩).val - (pos ⟨0, hs⟩).val =
            ∑ j : Fin k, ((pos ⟨j.val + 1, by have := j.isLt; omega⟩).val -
              (pos ⟨j.val, by have := j.isLt; omega⟩).val) := by
          intro k
          induction k with
          | zero => intro _; simp
          | succ k ih =>
            intro hk
            rw [Fin.sum_univ_castSucc]
            simp only [Fin.val_castSucc, Fin.val_last]
            rw [← ih (Nat.lt_of_succ_lt hk)]
            have hle1 : (pos ⟨0, hs⟩).val ≤ (pos ⟨k, Nat.lt_of_succ_lt hk⟩).val :=
              hmono.monotone (Fin.mk_le_mk.2 (Nat.zero_le k))
            have hle2 : (pos ⟨k, Nat.lt_of_succ_lt hk⟩).val ≤ (pos ⟨k + 1, hk⟩).val :=
              hmono.monotone (Fin.mk_le_mk.2 (Nat.le_succ k))
            omega
        exact hgen (s - 1) (Nat.sub_lt hs (Nat.succ_pos 0))
      have hsum_all : (pos ⟨0, hs⟩).val + (t - 1 - (pos lastQ).val) +
          ∑ j : Fin (s - 1), ((pos ⟨j.val + 1, by omega⟩).val - (pos ⟨j.val, by omega⟩).val - 1) =
          t - s := by
        have hstep : ∀ j : Fin (s - 1),
            (pos ⟨j.val + 1, by omega⟩).val - (pos ⟨j.val, by omega⟩).val =
            ((pos ⟨j.val + 1, by omega⟩).val - (pos ⟨j.val, by omega⟩).val - 1) + 1 := by
          intro j
          have hlt : (pos ⟨j.val, by omega⟩).val < (pos ⟨j.val + 1, by omega⟩).val :=
            hmono (Fin.mk_lt_mk.2 (Nat.lt_succ_self j.val))
          omega
        have hsum1 : ∑ j : Fin (s - 1), ((pos ⟨j.val + 1, by omega⟩).val - (pos ⟨j.val, by omega⟩).val) =
            (∑ j : Fin (s - 1), ((pos ⟨j.val + 1, by omega⟩).val - (pos ⟨j.val, by omega⟩).val - 1)) + (s - 1) := by
          rw [Finset.sum_congr rfl fun j _ => hstep j, Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
        have hle0 : (pos ⟨0, hs⟩).val ≤ (pos lastQ).val :=
          hmono.monotone (Fin.mk_le_mk.2 (Nat.zero_le _))
        have hleL : (pos lastQ).val < t := (pos lastQ).isLt
        omega
      have hsum_g : (gmode lastQ).val + ∑ j : Fin (s - 1), (gmode ⟨j.val, by omega⟩).val =
          ∑ q' : Fin s, (gmode q').val := by
        have hsplit : ∑ q' : Fin s, (gmode q').val =
            (gmode lastQ).val + ∑ q' ∈ Finset.univ.erase lastQ, (gmode q').val :=
          (Finset.add_sum_erase Finset.univ (fun q' : Fin s => (gmode q').val) (Finset.mem_univ lastQ)).symm
        rw [hsplit]
        congr 1
        refine Finset.sum_bij (fun j _ => ⟨j.val, by omega⟩) ?_ ?_ ?_ ?_
        · intro j _
          refine Finset.mem_erase.2 ⟨fun he => ?_, Finset.mem_univ _⟩
          have := congrArg Fin.val he; dsimp [lastQ] at this; have := j.isLt; omega
        · intro j1 _ j2 _ h; exact Fin.ext (by simpa using congrArg Fin.val h)
        · intro q' hq'
          have hne : q'.val ≠ s - 1 := fun h => (Finset.mem_erase.1 hq').1 (Fin.ext h)
          exact ⟨⟨q'.val, by have := q'.isLt; omega⟩, Finset.mem_univ _, Fin.ext rfl⟩
        · intro _ _; rfl
      have hsum_diff : ∑ j : Fin (s - 1), ((pos ⟨j.val + 1, by omega⟩).val - (pos ⟨j.val, by omega⟩).val - 1) =
          (∑ j : Fin (s - 1), (gmode ⟨j.val, by omega⟩).val) +
          ∑ r : Fin fInt, (((pos ⟨(eI r).1.val + 1, (Finset.mem_filter.1 (eI r).2).2.1⟩).val -
            (pos (eI r).1).val - 1) - 2) := by
        have hpart : ∀ j : Fin (s - 1),
            (pos ⟨j.val + 1, by omega⟩).val - (pos ⟨j.val, by omega⟩).val - 1 =
            (gmode ⟨j.val, by omega⟩).val +
            (if (gmode ⟨j.val, by omega⟩).val = 2 then
              ((pos ⟨j.val + 1, by omega⟩).val - (pos ⟨j.val, by omega⟩).val - 1) - 2 else 0) := by
          intro j
          have hv := hpos.2 ⟨j.val, by have := j.isLt; omega⟩
          rw [dif_pos (by dsimp only; have := j.isLt; omega)] at hv
          have hc := congrArg Fin.val hv
          rw [clamp3_val] at hc
          dsimp only at hc
          split_ifs with h2 <;> omega
        rw [Finset.sum_congr rfl fun j _ => hpart j, Finset.sum_add_distrib]
        congr 1
        rw [← Finset.sum_filter]
        refine Finset.sum_bij (fun j hj => eI.symm ⟨⟨j.val, by omega⟩, by
          simp only [I, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨by have := j.isLt; omega, (Finset.mem_filter.1 hj).2⟩⟩) ?_ ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro j1 hj1 j2 hj2 he
          have h1 := congrArg (fun r => (eI r).1.val) he
          simp only [Equiv.apply_symm_apply] at h1
          exact Fin.ext h1
        · intro r _
          have hr := (Finset.mem_filter.1 (eI r).2).2
          refine ⟨⟨(eI r).1.val, by omega⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hr.2⟩, ?_⟩
          apply eI.injective
          simp [Equiv.apply_symm_apply]
        · intro j hj
          simp [Equiv.apply_symm_apply]
      omega
    · intro p1 hp1 p2 hp2 heq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
      have ha : (p1 ⟨0, hs⟩).val = (p2 ⟨0, hs⟩).val := congrArg (fun x => x.1.val) heq
      have hg : ∀ r : Fin fInt,
          let q := (eI r).1
          have hq := (Finset.mem_filter.1 (eI r).2).2
          ((p1 ⟨q.val + 1, hq.1⟩).val - (p1 q).val - 1) - 2 =
          ((p2 ⟨q.val + 1, hq.1⟩).val - (p2 q).val - 1) - 2 := by
        intro r
        have := congrArg (fun x => (x.2.2 r).val) heq
        exact this
      have hind : ∀ k (hk : k < s), (p1 ⟨k, hk⟩).val = (p2 ⟨k, hk⟩).val := by
        intro k
        induction k with
        | zero => intro _; exact ha
        | succ k ih =>
          intro hk
          have hk' : k < s := Nat.lt_of_succ_lt hk
          have h1 := hp1.2 ⟨k, hk'⟩
          have h2 := hp2.2 ⟨k, hk'⟩
          rw [dif_pos hk] at h1 h2
          have hc1 := congrArg Fin.val h1
          have hc2 := congrArg Fin.val h2
          rw [clamp3_val] at hc1 hc2
          have hlt1 : (p1 ⟨k, hk'⟩).val < (p1 ⟨k + 1, hk⟩).val := hp1.1 (Fin.mk_lt_mk.2 (Nat.lt_succ_self k))
          have hlt2 : (p2 ⟨k, hk'⟩).val < (p2 ⟨k + 1, hk⟩).val := hp2.1 (Fin.mk_lt_mk.2 (Nat.lt_succ_self k))
          have hprev := ih hk'
          dsimp only at hc1 hc2
          by_cases hgm : (gmode ⟨k, hk'⟩).val = 2
          · have hmem : (⟨k, hk'⟩ : Fin s) ∈ I := Finset.mem_filter.2 ⟨Finset.mem_univ _, hk, hgm⟩
            have hgr := hg (eI.symm ⟨⟨k, hk'⟩, hmem⟩)
            simp only [Equiv.apply_symm_apply] at hgr
            omega
          · omega
      ext q
      exact hind q.val q.isLt
    · intro ⟨a, b, g⟩ habg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at habg
      let stepGap : Fin s → ℕ := fun q =>
        if hmem : q ∈ I then 2 + (g (eI.symm ⟨q, hmem⟩)).val else (gmode q).val
      have hstepSum : ∑ q ∈ Finset.univ.erase lastQ, stepGap q =
          (∑ q ∈ Finset.univ.erase lastQ, (gmode q).val) + ∑ r : Fin fInt, (g r).val := by
        have hpart : ∀ q ∈ Finset.univ.erase lastQ,
            stepGap q = (gmode q).val +
              if hmem : q ∈ I then (g (eI.symm ⟨q, hmem⟩)).val else 0 := by
          intro q _
          dsimp only [stepGap]
          split_ifs with hmem
          · have := (Finset.mem_filter.1 hmem).2.2; omega
          · omega
        rw [Finset.sum_congr rfl hpart, Finset.sum_add_distrib]
        congr 1
        have hsubI : I ⊆ Finset.univ.erase lastQ := by
          intro q hq
          refine Finset.mem_erase.2 ⟨fun he => ?_, Finset.mem_univ _⟩
          have hq1 := (Finset.mem_filter.1 hq).2.1
          have := congrArg Fin.val he; dsimp [lastQ] at this; omega
        rw [← Finset.sum_subset hsubI (fun q _ hq => dif_neg hq)]
        refine Finset.sum_bij (fun q hq => eI.symm ⟨q, hq⟩) ?_ ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro q1 hq1 q2 hq2 he
          have := congrArg (fun r => (eI r).1) he
          simpa using this
        · intro r _
          exact ⟨(eI r).1, (eI r).2, by simp⟩
        · intro q hq
          simp [hq]
      have hsum_all : a.val + b.val + ∑ q ∈ Finset.univ.erase lastQ, stepGap q = t - s := by
        have h1 : (gmode lastQ).val + ∑ q ∈ Finset.univ.erase lastQ, (gmode q).val =
            ∑ q : Fin s, (gmode q).val :=
          Finset.add_sum_erase Finset.univ (fun q : Fin s => (gmode q).val) (Finset.mem_univ lastQ)
        omega
      let pos : Fin s → Fin t := fun q =>
        ⟨a.val + q.val + ∑ r ∈ Finset.univ.filter (fun r : Fin s => r.val < q.val), stepGap r, by
          have hsub : (Finset.univ.filter fun r : Fin s => r.val < q.val) ⊆ Finset.univ.erase lastQ := by
            intro r hr
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
            refine Finset.mem_erase.2 ⟨fun he => ?_, Finset.mem_univ _⟩
            have := congrArg Fin.val he; dsimp [lastQ] at this; have := q.isLt; omega
          have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := stepGap)
            hsub fun _ _ _ => Nat.zero_le _
          have := q.isLt
          omega⟩
      have hpos_mono : StrictMono pos := by
        intro q1 q2 hlt
        change (pos q1).val < (pos q2).val
        simp only [pos]
        have hsub : (Finset.univ.filter fun r : Fin s => r.val < q1.val) ⊆
            (Finset.univ.filter fun r : Fin s => r.val < q2.val) := by
          intro r hr
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
          exact lt_trans hr hlt
        have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := stepGap)
          hsub fun _ _ _ => Nat.zero_le _
        have : q1.val < q2.val := hlt
        omega
      have hpos_last : (pos lastQ).val = t - 1 - b.val := by
        simp only [pos]
        have hfilt : (Finset.univ.filter fun r : Fin s => r.val < lastQ.val) = Finset.univ.erase lastQ := by
          ext r
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
          constructor
          · intro h he; rw [he] at h; exact Nat.lt_irrefl _ h
          · intro hne
            have h1 : r.val ≠ s - 1 := fun h => hne (Fin.ext h)
            have := r.isLt; dsimp [lastQ]; omega
        rw [hfilt]
        have hle_b : a.val + b.val + ∑ q ∈ Finset.univ.erase lastQ, stepGap q = t - s := hsum_all
        have hlv : lastQ.val = s - 1 := rfl
        rw [hlv]
        omega
      have hpos_diff : ∀ q : Fin s, (hq : q.val + 1 < s) →
          (pos ⟨q.val + 1, hq⟩).val - (pos q).val - 1 = stepGap q := by
        intro q hq
        simp only [pos]
        have hfilt : (Finset.univ.filter fun r : Fin s => r.val < q.val + 1) =
            insert q (Finset.univ.filter fun r : Fin s => r.val < q.val) := by
          ext r
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
          constructor
          · intro h
            rcases Nat.lt_succ_iff_lt_or_eq.1 h with h1 | h2
            · exact Or.inr h1
            · exact Or.inl (Fin.ext h2)
          · rintro (rfl | h)
            · exact Nat.lt_succ_self _
            · exact Nat.lt_succ_of_lt h
        rw [hfilt, Finset.sum_insert (by simp)]
        omega
      refine ⟨pos, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨hpos_mono, fun q => ?_⟩
        split_ifs with hlt
        · rw [hpos_diff q hlt]
          dsimp only [stepGap]
          split_ifs with hmem
          · have h2 := (Finset.mem_filter.1 hmem).2.2
            ext; rw [clamp3_val, h2]; omega
          · ext; rw [clamp3_val, Nat.min_eq_left (Nat.le_of_lt_succ (gmode q).isLt)]
        · have h0 : (pos ⟨0, hs⟩).val = a.val := by simp [pos]
          have hqL : q = lastQ := Fin.ext (by have := q.isLt; dsimp [lastQ]; omega)
          rw [hqL, h0, hpos_last]
          have hbt : t - 1 - (t - 1 - b.val) = b.val := by omega
          rw [hbt]
          exact habg.1
      · refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · ext; simp [pos]
        · ext; simp [hpos_last]; omega
        · ext r
          have hr := (Finset.mem_filter.1 (eI r).2).2
          have hd := hpos_diff (eI r).1 hr.1
          dsimp only
          rw [hd]
          dsimp only [stepGap]
          rw [dif_pos (eI r).2]
          simp
  rw [hpos_bij]
  unfold gapCountPoly
  dsimp only
  have hsplit_ab : ∀ (w : ℕ), (hw : w ≤ t) →
      (Finset.univ.filter fun ab : Fin (t + 1) × Fin (t + 1) => ab.1.val + ab.2.val = w).card = w + 1 := by
    intro w hw
    have hbij : (Finset.univ.filter fun ab : Fin (t + 1) × Fin (t + 1) => ab.1.val + ab.2.val = w).card =
        (Finset.range (w + 1)).card := by
      refine Finset.card_bij (fun ab _ => ab.1.val) ?_ ?_ ?_
      · intro ab hab
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hab
        simp only [Finset.mem_range]; omega
      · intro x hx y hy h
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
        exact Prod.ext (Fin.ext h) (Fin.ext (by omega))
      · intro a ha
        simp only [Finset.mem_range] at ha
        exact ⟨(⟨a, by omega⟩, ⟨w - a, by omega⟩),
          Finset.mem_filter.2 ⟨Finset.mem_univ _, by dsimp only; omega⟩, rfl⟩
    rw [hbij, Finset.card_range]
  have hfInt_le_s : fInt ≤ s := by
    calc fInt ≤ (Finset.univ : Finset (Fin s)).card := Finset.card_filter_le _ _
      _ = s := by simp
  have hMdef : M = t - t0 := rfl
  have ht0def : t0 = s + ∑ q : Fin s, (gmode q).val := rfl
  split_ifs with h0 h1 h2 h3
  · change (gmode lastQ).val = 0 at h0
    change fInt = 0 at h1
    have hempty : (Finset.univ.filter fun abg : Fin (t + 1) × Fin (t + 1) × (Fin fInt → Fin (M + 1)) =>
        clamp3 (abg.1.val + abg.2.1.val) = gmode lastQ ∧
        abg.1.val + abg.2.1.val + ∑ r : Fin fInt, (abg.2.2 r).val = (gmode lastQ).val + M) = ∅ := by
      ext ⟨a, b, g⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rintro ⟨hcl, hsum⟩
      have hc := congrArg Fin.val hcl
      rw [clamp3_val, h0] at hc
      have hab0 : a.val + b.val = 0 := by omega
      have hzero : ∑ r : Fin fInt, (g r).val = 0 := by
        have : fInt = 0 := h1
        exact Finset.sum_eq_zero fun r _ => Fin.elim0 (this ▸ r)
      omega
    simp [hempty]
  · change (gmode lastQ).val = 0 at h0
    change ¬ fInt = 0 at h1
    have hcard : (Finset.univ.filter fun abg : Fin (t + 1) × Fin (t + 1) × (Fin fInt → Fin (M + 1)) =>
        clamp3 (abg.1.val + abg.2.1.val) = gmode lastQ ∧
        abg.1.val + abg.2.1.val + ∑ r : Fin fInt, (abg.2.2 r).val = (gmode lastQ).val + M).card =
        Nat.choose (M + (fInt - 1)) (fInt - 1) := by
      rw [← stars_bars_card (fInt - 1) M]
      refine Finset.card_bij
        (fun abg _ r => abg.2.2 ⟨r.val, by have := r.isLt; omega⟩) ?_ ?_ ?_
      · intro ⟨a, b, g⟩ habg
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at habg ⊢
        have hc := congrArg Fin.val habg.1
        rw [clamp3_val, h0] at hc
        have hsum_eq : ∑ r : Fin (fInt - 1 + 1), (g ⟨r.val, by have := r.isLt; omega⟩).val =
            ∑ r : Fin fInt, (g r).val := by
          refine Finset.sum_bij (fun r _ => ⟨r.val, by have := r.isLt; omega⟩) ?_ ?_ ?_ ?_
          · intro _ _; exact Finset.mem_univ _
          · intro r1 _ r2 _ h; exact Fin.ext (by simpa using congrArg Fin.val h)
          · intro r _; exact ⟨⟨r.val, by have := r.isLt; omega⟩, Finset.mem_univ _, Fin.ext rfl⟩
          · intro _ _; rfl
        rw [hsum_eq]; omega
      · intro ⟨a1, b1, g1⟩ h1' ⟨a2, b2, g2⟩ h2' he
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1' h2'
        have hc1 := congrArg Fin.val h1'.1; rw [clamp3_val, h0] at hc1
        have hc2 := congrArg Fin.val h2'.1; rw [clamp3_val, h0] at hc2
        have ha12 : a1.val = a2.val := by omega
        have hb12 : b1.val = b2.val := by omega
        refine Prod.ext (Fin.ext ha12) (Prod.ext (Fin.ext hb12) ?_)
        ext r
        have := congrFun he ⟨r.val, by have := r.isLt; omega⟩
        exact congrArg Fin.val this
      · intro g hg
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
        refine ⟨(⟨0, by omega⟩, ⟨0, by omega⟩, fun r => g ⟨r.val, by have := r.isLt; omega⟩), ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨by ext; rw [clamp3_val, h0]; simp, ?_⟩
          have hsum_eq : ∑ r : Fin fInt, (g ⟨r.val, by have := r.isLt; omega⟩).val =
              ∑ r : Fin (fInt - 1 + 1), (g r).val := by
            refine Finset.sum_bij (fun r _ => ⟨r.val, by have := r.isLt; omega⟩) ?_ ?_ ?_ ?_
            · intro _ _; exact Finset.mem_univ _
            · intro r1 _ r2 _ h; exact Fin.ext (by simpa using congrArg Fin.val h)
            · intro r _; exact ⟨⟨r.val, by have := r.isLt; omega⟩, Finset.mem_univ _, Fin.ext rfl⟩
            · intro _ _; rfl
          rw [hsum_eq, hg, h0]
        · ext r; rfl
    rw [hcard]
    change (((M + (fInt - 1)).choose (fInt - 1) : ℕ) : ℚ) = (choosePoly (t0 + 1 - fInt) (fInt - 1)).eval (t : ℚ)
    rw [choosePoly_eval (t0 + 1 - fInt) (fInt - 1) t (by omega)]
    have hsub : t - (t0 + 1 - fInt) = M + (fInt - 1) := by omega
    rw [hsub]
  · change (gmode lastQ).val = 1 at h2
    change fInt = 0 at h3
    have hempty : (Finset.univ.filter fun abg : Fin (t + 1) × Fin (t + 1) × (Fin fInt → Fin (M + 1)) =>
        clamp3 (abg.1.val + abg.2.1.val) = gmode lastQ ∧
        abg.1.val + abg.2.1.val + ∑ r : Fin fInt, (abg.2.2 r).val = (gmode lastQ).val + M) = ∅ := by
      ext ⟨a, b, g⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rintro ⟨hcl, hsum⟩
      have hc := congrArg Fin.val hcl
      rw [clamp3_val, h2] at hc
      have hzero : ∑ r : Fin fInt, (g r).val = 0 := by
        have : fInt = 0 := h3
        exact Finset.sum_eq_zero fun r _ => Fin.elim0 (this ▸ r)
      omega
    simp [hempty]
  · change (gmode lastQ).val = 1 at h2
    change ¬ fInt = 0 at h3
    have hcard : (Finset.univ.filter fun abg : Fin (t + 1) × Fin (t + 1) × (Fin fInt → Fin (M + 1)) =>
        clamp3 (abg.1.val + abg.2.1.val) = gmode lastQ ∧
        abg.1.val + abg.2.1.val + ∑ r : Fin fInt, (abg.2.2 r).val = (gmode lastQ).val + M).card =
        2 * Nat.choose (M + (fInt - 1)) (fInt - 1) := by
      have hprod_card : 2 * Nat.choose (M + (fInt - 1)) (fInt - 1) =
          (Finset.univ ×ˢ Finset.univ.filter fun g : Fin (fInt - 1 + 1) → Fin (M + 1) =>
            ∑ r : Fin (fInt - 1 + 1), (g r).val = M : Finset (Bool × _)).card := by
        rw [Finset.card_product, Finset.card_univ, Fintype.card_bool, stars_bars_card]
      rw [hprod_card]
      refine Finset.card_bij
        (fun abg _ => (decide (abg.1.val = 1), fun r => abg.2.2 ⟨r.val, by have := r.isLt; omega⟩)) ?_ ?_ ?_
      · intro ⟨a, b, g⟩ habg
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at habg ⊢
        have hc := congrArg Fin.val habg.1
        rw [clamp3_val, h2] at hc
        have hsum_eq : ∑ r : Fin (fInt - 1 + 1), (g ⟨r.val, by have := r.isLt; omega⟩).val =
            ∑ r : Fin fInt, (g r).val := by
          refine Finset.sum_bij (fun r _ => ⟨r.val, by have := r.isLt; omega⟩) ?_ ?_ ?_ ?_
          · intro _ _; exact Finset.mem_univ _
          · intro r1 _ r2 _ h; exact Fin.ext (by simpa using congrArg Fin.val h)
          · intro r _; exact ⟨⟨r.val, by have := r.isLt; omega⟩, Finset.mem_univ _, Fin.ext rfl⟩
          · intro _ _; rfl
        rw [hsum_eq]; omega
      · intro ⟨a1, b1, g1⟩ h1' ⟨a2, b2, g2⟩ h2' he
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1' h2'
        have hc1 := congrArg Fin.val h1'.1; rw [clamp3_val, h2] at hc1
        have hc2 := congrArg Fin.val h2'.1; rw [clamp3_val, h2] at hc2
        have hba := congrArg Prod.fst he
        have ha12 : a1.val = a2.val := by
          have h1b : a1.val = 0 ∨ a1.val = 1 := by omega
          have h2b : a2.val = 0 ∨ a2.val = 1 := by omega
          rcases h1b with h1b | h1b <;> rcases h2b with h2b | h2b <;> simp_all
        have hb12 : b1.val = b2.val := by omega
        refine Prod.ext (Fin.ext ha12) (Prod.ext (Fin.ext hb12) ?_)
        ext r
        have := congrFun (congrArg Prod.snd he) ⟨r.val, by have := r.isLt; omega⟩
        exact congrArg Fin.val this
      · intro ⟨bit, g⟩ hbg
        simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_filter] at hbg
        let a : Fin (t + 1) := if bit then ⟨1, by omega⟩ else ⟨0, by omega⟩
        let b : Fin (t + 1) := if bit then ⟨0, by omega⟩ else ⟨1, by omega⟩
        refine ⟨(a, b, fun r => g ⟨r.val, by have := r.isLt; omega⟩), ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have hab1 : a.val + b.val = 1 := by cases bit <;> simp [a, b]
          refine ⟨by ext; rw [clamp3_val, h2, hab1]; rfl, ?_⟩
          have hsum_eq : ∑ r : Fin fInt, (g ⟨r.val, by have := r.isLt; omega⟩).val =
              ∑ r : Fin (fInt - 1 + 1), (g r).val := by
            refine Finset.sum_bij (fun r _ => ⟨r.val, by have := r.isLt; omega⟩) ?_ ?_ ?_ ?_
            · intro _ _; exact Finset.mem_univ _
            · intro r1 _ r2 _ h; exact Fin.ext (by simpa using congrArg Fin.val h)
            · intro r _; exact ⟨⟨r.val, by have := r.isLt; omega⟩, Finset.mem_univ _, Fin.ext rfl⟩
            · intro _ _; rfl
          rw [hab1, hsum_eq, hbg, h2]
        · refine Prod.ext ?_ (by ext r; rfl)
          cases bit <;> simp [a]
    rw [hcard]
    change ((2 * (M + (fInt - 1)).choose (fInt - 1) : ℕ) : ℚ) =
      (Polynomial.C 2 * choosePoly (t0 + 1 - fInt) (fInt - 1)).eval (t : ℚ)
    rw [Polynomial.eval_mul, Polynomial.eval_C,
      choosePoly_eval (t0 + 1 - fInt) (fInt - 1) t (by omega)]
    have hsub : t - (t0 + 1 - fInt) = M + (fInt - 1) := by omega
    rw [hsub]
    push_cast
    rfl
  · change ¬ (gmode lastQ).val = 0 at h0
    change ¬ (gmode lastQ).val = 1 at h2
    have h2 : (gmode lastQ).val = 2 := by have := (gmode lastQ).isLt; omega
    have hcard : (Finset.univ.filter fun abg : Fin (t + 1) × Fin (t + 1) × (Fin fInt → Fin (M + 1)) =>
        clamp3 (abg.1.val + abg.2.1.val) = gmode lastQ ∧
        abg.1.val + abg.2.1.val + ∑ r : Fin fInt, (abg.2.2 r).val = (gmode lastQ).val + M).card =
        Nat.choose (M + fInt + 1) (fInt + 1) + 2 * Nat.choose (M + fInt) fInt := by
      let Sbig := Finset.univ.filter fun abg : Fin (t + 1) × Fin (t + 1) × (Fin fInt → Fin (M + 1)) =>
        clamp3 (abg.1.val + abg.2.1.val) = gmode lastQ ∧
        abg.1.val + abg.2.1.val + ∑ r : Fin fInt, (abg.2.2 r).val = (gmode lastQ).val + M
      let Gset := Finset.univ.filter fun g0 : Fin (fInt + 1) → Fin (M + 1) =>
        ∑ r : Fin (fInt + 1), (g0 r).val = M
      have hpart : Sbig.card = ∑ g0 ∈ Gset, ((g0 (Fin.last fInt)).val + 3) := by
        have hp : Sbig.card = ∑ g0 ∈ Gset,
            (Sbig.filter fun abg =>
              abg.1.val + abg.2.1.val = (g0 (Fin.last fInt)).val + 2 ∧
              ∀ r : Fin fInt, abg.2.2 r = g0 r.castSucc).card := by
          rw [← Finset.card_biUnion]
          · congr 1
            ext ⟨a, b, g⟩
            simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, Sbig, Gset]
            constructor
            · intro habg
              have hc := congrArg Fin.val habg.1
              rw [clamp3_val, h2] at hc
              let g0 : Fin (fInt + 1) → Fin (M + 1) := fun r =>
                if hr : r.val < fInt then g ⟨r.val, hr⟩
                else ⟨a.val + b.val - 2, by omega⟩
              refine ⟨g0, ?_, habg, ?_, ?_⟩
              · rw [Fin.sum_univ_castSucc]
                have h1 : ∑ r : Fin fInt, (g0 r.castSucc).val = ∑ r : Fin fInt, (g r).val := by
                  refine Finset.sum_congr rfl fun r _ => by simp [g0]
                have h2' : (g0 (Fin.last fInt)).val = a.val + b.val - 2 := by simp [g0]
                rw [h1, h2']; omega
              · simp [g0]; omega
              · intro r; simp [g0]
            · rintro ⟨_, _, habg, _, _⟩
              exact habg
          · intro g1 _ g2 _ hne
            simp only [Function.onFun, Finset.disjoint_left]
            intro ⟨a, b, g⟩ h1' h2'
            simp only [Finset.mem_filter] at h1' h2'
            apply hne
            ext r
            by_cases hr : r.val < fInt
            · have h1r := h1'.2.2 ⟨r.val, hr⟩
              have h2r := h2'.2.2 ⟨r.val, hr⟩
              have he : (⟨r.val, hr⟩ : Fin fInt).castSucc = r := Fin.ext rfl
              rw [he] at h1r h2r
              exact congrArg Fin.val (h1r.symm.trans h2r)
            · have he : r = Fin.last fInt := Fin.ext (by simp only [Fin.val_last]; have := r.isLt; omega)
              subst he
              omega
        rw [hp]
        refine Finset.sum_congr rfl fun g0 hg0 => ?_
        simp only [Gset, Finset.mem_filter, Finset.mem_univ, true_and] at hg0
        have hwle : (g0 (Fin.last fInt)).val + 2 ≤ t := by
          have : (g0 (Fin.last fInt)).val ≤ M := by
            have := Finset.single_le_sum (f := fun r => (g0 r).val) (fun _ _ => Nat.zero_le _)
              (Finset.mem_univ (Fin.last fInt))
            omega
          have : 2 ≤ t0 := by
            have := Finset.single_le_sum (f := fun q => (gmode q).val) (fun _ _ => Nat.zero_le _)
              (Finset.mem_univ lastQ)
            omega
          omega
        change (Sbig.filter _).card = ((g0 (Fin.last fInt)).val + 2) + 1
        rw [← hsplit_ab ((g0 (Fin.last fInt)).val + 2) hwle]
        refine Finset.card_bij (fun abg _ => (abg.1, abg.2.1)) ?_ ?_ ?_
        · intro ⟨a, b, g⟩ h
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
          exact h.2.1
        · intro ⟨a1, b1, g1⟩ h1' ⟨a2, b2, g2⟩ h2' he
          simp only [Finset.mem_filter] at h1' h2'
          have ha : a1 = a2 := congrArg Prod.fst he
          have hb : b1 = b2 := congrArg Prod.snd he
          refine Prod.ext ha (Prod.ext hb ?_)
          funext r
          exact (h1'.2.2 r).trans (h2'.2.2 r).symm
        · intro ⟨a, b⟩ hab
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hab
          refine ⟨(a, b, fun r => g0 r.castSucc), ?_, rfl⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Sbig]
          refine ⟨⟨by ext; rw [clamp3_val, h2, hab]; omega, ?_⟩, hab, fun _ => trivial⟩
          rw [Fin.sum_univ_castSucc] at hg0
          rw [hab, h2]; omega
      rw [hpart]
      have hsplit3 : ∑ g0 ∈ Gset, ((g0 (Fin.last fInt)).val + 3) =
          (∑ g0 ∈ Gset, ((g0 (Fin.last fInt)).val + 1)) + 2 * Gset.card := by
        have hstep : ∀ g0 : Fin (fInt + 1) → Fin (M + 1),
            (g0 (Fin.last fInt)).val + 3 = ((g0 (Fin.last fInt)).val + 1) + 2 := fun _ => by omega
        simp_rw [hstep, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm]
      rw [hsplit3]
      dsimp only [Gset]
      rw [stars_bars_card fInt M]
      congr 1
      rw [add_assoc, ← stars_bars_card (fInt + 1) M]
      have hbij2 : (Finset.univ.filter fun g1 : Fin (fInt + 2) → Fin (M + 1) =>
          ∑ r : Fin (fInt + 2), (g1 r).val = M).card =
          ∑ g0 ∈ Gset, ((g0 (Fin.last fInt)).val + 1) := by
        let G1 := Finset.univ.filter fun g1 : Fin (fInt + 2) → Fin (M + 1) =>
          ∑ r : Fin (fInt + 2), (g1 r).val = M
        have hp : G1.card = ∑ g0 ∈ Gset,
            (G1.filter fun g1 =>
              (∀ r : Fin fInt, g1 r.castSucc.castSucc = g0 r.castSucc) ∧
              (g1 (Fin.last fInt).castSucc).val + (g1 (Fin.last (fInt + 1))).val =
                (g0 (Fin.last fInt)).val).card := by
          rw [← Finset.card_biUnion]
          · congr 1
            ext g1
            simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, G1, Gset]
            constructor
            · intro hg1
              have hg1' : (∑ i : Fin fInt, (g1 i.castSucc.castSucc).val) +
                  (g1 (Fin.last fInt).castSucc).val + (g1 (Fin.last (fInt + 1))).val = M := by
                simpa only [Fin.sum_univ_castSucc] using hg1
              let g0 : Fin (fInt + 1) → Fin (M + 1) := fun r =>
                if hr : r.val < fInt then g1 ⟨r.val, by omega⟩
                else ⟨(g1 (Fin.last fInt).castSucc).val + (g1 (Fin.last (fInt + 1))).val, by omega⟩
              refine ⟨g0, ?_, hg1,
                fun r => by
                  dsimp only [g0]
                  rw [dif_pos (by simp only [Fin.val_castSucc]; exact r.isLt)]
                  exact congrArg g1 (Fin.ext rfl),
                by
                  dsimp only [g0]
                  rw [dif_neg (by simp only [Fin.val_last]; omega)]⟩
              rw [Fin.sum_univ_castSucc]
              have h3 : ∑ r : Fin fInt, (g0 r.castSucc).val =
                  ∑ r : Fin fInt, (g1 r.castSucc.castSucc).val :=
                Finset.sum_congr rfl fun r _ => by
                  dsimp only [g0]
                  rw [dif_pos (by simp only [Fin.val_castSucc]; exact r.isLt)]
                  rfl
              have h4 : (g0 (Fin.last fInt)).val =
                  (g1 (Fin.last fInt).castSucc).val + (g1 (Fin.last (fInt + 1))).val := by
                dsimp only [g0]
                rw [dif_neg (by simp only [Fin.val_last]; omega)]
              rw [h3, h4]
              omega
            · rintro ⟨_, _, hg1, _, _⟩
              exact hg1
          · intro a _ b _ hne
            simp only [Function.onFun, Finset.disjoint_left]
            intro g1 h1' h2'
            simp only [Finset.mem_filter] at h1' h2'
            apply hne
            ext r
            by_cases hr : r.val < fInt
            · have h1r := h1'.2.1 ⟨r.val, hr⟩
              have h2r := h2'.2.1 ⟨r.val, hr⟩
              have he : (⟨r.val, hr⟩ : Fin fInt).castSucc = r := Fin.ext rfl
              rw [he] at h1r h2r
              exact congrArg Fin.val (h1r.symm.trans h2r)
            · have he : r = Fin.last fInt := Fin.ext (by simp only [Fin.val_last]; have := r.isLt; omega)
              subst he
              omega
        rw [hp]
        refine Finset.sum_congr rfl fun g0 hg0 => ?_
        simp only [Gset, Finset.mem_filter, Finset.mem_univ, true_and] at hg0
        rw [← Finset.card_range ((g0 (Fin.last fInt)).val + 1)]
        refine Finset.card_bij (fun g1 _ => (g1 (Fin.last (fInt + 1))).val) ?_ ?_ ?_
        · intro g1 hg1
          simp only [Finset.mem_filter] at hg1
          simp only [Finset.mem_range]; omega
        · intro x hx y hy he
          simp only [Finset.mem_filter] at hx hy
          ext r
          by_cases hr : r.val < fInt
          · have h1r := hx.2.1 ⟨r.val, hr⟩
            have h2r := hy.2.1 ⟨r.val, hr⟩
            have hrr : (⟨r.val, hr⟩ : Fin fInt).castSucc.castSucc = r := Fin.ext rfl
            rw [hrr] at h1r h2r
            exact congrArg Fin.val (h1r.trans h2r.symm)
          · by_cases hr2 : r.val = fInt
            · have hrr : r = (Fin.last fInt).castSucc := Fin.ext hr2
              rw [hrr]; omega
            · have hrr : r = Fin.last (fInt + 1) := Fin.ext (by simp only [Fin.val_last]; have := r.isLt; omega)
              rw [hrr]; exact he
        · intro k hk
          simp only [Finset.mem_range] at hk
          let g1 : Fin (fInt + 2) → Fin (M + 1) := fun r =>
            if hr : r.val < fInt then g0 ⟨r.val, by omega⟩
            else if r.val = fInt then ⟨(g0 (Fin.last fInt)).val - k, by have := (g0 (Fin.last fInt)).isLt; omega⟩
            else ⟨k, by have := (g0 (Fin.last fInt)).isLt; omega⟩
          refine ⟨g1, ?_, by simp [g1]⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, G1]
          refine ⟨?_,
            fun r => by
              dsimp only [g1]
              rw [dif_pos (by simp only [Fin.val_castSucc]; exact r.isLt)]
              exact congrArg g0 (Fin.ext rfl),
            by simp [g1]; omega⟩
          rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
          have h1 : ∑ r : Fin fInt, (g1 r.castSucc.castSucc).val = ∑ r : Fin fInt, (g0 r.castSucc).val :=
            Finset.sum_congr rfl fun r _ => by
              dsimp only [g1]
              rw [dif_pos (by simp only [Fin.val_castSucc]; exact r.isLt)]
              rfl
          have h2' : (g1 (Fin.last fInt).castSucc).val = (g0 (Fin.last fInt)).val - k := by simp [g1]
          have h3' : (g1 (Fin.last (fInt + 1))).val = k := by simp [g1]
          rw [Fin.sum_univ_castSucc] at hg0
          rw [h1, h2', h3']; omega
      exact hbij2.symm
    rw [hcard, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    have hfInt_le : fInt + 1 ≤ t0 := by
      have h1 : fInt ≤ s := by
        calc fInt ≤ (Finset.univ : Finset (Fin s)).card := Finset.card_filter_le _ _
          _ = s := by simp
      have h2' : 2 ≤ ∑ q : Fin s, (gmode q).val := by
        have := Finset.single_le_sum (f := fun q => (gmode q).val) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ lastQ)
        omega
      omega
    rw [choosePoly_eval (t0 - fInt - 1) (fInt + 1) t (by omega),
      choosePoly_eval (t0 - fInt) fInt t (by omega)]
    have hsub1 : t - (t0 - fInt - 1) = M + fInt + 1 := by omega
    have hsub2 : t - (t0 - fInt) = M + fInt := by omega
    rw [hsub1, hsub2]
    push_cast
    rfl

lemma blockIdx_prev_zero {p t : ℕ} (hp : 0 < p) (ht : 0 < t) (b : Fin t) :
    prevIdx (blockIdx (p := p) b ⟨0, by omega⟩) =
      blockIdx (p := p) (prevIdx b) ⟨2 * p - 1, by omega⟩ := by
  ext
  simp only [prevIdx, blockIdx, add_zero]
  have hn : 0 < 2 * p * t := by positivity
  by_cases hb : b.val = 0
  · rw [hb]
    have h1 : (0 + (t - 1)) % t = t - 1 := by
      rw [zero_add, Nat.mod_eq_of_lt (Nat.sub_lt ht (Nat.succ_pos 0))]
    rw [h1]
    have h2 : 2 * p * 0 + (2 * p * t - 1) = 2 * p * (t - 1) + (2 * p - 1) := by
      cases t with
      | zero => omega
      | succ t' => simp [Nat.mul_succ]; omega
    rw [h2, Nat.mod_eq_of_lt]
    cases t with
    | zero => omega
    | succ t' => simp [Nat.mul_succ]; omega
  · have h1 : (b.val + (t - 1)) % t = b.val - 1 := by
      have : b.val + (t - 1) = (b.val - 1) + t := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by have := b.isLt; omega)]
    rw [h1]
    have h2 : 2 * p * b.val + (2 * p * t - 1) = (2 * p * (b.val - 1) + (2 * p - 1)) + 2 * p * t := by
      cases b with
      | mk bv hbv =>
        cases bv with
        | zero => exact absurd rfl hb
        | succ b' => simp [Nat.mul_succ]; omega
    rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt]
    have hlt : b.val - 1 + 1 ≤ t := by have := b.isLt; omega
    have hmul : 2 * p * (b.val - 1 + 1) ≤ 2 * p * t := Nat.mul_le_mul_left (2 * p) hlt
    have : 2 * p * (b.val - 1 + 1) = 2 * p * (b.val - 1) + 2 * p := by ring
    omega

lemma blockIdx_next {p t : ℕ} (hp : 0 < p) (ht : 0 < t) (b : Fin t) (u : Fin (2 * p)) :
    nextIdx (blockIdx b u) =
      if hu : u.val + 1 < 2 * p then blockIdx b ⟨u.val + 1, hu⟩
      else blockIdx (nextIdx b) ⟨0, by omega⟩ := by
  ext
  simp only [nextIdx, blockIdx]
  split_ifs with hu
  · simp only [blockIdx]
    have hlt : 2 * p * b.val + (u.val + 1) < 2 * p * t := (blockIdx b ⟨u.val + 1, hu⟩).isLt
    rw [add_assoc, Nat.mod_eq_of_lt hlt]
  · simp only [blockIdx, add_zero]
    have hu_eq : u.val + 1 = 2 * p := by have := u.isLt; omega
    rw [add_assoc, hu_eq]
    have h1 : 2 * p * b.val + 2 * p = 2 * p * (b.val + 1) := by ring
    rw [h1, Nat.mul_mod_mul_left]

lemma blockIdx_prev {p t : ℕ} (hp : 0 < p) (ht : 0 < t) (b : Fin t) (u : Fin (2 * p)) :
    prevIdx (blockIdx b u) =
      if hu : 0 < u.val then blockIdx b ⟨u.val - 1, by have := u.isLt; omega⟩
      else blockIdx (prevIdx b) ⟨2 * p - 1, by omega⟩ := by
  split_ifs with hu
  · ext
    simp only [prevIdx, blockIdx]
    have h1 : 2 * p * b.val + u.val + (2 * p * t - 1) =
        (2 * p * b.val + (u.val - 1)) + 2 * p * t := by
      have : 0 < 2 * p * t := by positivity
      omega
    have hlt : 2 * p * b.val + (u.val - 1) < 2 * p * t :=
      (blockIdx b ⟨u.val - 1, by have := u.isLt; omega⟩).isLt
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
  · have hu0 : u = ⟨0, by omega⟩ := Fin.ext (by dsimp only; omega)
    rw [hu0]
    exact blockIdx_prev_zero hp ht b

lemma buildFromPos_at_pos {p t s : ℕ} (hp : 0 < p) (hs : 0 < s)
    (blocks : Fin s → Fin (2 * p) → Bool × Bool)
    (pos : Fin s → Fin t) (hmono : StrictMono pos) (q : Fin s) (u : Fin (2 * p)) :
    buildFromPos hp hs blocks pos hmono (blockIdx (pos q) u) = blocks q u := by
  unfold buildFromPos
  have hb : (⟨(blockIdx (pos q) u).val / (2 * p),
      Nat.div_lt_of_lt_mul (by linarith [(blockIdx (pos q) u).isLt])⟩ : Fin t) = pos q := by
    ext; simp only [blockIdx]
    rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt u.isLt, add_zero]
  have hu : (⟨(blockIdx (pos q) u).val % (2 * p), Nat.mod_lt _ (by omega)⟩ : Fin (2 * p)) = u := by
    ext; simp only [blockIdx, Nat.mul_add_mod, Nat.mod_eq_of_lt u.isLt]
  simp only [hb, hu]
  have hmem : ∃ q' : Fin s, pos q' = pos q := ⟨q, rfl⟩
  rw [dif_pos hmem]
  have heq : Classical.choose hmem = q := hmono.injective (Classical.choose_spec hmem)
  rw [heq]

lemma buildFromPos_at_gap {p t s : ℕ} (hp : 0 < p) (hs : 0 < s)
    (blocks : Fin s → Fin (2 * p) → Bool × Bool)
    (pos : Fin s → Fin t) (hmono : StrictMono pos) (b : Fin t)
    (hnot : ∀ q : Fin s, pos q ≠ b) (u : Fin (2 * p)) :
    let before := Finset.univ.filter fun q : Fin s => pos q < b
    let prevQ : Fin s :=
      if hne : before.Nonempty then before.max' hne
      else ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩
    buildFromPos hp hs blocks pos hmono (blockIdx b u) =
      pureBlock p (blocks prevQ ⟨2 * p - 1, by omega⟩).1 u := by
  unfold buildFromPos
  have hb : (⟨(blockIdx b u).val / (2 * p),
      Nat.div_lt_of_lt_mul (by linarith [(blockIdx b u).isLt])⟩ : Fin t) = b := by
    ext; simp only [blockIdx]
    rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt u.isLt, add_zero]
  have hu : (⟨(blockIdx b u).val % (2 * p), Nat.mod_lt _ (by omega)⟩ : Fin (2 * p)) = u := by
    ext; simp only [blockIdx, Nat.mul_add_mod, Nat.mod_eq_of_lt u.isLt]
  simp only [hb, hu]
  rw [dif_neg (by push Not; exact hnot)]

lemma buildFromPos_prevEnd {p t s : ℕ} (hp : 0 < p) (ht : 0 < t) (hs : 0 < s)
    (blocks : Fin s → Fin (2 * p) → Bool × Bool)
    (pos : Fin s → Fin t) (hmono : StrictMono pos) (q : Fin s) :
    (buildFromPos hp hs blocks pos hmono (blockIdx (prevIdx (pos q)) ⟨2 * p - 1, by omega⟩)).1 =
      (blocks (prevIdx q) ⟨2 * p - 1, by omega⟩).1 := by
  by_cases hmem : ∃ q' : Fin s, pos q' = prevIdx (pos q)
  · obtain ⟨q', hq'⟩ := hmem
    rw [← hq', buildFromPos_at_pos]
    have heq : q' = prevIdx q := by
      by_cases hq0 : q.val = 0
      · have hprev_q : prevIdx q = ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩ := by
          ext; simp [prevIdx, hq0, Nat.mod_eq_of_lt (Nat.sub_lt hs (Nat.succ_pos 0))]
        rw [hprev_q]
        by_contra hne
        have hlt : q' < ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩ :=
          lt_of_le_of_ne (Fin.mk_le_mk.2 (by have := q'.isLt; omega)) hne
        have hpos_lt := hmono hlt
        by_cases hp0 : (pos q).val = 0
        · have hprev0 : (prevIdx (pos q)).val = t - 1 := by
            simp [prevIdx, hp0, Nat.mod_eq_of_lt (Nat.sub_lt ht (Nat.succ_pos 0))]
          have : (pos q').val = t - 1 := by rw [hq', hprev0]
          have := (pos ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩).isLt
          have : (pos q').val < (pos ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩).val := hpos_lt
          omega
        · have hprev1 : (prevIdx (pos q)).val = (pos q).val - 1 := by
            simp only [prevIdx]
            have : (pos q).val + (t - 1) = ((pos q).val - 1) + t := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by have := (pos q).isLt; omega)]
          have hq'0 : pos q ≤ pos q' := hmono.monotone (Fin.mk_le_mk.2 (by omega))
          have : (pos q).val ≤ (pos q').val := hq'0
          have : (pos q').val = (pos q).val - 1 := by rw [hq', hprev1]
          omega
      · have hprev_q : (prevIdx q).val = q.val - 1 := by
          simp only [prevIdx]
          have : q.val + (t - 1) = (q.val - 1) + t := by omega
          have : q.val + (s - 1) = (q.val - 1) + s := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by have := q.isLt; omega)]
        have hp_pos : 0 < (pos q).val := by
          have := hmono (Fin.mk_lt_mk.2 (show 0 < q.val by omega) : ⟨0, hs⟩ < q)
          have : (pos ⟨0, hs⟩).val < (pos q).val := this
          omega
        have hprev_pos : (prevIdx (pos q)).val = (pos q).val - 1 := by
          simp only [prevIdx]
          have : (pos q).val + (t - 1) = ((pos q).val - 1) + t := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by have := (pos q).isLt; omega)]
        have hq'lt : q' < q := by
          by_contra hge
          have hle : q ≤ q' := le_of_not_gt hge
          have := hmono.monotone hle
          have : (pos q).val ≤ (pos q').val := this
          have : (pos q').val = (pos q).val - 1 := by rw [hq', hprev_pos]
          omega
        have hq'ge : prevIdx q ≤ q' := by
          by_contra hlt
          have hlt' : q' < prevIdx q := lt_of_not_ge hlt
          have h1 : (pos q').val < (pos (prevIdx q)).val := hmono hlt'
          have h2 : (pos (prevIdx q)).val < (pos q).val :=
            hmono (show (prevIdx q).val < q.val by rw [hprev_q]; omega)
          have : (pos q').val = (pos q).val - 1 := by rw [hq', hprev_pos]
          omega
        exact Fin.ext (by have : q'.val < q.val := hq'lt; have : (prevIdx q).val ≤ q'.val := hq'ge; omega)
    rw [heq]
  · push Not at hmem
    rw [buildFromPos_at_gap hp hs blocks pos hmono (prevIdx (pos q)) hmem]
    change pureEnd p hp _ = _
    rw [pureEnd_eq]
    have hprev_eq : (if hne : (Finset.univ.filter fun q' : Fin s => pos q' < prevIdx (pos q)).Nonempty
        then (Finset.univ.filter fun q' : Fin s => pos q' < prevIdx (pos q)).max' hne
        else ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩) = prevIdx q := by
      split_ifs with hne
      · have hmax := Finset.max'_mem _ hne
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmax
        by_cases hq0 : q.val = 0
        · have hprev_q : prevIdx q = ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩ := by
            ext; simp [prevIdx, hq0, Nat.mod_eq_of_lt (Nat.sub_lt hs (Nat.succ_pos 0))]
          rw [hprev_q]
          by_cases hp0 : (pos q).val = 0
          · have hprev0 : (prevIdx (pos q)).val = t - 1 := by
              simp [prevIdx, hp0, Nat.mod_eq_of_lt (Nat.sub_lt ht (Nat.succ_pos 0))]
            have hlast_mem : (⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩ : Fin s) ∈
                Finset.univ.filter fun q' : Fin s => pos q' < prevIdx (pos q) := by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              have hneL := hmem ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩
              have hltL : (pos ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩).val < t :=
                (pos ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩).isLt
              have hneVal : (pos ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩).val ≠ t - 1 :=
                fun h => hneL (Fin.ext (h.trans hprev0.symm))
              exact show (pos ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩).val < (prevIdx (pos q)).val by rw [hprev0]; omega
            have hge := Finset.le_max' _ _ hlast_mem
            exact le_antisymm (Fin.mk_le_mk.2 (by have := (Finset.max' _ hne).isLt; omega)) hge
          · have hprev1 : (prevIdx (pos q)).val = (pos q).val - 1 := by
              simp only [prevIdx]
              have : (pos q).val + (t - 1) = ((pos q).val - 1) + t := by omega
              rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by have := (pos q).isLt; omega)]
            have hle : pos q ≤ pos (Finset.max' _ hne) :=
              hmono.monotone (Fin.mk_le_mk.2 (by omega))
            have : (pos q).val ≤ (pos (Finset.max' _ hne)).val := hle
            have : (pos (Finset.max' _ hne)).val < (pos q).val - 1 := by rw [← hprev1]; exact hmax
            omega
        · have hprev_q : (prevIdx q).val = q.val - 1 := by
            simp only [prevIdx]
            have : q.val + (s - 1) = (q.val - 1) + s := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by have := q.isLt; omega)]
          have hp_pos : 0 < (pos q).val := by
            have := hmono (Fin.mk_lt_mk.2 (show 0 < q.val by omega) : ⟨0, hs⟩ < q)
            have : (pos ⟨0, hs⟩).val < (pos q).val := this
            omega
          have hprev1 : (prevIdx (pos q)).val = (pos q).val - 1 := by
            simp only [prevIdx]
            have : (pos q).val + (t - 1) = ((pos q).val - 1) + t := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by have := (pos q).isLt; omega)]
          have hmemP : prevIdx q ∈ Finset.univ.filter fun q' : Fin s => pos q' < prevIdx (pos q) := by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            have hlt1 : (pos (prevIdx q)).val < (pos q).val :=
              hmono (show (prevIdx q).val < q.val by rw [hprev_q]; omega)
            have hne1 : (pos (prevIdx q)).val ≠ (pos q).val - 1 :=
              fun h => hmem (prevIdx q) (Fin.ext (h.trans hprev1.symm))
            exact show (pos (prevIdx q)).val < (prevIdx (pos q)).val by rw [hprev1]; omega
          have hge := Finset.le_max' _ _ hmemP
          have hltM : Finset.max' _ hne < q := by
            by_contra hnotlt
            have hle : q ≤ Finset.max' _ hne := le_of_not_gt hnotlt
            have : (pos q).val ≤ (pos (Finset.max' _ hne)).val := hmono.monotone hle
            have : (pos (Finset.max' _ hne)).val < (pos q).val - 1 := by rw [← hprev1]; exact hmax
            omega
          exact Fin.ext (by have : (Finset.max' _ hne).val < q.val := hltM; have : (prevIdx q).val ≤ (Finset.max' _ hne).val := hge; omega)
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        have hq0 : q.val = 0 := by
          by_contra hq0'
          have hprev_q : (prevIdx q).val = q.val - 1 := by
            simp only [prevIdx]
            have : q.val + (s - 1) = (q.val - 1) + s := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by have := q.isLt; omega)]
          have hp_pos : 0 < (pos q).val := by
            have := hmono (Fin.mk_lt_mk.2 (show 0 < q.val by omega) : ⟨0, hs⟩ < q)
            have : (pos ⟨0, hs⟩).val < (pos q).val := this
            omega
          have hprev1 : (prevIdx (pos q)).val = (pos q).val - 1 := by
            simp only [prevIdx]
            have : (pos q).val + (t - 1) = ((pos q).val - 1) + t := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by have := (pos q).isLt; omega)]
          have hlt1 : (pos (prevIdx q)).val < (pos q).val :=
            hmono (show (prevIdx q).val < q.val by rw [hprev_q]; omega)
          have hne1 : (pos (prevIdx q)).val ≠ (pos q).val - 1 :=
            fun h => hmem (prevIdx q) (Fin.ext (h.trans hprev1.symm))
          have hmemP : prevIdx q ∈ Finset.univ.filter fun q' : Fin s => pos q' < prevIdx (pos q) :=
            Finset.mem_filter.2 ⟨Finset.mem_univ _, show (pos (prevIdx q)).val < (prevIdx (pos q)).val by rw [hprev1]; omega⟩
          rw [hne] at hmemP
          exact Finset.notMem_empty _ hmemP
        ext
        simp [prevIdx, hq0, Nat.mod_eq_of_lt (Nat.sub_lt hs (Nat.succ_pos 0))]
    rw [hprev_eq]

lemma buildFromPos_unmarked_gap {p t s : ℕ} (hp : 0 < p) (ht : 0 < t) (hs : 0 < s)
    (blocks : Fin s → Fin (2 * p) → Bool × Bool)
    (pos : Fin s → Fin t) (hmono : StrictMono pos) (b : Fin t)
    (hnot : ∀ q : Fin s, pos q ≠ b) :
    isMarkedBlock (buildFromPos hp hs blocks pos hmono) b = false := by
  simp only [isMarkedBlock, decide_eq_false_iff_not, not_exists, not_or]
  intro u
  let before := Finset.univ.filter fun q : Fin s => pos q < b
  let prevQ : Fin s :=
    if hne : before.Nonempty then before.max' hne
    else ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩
  have hcur := buildFromPos_at_gap hp hs blocks pos hmono b hnot u
  dsimp only at hcur
  refine ⟨by rw [hcur]; simp [pureBlock], ?_⟩
  rw [blockIdx_prev hp ht b u]
  split_ifs with hu
  · have hprev := buildFromPos_at_gap hp hs blocks pos hmono b hnot ⟨u.val - 1, by have := u.isLt; omega⟩
    dsimp only at hprev
    rw [hprev, hcur]
    simp only [pureBlock]
    cases (blocks prevQ ⟨2 * p - 1, by omega⟩).1 <;>
      simp only [↓reduceIte, ne_eq, decide_eq_decide] <;>
      · intro hiff
        by_cases hm : u.val % 2 = 0 <;> simp_all <;> omega
  · have hu0 : u.val = 0 := by omega
    rw [hcur]
    have hprevEnd : (buildFromPos hp hs blocks pos hmono (blockIdx (prevIdx b) ⟨2 * p - 1, by omega⟩)).1 =
        (blocks prevQ ⟨2 * p - 1, by omega⟩).1 := by
      by_cases hpm : ∃ q' : Fin s, pos q' = prevIdx b
      · obtain ⟨q', hq'⟩ := hpm
        rw [← hq', buildFromPos_at_pos]
        have heq : prevQ = q' := by
          dsimp only [prevQ, before]
          split_ifs with hne
          · have hmax := Finset.max'_mem _ hne
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmax
            by_cases hb0 : b.val = 0
            · have hle : pos q' < b := by
                have := (pos (Finset.max' _ hne)).isLt
                have : (pos (Finset.max' _ hne)).val < 0 := by rw [← hb0]; exact hmax
                omega
              exact absurd hle (by omega)
            · have hpb : (prevIdx b).val = b.val - 1 := by
                simp only [prevIdx]
                have : b.val + (t - 1) = (b.val - 1) + t := by omega
                rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by have := b.isLt; omega)]
              have hq'mem : q' ∈ Finset.univ.filter fun q : Fin s => pos q < b := by
                simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                exact show (pos q').val < b.val by rw [hq', hpb]; omega
              have hge := Finset.le_max' _ _ hq'mem
              have hle : Finset.max' _ hne ≤ q' := by
                by_contra hgt
                have hlt : q' < Finset.max' _ hne := lt_of_not_ge hgt
                have h1 : (pos q').val < (pos (Finset.max' _ hne)).val := hmono hlt
                have h2 : (pos (Finset.max' _ hne)).val < b.val := hmax
                have : (pos q').val = b.val - 1 := by rw [hq', hpb]
                omega
              exact le_antisymm hle hge
          · rw [Finset.not_nonempty_iff_eq_empty] at hne
            have hb0 : b.val = 0 := by
              by_contra hb0'
              have hpb : (prevIdx b).val = b.val - 1 := by
                simp only [prevIdx]
                have : b.val + (t - 1) = (b.val - 1) + t := by omega
                rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by have := b.isLt; omega)]
              have hq'mem : q' ∈ Finset.univ.filter fun q : Fin s => pos q < b :=
                Finset.mem_filter.2 ⟨Finset.mem_univ _, show (pos q').val < b.val by rw [hq', hpb]; omega⟩
              rw [hne] at hq'mem
              exact Finset.notMem_empty _ hq'mem
            have hpb : (prevIdx b).val = t - 1 := by
              simp [prevIdx, hb0, Nat.mod_eq_of_lt (Nat.sub_lt ht (Nat.succ_pos 0))]
            by_contra hneL
            have hlt : q' < ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩ :=
              lt_of_le_of_ne (Fin.mk_le_mk.2 (by have := q'.isLt; omega)) (Ne.symm hneL)
            have h1 : (pos q').val < (pos ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩).val := hmono hlt
            have h2 := (pos ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩).isLt
            have : (pos q').val = t - 1 := by rw [hq', hpb]
            omega
        rw [heq]
      · push Not at hpm
        rw [buildFromPos_at_gap hp hs blocks pos hmono (prevIdx b) hpm]
        change pureEnd p hp _ = _
        rw [pureEnd_eq]
        have hsame : (if hne : (Finset.univ.filter fun q : Fin s => pos q < prevIdx b).Nonempty
            then (Finset.univ.filter fun q : Fin s => pos q < prevIdx b).max' hne
            else ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩) = prevQ := by
          dsimp only [prevQ, before]
          by_cases hb0 : b.val = 0
          · have he1 : (Finset.univ.filter fun q : Fin s => pos q < b) = ∅ := by
              ext q; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
              intro h; have : (pos q).val < 0 := by rw [← hb0]; exact h
              omega
            have hpb : (prevIdx b).val = t - 1 := by
              simp [prevIdx, hb0, Nat.mod_eq_of_lt (Nat.sub_lt ht (Nat.succ_pos 0))]
            have he2 : (Finset.univ.filter fun q : Fin s => pos q < prevIdx b) = Finset.univ := by
              ext q; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
              have hne1 : (pos q).val ≠ t - 1 := fun h => hpm q (Fin.ext (h.trans hpb.symm))
              exact show (pos q).val < (prevIdx b).val by rw [hpb]; have := (pos q).isLt; omega
            have huniv_ne : (Finset.univ : Finset (Fin s)).Nonempty :=
              Finset.univ_nonempty_iff.2 ⟨⟨0, hs⟩⟩
            simp only [he1, he2, huniv_ne, ↓reduceDIte, Finset.not_nonempty_empty]
            have hge := Finset.le_max' (Finset.univ : Finset (Fin s))
              (⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩ : Fin s) (Finset.mem_univ _)
            exact le_antisymm (Fin.mk_le_mk.2 (by have := ((Finset.univ : Finset (Fin s)).max' huniv_ne).isLt; omega)) hge
          · have hpb : (prevIdx b).val = b.val - 1 := by
              simp only [prevIdx]
              have : b.val + (t - 1) = (b.val - 1) + t := by omega
              rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by have := b.isLt; omega)]
            have heq : (Finset.univ.filter fun q : Fin s => pos q < prevIdx b) =
                (Finset.univ.filter fun q : Fin s => pos q < b) := by
              ext q
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              constructor
              · intro h
                have hlt : (pos q).val < b.val - 1 := by rw [← hpb]; exact h
                exact show (pos q).val < b.val by omega
              · intro h
                have hne1 : (pos q).val ≠ b.val - 1 := fun he => hpm q (Fin.ext (he.trans hpb.symm))
                exact show (pos q).val < (prevIdx b).val by rw [hpb]; have : (pos q).val < b.val := h; omega
            simp only [heq]
        rw [hsame]
    rw [hprevEnd]
    simp only [pureBlock, hu0]
    cases (blocks prevQ ⟨2 * p - 1, by omega⟩).1 <;> simp

lemma buildFromPos_marked_at_pos {p t s : ℕ} (hp : 0 < p) (ht : 0 < t) (hs : 0 < s)
    (blocks : Fin s → Fin (2 * p) → Bool × Bool)
    (pos : Fin s → Fin t) (hmono : StrictMono pos) (q : Fin s) :
    isMarkedBlock (buildFromPos hp hs blocks pos hmono) (pos q) =
      decide (∃ u : Fin (2 * p),
        (blocks q u).2 = true ∨
        (if hu : 0 < u.val then (blocks q ⟨u.val - 1, by have := u.isLt; omega⟩).1
         else (blocks (prevIdx q) ⟨2 * p - 1, by omega⟩).1) = (blocks q u).1) := by
  unfold isMarkedBlock
  rw [decide_eq_decide]
  refine exists_congr fun u => ?_
  dsimp only
  rw [buildFromPos_at_pos, blockIdx_prev hp ht (pos q) u]
  split_ifs with hu
  · rw [buildFromPos_at_pos]
  · rw [buildFromPos_prevEnd hp ht]

lemma buildFromPos_reconstruct {p t s : ℕ} (hp : 0 < p) (ht : 0 < t) (hs : 0 < s)
    (cfg : Fin (2 * p * t) → Bool × Bool)
    (hcard : (Finset.univ.filter fun b : Fin t => isMarkedBlock cfg b = true).card = s) :
    let M := Finset.univ.filter fun b : Fin t => isMarkedBlock cfg b = true
    let e : Fin s ≃o M := M.orderIsoOfFin hcard
    let blocks : Fin s → Fin (2 * p) → Bool × Bool := fun q => blockOf cfg (e q).1
    let pos : Fin s → Fin t := fun q => (e q).1
    let hmono : StrictMono pos := fun _ _ h => e.strictMono h
    buildFromPos hp hs blocks pos hmono = cfg := by
  intro M e blocks pos hmono
  ext i
  · let b : Fin t := ⟨i.val / (2 * p), Nat.div_lt_of_lt_mul (by linarith [i.isLt])⟩
    let u : Fin (2 * p) := ⟨i.val % (2 * p), Nat.mod_lt _ (by omega)⟩
    have hi : i = blockIdx b u := by
      ext; simp only [blockIdx, b, u]; exact (Nat.div_add_mod i.val (2 * p)).symm
    conv_lhs => rw [hi]
    conv_rhs => rw [hi]
    by_cases hbm : b ∈ M
    · let q := e.symm ⟨b, hbm⟩
      have hposq : pos q = b := by simp [pos, q]
      rw [← hposq, buildFromPos_at_pos]
      dsimp only [blocks, blockOf]
    · have hnot : ∀ q : Fin s, pos q ≠ b := fun q hq => hbm (hq ▸ (e q).2)
      rw [buildFromPos_at_gap hp hs blocks pos hmono b hnot u]
      have hwalk : ∀ d : ℕ, ∀ b' : Fin t, (∀ k < d + 1, prevIdx^[k] b' ∉ M) →
          (prevIdx^[d + 1] b' ∈ M) →
          (cfg (blockIdx b' u)).1 = (pureBlock p (cfg (blockIdx (prevIdx^[d + 1] b') ⟨2 * p - 1, by omega⟩)).1 u).1 := by
        intro d
        induction d with
        | zero =>
          intro b' hnone _
          have hb'u : isMarkedBlock cfg b' = false :=
            Bool.eq_false_iff.2 fun h => hnone 0 (Nat.succ_pos 0) (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
          have hpe := unmarked_eq_pure hp ht cfg b' hb'u
          have h1 := congrArg (fun f => (f u).1) hpe
          simp only [blockOf] at h1
          rw [h1, blockIdx_prev_zero hp ht b', Function.iterate_one]
        | succ d ih =>
          intro b' hnone hhit
          have hb'u : isMarkedBlock cfg b' = false :=
            Bool.eq_false_iff.2 fun h => hnone 0 (Nat.succ_pos _) (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
          have hpe := unmarked_eq_pure hp ht cfg b' hb'u
          have h1 := congrArg (fun f => (f u).1) hpe
          simp only [blockOf] at h1
          rw [h1, blockIdx_prev_zero hp ht b']
          have hpe_eq : (cfg (blockIdx (prevIdx b') ⟨2 * p - 1, by omega⟩)).1 =
              (cfg (blockIdx (prevIdx^[d + 2] b') ⟨2 * p - 1, by omega⟩)).1 := by
            have hstep : ∀ k (b0 : Fin t), (∀ j < k, prevIdx^[j] b0 ∉ M) →
                (cfg (blockIdx b0 ⟨2 * p - 1, by omega⟩)).1 =
                (cfg (blockIdx (prevIdx^[k] b0) ⟨2 * p - 1, by omega⟩)).1 := by
              intro k
              induction k with
              | zero => intro _ _; rfl
              | succ k ihk =>
                intro b0 hn0
                have hm0 : isMarkedBlock cfg b0 = false :=
                  Bool.eq_false_iff.2 fun h => hn0 0 (Nat.succ_pos k)
                    (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
                have he0 := congrArg (fun f => (f ⟨2 * p - 1, by omega⟩).1)
                  (unmarked_eq_pure hp ht cfg b0 hm0)
                simp only [blockOf] at he0
                change _ = pureEnd p hp _ at he0
                rw [pureEnd_eq, blockIdx_prev_zero hp ht b0] at he0
                rw [he0, ihk (prevIdx b0) (fun j hj => by
                  rw [← Function.iterate_succ_apply]; exact hn0 (j + 1) (by omega)),
                  ← Function.iterate_succ_apply]
            have hres0 := hstep (d + 1) (prevIdx b') (fun j hj => by
              rw [← Function.iterate_succ_apply]; exact hnone (j + 1) (by omega))
            rw [← Function.iterate_succ_apply prevIdx (d + 1) b'] at hres0
            exact hres0
          rw [hpe_eq]
      let before := Finset.univ.filter fun q : Fin s => pos q < b
      let prevQ : Fin s :=
        if hne : before.Nonempty then before.max' hne
        else ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩
      let d : ℕ := (b.val + t - (pos prevQ).val) % t
      have hd_pos : 0 < d := by
        by_contra h0
        have hd0 : d = 0 := by omega
        have heq : pos prevQ = b := by
          ext
          dsimp only [d] at hd0
          obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hd0
          have hb_lt := b.isLt; have hp_lt := (pos prevQ).isLt
          have hk1 : k = 1 := by
            rcases k with _ | _ | k
            · omega
            · rfl
            · have : t * (k + 1 + 1) = t * k + 2 * t := by ring
              omega
          rw [hk1, mul_one] at hk
          omega
        exact hnot prevQ heq
      have hiter_val : ∀ k (b0 : Fin t), (prevIdx^[k] b0).val = (b0.val + k * (t - 1)) % t := by
        intro k
        induction k with
        | zero => intro b0; simp [Nat.mod_eq_of_lt b0.isLt]
        | succ k ih =>
          intro b0
          rw [Function.iterate_succ_apply']
          simp only [prevIdx]
          rw [ih, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
          congr 1; ring
      have hreach : prevIdx^[d] b = pos prevQ := by
        ext
        rw [hiter_val]
        have hmod2 : (d + (pos prevQ).val) % t = b.val := by
          dsimp only [d]
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
          have hsum : b.val + t - (pos prevQ).val + (pos prevQ).val = b.val + t := by
            have := (pos prevQ).isLt; omega
          rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt b.isLt]
        have hsub : b.val + d * (t - 1) + d = b.val + d * t := by
          cases t with
          | zero => omega
          | succ t' => simp [Nat.mul_succ]; omega
        have h2 : (b.val + d * (t - 1) + d) % t = b.val := by
          rw [hsub, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt b.isLt]
        have h3 : ((b.val + d * (t - 1)) % t + d) % t = ((pos prevQ).val + d) % t := by
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, h2, add_comm, hmod2]
        have hlt1 : (b.val + d * (t - 1)) % t < t := Nat.mod_lt _ ht
        have hlt2 : (pos prevQ).val < t := (pos prevQ).isLt
        have hq1 := Nat.div_add_mod ((b.val + d * (t - 1)) % t + d) t
        have hq2 := Nat.div_add_mod ((pos prevQ).val + d) t
        have hqeq : ((b.val + d * (t - 1)) % t + d) / t = ((pos prevQ).val + d) / t := by
          by_contra hne
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · have : t * (((b.val + d * (t - 1)) % t + d) / t) + t ≤ t * (((pos prevQ).val + d) / t) := by nlinarith
            omega
          · have : t * (((pos prevQ).val + d) / t) + t ≤ t * (((b.val + d * (t - 1)) % t + d) / t) := by nlinarith
            omega
        have hmul : t * (((b.val + d * (t - 1)) % t + d) / t) = t * (((pos prevQ).val + d) / t) :=
          congrArg (t * ·) hqeq
        omega
      have hnone : ∀ k < d, prevIdx^[k] b ∉ M := by
        intro k hk hmem
        let q := e.symm ⟨prevIdx^[k] b, hmem⟩
        have hposq : pos q = prevIdx^[k] b := by simp [pos, q]
        have hk_val : (pos q).val = (b.val + k * (t - 1)) % t := by rw [hposq, hiter_val]
        by_cases hne : before.Nonempty
        · have hprev_val : prevQ = before.max' hne := dif_pos hne
          have hmax := Finset.max'_mem _ hne
          simp only [before, Finset.mem_filter, Finset.mem_univ, true_and] at hmax
          have hd_eq : d = b.val - (pos (before.max' hne)).val := by
            dsimp only [d]; rw [hprev_val]
            have : (pos (before.max' hne)).val < b.val := hmax
            have : b.val + t - (pos (before.max' hne)).val = (b.val - (pos (before.max' hne)).val) + t := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by have := b.isLt; omega)]
          have hk_lt_b : k ≤ b.val := by omega
          have hkq : (pos q).val = b.val - k := by
            rw [hk_val]
            have h1 : b.val + k * (t - 1) = (b.val - k) + k * t := by
              cases t with
              | zero => omega
              | succ t' => simp [Nat.mul_succ]; omega
            rw [h1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by have := b.isLt; omega)]
          cases k with
          | zero => exact hnot q (Fin.ext (by omega))
          | succ k' =>
            have hqmem : q ∈ before :=
              Finset.mem_filter.2 ⟨Finset.mem_univ _, show (pos q).val < b.val by omega⟩
            have hle := Finset.le_max' _ _ hqmem
            have : (pos q).val ≤ (pos (before.max' hne)).val := hmono.monotone hle
            omega
        · have hprev_val : prevQ = ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩ := dif_neg hne
          rw [Finset.not_nonempty_iff_eq_empty] at hne
          have hge_b : b.val ≤ (pos q).val := by
            by_contra hlt
            have hqmem : q ∈ before :=
              Finset.mem_filter.2 ⟨Finset.mem_univ _, show (pos q).val < b.val by omega⟩
            rw [hne] at hqmem
            exact Finset.notMem_empty _ hqmem
          have hle_last : (pos q).val ≤ (pos ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩).val :=
            hmono.monotone (show q.val ≤ s - 1 by have := q.isLt; omega)
          have hd_eq : d = b.val + t - (pos ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩).val := by
            dsimp only [d]; rw [hprev_val]
            have hgb : b.val < (pos ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩).val := by
              have hneL := hnot ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩
              have : b.val ≤ (pos ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩).val := by
                by_contra hlt
                have hmemL : (⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩ : Fin s) ∈ before :=
                  Finset.mem_filter.2 ⟨Finset.mem_univ _, show (pos _).val < b.val by omega⟩
                rw [hne] at hmemL
                exact Finset.notMem_empty _ hmemL
              have : (pos ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩).val ≠ b.val := fun h => hneL (Fin.ext h)
              omega
            exact Nat.mod_eq_of_lt (by omega)
          by_cases hk_le : k ≤ b.val
          · have hkq : (pos q).val = b.val - k := by
              rw [hk_val]
              have h1 : b.val + k * (t - 1) = (b.val - k) + k * t := by
                cases t with
                | zero => omega
                | succ t' => simp [Nat.mul_succ]; omega
              rw [h1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by have := b.isLt; omega)]
            cases k with
            | zero => exact hnot q (Fin.ext (by omega))
            | succ k' => omega
          · have hkq : (pos q).val = b.val + t - k := by
              rw [hk_val]
              have h1 : b.val + k * (t - 1) = (b.val + t - k) + (k - 1) * t := by
                cases t with
                | zero => omega
                | succ t' =>
                  cases k with
                  | zero => omega
                  | succ k' => simp [Nat.mul_succ, Nat.succ_mul]; omega
              rw [h1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
            omega
      have hres := hwalk (d - 1) b (by rw [Nat.sub_add_cancel hd_pos]; exact hnone)
        (by rw [Nat.sub_add_cancel hd_pos, hreach]; exact (e prevQ).2)
      rw [Nat.sub_add_cancel hd_pos, hreach] at hres
      exact hres.symm
  · let b : Fin t := ⟨i.val / (2 * p), Nat.div_lt_of_lt_mul (by linarith [i.isLt])⟩
    let u : Fin (2 * p) := ⟨i.val % (2 * p), Nat.mod_lt _ (by omega)⟩
    have hi : i = blockIdx b u := by
      ext; simp only [blockIdx, b, u]; exact (Nat.div_add_mod i.val (2 * p)).symm
    conv_lhs => rw [hi]
    conv_rhs => rw [hi]
    by_cases hbm : b ∈ M
    · let q := e.symm ⟨b, hbm⟩
      have hposq : pos q = b := by simp [pos, q]
      rw [← hposq, buildFromPos_at_pos]
      dsimp only [blocks, blockOf]
    · have hnot : ∀ q : Fin s, pos q ≠ b := fun q hq => hbm (hq ▸ (e q).2)
      rw [buildFromPos_at_gap hp hs blocks pos hmono b hnot u]
      have hbu : isMarkedBlock cfg b = false :=
        Bool.eq_false_iff.2 fun h => hbm (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
      have hpe := congrArg (fun f => (f u).2) (unmarked_eq_pure hp ht cfg b hbu)
      simpa [blockOf, pureBlock] using hpe.symm

def templateBlocksValid {p s : ℕ} (hp : 0 < p) (blocks : Fin s → Fin (2 * p) → Bool × Bool) : Prop :=
  ∀ q : Fin s,
    (∃ u : Fin (2 * p),
      (blocks q u).2 = true ∨
      (if hu : 0 < u.val then (blocks q ⟨u.val - 1, by have := u.isLt; omega⟩).1
       else (blocks (prevIdx q) ⟨2 * p - 1, by omega⟩).1) = (blocks q u).1)

lemma buildFromPos_invariants {p m h t1 t2 s : ℕ} (hp : 0 < p) (ht1 : 0 < t1) (ht2 : 0 < t2)
    (hs : 0 < s) (H : Fin (2 * p) → Fin m → ZMod 2) (mixedOnly : Bool)
    (blocks : Fin s → Fin (2 * p) → Bool × Bool) (gmode : Fin s → Fin 3)
    (pos1 : Fin s → Fin t1) (pos2 : Fin s → Fin t2)
    (hv1 : validGapTuple gmode pos1) (hv2 : validGapTuple gmode pos2)
    (htv : templateBlocksValid hp blocks) :
    let cfg1 := buildFromPos hp hs blocks pos1 hv1.1
    let cfg2 := buildFromPos hp hs blocks pos2 hv2.1
    let s1 := fun i => (cfg1 i).1
    let s2 := fun i => (cfg2 i).1
    let K1 := Finset.univ.filter fun i : Fin (2 * p * t1) => (cfg1 i).2 = true
    let K2 := Finset.univ.filter fun i : Fin (2 * p * t2) => (cfg2 i).2 = true
    let col1 : Fin (2 * p * t1) → Fin m → ZMod 2 :=
      fun i => H ⟨i.val % (2 * p), Nat.mod_lt _ (by omega)⟩
    let col2 : Fin (2 * p * t2) → Fin m → ZMod 2 :=
      fun i => H ⟨i.val % (2 * p), Nat.mod_lt _ (by omega)⟩
    (validPair h mixedOnly cfg1 ↔ validPair h mixedOnly cfg2) ∧
    (defectSet s1).card = (defectSet s2).card ∧
    K1.card = K2.card ∧
    runColSet col1 s1 K1 = runColSet col2 s2 K2 := by
  intro cfg1 cfg2 s1 s2 K1 K2 col1 col2
  have hdef_eq : ∀ (t : ℕ) (ht : 0 < t) (pos : Fin s → Fin t) (hmono : StrictMono pos),
      (defectSet (fun i => (buildFromPos hp hs blocks pos hmono i).1)).card =
      ∑ q : Fin s, (Finset.univ.filter fun u : Fin (2 * p) =>
        (if hu : 0 < u.val then (blocks q ⟨u.val - 1, by have := u.isLt; omega⟩).1
         else (blocks (prevIdx q) ⟨2 * p - 1, by omega⟩).1) = (blocks q u).1).card := by
    intro t ht pos hmono
    let cfg := buildFromPos hp hs blocks pos hmono
    have hbij : (defectSet (fun i => (cfg i).1)).card =
        (Finset.univ.biUnion fun q : Fin s =>
          (Finset.univ.filter fun u : Fin (2 * p) =>
            (if hu : 0 < u.val then (blocks q ⟨u.val - 1, by have := u.isLt; omega⟩).1
             else (blocks (prevIdx q) ⟨2 * p - 1, by omega⟩).1) = (blocks q u).1).image
          (fun u => blockIdx (pos q) u)).card := by
      congr 1
      ext i
      let b : Fin t := ⟨i.val / (2 * p), Nat.div_lt_of_lt_mul (by linarith [i.isLt])⟩
      let u : Fin (2 * p) := ⟨i.val % (2 * p), Nat.mod_lt _ (by omega)⟩
      have hi : i = blockIdx b u := by
        ext; simp only [blockIdx, b, u]; exact (Nat.div_add_mod i.val (2 * p)).symm
      rw [hi]
      simp only [defectSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
        Finset.mem_image]
      constructor
      · intro hdef
        by_cases hbm : ∃ q : Fin s, pos q = b
        · obtain ⟨q, hq⟩ := hbm
          refine ⟨q, u, ?_, by rw [hq]⟩
          dsimp only [cfg] at hdef
          rw [← hq, blockIdx_prev hp ht (pos q) u, buildFromPos_at_pos] at hdef
          split_ifs at hdef ⊢ with hu
          · rwa [buildFromPos_at_pos] at hdef
          · rwa [buildFromPos_prevEnd hp ht] at hdef
        · push Not at hbm
          have hunm := buildFromPos_unmarked_gap hp ht hs blocks pos hmono b hbm
          simp only [isMarkedBlock, decide_eq_false_iff_not, not_exists, not_or] at hunm
          exact absurd hdef (hunm u).2
      · rintro ⟨q, u', hu', heq⟩
        have hb_eq : pos q = b := by
          have := congrArg (fun x : Fin (2 * p * t) => x.val / (2 * p)) heq
          simp only [blockIdx, Nat.mul_add_div (show 0 < 2 * p by omega),
            Nat.div_eq_of_lt u'.isLt, Nat.div_eq_of_lt u.isLt, add_zero] at this
          exact Fin.ext this
        have hu_eq : u' = u := by
          have := congrArg (fun x : Fin (2 * p * t) => x.val % (2 * p)) heq
          simp only [blockIdx, Nat.mul_add_mod, Nat.mod_eq_of_lt u'.isLt, Nat.mod_eq_of_lt u.isLt] at this
          exact Fin.ext this
        subst hu_eq
        dsimp only [cfg]
        rw [← hb_eq, blockIdx_prev hp ht (pos q) u, buildFromPos_at_pos]
        split_ifs at hu' ⊢ with hu
        · rwa [buildFromPos_at_pos]
        · rwa [buildFromPos_prevEnd hp ht]
    rw [hbij, Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun q _ => Finset.card_image_of_injective _ fun u1 u2 he => ?_
      have := congrArg Fin.val he
      simp only [blockIdx] at this
      exact Fin.ext (by omega)
    · intro q1 _ q2 _ hne
      simp only [Function.onFun, Finset.disjoint_left, Finset.mem_image]
      rintro _ ⟨u1, _, rfl⟩ ⟨u2, _, he⟩
      have := congrArg (fun x : Fin (2 * p * t) => x.val / (2 * p)) he
      simp only [blockIdx, Nat.mul_add_div (show 0 < 2 * p by omega),
        Nat.div_eq_of_lt u1.isLt, Nat.div_eq_of_lt u2.isLt, add_zero] at this
      exact hne (hmono.injective (Fin.ext this.symm))
  have hK_eq : ∀ (t : ℕ) (ht : 0 < t) (pos : Fin s → Fin t) (hmono : StrictMono pos),
      (Finset.univ.filter fun i : Fin (2 * p * t) =>
        (buildFromPos hp hs blocks pos hmono i).2 = true).card =
      ∑ q : Fin s, (Finset.univ.filter fun u : Fin (2 * p) => (blocks q u).2 = true).card := by
    intro t ht pos hmono
    let cfg := buildFromPos hp hs blocks pos hmono
    have hbij : (Finset.univ.filter fun i : Fin (2 * p * t) => (cfg i).2 = true).card =
        (Finset.univ.biUnion fun q : Fin s =>
          (Finset.univ.filter fun u : Fin (2 * p) => (blocks q u).2 = true).image
            (fun u => blockIdx (pos q) u)).card := by
      congr 1
      ext i
      let b : Fin t := ⟨i.val / (2 * p), Nat.div_lt_of_lt_mul (by linarith [i.isLt])⟩
      let u : Fin (2 * p) := ⟨i.val % (2 * p), Nat.mod_lt _ (by omega)⟩
      have hi : i = blockIdx b u := by
        ext; simp only [blockIdx, b, u]; exact (Nat.div_add_mod i.val (2 * p)).symm
      rw [hi]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_image]
      constructor
      · intro he
        by_cases hbm : ∃ q : Fin s, pos q = b
        · obtain ⟨q, hq⟩ := hbm
          refine ⟨q, u, ?_, by rw [hq]⟩
          dsimp only [cfg] at he
          rw [← hq, buildFromPos_at_pos] at he
          exact he
        · push Not at hbm
          dsimp only [cfg] at he
          rw [buildFromPos_at_gap hp hs blocks pos hmono b hbm u] at he
          simp [pureBlock] at he
      · rintro ⟨q, u', hu', heq⟩
        have hb_eq : pos q = b := by
          have := congrArg (fun x : Fin (2 * p * t) => x.val / (2 * p)) heq
          simp only [blockIdx, Nat.mul_add_div (show 0 < 2 * p by omega),
            Nat.div_eq_of_lt u'.isLt, Nat.div_eq_of_lt u.isLt, add_zero] at this
          exact Fin.ext this
        have hu_eq : u' = u := by
          have := congrArg (fun x : Fin (2 * p * t) => x.val % (2 * p)) heq
          simp only [blockIdx, Nat.mul_add_mod, Nat.mod_eq_of_lt u'.isLt, Nat.mod_eq_of_lt u.isLt] at this
          exact Fin.ext this
        subst hu_eq
        dsimp only [cfg]
        rw [← hb_eq, buildFromPos_at_pos]
        exact hu'
    rw [hbij, Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun q _ => Finset.card_image_of_injective _ fun u1 u2 he => ?_
      have := congrArg Fin.val he; simp only [blockIdx] at this; exact Fin.ext (by omega)
    · intro q1 _ q2 _ hne
      simp only [Function.onFun, Finset.disjoint_left, Finset.mem_image]
      rintro _ ⟨u1, _, rfl⟩ ⟨u2, _, he⟩
      have := congrArg (fun x : Fin (2 * p * t) => x.val / (2 * p)) he
      simp only [blockIdx, Nat.mul_add_div (show 0 < 2 * p by omega),
        Nat.div_eq_of_lt u1.isLt, Nat.div_eq_of_lt u2.isLt, add_zero] at this
      exact hne (hmono.injective (Fin.ext this.symm))
  have hdef12 : (defectSet s1).card = (defectSet s2).card := by
    rw [hdef_eq t1 ht1 pos1 hv1.1, hdef_eq t2 ht2 pos2 hv2.1]
  have hK12 : K1.card = K2.card := by
    rw [hK_eq t1 ht1 pos1 hv1.1, hK_eq t2 ht2 pos2 hv2.1]
  have hgap_nonempty_iff : ∀ (t : ℕ) (ht : 0 < t) (pos : Fin s → Fin t)
      (hv : validGapTuple gmode pos) (q : Fin s),
      (∃ b : Fin t, (∀ q' : Fin s, pos q' ≠ b) ∧
        (if hne : (Finset.univ.filter fun q' : Fin s => pos q' < b).Nonempty
         then (Finset.univ.filter fun q' : Fin s => pos q' < b).max' hne
         else ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩) = q) ↔ 0 < (gmode q).val := by
    intro t ht pos hv q
    have hgm := hv.2 q
    split_ifs at hgm with hlt
    · have hgmV := congrArg Fin.val hgm
      rw [clamp3_val] at hgmV
      constructor
      · rintro ⟨b, hnot, hprev⟩
        by_contra h0
        have hg0 : (gmode q).val = 0 := by omega
        have hdiff0 : (pos ⟨q.val + 1, hlt⟩).val - (pos q).val - 1 = 0 := by omega
        have hlt_b : (pos q).val < b.val := by
          split_ifs at hprev with hne
          · have hm := Finset.max'_mem _ hne
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
            rw [hprev] at hm; exact hm
          · have hqL : q.val = s - 1 := by
              have := congrArg Fin.val hprev
              dsimp only at this
              omega
            omega
        have hle_next : b.val < (pos ⟨q.val + 1, hlt⟩).val := by
          by_contra hge
          have hne_next : (pos ⟨q.val + 1, hlt⟩).val ≠ b.val := fun h => hnot ⟨q.val + 1, hlt⟩ (Fin.ext h)
          have hmem : (⟨q.val + 1, hlt⟩ : Fin s) ∈ Finset.univ.filter fun q' : Fin s => pos q' < b :=
            Finset.mem_filter.2 ⟨Finset.mem_univ _, Fin.mk_lt_mk.2 (by omega)⟩
          have hne : (Finset.univ.filter fun q' : Fin s => pos q' < b).Nonempty := ⟨_, hmem⟩
          rw [dif_pos hne] at hprev
          have hle := Finset.le_max' _ _ hmem
          rw [hprev] at hle
          have : q.val + 1 ≤ q.val := hle
          omega
        omega
      · intro hpos
        have hdiff : 1 ≤ (pos ⟨q.val + 1, hlt⟩).val - (pos q).val - 1 := by omega
        let b : Fin t := ⟨(pos q).val + 1, by have := (pos ⟨q.val + 1, hlt⟩).isLt; omega⟩
        refine ⟨b, ?_, ?_⟩
        · intro q' hq'
          by_cases hle : q' ≤ q
          · have : (pos q').val ≤ (pos q).val := hv.1.monotone hle
            have : (pos q').val = (pos q).val + 1 := congrArg Fin.val hq'
            omega
          · have hge : ⟨q.val + 1, hlt⟩ ≤ q' := Fin.mk_le_mk.2 (by have : q.val < q'.val := lt_of_not_ge hle; omega)
            have : (pos ⟨q.val + 1, hlt⟩).val ≤ (pos q').val := hv.1.monotone hge
            have : (pos q').val = (pos q).val + 1 := congrArg Fin.val hq'
            omega
        · have hmem : q ∈ Finset.univ.filter fun q' : Fin s => pos q' < b :=
            Finset.mem_filter.2 ⟨Finset.mem_univ _, Fin.mk_lt_mk.2 (Nat.lt_succ_self _)⟩
          have hne : (Finset.univ.filter fun q' : Fin s => pos q' < b).Nonempty := ⟨q, hmem⟩
          rw [dif_pos hne]
          have hge := Finset.le_max' _ _ hmem
          have hle : Finset.max' _ hne ≤ q := by
            by_contra hgt
            have hge2 : ⟨q.val + 1, hlt⟩ ≤ Finset.max' _ hne :=
              show q.val + 1 ≤ (Finset.max' _ hne).val by have : q.val < (Finset.max' _ hne).val := lt_of_not_ge hgt; omega
            have h1 : (pos ⟨q.val + 1, hlt⟩).val ≤ (pos (Finset.max' _ hne)).val := hv.1.monotone hge2
            have h2 := Finset.max'_mem _ hne
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h2
            have : (pos (Finset.max' _ hne)).val < (pos q).val + 1 := h2
            omega
          exact le_antisymm hle hge
    · have hqL : q = ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩ := Fin.ext (by dsimp only; have := q.isLt; omega)
      have hgmV := congrArg Fin.val hgm
      rw [clamp3_val] at hgmV
      constructor
      · rintro ⟨b, hnot, hprev⟩
        by_contra h0
        have hg0 : (gmode q).val = 0 := by omega
        have hsum0 : (pos ⟨0, hs⟩).val + (t - 1 - (pos q).val) = 0 := by omega
        split_ifs at hprev with hne
        · have hm := Finset.max'_mem _ hne
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
          rw [hprev] at hm
          have : (pos q).val < b.val := hm
          have := b.isLt
          omega
        · rw [Finset.not_nonempty_iff_eq_empty] at hne
          by_cases hb0 : b.val = 0
          · exact hnot ⟨0, hs⟩ (Fin.ext (by omega))
          · have hmem : (⟨0, hs⟩ : Fin s) ∈ Finset.univ.filter fun q' : Fin s => pos q' < b :=
              Finset.mem_filter.2 ⟨Finset.mem_univ _, Fin.mk_lt_mk.2 (by omega)⟩
            rw [hne] at hmem
            exact Finset.notMem_empty _ hmem
      · intro hpos
        have hsum_pos : 1 ≤ (pos ⟨0, hs⟩).val + (t - 1 - (pos q).val) := by omega
        by_cases ha : 0 < (pos ⟨0, hs⟩).val
        · let b : Fin t := ⟨0, ht⟩
          refine ⟨b, ?_, ?_⟩
          · intro q' hq'
            have : (pos ⟨0, hs⟩).val ≤ (pos q').val := hv.1.monotone (Fin.mk_le_mk.2 (Nat.zero_le _))
            have : (pos q').val = 0 := congrArg Fin.val hq'
            omega
          · have hempty : (Finset.univ.filter fun q' : Fin s => pos q' < b) = ∅ := by
              ext q'; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
              intro h; have : (pos q').val < 0 := h; omega
            rw [dif_neg (by simp [hempty]), ← hqL]
        · have hblt : (pos q).val + 1 < t := by omega
          let b : Fin t := ⟨(pos q).val + 1, hblt⟩
          refine ⟨b, ?_, ?_⟩
          · intro q' hq'
            have : (pos q').val ≤ (pos q).val := hv.1.monotone (Fin.mk_le_mk.2 (by rw [hqL]; have := q'.isLt; omega))
            have : (pos q').val = (pos q).val + 1 := congrArg Fin.val hq'
            omega
          · have hmem : q ∈ Finset.univ.filter fun q' : Fin s => pos q' < b :=
              Finset.mem_filter.2 ⟨Finset.mem_univ _, Fin.mk_lt_mk.2 (Nat.lt_succ_self _)⟩
            have hne : (Finset.univ.filter fun q' : Fin s => pos q' < b).Nonempty := ⟨q, hmem⟩
            rw [dif_pos hne]
            have hge := Finset.le_max' _ _ hmem
            exact le_antisymm (Fin.mk_le_mk.2 (by rw [hqL]; have := (Finset.max' _ hne).isLt; omega)) hge
  have hhas_val : ∀ (t : ℕ) (ht : 0 < t) (pos : Fin s → Fin t) (hv : validGapTuple gmode pos)
      (bpar : Fin 2) (v : Bool),
      (∃ i : Fin (2 * p * t), i.val % 2 = bpar.val ∧ (buildFromPos hp hs blocks pos hv.1 i).1 = v) ↔
      (∃ q : Fin s, ∃ u : Fin (2 * p), u.val % 2 = bpar.val ∧ (blocks q u).1 = v) ∨
      (∃ q : Fin s, 0 < (gmode q).val ∧
        ∃ u : Fin (2 * p), u.val % 2 = bpar.val ∧ (pureBlock p (blocks q ⟨2 * p - 1, by omega⟩).1 u).1 = v) := by
    intro t ht pos hv bpar v
    constructor
    · rintro ⟨i, hip, hiv⟩
      let b : Fin t := ⟨i.val / (2 * p), Nat.div_lt_of_lt_mul (by linarith [i.isLt])⟩
      let u : Fin (2 * p) := ⟨i.val % (2 * p), Nat.mod_lt _ (by omega)⟩
      have hi : i = blockIdx b u := by
        ext; simp only [blockIdx, b, u]; exact (Nat.div_add_mod i.val (2 * p)).symm
      have hup : u.val % 2 = bpar.val := by
        rw [← hip]
        have h1 : i.val = 2 * p * b.val + u.val := (Nat.div_add_mod i.val (2 * p)).symm
        have h2 : 2 * p * b.val = 2 * (p * b.val) := by ring
        rw [h1, h2]
        omega
      rw [hi] at hiv
      by_cases hbm : ∃ q : Fin s, pos q = b
      · obtain ⟨q, hq⟩ := hbm
        left
        refine ⟨q, u, hup, ?_⟩
        rw [← hq, buildFromPos_at_pos] at hiv
        exact hiv
      · push Not at hbm
        right
        let q := if hne : (Finset.univ.filter fun q' : Fin s => pos q' < b).Nonempty
          then (Finset.univ.filter fun q' : Fin s => pos q' < b).max' hne
          else ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩
        have hgp : 0 < (gmode q).val := (hgap_nonempty_iff t ht pos hv q).1 ⟨b, hbm, rfl⟩
        refine ⟨q, hgp, u, hup, ?_⟩
        rw [buildFromPos_at_gap hp hs blocks pos hv.1 b hbm u] at hiv
        exact hiv
    · rintro (⟨q, u, hup, hval⟩ | ⟨q, hgp, u, hup, hval⟩)
      · refine ⟨blockIdx (pos q) u, ?_, ?_⟩
        · simp only [blockIdx]
          have h2 : 2 * p * (pos q).val = 2 * (p * (pos q).val) := by ring
          omega
        · rw [buildFromPos_at_pos]; exact hval
      · obtain ⟨b, hnot, hprev⟩ := (hgap_nonempty_iff t ht pos hv q).2 hgp
        refine ⟨blockIdx b u, ?_, ?_⟩
        · simp only [blockIdx]
          have h2 : 2 * p * b.val = 2 * (p * b.val) := by ring
          omega
        · rw [buildFromPos_at_gap hp hs blocks pos hv.1 b hnot u]
          rw [hprev]
          exact hval
  have he_start_iff : ∀ (t : ℕ) (ht : 0 < t) (pos : Fin s → Fin t) (hv : validGapTuple gmode pos),
      (∀ i : Fin (2 * p * t), (buildFromPos hp hs blocks pos hv.1 i).2 = true →
        isStart (fun j => (buildFromPos hp hs blocks pos hv.1 j).1) i = true) ↔
      (∀ q : Fin s, ∀ u : Fin (2 * p), (blocks q u).2 = true →
        (blocks q u).1 = true ∧
        (if hu : 0 < u.val then (blocks q ⟨u.val - 1, by have := u.isLt; omega⟩).1
         else (blocks (prevIdx q) ⟨2 * p - 1, by omega⟩).1) = false) := by
    intro t ht pos hv
    constructor
    · intro hall q u hu
      have h1 := hall (blockIdx (pos q) u) (by rw [buildFromPos_at_pos]; exact hu)
      simp only [isStart, Bool.and_eq_true, Bool.not_eq_true'] at h1
      rw [buildFromPos_at_pos, blockIdx_prev hp ht (pos q) u] at h1
      refine ⟨h1.1, ?_⟩
      split_ifs at h1 ⊢ with hup
      · rw [buildFromPos_at_pos] at h1; exact h1.2
      · rw [buildFromPos_prevEnd hp ht] at h1; exact h1.2
    · intro hall i hi
      let b : Fin t := ⟨i.val / (2 * p), Nat.div_lt_of_lt_mul (by linarith [i.isLt])⟩
      let u : Fin (2 * p) := ⟨i.val % (2 * p), Nat.mod_lt _ (by omega)⟩
      have hbi : i = blockIdx b u := by
        ext; simp only [blockIdx, b, u]; exact (Nat.div_add_mod i.val (2 * p)).symm
      rw [hbi] at hi ⊢
      by_cases hbm : ∃ q : Fin s, pos q = b
      · obtain ⟨q, hq⟩ := hbm
        rw [← hq, buildFromPos_at_pos] at hi
        obtain ⟨h1, h2⟩ := hall q u hi
        rw [← hq]
        simp only [isStart, Bool.and_eq_true, Bool.not_eq_true']
        rw [buildFromPos_at_pos, blockIdx_prev hp ht (pos q) u]
        refine ⟨h1, ?_⟩
        split_ifs at h2 ⊢ with hup
        · rwa [buildFromPos_at_pos]
        · rwa [buildFromPos_prevEnd hp ht]
      · push Not at hbm
        rw [buildFromPos_at_gap hp hs blocks pos hv.1 b hbm u] at hi
        simp [pureBlock] at hi
  have hvalid12 : validPair h mixedOnly cfg1 ↔ validPair h mixedOnly cfg2 := by
    unfold validPair
    dsimp only
    have hnot1 : (∃ z : Fin (2 * p * t1), s1 z = false) ↔
        (∃ z : Fin (2 * p * t2), s2 z = false) := by
      have h1 : (∃ z : Fin (2 * p * t1), s1 z = false) ↔
          ∃ bpar : Fin 2, ∃ z : Fin (2 * p * t1), z.val % 2 = bpar.val ∧ s1 z = false :=
        ⟨fun ⟨z, hz⟩ => ⟨⟨z.val % 2, Nat.mod_lt _ (by decide)⟩, z, rfl, hz⟩,
         fun ⟨_, z, _, hz⟩ => ⟨z, hz⟩⟩
      have h2 : (∃ z : Fin (2 * p * t2), s2 z = false) ↔
          ∃ bpar : Fin 2, ∃ z : Fin (2 * p * t2), z.val % 2 = bpar.val ∧ s2 z = false :=
        ⟨fun ⟨z, hz⟩ => ⟨⟨z.val % 2, Nat.mod_lt _ (by decide)⟩, z, rfl, hz⟩,
         fun ⟨_, z, _, hz⟩ => ⟨z, hz⟩⟩
      rw [h1, h2]
      exact exists_congr fun bpar => (hhas_val t1 ht1 pos1 hv1 bpar false).trans
        (hhas_val t2 ht2 pos2 hv2 bpar false).symm
    have hmix1 : (isMixed s1 = true) ↔ (isMixed s2 = true) := by
      simp only [isMixed, decide_eq_true_eq]
      exact forall_congr' fun bpar => (hhas_val t1 ht1 pos1 hv1 bpar true).trans
        (hhas_val t2 ht2 pos2 hv2 bpar true).symm
    rw [hnot1, he_start_iff t1 ht1 pos1 hv1, he_start_iff t2 ht2 pos2 hv2, hdef12, hK12, hmix1]
  have hrun_col_sub : ∀ (ta tb : ℕ) (hta : 0 < ta) (htb : 0 < tb)
      (posa : Fin s → Fin ta) (posb : Fin s → Fin tb)
      (hva : validGapTuple gmode posa) (hvb : validGapTuple gmode posb),
      let cfga := buildFromPos hp hs blocks posa hva.1
      let cfgb := buildFromPos hp hs blocks posb hvb.1
      let sa := fun i => (cfga i).1
      let sb := fun i => (cfgb i).1
      let Ka := Finset.univ.filter fun i : Fin (2 * p * ta) => (cfga i).2 = true
      let Kb := Finset.univ.filter fun i : Fin (2 * p * tb) => (cfgb i).2 = true
      let cola : Fin (2 * p * ta) → Fin m → ZMod 2 :=
        fun i => H ⟨i.val % (2 * p), Nat.mod_lt _ (by omega)⟩
      let colb : Fin (2 * p * tb) → Fin m → ZMod 2 :=
        fun i => H ⟨i.val % (2 * p), Nat.mod_lt _ (by omega)⟩
      runColSet cola sa Ka ⊆ runColSet colb sb Kb := by
    intro ta tb hta htb posa posb hva hvb cfga cfgb sa sb Ka Kb cola colb
    rintro v ⟨ja, hja, rfl⟩
    have hjaS : isStart sa ja = true := (Finset.mem_filter.1 (Finset.mem_sdiff.1 hja).1).2
    have hjaK : (cfga ja).2 = false := by
      have hn := (Finset.mem_sdiff.1 hja).2
      simp only [Ka, Finset.mem_filter, Finset.mem_univ, true_and] at hn
      exact Bool.eq_false_iff.2 hn
    have hja_true : sa ja = true := (Eq.mp (Bool.and_eq_true _ _) hjaS).1
    have hja_prev : sa (prevIdx ja) = false := by
      have := (Eq.mp (Bool.and_eq_true _ _) hjaS).2
      simpa using this
    let ba : Fin ta := ⟨ja.val / (2 * p), Nat.div_lt_of_lt_mul (by linarith [ja.isLt])⟩
    let ua : Fin (2 * p) := ⟨ja.val % (2 * p), Nat.mod_lt _ (by omega)⟩
    have hja_eq : ja = blockIdx ba ua := by
      ext; simp only [blockIdx, ba, ua]; exact (Nat.div_add_mod ja.val (2 * p)).symm
    have hsingleton_col : ∀ (t : ℕ) (ht : 0 < t) (pos : Fin s → Fin t) (hv : validGapTuple gmode pos)
        (j : Fin (2 * p * t)),
        let cfg := buildFromPos hp hs blocks pos hv.1
        let st := fun i => (cfg i).1
        isStart st j = true → st (nextIdx j) = false →
        runCol (fun i => H ⟨i.val % (2 * p), Nat.mod_lt _ (by omega)⟩) st j =
          H ⟨j.val % (2 * p), Nat.mod_lt _ (by omega)⟩ := by
      intro t ht pos hv j cfg st hst hnxt
      have hfilt : (Finset.univ.filter fun i : Fin (2 * p * t) =>
          st i = true ∧ walkBack st (2 * p * t) i = j) = {j} := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨hi, hw⟩
          by_contra hne
          have hstep : ∀ k (x : Fin (2 * p * t)), st x = true → x ≠ j →
              walkBack st k x = j → False := by
            intro k
            induction k with
            | zero => intro x _ hne' hw'; exact hne' hw'
            | succ k ih =>
              intro x hx hne' hw'
              simp only [walkBack] at hw'
              split_ifs at hw' with hp'
              · by_cases hpx : prevIdx x = j
                · rw [← hpx, nextIdx_prevIdx] at hnxt
                  exact Bool.noConfusion (hx.symm.trans hnxt)
                · exact ih (prevIdx x) hp' hpx hw'
              · exact hne' hw'
          exact hstep (2 * p * t) i hi hne hw
        · rintro rfl
          exact ⟨(Eq.mp (Bool.and_eq_true _ _) hst).1, walkBack_of_start st i hst _⟩
      ext b
      simp [runCol, hfilt]
    have hrun_by_next : ∀ (t : ℕ) (ht : 0 < t) (pos : Fin s → Fin t) (hv : validGapTuple gmode pos)
        (j : Fin (2 * p * t)) (L : ℕ) (hL : L < 2 * p * t),
        let cfg := buildFromPos hp hs blocks pos hv.1
        let st := fun i => (cfg i).1
        isStart st j = true →
        (∀ r < L, st (nextIdx^[r] j) = true) →
        st (nextIdx^[L] j) = false →
        runCol (fun i => H ⟨i.val % (2 * p), Nat.mod_lt _ (by omega)⟩) st j =
          fun b => ∑ r ∈ Finset.range L, H ⟨(nextIdx^[r] j).val % (2 * p), Nat.mod_lt _ (by omega)⟩ b := by
      intro t ht pos hv j L hL cfg st hst hall hstop
      have hiter_val : ∀ r (x : Fin (2 * p * t)), (nextIdx^[r] x).val = (x.val + r) % (2 * p * t) := by
        intro r
        induction r with
        | zero => intro x; simp [Nat.mod_eq_of_lt x.isLt]
        | succ r ih =>
          intro x
          rw [Function.iterate_succ_apply']
          simp only [nextIdx]
          rw [ih, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, add_assoc]
      have hfilt : (Finset.univ.filter fun i : Fin (2 * p * t) =>
          st i = true ∧ walkBack st (2 * p * t) i = j) =
          (Finset.range L).image (fun r => nextIdx^[r] j) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_range]
        constructor
        · rintro ⟨hi, hw⟩
          have hrec : ∀ k (x : Fin (2 * p * t)), st x = true → walkBack st k x = j →
              ∃ r < L, nextIdx^[r] j = x := by
            intro k
            induction k with
            | zero =>
              intro x _ hx
              have hLpos : 0 < L := by
                by_contra h0
                have hL0 : L = 0 := by omega
                rw [hL0] at hstop
                exact Bool.noConfusion ((Eq.mp (Bool.and_eq_true _ _) hst).1.symm.trans hstop)
              exact ⟨0, hLpos, hx.symm⟩
            | succ k ih =>
              intro x hx hw'
              simp only [walkBack] at hw'
              split_ifs at hw' with hp'
              · obtain ⟨r, hr, hrx⟩ := ih (prevIdx x) hp' hw'
                have hnxt_eq : nextIdx^[r + 1] j = x := by
                  rw [Function.iterate_succ_apply', hrx, nextIdx_prevIdx]
                have hr1 : r + 1 < L := by
                  by_contra hge
                  have heq : r + 1 = L := by omega
                  rw [← heq, hnxt_eq] at hstop
                  exact Bool.noConfusion (hx.symm.trans hstop)
                exact ⟨r + 1, hr1, hnxt_eq⟩
              · have hLpos : 0 < L := by
                  by_contra h0
                  have hL0 : L = 0 := by omega
                  rw [hL0] at hstop
                  exact Bool.noConfusion ((Eq.mp (Bool.and_eq_true _ _) hst).1.symm.trans hstop)
                exact ⟨0, hLpos, hw'.symm⟩
          exact hrec (2 * p * t) i hi hw
        · rintro ⟨r, hr, rfl⟩
          refine ⟨hall r hr, ?_⟩
          have hback : ∀ m ≤ r, ∀ k, m ≤ k → walkBack st k (nextIdx^[m] j) = j := by
            intro m
            induction m with
            | zero => intro _ k _; exact walkBack_of_start st j hst k
            | succ m ihm =>
              intro hm k hk
              cases k with
              | zero => omega
              | succ k =>
                simp only [walkBack, Function.iterate_succ_apply', prevIdx_nextIdx]
                rw [if_pos (hall m (by omega))]
                exact ihm (by omega) k (by omega)
          exact hback r le_rfl (2 * p * t) (by omega)
      ext b
      simp only [runCol, hfilt]
      rw [Finset.sum_image]
      intro r1 hr1 r2 hr2 heq
      simp only [Finset.mem_coe, Finset.mem_range] at hr1 hr2
      have h1 := congrArg Fin.val heq
      rw [hiter_val, hiter_val] at h1
      have hq1 := Nat.div_add_mod (j.val + r1) (2 * p * t)
      have hq2 := Nat.div_add_mod (j.val + r2) (2 * p * t)
      have hn : 0 < 2 * p * t := by positivity
      have hdiv : (j.val + r1) / (2 * p * t) = (j.val + r2) / (2 * p * t) := by
        have hlt1 : j.val + r1 < 2 * p * t * 2 := by have := j.isLt; omega
        have hlt2 : j.val + r2 < 2 * p * t * 2 := by have := j.isLt; omega
        have h1d : (j.val + r1) / (2 * p * t) = 0 ∨ (j.val + r1) / (2 * p * t) = 1 := by
          have hlt1' : (j.val + r1) / (2 * p * t) < 2 := Nat.div_lt_of_lt_mul hlt1
          rcases Nat.lt_succ_iff_lt_or_eq.1 hlt1' with hlt0 | heq1
          · exact Or.inl (Nat.lt_one_iff.1 hlt0)
          · exact Or.inr heq1
        have h2d : (j.val + r2) / (2 * p * t) = 0 ∨ (j.val + r2) / (2 * p * t) = 1 := by
          have hlt2' : (j.val + r2) / (2 * p * t) < 2 := Nat.div_lt_of_lt_mul hlt2
          rcases Nat.lt_succ_iff_lt_or_eq.1 hlt2' with hlt0 | heq1
          · exact Or.inl (Nat.lt_one_iff.1 hlt0)
          · exact Or.inr heq1
        have h1e : 2 * p * t * 0 = 0 := mul_zero _
        have h2e : 2 * p * t * 1 = 2 * p * t := mul_one _
        rcases h1d with h1d | h1d <;> rcases h2d with h2d | h2d <;>
          simp only [h1d, h2d, h1e, h2e] at hq1 hq2 ⊢ <;> omega
      have hmul : (2 * p * t) * ((j.val + r1) / (2 * p * t)) = (2 * p * t) * ((j.val + r2) / (2 * p * t)) :=
        congrArg ((2 * p * t) * ·) hdiv
      omega
    let prevQOf : ∀ {t : ℕ} (pos : Fin s → Fin t) (b : Fin t), Fin s := fun pos b =>
      if hne : (Finset.univ.filter fun q' : Fin s => pos q' < b).Nonempty
      then (Finset.univ.filter fun q' : Fin s => pos q' < b).max' hne
      else ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩
    have hprevQ_step : ∀ {t : ℕ} (ht : 0 < t) (pos : Fin s → Fin t) (x : Fin t),
        (∀ q' : Fin s, pos q' ≠ x) → (∀ q' : Fin s, pos q' ≠ prevIdx x) →
        prevQOf pos (prevIdx x) = prevQOf pos x := by
      intro t ht pos x hx hpx
      dsimp only [prevQOf]
      by_cases hx0 : x.val = 0
      · have he1 : (Finset.univ.filter fun q' : Fin s => pos q' < x) = ∅ := by
          ext q'; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          intro h; have : (pos q').val < 0 := by rw [← hx0]; exact h
          omega
        have hpxv : (prevIdx x).val = t - 1 := by
          simp [prevIdx, hx0, Nat.mod_eq_of_lt (Nat.sub_lt ht (Nat.succ_pos 0))]
        have he2 : (Finset.univ.filter fun q' : Fin s => pos q' < prevIdx x) = Finset.univ := by
          ext q'; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
          have hne1 : (pos q').val ≠ t - 1 := fun h => hpx q' (Fin.ext (h.trans hpxv.symm))
          exact show (pos q').val < (prevIdx x).val by rw [hpxv]; have := (pos q').isLt; omega
        have huniv_ne : (Finset.univ : Finset (Fin s)).Nonempty :=
          Finset.univ_nonempty_iff.2 ⟨⟨0, hs⟩⟩
        simp only [he1, he2, huniv_ne, ↓reduceDIte, Finset.not_nonempty_empty]
        have hge := Finset.le_max' (Finset.univ : Finset (Fin s))
          (⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩ : Fin s) (Finset.mem_univ _)
        exact le_antisymm (Fin.mk_le_mk.2 (by have := ((Finset.univ : Finset (Fin s)).max' huniv_ne).isLt; omega)) hge
      · have hpxv : (prevIdx x).val = x.val - 1 := by
          simp only [prevIdx]
          have : x.val + (t - 1) = (x.val - 1) + t := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by have := x.isLt; omega)]
        have heq : (Finset.univ.filter fun q' : Fin s => pos q' < prevIdx x) =
            (Finset.univ.filter fun q' : Fin s => pos q' < x) := by
          ext q'; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro h
            have hlt : (pos q').val < x.val - 1 := by rw [← hpxv]; exact h
            exact show (pos q').val < x.val by omega
          · intro h
            have hne1 : (pos q').val ≠ x.val - 1 := fun he => hpx q' (Fin.ext (he.trans hpxv.symm))
            exact show (pos q').val < (prevIdx x).val by rw [hpxv]; have : (pos q').val < x.val := h; omega
        simp only [heq]
    have hprevQ_before_pos : ∀ {t : ℕ} (ht : 0 < t) (pos : Fin s → Fin t) (hmono : StrictMono pos)
        (r : Fin s), (∀ q'' : Fin s, pos q'' ≠ prevIdx (pos r)) →
        prevQOf pos (prevIdx (pos r)) = prevIdx r := by
      intro t ht pos hmono r hmem
      dsimp only [prevQOf]
      split_ifs with hne
      · have hmax := Finset.max'_mem _ hne
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmax
        by_cases hq0 : r.val = 0
        · have hprev_q : prevIdx r = ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩ := by
            ext; simp [prevIdx, hq0, Nat.mod_eq_of_lt (Nat.sub_lt hs (Nat.succ_pos 0))]
          rw [hprev_q]
          by_cases hp0 : (pos r).val = 0
          · have hprev0 : (prevIdx (pos r)).val = t - 1 := by
              simp [prevIdx, hp0, Nat.mod_eq_of_lt (Nat.sub_lt ht (Nat.succ_pos 0))]
            have hlast_mem : (⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩ : Fin s) ∈
                Finset.univ.filter fun q' : Fin s => pos q' < prevIdx (pos r) := by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              have hneL := hmem ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩
              have hltL : (pos ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩).val < t :=
                (pos ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩).isLt
              have hneVal : (pos ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩).val ≠ t - 1 :=
                fun h => hneL (Fin.ext (h.trans hprev0.symm))
              exact show (pos ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩).val < (prevIdx (pos r)).val by rw [hprev0]; omega
            have hge := Finset.le_max' _ _ hlast_mem
            exact le_antisymm (Fin.mk_le_mk.2 (by have := (Finset.max' _ hne).isLt; omega)) hge
          · have hprev1 : (prevIdx (pos r)).val = (pos r).val - 1 := by
              simp only [prevIdx]
              have : (pos r).val + (t - 1) = ((pos r).val - 1) + t := by omega
              rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by have := (pos r).isLt; omega)]
            have hle : pos r ≤ pos (Finset.max' _ hne) :=
              hmono.monotone (Fin.mk_le_mk.2 (by omega))
            have : (pos r).val ≤ (pos (Finset.max' _ hne)).val := hle
            have : (pos (Finset.max' _ hne)).val < (pos r).val - 1 := by rw [← hprev1]; exact hmax
            omega
        · have hprev_q : (prevIdx r).val = r.val - 1 := by
            simp only [prevIdx]
            have : r.val + (s - 1) = (r.val - 1) + s := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by have := r.isLt; omega)]
          have hp_pos : 0 < (pos r).val := by
            have := hmono (Fin.mk_lt_mk.2 (show 0 < r.val by omega) : ⟨0, hs⟩ < r)
            have : (pos ⟨0, hs⟩).val < (pos r).val := this
            omega
          have hprev1 : (prevIdx (pos r)).val = (pos r).val - 1 := by
            simp only [prevIdx]
            have : (pos r).val + (t - 1) = ((pos r).val - 1) + t := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by have := (pos r).isLt; omega)]
          have hmemP : prevIdx r ∈ Finset.univ.filter fun q' : Fin s => pos q' < prevIdx (pos r) := by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            have hlt1 : (pos (prevIdx r)).val < (pos r).val :=
              hmono (show (prevIdx r).val < r.val by rw [hprev_q]; omega)
            have hne1 : (pos (prevIdx r)).val ≠ (pos r).val - 1 :=
              fun h => hmem (prevIdx r) (Fin.ext (h.trans hprev1.symm))
            exact show (pos (prevIdx r)).val < (prevIdx (pos r)).val by rw [hprev1]; omega
          have hge := Finset.le_max' _ _ hmemP
          have hltM : Finset.max' _ hne < r := by
            by_contra hnotlt
            have hle : r ≤ Finset.max' _ hne := le_of_not_gt hnotlt
            have : (pos r).val ≤ (pos (Finset.max' _ hne)).val := hmono.monotone hle
            have : (pos (Finset.max' _ hne)).val < (pos r).val - 1 := by rw [← hprev1]; exact hmax
            omega
          exact Fin.ext (by have : (Finset.max' _ hne).val < r.val := hltM; have : (prevIdx r).val ≤ (Finset.max' _ hne).val := hge; omega)
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        have hq0 : r.val = 0 := by
          by_contra hq0'
          have hprev_q : (prevIdx r).val = r.val - 1 := by
            simp only [prevIdx]
            have : r.val + (s - 1) = (r.val - 1) + s := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by have := r.isLt; omega)]
          have hp_pos : 0 < (pos r).val := by
            have := hmono (Fin.mk_lt_mk.2 (show 0 < r.val by omega) : ⟨0, hs⟩ < r)
            have : (pos ⟨0, hs⟩).val < (pos r).val := this
            omega
          have hprev1 : (prevIdx (pos r)).val = (pos r).val - 1 := by
            simp only [prevIdx]
            have : (pos r).val + (t - 1) = ((pos r).val - 1) + t := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by have := (pos r).isLt; omega)]
          have hlt1 : (pos (prevIdx r)).val < (pos r).val :=
            hmono (show (prevIdx r).val < r.val by rw [hprev_q]; omega)
          have hne1 : (pos (prevIdx r)).val ≠ (pos r).val - 1 :=
            fun h => hmem (prevIdx r) (Fin.ext (h.trans hprev1.symm))
          have hmemP : prevIdx r ∈ Finset.univ.filter fun q' : Fin s => pos q' < prevIdx (pos r) :=
            Finset.mem_filter.2 ⟨Finset.mem_univ _, show (pos (prevIdx r)).val < (prevIdx (pos r)).val by rw [hprev1]; omega⟩
          rw [hne] at hmemP
          exact Finset.notMem_empty _ hmemP
        ext
        simp [prevIdx, hq0, Nat.mod_eq_of_lt (Nat.sub_lt hs (Nat.succ_pos 0))]
    have hnext_pos_eq : ∀ {t : ℕ} (ht : 0 < t) (pos : Fin s → Fin t) (hv : validGapTuple gmode pos)
        (q : Fin s), pos (nextIdx q) = nextIdx (pos q) ↔ (gmode q).val = 0 := by
      intro t ht pos hv q
      have hgm := hv.2 q
      split_ifs at hgm with hlt
      · have hgmV := congrArg Fin.val hgm
        rw [clamp3_val] at hgmV
        have hnq : nextIdx q = ⟨q.val + 1, hlt⟩ := by
          ext; simp [nextIdx, Nat.mod_eq_of_lt hlt]
        have hlt_pos : (pos q).val < (pos ⟨q.val + 1, hlt⟩).val :=
          hv.1 (Fin.mk_lt_mk.2 (Nat.lt_succ_self q.val))
        have hnp : (nextIdx (pos q)).val = (pos q).val + 1 := by
          simp only [nextIdx]; exact Nat.mod_eq_of_lt (by have := (pos ⟨q.val + 1, hlt⟩).isLt; omega)
        rw [hnq, Fin.ext_iff, hnp]
        omega
      · have hgmV := congrArg Fin.val hgm
        rw [clamp3_val] at hgmV
        have hqL : q.val = s - 1 := by have := q.isLt; omega
        have hnq : nextIdx q = ⟨0, hs⟩ := by
          ext; simp only [nextIdx]
          have : q.val + 1 = s := by omega
          rw [this, Nat.mod_self]
        rw [hnq]
        by_cases hlast : (pos q).val + 1 = t
        · have hnp : (nextIdx (pos q)).val = 0 := by
            simp only [nextIdx]; rw [hlast, Nat.mod_self]
          rw [Fin.ext_iff, hnp]
          omega
        · have hnp : (nextIdx (pos q)).val = (pos q).val + 1 := by
            simp only [nextIdx]; exact Nat.mod_eq_of_lt (by have := (pos q).isLt; omega)
          have hle0 : (pos ⟨0, hs⟩).val ≤ (pos q).val :=
            hv.1.monotone (Fin.mk_le_mk.2 (Nat.zero_le _))
          rw [Fin.ext_iff, hnp]
          have := (pos q).isLt
          omega
    have hfirst_gap : ∀ {t : ℕ} (ht : 0 < t) (pos : Fin s → Fin t) (hv : validGapTuple gmode pos)
        (q : Fin s), 0 < (gmode q).val →
        (∀ q' : Fin s, pos q' ≠ nextIdx (pos q)) ∧ prevQOf pos (nextIdx (pos q)) = q := by
      intro t ht pos hv q hgpos
      have hnot : ∀ q' : Fin s, pos q' ≠ nextIdx (pos q) := by
        intro q' hq'
        have hgm := hv.2 q
        split_ifs at hgm with hlt
        · have hgmV := congrArg Fin.val hgm
          rw [clamp3_val] at hgmV
          have hlt_pos : (pos q).val < (pos ⟨q.val + 1, hlt⟩).val :=
            hv.1 (Fin.mk_lt_mk.2 (Nat.lt_succ_self q.val))
          have hnp : (nextIdx (pos q)).val = (pos q).val + 1 := by
            simp only [nextIdx]; exact Nat.mod_eq_of_lt (by have := (pos ⟨q.val + 1, hlt⟩).isLt; omega)
          have hq'v : (pos q').val = (pos q).val + 1 := by rw [hq', hnp]
          have hq_lt : q < q' := by
            by_contra hle
            have : (pos q').val ≤ (pos q).val := hv.1.monotone (le_of_not_gt hle)
            omega
          have hge : ⟨q.val + 1, hlt⟩ ≤ q' := Fin.mk_le_mk.2 (by have : q.val < q'.val := hq_lt; omega)
          have : (pos ⟨q.val + 1, hlt⟩).val ≤ (pos q').val := hv.1.monotone hge
          omega
        · have hgmV := congrArg Fin.val hgm
          rw [clamp3_val] at hgmV
          have hqL : q.val = s - 1 := by have := q.isLt; omega
          have hle_q : (pos q').val ≤ (pos q).val :=
            hv.1.monotone (Fin.mk_le_mk.2 (by have := q'.isLt; omega))
          have hge_0 : (pos ⟨0, hs⟩).val ≤ (pos q').val :=
            hv.1.monotone (Fin.mk_le_mk.2 (Nat.zero_le _))
          by_cases hlast : (pos q).val + 1 = t
          · have hnp : (nextIdx (pos q)).val = 0 := by
              simp only [nextIdx]; rw [hlast, Nat.mod_self]
            have hq'v : (pos q').val = 0 := by rw [hq', hnp]
            omega
          · have hnp : (nextIdx (pos q)).val = (pos q).val + 1 := by
              simp only [nextIdx]; exact Nat.mod_eq_of_lt (by have := (pos q).isLt; omega)
            have hq'v : (pos q').val = (pos q).val + 1 := by rw [hq', hnp]
            omega
      refine ⟨hnot, ?_⟩
      dsimp only [prevQOf]
      by_cases hlast : (pos q).val + 1 = t
      · have hnp : (nextIdx (pos q)).val = 0 := by
          simp only [nextIdx]; rw [hlast, Nat.mod_self]
        have hempty : (Finset.univ.filter fun q' : Fin s => pos q' < nextIdx (pos q)) = ∅ := by
          ext q'; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          intro h; have : (pos q').val < 0 := by rw [← hnp]; exact h
          omega
        rw [dif_neg (by simp [hempty])]
        ext
        by_contra hne
        have hlt : q < ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩ :=
          lt_of_le_of_ne (Fin.mk_le_mk.2 (by have := q.isLt; omega)) (fun h => hne (congrArg Fin.val h).symm)
        have h1 : (pos q).val < (pos ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩).val := hv.1 hlt
        have h2 := (pos ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩).isLt
        omega
      · have hnp : (nextIdx (pos q)).val = (pos q).val + 1 := by
          simp only [nextIdx]; exact Nat.mod_eq_of_lt (by have := (pos q).isLt; omega)
        have hmem : q ∈ Finset.univ.filter fun q' : Fin s => pos q' < nextIdx (pos q) :=
          Finset.mem_filter.2 ⟨Finset.mem_univ _, show (pos q).val < (nextIdx (pos q)).val by rw [hnp]; omega⟩
        have hne : (Finset.univ.filter fun q' : Fin s => pos q' < nextIdx (pos q)).Nonempty := ⟨q, hmem⟩
        rw [dif_pos hne]
        have hge := Finset.le_max' _ _ hmem
        have hle : Finset.max' _ hne ≤ q := by
          by_contra hgt
          have hltq : q < Finset.max' _ hne := lt_of_not_ge hgt
          have h1 : (pos q).val < (pos (Finset.max' _ hne)).val := hv.1 hltq
          have h2 := Finset.max'_mem _ hne
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h2
          have h3 : (pos (Finset.max' _ hne)).val < (pos q).val + 1 := by rw [← hnp]; exact h2
          omega
        exact le_antisymm hle hge
    have hgap2_second : ∀ {t : ℕ} (ht : 0 < t) (pos : Fin s → Fin t) (hv : validGapTuple gmode pos)
        (q : Fin s), (gmode q).val = 2 →
        ∀ q' : Fin s, pos q' ≠ nextIdx (nextIdx (pos q)) := by
      intro t ht pos hv q hg2 q' hq'
      have hgm := hv.2 q
      split_ifs at hgm with hlt
      · have hgmV := congrArg Fin.val hgm
        rw [clamp3_val, hg2] at hgmV
        have hlt_pos : (pos q).val + 2 < (pos ⟨q.val + 1, hlt⟩).val := by omega
        have hlt_t : (pos q).val + 2 < t := lt_trans hlt_pos (pos ⟨q.val + 1, hlt⟩).isLt
        have hn2 : (nextIdx (nextIdx (pos q))).val = (pos q).val + 2 := by
          simp only [nextIdx]
          have h1lt : (pos q).val + 1 < t := by omega
          rw [Nat.mod_eq_of_lt h1lt, Nat.mod_eq_of_lt hlt_t]
        have hq'v : (pos q').val = (pos q).val + 2 := by rw [hq', hn2]
        by_cases hle : q' ≤ q
        · have : (pos q').val ≤ (pos q).val := hv.1.monotone hle
          omega
        · have hge : ⟨q.val + 1, hlt⟩ ≤ q' :=
            Fin.mk_le_mk.2 (by have : q.val < q'.val := lt_of_not_ge hle; omega)
          have : (pos ⟨q.val + 1, hlt⟩).val ≤ (pos q').val := hv.1.monotone hge
          omega
      · have hgmV := congrArg Fin.val hgm
        rw [clamp3_val, hg2] at hgmV
        have hqL : q.val = s - 1 := by have := q.isLt; omega
        have hle_q : (pos q').val ≤ (pos q).val :=
          hv.1.monotone (Fin.mk_le_mk.2 (by have := q'.isLt; omega))
        have hge_0 : (pos ⟨0, hs⟩).val ≤ (pos q').val :=
          hv.1.monotone (Fin.mk_le_mk.2 (Nat.zero_le _))
        by_cases h2lt : (pos q).val + 2 < t
        · have hn2 : (nextIdx (nextIdx (pos q))).val = (pos q).val + 2 := by
            simp only [nextIdx]
            have h1lt : (pos q).val + 1 < t := by omega
            rw [Nat.mod_eq_of_lt h1lt, Nat.mod_eq_of_lt h2lt]
          have hq'v : (pos q').val = (pos q).val + 2 := by rw [hq', hn2]
          omega
        · by_cases h1lt : (pos q).val + 1 < t
          · have h1eq : (pos q).val + 2 = t := by omega
            have hn2 : (nextIdx (nextIdx (pos q))).val = 0 := by
              simp only [nextIdx]
              rw [Nat.mod_eq_of_lt h1lt, h1eq, Nat.mod_self]
            have hq'v : (pos q').val = 0 := by rw [hq', hn2]
            omega
          · have h1eq : (pos q).val + 1 = t := by have := (pos q).isLt; omega
            have ht2 : 2 ≤ t := by have := (pos ⟨0, hs⟩).isLt; omega
            have hn2 : (nextIdx (nextIdx (pos q))).val = 1 := by
              simp only [nextIdx]
              rw [h1eq, Nat.mod_self, zero_add, Nat.mod_eq_of_lt (by omega)]
            have hq'v : (pos q').val = 1 := by rw [hq', hn2]
            omega
    have htwo_gap_gives_2 : ∀ {t : ℕ} (ht : 0 < t) (pos : Fin s → Fin t) (hv : validGapTuple gmode pos)
        (b : Fin t) (q : Fin s),
        (∀ q' : Fin s, pos q' ≠ b) → (∀ q' : Fin s, pos q' ≠ nextIdx b) →
        prevQOf pos b = q → (gmode q).val = 2 := by
      intro t ht pos hv b q hnot1 hnot2 hprev
      have hgm := hv.2 q
      split_ifs at hgm with hlt
      · have hgmV := congrArg Fin.val hgm
        rw [clamp3_val] at hgmV
        dsimp only [prevQOf] at hprev
        split_ifs at hprev with hne
        · have hmax := Finset.max'_mem _ hne
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmax
          rw [hprev] at hmax
          have hblt : b.val < (pos ⟨q.val + 1, hlt⟩).val := by
            by_contra hge
            have hne1 : (pos ⟨q.val + 1, hlt⟩).val ≠ b.val := fun h => hnot1 ⟨q.val + 1, hlt⟩ (Fin.ext h)
            have hmem : (⟨q.val + 1, hlt⟩ : Fin s) ∈ Finset.univ.filter fun q' : Fin s => pos q' < b :=
              Finset.mem_filter.2 ⟨Finset.mem_univ _, Fin.mk_lt_mk.2 (by omega)⟩
            have hle := Finset.le_max' _ _ hmem
            rw [hprev] at hle
            have : q.val + 1 ≤ q.val := hle
            omega
          have hnb : (nextIdx b).val = b.val + 1 := by
            simp only [nextIdx]; exact Nat.mod_eq_of_lt (by have := (pos ⟨q.val + 1, hlt⟩).isLt; omega)
          have hne2 : b.val + 1 ≠ (pos ⟨q.val + 1, hlt⟩).val :=
            fun h => hnot2 ⟨q.val + 1, hlt⟩ (Fin.ext (h.symm.trans hnb.symm))
          have : (pos q).val < b.val := hmax
          omega
        · have hqL : q.val = s - 1 := by rw [← hprev]
          omega
      · have hgmV := congrArg Fin.val hgm
        rw [clamp3_val] at hgmV
        dsimp only [prevQOf] at hprev
        split_ifs at hprev with hne
        · have hmax := Finset.max'_mem _ hne
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmax
          rw [hprev] at hmax
          have : (pos q).val < b.val := hmax
          by_cases hlast : b.val + 1 = t
          · have hnb : (nextIdx b).val = 0 := by
              simp only [nextIdx]; rw [hlast, Nat.mod_self]
            have hne0 : (pos ⟨0, hs⟩).val ≠ 0 :=
              fun h => hnot2 ⟨0, hs⟩ (Fin.ext (h.trans hnb.symm))
            omega
          · have := b.isLt; omega
        · rw [Finset.not_nonempty_iff_eq_empty] at hne
          have hblt : b.val < (pos ⟨0, hs⟩).val := by
            by_contra hge
            have hne0 : (pos ⟨0, hs⟩).val ≠ b.val := fun h => hnot1 ⟨0, hs⟩ (Fin.ext h)
            have hmem : (⟨0, hs⟩ : Fin s) ∈ Finset.univ.filter fun q' : Fin s => pos q' < b :=
              Finset.mem_filter.2 ⟨Finset.mem_univ _, Fin.mk_lt_mk.2 (by omega)⟩
            rw [hne] at hmem
            exact Finset.notMem_empty _ hmem
          have hnb : (nextIdx b).val = b.val + 1 := by
            simp only [nextIdx]; exact Nat.mod_eq_of_lt (by have := (pos ⟨0, hs⟩).isLt; omega)
          have hne2 : b.val + 1 ≠ (pos ⟨0, hs⟩).val :=
            fun h => hnot2 ⟨0, hs⟩ (Fin.ext (h.symm.trans hnb.symm))
          omega
    by_cases hgap_sing : (∀ q : Fin s, posa q ≠ ba) ∧ sa (nextIdx ja) = false
    · obtain ⟨hnot, hnxt⟩ := hgap_sing
      dsimp only [cola, sa, cfga]
      rw [hsingleton_col ta hta posa hva ja hjaS hnxt]
      let q := prevQOf posa ba
      have hgp : 0 < (gmode q).val := (hgap_nonempty_iff ta hta posa hva q).1 ⟨ba, hnot, rfl⟩
      have hua_true : (pureBlock p (blocks q ⟨2 * p - 1, by omega⟩).1 ua).1 = true := by
        dsimp only [sa, cfga] at hja_true
        rw [hja_eq, buildFromPos_at_gap hp hs blocks posa hva.1 ba hnot ua] at hja_true
        exact hja_true
      let bb : Fin tb := nextIdx (posb q)
      have hbb_info := hfirst_gap htb posb hvb q hgp
      have hnotb : ∀ q' : Fin s, posb q' ≠ bb := hbb_info.1
      have hprevb : prevQOf posb bb = q := hbb_info.2
      have hcaseb : ua.val + 1 < 2 * p ∨ (∀ q' : Fin s, posb q' ≠ nextIdx bb) ∨
          (blocks (nextIdx q) ⟨0, by omega⟩).1 = false := by
        by_cases hu1 : ua.val + 1 < 2 * p
        · exact Or.inl hu1
        · by_cases hblk0 : (blocks (nextIdx q) ⟨0, by omega⟩).1 = false
          · exact Or.inr (Or.inr hblk0)
          · right; left
            have hblk0t : (blocks (nextIdx q) ⟨0, by omega⟩).1 = true :=
              Bool.eq_true_of_not_eq_false hblk0
            have hna_unm : ∀ q' : Fin s, posa q' ≠ nextIdx ba := by
              intro q' hq'
              have hq'eq : q' = nextIdx q := by
                have h1 : prevIdx (posa q') = ba := by rw [hq', prevIdx_nextIdx]
                have h2 : prevQOf posa (prevIdx (posa q')) = prevIdx q' :=
                  hprevQ_before_pos hta posa hva.1 q' (by rwa [h1])
                have h3 : prevIdx q' = q := by rw [← h2, h1]
                rw [← h3, nextIdx_prevIdx]
              dsimp only [sa, cfga] at hnxt
              rw [hja_eq, blockIdx_next hp hta ba ua, dif_neg hu1, ← hq', buildFromPos_at_pos, hq'eq] at hnxt
              exact Bool.noConfusion (hblk0t.symm.trans hnxt)
            have hg2 : (gmode q).val = 2 := htwo_gap_gives_2 hta posa hva ba q hnot hna_unm rfl
            exact hgap2_second htb posb hvb q hg2
      have hnext_is_false : sb (nextIdx (blockIdx bb ua)) = false := by
        dsimp only [sb, cfgb]
        rw [blockIdx_next hp htb bb ua]
        split_ifs with hu1
        · rw [buildFromPos_at_gap hp hs blocks posb hvb.1 bb hnotb]
          change (pureBlock p (blocks (prevQOf posb bb) ⟨2 * p - 1, by omega⟩).1 ⟨ua.val + 1, hu1⟩).1 = false
          rw [hprevb]
          simp only [pureBlock] at hua_true ⊢
          cases hpe : (blocks q ⟨2 * p - 1, by omega⟩).1 <;>
            simp only [hpe, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq, decide_eq_false_iff_not] at hua_true ⊢ <;> omega
        · rcases hcaseb with hlt | hnext_gap | hblk0
          · exact absurd hlt hu1
          · rw [buildFromPos_at_gap hp hs blocks posb hvb.1 (nextIdx bb) hnext_gap]
            change (pureBlock p (blocks (prevQOf posb (nextIdx bb)) ⟨2 * p - 1, by omega⟩).1 _).1 = false
            have hprev_next : prevQOf posb (nextIdx bb) = q := by
              have h1 := hprevQ_step htb posb (nextIdx bb) hnext_gap (by rwa [prevIdx_nextIdx])
              rw [prevIdx_nextIdx, hprevb] at h1
              exact h1.symm
            rw [hprev_next]
            simp only [pureBlock] at hua_true ⊢
            have hua_last : ua.val = 2 * p - 1 := by have := ua.isLt; omega
            rw [hua_last] at hua_true
            have hmod : (2 * p - 1) % 2 = 1 := by omega
            cases hpe : (blocks q ⟨2 * p - 1, by omega⟩).1 <;> simp [hpe, hmod] at hua_true ⊢
          · by_cases hnext_m : ∃ q' : Fin s, posb q' = nextIdx bb
            · obtain ⟨q', hq'⟩ := hnext_m
              rw [← hq', buildFromPos_at_pos]
              have hq'eq : q' = nextIdx q := by
                have h1 : prevIdx (posb q') = bb := by rw [hq', prevIdx_nextIdx]
                have h2 : prevQOf posb (prevIdx (posb q')) = prevIdx q' :=
                  hprevQ_before_pos htb posb hvb.1 q' (by rwa [h1])
                have h3 : prevIdx q' = q := by rw [← h2, h1, hprevb]
                rw [← h3, nextIdx_prevIdx]
              rw [hq'eq]
              exact hblk0
            · push Not at hnext_m
              rw [buildFromPos_at_gap hp hs blocks posb hvb.1 (nextIdx bb) hnext_m]
              change (pureBlock p (blocks (prevQOf posb (nextIdx bb)) ⟨2 * p - 1, by omega⟩).1 _).1 = false
              have hprev_next : prevQOf posb (nextIdx bb) = q := by
                have h1 := hprevQ_step htb posb (nextIdx bb) hnext_m (by rwa [prevIdx_nextIdx])
                rw [prevIdx_nextIdx, hprevb] at h1
                exact h1.symm
              rw [hprev_next]
              simp only [pureBlock] at hua_true ⊢
              have hua_last : ua.val = 2 * p - 1 := by have := ua.isLt; omega
              rw [hua_last] at hua_true
              have hmod : (2 * p - 1) % 2 = 1 := by omega
              cases hpe : (blocks q ⟨2 * p - 1, by omega⟩).1 <;> simp [hpe, hmod] at hua_true ⊢
      let jb := blockIdx bb ua
      have hjb_unm := buildFromPos_unmarked_gap hp htb hs blocks posb hvb.1 bb hnotb
      have hjb_true : sb jb = true := by
        dsimp only [sb, cfgb, jb]
        rw [buildFromPos_at_gap hp hs blocks posb hvb.1 bb hnotb ua]
        change (pureBlock p (blocks (prevQOf posb bb) ⟨2 * p - 1, by omega⟩).1 ua).1 = true
        rw [hprevb]; exact hua_true
      have hjb_prev : sb (prevIdx jb) = false := by
        simp only [isMarkedBlock, decide_eq_false_iff_not, not_exists, not_or] at hjb_unm
        have hne := (hjb_unm ua).2
        change sb (prevIdx jb) ≠ sb jb at hne
        rw [hjb_true] at hne
        exact Bool.eq_false_iff.2 hne
      have hjb_start : isStart sb jb = true := by
        simp [isStart, hjb_true, hjb_prev]
      have hjb_notK : jb ∉ Kb := by
        simp only [Kb, Finset.mem_filter, Finset.mem_univ, true_and, cfgb, jb]
        rw [buildFromPos_at_gap hp hs blocks posb hvb.1 bb hnotb ua]
        simp [pureBlock]
      refine ⟨jb, Finset.mem_sdiff.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hjb_start⟩, hjb_notK⟩, ?_⟩
      dsimp only [colb, sb, cfgb]
      rw [hsingleton_col tb htb posb hvb jb hjb_start hnext_is_false]
      have hmod_eq : jb.val % (2 * p) = ja.val % (2 * p) := by
        simp only [jb, blockIdx, Nat.mul_add_mod, Nat.mod_eq_of_lt ua.isLt, ua]
      have hfin : (⟨jb.val % (2 * p), Nat.mod_lt _ (by omega)⟩ : Fin (2 * p)) =
          ⟨ja.val % (2 * p), Nat.mod_lt _ (by omega)⟩ := Fin.ext hmod_eq
      rw [hfin]
    · have hwalk_marked : ∀ (q0 : Fin s) (u0 : Fin (2 * p)) (r : ℕ),
          (∀ k < r, sa (nextIdx^[k] (blockIdx (posa q0) u0)) = true) →
          (∃ q' u', nextIdx^[r] (blockIdx (posa q0) u0) = blockIdx (posa q') u' ∧
            nextIdx^[r] (blockIdx (posb q0) u0) = blockIdx (posb q') u') ∨
          (sa (nextIdx^[r] (blockIdx (posa q0) u0)) = false ∧
            sb (nextIdx^[r] (blockIdx (posb q0) u0)) = false) := by
        intro q0 u0 r
        induction r with
        | zero => intro _; exact Or.inl ⟨q0, u0, rfl, rfl⟩
        | succ r ih =>
          intro hall
          have hprev := ih fun k hk => hall k (by omega)
          rcases hprev with ⟨q', u', hqa, hqb⟩ | ⟨hfa, _⟩
          · rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hqa, hqb,
              blockIdx_next hp hta, blockIdx_next hp htb]
            split_ifs with hu1
            · exact Or.inl ⟨q', ⟨u'.val + 1, hu1⟩, rfl, rfl⟩
            · by_cases hg0 : (gmode q').val = 0
              · rw [← (hnext_pos_eq hta posa hva q').2 hg0,
                  ← (hnext_pos_eq htb posb hvb q').2 hg0]
                exact Or.inl ⟨nextIdx q', ⟨0, by omega⟩, rfl, rfl⟩
              · right
                have hgpos : 0 < (gmode q').val := Nat.pos_of_ne_zero hg0
                have hna_unm := (hfirst_gap hta posa hva q' hgpos).1
                have hnb_unm := (hfirst_gap htb posb hvb q' hgpos).1
                have hu_last : u' = ⟨2 * p - 1, by omega⟩ := Fin.ext (by dsimp only; have := u'.isLt; omega)
                have hpa_t : sa (blockIdx (posa q') u') = true := by
                  rw [← hqa]; exact hall r (Nat.lt_succ_self r)
                have hpb_t : sb (blockIdx (posb q') u') = true := by
                  dsimp only [sb, cfgb]
                  rw [buildFromPos_at_pos]
                  dsimp only [sa, cfga] at hpa_t
                  rwa [buildFromPos_at_pos] at hpa_t
                have hma := buildFromPos_unmarked_gap hp hta hs blocks posa hva.1 (nextIdx (posa q')) hna_unm
                have hmb := buildFromPos_unmarked_gap hp htb hs blocks posb hvb.1 (nextIdx (posb q')) hnb_unm
                simp only [isMarkedBlock, decide_eq_false_iff_not, not_exists, not_or] at hma hmb
                have hnea := (hma ⟨0, by omega⟩).2
                have hneb := (hmb ⟨0, by omega⟩).2
                change sa (prevIdx (blockIdx (nextIdx (posa q')) ⟨0, by omega⟩)) ≠
                  sa (blockIdx (nextIdx (posa q')) ⟨0, by omega⟩) at hnea
                change sb (prevIdx (blockIdx (nextIdx (posb q')) ⟨0, by omega⟩)) ≠
                  sb (blockIdx (nextIdx (posb q')) ⟨0, by omega⟩) at hneb
                rw [blockIdx_prev_zero hp hta, prevIdx_nextIdx, ← hu_last, hpa_t] at hnea
                rw [blockIdx_prev_zero hp htb, prevIdx_nextIdx, ← hu_last, hpb_t] at hneb
                exact ⟨Bool.eq_false_iff.2 hnea.symm, Bool.eq_false_iff.2 hneb.symm⟩
          · exact absurd (hall r (Nat.lt_succ_self r)) (by rw [hfa]; decide)
      have hiter_prev : ∀ {n : ℕ} (hn : 0 < n) (x : Fin n), nextIdx^[n - 1] x = prevIdx x := by
        intro n hn x
        have hiter_val : ∀ r (y : Fin n), (nextIdx^[r] y).val = (y.val + r) % n := by
          intro r
          induction r with
          | zero => intro y; simp [Nat.mod_eq_of_lt y.isLt]
          | succ r ih =>
            intro y
            rw [Function.iterate_succ_apply']
            simp only [nextIdx]
            rw [ih, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, add_assoc]
        ext
        rw [hiter_val]
        rfl
      have hex_stop : ∃ k : ℕ, sa (nextIdx^[k] ja) = false :=
        ⟨2 * p * ta - 1, by rw [hiter_prev (by positivity) ja]; exact hja_prev⟩
      let L : ℕ := Nat.find hex_stop
      have hL_stop : sa (nextIdx^[L] ja) = false := Nat.find_spec hex_stop
      have hL_all : ∀ r < L, sa (nextIdx^[r] ja) = true := fun r hr =>
        Bool.eq_true_of_not_eq_false (Nat.find_min hex_stop hr)
      have hL_lta : L < 2 * p * ta := by
        have hle : L ≤ 2 * p * ta - 1 := Nat.find_min' hex_stop (by rw [hiter_prev (by positivity) ja]; exact hja_prev)
        have : 0 < 2 * p * ta := by positivity
        omega
      by_cases hbm : ∃ q : Fin s, posa q = ba
      · obtain ⟨q, hq⟩ := hbm
        have hja_pos : ja = blockIdx (posa q) ua := by rw [hq]; exact hja_eq
        let jb : Fin (2 * p * tb) := blockIdx (posb q) ua
        have hjb_true : sb jb = true := by
          dsimp only [sb, cfgb, jb]; rw [buildFromPos_at_pos]
          dsimp only [sa, cfga] at hja_true
          rwa [hja_pos, buildFromPos_at_pos] at hja_true
        have hjb_prev : sb (prevIdx jb) = false := by
          dsimp only [sb, cfgb, jb]; rw [blockIdx_prev hp htb]
          dsimp only [sa, cfga] at hja_prev
          rw [hja_pos, blockIdx_prev hp hta] at hja_prev
          split_ifs at hja_prev ⊢ with hu
          · rw [buildFromPos_at_pos] at hja_prev ⊢; exact hja_prev
          · rw [buildFromPos_prevEnd hp hta] at hja_prev
            rw [buildFromPos_prevEnd hp htb]
            exact hja_prev
        have hjb_start : isStart sb jb = true := by simp [isStart, hjb_true, hjb_prev]
        have hjb_notK : jb ∉ Kb := by
          simp only [Kb, Finset.mem_filter, Finset.mem_univ, true_and, cfgb, jb]
          rw [buildFromPos_at_pos]
          dsimp only [cfga] at hjaK
          rw [hja_pos, buildFromPos_at_pos] at hjaK
          rw [hjaK]; decide
        have hstep_eq : ∀ r ≤ L, sa (nextIdx^[r] ja) = sb (nextIdx^[r] jb) := by
          intro r hr
          have hw := hwalk_marked q ua r (fun k hk => by rw [← hja_pos]; exact hL_all k (by omega))
          rw [← hja_pos] at hw
          rcases hw with ⟨q', u', hqa, hqb⟩ | ⟨hfa, hfb⟩
          · dsimp only [sa, cfga, sb, cfgb]
            rw [hqa, hqb, buildFromPos_at_pos, buildFromPos_at_pos]
          · rw [hfa, hfb]
        have hL_all_b : ∀ r < L, sb (nextIdx^[r] jb) = true := fun r hr =>
          (hstep_eq r (le_of_lt hr)).symm.trans (hL_all r hr)
        have hL_stop_b : sb (nextIdx^[L] jb) = false :=
          (hstep_eq L le_rfl).symm.trans hL_stop
        have hL_ltb : L < 2 * p * tb := by
          by_contra hge
          have hpos_tb : 0 < 2 * p * tb := by positivity
          have h1 : 2 * p * tb - 1 < L := by omega
          have h2 := hL_all_b (2 * p * tb - 1) h1
          rw [hiter_prev hpos_tb jb, hjb_prev] at h2
          exact Bool.noConfusion h2
        refine ⟨jb, Finset.mem_sdiff.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hjb_start⟩, hjb_notK⟩, ?_⟩
        dsimp only [cola, colb, sa, sb, cfga, cfgb]
        rw [hrun_by_next ta hta posa hva ja L hL_lta hjaS hL_all hL_stop,
          hrun_by_next tb htb posb hvb jb L hL_ltb hjb_start hL_all_b hL_stop_b]
        ext b
        refine Finset.sum_congr rfl fun r hr => ?_
        have hrl : r < L := Finset.mem_range.1 hr
        have hw := hwalk_marked q ua r (fun k hk => by rw [← hja_pos]; exact hL_all k (by omega))
        rw [← hja_pos] at hw
        rcases hw with ⟨q', u', hqa, hqb⟩ | ⟨hfa, _⟩
        · have hm : (nextIdx^[r] ja).val % (2 * p) = (nextIdx^[r] jb).val % (2 * p) := by
            rw [hqa, hqb]; simp only [blockIdx, Nat.mul_add_mod, Nat.mod_eq_of_lt u'.isLt]
          have hfin : (⟨(nextIdx^[r] ja).val % (2 * p), Nat.mod_lt _ (by omega)⟩ : Fin (2 * p)) =
              ⟨(nextIdx^[r] jb).val % (2 * p), Nat.mod_lt _ (by omega)⟩ := Fin.ext hm
          rw [hfin]
        · exact absurd (hL_all r hrl) (by rw [hfa]; decide)
      · push Not at hbm
        have hnxt_t : sa (nextIdx ja) = true := by
          by_contra hne
          exact hgap_sing ⟨hbm, Bool.eq_false_iff.2 hne⟩
        have hua_last : ua = ⟨2 * p - 1, by omega⟩ := by
          by_contra hne
          have hu1 : ua.val + 1 < 2 * p := by
            have := ua.isLt; have : ua.val ≠ 2 * p - 1 := fun h => hne (Fin.ext h); omega
          have hunm := buildFromPos_unmarked_gap hp hta hs blocks posa hva.1 ba hbm
          simp only [isMarkedBlock, decide_eq_false_iff_not, not_exists, not_or] at hunm
          have hne2 := (hunm ⟨ua.val + 1, hu1⟩).2
          change sa (prevIdx (blockIdx ba ⟨ua.val + 1, hu1⟩)) ≠ sa (blockIdx ba ⟨ua.val + 1, hu1⟩) at hne2
          have hnx : nextIdx ja = blockIdx ba ⟨ua.val + 1, hu1⟩ := by
            rw [hja_eq, blockIdx_next hp hta ba ua, dif_pos hu1]
          rw [← hnx, prevIdx_nextIdx, hja_true, hnxt_t] at hne2
          exact hne2 rfl
        have hna_marked : ∃ q : Fin s, posa q = nextIdx ba := by
          by_contra hnone
          push Not at hnone
          have hunm := buildFromPos_unmarked_gap hp hta hs blocks posa hva.1 (nextIdx ba) hnone
          simp only [isMarkedBlock, decide_eq_false_iff_not, not_exists, not_or] at hunm
          have hne2 := (hunm ⟨0, by omega⟩).2
          change sa (prevIdx (blockIdx (nextIdx ba) ⟨0, by omega⟩)) ≠
            sa (blockIdx (nextIdx ba) ⟨0, by omega⟩) at hne2
          have hnx : nextIdx ja = blockIdx (nextIdx ba) ⟨0, by omega⟩ := by
            conv_lhs => rw [hja_eq]
            rw [blockIdx_next hp hta ba ua, dif_neg (by rw [hua_last]; dsimp only; omega)]
          rw [← hnx, prevIdx_nextIdx, hja_true, hnxt_t] at hne2
          exact hne2 rfl
        obtain ⟨q, hq⟩ := hna_marked
        have hba_eq : ba = prevIdx (posa q) := by rw [hq, prevIdx_nextIdx]
        have hja_eq2 : ja = blockIdx (prevIdx (posa q)) ⟨2 * p - 1, by omega⟩ := by
          rw [← hba_eq, ← hua_last]; exact hja_eq
        have hprev_gpos : 0 < (gmode (prevIdx q)).val := by
          by_contra h0
          have hg0 : (gmode (prevIdx q)).val = 0 := by omega
          have h1 := (hnext_pos_eq hta posa hva (prevIdx q)).2 hg0
          rw [nextIdx_prevIdx] at h1
          have h2 : posa (prevIdx q) = ba := by rw [hba_eq, h1, prevIdx_nextIdx]
          exact hbm (prevIdx q) h2
        have hpb_unm : ∀ q' : Fin s, posb q' ≠ prevIdx (posb q) := by
          intro q' hq'
          have hne_g : (gmode (prevIdx q)).val ≠ 0 := by omega
          have h1 := (hnext_pos_eq htb posb hvb (prevIdx q)).not.2 hne_g
          rw [nextIdx_prevIdx] at h1
          have hq'eq : q' = prevIdx q := by
            have hlt_lem := (hfirst_gap htb posb hvb (prevIdx q) hprev_gpos).1
            have hprev_pos : prevIdx (posb q) = posb q' := hq'.symm
            have hnb := congrArg nextIdx hprev_pos
            rw [nextIdx_prevIdx] at hnb
            by_cases hq0 : q.val = 0
            · have hpq : prevIdx q = ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩ := by
                ext; simp [prevIdx, hq0, Nat.mod_eq_of_lt (Nat.sub_lt hs (Nat.succ_pos 0))]
              rw [hpq]
              by_contra hneL
              have hlt : q' < ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩ :=
                lt_of_le_of_ne (Fin.mk_le_mk.2 (by have := q'.isLt; omega)) hneL
              have hltp : (posb q').val < (posb ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩).val := hvb.1 hlt
              by_cases hp0 : (posb q).val = 0
              · have hpv : (prevIdx (posb q)).val = tb - 1 := by
                  simp [prevIdx, hp0, Nat.mod_eq_of_lt (Nat.sub_lt htb (Nat.succ_pos 0))]
                have : (posb q').val = tb - 1 := by rw [hq', hpv]
                have := (posb ⟨s - 1, Nat.sub_lt hs (Nat.succ_pos 0)⟩).isLt
                omega
              · have hpv : (prevIdx (posb q)).val = (posb q).val - 1 := by
                  simp only [prevIdx]
                  have : (posb q).val + (tb - 1) = ((posb q).val - 1) + tb := by omega
                  rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by have := (posb q).isLt; omega)]
                have hle0 : (posb q).val ≤ (posb q').val := hvb.1.monotone (Fin.mk_le_mk.2 (by omega))
                have : (posb q').val = (posb q).val - 1 := by rw [hq', hpv]
                omega
            · have hpq : (prevIdx q).val = q.val - 1 := by
                simp only [prevIdx]
                have : q.val + (s - 1) = (q.val - 1) + s := by omega
                rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by have := q.isLt; omega)]
              have hp_pos : 0 < (posb q).val := by
                have := hvb.1 (Fin.mk_lt_mk.2 (show 0 < q.val by omega) : ⟨0, hs⟩ < q)
                have : (posb ⟨0, hs⟩).val < (posb q).val := this
                omega
              have hpv : (prevIdx (posb q)).val = (posb q).val - 1 := by
                simp only [prevIdx]
                have : (posb q).val + (tb - 1) = ((posb q).val - 1) + tb := by omega
                rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by have := (posb q).isLt; omega)]
              have hq'lt : q' < q := by
                by_contra hge
                have : (posb q).val ≤ (posb q').val := hvb.1.monotone (le_of_not_gt hge)
                have : (posb q').val = (posb q).val - 1 := by rw [hq', hpv]
                omega
              have hq'ge : prevIdx q ≤ q' := by
                by_contra hlt
                have h1' : (posb q').val < (posb (prevIdx q)).val := hvb.1 (lt_of_not_ge hlt)
                have h2' : (posb (prevIdx q)).val < (posb q).val :=
                  hvb.1 (show (prevIdx q).val < q.val by rw [hpq]; omega)
                have : (posb q').val = (posb q).val - 1 := by rw [hq', hpv]
                omega
              exact Fin.ext (by have : q'.val < q.val := hq'lt; have : (prevIdx q).val ≤ q'.val := hq'ge; omega)
          rw [hq'eq] at hq'
          have h2 := congrArg nextIdx hq'
          rw [nextIdx_prevIdx] at h2
          exact h1 h2.symm
        let jb : Fin (2 * p * tb) := blockIdx (prevIdx (posb q)) ⟨2 * p - 1, by omega⟩
        have hjb_true : sb jb = true := by
          dsimp only [sb, cfgb, jb]; rw [buildFromPos_prevEnd hp htb]
          dsimp only [sa, cfga] at hja_true
          rwa [hja_eq2, buildFromPos_prevEnd hp hta] at hja_true
        have hjb_unm := buildFromPos_unmarked_gap hp htb hs blocks posb hvb.1 (prevIdx (posb q)) hpb_unm
        have hjb_prev : sb (prevIdx jb) = false := by
          simp only [isMarkedBlock, decide_eq_false_iff_not, not_exists, not_or] at hjb_unm
          have hne := (hjb_unm ⟨2 * p - 1, by omega⟩).2
          change sb (prevIdx jb) ≠ sb jb at hne
          rw [hjb_true] at hne
          exact Bool.eq_false_iff.2 hne
        have hjb_start : isStart sb jb = true := by simp [isStart, hjb_true, hjb_prev]
        have hjb_notK : jb ∉ Kb := by
          simp only [Kb, Finset.mem_filter, Finset.mem_univ, true_and, cfgb, jb]
          rw [buildFromPos_at_gap hp hs blocks posb hvb.1 (prevIdx (posb q)) hpb_unm]
          simp [pureBlock]
        have hnotlt2p : ¬ ((⟨2 * p - 1, by omega⟩ : Fin (2 * p)).val + 1 < 2 * p) := by dsimp only; omega
        have hnxt_ja : nextIdx ja = blockIdx (posa q) ⟨0, by omega⟩ := by
          conv_lhs => rw [hja_eq2]
          rw [blockIdx_next hp hta, dif_neg hnotlt2p, nextIdx_prevIdx]
        have hnxt_jb : nextIdx jb = blockIdx (posb q) ⟨0, by omega⟩ := by
          dsimp only [jb]
          rw [blockIdx_next hp htb, dif_neg hnotlt2p, nextIdx_prevIdx]
        have hstep_eq : ∀ r ≤ L, sa (nextIdx^[r] ja) = sb (nextIdx^[r] jb) := by
          intro r hr
          cases r with
          | zero => simp [hja_true, hjb_true]
          | succ r' =>
            rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hnxt_ja, hnxt_jb]
            have hw := hwalk_marked q ⟨0, by omega⟩ r' (fun k hk => by
              rw [← hnxt_ja, ← Function.iterate_succ_apply]
              exact hL_all (k + 1) (by omega))
            rcases hw with ⟨q', u', hqa, hqb⟩ | ⟨hfa, hfb⟩
            · dsimp only [sa, cfga, sb, cfgb]
              rw [hqa, hqb, buildFromPos_at_pos, buildFromPos_at_pos]
            · rw [hfa, hfb]
        have hL_all_b : ∀ r < L, sb (nextIdx^[r] jb) = true := fun r hr =>
          (hstep_eq r (le_of_lt hr)).symm.trans (hL_all r hr)
        have hL_stop_b : sb (nextIdx^[L] jb) = false :=
          (hstep_eq L le_rfl).symm.trans hL_stop
        have hL_ltb : L < 2 * p * tb := by
          by_contra hge
          have hpos_tb : 0 < 2 * p * tb := by positivity
          have h1 : 2 * p * tb - 1 < L := by omega
          have h2 := hL_all_b (2 * p * tb - 1) h1
          rw [hiter_prev hpos_tb jb, hjb_prev] at h2
          exact Bool.noConfusion h2
        refine ⟨jb, Finset.mem_sdiff.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hjb_start⟩, hjb_notK⟩, ?_⟩
        dsimp only [cola, colb, sa, sb, cfga, cfgb]
        rw [hrun_by_next ta hta posa hva ja L hL_lta hjaS hL_all hL_stop,
          hrun_by_next tb htb posb hvb jb L hL_ltb hjb_start hL_all_b hL_stop_b]
        ext b
        refine Finset.sum_congr rfl fun r hr => ?_
        have hrl : r < L := Finset.mem_range.1 hr
        cases r with
        | zero =>
          simp only [Function.iterate_zero_apply]
          have hm : ja.val % (2 * p) = jb.val % (2 * p) := by
            rw [hja_eq2]
            simp only [jb, blockIdx, Nat.mul_add_mod, Nat.mod_eq_of_lt (show 2 * p - 1 < 2 * p by omega)]
          have hfin : (⟨ja.val % (2 * p), Nat.mod_lt _ (by omega)⟩ : Fin (2 * p)) =
              ⟨jb.val % (2 * p), Nat.mod_lt _ (by omega)⟩ := Fin.ext hm
          rw [hfin]
        | succ r' =>
          rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hnxt_ja, hnxt_jb]
          have hw := hwalk_marked q ⟨0, by omega⟩ r' (fun k hk => by
            rw [← hnxt_ja, ← Function.iterate_succ_apply]
            exact hL_all (k + 1) (by omega))
          rcases hw with ⟨q', u', hqa, hqb⟩ | ⟨hfa, _⟩
          · have hm : (nextIdx^[r'] (blockIdx (p := p) (posa q) ⟨0, by omega⟩)).val % (2 * p) =
                (nextIdx^[r'] (blockIdx (p := p) (posb q) ⟨0, by omega⟩)).val % (2 * p) := by
              rw [hqa, hqb]; simp only [blockIdx, Nat.mul_add_mod, Nat.mod_eq_of_lt u'.isLt]
            have hfin : (⟨(nextIdx^[r'] (blockIdx (p := p) (posa q) ⟨0, by omega⟩)).val % (2 * p),
                Nat.mod_lt _ (by omega)⟩ : Fin (2 * p)) =
                ⟨(nextIdx^[r'] (blockIdx (p := p) (posb q) ⟨0, by omega⟩)).val % (2 * p),
                  Nat.mod_lt _ (by omega)⟩ := Fin.ext hm
            rw [hfin]
          · have h1 := hL_all (r' + 1) hrl
            rw [Function.iterate_succ_apply, hnxt_ja, hfa] at h1
            exact Bool.noConfusion h1
  exact ⟨hvalid12, hdef12, hK12, Set.Subset.antisymm
    (hrun_col_sub t1 t2 ht1 ht2 pos1 pos2 hv1 hv2)
    (hrun_col_sub t2 t1 ht2 ht1 pos2 pos1 hv2 hv1)⟩

def pureCycleCfg {p t : ℕ} (b0 : Bool) : Fin (2 * p * t) → Bool × Bool :=
  fun i => (if b0 then decide (i.val % 2 = 0) else decide (i.val % 2 = 1), false)

lemma pureCycleCfg_unmarked {p t : ℕ} (hp : 0 < p) (ht : 0 < t) (b0 : Bool) (b : Fin t) :
    isMarkedBlock (pureCycleCfg (p := p) (t := t) b0) b = false := by
  simp only [isMarkedBlock, decide_eq_false_iff_not, not_exists, not_or]
  intro u
  refine ⟨by simp [pureCycleCfg], ?_⟩
  simp only [pureCycleCfg]
  have hn : 0 < 2 * p * t := by positivity
  have hprev_val : (prevIdx (blockIdx b u)).val % 2 ≠ (blockIdx b u).val % 2 := by
    simp only [prevIdx]
    by_cases h0 : (blockIdx b u).val = 0
    · rw [h0, zero_add, Nat.mod_eq_of_lt (Nat.sub_lt hn (Nat.succ_pos 0))]
      have h2pt : 2 * p * t = 2 * (p * t) := by ring
      have hmod : (2 * p * t - 1) % 2 = 1 := by omega
      omega
    · have h1 : (blockIdx b u).val + (2 * p * t - 1) = ((blockIdx b u).val - 1) + 2 * p * t := by omega
      have hlt : (blockIdx b u).val - 1 < 2 * p * t := by have := (blockIdx b u).isLt; omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
      omega
  cases b0 <;> simp only [↓reduceIte, ne_eq, decide_eq_decide] <;>
    · intro hiff
      by_cases hm : (blockIdx b u).val % 2 = 0 <;> simp_all <;> omega

lemma eq_pureCycleCfg_of_no_marked {p t : ℕ} (hp : 0 < p) (ht : 0 < t)
    (cfg : Fin (2 * p * t) → Bool × Bool)
    (h0 : (Finset.univ.filter fun b : Fin t => isMarkedBlock cfg b = true).card = 0) :
    cfg = pureCycleCfg (cfg ⟨0, by positivity⟩).1 := by
  have hall_unm : ∀ i : Fin (2 * p * t), (cfg i).2 = false ∧ (cfg (prevIdx i)).1 ≠ (cfg i).1 := by
    intro i
    let b : Fin t := ⟨i.val / (2 * p), Nat.div_lt_of_lt_mul (by linarith [i.isLt])⟩
    let u : Fin (2 * p) := ⟨i.val % (2 * p), Nat.mod_lt _ (by omega)⟩
    have hi : i = blockIdx b u := by ext; simp only [blockIdx, b, u]; exact (Nat.div_add_mod i.val (2 * p)).symm
    have hbu : isMarkedBlock cfg b = false := by
      by_contra hne
      have hbt : isMarkedBlock cfg b = true := Bool.eq_true_of_not_eq_false hne
      have hpos : 0 < (Finset.univ.filter fun b' : Fin t => isMarkedBlock cfg b' = true).card :=
        Finset.card_pos.2 ⟨b, Finset.mem_filter.2 ⟨Finset.mem_univ _, hbt⟩⟩
      omega
    simp only [isMarkedBlock, decide_eq_false_iff_not, not_exists, not_or] at hbu
    rw [hi]
    exact ⟨Bool.eq_false_iff.2 (hbu u).1, (hbu u).2⟩
  have hfst : ∀ k (hk : k < 2 * p * t),
      (cfg ⟨k, hk⟩).1 = (if (cfg ⟨0, by positivity⟩).1 then decide (k % 2 = 0) else decide (k % 2 = 1)) := by
    intro k
    induction k with
    | zero => intro hk; cases h : (cfg ⟨0, by positivity⟩).1 <;> simp [h]
    | succ k ih =>
      intro hk
      have hk' : k < 2 * p * t := Nat.lt_of_succ_lt hk
      have hprev : prevIdx ⟨k + 1, hk⟩ = ⟨k, hk'⟩ := by
        ext
        simp only [prevIdx]
        have hn : 0 < 2 * p * t := by positivity
        have h1 : k + 1 + (2 * p * t - 1) = k + 2 * p * t := by omega
        rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hk']
      have hne := (hall_unm ⟨k + 1, hk⟩).2
      rw [hprev, ih hk'] at hne
      cases h0 : (cfg ⟨0, by positivity⟩).1 <;> cases h1 : (cfg ⟨k + 1, hk⟩).1 <;> simp_all <;> omega
  ext i
  · exact hfst i.val i.isLt
  · exact (hall_unm i).1

lemma pureCycleCfg_invariants {p m h t : ℕ} (hp : 0 < p) (ht : 0 < t)
    (H : Fin (2 * p) → Fin m → ZMod 2) (mixedOnly : Bool) (b0 : Bool) :
    let cfg := pureCycleCfg (p := p) (t := t) b0
    let s := fun i => (cfg i).1
    let K := Finset.univ.filter fun i : Fin (2 * p * t) => (cfg i).2 = true
    let col : Fin (2 * p * t) → Fin m → ZMod 2 :=
      fun i => H ⟨i.val % (2 * p), Nat.mod_lt _ (by omega)⟩
    (validPair h mixedOnly cfg ↔ mixedOnly = false) ∧
    (defectSet s).card = 0 ∧
    K.card = 0 ∧
    runColSet col s K = (fun u : Fin (2 * p) => H u) ''
      {u : Fin (2 * p) | (if b0 then decide (u.val % 2 = 0) else decide (u.val % 2 = 1)) = true} := by
  intro cfg s K col
  have hdef : defectSet s = ∅ := by
    ext i
    simp only [defectSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    let b : Fin t := ⟨i.val / (2 * p), Nat.div_lt_of_lt_mul (by linarith [i.isLt])⟩
    let u : Fin (2 * p) := ⟨i.val % (2 * p), Nat.mod_lt _ (by omega)⟩
    have hi : i = blockIdx b u := by ext; simp only [blockIdx, b, u]; exact (Nat.div_add_mod i.val (2 * p)).symm
    have hbu := pureCycleCfg_unmarked hp ht b0 b
    simp only [isMarkedBlock, decide_eq_false_iff_not, not_exists, not_or] at hbu
    rw [hi]
    exact (hbu u).2
  have hK : K = ∅ := by ext i; simp [K, cfg, pureCycleCfg]
  have hnotmixed : isMixed s = false := by
    simp only [isMixed, decide_eq_false_iff_not, not_forall]
    cases b0
    · refine ⟨⟨0, by decide⟩, fun ⟨i, hi, hs⟩ => ?_⟩
      simp only [s, cfg, pureCycleCfg, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at hs
      change i.val % 2 = 0 at hi
      omega
    · refine ⟨⟨1, by decide⟩, fun ⟨i, hi, hs⟩ => ?_⟩
      simp only [s, cfg, pureCycleCfg, ↓reduceIte, decide_eq_true_eq] at hs
      change i.val % 2 = 1 at hi
      omega
  have hvalid : validPair h mixedOnly cfg ↔ mixedOnly = false := by
    have hfalse : ∃ z : Fin (2 * p * t), s z = false := by
      cases b0
      · exact ⟨⟨0, by positivity⟩, by simp [s, cfg, pureCycleCfg]⟩
      · exact ⟨⟨1, by have h2 : 2 ≤ 2 * p * t := (by nlinarith); omega⟩, by simp [s, cfg, pureCycleCfg]⟩
    have he : ∀ i : Fin (2 * p * t), (cfg i).2 = true → isStart s i = true := fun i hi => by
      simp [cfg, pureCycleCfg] at hi
    constructor
    · intro hv
      cases hmx : mixedOnly
      · rfl
      · have hm := hv.2.2.2 hmx
        exact Bool.noConfusion (hnotmixed.symm.trans hm)
    · intro hmf
      refine ⟨hfalse, he, ?_, fun h' => Bool.noConfusion (hmf.symm.trans h')⟩
      change (defectSet s).card / 2 + K.card ≤ h
      rw [hdef, hK]
      simp
  have hrcs : runColSet col s K = (fun u : Fin (2 * p) => H u) ''
      {u : Fin (2 * p) | (if b0 then decide (u.val % 2 = 0) else decide (u.val % 2 = 1)) = true} := by
    have hsing : ∀ i : Fin (2 * p * t), s i = true →
        isStart s i = true ∧ runCol col s i = col i := by
      intro i hi
      have hne_prev : s (prevIdx i) ≠ s i := fun h =>
        Finset.notMem_empty i (hdef ▸ Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
      have hne_next : s i ≠ s (nextIdx i) := fun h => by
        have h1 : s (prevIdx (nextIdx i)) = s (nextIdx i) := by rwa [prevIdx_nextIdx]
        exact Finset.notMem_empty (nextIdx i) (hdef ▸ Finset.mem_filter.2 ⟨Finset.mem_univ _, h1⟩)
      have hpf : s (prevIdx i) = false := Bool.eq_false_iff.2 (by rwa [hi] at hne_prev)
      have hnf : s (nextIdx i) = false := Bool.eq_false_iff.2 (fun h => hne_next (hi.trans h.symm))
      have hst : isStart s i = true := by simp [isStart, hi, hpf]
      refine ⟨hst, ?_⟩
      have hfilt : (Finset.univ.filter fun j : Fin (2 * p * t) =>
          s j = true ∧ walkBack s (2 * p * t) j = i) = {i} := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨hj, hw⟩
          by_contra hne
          have hstep : ∀ k (x : Fin (2 * p * t)), s x = true → x ≠ i →
              walkBack s k x = i → False := by
            intro k
            induction k with
            | zero => intro x _ hne' hw'; exact hne' hw'
            | succ k ih =>
              intro x hx hne' hw'
              simp only [walkBack] at hw'
              split_ifs at hw' with hp'
              · by_cases hpx : prevIdx x = i
                · rw [← hpx, nextIdx_prevIdx] at hnf
                  exact Bool.noConfusion (hx.symm.trans hnf)
                · exact ih (prevIdx x) hp' hpx hw'
              · exact hne' hw'
          exact hstep (2 * p * t) j hj hne hw
        · rintro rfl; exact ⟨hi, walkBack_of_start s j hst _⟩
      ext b; simp [runCol, hfilt]
    ext v
    simp only [runColSet, hK, Finset.sdiff_empty, Set.mem_image, Finset.mem_coe, runStarts,
      Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    constructor
    · rintro ⟨i, hi, rfl⟩
      have hit : s i = true := (Eq.mp (Bool.and_eq_true _ _) hi).1
      rw [(hsing i hit).2]
      refine ⟨⟨i.val % (2 * p), Nat.mod_lt _ (by omega)⟩, ?_, rfl⟩
      simp only [s, cfg, pureCycleCfg] at hit
      have hmod2 : (i.val % (2 * p)) % 2 = i.val % 2 := by
        have hdiv := Nat.div_add_mod i.val (2 * p)
        have h2p : 2 * p * (i.val / (2 * p)) = 2 * (p * (i.val / (2 * p))) := by ring
        omega
      simpa [hmod2] using hit
    · rintro ⟨u, hu, rfl⟩
      let i : Fin (2 * p * t) := blockIdx ⟨0, ht⟩ u
      have hiv : i.val = u.val := by simp [i, blockIdx]
      have hit : s i = true := by simpa [s, cfg, pureCycleCfg, hiv] using hu
      have hsi := hsing i hit
      refine ⟨i, hsi.1, ?_⟩
      rw [hsi.2]
      dsimp only [col]
      congr 1; ext; simp only [hiv, Nat.mod_eq_of_lt u.isLt]
  exact ⟨hvalid, by simp [hdef], by simp [hK], hrcs⟩

lemma strictMono_orderIso_eq {s t : ℕ} (pos : Fin s → Fin t) (hmono : StrictMono pos)
    (M : Finset (Fin t)) (hM : M = Finset.univ.image pos) (hcard : M.card = s) :
    ∀ q : Fin s, (M.orderIsoOfFin hcard q).1 = pos q := by
  have heq_f : ∀ f : Fin s → Fin s, StrictMono f → ∀ q : Fin s, f q = q := by
    intro f hf
    have hge : ∀ k (hk : k < s), k ≤ (f ⟨k, hk⟩).val := by
      intro k
      induction k with
      | zero => intro _; exact Nat.zero_le _
      | succ k ih =>
        intro hk
        have hk' : k < s := Nat.lt_of_succ_lt hk
        have h1 := ih hk'
        have h2 : (f ⟨k, hk'⟩).val < (f ⟨k + 1, hk⟩).val := hf (Fin.mk_lt_mk.2 (Nat.lt_succ_self k))
        omega
    have hle : ∀ k (hk : k < s), (f ⟨k, hk⟩).val ≤ k := by
      intro k hk
      by_contra hgt
      have hback : ∀ d (hd : k + d < s), k + d + 1 ≤ (f ⟨k + d, hd⟩).val := by
        intro d
        induction d with
        | zero => intro hd; simp only [Nat.add_zero] at *; omega
        | succ d ih =>
          intro hd
          have hd' : k + d < s := by omega
          have h1 := ih hd'
          have h2 : (f ⟨k + d, hd'⟩).val < (f ⟨k + (d + 1), hd⟩).val :=
            hf (Fin.mk_lt_mk.2 (by omega))
          omega
      have hlast := hback (s - 1 - k) (by omega)
      have := (f ⟨k + (s - 1 - k), by omega⟩).isLt
      omega
    intro q
    exact Fin.ext (le_antisymm (hle q.val q.isLt) (hge q.val q.isLt))
  have hmem : ∀ q : Fin s, (M.orderIsoOfFin hcard q).1 ∈ Finset.univ.image pos := fun q =>
    hM ▸ (M.orderIsoOfFin hcard q).2
  let f : Fin s → Fin s := fun q => Classical.choose (Finset.mem_image.1 (hmem q))
  have hf_eq : ∀ q : Fin s, pos (f q) = (M.orderIsoOfFin hcard q).1 := fun q =>
    (Classical.choose_spec (Finset.mem_image.1 (hmem q))).2
  have hf_mono : StrictMono f := by
    intro q1 q2 hlt
    have h1 : pos (f q1) < pos (f q2) := by
      rw [hf_eq q1, hf_eq q2]
      exact (M.orderIsoOfFin hcard).strictMono hlt
    by_contra hge
    have : pos (f q2) ≤ pos (f q1) := hmono.monotone (le_of_not_gt hge)
    exact not_lt_of_ge this h1
  intro q
  rw [← hf_eq q, heq_f f hf_mono q]

lemma templateOf_buildFromPos {p h t : ℕ} (hp : 0 < p) (ht : 0 < t)
    (s' : Fin (2 * h)) (blocks : Fin (s'.val + 1) → Fin (2 * p) → Bool × Bool)
    (gmode : Fin (s'.val + 1) → Fin 3)
    (pos : Fin (s'.val + 1) → Fin t)
    (hv : validGapTuple gmode pos) (htv : templateBlocksValid hp blocks) :
    let cfg := buildFromPos hp (Nat.succ_pos s'.val) blocks pos hv.1
    ∃ hM : (Finset.univ.filter fun b : Fin t => isMarkedBlock cfg b = true).card ≤ 2 * h,
      templateOf hp ht cfg hM = Sum.inr ⟨s', (blocks, gmode)⟩ := by
  intro cfg
  let M := Finset.univ.filter fun b : Fin t => isMarkedBlock cfg b = true
  have hM_eq : M = Finset.univ.image pos := by
    ext b
    simp only [M, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hbm
      by_contra hnot
      push Not at hnot
      have := buildFromPos_unmarked_gap hp ht (Nat.succ_pos s'.val) blocks pos hv.1 b hnot
      exact Bool.noConfusion (hbm.symm.trans this)
    · rintro ⟨q, rfl⟩
      rw [buildFromPos_marked_at_pos hp ht (Nat.succ_pos s'.val) blocks pos hv.1 q]
      exact decide_eq_true (htv q)
  have hMcard : M.card = s'.val + 1 := by
    rw [hM_eq, Finset.card_image_of_injective _ hv.1.injective, Finset.card_univ, Fintype.card_fin]
  have hMle : M.card ≤ 2 * h := by rw [hMcard]; exact s'.isLt
  refine ⟨hMle, ?_⟩
  unfold templateOf
  dsimp only
  change (if h0 : M.card = 0 then Sum.inl (cfg ⟨0, by positivity⟩).1 else _) = _
  rw [dif_neg (by omega)]
  congr 1
  have hord : ∀ q : Fin M.card, (M.orderIsoOfFin rfl q).1 = pos ⟨q.val, by omega⟩ := by
    intro q
    exact strictMono_orderIso_eq (fun q' : Fin M.card => pos ⟨q'.val, by omega⟩)
      (fun _ _ hlt => hv.1 (Fin.mk_lt_mk.2 hlt)) M
      (by
        ext b
        simp only [hM_eq, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨fun ⟨q', hq'⟩ => ⟨⟨q'.val, by omega⟩, hq'⟩,
          fun ⟨q', hq'⟩ => ⟨⟨q'.val, by omega⟩, hq'⟩⟩) rfl q
  have haux : ∀ (m : ℕ) (hms : m = s'.val + 1) (hm : m ≤ 2 * h) (hm0 : m ≠ 0) (e : Fin m ≃o M)
      (he : ∀ q : Fin m, (e q).1 = pos ⟨q.val, by omega⟩),
      (⟨⟨m - 1, by omega⟩,
        (fun q : Fin (m - 1 + 1) => blockOf cfg (e ⟨q.val, by omega⟩).1,
         fun q : Fin (m - 1 + 1) =>
           if hlt : q.val + 1 < m then
             clamp3 ((e ⟨q.val + 1, hlt⟩).1.val - (e ⟨q.val, by omega⟩).1.val - 1)
           else
             clamp3 ((e ⟨0, Nat.pos_of_ne_zero hm0⟩).1.val + (t - 1 - (e ⟨q.val, by omega⟩).1.val)))⟩ :
        Σ s'' : Fin (2 * h), (Fin (s''.val + 1) → Fin (2 * p) → Bool × Bool) × (Fin (s''.val + 1) → Fin 3)) =
      ⟨s', (blocks, gmode)⟩ := by
    rintro m rfl hm hm0 e he
    refine Sigma.ext (Fin.ext rfl) (heq_of_eq (Prod.ext ?_ ?_))
    · funext q
      dsimp only
      rw [he ⟨q.val, q.isLt⟩]
      ext u
      · exact congrArg Prod.fst (buildFromPos_at_pos hp (Nat.succ_pos s'.val) blocks pos hv.1 q u)
      · exact congrArg Prod.snd (buildFromPos_at_pos hp (Nat.succ_pos s'.val) blocks pos hv.1 q u)
    · funext q
      dsimp only
      have hvq := hv.2 q
      split_ifs with hlt
      · rw [he ⟨q.val + 1, hlt⟩, he ⟨q.val, q.isLt⟩]
        rw [dif_pos hlt] at hvq
        exact hvq
      · rw [he ⟨0, Nat.pos_of_ne_zero hm0⟩, he ⟨q.val, q.isLt⟩]
        rw [dif_neg hlt] at hvq
        exact hvq
  exact haux M.card hMcard hMle (by omega) (M.orderIsoOfFin rfl) hord

lemma templateOf_eq_inr {p h t : ℕ} (hp : 0 < p) (ht : 0 < t)
    (cfg : Fin (2 * p * t) → Bool × Bool)
    (hM : (Finset.univ.filter fun b : Fin t => isMarkedBlock cfg b = true).card ≤ 2 * h)
    (s' : Fin (2 * h)) (blocks : Fin (s'.val + 1) → Fin (2 * p) → Bool × Bool)
    (gmode : Fin (s'.val + 1) → Fin 3)
    (htmpl : templateOf hp ht cfg hM = Sum.inr ⟨s', (blocks, gmode)⟩) :
    ∃ (pos : Fin (s'.val + 1) → Fin t) (hv : validGapTuple gmode pos),
      buildFromPos hp (Nat.succ_pos s'.val) blocks pos hv.1 = cfg ∧
      templateBlocksValid hp blocks := by
  let M := Finset.univ.filter fun b : Fin t => isMarkedBlock cfg b = true
  unfold templateOf at htmpl
  dsimp only at htmpl
  by_cases h0 : M.card = 0
  · change (if h0' : M.card = 0 then _ else _) = _ at htmpl
    rw [dif_pos h0] at htmpl
    cases htmpl
  · change (if h0' : M.card = 0 then _ else _) = _ at htmpl
    rw [dif_neg h0] at htmpl
    have hsig := Sum.inr.inj htmpl
    have hMcard : M.card = s'.val + 1 := by
      have h1 := congrArg (fun x => x.1.val) hsig
      change M.card - 1 = s'.val at h1
      omega
    have haux : ∀ (m : ℕ) (hms : m = s'.val + 1) (hm : m ≤ 2 * h) (hm0 : m ≠ 0)
        (e : Fin m ≃o M)
        (heq : (⟨⟨m - 1, by omega⟩,
          (fun q : Fin (m - 1 + 1) => blockOf cfg (e ⟨q.val, by omega⟩).1,
           fun q : Fin (m - 1 + 1) =>
             if hlt : q.val + 1 < m then
               clamp3 ((e ⟨q.val + 1, hlt⟩).1.val - (e ⟨q.val, by omega⟩).1.val - 1)
             else
               clamp3 ((e ⟨0, Nat.pos_of_ne_zero hm0⟩).1.val + (t - 1 - (e ⟨q.val, by omega⟩).1.val)))⟩ :
          Σ s'' : Fin (2 * h), (Fin (s''.val + 1) → Fin (2 * p) → Bool × Bool) × (Fin (s''.val + 1) → Fin 3)) =
          ⟨s', (blocks, gmode)⟩),
        (fun q : Fin (s'.val + 1) => blockOf cfg (e ⟨q.val, by omega⟩).1) = blocks ∧
        validGapTuple gmode (fun q : Fin (s'.val + 1) => (e ⟨q.val, by omega⟩).1) := by
      rintro m rfl hm hm0 e heq
      have hpair :
          (fun q : Fin (s'.val + 1) => blockOf cfg (e ⟨q.val, by omega⟩).1,
           fun q : Fin (s'.val + 1) =>
             if hlt : q.val + 1 < s'.val + 1 then
               clamp3 ((e ⟨q.val + 1, hlt⟩).1.val - (e ⟨q.val, by omega⟩).1.val - 1)
             else
               clamp3 ((e ⟨0, Nat.pos_of_ne_zero hm0⟩).1.val + (t - 1 - (e ⟨q.val, by omega⟩).1.val))) =
          (blocks, gmode) := eq_of_heq (Sigma.ext_iff.1 heq).2
      refine ⟨congrArg Prod.fst hpair, ?_, fun q => ?_⟩
      · intro q1 q2 hlt
        exact e.strictMono (Fin.mk_lt_mk.2 hlt)
      · have hq := congrFun (congrArg Prod.snd hpair) q
        dsimp only at hq ⊢
        split_ifs at hq ⊢ <;> exact hq
    obtain ⟨hblocks_eq, hval⟩ := haux M.card hMcard hM h0 (M.orderIsoOfFin rfl) hsig
    let pos' : Fin (s'.val + 1) → Fin t := fun q => (M.orderIsoOfFin rfl ⟨q.val, by omega⟩).1
    let pos : Fin (s'.val + 1) → Fin t := fun q => (M.orderIsoOfFin hMcard q).1
    have hpos_eq : pos' = pos := by
      funext q
      exact (strictMono_orderIso_eq pos' hval.1 M (by
        ext b
        simp only [Finset.mem_image, Finset.mem_univ, true_and, pos']
        constructor
        · intro hb
          let q0 := (M.orderIsoOfFin rfl).symm ⟨b, hb⟩
          exact ⟨⟨q0.val, by omega⟩, by simp [q0]⟩
        · rintro ⟨q', rfl⟩
          exact (M.orderIsoOfFin rfl ⟨q'.val, by omega⟩).2) hMcard q).symm
    have hblocks_eq' : (fun q : Fin (s'.val + 1) => blockOf cfg (pos q)) = blocks := by
      rwa [← hpos_eq]
    have hval' : validGapTuple gmode pos := by
      rwa [← hpos_eq]
    have hrec : buildFromPos hp (Nat.succ_pos s'.val) blocks pos hval'.1 = cfg := by
      rw [← hblocks_eq']
      exact buildFromPos_reconstruct hp ht (Nat.succ_pos s'.val) cfg hMcard
    have htv : templateBlocksValid hp blocks := by
      intro q
      have hmq : isMarkedBlock cfg (pos q) = true :=
        (Finset.mem_filter.1 (M.orderIsoOfFin hMcard q).2).2
      rw [← hrec, buildFromPos_marked_at_pos hp ht (Nat.succ_pos s'.val) blocks pos hval'.1 q] at hmq
      exact of_decide_eq_true hmq
    exact ⟨pos, hval', hrec, htv⟩

lemma main_theorem (p m h : ℕ) (hp : 0 < p)
    (H : Fin (2*p) → Fin m → ZMod 2) (mixedOnly : Bool) :
    let F := ZMod 2
    ∃ P : Fin (h+1) → Polynomial ℚ,
      (∀ j, (P j).natDegree ≤ 2*(h-j.val)) ∧
      (mixedOnly = true → P ⟨h, Nat.lt_succ_self h⟩ = 0) ∧
      ∀ t : ℕ, 10*(h+1) ≤ t →
        let n := 2*p*t
        let W := Fin n → F
        letI : Fintype (Submodule F W) := Fintype.ofFinite _
        let next := fun i : Fin n =>
          (⟨(i.val+1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩ : Fin n)
        let col := fun i : Fin n =>
          H ⟨i.val % (2*p), Nat.mod_lt _ (Nat.mul_pos (Nat.succ_pos 1) hp)⟩
        let good := fun U : Submodule F W =>
          Module.finrank F U = p*t-h ∧
          (∀ x ∈ U, ∀ b : Fin m, (∑ i, col i b * x i) = 0) ∧
          (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next i) = x (next i) * y i) ∧
          (mixedOnly = true → ∀ b : Fin 2, ∃ i : Fin n, i.val % 2 = b.val ∧ ∃ x ∈ U, x i ≠ 0)
        (((Finset.univ.filter good).card : ℕ) : ℚ) =
          ∑ j, (P j).eval (t : ℚ) * (2 : ℚ)^(p*j.val*t) := by
  let coeffOf : PEqualNP.Outside.L_lib_911.Template p h → Fin (h + 1) → Polynomial ℚ := fun T j =>
    match T with
    | Sum.inl b0 =>
      if mixedOnly = true then 0
      else
        let rk := Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
          ((fun u : Fin (2 * p) => H u) ''
            {u : Fin (2 * p) | (if b0 then decide (u.val % 2 = 0) else decide (u.val % 2 = 1)) = true}))
        if rk ≤ h then
          Polynomial.C ((PEqualNP.Outside.L_lib_911.qBinPoly rk (h - rk)).coeff j.val)
        else 0
    | Sum.inr ⟨s', (blocks, gmode)⟩ =>
      let s := s'.val + 1
      have hs : 0 < s := Nat.succ_pos _
      let pos0 := PEqualNP.Outside.L_lib_911.canonPos gmode
      let hv0 := PEqualNP.Outside.L_lib_911.canonPos_valid hs gmode
      let cfg0 := PEqualNP.Outside.L_lib_911.buildFromPos hp hs blocks pos0 hv0.1
      let s0 := fun i => (cfg0 i).1
      let K0 := Finset.univ.filter fun i => (cfg0 i).2 = true
      let col0 : Fin (2 * p * (s + ∑ q : Fin s, (gmode q).val)) → Fin m → ZMod 2 :=
        fun i => H ⟨i.val % (2 * p), Nat.mod_lt _ (by omega)⟩
      let J0 := (PEqualNP.Outside.L_lib_911.defectSet s0).card / 2
      let rk0 := Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
        (PEqualNP.Outside.L_lib_911.runColSet col0 s0 K0))
      if PEqualNP.Outside.L_lib_911.templateBlocksValid hp blocks ∧
          PEqualNP.Outside.L_lib_911.validPair h mixedOnly cfg0 ∧
          J0 + K0.card + rk0 ≤ h then
        Polynomial.C ((-1 : ℚ) ^ K0.card *
          (PEqualNP.Outside.L_lib_911.qBinPoly (J0 + K0.card + rk0) (h - (J0 + K0.card + rk0))).coeff j.val) *
          PEqualNP.Outside.L_lib_911.gapCountPoly hs gmode
      else 0
  let P : Fin (h + 1) → Polynomial ℚ := fun j => ∑ T : PEqualNP.Outside.L_lib_911.Template p h, coeffOf T j
  refine ⟨P, ?_, ?_, ?_⟩
  · intro j
    have hterm_deg : ∀ T : PEqualNP.Outside.L_lib_911.Template p h,
        (coeffOf T j).natDegree ≤ 2 * (h - j.val) := by
      intro T
      cases T with
      | inl b0 =>
        dsimp only [coeffOf]
        by_cases hmx : mixedOnly = true
        · rw [if_pos hmx]; simp
        · rw [if_neg hmx]
          by_cases hrk : Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
            ((fun u : Fin (2 * p) => H u) ''
              {u : Fin (2 * p) | (if b0 then decide (u.val % 2 = 0) else decide (u.val % 2 = 1)) = true})) ≤ h
          · rw [if_pos hrk]; simp [Polynomial.natDegree_C]
          · rw [if_neg hrk]; simp
      | inr Q =>
        rcases Q with ⟨s', blocks, gmode⟩
        dsimp only [coeffOf]
        split_ifs with hcond
        · obtain ⟨htv, hval0, hle⟩ := hcond
          let s := s'.val + 1
          have hs : 0 < s := Nat.succ_pos _
          let t0 := s + ∑ q : Fin s, (gmode q).val
          have ht0 : 0 < t0 := by omega
          let pos0 := PEqualNP.Outside.L_lib_911.canonPos gmode
          let hv0 := PEqualNP.Outside.L_lib_911.canonPos_valid hs gmode
          let cfg0 := PEqualNP.Outside.L_lib_911.buildFromPos hp hs blocks pos0 hv0.1
          let s0 := fun i => (cfg0 i).1
          let K0 := Finset.univ.filter fun i => (cfg0 i).2 = true
          let col0 : Fin (2 * p * t0) → Fin m → ZMod 2 :=
            fun i => H ⟨i.val % (2 * p), Nat.mod_lt _ (by omega)⟩
          let J0 := (PEqualNP.Outside.L_lib_911.defectSet s0).card / 2
          let rk0 := Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
            (PEqualNP.Outside.L_lib_911.runColSet col0 s0 K0))
          by_cases hjle : j.val ≤ h - (J0 + K0.card + rk0)
          · have hM0 : (Finset.univ.filter fun b : Fin t0 =>
                PEqualNP.Outside.L_lib_911.isMarkedBlock cfg0 b = true) = Finset.univ.image pos0 := by
              ext b
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
              constructor
              · intro hbm
                by_contra hnot
                push Not at hnot
                have := PEqualNP.Outside.L_lib_911.buildFromPos_unmarked_gap hp ht0 hs blocks pos0 hv0.1 b hnot
                exact Bool.noConfusion (hbm.symm.trans this)
              · rintro ⟨q, rfl⟩
                rw [PEqualNP.Outside.L_lib_911.buildFromPos_marked_at_pos hp ht0 hs blocks pos0 hv0.1 q]
                exact decide_eq_true (htv q)
            have hs_eq : s = (Finset.univ.filter fun b : Fin t0 =>
                PEqualNP.Outside.L_lib_911.isMarkedBlock cfg0 b = true).card := by
              rw [hM0, Finset.card_image_of_injective _ hv0.1.injective, Finset.card_univ, Fintype.card_fin]
            have hdef_even : 2 * (PEqualNP.Outside.L_lib_911.runStarts s0).card +
                (PEqualNP.Outside.L_lib_911.defectSet s0).card = 2 * p * t0 :=
              PEqualNP.Outside.L_lib_911.two_mul_starts_add_defects s0
            have h2pt0 : 2 * p * t0 = 2 * (p * t0) := by ring
            have hdef_eq : (PEqualNP.Outside.L_lib_911.defectSet s0).card = 2 * J0 := by
              dsimp only [J0]; omega
            have hs_le : s ≤ 2 * (h - j.val) := by
              have h1 := PEqualNP.Outside.L_lib_911.markedBlocks_card_le hp cfg0
              change (Finset.univ.filter fun b : Fin t0 =>
                PEqualNP.Outside.L_lib_911.isMarkedBlock cfg0 b = true).card ≤
                (PEqualNP.Outside.L_lib_911.defectSet s0).card + K0.card at h1
              rw [← hs_eq, hdef_eq] at h1
              omega
            calc (Polynomial.C ((-1 : ℚ) ^ K0.card *
                    (PEqualNP.Outside.L_lib_911.qBinPoly (J0 + K0.card + rk0) (h - (J0 + K0.card + rk0))).coeff j.val) *
                    PEqualNP.Outside.L_lib_911.gapCountPoly hs gmode).natDegree
                ≤ (Polynomial.C _).natDegree + (PEqualNP.Outside.L_lib_911.gapCountPoly hs gmode).natDegree :=
                  Polynomial.natDegree_mul_le
              _ ≤ 0 + s := by
                  rw [Polynomial.natDegree_C]
                  exact Nat.add_le_add_left (PEqualNP.Outside.L_lib_911.gapCountPoly_natDegree_le hs gmode) 0
              _ ≤ 2 * (h - j.val) := by omega
          · have hcz : (PEqualNP.Outside.L_lib_911.qBinPoly (J0 + K0.card + rk0)
                (h - (J0 + K0.card + rk0))).coeff j.val = 0 :=
              Polynomial.coeff_eq_zero_of_natDegree_lt
                (lt_of_le_of_lt (PEqualNP.Outside.L_lib_911.qBinPoly_natDegree_le _ _) (by omega))
            change (Polynomial.C ((-1 : ℚ) ^ K0.card *
              (PEqualNP.Outside.L_lib_911.qBinPoly (J0 + K0.card + rk0) (h - (J0 + K0.card + rk0))).coeff j.val) *
              PEqualNP.Outside.L_lib_911.gapCountPoly hs gmode).natDegree ≤ 2 * (h - j.val)
            simp [hcz]
        · simp
    have hsum_deg : ∀ (S : Finset (PEqualNP.Outside.L_lib_911.Template p h)),
        (∑ T ∈ S, coeffOf T j).natDegree ≤ 2 * (h - j.val) := by
      intro S
      induction S using Finset.induction_on with
      | empty => simp
      | @insert a S ha ih =>
        rw [Finset.sum_insert ha]
        exact (Polynomial.natDegree_add_le _ _).trans (max_le (hterm_deg a) ih)
    exact hsum_deg Finset.univ
  · intro hmix
    dsimp only [P]
    refine Finset.sum_eq_zero fun T _ => ?_
    cases T with
    | inl b0 =>
      simp [coeffOf, hmix]
    | inr Q =>
      rcases Q with ⟨s', blocks, gmode⟩
      dsimp only [coeffOf]
      split_ifs with hcond
      · obtain ⟨htv, _, hle⟩ := hcond
        let s := s'.val + 1
        have hs : 0 < s := Nat.succ_pos _
        let t0 := s + ∑ q : Fin s, (gmode q).val
        have ht0 : 0 < t0 := by omega
        let pos0 := PEqualNP.Outside.L_lib_911.canonPos gmode
        let hv0 := PEqualNP.Outside.L_lib_911.canonPos_valid hs gmode
        let cfg0 := PEqualNP.Outside.L_lib_911.buildFromPos hp hs blocks pos0 hv0.1
        let s0 := fun i => (cfg0 i).1
        let K0 := Finset.univ.filter fun i => (cfg0 i).2 = true
        let col0 : Fin (2 * p * t0) → Fin m → ZMod 2 :=
          fun i => H ⟨i.val % (2 * p), Nat.mod_lt _ (by omega)⟩
        let J0 := (PEqualNP.Outside.L_lib_911.defectSet s0).card / 2
        let rk0 := Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
          (PEqualNP.Outside.L_lib_911.runColSet col0 s0 K0))
        have hM0 : (Finset.univ.filter fun b : Fin t0 =>
            PEqualNP.Outside.L_lib_911.isMarkedBlock cfg0 b = true) = Finset.univ.image pos0 := by
          ext b
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
          constructor
          · intro hbm
            by_contra hnot
            push Not at hnot
            have := PEqualNP.Outside.L_lib_911.buildFromPos_unmarked_gap hp ht0 hs blocks pos0 hv0.1 b hnot
            exact Bool.noConfusion (hbm.symm.trans this)
          · rintro ⟨q, rfl⟩
            rw [PEqualNP.Outside.L_lib_911.buildFromPos_marked_at_pos hp ht0 hs blocks pos0 hv0.1 q]
            exact decide_eq_true (htv q)
        have hs_eq : s = (Finset.univ.filter fun b : Fin t0 =>
            PEqualNP.Outside.L_lib_911.isMarkedBlock cfg0 b = true).card := by
          rw [hM0, Finset.card_image_of_injective _ hv0.1.injective, Finset.card_univ, Fintype.card_fin]
        have hdef_even : 2 * (PEqualNP.Outside.L_lib_911.runStarts s0).card +
            (PEqualNP.Outside.L_lib_911.defectSet s0).card = 2 * p * t0 :=
          PEqualNP.Outside.L_lib_911.two_mul_starts_add_defects s0
        have h2pt0 : 2 * p * t0 = 2 * (p * t0) := by ring
        have hdef_eq : (PEqualNP.Outside.L_lib_911.defectSet s0).card = 2 * J0 := by
          dsimp only [J0]; omega
        have hpos_sum : 0 < J0 + K0.card + rk0 := by
          have h1 := PEqualNP.Outside.L_lib_911.markedBlocks_card_le hp cfg0
          change (Finset.univ.filter fun b : Fin t0 =>
            PEqualNP.Outside.L_lib_911.isMarkedBlock cfg0 b = true).card ≤
            (PEqualNP.Outside.L_lib_911.defectSet s0).card + K0.card at h1
          rw [← hs_eq, hdef_eq] at h1
          omega
        have hcz : (PEqualNP.Outside.L_lib_911.qBinPoly (J0 + K0.card + rk0)
            (h - (J0 + K0.card + rk0))).coeff h = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt
            (lt_of_le_of_lt (PEqualNP.Outside.L_lib_911.qBinPoly_natDegree_le _ _) (by omega))
        change Polynomial.C ((-1 : ℚ) ^ K0.card *
          (PEqualNP.Outside.L_lib_911.qBinPoly (J0 + K0.card + rk0) (h - (J0 + K0.card + rk0))).coeff h) *
          PEqualNP.Outside.L_lib_911.gapCountPoly hs gmode = 0
        simp [hcz]
      · rfl
  · intro t ht n W next col good
    letI : Fintype (Submodule (ZMod 2) W) := Fintype.ofFinite _
    have htpos : 0 < t := by omega
    have hgood_eq := PEqualNP.Outside.L_lib_911.good_card_eq_ie p m h t hp ht H mixedOnly
    dsimp only at hgood_eq
    have hfilt_eq : Finset.univ.filter good =
        Finset.univ.filter (fun U : Submodule (ZMod 2) W =>
          Module.finrank (ZMod 2) U = p * t - h ∧
          (∀ x ∈ U, ∀ b : Fin m, (∑ i, col i b * x i) = 0) ∧
          (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (PEqualNP.Outside.L_lib_911.nextIdx i) =
            x (PEqualNP.Outside.L_lib_911.nextIdx i) * y i) ∧
          (mixedOnly = true → ∀ b : Fin 2, ∃ i : Fin n, i.val % 2 = b.val ∧ ∃ x ∈ U, x i ≠ 0)) := by
      ext U
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rfl
    change (((Finset.univ.filter good).card : ℕ) : ℚ) = _
    rw [hfilt_eq, hgood_eq]
    let S := Finset.univ.filter (PEqualNP.Outside.L_lib_911.validPair (n := 2 * p * t) h mixedOnly)
    let tmpl : (Fin (2 * p * t) → Bool × Bool) → PEqualNP.Outside.L_lib_911.Template p h := fun cfg =>
      if hM : (Finset.univ.filter fun b : Fin t =>
          PEqualNP.Outside.L_lib_911.isMarkedBlock cfg b = true).card ≤ 2 * h
      then PEqualNP.Outside.L_lib_911.templateOf hp htpos cfg hM
      else Sum.inl false
    let wCfg : (Fin (2 * p * t) → Bool × Bool) → ℚ := fun cfg =>
      let s := fun i => (cfg i).1
      let K := Finset.univ.filter fun i : Fin (2 * p * t) => (cfg i).2 = true
      let J := (PEqualNP.Outside.L_lib_911.defectSet s).card / 2
      let rk := Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
        (PEqualNP.Outside.L_lib_911.runColSet col s K))
      (-1 : ℚ) ^ K.card *
        (if J + K.card + rk ≤ h then
          (PEqualNP.Outside.L_lib_911.qBinPoly (J + K.card + rk) (h - (J + K.card + rk))).eval
            ((2 : ℚ) ^ (p * t))
        else 0)
    have hpart : ∑ cfg ∈ S, wCfg cfg =
        ∑ T : PEqualNP.Outside.L_lib_911.Template p h,
          ∑ cfg ∈ S.filter (fun cfg => tmpl cfg = T), wCfg cfg := by
      exact (Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) wCfg).symm
    have hrhs_swap : ∑ j : Fin (h + 1), (P j).eval (t : ℚ) * (2 : ℚ) ^ (p * j.val * t) =
        ∑ T : PEqualNP.Outside.L_lib_911.Template p h,
          ∑ j : Fin (h + 1), (coeffOf T j).eval (t : ℚ) * (2 : ℚ) ^ (p * j.val * t) := by
      dsimp only [P]
      simp_rw [← Polynomial.coe_evalRingHom, map_sum, Polynomial.coe_evalRingHom, Finset.sum_mul]
      exact Finset.sum_comm
    change ∑ cfg ∈ S, wCfg cfg = _
    rw [hpart, hrhs_swap]
    refine Finset.sum_congr rfl fun T _ => ?_
    have hqbin_expand : ∀ a : ℕ, a ≤ h →
        (PEqualNP.Outside.L_lib_911.qBinPoly a (h - a)).eval ((2 : ℚ) ^ (p * t)) =
        ∑ j : Fin (h + 1), (PEqualNP.Outside.L_lib_911.qBinPoly a (h - a)).coeff j.val *
          (2 : ℚ) ^ (p * j.val * t) := by
      intro a ha
      have hdeg : (PEqualNP.Outside.L_lib_911.qBinPoly a (h - a)).natDegree < h + 1 :=
        lt_of_le_of_lt (PEqualNP.Outside.L_lib_911.qBinPoly_natDegree_le a (h - a)) (by omega)
      rw [Polynomial.eval_eq_sum_range' hdeg, ← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← pow_mul]
      congr 2; ring
    have hM_le_of_mem : ∀ cfg ∈ S,
        (Finset.univ.filter fun b : Fin t =>
          PEqualNP.Outside.L_lib_911.isMarkedBlock cfg b = true).card ≤ 2 * h := by
      intro cfg hcfg
      have hv := (Finset.mem_filter.1 hcfg).2
      have hdef_even := PEqualNP.Outside.L_lib_911.two_mul_starts_add_defects (fun i => (cfg i).1)
      have h2pt : 2 * p * t = 2 * (p * t) := by ring
      have h1 := PEqualNP.Outside.L_lib_911.markedBlocks_card_le hp cfg
      have h2 := hv.2.2.1
      dsimp only at h1 h2
      omega
    cases T with
    | inl b0 =>
      by_cases hmix : mixedOnly = true
      · have hempty : S.filter (fun cfg => tmpl cfg = Sum.inl b0) = ∅ := by
          ext cfg
          simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
          intro hcfg htmpl
          have hM := hM_le_of_mem cfg hcfg
          dsimp only [tmpl] at htmpl
          rw [dif_pos hM] at htmpl
          unfold PEqualNP.Outside.L_lib_911.templateOf at htmpl
          dsimp only at htmpl
          by_cases h0 : (Finset.univ.filter fun b : Fin t =>
              PEqualNP.Outside.L_lib_911.isMarkedBlock cfg b = true).card = 0
          · rw [dif_pos h0] at htmpl
            have hcfg_eq := PEqualNP.Outside.L_lib_911.eq_pureCycleCfg_of_no_marked hp htpos cfg h0
            have hinv := PEqualNP.Outside.L_lib_911.pureCycleCfg_invariants (h := h) hp htpos H mixedOnly
              (cfg ⟨0, by positivity⟩).1
            have hval := (Finset.mem_filter.1 hcfg).2
            rw [hcfg_eq] at hval
            have hmf := hinv.1.1 hval
            rw [hmix] at hmf
            exact Bool.noConfusion hmf
          · rw [dif_neg h0] at htmpl
            cases htmpl
        simp [hempty, coeffOf, hmix]
      · have hmf : mixedOnly = false := Bool.eq_false_iff.2 hmix
        have hsing : S.filter (fun cfg => tmpl cfg = Sum.inl b0) =
            {PEqualNP.Outside.L_lib_911.pureCycleCfg b0} := by
          ext cfg
          simp only [Finset.mem_filter, Finset.mem_singleton]
          constructor
          · rintro ⟨hcfg, htmpl⟩
            have hM := hM_le_of_mem cfg hcfg
            dsimp only [tmpl] at htmpl
            rw [dif_pos hM] at htmpl
            unfold PEqualNP.Outside.L_lib_911.templateOf at htmpl
            dsimp only at htmpl
            by_cases h0 : (Finset.univ.filter fun b : Fin t =>
                PEqualNP.Outside.L_lib_911.isMarkedBlock cfg b = true).card = 0
            · rw [dif_pos h0] at htmpl
              have hb0 : (cfg ⟨0, by positivity⟩).1 = b0 := Sum.inl.inj htmpl
              rw [← hb0]
              exact PEqualNP.Outside.L_lib_911.eq_pureCycleCfg_of_no_marked hp htpos cfg h0
            · rw [dif_neg h0] at htmpl
              cases htmpl
          · rintro rfl
            have hinv := PEqualNP.Outside.L_lib_911.pureCycleCfg_invariants (h := h) hp htpos H mixedOnly b0
            have hM0 : (Finset.univ.filter fun b : Fin t =>
                PEqualNP.Outside.L_lib_911.isMarkedBlock
                  (PEqualNP.Outside.L_lib_911.pureCycleCfg (p := p) (t := t) b0) b = true) = ∅ := by
              ext b; simp [PEqualNP.Outside.L_lib_911.pureCycleCfg_unmarked hp htpos b0 b]
            have hmemS : PEqualNP.Outside.L_lib_911.pureCycleCfg b0 ∈ S :=
              Finset.mem_filter.2 ⟨Finset.mem_univ _, hinv.1.2 hmf⟩
            refine ⟨hmemS, ?_⟩
            dsimp only [tmpl]
            rw [dif_pos (by simp [hM0])]
            unfold PEqualNP.Outside.L_lib_911.templateOf
            dsimp only
            rw [dif_pos (by simp [hM0])]
            congr 1
            cases b0 <;> simp [PEqualNP.Outside.L_lib_911.pureCycleCfg]
        rw [hsing, Finset.sum_singleton]
        have hinv := PEqualNP.Outside.L_lib_911.pureCycleCfg_invariants (h := h) hp htpos H mixedOnly b0
        dsimp only [wCfg, coeffOf]
        simp_rw [if_neg hmix]
        rw [hinv.2.1, hinv.2.2.1, hinv.2.2.2]
        simp only [Nat.zero_div, zero_add, pow_zero, one_mul]
        let rkP := Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
          ((fun u : Fin (2 * p) => H u) ''
            {u : Fin (2 * p) | (if b0 then decide (u.val % 2 = 0) else decide (u.val % 2 = 1)) = true}))
        by_cases hrk : rkP ≤ h
        · rw [if_pos hrk, hqbin_expand _ hrk]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [if_pos hrk, Polynomial.eval_C]
        · rw [if_neg hrk]
          refine (Finset.sum_eq_zero fun j _ => ?_).symm
          rw [if_neg hrk, Polynomial.eval_zero, zero_mul]
    | inr Q =>
      rcases Q with ⟨s', blocks, gmode⟩
      let s := s'.val + 1
      have hs : 0 < s := Nat.succ_pos _
      let t0 := s + ∑ q : Fin s, (gmode q).val
      have ht0 : 0 < t0 := by omega
      have ht0_lt : t0 < t := by
        have hle := PEqualNP.Outside.L_lib_911.templateMinT_le
          (Sum.inr ⟨s', (blocks, gmode)⟩ : PEqualNP.Outside.L_lib_911.Template p h)
        simp only [PEqualNP.Outside.L_lib_911.templateMinT] at hle
        dsimp only [t0, s]
        omega
      let pos0 := PEqualNP.Outside.L_lib_911.canonPos gmode
      let hv0 := PEqualNP.Outside.L_lib_911.canonPos_valid hs gmode
      let cfg0 := PEqualNP.Outside.L_lib_911.buildFromPos hp hs blocks pos0 hv0.1
      let s0 := fun i => (cfg0 i).1
      let K0 := Finset.univ.filter fun i => (cfg0 i).2 = true
      let col0 : Fin (2 * p * t0) → Fin m → ZMod 2 :=
        fun i => H ⟨i.val % (2 * p), Nat.mod_lt _ (by omega)⟩
      let J0 := (PEqualNP.Outside.L_lib_911.defectSet s0).card / 2
      let rk0 := Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
        (PEqualNP.Outside.L_lib_911.runColSet col0 s0 K0))
      by_cases hvalidT : PEqualNP.Outside.L_lib_911.templateBlocksValid hp blocks ∧
          PEqualNP.Outside.L_lib_911.validPair h mixedOnly cfg0
      · obtain ⟨htv, hval0⟩ := hvalidT
        have hfib_eq : ∀ cfg ∈ S.filter (fun cfg => tmpl cfg = Sum.inr ⟨s', (blocks, gmode)⟩),
            wCfg cfg = (-1 : ℚ) ^ K0.card *
              (if J0 + K0.card + rk0 ≤ h then
                (PEqualNP.Outside.L_lib_911.qBinPoly (J0 + K0.card + rk0) (h - (J0 + K0.card + rk0))).eval
                  ((2 : ℚ) ^ (p * t))
              else 0) := by
          intro cfg hcfg
          have hcfgS := (Finset.mem_filter.1 hcfg).1
          have htmpl := (Finset.mem_filter.1 hcfg).2
          have hM := hM_le_of_mem cfg hcfgS
          dsimp only [tmpl] at htmpl
          rw [dif_pos hM] at htmpl
          obtain ⟨pos, hpos_valid, hrec, _⟩ :=
            PEqualNP.Outside.L_lib_911.templateOf_eq_inr hp htpos cfg hM s' blocks gmode htmpl
          have hinv := PEqualNP.Outside.L_lib_911.buildFromPos_invariants (h := h) hp htpos ht0 hs
            H mixedOnly blocks gmode pos pos0 hpos_valid hv0 htv
          rw [← hrec]
          dsimp only [wCfg]
          rw [hinv.2.1, hinv.2.2.1, hinv.2.2.2]
        have hfib_card : (S.filter (fun cfg => tmpl cfg = Sum.inr ⟨s', (blocks, gmode)⟩)).card =
            (Finset.univ.filter fun pos : Fin s → Fin t =>
              PEqualNP.Outside.L_lib_911.validGapTuple gmode pos).card := by
          symm
          refine Finset.card_bij
            (fun pos hpos => PEqualNP.Outside.L_lib_911.buildFromPos hp hs blocks pos (Finset.mem_filter.1 hpos).2.1)
            ?_ ?_ ?_
          · intro pos hpos
            have hv := (Finset.mem_filter.1 hpos).2
            let cfg := PEqualNP.Outside.L_lib_911.buildFromPos hp hs blocks pos hv.1
            have hinv := PEqualNP.Outside.L_lib_911.buildFromPos_invariants (h := h) hp htpos ht0 hs
              H mixedOnly blocks gmode pos pos0 hv hv0 htv
            have hcfgS : cfg ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hinv.1.2 hval0⟩
            refine Finset.mem_filter.2 ⟨hcfgS, ?_⟩
            obtain ⟨hMle, htmpl_eq⟩ := PEqualNP.Outside.L_lib_911.templateOf_buildFromPos hp htpos
              s' blocks gmode pos hv htv
            dsimp only [tmpl]
            rw [dif_pos hMle]
            exact htmpl_eq
          · intro pos1 hpos1 pos2 hpos2 heq
            have hv1 := (Finset.mem_filter.1 hpos1).2
            have hv2 := (Finset.mem_filter.1 hpos2).2
            have hM1 : (Finset.univ.filter fun b : Fin t =>
                PEqualNP.Outside.L_lib_911.isMarkedBlock
                  (PEqualNP.Outside.L_lib_911.buildFromPos hp hs blocks pos1 hv1.1) b = true) =
                Finset.univ.image pos1 := by
              ext b
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
              constructor
              · intro hbm; by_contra hnot; push Not at hnot
                exact Bool.noConfusion (hbm.symm.trans
                  (PEqualNP.Outside.L_lib_911.buildFromPos_unmarked_gap hp htpos hs blocks pos1 hv1.1 b hnot))
              · rintro ⟨q, rfl⟩
                rw [PEqualNP.Outside.L_lib_911.buildFromPos_marked_at_pos hp htpos hs blocks pos1 hv1.1 q]
                exact decide_eq_true (htv q)
            have hM2 : (Finset.univ.filter fun b : Fin t =>
                PEqualNP.Outside.L_lib_911.isMarkedBlock
                  (PEqualNP.Outside.L_lib_911.buildFromPos hp hs blocks pos2 hv2.1) b = true) =
                Finset.univ.image pos2 := by
              ext b
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
              constructor
              · intro hbm; by_contra hnot; push Not at hnot
                exact Bool.noConfusion (hbm.symm.trans
                  (PEqualNP.Outside.L_lib_911.buildFromPos_unmarked_gap hp htpos hs blocks pos2 hv2.1 b hnot))
              · rintro ⟨q, rfl⟩
                rw [PEqualNP.Outside.L_lib_911.buildFromPos_marked_at_pos hp htpos hs blocks pos2 hv2.1 q]
                exact decide_eq_true (htv q)
            have himg : Finset.univ.image pos1 = Finset.univ.image pos2 := by
              rw [← hM1, ← hM2, heq]
            have hc1 : (Finset.univ.image pos1).card = s := by
              rw [Finset.card_image_of_injective _ hv1.1.injective, Finset.card_univ, Fintype.card_fin]
            funext q
            rw [← PEqualNP.Outside.L_lib_911.strictMono_orderIso_eq pos1 hv1.1 _ rfl hc1 q,
              ← PEqualNP.Outside.L_lib_911.strictMono_orderIso_eq pos2 hv2.1 _ himg hc1 q]
          · intro cfg hcfg
            have hcfgS := (Finset.mem_filter.1 hcfg).1
            have htmpl := (Finset.mem_filter.1 hcfg).2
            have hM := hM_le_of_mem cfg hcfgS
            dsimp only [tmpl] at htmpl
            rw [dif_pos hM] at htmpl
            obtain ⟨pos, hpos_valid, hrec, _⟩ :=
              PEqualNP.Outside.L_lib_911.templateOf_eq_inr hp htpos cfg hM s' blocks gmode htmpl
            exact ⟨pos, Finset.mem_filter.2 ⟨Finset.mem_univ _, hpos_valid⟩, hrec⟩
        rw [Finset.sum_congr rfl hfib_eq, Finset.sum_const, nsmul_eq_mul, hfib_card,
          PEqualNP.Outside.L_lib_911.validGapTuple_card hs gmode ht0_lt]
        by_cases hle : J0 + K0.card + rk0 ≤ h
        · rw [if_pos hle, hqbin_expand _ hle, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          have hc : coeffOf (Sum.inr ⟨s', (blocks, gmode)⟩) j =
              Polynomial.C ((-1 : ℚ) ^ K0.card *
                (PEqualNP.Outside.L_lib_911.qBinPoly (J0 + K0.card + rk0) (h - (J0 + K0.card + rk0))).coeff j.val) *
                PEqualNP.Outside.L_lib_911.gapCountPoly hs gmode := by
            dsimp only [coeffOf]
            exact if_pos ⟨htv, hval0, hle⟩
          rw [hc, Polynomial.eval_mul, Polynomial.eval_C]
          ring
        · rw [if_neg hle, mul_zero, mul_zero]
          refine (Finset.sum_eq_zero fun j _ => ?_).symm
          dsimp only [coeffOf]
          rw [if_neg (fun hc => hle hc.2.2)]
          simp
      · have hempty : S.filter (fun cfg => tmpl cfg = Sum.inr ⟨s', (blocks, gmode)⟩) = ∅ := by
          ext cfg
          simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
          intro hcfgS htmpl
          have hM := hM_le_of_mem cfg hcfgS
          dsimp only [tmpl] at htmpl
          rw [dif_pos hM] at htmpl
          obtain ⟨pos, hpos_valid, hrec, htv⟩ :=
            PEqualNP.Outside.L_lib_911.templateOf_eq_inr hp htpos cfg hM s' blocks gmode htmpl
          have hinv := PEqualNP.Outside.L_lib_911.buildFromPos_invariants (h := h) hp htpos ht0 hs
            H mixedOnly blocks gmode pos pos0 hpos_valid hv0 htv
          have hval0 : PEqualNP.Outside.L_lib_911.validPair h mixedOnly cfg0 :=
            hinv.1.1 (by rw [hrec]; exact (Finset.mem_filter.1 hcfgS).2)
          exact hvalidT ⟨htv, hval0⟩
        rw [hempty, Finset.sum_empty]
        refine (Finset.sum_eq_zero fun j _ => ?_).symm
        dsimp only [coeffOf]
        rw [if_neg (fun hc => hvalidT ⟨hc.1, hc.2.1⟩)]
        simp

end

end PEqualNP.Outside.L_lib_911

theorem PEqualNP.Outside.L_lib_911 : (∀ (p m h : ℕ) (hp : 0 < p)
  (H : Fin (2*p) → Fin m → ZMod 2) (mixedOnly : Bool),
  letI : ∀ q : Prop, Decidable q := Classical.propDecidable
  let F := ZMod 2
  ∃ P : Fin (h+1) → Polynomial ℚ,
    (∀ j, (P j).natDegree ≤ 2*(h-j.val)) ∧
    (mixedOnly = true → P ⟨h, Nat.lt_succ_self h⟩ = 0) ∧
    ∀ t : ℕ, 10*(h+1) ≤ t →
      let n := 2*p*t
      let W := Fin n → F
      letI : Fintype (Submodule F W) := Fintype.ofFinite _
      let next := fun i : Fin n =>
        (⟨(i.val+1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩ : Fin n)
      let col := fun i : Fin n =>
        H ⟨i.val % (2*p), Nat.mod_lt _ (Nat.mul_pos (Nat.succ_pos 1) hp)⟩
      let good := fun U : Submodule F W =>
        Module.finrank F U = p*t-h ∧
        (∀ x ∈ U, ∀ b : Fin m, (∑ i, col i b * x i) = 0) ∧
        (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next i) = x (next i) * y i) ∧
        (mixedOnly = true → ∀ b : Fin 2, ∃ i : Fin n, i.val % 2 = b.val ∧ ∃ x ∈ U, x i ≠ 0)
      (((Finset.univ.filter good).card : ℕ) : ℚ) =
        ∑ j, (P j).eval (t : ℚ) * (2 : ℚ)^(p*j.val*t)) := by
  intro p m h hp H mixedOnly
  obtain ⟨P, hdeg, hmix, heval⟩ := PEqualNP.Outside.L_lib_911.main_theorem p m h hp H mixedOnly
  refine ⟨P, hdeg, hmix, fun t ht => ?_⟩
  dsimp only
  have h1 := heval t ht
  dsimp only at h1
  rw [← h1]
  congr 2
  ext U
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
