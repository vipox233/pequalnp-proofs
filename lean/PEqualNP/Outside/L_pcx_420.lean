import PEqualNP.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.FieldTheory.Finiteness
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace PEqualNP.Outside.L_pcx_420_aux

abbrev F := ZMod 2
abbrev X (r : ℕ) := Fin r → Fin 3 → F
abbrev Y (r : ℕ) := Fin r → F

def fTarget {r : ℕ} (x : X r) (i : Fin r) : F := x i 2 + x i 0 * x i 1

def symp {r : ℕ} (j : Fin r) (u v : X r) : F := u j 0 * v j 1 + u j 1 * v j 0

def rad {r : ℕ} (S : Submodule F (X r)) : Submodule F S :=
  { carrier := {u : S | ∀ v : S, ∀ j : Fin r, symp j u.1 v.1 = 0}
  , zero_mem' := by
      intro v j
      simp [symp]
  , add_mem' := by
      intro a b ha hb v j
      have h1 := ha v j
      have h2 := hb v j
      change (a.1 j 0 + b.1 j 0) * v.1 j 1 + (a.1 j 1 + b.1 j 1) * v.1 j 0 = 0
      have h3 : (a.1 j 0 + b.1 j 0) * v.1 j 1 + (a.1 j 1 + b.1 j 1) * v.1 j 0 =
          symp j a.1 v.1 + symp j b.1 v.1 := by
        simp only [symp]
        ring
      rw [h3, h1, h2, add_zero]
  , smul_mem' := by
      intro c a ha v j
      have h1 := ha v j
      change (c * a.1 j 0) * v.1 j 1 + (c * a.1 j 1) * v.1 j 0 = 0
      have h3 : (c * a.1 j 0) * v.1 j 1 + (c * a.1 j 1) * v.1 j 0 = c * symp j a.1 v.1 := by
        simp only [symp]
        ring
      rw [h3, h1, mul_zero] }

def lam {r : ℕ} (S : Submodule F (X r)) (p : F × F) (i : Fin r) : rad S →ₗ[F] F where
  toFun d := d.1.1 i 2 + d.1.1 i 0 * d.1.1 i 1 + p.1 * d.1.1 i 1 + p.2 * d.1.1 i 0
  map_add' d₁ d₂ := by
    have hsym : symp i d₁.1.1 d₂.1.1 = 0 := d₁.2 d₂.1 i
    have hEq : (d₁.1.1 i 2 + d₂.1.1 i 2) +
        (d₁.1.1 i 0 + d₂.1.1 i 0) * (d₁.1.1 i 1 + d₂.1.1 i 1) +
        p.1 * (d₁.1.1 i 1 + d₂.1.1 i 1) + p.2 * (d₁.1.1 i 0 + d₂.1.1 i 0) =
        (d₁.1.1 i 2 + d₁.1.1 i 0 * d₁.1.1 i 1 + p.1 * d₁.1.1 i 1 + p.2 * d₁.1.1 i 0) +
        (d₂.1.1 i 2 + d₂.1.1 i 0 * d₂.1.1 i 1 + p.1 * d₂.1.1 i 1 + p.2 * d₂.1.1 i 0) +
        symp i d₁.1.1 d₂.1.1 := by
      simp only [symp]
      ring
    change (d₁.1.1 i 2 + d₂.1.1 i 2) +
        (d₁.1.1 i 0 + d₂.1.1 i 0) * (d₁.1.1 i 1 + d₂.1.1 i 1) +
        p.1 * (d₁.1.1 i 1 + d₂.1.1 i 1) + p.2 * (d₁.1.1 i 0 + d₂.1.1 i 0) = _
    rw [hEq, hsym, add_zero]
  map_smul' c d := by
    have hcc : c * c = c := by fin_cases c <;> rfl
    change (c * d.1.1 i 2) + (c * d.1.1 i 0) * (c * d.1.1 i 1) +
        p.1 * (c * d.1.1 i 1) + p.2 * (c * d.1.1 i 0) =
        c * (d.1.1 i 2 + d.1.1 i 0 * d.1.1 i 1 + p.1 * d.1.1 i 1 + p.2 * d.1.1 i 0)
    calc (c * d.1.1 i 2) + (c * d.1.1 i 0) * (c * d.1.1 i 1) +
          p.1 * (c * d.1.1 i 1) + p.2 * (c * d.1.1 i 0)
        = (c * d.1.1 i 2) + (c * c) * (d.1.1 i 0 * d.1.1 i 1) +
          p.1 * (c * d.1.1 i 1) + p.2 * (c * d.1.1 i 0) := by ring
      _ = c * (d.1.1 i 2 + d.1.1 i 0 * d.1.1 i 1 + p.1 * d.1.1 i 1 + p.2 * d.1.1 i 0) := by
          rw [hcc]
          ring

lemma fTarget_shift {r : ℕ} (a w u : X r) (i : Fin r) :
    fTarget (a + (w + u)) i = fTarget (a + w) i +
      (u i 2 + u i 0 * u i 1 + a i 0 * u i 1 + a i 1 * u i 0) + symp i u w := by
  simp only [fTarget, symp, Pi.add_apply]
  ring

def pSub {r : ℕ} (S : Submodule F (X r)) (a : X r) : Submodule F (rad S) :=
  ⨅ i : Fin r, LinearMap.ker (lam S (a i 0, a i 1) i)

def pInS {r : ℕ} (S : Submodule F (X r)) (a : X r) : Submodule F S :=
  (pSub S a).map (rad S).subtype

lemma mem_pSub {r : ℕ} (S : Submodule F (X r)) (a : X r) (d : rad S) :
    d ∈ pSub S a ↔ ∀ i : Fin r, lam S (a i 0, a i 1) i d = 0 := by
  simp only [pSub, Submodule.mem_iInf, LinearMap.mem_ker]

lemma exists_ask_iff {r : ℕ} (S : Submodule F (X r)) (a : X r) (e : ℕ) :
    (∃ (ask : X r →ₗ[F] (Fin e → F)) (out : (Fin e → F) → Y r),
      ∀ u ∈ S, out (ask (a + u)) = fTarget (a + u)) ↔
    Module.finrank F S ≤ e + Module.finrank F (pSub S a) := by
  classical
  constructor
  · rintro ⟨ask, out, hout⟩
    let askS : S →ₗ[F] (Fin e → F) := ask.comp S.subtype
    have hrk := LinearMap.finrank_range_add_finrank_ker askS
    have hrg : Module.finrank F (LinearMap.range askS) ≤ e := by
      calc Module.finrank F (LinearMap.range askS) ≤ Module.finrank F (Fin e → F) :=
            Submodule.finrank_le _
        _ = e := Module.finrank_fin_fun F
    have hker : LinearMap.ker askS ≤ pInS S a := by
      intro u hu
      have hu0 : ask u.1 = 0 := hu
      have hshift : ∀ w : S, fTarget (a + (w.1 + u.1)) = fTarget (a + w.1) := by
        intro w
        have h1 := hout (w.1 + u.1) (S.add_mem w.2 u.2)
        have h2 := hout w.1 w.2
        have h3 : ask (a + (w.1 + u.1)) = ask (a + w.1) := by
          rw [← add_assoc, map_add, hu0, add_zero]
        rw [← h1, h3, h2]
      have hlin : ∀ i : Fin r,
          u.1 i 2 + u.1 i 0 * u.1 i 1 + a i 0 * u.1 i 1 + a i 1 * u.1 i 0 = 0 := by
        intro i
        have h0 := congrFun (hshift 0) i
        simp only [Submodule.coe_zero] at h0
        have hsh := fTarget_shift a 0 u.1 i
        have hsym0 : symp i u.1 0 = 0 := by simp [symp]
        rw [hsym0, add_zero] at hsh
        rw [hsh] at h0
        exact add_left_cancel (h0.trans (add_zero _).symm)
      have hurad : u ∈ rad S := by
        intro w i
        have hw := congrFun (hshift w) i
        have hsh := fTarget_shift a w.1 u.1 i
        rw [hlin i, add_zero] at hsh
        rw [hsh] at hw
        exact add_left_cancel (hw.trans (add_zero _).symm)
      refine ⟨⟨u, hurad⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_pSub]
      intro i
      exact hlin i
    have hkle : Module.finrank F (LinearMap.ker askS) ≤ Module.finrank F (pSub S a) := by
      calc Module.finrank F (LinearMap.ker askS) ≤ Module.finrank F (pInS S a) :=
            Submodule.finrank_mono hker
        _ = Module.finrank F (pSub S a) := Submodule.finrank_map_subtype_eq (rad S) (pSub S a)
    omega
  · intro hle
    let Q := S ⧸ pInS S a
    have hq_eq : Module.finrank F Q + Module.finrank F (pSub S a) = Module.finrank F S := by
      rw [← Submodule.finrank_map_subtype_eq (rad S) (pSub S a)]
      exact Submodule.finrank_quotient_add_finrank (pInS S a)
    set q := Module.finrank F Q
    have hqe : q ≤ e := by omega
    let iso : Q ≃ₗ[F] (Fin q → F) :=
      LinearEquiv.ofFinrankEq Q (Fin q → F) (by rw [Module.finrank_fin_fun])
    let pad : (Fin q → F) →ₗ[F] (Fin e → F) :=
      { toFun := fun v k => if hk : k.1 < q then v ⟨k.1, hk⟩ else 0
        map_add' := fun v w => by
          funext k
          by_cases hk : k.1 < q <;> simp [hk]
        map_smul' := fun c v => by
          funext k
          by_cases hk : k.1 < q <;> simp [hk] }
    have hpad_inj : Function.Injective pad := by
      intro v w hvw
      funext j
      have h := congrFun hvw ⟨j.1, lt_of_lt_of_le j.2 hqe⟩
      simp only [pad, LinearMap.coe_mk, AddHom.coe_mk, j.2, dite_true] at h
      exact h
    let askS : S →ₗ[F] (Fin e → F) := pad.comp (iso.toLinearMap.comp (pInS S a).mkQ)
    obtain ⟨ask, hask⟩ := LinearMap.exists_extend askS
    have hcoset : ∀ u₁ ∈ S, ∀ u₂ ∈ S, ask (a + u₁) = ask (a + u₂) →
        fTarget (a + u₁) = fTarget (a + u₂) := by
      intro u₁ hu₁ u₂ hu₂ heq
      have hu_eq : ask u₁ = ask u₂ := by simpa [map_add] using heq
      have hsub0 : ask (u₁ - u₂) = 0 := by rw [map_sub, hu_eq, sub_self]
      have hmk0 : askS ⟨u₁ - u₂, S.sub_mem hu₁ hu₂⟩ = 0 := by
        have := congrArg (fun g => g ⟨u₁ - u₂, S.sub_mem hu₁ hu₂⟩) hask
        simpa [LinearMap.comp_apply, Submodule.subtype_apply, hsub0] using this.symm
      have hq0 : (pInS S a).mkQ ⟨u₁ - u₂, S.sub_mem hu₁ hu₂⟩ = 0 := by
        apply iso.injective
        apply hpad_inj
        rw [map_zero, map_zero]
        exact hmk0
      have hmem : (⟨u₁ - u₂, S.sub_mem hu₁ hu₂⟩ : S) ∈ pInS S a :=
        (Submodule.Quotient.mk_eq_zero (pInS S a)).mp hq0
      obtain ⟨d, hd, hdeq⟩ := hmem
      have hdval : d.1.1 = u₁ - u₂ := congrArg Subtype.val hdeq
      funext i
      have hu1eq : u₁ = u₂ + d.1.1 := by rw [hdval, add_sub_cancel]
      rw [hu1eq, fTarget_shift a u₂ d.1.1 i]
      have hlam0 : lam S (a i 0, a i 1) i d = 0 := (mem_pSub S a d).mp hd i
      have hsym0 : symp i d.1.1 u₂ = 0 := d.2 ⟨u₂, hu₂⟩ i
      change fTarget (a + u₂) i + lam S (a i 0, a i 1) i d + symp i d.1.1 u₂ = fTarget (a + u₂) i
      rw [hlam0, hsym0, add_zero, add_zero]
    let out : (Fin e → F) → Y r := fun y =>
      if h : ∃ u ∈ S, ask (a + u) = y then fTarget (a + Classical.choose h) else 0
    refine ⟨ask, out, fun u hu => ?_⟩
    have hex : ∃ w ∈ S, ask (a + w) = ask (a + u) := ⟨u, hu, rfl⟩
    simp only [out, hex, dite_true]
    exact hcoset _ (Classical.choose_spec hex).1 u hu (Classical.choose_spec hex).2

def annKer {K : Type*} [Field K] {V : Type*} [AddCommMonoid V] [Module K V]
    (W : Submodule K (V →ₗ[K] K)) : Submodule K V :=
  { carrier := {d : V | ∀ φ ∈ W, φ d = 0}
  , zero_mem' := fun φ _ => map_zero φ
  , add_mem' := fun ha hb φ hφ => by rw [map_add, ha φ hφ, hb φ hφ, add_zero]
  , smul_mem' := fun c a ha φ hφ => by rw [map_smul, ha φ hφ, smul_zero] }

lemma finrank_annKer {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    [Module.Finite K V] [Module.Finite K (V →ₗ[K] K)]
    (W : Submodule K (V →ₗ[K] K)) :
    Module.finrank K W + Module.finrank K (annKer W) = Module.finrank K V := by
  classical
  have : Module.Free K ↥W := Module.Free.of_divisionRing K ↥W
  set m := Module.finrank K W
  obtain ⟨b⟩ : Nonempty (Module.Basis (Fin m) K W) := ⟨Module.finBasis K W⟩
  let ev : V →ₗ[K] (Fin m → K) :=
    { toFun := fun d t => (b t).1 d
      map_add' := fun d₁ d₂ => funext fun t => map_add (b t).1 d₁ d₂
      map_smul' := fun c d => funext fun t => map_smul (b t).1 c d }
  have hker : LinearMap.ker ev = annKer W := by
    ext d
    simp only [LinearMap.mem_ker, annKer, Submodule.mem_mk, AddSubmonoid.mem_mk,
      AddSubsemigroup.mem_mk, Set.mem_ofPred_eq]
    constructor
    · intro hd φ hφ
      have hrepr : (⟨φ, hφ⟩ : W) = ∑ t : Fin m, (b.repr ⟨φ, hφ⟩ t) • b t :=
        (b.sum_repr ⟨φ, hφ⟩).symm
      have hval : φ = ∑ t : Fin m, (b.repr ⟨φ, hφ⟩ t) • (b t).1 := by
        simpa only [Submodule.coe_sum, SetLike.val_smul] using congrArg Subtype.val hrepr
      rw [hval, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun t _ => ?_
      have hdt : (b t).1 d = 0 := congrFun hd t
      simp [LinearMap.smul_apply, hdt]
    · intro hd
      funext t
      exact hd (b t).1 (b t).2
  have hrg_le : Module.finrank K (LinearMap.range ev) ≤ m := by
    calc Module.finrank K (LinearMap.range ev) ≤ Module.finrank K (Fin m → K) :=
          Submodule.finrank_le _
      _ = m := Module.finrank_fin_fun K
  have hrg_eq : Module.finrank K (LinearMap.range ev) = m := by
    by_contra hne
    have hlt : Module.finrank K (LinearMap.range ev) < m := lt_of_le_of_ne hrg_le hne
    set k := Module.finrank K (LinearMap.range ev)
    have : Module.Free K ↥(LinearMap.range ev) :=
      Module.Free.of_divisionRing K ↥(LinearMap.range ev)
    obtain ⟨bR⟩ : Nonempty (Module.Basis (Fin k) K (LinearMap.range ev)) :=
      ⟨Module.finBasis K (LinearMap.range ev)⟩
    let mat : (Fin m → K) →ₗ[K] (Fin k → K) :=
      { toFun := fun c j => ∑ t : Fin m, c t * (bR j).1 t
        map_add' := fun c₁ c₂ => by
          funext j
          simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
        map_smul' := fun s c => by
          funext j
          simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, ← Finset.mul_sum] }
    have hmrk := LinearMap.finrank_range_add_finrank_ker mat
    have hmrg : Module.finrank K (LinearMap.range mat) ≤ k := by
      calc Module.finrank K (LinearMap.range mat) ≤ Module.finrank K (Fin k → K) :=
            Submodule.finrank_le _
        _ = k := Module.finrank_fin_fun K
    have hmk_pos : 0 < Module.finrank K (LinearMap.ker mat) := by
      rw [Module.finrank_fin_fun] at hmrk
      omega
    have hker_ne : LinearMap.ker mat ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hmk_pos
      omega
    obtain ⟨c, hc_mem, hc_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker_ne
    have hsum0 : (∑ t : Fin m, c t • b t : W) = 0 := by
      apply Subtype.ext
      ext d
      have hcomb : (⟨ev d, LinearMap.mem_range_self ev d⟩ : LinearMap.range ev) =
          ∑ j : Fin k, (bR.repr ⟨ev d, LinearMap.mem_range_self ev d⟩ j) • bR j :=
        (bR.sum_repr _).symm
      have hevd : ∀ t : Fin m, (b t).1 d =
          ∑ j : Fin k, (bR.repr ⟨ev d, LinearMap.mem_range_self ev d⟩ j) * (bR j).1 t := by
        intro t
        have h1 := congrArg (fun z : LinearMap.range ev => z.1 t) hcomb
        simp only [Submodule.coe_sum, SetLike.val_smul, Finset.sum_apply, Pi.smul_apply,
          smul_eq_mul] at h1
        exact h1
      have hsub_val : ((∑ t : Fin m, c t • b t : W).1) d = ∑ t : Fin m, c t * (b t).1 d := by
        simp [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [hsub_val]
      simp_rw [hevd, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun j _ => ?_
      have hcj : ∑ t : Fin m, c t * (bR j).1 t = 0 := congrFun hc_mem j
      calc ∑ t : Fin m, c t * (bR.repr ⟨ev d, LinearMap.mem_range_self ev d⟩ j * (bR j).1 t)
          = bR.repr ⟨ev d, LinearMap.mem_range_self ev d⟩ j *
              ∑ t : Fin m, c t * (bR j).1 t := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun t _ => ?_
            ring
        _ = 0 := by rw [hcj, mul_zero]
    have hc0 : ∀ t : Fin m, c t = 0 := by
      intro t
      have hrep := congrArg (fun w : W => b.repr w t) hsum0
      rw [b.repr_sum_self, map_zero] at hrep
      simpa using hrep
    exact hc_ne (funext hc0)
  have hevrk := LinearMap.finrank_range_add_finrank_ker ev
  rw [hrg_eq, hker] at hevrk
  exact hevrk

def wRow {r : ℕ} (S : Submodule F (X r)) (a : X r) : Submodule F (rad S →ₗ[F] F) :=
  Submodule.span F (Set.range fun i : Fin r => lam S (a i 0, a i 1) i)

lemma annKer_wRow {r : ℕ} (S : Submodule F (X r)) (a : X r) :
    annKer (wRow S a) = pSub S a := by
  ext d
  rw [mem_pSub]
  simp only [annKer, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_ofPred_eq]
  constructor
  · intro hd i
    exact hd _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro hd φ hφ
    refine Submodule.span_induction (p := fun g _ => g d = 0) ?_ ?_ ?_ ?_ hφ
    · rintro _ ⟨i, rfl⟩
      exact hd i
    · simp
    · intro g₁ g₂ _ _ hg₁ hg₂
      simp [hg₁, hg₂]
    · intro c g _ hg
      simp [hg]

def uSpan {r : ℕ} {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W] [DecidableEq W]
    (A : Fin r → Finset W) (J : Finset (Fin r)) : Submodule K W :=
  Submodule.span K (↑(J.biUnion A) : Set W)

noncomputable def rkSpan {r : ℕ} {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W]
    [DecidableEq W] (A : Fin r → Finset W) (J : Finset (Fin r)) : ℕ :=
  Module.finrank K (uSpan (K := K) A J)

noncomputable def radoVal {r : ℕ} {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W]
    [DecidableEq W] (A : Fin r → Finset W) (J : Finset (Fin r)) : ℕ :=
  (r - J.card) + rkSpan (K := K) A J

noncomputable def aSet {r : ℕ} (S : Submodule F (X r)) (i : Fin r) : Finset (rad S →ₗ[F] F) := by
  classical
  exact (Finset.univ : Finset (F × F)).image (fun p => lam S p i)

def rSub {r : ℕ} (S : Submodule F (X r)) (J : Finset (Fin r)) : Submodule F (rad S) :=
  { carrier := {d : rad S | ∀ j ∈ J, d.1.1 j = 0}
  , zero_mem' := fun j _ => rfl
  , add_mem' := fun ha hb j hj => by simp [ha j hj, hb j hj]
  , smul_mem' := fun c a ha j hj => by simp [ha j hj] }

lemma annKer_uSpan_aSet {r : ℕ} (S : Submodule F (X r)) (J : Finset (Fin r))
    [DecidableEq (rad S →ₗ[F] F)] :
    annKer (uSpan (K := F) (aSet S) J) = rSub S J := by
  classical
  ext d
  simp only [annKer, rSub, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_ofPred_eq]
  constructor
  · intro hd j hj
    have hlam : ∀ p : F × F, lam S p j d = 0 := by
      intro p
      apply hd
      apply Submodule.subset_span
      simp only [Finset.mem_coe, Finset.mem_biUnion, aSet, Finset.mem_image, Finset.mem_univ,
        true_and]
      exact ⟨j, hj, p, rfl⟩
    have h00 := hlam (0, 0)
    have h10 := hlam (1, 0)
    have h01 := hlam (0, 1)
    simp only [lam, LinearMap.coe_mk, AddHom.coe_mk, zero_mul, one_mul, add_zero] at h00 h10 h01
    rw [h00, zero_add] at h10
    rw [h00, zero_add] at h01
    rw [h01, zero_mul, add_zero] at h00
    funext c
    fin_cases c
    · exact h01
    · exact h10
    · exact h00
  · intro hd φ hφ
    refine Submodule.span_induction (p := fun g _ => g d = 0) ?_ ?_ ?_ ?_ hφ
    · intro g hg
      simp only [Finset.mem_coe, Finset.mem_biUnion, aSet, Finset.mem_image, Finset.mem_univ,
        true_and] at hg
      obtain ⟨j, hj, p, rfl⟩ := hg
      have hdj := hd j hj
      have h0 : d.1.1 j 0 = 0 := congrFun hdj 0
      have h1 : d.1.1 j 1 = 0 := congrFun hdj 1
      have h2 : d.1.1 j 2 = 0 := congrFun hdj 2
      simp [lam, h0, h1, h2]
    · simp
    · intro g₁ g₂ _ _ hg₁ hg₂
      simp [hg₁, hg₂]
    · intro c g _ hg
      simp [hg]

lemma natCard_eq_two_pow_finrank {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V] :
    Nat.card V = 2 ^ Module.finrank F V := by
  rw [Module.natCard_eq_pow_finrank (K := F) (V := V)]
  have h2 : Nat.card F = 2 := by
    rw [Nat.card_eq_fintype_card, ZMod.card]
  rw [h2]

def rSubX {r : ℕ} (S : Submodule F (X r)) (J : Finset (Fin r)) : Submodule F (X r) :=
  { carrier := {u : X r | u ∈ S ∧ (∀ j ∈ J, u j = 0) ∧ ∀ v : S, ∀ j : Fin r, symp j u v.1 = 0}
  , zero_mem' := ⟨S.zero_mem, fun _ _ => rfl, fun _ _ => by simp [symp]⟩
  , add_mem' := fun {a b} ha hb =>
      ⟨S.add_mem ha.1 hb.1, fun j hj => by simp [ha.2.1 j hj, hb.2.1 j hj], fun v j => by
        have h1 := ha.2.2 v j
        have h2 := hb.2.2 v j
        have h3 : symp j (a + b) v.1 = symp j a v.1 + symp j b v.1 := by
          simp only [symp, Pi.add_apply]
          ring
        rw [h3, h1, h2, add_zero]⟩
  , smul_mem' := fun c a ha =>
      ⟨S.smul_mem c ha.1, fun j hj => by simp [ha.2.1 j hj], fun v j => by
        have h1 := ha.2.2 v j
        have h3 : symp j (c • a) v.1 = c * symp j a v.1 := by
          simp only [symp, Pi.smul_apply, smul_eq_mul]
          ring
        rw [h3, h1, mul_zero]⟩ }

lemma natCard_rSub {r : ℕ} (S : Submodule F (X r)) (J : Finset (Fin r)) :
    Nat.card {u : S // (∀ j ∈ J, u.val j = 0) ∧
      ∀ v : S, ∀ j : Fin r, u.val j 0 * v.val j 1 + u.val j 1 * v.val j 0 = 0} =
    2 ^ Module.finrank F (rSub S J) := by
  let eqv1 : {u : S // (∀ j ∈ J, u.val j = 0) ∧
      ∀ v : S, ∀ j : Fin r, u.val j 0 * v.val j 1 + u.val j 1 * v.val j 0 = 0} ≃
      ↥(rSubX S J) :=
    { toFun := fun x => ⟨x.1.1, x.1.2, x.2.1, x.2.2⟩
      invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2.1, y.2.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let eqvL : ↥(rSubX S J) ≃ₗ[F] ↥(rSub S J) :=
    { toFun := fun y => ⟨⟨⟨y.1, y.2.1⟩, y.2.2.2⟩, y.2.2.1⟩
      invFun := fun z => ⟨z.1.1.1, z.1.1.2, z.2, z.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  rw [Nat.card_congr eqv1, natCard_eq_two_pow_finrank, eqvL.finrank_eq]

lemma transversal_le_rado {r : ℕ} {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W]
    [Module.Finite K W] [DecidableEq W]
    (A : Fin r → Finset W) (φ : Fin r → W) (hφ : ∀ i, φ i ∈ A i) (J : Finset (Fin r)) :
    Module.finrank K (Submodule.span K (Set.range φ)) ≤ radoVal (K := K) A J := by
  let T : Finset W := (Finset.univ \ J).image φ
  have hsub : Set.range φ ⊆ (↑(J.biUnion A) : Set W) ∪ (↑T : Set W) := by
    rintro _ ⟨i, rfl⟩
    by_cases hi : i ∈ J
    · left
      exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨i, hi, hφ i⟩)
    · right
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr
        ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩, rfl⟩)
  have hle_sup : Submodule.span K (Set.range φ) ≤
      uSpan (K := K) A J ⊔ Submodule.span K (↑T : Set W) := by
    rw [uSpan, ← Submodule.span_union]
    exact Submodule.span_mono hsub
  have hfin1 : Module.finrank K (Submodule.span K (Set.range φ)) ≤
      Module.finrank K (uSpan (K := K) A J ⊔ Submodule.span K (↑T : Set W) : Submodule K W) :=
    Submodule.finrank_mono hle_sup
  have hsup_eq := Submodule.finrank_sup_add_finrank_inf_eq (uSpan (K := K) A J)
    (Submodule.span K (↑T : Set W))
  have hT_rk : Module.finrank K (Submodule.span K (↑T : Set W)) ≤ T.card := by
    simpa using finrank_span_le_card (R := K) (↑T : Set W)
  have hT_card : T.card ≤ r - J.card := by
    calc T.card ≤ (Finset.univ \ J).card := Finset.card_image_le
      _ = (Finset.univ : Finset (Fin r)).card - (J ∩ Finset.univ).card := Finset.card_sdiff
      _ = r - J.card := by simp
  simp only [radoVal, rkSpan]
  omega

lemma exists_transversal_ge_min {r : ℕ} {K : Type*} [Field K] {W : Type*} [AddCommGroup W]
    [Module K W] [Module.Finite K W] [DecidableEq W]
    (M : ℕ) :
    ∀ n : ℕ, ∀ A : Fin r → Finset W,
      (∀ i, (A i).Nonempty) →
      (∑ i : Fin r, ((A i).card - 1)) = n →
      (∀ J : Finset (Fin r), M ≤ radoVal (K := K) A J) →
      ∃ φ : Fin r → W, (∀ i, φ i ∈ A i) ∧
        M ≤ Module.finrank K (Submodule.span K (Set.range φ)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro A hne hfuel hM
    by_cases hcard : ∀ i : Fin r, (A i).card ≤ 1
    · let φ : Fin r → W := fun i => Classical.choose (hne i)
      have hφ : ∀ i, φ i ∈ A i := fun i => Classical.choose_spec (hne i)
      have hAi : ∀ i, A i = {φ i} := by
        intro i
        rw [Finset.eq_singleton_iff_unique_mem]
        refine ⟨hφ i, fun z hz => Finset.card_le_one.mp (hcard i) z hz (φ i) (hφ i)⟩
      have hset : (↑((Finset.univ : Finset (Fin r)).biUnion A) : Set W) = Set.range φ := by
        ext w
        simp only [Finset.mem_coe, Finset.mem_biUnion, Finset.mem_univ, true_and, hAi,
          Finset.mem_singleton, Set.mem_range]
        constructor
        · rintro ⟨i, rfl⟩; exact ⟨i, rfl⟩
        · rintro ⟨i, rfl⟩; exact ⟨i, rfl⟩
      have hMu := hM Finset.univ
      unfold radoVal rkSpan uSpan at hMu
      rw [hset, Finset.card_univ, Fintype.card_fin, Nat.sub_self, zero_add] at hMu
      exact ⟨φ, hφ, hMu⟩
    · push Not at hcard
      obtain ⟨i₀, hi₀⟩ := hcard
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hi₀
      let A₁ : Fin r → Finset W := Function.update A i₀ ((A i₀).erase x)
      let A₂ : Fin r → Finset W := Function.update A i₀ ((A i₀).erase y)
      have hne₁ : ∀ i, (A₁ i).Nonempty := by
        intro i
        by_cases hi : i = i₀
        · subst hi
          exact ⟨y, by simp [A₁, hy, hxy.symm]⟩
        · simp [A₁, hi, hne i]
      have hne₂ : ∀ i, (A₂ i).Nonempty := by
        intro i
        by_cases hi : i = i₀
        · subst hi
          exact ⟨x, by simp [A₂, hx, hxy]⟩
        · simp [A₂, hi, hne i]
      have hsub₁ : ∀ i, A₁ i ⊆ A i := by
        intro i
        by_cases hi : i = i₀
        · subst hi
          simp [A₁, Finset.erase_subset]
        · simp [A₁, hi]
      have hsub₂ : ∀ i, A₂ i ⊆ A i := by
        intro i
        by_cases hi : i = i₀
        · subst hi
          simp [A₂, Finset.erase_subset]
        · simp [A₂, hi]
      have hfuel₁ : (∑ i : Fin r, ((A₁ i).card - 1)) < n := by
        rw [← hfuel, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀),
          ← Finset.add_sum_erase _ (fun i => (A i).card - 1) (Finset.mem_univ i₀)]
        have hrest : ∑ i ∈ Finset.univ.erase i₀, ((A₁ i).card - 1) =
            ∑ i ∈ Finset.univ.erase i₀, ((A i).card - 1) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          have hne_i : i ≠ i₀ := (Finset.mem_erase.mp hi).1
          simp [A₁, hne_i]
        rw [hrest]
        have hc1 : (A₁ i₀).card = (A i₀).card - 1 := by
          simp [A₁, Finset.card_erase_of_mem hx]
        omega
      have hfuel₂ : (∑ i : Fin r, ((A₂ i).card - 1)) < n := by
        rw [← hfuel, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀),
          ← Finset.add_sum_erase _ (fun i => (A i).card - 1) (Finset.mem_univ i₀)]
        have hrest : ∑ i ∈ Finset.univ.erase i₀, ((A₂ i).card - 1) =
            ∑ i ∈ Finset.univ.erase i₀, ((A i).card - 1) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          have hne_i : i ≠ i₀ := (Finset.mem_erase.mp hi).1
          simp [A₂, hne_i]
        rw [hrest]
        have hc2 : (A₂ i₀).card = (A i₀).card - 1 := by
          simp [A₂, Finset.card_erase_of_mem hy]
        omega
      by_cases hM₁ : ∀ J : Finset (Fin r), M ≤ radoVal (K := K) A₁ J
      · obtain ⟨φ, hφ, hφM⟩ := ih _ hfuel₁ A₁ hne₁ rfl hM₁
        exact ⟨φ, fun i => hsub₁ i (hφ i), hφM⟩
      · by_cases hM₂ : ∀ J : Finset (Fin r), M ≤ radoVal (K := K) A₂ J
        · obtain ⟨φ, hφ, hφM⟩ := ih _ hfuel₂ A₂ hne₂ rfl hM₂
          exact ⟨φ, fun i => hsub₂ i (hφ i), hφM⟩
        · exfalso
          push Not at hM₁ hM₂
          obtain ⟨J₁, hJ₁⟩ := hM₁
          obtain ⟨J₂, hJ₂⟩ := hM₂
          have hi₀₁ : i₀ ∈ J₁ := by
            by_contra hnot
            have hbi : J₁.biUnion A₁ = J₁.biUnion A := by
              refine Finset.biUnion_congr rfl fun j hj => ?_
              have hne_j : j ≠ i₀ := fun h => hnot (h ▸ hj)
              simp [A₁, hne_j]
            have heq : radoVal (K := K) A₁ J₁ = radoVal (K := K) A J₁ := by
              unfold radoVal rkSpan uSpan
              rw [hbi]
            have := hM J₁
            omega
          have hi₀₂ : i₀ ∈ J₂ := by
            by_contra hnot
            have hbi : J₂.biUnion A₂ = J₂.biUnion A := by
              refine Finset.biUnion_congr rfl fun j hj => ?_
              have hne_j : j ≠ i₀ := fun h => hnot (h ▸ hj)
              simp [A₂, hne_j]
            have heq : radoVal (K := K) A₂ J₂ = radoVal (K := K) A J₂ := by
              unfold radoVal rkSpan uSpan
              rw [hbi]
            have := hM J₂
            omega
          let U₁ := uSpan (K := K) A₁ J₁
          let U₂ := uSpan (K := K) A₂ J₂
          have hsup : uSpan (K := K) A (J₁ ∪ J₂) ≤ U₁ ⊔ U₂ := by
            rw [uSpan, Submodule.span_le]
            intro w hw
            obtain ⟨j, hj, hwj⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hw)
            by_cases hj0 : j = i₀
            · subst hj0
              by_cases hwx : w = x
              · subst hwx
                have hmem2 : w ∈ J₂.biUnion A₂ :=
                  Finset.mem_biUnion.mpr ⟨j, hi₀₂, by simp [A₂, hx, hxy]⟩
                exact Submodule.mem_sup_right (Submodule.subset_span (Finset.mem_coe.mpr hmem2))
              · have hmem1 : w ∈ J₁.biUnion A₁ :=
                  Finset.mem_biUnion.mpr ⟨j, hi₀₁, by simp [A₁, hwj, hwx]⟩
                exact Submodule.mem_sup_left (Submodule.subset_span (Finset.mem_coe.mpr hmem1))
            · rcases Finset.mem_union.mp hj with hj₁ | hj₂
              · have hmem1 : w ∈ J₁.biUnion A₁ :=
                  Finset.mem_biUnion.mpr ⟨j, hj₁, by simp [A₁, hj0, hwj]⟩
                exact Submodule.mem_sup_left (Submodule.subset_span (Finset.mem_coe.mpr hmem1))
              · have hmem2 : w ∈ J₂.biUnion A₂ :=
                  Finset.mem_biUnion.mpr ⟨j, hj₂, by simp [A₂, hj0, hwj]⟩
                exact Submodule.mem_sup_right (Submodule.subset_span (Finset.mem_coe.mpr hmem2))
          have hinf : uSpan (K := K) A ((J₁ ∩ J₂).erase i₀) ≤ U₁ ⊓ U₂ := by
            rw [uSpan, Submodule.span_le]
            intro w hw
            obtain ⟨j, hj, hwj⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hw)
            obtain ⟨hj0, hj12⟩ := Finset.mem_erase.mp hj
            obtain ⟨hj1, hj2⟩ := Finset.mem_inter.mp hj12
            refine ⟨?_, ?_⟩
            · exact Submodule.subset_span (Finset.mem_coe.mpr
                (Finset.mem_biUnion.mpr ⟨j, hj1, by simp [A₁, hj0, hwj]⟩))
            · exact Submodule.subset_span (Finset.mem_coe.mpr
                (Finset.mem_biUnion.mpr ⟨j, hj2, by simp [A₂, hj0, hwj]⟩))
          have hrk_sup : rkSpan (K := K) A (J₁ ∪ J₂) ≤
              Module.finrank K (U₁ ⊔ U₂ : Submodule K W) :=
            Submodule.finrank_mono hsup
          have hrk_inf : rkSpan (K := K) A ((J₁ ∩ J₂).erase i₀) ≤
              Module.finrank K (U₁ ⊓ U₂ : Submodule K W) :=
            Submodule.finrank_mono hinf
          have hmod := Submodule.finrank_sup_add_finrank_inf_eq U₁ U₂
          have hcard_ui := Finset.card_union_add_card_inter J₁ J₂
          have hcard_er := Finset.card_erase_add_one (Finset.mem_inter.mpr ⟨hi₀₁, hi₀₂⟩)
          have hJ₁_le : J₁.card ≤ r := by simpa using J₁.card_le_univ
          have hJ₂_le : J₂.card ≤ r := by simpa using J₂.card_le_univ
          have hJu_le : (J₁ ∪ J₂).card ≤ r := by simpa using (J₁ ∪ J₂).card_le_univ
          have hJi_le : ((J₁ ∩ J₂).erase i₀).card ≤ r := by
            simpa using ((J₁ ∩ J₂).erase i₀).card_le_univ
          have hMu := hM (J₁ ∪ J₂)
          have hMi := hM ((J₁ ∩ J₂).erase i₀)
          simp only [radoVal] at hJ₁ hJ₂ hMu hMi
          change Module.finrank K (U₁ ⊔ U₂ : Submodule K W) +
            Module.finrank K (U₁ ⊓ U₂ : Submodule K W) =
            rkSpan (K := K) A₁ J₁ + rkSpan (K := K) A₂ J₂ at hmod
          omega

theorem main (r : ℕ) (S : Submodule F (X r)) (e : ℕ) :
    (∀ a : X r, ∃ (ask : X r →ₗ[F] (Fin e → F)) (out : (Fin e → F) → Y r),
      ∀ u ∈ S, out (ask (a + u)) = fTarget (a + u)) ↔
    ∃ J : Finset (Fin r),
      2 ^ (r - J.card) * Nat.card S ≤ 2 ^ e * Nat.card
        {u : S // (∀ j ∈ J, u.val j = 0) ∧
          ∀ v : S, ∀ j : Fin r,
            u.val j 0 * v.val j 1 + u.val j 1 * v.val j 0 = 0} := by
  classical
  have : Finite (rad S →ₗ[F] F) :=
    Finite.of_injective (fun g : rad S →ₗ[F] F => (g : rad S → F)) DFunLike.coe_injective
  have : Module.Finite F (rad S →ₗ[F] F) := Module.Finite.of_finite
  have hrad_le : Module.finrank F (rad S) ≤ Module.finrank F S := Submodule.finrank_le (rad S)
  have hrow_iff : ∀ a : X r,
      (∃ (ask : X r →ₗ[F] (Fin e → F)) (out : (Fin e → F) → Y r),
        ∀ u ∈ S, out (ask (a + u)) = fTarget (a + u)) ↔
      (Module.finrank F S - Module.finrank F (rad S)) + Module.finrank F (wRow S a) ≤ e := by
    intro a
    rw [exists_ask_iff]
    have hnn := finrank_annKer (K := F) (V := rad S) (wRow S a)
    rw [annKer_wRow] at hnn
    omega
  have hcert_iff : ∀ J : Finset (Fin r),
      (2 ^ (r - J.card) * Nat.card S ≤ 2 ^ e * Nat.card
        {u : S // (∀ j ∈ J, u.val j = 0) ∧
          ∀ v : S, ∀ j : Fin r,
            u.val j 0 * v.val j 1 + u.val j 1 * v.val j 0 = 0}) ↔
      (Module.finrank F S - Module.finrank F (rad S)) + radoVal (K := F) (aSet S) J ≤ e := by
    intro J
    rw [natCard_eq_two_pow_finrank (V := S), natCard_rSub S J, ← pow_add, ← pow_add,
      Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)]
    have hnn := finrank_annKer (K := F) (V := rad S) (uSpan (K := F) (aSet S) J)
    rw [annKer_uSpan_aSet] at hnn
    simp only [radoVal, rkSpan]
    omega
  constructor
  · intro hfin
    have h0 : (Module.finrank F S - Module.finrank F (rad S)) + Module.finrank F (wRow S 0) ≤ e :=
      (hrow_iff 0).mp (hfin 0)
    set kBud := e - (Module.finrank F S - Module.finrank F (rad S))
    have hexJ : ∃ J : Finset (Fin r), radoVal (K := F) (aSet S) J ≤ kBud := by
      by_contra hno
      push Not at hno
      have hne : ∀ i : Fin r, (aSet S i).Nonempty := by
        intro i
        refine ⟨lam S (0, 0) i, ?_⟩
        simp only [aSet, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨(0, 0), rfl⟩
      obtain ⟨φ, hφ, hφrk⟩ :=
        exists_transversal_ge_min (K := F) (kBud + 1) _ (aSet S) hne rfl (fun J => hno J)
      have hp_ex : ∀ i : Fin r, ∃ p : F × F, lam S p i = φ i := by
        intro i
        have hi := hφ i
        simp only [aSet, Finset.mem_image, Finset.mem_univ, true_and] at hi
        exact hi
      let pSel : Fin r → F × F := fun i => Classical.choose (hp_ex i)
      have hpSel : ∀ i : Fin r, lam S (pSel i) i = φ i := fun i => Classical.choose_spec (hp_ex i)
      let a : X r := fun i c => if c = 0 then (pSel i).1 else if c = 1 then (pSel i).2 else 0
      have ha_eq : ∀ i : Fin r, (a i 0, a i 1) = pSel i := by
        intro i
        ext <;> simp [a]
      have hw_eq : wRow S a = Submodule.span F (Set.range φ) := by
        simp only [wRow]
        congr 1
        ext g
        simp only [Set.mem_range, ha_eq, hpSel]
      have hfa := (hrow_iff a).mp (hfin a)
      rw [hw_eq] at hfa
      omega
    obtain ⟨J, hJ⟩ := hexJ
    exact ⟨J, (hcert_iff J).mpr (by omega)⟩
  · rintro ⟨J, hJ⟩ a
    have hJ' := (hcert_iff J).mp hJ
    rw [hrow_iff a]
    let φ : Fin r → (rad S →ₗ[F] F) := fun i => lam S (a i 0, a i 1) i
    have hφ : ∀ i, φ i ∈ aSet S i := by
      intro i
      simp only [aSet, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨(a i 0, a i 1), rfl⟩
    have hle := transversal_le_rado (K := F) (aSet S) φ hφ J
    change Module.finrank F (wRow S a) ≤ radoVal (K := F) (aSet S) J at hle
    omega

end PEqualNP.Outside.L_pcx_420_aux

theorem PEqualNP.Outside.L_pcx_420 : (∀ r : ℕ,
  let F := ZMod 2
  let X := Fin r → Fin 3 → F
  let Y := Fin r → F
  let f := fun (x : X) (i : Fin r) => x i 2 + x i 0 * x i 1
  let finish := fun (S : Submodule F X) (e : ℕ) =>
    ∀ a : X, ∃ (ask : X →ₗ[F] (Fin e → F)) (out : (Fin e → F) → Y),
      ∀ u ∈ S, out (ask (a+u)) = f (a+u)
  ∀ (S : Submodule F X) (e : ℕ),
    finish S e ↔ ∃ J : Finset (Fin r),
      2^(r-J.card) * Nat.card S ≤ 2^e * Nat.card
        {u : S // (∀ j ∈ J, u.val j = 0) ∧
          ∀ v : S, ∀ j : Fin r,
            u.val j 0 * v.val j 1 + u.val j 1 * v.val j 0 = 0}) := by
  exact fun r S e => PEqualNP.Outside.L_pcx_420_aux.main r S e
