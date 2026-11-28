import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.FieldTheory.Finite.Basic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1041

section Part3

open Module Submodule Matrix Finset

lemma dotProduct_mulVec_comm {k m : ℕ} (M : Matrix (Fin k) (Fin m) (ZMod 2))
    (x : Fin m → ZMod 2) (y : Fin k → ZMod 2) :
    dotProduct (M.mulVec x) y = dotProduct x (Mᵀ.mulVec y) := by
  rw [dotProduct_mulVec, vecMul_transpose]

theorem part3_abstract (k n b : ℕ)
    (A G : Matrix (Fin k) (Fin k) (ZMod 2))
    (P : Matrix (Fin k) (Fin n) (ZMod 2))
    (hAGA : A * G * A = A)
    (hA_sym : Aᵀ = A)
    (hArk : A.rank = 2 * b) :
    let W := Fin k → ZMod 2
    let T := (Finset.univ : Finset W).filter (fun c => Pᵀ.mulVec c = 0 ∧ A.mulVec (G.mulVec c) = c)
    let R := T.filter (fun c => ∀ z ∈ T, dotProduct (G.mulVec c) z = 0)
    2 ^ (Pᵀ * A * P).rank * T.card * R.card = 2 ^ (2 * b) := by
  classical
  intro W T R
  let F := ZMod 2
  let U : Submodule F W := LinearMap.range A.mulVecLin
  have hmemU : ∀ c : W, c ∈ U ↔ A.mulVec (G.mulVec c) = c := by
    intro c
    constructor
    · rintro ⟨x, rfl⟩
      change A *ᵥ G *ᵥ A *ᵥ x = A *ᵥ x
      rw [Matrix.mulVec_mulVec (A *ᵥ x) A G, Matrix.mulVec_mulVec x (A * G) A, hAGA]
    · intro h
      exact ⟨G.mulVec c, h⟩
  have hU_dim : finrank F U = 2 * b := by
    rw [← hArk, Matrix.rank]
  let Tsub : Submodule F W := LinearMap.ker Pᵀ.mulVecLin ⊓ U
  have hT_mem : ∀ c : W, c ∈ T ↔ c ∈ Tsub := by
    intro c
    simp only [T, Tsub, Finset.mem_filter, Finset.mem_univ, true_and, Submodule.mem_inf,
      LinearMap.mem_ker, hmemU]
    rfl
  let phi : U →ₗ[F] (Fin n → F) := Pᵀ.mulVecLin.comp U.subtype
  have hker_phi : finrank F (LinearMap.ker phi) = finrank F Tsub := by
    have hmap : (LinearMap.ker phi).map U.subtype = Tsub := by
      ext c
      simp only [Submodule.mem_map, LinearMap.mem_ker, Submodule.coe_subtype, Tsub, Submodule.mem_inf]
      constructor
      · rintro ⟨⟨c, hcU⟩, hker, rfl⟩; exact ⟨hker, hcU⟩
      · rintro ⟨hker, hcU⟩; exact ⟨⟨c, hcU⟩, hker, rfl⟩
    rw [← hmap, Submodule.finrank_map_subtype_eq]
  have hrng_phi : LinearMap.range phi = LinearMap.range (Pᵀ * A).mulVecLin := by
    ext y
    simp only [phi, U, LinearMap.mem_range, LinearMap.coe_comp, Function.comp_apply,
      Submodule.coe_subtype, Subtype.exists]
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, (Matrix.mulVec_mulVec x Pᵀ A).symm⟩
    · rintro ⟨x, rfl⟩
      refine ⟨A.mulVec x, ⟨x, rfl⟩, ?_⟩
      change Pᵀ *ᵥ A *ᵥ x = (Pᵀ * A) *ᵥ x
      exact Matrix.mulVec_mulVec x Pᵀ A
  have hphi_dim := LinearMap.finrank_range_add_finrank_ker phi
  rw [hrng_phi, hker_phi] at hphi_dim
  have hrk_PA : finrank F (LinearMap.range (Pᵀ * A).mulVecLin) = (A * P).rank := by
    have htr : (Pᵀ * A)ᵀ = A * P := by rw [Matrix.transpose_mul, Matrix.transpose_transpose, hA_sym]
    rw [← Matrix.rank, ← Matrix.rank_transpose, htr]
  rw [hrk_PA, hU_dim] at hphi_dim
  let APsub : Submodule F W := LinearMap.range (A * P).mulVecLin
  have hAP_le_U : APsub ≤ U := by
    rintro c ⟨v, rfl⟩
    exact ⟨P.mulVec v, Matrix.mulVec_mulVec v A P⟩
  have hAP_dim : finrank F APsub = (A * P).rank := rfl
  let pairing : U →ₗ[F] Module.Dual F Tsub :=
    { toFun := fun c =>
        { toFun := fun z => dotProduct (G.mulVec c.1) z.1
          map_add' := fun z1 z2 => by
            change dotProduct (G.mulVec c.1) (z1.1 + z2.1) = _
            rw [dotProduct_add]
          map_smul' := fun r z => by
            change dotProduct (G.mulVec c.1) (r • z.1) = r * dotProduct (G.mulVec c.1) z.1
            rw [dotProduct_smul, smul_eq_mul] }
      map_add' := fun c1 c2 => by
        ext z
        change dotProduct (G.mulVec (c1.1 + c2.1)) z.1 = _
        rw [Matrix.mulVec_add, add_dotProduct]
        rfl
      map_smul' := fun r c => by
        ext z
        change dotProduct (G.mulVec (r • c.1)) z.1 = r * dotProduct (G.mulVec c.1) z.1
        rw [Matrix.mulVec_smul, smul_dotProduct, smul_eq_mul] }
  let pairU : U →ₗ[F] Module.Dual F U :=
    { toFun := fun c =>
        { toFun := fun z => dotProduct (G.mulVec c.1) z.1
          map_add' := fun z1 z2 => by
            change dotProduct (G.mulVec c.1) (z1.1 + z2.1) = _
            rw [dotProduct_add]
          map_smul' := fun r z => by
            change dotProduct (G.mulVec c.1) (r • z.1) = r * dotProduct (G.mulVec c.1) z.1
            rw [dotProduct_smul, smul_eq_mul] }
      map_add' := fun c1 c2 => by
        ext z
        change dotProduct (G.mulVec (c1.1 + c2.1)) z.1 = _
        rw [Matrix.mulVec_add, add_dotProduct]
        rfl
      map_smul' := fun r c => by
        ext z
        change dotProduct (G.mulVec (r • c.1)) z.1 = r * dotProduct (G.mulVec c.1) z.1
        rw [Matrix.mulVec_smul, smul_dotProduct, smul_eq_mul] }
  have hpairU_inj : Function.Injective pairU := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro c hc
    have h1 : ∀ x : W, dotProduct (A.mulVec (G.mulVec c.1)) x = 0 := by
      intro x
      have hxU : A.mulVec x ∈ U := ⟨x, rfl⟩
      have h0 : dotProduct (G.mulVec c.1) (A.mulVec x) = 0 := LinearMap.congr_fun hc ⟨A.mulVec x, hxU⟩
      rwa [dotProduct_comm, dotProduct_mulVec_comm, hA_sym, dotProduct_comm] at h0
    have hcU := (hmemU c.1).mp c.2
    rw [hcU] at h1
    ext i
    change (c.1 : Fin k → ZMod 2) i = 0
    have hi := h1 (Pi.single i 1)
    simpa using hi
  have hpairU_surj : Function.Surjective pairU := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    have hd := Subspace.dual_finrank_eq (K := F) (V := U)
    have hr := LinearMap.finrank_range_of_inj hpairU_inj
    exact hr.trans hd.symm
  have hpair_surj : Function.Surjective pairing := by
    intro f
    have hT_le_U : Tsub ≤ U := inf_le_right
    let Ksub : Submodule F U := Tsub.comap U.subtype
    obtain ⟨Kcomp, hK⟩ := Submodule.exists_isCompl Ksub
    let p : U →ₗ[F] Ksub := Ksub.projectionOnto Kcomp hK
    let e : Ksub →ₗ[F] Tsub :=
      { toFun := fun z => ⟨z.1.1, z.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    obtain ⟨c, hc⟩ := hpairU_surj (f.comp (e.comp p))
    refine ⟨c, ?_⟩
    ext ⟨z, hz⟩
    have hmem : (⟨z, hT_le_U hz⟩ : U) ∈ Ksub := hz
    have hp : p ⟨z, hT_le_U hz⟩ = ⟨⟨z, hT_le_U hz⟩, hmem⟩ :=
      Submodule.projectionOnto_apply_left hK ⟨⟨z, hT_le_U hz⟩, hmem⟩
    have hcf : dotProduct (G.mulVec c.1) z = f (e (p ⟨z, hT_le_U hz⟩)) :=
      LinearMap.congr_fun hc ⟨z, hT_le_U hz⟩
    change dotProduct (G.mulVec c.1) z = f ⟨z, hz⟩
    rw [hp] at hcf
    exact hcf
  let TperpU : Submodule F W := (LinearMap.ker pairing).map U.subtype
  have hTperpU_dim : finrank F TperpU = finrank F U - finrank F Tsub := by
    have hdim := LinearMap.finrank_range_add_finrank_ker pairing
    rw [LinearMap.range_eq_top.mpr hpair_surj, finrank_top, Subspace.dual_finrank_eq] at hdim
    rw [Submodule.finrank_map_subtype_eq]
    omega
  have hAP_le_TperpU : APsub ≤ TperpU := by
    rintro c ⟨v, rfl⟩
    refine ⟨⟨A.mulVec (P.mulVec v), ⟨P.mulVec v, rfl⟩⟩, ?_, Matrix.mulVec_mulVec v A P⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    ext ⟨z, hz⟩
    have hzmem : z ∈ Tsub := hz
    have hzT : Pᵀ.mulVec z = 0 := hzmem.1
    have hzU : A.mulVec (G.mulVec z) = z := (hmemU z).mp hzmem.2
    change dotProduct (G.mulVec (A.mulVec (P.mulVec v))) z = 0
    calc dotProduct (G.mulVec (A.mulVec (P.mulVec v))) z
        = dotProduct (G.mulVec (A.mulVec (P.mulVec v))) (A.mulVec (G.mulVec z)) := by rw [hzU]
      _ = dotProduct (Aᵀ.mulVec (G.mulVec (A.mulVec (P.mulVec v)))) (G.mulVec z) := by
          rw [dotProduct_comm, dotProduct_mulVec_comm, dotProduct_comm]
      _ = dotProduct (A.mulVec (P.mulVec v)) (G.mulVec z) := by
          rw [hA_sym, Matrix.mulVec_mulVec (A.mulVec (P.mulVec v)) A G,
              Matrix.mulVec_mulVec (P.mulVec v) (A * G) A, hAGA]
      _ = dotProduct (P.mulVec v) (Aᵀ.mulVec (G.mulVec z)) := dotProduct_mulVec_comm A _ _
      _ = dotProduct (P.mulVec v) z := by rw [hA_sym, hzU]
      _ = dotProduct v (Pᵀ.mulVec z) := dotProduct_mulVec_comm P _ _
      _ = 0 := by rw [hzT, dotProduct_zero]
  have hAP_eq_TperpU : APsub = TperpU := by
    apply Submodule.eq_of_le_of_finrank_eq hAP_le_TperpU
    rw [hAP_dim, hTperpU_dim, hU_dim]
    omega
  let Rsub : Submodule F W := Tsub ⊓ APsub
  have hR_mem : ∀ c : W, c ∈ R ↔ c ∈ Rsub := by
    intro c
    simp only [R, Finset.mem_filter]
    constructor
    · rintro ⟨hcT, hdot⟩
      have hcTs : c ∈ Tsub := (hT_mem c).mp hcT
      refine ⟨hcTs, ?_⟩
      rw [hAP_eq_TperpU]
      refine ⟨⟨c, hcTs.2⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      ext ⟨z, hz⟩
      exact hdot z ((hT_mem z).mpr hz)
    · rintro ⟨hcTs, hcAP⟩
      refine ⟨(hT_mem c).mpr hcTs, ?_⟩
      rw [hAP_eq_TperpU] at hcAP
      rcases hcAP with ⟨⟨c', hc'U⟩, hker, hceq⟩
      subst hceq
      intro z hz
      exact LinearMap.congr_fun hker ⟨z, (hT_mem z).mp hz⟩
  let mu : APsub →ₗ[F] (Fin n → F) := Pᵀ.mulVecLin.comp APsub.subtype
  have hker_mu : finrank F (LinearMap.ker mu) = finrank F Rsub := by
    have hmap : (LinearMap.ker mu).map APsub.subtype = Rsub := by
      ext c
      simp only [Submodule.mem_map, LinearMap.mem_ker, Submodule.coe_subtype, Rsub, Submodule.mem_inf, Tsub]
      constructor
      · rintro ⟨⟨c, hcAP⟩, hker, rfl⟩; exact ⟨⟨hker, hAP_le_U hcAP⟩, hcAP⟩
      · rintro ⟨⟨hker, _⟩, hcAP⟩; exact ⟨⟨c, hcAP⟩, hker, rfl⟩
    rw [← hmap, Submodule.finrank_map_subtype_eq]
  have hrng_mu : LinearMap.range mu = LinearMap.range (Pᵀ * A * P).mulVecLin := by
    ext y
    simp only [mu, APsub, LinearMap.mem_range, LinearMap.coe_comp, Function.comp_apply,
      Submodule.coe_subtype, Subtype.exists]
    constructor
    · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
      exact ⟨v, by change (Pᵀ * A * P) *ᵥ v = Pᵀ *ᵥ (A * P) *ᵥ v; rw [Matrix.mul_assoc, Matrix.mulVec_mulVec]⟩
    · rintro ⟨v, rfl⟩
      exact ⟨(A * P).mulVec v, ⟨v, rfl⟩, by
        change Pᵀ *ᵥ (A * P) *ᵥ v = (Pᵀ * A * P) *ᵥ v; rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc]⟩
  have hmu_dim := LinearMap.finrank_range_add_finrank_ker mu
  rw [hrng_mu, hker_mu] at hmu_dim
  have hrk_PAP : finrank F (LinearMap.range (Pᵀ * A * P).mulVecLin) = (Pᵀ * A * P).rank := rfl
  rw [hrk_PAP, hAP_dim] at hmu_dim
  have hsum : (Pᵀ * A * P).rank + finrank F Tsub + finrank F Rsub = 2 * b := by omega
  let : Fintype Tsub := Fintype.ofFinite Tsub
  let : Fintype Rsub := Fintype.ofFinite Rsub
  have hT_card : T.card = 2 ^ finrank F Tsub := by
    have hs : T = (Tsub : Set W).toFinset := by ext c; simp [hT_mem]
    rw [hs, Set.toFinset_card]
    have hc := Module.card_eq_pow_finrank (K := F) (V := Tsub)
    rw [ZMod.card] at hc
    simpa [Nat.card_eq_fintype_card] using hc
  have hR_card : R.card = 2 ^ finrank F Rsub := by
    have hs : R = (Rsub : Set W).toFinset := by ext c; simp [hR_mem]
    rw [hs, Set.toFinset_card]
    have hc := Module.card_eq_pow_finrank (K := F) (V := Rsub)
    rw [ZMod.card] at hc
    simpa [Nat.card_eq_fintype_card] using hc
  rw [hT_card, hR_card, ← pow_add, ← pow_add, hsum]

end Part3

section Parts12

open Finset Matrix

lemma symm_A (k : ℕ) (hk : 0 < k) (E : Finset (Fin k)) :
    let nxt : Fin k → Fin k := fun i => ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩
    let A : Matrix (Fin k) (Fin k) (ZMod 2) := fun i j =>
      (if i ∈ E ∧ nxt i = j then 1 else 0) + (if j ∈ E ∧ nxt j = i then 1 else 0)
    Aᵀ = A := by
  intro nxt A
  ext i j
  change A j i = A i j
  dsimp only [A]
  exact add_comm _ _

lemma symm_G (k : ℕ) (hk : 0 < k) (E : Finset (Fin k)) :
    let ix : ℕ → Fin k := fun n => ⟨n % k, Nat.mod_lt _ hk⟩
    let nxt : Fin k → Fin k := fun i => ix (i.val + 1)
    let miss := Finset.univ \ E
    let base := if h : miss.Nonempty then (nxt (miss.min' h)).val else 0
    let pos : Fin k → ℕ := fun i => (i.val + k - base) % k
    let start : ℕ → ℕ := fun u => ((Finset.range (u + 1)).filter fun j =>
      j = 0 ∨ ix (base + (j - 1)) ∉ E).sup id
    let lim := if E = Finset.univ then k - (if k % 2 = 0 then 2 else 1) else k
    let G : Matrix (Fin k) (Fin k) (ZMod 2) := fun i j =>
      let u := min (pos i) (pos j)
      let v := max (pos i) (pos j)
      if v < lim ∧ start u = start v ∧ (u - start u) % 2 = 0 ∧ (v - start v) % 2 = 1 then 1 else 0
    Gᵀ = G := by
  intro ix nxt miss base pos start lim G
  ext i j
  change G j i = G i j
  dsimp only [G]
  simp only [min_comm (pos j) (pos i), max_comm (pos j) (pos i)]

private lemma k2_empty :
    let E : Finset (Fin 2) := ∅
    let ix := fun n : Nat => (⟨n % 2, Nat.mod_lt _ (by omega)⟩ : Fin 2)
    let nxt := fun i : Fin 2 => ix (i.val + 1)
    let A : Matrix (Fin 2) (Fin 2) (ZMod 2) := fun i j =>
      (if i ∈ E ∧ nxt i = j then 1 else 0) + (if j ∈ E ∧ nxt j = i then 1 else 0)
    let m := (E.powerset.filter (fun M => ∀ i ∈ M, nxt i ∉ M)).sup Finset.card
    let b := if E = Finset.univ ∧ 2 % 2 = 0 then m - 1 else m
    A = 0 ∧ b = 0 := by
  refine ⟨?_, by decide⟩
  ext i j; fin_cases i <;> fin_cases j <;> decide

private lemma k2_zero :
    let E : Finset (Fin 2) := {0}
    let ix := fun n : Nat => (⟨n % 2, Nat.mod_lt _ (by omega)⟩ : Fin 2)
    let nxt := fun i : Fin 2 => ix (i.val + 1)
    let miss := Finset.univ \ E
    let base := if h : miss.Nonempty then (nxt (miss.min' h)).val else 0
    let pos := fun i : Fin 2 => (i.val + 2 - base) % 2
    let start := fun u : Nat => ((Finset.range (u + 1)).filter (fun j =>
      j = 0 ∨ ix (base + (j - 1)) ∉ E)).sup id
    let lim := if E = Finset.univ then 2 - (if 2 % 2 = 0 then 2 else 1) else 2
    let A : Matrix (Fin 2) (Fin 2) (ZMod 2) := fun i j =>
      (if i ∈ E ∧ nxt i = j then 1 else 0) + (if j ∈ E ∧ nxt j = i then 1 else 0)
    let G : Matrix (Fin 2) (Fin 2) (ZMod 2) := fun i j =>
      let u := min (pos i) (pos j)
      let v := max (pos i) (pos j)
      if v < lim ∧ start u = start v ∧ (u - start u) % 2 = 0 ∧ (v - start v) % 2 = 1 then 1 else 0
    let m := (E.powerset.filter (fun M => ∀ i ∈ M, nxt i ∉ M)).sup Finset.card
    let b := if E = Finset.univ ∧ 2 % 2 = 0 then m - 1 else m
    A * G * A = A ∧ b = 1 ∧ A * A = 1 := by
  refine ⟨?_, by decide, ?_⟩ <;> (ext i j; fin_cases i <;> fin_cases j <;> decide)

private lemma k2_one :
    let E : Finset (Fin 2) := {1}
    let ix := fun n : Nat => (⟨n % 2, Nat.mod_lt _ (by omega)⟩ : Fin 2)
    let nxt := fun i : Fin 2 => ix (i.val + 1)
    let miss := Finset.univ \ E
    let base := if h : miss.Nonempty then (nxt (miss.min' h)).val else 0
    let pos := fun i : Fin 2 => (i.val + 2 - base) % 2
    let start := fun u : Nat => ((Finset.range (u + 1)).filter (fun j =>
      j = 0 ∨ ix (base + (j - 1)) ∉ E)).sup id
    let lim := if E = Finset.univ then 2 - (if 2 % 2 = 0 then 2 else 1) else 2
    let A : Matrix (Fin 2) (Fin 2) (ZMod 2) := fun i j =>
      (if i ∈ E ∧ nxt i = j then 1 else 0) + (if j ∈ E ∧ nxt j = i then 1 else 0)
    let G : Matrix (Fin 2) (Fin 2) (ZMod 2) := fun i j =>
      let u := min (pos i) (pos j)
      let v := max (pos i) (pos j)
      if v < lim ∧ start u = start v ∧ (u - start u) % 2 = 0 ∧ (v - start v) % 2 = 1 then 1 else 0
    let m := (E.powerset.filter (fun M => ∀ i ∈ M, nxt i ∉ M)).sup Finset.card
    let b := if E = Finset.univ ∧ 2 % 2 = 0 then m - 1 else m
    A * G * A = A ∧ b = 1 ∧ A * A = 1 := by
  refine ⟨?_, by decide, ?_⟩ <;> (ext i j; fin_cases i <;> fin_cases j <;> decide)

private lemma k2_univ :
    let E : Finset (Fin 2) := Finset.univ
    let ix := fun n : Nat => (⟨n % 2, Nat.mod_lt _ (by omega)⟩ : Fin 2)
    let nxt := fun i : Fin 2 => ix (i.val + 1)
    let A : Matrix (Fin 2) (Fin 2) (ZMod 2) := fun i j =>
      (if i ∈ E ∧ nxt i = j then 1 else 0) + (if j ∈ E ∧ nxt j = i then 1 else 0)
    let m := (E.powerset.filter (fun M => ∀ i ∈ M, nxt i ∉ M)).sup Finset.card
    let b := if E = Finset.univ ∧ 2 % 2 = 0 then m - 1 else m
    A = 0 ∧ b = 0 := by
  refine ⟨?_, by decide⟩
  ext i j; fin_cases i <;> fin_cases j <;> decide

lemma small_k (k : ℕ) (hk : 0 < k) (hk_le : k ≤ 2) (E : Finset (Fin k)) :
    let F := ZMod 2
    let ix := fun n : Nat => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
    let nxt := fun i : Fin k => ix (i.val + 1)
    let miss := Finset.univ \ E
    let base := if h : miss.Nonempty then (nxt (miss.min' h)).val else 0
    let pos := fun i : Fin k => (i.val + k - base) % k
    let start := fun u : Nat => ((Finset.range (u + 1)).filter (fun j =>
      j = 0 ∨ ix (base + (j - 1)) ∉ E)).sup id
    let lim := if E = Finset.univ then k - (if k % 2 = 0 then 2 else 1) else k
    let A : Matrix (Fin k) (Fin k) F := fun i j =>
      (if i ∈ E ∧ nxt i = j then 1 else 0) + (if j ∈ E ∧ nxt j = i then 1 else 0)
    let G : Matrix (Fin k) (Fin k) F := fun i j =>
      let u := min (pos i) (pos j)
      let v := max (pos i) (pos j)
      if v < lim ∧ start u = start v ∧ (u - start u) % 2 = 0 ∧ (v - start v) % 2 = 1 then 1 else 0
    let m := (E.powerset.filter (fun M => ∀ i ∈ M, nxt i ∉ M)).sup Finset.card
    let b := if E = Finset.univ ∧ k % 2 = 0 then m - 1 else m
    A * G * A = A ∧ A.rank = 2 * b := by
  have hk12 : k = 1 ∨ k = 2 := by omega
  rcases hk12 with rfl | rfl
  · intro F ix nxt miss base pos start lim A G m b
    have hA0 : A = 0 := by
      ext i j; fin_cases i; fin_cases j
      simp only [A, Matrix.zero_apply]
      by_cases h0 : (0 : Fin 1) ∈ E
      · have : nxt (0 : Fin 1) = 0 := rfl
        simp [h0, this]
        decide
      · simp [h0]
    have hm0 : m = 0 := by
      apply Nat.eq_zero_of_le_zero
      apply Finset.sup_le
      intro M hM
      simp only [Finset.mem_filter, Finset.mem_powerset] at hM
      have hMe : M = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro i hi
        have hnxt : nxt i = i := by fin_cases i; rfl
        exact hM.2 i hi (by rwa [hnxt])
      simp [hMe]
    have hb0 : b = 0 := by simp [b, hm0]
    rw [hA0, hb0]
    simp
  · intro F ix nxt miss base pos start lim A G m b
    have hE : E = ∅ ∨ E = {0} ∨ E = {1} ∨ E = Finset.univ := by revert E; decide
    rcases hE with rfl | rfl | rfl | rfl
    · obtain ⟨hA0, hb0⟩ := k2_empty
      change A = 0 at hA0; change b = 0 at hb0
      rw [hA0, hb0]; simp
    · obtain ⟨hAGA, hb1, hAA⟩ := k2_zero
      change A * G * A = A at hAGA; change b = 1 at hb1; change A * A = 1 at hAA
      have hrk2 : A.rank = 2 := by
        have h1 : (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)).rank = 2 := by simp
        have hle1 : (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)).rank ≤ A.rank := by
          rw [← hAA]; exact Matrix.rank_mul_le_left A A
        have hle2 : A.rank ≤ 2 := by
          simpa using (A.rank_le_card_height : A.rank ≤ Fintype.card (Fin 2))
        omega
      exact ⟨hAGA, by rw [hb1, hrk2]⟩
    · obtain ⟨hAGA, hb1, hAA⟩ := k2_one
      change A * G * A = A at hAGA; change b = 1 at hb1; change A * A = 1 at hAA
      have hrk2 : A.rank = 2 := by
        have h1 : (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)).rank = 2 := by simp
        have hle1 : (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)).rank ≤ A.rank := by
          rw [← hAA]; exact Matrix.rank_mul_le_left A A
        have hle2 : A.rank ≤ 2 := by
          simpa using (A.rank_le_card_height : A.rank ≤ Fintype.card (Fin 2))
        omega
      exact ⟨hAGA, by rw [hb1, hrk2]⟩
    · obtain ⟨hA0, hb0⟩ := k2_univ
      change A = 0 at hA0; change b = 0 at hb0
      rw [hA0, hb0]; simp

end Parts12

section LargeK

open Finset Matrix Module

section All

variable (k : ℕ) (hk : 0 < k) (E : Finset (Fin k))

def ix (n : ℕ) : Fin k := ⟨n % k, Nat.mod_lt _ hk⟩
def nxt (i : Fin k) : Fin k := ix k hk (i.val + 1)
def miss : Finset (Fin k) := Finset.univ \ E
def base : ℕ := if h : (miss k E).Nonempty then (nxt k hk ((miss k E).min' h)).val else 0
def pos (i : Fin k) : ℕ := (i.val + k - base k hk E) % k
def start (u : ℕ) : ℕ :=
  ((Finset.range (u + 1)).filter fun j => j = 0 ∨ ix k hk (base k hk E + (j - 1)) ∉ E).sup id
def lim : ℕ := if E = Finset.univ then k - (if k % 2 = 0 then 2 else 1) else k
def ofPos (p : ℕ) : Fin k := ix k hk (base k hk E + p)

lemma base_lt : base k hk E < k := by
  unfold base
  split_ifs
  · exact Fin.isLt _
  · exact hk

lemma pos_lt (i : Fin k) : pos k hk E i < k := Nat.mod_lt _ hk

lemma lim_le : lim k E ≤ k := by
  unfold lim
  split_ifs <;> omega

lemma pos_ofPos {p : ℕ} (hp : p < k) : pos k hk E (ofPos k hk E p) = p := by
  unfold pos ofPos ix
  dsimp only
  have hb : base k hk E < k := base_lt k hk E
  by_cases h : base k hk E + p < k
  · rw [Nat.mod_eq_of_lt h, show base k hk E + p + k - base k hk E = p + k by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt hp]
  · have hmod : (base k hk E + p) % k = base k hk E + p - k := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hmod, show base k hk E + p - k + k - base k hk E = p by omega, Nat.mod_eq_of_lt hp]

lemma ofPos_pos (i : Fin k) : ofPos k hk E (pos k hk E i) = i := by
  unfold ofPos pos ix
  apply Fin.ext
  dsimp only
  have hb : base k hk E < k := base_lt k hk E
  rw [Nat.add_mod_mod, show base k hk E + (i.val + k - base k hk E) = i.val + k by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

lemma nxt_ofPos (p : ℕ) : nxt k hk (ofPos k hk E p) = ofPos k hk E (p + 1) := by
  unfold nxt ofPos ix
  apply Fin.ext
  dsimp only
  rw [Nat.mod_add_mod, add_assoc]

lemma ofPos_tail_not_mem (hE : E ≠ Finset.univ) : ofPos k hk E (k - 1) ∉ E := by
  have hm : (miss k E).Nonempty := by
    rw [miss, Finset.nonempty_iff_ne_empty]
    intro he
    apply hE
    ext i
    simp only [Finset.mem_univ, iff_true]
    by_contra hi
    have : i ∈ (Finset.univ \ E : Finset (Fin k)) := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩
    rw [he] at this
    exact Finset.notMem_empty i this
  let e0 := (miss k E).min' hm
  have he0_mem : e0 ∈ miss k E := Finset.min'_mem _ hm
  have he0_notE : e0 ∉ E := (Finset.mem_sdiff.mp he0_mem).2
  have hbase : base k hk E = (nxt k hk e0).val := by simp [base, hm, e0]
  have heq : ofPos k hk E (k - 1) = e0 := by
    unfold ofPos ix
    apply Fin.ext
    dsimp only
    rw [hbase]
    change ((e0.val + 1) % k + (k - 1)) % k = e0.val
    rw [Nat.mod_add_mod, show e0.val + 1 + (k - 1) = e0.val + k by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt e0.isLt]
  rwa [heq]

lemma start_le (u : ℕ) : start k hk E u ≤ u := by
  unfold start
  apply Finset.sup_le
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_range] at hj
  exact Nat.lt_succ_iff.mp hj.1

lemma start_zero : start k hk E 0 = 0 :=
  Nat.eq_zero_of_le_zero (start_le k hk E 0)

lemma start_mono {u v : ℕ} (huv : u ≤ v) : start k hk E u ≤ start k hk E v := by
  unfold start
  exact Finset.sup_mono (Finset.filter_subset_filter _ (Finset.range_mono (Nat.succ_le_succ huv)))

lemma start_eq_of_le {u v : ℕ} (huv : u ≤ v) (hsu : start k hk E v ≤ u) :
    start k hk E u = start k hk E v := by
  unfold start
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · intro hj; exact ⟨by omega, hj.2⟩
  · intro hj
    have hmem : j ∈ (Finset.range (v + 1)).filter
        (fun j => j = 0 ∨ ix k hk (base k hk E + (j - 1)) ∉ E) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj.1, hj.2⟩
    have hle : j ≤ start k hk E v := Finset.le_sup (f := id) hmem
    exact ⟨by omega, hj.2⟩

lemma start_succ_eq (u : ℕ) : start k hk E (u + 1) = start k hk E u ↔ ofPos k hk E u ∈ E := by
  by_cases hu : ofPos k hk E u ∈ E
  · constructor
    · intro _; exact hu
    · intro _
      unfold start
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨hj, hp⟩
        refine ⟨?_, hp⟩
        by_contra hge
        have hju : j = u + 1 := by omega
        subst hju
        rcases hp with h0 | hnot
        · omega
        · exact hnot (by simpa [ofPos] using hu)
      · rintro ⟨hj, hp⟩; exact ⟨by omega, hp⟩
  · constructor
    · intro h
      exfalso
      have hmem : u + 1 ∈ (Finset.range (u + 2)).filter
          (fun j => j = 0 ∨ ix k hk (base k hk E + (j - 1)) ∉ E) := by
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, Or.inr (by simpa [ofPos] using hu)⟩
      have hge : u + 1 ≤ start k hk E (u + 1) := Finset.le_sup (f := id) hmem
      have hle : start k hk E u ≤ u := start_le k hk E u
      omega
    · intro h; exact absurd h hu

lemma start_univ (hE : E = Finset.univ) (u : ℕ) : start k hk E u = 0 := by
  unfold start
  apply Nat.eq_zero_of_le_zero
  apply Finset.sup_le
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_range] at hj
  rcases hj.2 with rfl | hnot
  · exact le_refl 0
  · exfalso; apply hnot; rw [hE]; exact Finset.mem_univ _

lemma mem_E_of_start_lt {p : ℕ} (hs : start k hk E (p + 1) ≤ p) : ofPos k hk E p ∈ E := by
  rw [← start_succ_eq]
  exact (start_eq_of_le k hk E (Nat.le_succ p) hs).symm

lemma mem_E_of_start_eq {u v : ℕ} (huv : u < v) (hseq : start k hk E u = start k hk E v) :
    ofPos k hk E u ∈ E := by
  apply mem_E_of_start_lt
  have h1 := start_le k hk E u
  have h2 := start_mono k hk E (show u + 1 ≤ v by omega)
  omega

def A : Matrix (Fin k) (Fin k) (ZMod 2) := fun i j =>
  (if i ∈ E ∧ nxt k hk i = j then 1 else 0) + (if j ∈ E ∧ nxt k hk j = i then 1 else 0)

def G : Matrix (Fin k) (Fin k) (ZMod 2) := fun i j =>
  let u := min (pos k hk E i) (pos k hk E j)
  let v := max (pos k hk E i) (pos k hk E j)
  if v < lim k E ∧ start k hk E u = start k hk E v ∧
      (u - start k hk E u) % 2 = 0 ∧ (v - start k hk E v) % 2 = 1 then 1 else 0

lemma symm_A_loc : (A k hk E)ᵀ = A k hk E := by
  ext i j; change A k hk E j i = A k hk E i j; dsimp only [A]; exact add_comm _ _

lemma symm_G_loc : (G k hk E)ᵀ = G k hk E := by
  ext i j; change G k hk E j i = G k hk E i j; dsimp only [G]
  simp only [min_comm (pos k hk E j) (pos k hk E i), max_comm (pos k hk E j) (pos k hk E i)]

lemma A_ofPos (hk3 : 3 ≤ k) {p q : ℕ} (hp : p < k) (hq : q < k) :
    A k hk E (ofPos k hk E p) (ofPos k hk E q) =
      (if p + 1 = q ∧ ofPos k hk E p ∈ E then (1 : ZMod 2) else 0) +
      (if q + 1 = p ∧ ofPos k hk E q ∈ E then 1 else 0) +
      (if E = Finset.univ ∧ p = k - 1 ∧ q = 0 then 1 else 0) +
      (if E = Finset.univ ∧ q = k - 1 ∧ p = 0 then 1 else 0) := by
  have h1 : nxt k hk (ofPos k hk E p) = ofPos k hk E q ↔ p + 1 = q ∨ (p = k - 1 ∧ q = 0) := by
    rw [nxt_ofPos]
    constructor
    · intro heq
      have hpos := congrArg (pos k hk E) heq
      rw [pos_ofPos k hk E hq] at hpos
      have hmod : (p + 1) % k = q := by
        have hp' : pos k hk E (ofPos k hk E (p + 1)) = (p + 1) % k := by
          by_cases hlt : p + 1 < k
          · rw [pos_ofPos k hk E hlt, Nat.mod_eq_of_lt hlt]
          · have hpk : p + 1 = k := by omega
            rw [hpk, show ofPos k hk E k = ofPos k hk E 0 by
              unfold ofPos ix; apply Fin.ext; simp, pos_ofPos k hk E hk, Nat.mod_self]
        omega
      by_cases hlt : p + 1 < k
      · left; rw [Nat.mod_eq_of_lt hlt] at hmod; exact hmod
      · right; have hpk : p = k - 1 := by omega
        subst hpk; rw [show k - 1 + 1 = k by omega, Nat.mod_self] at hmod; exact ⟨rfl, hmod.symm⟩
    · rintro (rfl | ⟨rfl, rfl⟩)
      · rfl
      · unfold ofPos ix; apply Fin.ext; simp [show k - 1 + 1 = k by omega]
  have h2 : nxt k hk (ofPos k hk E q) = ofPos k hk E p ↔ q + 1 = p ∨ (q = k - 1 ∧ p = 0) := by
    rw [nxt_ofPos]
    constructor
    · intro heq
      have hpos := congrArg (pos k hk E) heq
      rw [pos_ofPos k hk E hp] at hpos
      have hmod : (q + 1) % k = p := by
        have hq' : pos k hk E (ofPos k hk E (q + 1)) = (q + 1) % k := by
          by_cases hlt : q + 1 < k
          · rw [pos_ofPos k hk E hlt, Nat.mod_eq_of_lt hlt]
          · have hqk : q + 1 = k := by omega
            rw [hqk, show ofPos k hk E k = ofPos k hk E 0 by
              unfold ofPos ix; apply Fin.ext; simp, pos_ofPos k hk E hk, Nat.mod_self]
        omega
      by_cases hlt : q + 1 < k
      · left; rw [Nat.mod_eq_of_lt hlt] at hmod; exact hmod
      · right; have hqk : q = k - 1 := by omega
        subst hqk; rw [show k - 1 + 1 = k by omega, Nat.mod_self] at hmod; exact ⟨rfl, hmod.symm⟩
    · rintro (rfl | ⟨rfl, rfl⟩)
      · rfl
      · unfold ofPos ix; apply Fin.ext; simp [show k - 1 + 1 = k by omega]
  have hfst : (if ofPos k hk E p ∈ E ∧ nxt k hk (ofPos k hk E p) = ofPos k hk E q then (1 : ZMod 2) else 0) =
      (if p + 1 = q ∧ ofPos k hk E p ∈ E then 1 else 0) +
      (if E = Finset.univ ∧ p = k - 1 ∧ q = 0 then 1 else 0) := by
    simp only [h1]
    by_cases hE : E = Finset.univ
    · simp only [hE, Finset.mem_univ, true_and, and_true]
      by_cases hp1 : p + 1 = q
      · rw [if_pos (Or.inl hp1), if_pos hp1, if_neg (by rintro ⟨_, rfl⟩; simp at hp1), add_zero]
      · by_cases hp2 : p = k - 1 ∧ q = 0
        · rw [if_pos (Or.inr hp2), if_neg hp1, if_pos hp2, zero_add]
        · rw [if_neg (by tauto), if_neg hp1, if_neg hp2, zero_add]
    · have htail := ofPos_tail_not_mem k hk E hE
      have hEu0 : (if E = Finset.univ ∧ p = k - 1 ∧ q = 0 then (1 : ZMod 2) else 0) = 0 :=
        if_neg (fun h => hE h.1)
      rw [hEu0, add_zero]
      by_cases hpe : ofPos k hk E p ∈ E
      · have hne : ¬ (p = k - 1 ∧ q = 0) := by rintro ⟨rfl, _⟩; exact htail hpe
        by_cases hp1 : p + 1 = q
        · rw [if_pos ⟨hpe, Or.inl hp1⟩, if_pos ⟨hp1, hpe⟩]
        · rw [if_neg (by rintro ⟨_, h | h⟩; exact hp1 h; exact hne h), if_neg (fun h => hp1 h.1)]
      · rw [if_neg (fun h => hpe h.1), if_neg (fun h => hpe h.2)]
  have hsnd : (if ofPos k hk E q ∈ E ∧ nxt k hk (ofPos k hk E q) = ofPos k hk E p then (1 : ZMod 2) else 0) =
      (if q + 1 = p ∧ ofPos k hk E q ∈ E then 1 else 0) +
      (if E = Finset.univ ∧ q = k - 1 ∧ p = 0 then 1 else 0) := by
    simp only [h2]
    by_cases hE : E = Finset.univ
    · simp only [hE, Finset.mem_univ, true_and, and_true]
      by_cases hq1 : q + 1 = p
      · rw [if_pos (Or.inl hq1), if_pos hq1, if_neg (by rintro ⟨_, rfl⟩; simp at hq1), add_zero]
      · by_cases hq2 : q = k - 1 ∧ p = 0
        · rw [if_pos (Or.inr hq2), if_neg hq1, if_pos hq2, zero_add]
        · rw [if_neg (by tauto), if_neg hq1, if_neg hq2, zero_add]
    · have htail := ofPos_tail_not_mem k hk E hE
      have hEu0 : (if E = Finset.univ ∧ q = k - 1 ∧ p = 0 then (1 : ZMod 2) else 0) = 0 :=
        if_neg (fun h => hE h.1)
      rw [hEu0, add_zero]
      by_cases hqe : ofPos k hk E q ∈ E
      · have hne : ¬ (q = k - 1 ∧ p = 0) := by rintro ⟨rfl, _⟩; exact htail hqe
        by_cases hq1 : q + 1 = p
        · rw [if_pos ⟨hqe, Or.inl hq1⟩, if_pos ⟨hq1, hqe⟩]
        · rw [if_neg (by rintro ⟨_, h | h⟩; exact hq1 h; exact hne h), if_neg (fun h => hq1 h.1)]
      · rw [if_neg (fun h => hqe h.1), if_neg (fun h => hqe h.2)]
  unfold A
  rw [hfst, hsnd]
  abel

def active (p : ℕ) : Prop :=
  p < lim k E ∧ ((p - start k hk E p) % 2 = 1 ∨ (p + 1 < lim k E ∧ start k hk E (p + 1) = start k hk E p))

def gaPred (p q : ℕ) : Prop :=
  active k hk E p ∧
  if (p - start k hk E p) % 2 = 1 then
    q = p ∨ (E = Finset.univ ∧ q = k - 1)
  else
    q = p ∨ (start k hk E q = start k hk E p ∧ ¬ active k hk E q ∧ q ≤ lim k E)

lemma G_ofPos {p q : ℕ} (hp : p < k) (hq : q < k) :
    G k hk E (ofPos k hk E p) (ofPos k hk E q) =
      if max p q < lim k E ∧ start k hk E (min p q) = start k hk E (max p q) ∧
         (min p q - start k hk E (min p q)) % 2 = 0 ∧
         (max p q - start k hk E (max p q)) % 2 = 1
      then 1 else 0 := by
  unfold G
  rw [pos_ofPos k hk E hp, pos_ofPos k hk E hq]

lemma G_eq_zero_of_not_active {p r : ℕ} (hp : p < k) (hr : r < k)
    (hna : ¬ active k hk E p) :
    G k hk E (ofPos k hk E p) (ofPos k hk E r) = 0 := by
  rw [G_ofPos k hk E hp hr, ite_eq_right_iff]
  intro ⟨hmax, hst, hmin_p, hmax_p⟩
  exfalso; apply hna
  rcases le_or_gt r p with hrp | hpr
  · rw [min_eq_right hrp, max_eq_left hrp] at *
    exact ⟨hmax, Or.inl hmax_p⟩
  · rw [min_eq_left hpr.le, max_eq_right hpr.le] at *
    have hp1_lt : p + 1 < lim k E := by
      by_contra hge
      have hrp1 : r = p + 1 := by omega
      subst hrp1
      omega
    have hst1 : start k hk E (p + 1) = start k hk E p := by
      have h1 := start_mono k hk E (show p ≤ p + 1 by omega)
      have h2 := start_mono k hk E (show p + 1 ≤ r by omega)
      omega
    exact ⟨by omega, Or.inr ⟨hp1_lt, hst1⟩⟩

def posEquiv : Fin k ≃ Fin k where
  toFun i := ⟨pos k hk E i, pos_lt k hk E i⟩
  invFun p := ofPos k hk E p.val
  left_inv i := ofPos_pos k hk E i
  right_inv p := Fin.ext (pos_ofPos k hk E p.isLt)

lemma sum_A_mul (hk3 : 3 ≤ k) (f : Fin k → ZMod 2) {q : ℕ} (hq : q < k) :
    (∑ r : Fin k, f r * A k hk E r (ofPos k hk E q)) =
      (if 0 < q ∧ ofPos k hk E (q - 1) ∈ E then f (ofPos k hk E (q - 1)) else 0) +
      (if q + 1 < k ∧ ofPos k hk E q ∈ E then f (ofPos k hk E (q + 1)) else 0) +
      (if E = Finset.univ ∧ q = 0 then f (ofPos k hk E (k - 1)) else 0) +
      (if E = Finset.univ ∧ q = k - 1 then f (ofPos k hk E 0) else 0) := by
  rw [← (posEquiv k hk E).symm.sum_comp]
  dsimp [posEquiv]
  have hterm : ∀ r : Fin k, f (ofPos k hk E r.val) * A k hk E (ofPos k hk E r.val) (ofPos k hk E q) =
      (if r.val + 1 = q ∧ ofPos k hk E r.val ∈ E then f (ofPos k hk E r.val) else 0) +
      (if q + 1 = r.val ∧ ofPos k hk E q ∈ E then f (ofPos k hk E r.val) else 0) +
      (if E = Finset.univ ∧ r.val = k - 1 ∧ q = 0 then f (ofPos k hk E r.val) else 0) +
      (if E = Finset.univ ∧ q = k - 1 ∧ r.val = 0 then f (ofPos k hk E r.val) else 0) := by
    intro r
    rw [A_ofPos k hk E hk3 r.isLt hq]
    simp only [mul_add, mul_ite, mul_one, mul_zero]
  simp_rw [hterm, Finset.sum_add_distrib]
  have s1 : (∑ r : Fin k, if r.val + 1 = q ∧ ofPos k hk E r.val ∈ E then f (ofPos k hk E r.val) else 0) =
      if 0 < q ∧ ofPos k hk E (q - 1) ∈ E then f (ofPos k hk E (q - 1)) else 0 := by
    by_cases h : 0 < q ∧ ofPos k hk E (q - 1) ∈ E
    · rw [if_pos h]
      refine (Finset.sum_eq_single (⟨q - 1, by omega⟩ : Fin k) ?_ ?_).trans
        (by simp [show q - 1 + 1 = q by omega, h.2])
      · intro r _ hne
        have hrv : r.val ≠ q - 1 := fun heq => hne (Fin.ext heq)
        rw [if_neg]; omega
      · intro hm; exact absurd (Finset.mem_univ _) hm
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun r _ => ?_
      rw [if_neg]; rintro ⟨hr1, hrm⟩; apply h
      exact ⟨by omega, by simpa [show r.val = q - 1 by omega] using hrm⟩
  have s2 : (∑ r : Fin k, if q + 1 = r.val ∧ ofPos k hk E q ∈ E then f (ofPos k hk E r.val) else 0) =
      if q + 1 < k ∧ ofPos k hk E q ∈ E then f (ofPos k hk E (q + 1)) else 0 := by
    by_cases h : q + 1 < k ∧ ofPos k hk E q ∈ E
    · rw [if_pos h]
      refine (Finset.sum_eq_single (⟨q + 1, h.1⟩ : Fin k) ?_ ?_).trans (by simp [h.2])
      · intro r _ hne
        have hrv : r.val ≠ q + 1 := fun heq => hne (Fin.ext heq)
        rw [if_neg]; omega
      · intro hm; exact absurd (Finset.mem_univ _) hm
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun r _ => ?_
      rw [if_neg]; rintro ⟨hq1, hqm⟩; apply h
      exact ⟨by omega, hqm⟩
  have s3 : (∑ r : Fin k, if E = Finset.univ ∧ r.val = k - 1 ∧ q = 0 then f (ofPos k hk E r.val) else 0) =
      if E = Finset.univ ∧ q = 0 then f (ofPos k hk E (k - 1)) else 0 := by
    by_cases h : E = Finset.univ ∧ q = 0
    · rw [if_pos h]
      refine (Finset.sum_eq_single (⟨k - 1, by omega⟩ : Fin k) ?_ ?_).trans (by simp [h])
      · intro r _ hne
        have hrv : r.val ≠ k - 1 := fun heq => hne (Fin.ext heq)
        rw [if_neg]; omega
      · intro hm; exact absurd (Finset.mem_univ _) hm
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun r _ => ?_
      rw [if_neg]; rintro ⟨h1, _, h2⟩; exact h ⟨h1, h2⟩
  have s4 : (∑ r : Fin k, if E = Finset.univ ∧ q = k - 1 ∧ r.val = 0 then f (ofPos k hk E r.val) else 0) =
      if E = Finset.univ ∧ q = k - 1 then f (ofPos k hk E 0) else 0 := by
    by_cases h : E = Finset.univ ∧ q = k - 1
    · rw [if_pos h]
      refine (Finset.sum_eq_single (⟨0, hk⟩ : Fin k) ?_ ?_).trans (by simp [h])
      · intro r _ hne
        have hrv : r.val ≠ 0 := fun heq => hne (Fin.ext heq)
        rw [if_neg]; omega
      · intro hm; exact absurd (Finset.mem_univ _) hm
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun r _ => ?_
      rw [if_neg]; rintro ⟨h1, h2, _⟩; exact h ⟨h1, h2⟩
  rw [s1, s2, s3, s4]

private lemma z2_ite_add_eq_zero {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) :
    (if P then (1 : ZMod 2) else 0) + (if Q then (1 : ZMod 2) else 0) = 0 := by
  by_cases hp : P
  · have hq : Q := h.mp hp
    simp [hp, hq]
    decide
  · have hq : ¬ Q := fun hq => hp (h.mpr hq)
    simp [hp, hq]

private lemma z2_11 : (1 : ZMod 2) + 1 = 0 := by decide

section ClassicalSec
open Classical

lemma GA_ofPos_eq (hk3 : 3 ≤ k) {p q : ℕ} (hp : p < k) (hq : q < k) :
    (G k hk E * A k hk E) (ofPos k hk E p) (ofPos k hk E q) =
      if gaPred k hk E p q then 1 else 0 := by
  change (∑ r : Fin k, G k hk E (ofPos k hk E p) r * A k hk E r (ofPos k hk E q)) = _
  rw [sum_A_mul k hk E hk3 (fun r => G k hk E (ofPos k hk E p) r) hq]
  by_cases hna : active k hk E p
  · have hplim : p < lim k E := hna.1
    have hlimk : lim k E ≤ k := lim_le k E
    have hsp : start k hk E p ≤ p := start_le k hk E p
    have hu_lim : E = Finset.univ → lim k E % 2 = 0 ∧ lim k E ≤ k - 1 ∧
        (lim k E = k - 2 ∨ lim k E = k - 1) := by
      intro hE; unfold lim; rw [ite_eq_left_iff.mpr (fun h => absurd hE h)]
      by_cases hk2 : k % 2 = 0 <;> simp [hk2] <;> omega
    rcases Nat.mod_two_eq_zero_or_one (p - start k hk E p) with hpar | hpar
    · -- EVEN (p - start p) % 2 = 0
      have hp_next : p + 1 < lim k E ∧ start k hk E (p + 1) = start k hk E p := by
        rcases hna.2 with h1 | h2
        · omega
        · exact h2
      have hG_even : ∀ r < k, G k hk E (ofPos k hk E p) (ofPos k hk E r) =
          if p < r ∧ r < lim k E ∧ start k hk E r = start k hk E p ∧
             (r - start k hk E p) % 2 = 1 then 1 else 0 := by
        intro r hr
        rw [G_ofPos k hk E hp hr]
        by_cases hlt : p < r
        · rw [min_eq_left hlt.le, max_eq_right hlt.le]
          by_cases hs : start k hk E r = start k hk E p
          · simp [hlt, hs, hpar]
          · simp [hlt, hs, Ne.symm hs]
        · rw [min_eq_right (by omega), max_eq_left (by omega)]
          have hcond : ¬ (p < r ∧ r < lim k E ∧ start k hk E r = start k hk E p ∧ (r - start k hk E p) % 2 = 1) := by omega
          have hcond2 : ¬ (p < lim k E ∧ start k hk E r = start k hk E p ∧ (r - start k hk E r) % 2 = 0 ∧ (p - start k hk E p) % 2 = 1) := by omega
          rw [if_neg hcond, if_neg hcond2]
      have hT3 : (if E = Finset.univ ∧ q = 0 then G k hk E (ofPos k hk E p) (ofPos k hk E (k - 1)) else 0) = 0 := by
        split_ifs with h
        · rw [hG_even (k - 1) (by omega), if_neg]; obtain ⟨_, h2, _⟩ := hu_lim h.1; omega
        · rfl
      have hT4 : (if E = Finset.univ ∧ q = k - 1 then G k hk E (ofPos k hk E p) (ofPos k hk E 0) else 0) = 0 := by
        split_ifs with h
        · rw [hG_even 0 hk, if_neg]; omega
        · rfl
      rw [hT3, hT4, add_zero, add_zero]
      by_cases hqp : q = p
      · subst hqp
        have hpar1 : (q - start k hk E q) % 2 ≠ 1 := by omega
        have hpt : gaPred k hk E q q := by simp [gaPred, hna, hpar1]
        rw [if_pos hpt]
        have hT1 : (if 0 < q ∧ ofPos k hk E (q - 1) ∈ E then G k hk E (ofPos k hk E q) (ofPos k hk E (q - 1)) else 0) = 0 := by
          split_ifs with h
          · rw [hG_even (q - 1) (by omega), if_neg]; omega
          · rfl
        have hT2 : (if q + 1 < k ∧ ofPos k hk E q ∈ E then G k hk E (ofPos k hk E q) (ofPos k hk E (q + 1)) else 0) = 1 := by
          have hqE : ofPos k hk E q ∈ E := (start_succ_eq k hk E q).mp hp_next.2
          rw [if_pos ⟨by omega, hqE⟩, hG_even (q + 1) (by omega), if_pos ⟨by omega, hp_next.1, hp_next.2, by omega⟩]
        rw [hT1, hT2, zero_add]
      · by_cases hstop : start k hk E q = start k hk E p ∧ ¬ active k hk E q ∧ q ≤ lim k E
        · have hpar1 : (p - start k hk E p) % 2 ≠ 1 := by omega
          have hpt : gaPred k hk E p q := by simp [gaPred, hna, hpar1, hstop]
          rw [if_pos hpt]
          have hpgtq : p < q := by
            by_contra hle
            have hqp' : q < p := by omega
            apply hstop.2.1
            refine ⟨by omega, Or.inr ⟨by omega, ?_⟩⟩
            have h1 := start_mono k hk E (show q ≤ q + 1 by omega)
            have h2 := start_mono k hk E (show q + 1 ≤ p by omega)
            omega
          have hq_even : (q - start k hk E p) % 2 = 0 := by
            by_cases hqlim : q = lim k E
            · have hE : E = Finset.univ := by
                by_contra hne
                have hlk : lim k E = k := by simp [lim, hne]
                omega
              have := hu_lim hE
              rw [hqlim, start_univ k hk E hE]
              simp [this.1]
            · have hql : q < lim k E := by omega
              by_contra hodd
              apply hstop.2.1
              exact ⟨hql, Or.inl (by rw [hstop.1]; omega)⟩
          have hqge2 : p + 2 ≤ q := by omega
          have hq1_eq : start k hk E (q - 1) = start k hk E p := by
            have h1 := start_mono k hk E (show p ≤ q - 1 by omega)
            have h2 := start_mono k hk E (show q - 1 ≤ q by omega)
            omega
          have hT1 : (if 0 < q ∧ ofPos k hk E (q - 1) ∈ E then G k hk E (ofPos k hk E p) (ofPos k hk E (q - 1)) else 0) = 1 := by
            have hqmE : ofPos k hk E (q - 1) ∈ E := mem_E_of_start_eq k hk E (u := q - 1) (v := q) (by omega) (by rw [hq1_eq, hstop.1])
            rw [if_pos ⟨by omega, hqmE⟩, hG_even (q - 1) (by omega), if_pos ⟨by omega, by omega, hq1_eq, by omega⟩]
          have hT2 : (if q + 1 < k ∧ ofPos k hk E q ∈ E then G k hk E (ofPos k hk E p) (ofPos k hk E (q + 1)) else 0) = 0 := by
            split_ifs with h
            · rw [hG_even (q + 1) (by omega), if_neg]
              rintro ⟨_, hlim1, hs1, _⟩
              apply hstop.2.1
              exact ⟨by omega, Or.inr ⟨hlim1, by rw [hstop.1, hs1]⟩⟩
            · rfl
          rw [hT1, hT2, add_zero]
        · have hpar1 : (p - start k hk E p) % 2 ≠ 1 := by omega
          have hpred_f : ¬ gaPred k hk E p q := by
            simp only [gaPred, hna, hpar1, hqp, hstop, or_self, ite_false, and_false, not_false_eq_true]
          rw [if_neg hpred_f]
          have h12 : (0 < q ∧ ofPos k hk E (q - 1) ∈ E ∧ p < q - 1 ∧ q - 1 < lim k E ∧
              start k hk E (q - 1) = start k hk E p ∧ (q - 1 - start k hk E p) % 2 = 1) ↔
              (q + 1 < k ∧ ofPos k hk E q ∈ E ∧ p < q + 1 ∧ q + 1 < lim k E ∧
              start k hk E (q + 1) = start k hk E p ∧ (q + 1 - start k hk E p) % 2 = 1) := by
            constructor
            · rintro ⟨hq0, hqmE, hpm, hm_lim, hsm, hpm1⟩
              have hsq : start k hk E q = start k hk E p := by
                have := (start_succ_eq k hk E (q - 1)).mpr hqmE
                rw [show q - 1 + 1 = q by omega] at this
                rw [this, hsm]
              have hqact : active k hk E q := by
                by_contra hn
                exact hstop ⟨hsq, hn, by omega⟩
              have hq_even : (q - start k hk E p) % 2 = 0 := by omega
              have hq_next : q + 1 < lim k E ∧ start k hk E (q + 1) = start k hk E q := by
                rcases hqact.2 with h1 | h2
                · rw [hsq] at h1; omega
                · exact h2
              have hqE : ofPos k hk E q ∈ E := (start_succ_eq k hk E q).mp hq_next.2
              exact ⟨by omega, hqE, by omega, hq_next.1, by rw [hq_next.2, hsq], by omega⟩
            · rintro ⟨hq1k, hqE, hpq1, hq1lim, hsq1, hpar1'⟩
              have hsq : start k hk E q = start k hk E p := by
                have := (start_succ_eq k hk E q).mpr hqE
                rw [← this, hsq1]
              have hsq_le : start k hk E p ≤ q := by rw [← hsq]; exact start_le k hk E q
              have hq_even : (q - start k hk E p) % 2 = 0 := by omega
              have hqm1_ge : p < q - 1 := by omega
              have hqm1_st : start k hk E (q - 1) = start k hk E p := by
                have h1 := start_mono k hk E (show p ≤ q - 1 by omega)
                have h2 := start_mono k hk E (show q - 1 ≤ q by omega)
                omega
              have hqmE : ofPos k hk E (q - 1) ∈ E := mem_E_of_start_eq k hk E (u := q - 1) (v := q) (by omega) (by rw [hqm1_st, hsq])
              exact ⟨by omega, hqmE, hqm1_ge, by omega, hqm1_st, by omega⟩
          have hLHS_eq :
              (if 0 < q ∧ ofPos k hk E (q - 1) ∈ E then G k hk E (ofPos k hk E p) (ofPos k hk E (q - 1)) else 0) +
              (if q + 1 < k ∧ ofPos k hk E q ∈ E then G k hk E (ofPos k hk E p) (ofPos k hk E (q + 1)) else 0) =
              (if 0 < q ∧ ofPos k hk E (q - 1) ∈ E ∧ p < q - 1 ∧ q - 1 < lim k E ∧
                  start k hk E (q - 1) = start k hk E p ∧ (q - 1 - start k hk E p) % 2 = 1 then 1 else 0) +
              (if q + 1 < k ∧ ofPos k hk E q ∈ E ∧ p < q + 1 ∧ q + 1 < lim k E ∧
                  start k hk E (q + 1) = start k hk E p ∧ (q + 1 - start k hk E p) % 2 = 1 then 1 else 0) := by
            congr 1
            · by_cases h0 : 0 < q ∧ ofPos k hk E (q - 1) ∈ E
              · rw [if_pos h0, hG_even (q - 1) (by omega)]; simp [h0]
              · rw [if_neg h0, if_neg]; intro h; exact h0 ⟨h.1, h.2.1⟩
            · by_cases h0 : q + 1 < k ∧ ofPos k hk E q ∈ E
              · rw [if_pos h0, hG_even (q + 1) h0.1]; simp [h0]
              · rw [if_neg h0, if_neg]; intro h; exact h0 ⟨h.1, h.2.1⟩
          rw [hLHS_eq]
          exact z2_ite_add_eq_zero h12
    · -- ODD (p - start p) % 2 = 1
      have hsp_lt : start k hk E p < p := by omega
      have hG_odd : ∀ r < k, G k hk E (ofPos k hk E p) (ofPos k hk E r) =
          if r < p ∧ start k hk E r = start k hk E p ∧ (r - start k hk E p) % 2 = 0 then 1 else 0 := by
        intro r hr
        rw [G_ofPos k hk E hp hr]
        by_cases hlt : r < p
        · rw [min_comm p r, min_eq_left hlt.le, max_comm p r, max_eq_right hlt.le]
          by_cases hs : start k hk E r = start k hk E p
          · simp [hlt, hplim, hs, hpar]
          · simp [hlt, hs]
        · rw [min_comm p r, min_eq_right (by omega), max_comm p r, max_eq_left (by omega)]
          have hc1 : ¬ (r < p ∧ start k hk E r = start k hk E p ∧ (r - start k hk E p) % 2 = 0) := by omega
          have hc2 : ¬ (max r p < lim k E ∧ start k hk E p = start k hk E r ∧ (p - start k hk E p) % 2 = 0 ∧ (r - start k hk E r) % 2 = 1) := by omega
          rw [if_neg hc1, if_neg]
          rintro ⟨_, _, h2, _⟩
          omega
      have hT3 : (if E = Finset.univ ∧ q = 0 then G k hk E (ofPos k hk E p) (ofPos k hk E (k - 1)) else 0) = 0 := by
        split_ifs with h
        · rw [hG_odd (k - 1) (by omega), if_neg]; obtain ⟨_, h2, _⟩ := hu_lim h.1; omega
        · rfl
      rw [hT3]
      simp only [add_zero]
      by_cases hqp : q = p
      · subst hqp
        simp only [gaPred, hna, hpar, ite_true, true_or, and_self]
        have hT1 : (if 0 < q ∧ ofPos k hk E (q - 1) ∈ E then G k hk E (ofPos k hk E q) (ofPos k hk E (q - 1)) else 0) = 1 := by
          have hsm1 : start k hk E (q - 1) = start k hk E q := start_eq_of_le k hk E (by omega) (by omega)
          have hqmE : ofPos k hk E (q - 1) ∈ E := mem_E_of_start_eq k hk E (u := q - 1) (v := q) (by omega) hsm1
          rw [if_pos ⟨by omega, hqmE⟩, hG_odd (q - 1) (by omega), if_pos ⟨by omega, hsm1, by omega⟩]
        have hT2 : (if q + 1 < k ∧ ofPos k hk E q ∈ E then G k hk E (ofPos k hk E q) (ofPos k hk E (q + 1)) else 0) = 0 := by
          split_ifs with h
          · rw [hG_odd (q + 1) h.1, if_neg]; omega
          · rfl
        have hT4 : (if E = Finset.univ ∧ q = k - 1 then G k hk E (ofPos k hk E q) (ofPos k hk E 0) else 0) = 0 := by
          split_ifs with h
          · obtain ⟨_, h2, _⟩ := hu_lim h.1
            rw [h.2] at hplim
            omega
          · rfl
        rw [hT1, hT2, hT4, add_zero, add_zero]
      · by_cases hEk : E = Finset.univ ∧ q = k - 1
        · have hna_u : active k hk Finset.univ p := hEk.1 ▸ hna
          have hpar_u : (p - start k hk Finset.univ p) % 2 = 1 := hEk.1 ▸ hpar
          have hpt : gaPred k hk E p q := by
            rw [hEk.1, hEk.2]
            exact ⟨hna_u, by rw [if_pos hpar_u]; exact Or.inr ⟨rfl, rfl⟩⟩
          rw [if_pos hpt]
          have hsu : start k hk E p = 0 := start_univ k hk E hEk.1 p
          have hT1 : (if 0 < q ∧ ofPos k hk E (q - 1) ∈ E then G k hk E (ofPos k hk E p) (ofPos k hk E (q - 1)) else 0) = 0 := by
            split_ifs with h
            · rw [hG_odd (q - 1) (by omega), if_neg]
              obtain ⟨_, h2, hor⟩ := hu_lim hEk.1
              rcases hor with hlim2 | hlim1
              · rw [hEk.2]; omega
              · have hko : k % 2 = 1 := by
                  by_contra hke
                  have : k % 2 = 0 := by omega
                  simp [lim, hEk.1, this] at hlim1
                  omega
                rw [hEk.2, hsu]
                omega
            · rfl
          have hT2 : (if q + 1 < k ∧ ofPos k hk E q ∈ E then G k hk E (ofPos k hk E p) (ofPos k hk E (q + 1)) else 0) = 0 := by
            rw [if_neg]; omega
          have hT4 : (if E = Finset.univ ∧ q = k - 1 then G k hk E (ofPos k hk E p) (ofPos k hk E 0) else 0) = 1 := by
            rw [if_pos hEk, hG_odd 0 hk, if_pos ⟨by omega, by rw [start_zero, hsu], by rw [hsu]⟩]
          rw [hT1, hT2, hT4, zero_add, zero_add]
        · have hpred_f : ¬ gaPred k hk E p q := by
            simp only [gaPred, hna, hpar, ite_true, hqp, hEk, or_self, and_false, not_false_eq_true]
          rw [if_neg hpred_f, if_neg hEk, add_zero]
          have h12 : (0 < q ∧ ofPos k hk E (q - 1) ∈ E ∧ q - 1 < p ∧
              start k hk E (q - 1) = start k hk E p ∧ (q - 1 - start k hk E p) % 2 = 0) ↔
              (q + 1 < k ∧ ofPos k hk E q ∈ E ∧ q + 1 < p ∧
              start k hk E (q + 1) = start k hk E p ∧ (q + 1 - start k hk E p) % 2 = 0) := by
            constructor
            · rintro ⟨hq0, hqmE, hqp1, hsm, hpar0⟩
              have hsp_le_qm : start k hk E p ≤ q - 1 := by
                rw [← hsm]; exact start_le k hk E (q - 1)
              have hsq : start k hk E q = start k hk E p := by
                have := (start_succ_eq k hk E (q - 1)).mpr hqmE
                rw [show q - 1 + 1 = q by omega] at this
                rw [this, hsm]
              have hqp_lt : q + 1 < p := by omega
              have hsq1 : start k hk E (q + 1) = start k hk E p := by
                have h1 := start_mono k hk E (show q ≤ q + 1 by omega)
                have h2 := start_mono k hk E (show q + 1 ≤ p by omega)
                omega
              have hqE : ofPos k hk E q ∈ E := mem_E_of_start_eq k hk E (u := q) (v := p) (by omega) hsq
              exact ⟨by omega, hqE, hqp_lt, hsq1, by omega⟩
            · rintro ⟨hq1k, hqE, hq1p, hsq1, hpar1⟩
              have hsq : start k hk E q = start k hk E p := by
                have := (start_succ_eq k hk E q).mpr hqE
                rw [← this, hsq1]
              have hsq_le : start k hk E p ≤ q := by rw [← hsq]; exact start_le k hk E q
              have hq_gt_s : start k hk E p < q := by
                by_contra hle
                have hqs : q = start k hk E p := by omega
                rw [hqs] at hpar1
                omega
              have hsm1 : start k hk E (q - 1) = start k hk E p :=
                start_eq_of_le k hk E (by omega) (by omega)
              have hqmE : ofPos k hk E (q - 1) ∈ E := mem_E_of_start_eq k hk E (u := q - 1) (v := q) (by omega) (by rw [hsm1, hsq])
              exact ⟨by omega, hqmE, by omega, hsm1, by omega⟩
          have hLHS_eq :
              (if 0 < q ∧ ofPos k hk E (q - 1) ∈ E then G k hk E (ofPos k hk E p) (ofPos k hk E (q - 1)) else 0) +
              (if q + 1 < k ∧ ofPos k hk E q ∈ E then G k hk E (ofPos k hk E p) (ofPos k hk E (q + 1)) else 0) =
              (if 0 < q ∧ ofPos k hk E (q - 1) ∈ E ∧ q - 1 < p ∧
                  start k hk E (q - 1) = start k hk E p ∧ (q - 1 - start k hk E p) % 2 = 0 then 1 else 0) +
              (if q + 1 < k ∧ ofPos k hk E q ∈ E ∧ q + 1 < p ∧
                  start k hk E (q + 1) = start k hk E p ∧ (q + 1 - start k hk E p) % 2 = 0 then 1 else 0) := by
            congr 1
            · by_cases h0 : 0 < q ∧ ofPos k hk E (q - 1) ∈ E
              · rw [if_pos h0, hG_odd (q - 1) (by omega)]; simp [h0]
              · rw [if_neg h0, if_neg]; intro h; exact h0 ⟨h.1, h.2.1⟩
            · by_cases h0 : q + 1 < k ∧ ofPos k hk E q ∈ E
              · rw [if_pos h0, hG_odd (q + 1) h0.1]; simp [h0]
              · rw [if_neg h0, if_neg]; intro h; exact h0 ⟨h.1, h.2.1⟩
          rw [hLHS_eq]
          exact z2_ite_add_eq_zero h12
  · have h1 : (if 0 < q ∧ ofPos k hk E (q - 1) ∈ E then G k hk E (ofPos k hk E p) (ofPos k hk E (q - 1)) else 0) = 0 := by
      split_ifs
      · exact G_eq_zero_of_not_active k hk E hp (by omega) hna
      · rfl
    have h2 : (if q + 1 < k ∧ ofPos k hk E q ∈ E then G k hk E (ofPos k hk E p) (ofPos k hk E (q + 1)) else 0) = 0 := by
      split_ifs with h
      · exact G_eq_zero_of_not_active k hk E hp h.1 hna
      · rfl
    have h3 : (if E = Finset.univ ∧ q = 0 then G k hk E (ofPos k hk E p) (ofPos k hk E (k - 1)) else 0) = 0 := by
      split_ifs
      · exact G_eq_zero_of_not_active k hk E hp (by omega) hna
      · rfl
    have h4 : (if E = Finset.univ ∧ q = k - 1 then G k hk E (ofPos k hk E p) (ofPos k hk E 0) else 0) = 0 := by
      split_ifs
      · exact G_eq_zero_of_not_active k hk E hp hk hna
      · rfl
    rw [h1, h2, h3, h4, if_neg (fun h => hna h.1)]
    simp

lemma GA_eq_single_of_active (hk3 : 3 ≤ k) {p q : ℕ} (hp : p < k) (hq : q < k)
    (hact : active k hk E q) :
    (G k hk E * A k hk E) (ofPos k hk E p) (ofPos k hk E q) = if p = q then 1 else 0 := by
  rw [GA_ofPos_eq k hk E hk3 hp hq]
  by_cases hpq : p = q
  · subst hpq
    have hgp : gaPred k hk E p p := by
      refine ⟨hact, ?_⟩
      split_ifs <;> exact Or.inl rfl
    rw [if_pos rfl, if_pos hgp]
  · have hngp : ¬ gaPred k hk E p q := by
      rintro ⟨_, hcond⟩
      have hqlim : q < lim k E := hact.1
      split_ifs at hcond with hpar
      · rcases hcond with rfl | ⟨hE, rfl⟩
        · exact hpq rfl
        · unfold lim at hqlim
          rw [if_pos hE] at hqlim
          split_ifs at hqlim <;> omega
      · rcases hcond with rfl | ⟨_, hnq, _⟩
        · exact hpq rfl
        · exact hnq hact
    rw [if_neg hpq, if_neg hngp]

end ClassicalSec
lemma AGA_ofPos (hk3 : 3 ≤ k) {p q : ℕ} (hp : p < k) (hq : q < k) :
    (A k hk E * (G k hk E * A k hk E)) (ofPos k hk E p) (ofPos k hk E q) =
      A k hk E (ofPos k hk E p) (ofPos k hk E q) := by
  classical
  change (∑ r : Fin k, A k hk E (ofPos k hk E p) r * (G k hk E * A k hk E) r (ofPos k hk E q)) = _
  by_cases hact : active k hk E q
  · have hsub : ∀ r : Fin k, A k hk E (ofPos k hk E p) r * (G k hk E * A k hk E) r (ofPos k hk E q) =
        if r = ofPos k hk E q then A k hk E (ofPos k hk E p) r else 0 := by
      intro r
      have hGA := GA_eq_single_of_active k hk E hk3 (pos_lt k hk E r) hq hact
      rw [ofPos_pos] at hGA
      rw [hGA]
      by_cases hpr : pos k hk E r = q
      · have hr_eq : r = ofPos k hk E q := by rw [← ofPos_pos k hk E r, hpr]
        subst hr_eq
        simp [pos_ofPos k hk E hq]
      · have hr_ne : r ≠ ofPos k hk E q := fun heq => hpr (by rw [heq, pos_ofPos k hk E hq])
        rw [if_neg hpr, if_neg hr_ne, mul_zero]
    simp_rw [hsub]
    simp
  · have hcomm : (∑ r : Fin k, A k hk E (ofPos k hk E p) r * (G k hk E * A k hk E) r (ofPos k hk E q)) =
        ∑ r : Fin k, (G k hk E * A k hk E) r (ofPos k hk E q) * A k hk E r (ofPos k hk E p) := by
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [mul_comm, show A k hk E (ofPos k hk E p) r = A k hk E r (ofPos k hk E p) by
        rw [← Matrix.transpose_apply (A k hk E), symm_A_loc k hk E]]
    rw [hcomm, sum_A_mul k hk E hk3 (fun r => (G k hk E * A k hk E) r (ofPos k hk E q)) hp,
      A_ofPos k hk E hk3 hp hq]
    have hlimk : lim k E ≤ k := lim_le k E
    by_cases hE : E = Finset.univ
    · have hst : ∀ u, start k hk E u = 0 := start_univ k hk E hE
      have hlim_val : lim k E = k - (if k % 2 = 0 then 2 else 1) := by simp [lim, hE]
      have hact_univ : ∀ r, active k hk E r ↔ r < lim k E := by
        intro r; simp only [active, hst, Nat.sub_zero]
        constructor
        · rintro ⟨hr, _⟩; exact hr
        · intro hr
          refine ⟨hr, ?_⟩
          rcases Nat.mod_two_eq_zero_or_one r with h0 | h1
          · right; refine ⟨?_, trivial⟩
            by_cases hk2 : k % 2 = 0 <;> simp [hlim_val, hk2] at hr ⊢ <;> omega
          · exact Or.inl h1
      have hqlim : lim k E ≤ q := by by_contra hlt; exact hact ((hact_univ q).mpr (by omega))
      have hga_univ : ∀ r < k, (G k hk E * A k hk E) (ofPos k hk E r) (ofPos k hk E q) =
          if r < lim k E ∧ (r % 2 = 1 ∧ q = k - 1 ∨ r % 2 = 0 ∧ q = lim k E) then 1 else 0 := by
        intro r hr
        rw [GA_ofPos_eq k hk E hk3 hr hq]
        by_cases hrl : r < lim k E
        · have hr_act : active k hk E r := (hact_univ r).mpr hrl
          have hne_rq : r ≠ q := fun heq => hact (heq ▸ hr_act)
          rcases Nat.mod_two_eq_zero_or_one r with h0 | h1
          · have hgp : gaPred k hk E r q ↔ q = lim k E := by
              have hne1 : (r - start k hk E r) % 2 ≠ 1 := by rw [hst]; omega
              have hqle : q ≤ lim k E ↔ q = lim k E := by omega
              have hr_act_u : active k hk Finset.univ r := hE ▸ hr_act
              have hact_u : ¬ active k hk Finset.univ q := hE ▸ hact
              have hst_u : ∀ u, start k hk Finset.univ u = 0 := hE ▸ hst
              have hne1_u : (r - start k hk Finset.univ r) % 2 ≠ 1 := by rw [hst_u]; omega
              have hqle_u : q ≤ lim k Finset.univ ↔ q = lim k Finset.univ := hE ▸ hqle
              rw [hE]
              dsimp only [gaPred]
              rw [if_neg hne1_u]
              simp only [hr_act_u, true_and, hst_u, hact_u, not_false_eq_true, hqle_u, and_true]
              exact or_iff_right hne_rq.symm
            by_cases hql : q = lim k E
            · rw [if_pos (hgp.mpr hql), if_pos ⟨hrl, Or.inr ⟨h0, hql⟩⟩]
            · rw [if_neg (fun h => hql (hgp.mp h)), if_neg]
              rintro ⟨_, ⟨h1', _⟩ | ⟨_, h2'⟩⟩
              · omega
              · exact hql h2'
          · have hgp : gaPred k hk E r q ↔ q = k - 1 := by
              have hr_act_u : active k hk Finset.univ r := hE ▸ hr_act
              have hst_u : ∀ u, start k hk Finset.univ u = 0 := hE ▸ hst
              have hpar1_u : (r - start k hk Finset.univ r) % 2 = 1 := by rw [hst_u]; omega
              rw [hE]
              dsimp only [gaPred]
              rw [if_pos hpar1_u]
              simp only [hr_act_u, true_and]
              exact or_iff_right hne_rq.symm
            by_cases hqk1 : q = k - 1
            · rw [if_pos (hgp.mpr hqk1), if_pos ⟨hrl, Or.inl ⟨h1, hqk1⟩⟩]
            · rw [if_neg (fun h => hqk1 (hgp.mp h)), if_neg]
              rintro ⟨_, ⟨_, h1'⟩ | ⟨h2', _⟩⟩
              · exact hqk1 h1'
              · omega
        · rw [if_neg (fun h => hrl ((hact_univ r).mp h.1)), if_neg (fun h => hrl h.1)]
      have hT1 : (if 0 < p ∧ ofPos k hk E (p - 1) ∈ E then (G k hk E * A k hk E) (ofPos k hk E (p - 1)) (ofPos k hk E q) else 0) =
          if 0 < p ∧ p - 1 < lim k E ∧ ((p - 1) % 2 = 1 ∧ q = k - 1 ∨ (p - 1) % 2 = 0 ∧ q = lim k E) then 1 else 0 := by
        by_cases h1 : 0 < p ∧ ofPos k hk E (p - 1) ∈ E
        · rw [if_pos h1, hga_univ (p - 1) (by omega)]
          simp [h1.1]
        · rw [if_neg h1, if_neg]; intro h2; apply h1; exact ⟨h2.1, by rw [hE]; exact Finset.mem_univ _⟩
      have hT2 : (if p + 1 < k ∧ ofPos k hk E p ∈ E then (G k hk E * A k hk E) (ofPos k hk E (p + 1)) (ofPos k hk E q) else 0) =
          if p + 1 < lim k E ∧ ((p + 1) % 2 = 1 ∧ q = k - 1 ∨ (p + 1) % 2 = 0 ∧ q = lim k E) then 1 else 0 := by
        by_cases h1 : p + 1 < k ∧ ofPos k hk E p ∈ E
        · rw [if_pos h1, hga_univ (p + 1) h1.1]
        · rw [if_neg h1, if_neg]; intro h2; apply h1; exact ⟨by omega, by rw [hE]; exact Finset.mem_univ _⟩
      have hT3 : (if E = Finset.univ ∧ p = 0 then (G k hk E * A k hk E) (ofPos k hk E (k - 1)) (ofPos k hk E q) else 0) = 0 := by
        split_ifs with h
        · rw [hga_univ (k - 1) (by omega), if_neg]
          rintro ⟨hlt, _⟩
          by_cases hk2 : k % 2 = 0 <;> simp [hlim_val, hk2] at hlt <;> omega
        · rfl
      have hT4 : (if E = Finset.univ ∧ p = k - 1 then (G k hk E * A k hk E) (ofPos k hk E 0) (ofPos k hk E q) else 0) =
          if p = k - 1 ∧ q = lim k E then 1 else 0 := by
        by_cases h1 : E = Finset.univ ∧ p = k - 1
        · rw [if_pos h1, hga_univ 0 hk]
          by_cases hql : q = lim k E
          · rw [if_pos ⟨by by_cases hk2 : k % 2 = 0 <;> simp [hlim_val, hk2] <;> omega, Or.inr ⟨by simp, hql⟩⟩,
              if_pos ⟨h1.2, hql⟩]
          · rw [if_neg, if_neg]
            · intro hm; exact hql hm.2
            · rintro ⟨_, ⟨h0, _⟩ | ⟨_, hm⟩⟩
              · omega
              · exact hql hm
        · rw [if_neg h1, if_neg]; intro hm; exact h1 ⟨hE, hm.1⟩
      rw [hT1, hT2, hT3, hT4, add_zero]
      simp only [hE, Finset.mem_univ, and_true, true_and]
      have hlim_univ : lim k Finset.univ = k - (if k % 2 = 0 then 2 else 1) := by simp [lim]
      by_cases hk2 : k % 2 = 0
      · have hlim2 : lim k E = k - 2 := by simp [hlim_val, hk2]
        have hlim2' : lim k Finset.univ = k - 2 := by simp [hlim_univ, hk2]
        rw [hlim2']
        have hq2 : q = k - 2 ∨ q = k - 1 := by omega
        rcases hq2 with rfl | rfl
        · have hk4 : 4 ≤ k := by omega
          have h1 : (if 0 < p ∧ p - 1 < k - 2 ∧ ((p - 1) % 2 = 1 ∧ k - 2 = k - 1 ∨ (p - 1) % 2 = 0 ∧ k - 2 = k - 2) then (1 : ZMod 2) else 0) =
              if 0 < p ∧ p - 1 < k - 2 ∧ (p - 1) % 2 = 0 then 1 else 0 := by
            congr 1; ext; constructor
            · rintro ⟨a, b, ⟨_, h⟩ | ⟨c, _⟩⟩
              · omega
              · exact ⟨a, b, c⟩
            · rintro ⟨a, b, c⟩; exact ⟨a, b, Or.inr ⟨c, rfl⟩⟩
          have h2 : (if p + 1 < k - 2 ∧ ((p + 1) % 2 = 1 ∧ k - 2 = k - 1 ∨ (p + 1) % 2 = 0 ∧ k - 2 = k - 2) then (1 : ZMod 2) else 0) =
              if p + 1 < k - 2 ∧ (p + 1) % 2 = 0 then 1 else 0 := by
            congr 1; ext; constructor
            · rintro ⟨a, ⟨_, h⟩ | ⟨c, _⟩⟩
              · omega
              · exact ⟨a, c⟩
            · rintro ⟨a, c⟩; exact ⟨a, Or.inr ⟨c, rfl⟩⟩
          rw [h1, h2]
          have hc1 : (if p = k - 1 ∧ k - 2 = k - 2 then (1 : ZMod 2) else 0) = if p = k - 1 then 1 else 0 := by
            simp
          have hc2 : (if p = k - 1 ∧ k - 2 = 0 then (1 : ZMod 2) else 0) = 0 := if_neg (by omega)
          have hc3 : (if k - 2 = k - 1 ∧ p = 0 then (1 : ZMod 2) else 0) = 0 := if_neg (by omega)
          have hc4 : (if k - 2 + 1 = p then (1 : ZMod 2) else 0) = if p = k - 1 then 1 else 0 := by
            congr 1; ext; omega
          rw [hc1, hc2, hc3, hc4, add_zero, add_zero]
          have hl_eq :
              (if 0 < p ∧ p - 1 < k - 2 ∧ (p - 1) % 2 = 0 then (1 : ZMod 2) else 0) +
              (if p + 1 < k - 2 ∧ (p + 1) % 2 = 0 then 1 else 0) =
              if p + 1 = k - 2 then 1 else 0 := by
            by_cases hp0 : p = 0
            · subst hp0
              rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), zero_add]
            · by_cases hpk3 : p = k - 3
              · subst hpk3
                rw [if_pos ⟨by omega, by omega, by omega⟩, if_neg (by omega), if_pos (by omega), add_zero]
              · by_cases hge : k - 2 ≤ p
                · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), zero_add]
                · have hp1ne : p + 1 ≠ k - 2 := by omega
                  have hp0' : 0 < p := by omega
                  have hltm : p - 1 < k - 2 := by omega
                  have hltp : p + 1 < k - 2 := by omega
                  rw [if_neg hp1ne]
                  exact z2_ite_add_eq_zero ⟨fun ⟨_, _, hc⟩ => ⟨hltp, by omega⟩, fun ⟨_, hc⟩ => ⟨hp0', hltm, by omega⟩⟩
          rw [hl_eq]
        · have hk4 : 4 ≤ k := by omega
          have h1 : (if 0 < p ∧ p - 1 < k - 2 ∧ ((p - 1) % 2 = 1 ∧ k - 1 = k - 1 ∨ (p - 1) % 2 = 0 ∧ k - 1 = k - 2) then (1 : ZMod 2) else 0) =
              if 0 < p ∧ p - 1 < k - 2 ∧ (p - 1) % 2 = 1 then 1 else 0 := by
            congr 1; ext; constructor
            · rintro ⟨a, b, ⟨c, _⟩ | ⟨_, h⟩⟩
              · exact ⟨a, b, c⟩
              · omega
            · rintro ⟨a, b, c⟩; exact ⟨a, b, Or.inl ⟨c, rfl⟩⟩
          have h2 : (if p + 1 < k - 2 ∧ ((p + 1) % 2 = 1 ∧ k - 1 = k - 1 ∨ (p + 1) % 2 = 0 ∧ k - 1 = k - 2) then (1 : ZMod 2) else 0) =
              if p + 1 < k - 2 ∧ (p + 1) % 2 = 1 then 1 else 0 := by
            congr 1; ext; constructor
            · rintro ⟨a, ⟨c, _⟩ | ⟨_, h⟩⟩
              · exact ⟨a, c⟩
              · omega
            · rintro ⟨a, c⟩; exact ⟨a, Or.inl ⟨c, rfl⟩⟩
          have h3 : (if p = k - 1 ∧ k - 1 = k - 2 then (1 : ZMod 2) else 0) = 0 := if_neg (by omega)
          have hr2 : (if k - 1 + 1 = p then (1 : ZMod 2) else 0) = 0 := if_neg (by omega)
          have hr3 : (if p = k - 1 ∧ k - 1 = 0 then (1 : ZMod 2) else 0) = 0 := if_neg (by omega)
          have hr4 : (if k - 1 = k - 1 ∧ p = 0 then (1 : ZMod 2) else 0) = if p = 0 then 1 else 0 := by simp [true_and]
          rw [h1, h2, h3, add_zero, hr2, hr3, add_zero, add_zero, hr4]
          by_cases hp0 : p = 0
          · subst hp0
            rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩, if_neg (by omega), if_pos rfl, zero_add]
          · by_cases hpk2 : p = k - 2
            · subst hpk2
              rw [if_pos ⟨by omega, by omega, by omega⟩, if_neg (by omega), if_pos (by omega), if_neg (by omega), add_zero]
            · by_cases hge : p = k - 1 ∨ p = k - 3
              · rw [if_neg (by rcases hge with rfl | rfl <;> omega), if_neg (by rcases hge with rfl | rfl <;> omega),
                  if_neg (by rcases hge with rfl | rfl <;> omega), if_neg hp0, add_zero]
              · have hp1ne : p + 1 ≠ k - 1 := by omega
                have hp0' : 0 < p := by omega
                have hltm : p - 1 < k - 2 := by omega
                have hltp : p + 1 < k - 2 := by omega
                rw [if_neg hp1ne, if_neg hp0, add_zero]
                exact z2_ite_add_eq_zero ⟨fun ⟨_, _, hc⟩ => ⟨hltp, by omega⟩, fun ⟨_, hc⟩ => ⟨hp0', hltm, by omega⟩⟩
      · have hlim1 : lim k E = k - 1 := by simp [hlim_val, hk2]
        have hlim1' : lim k Finset.univ = k - 1 := by simp [hlim_univ, hk2]
        rw [hlim1']
        have hqk1 : q = k - 1 := by omega
        subst hqk1
        have h1 : (if 0 < p ∧ p - 1 < k - 1 ∧ ((p - 1) % 2 = 1 ∧ k - 1 = k - 1 ∨ (p - 1) % 2 = 0 ∧ k - 1 = k - 1) then (1 : ZMod 2) else 0) =
            if 0 < p ∧ p - 1 < k - 1 then 1 else 0 := by
          congr 1; ext; constructor
          · rintro ⟨a, b, _⟩; exact ⟨a, b⟩
          · rintro ⟨a, b⟩
            rcases Nat.mod_two_eq_zero_or_one (p - 1) with ho | he
            · exact ⟨a, b, Or.inr ⟨ho, rfl⟩⟩
            · exact ⟨a, b, Or.inl ⟨he, rfl⟩⟩
        have h2 : (if p + 1 < k - 1 ∧ ((p + 1) % 2 = 1 ∧ k - 1 = k - 1 ∨ (p + 1) % 2 = 0 ∧ k - 1 = k - 1) then (1 : ZMod 2) else 0) =
            if p + 1 < k - 1 then 1 else 0 := by
          congr 1; ext; constructor
          · rintro ⟨a, _⟩; exact a
          · intro a
            rcases Nat.mod_two_eq_zero_or_one (p + 1) with ho | he
            · exact ⟨a, Or.inr ⟨ho, rfl⟩⟩
            · exact ⟨a, Or.inl ⟨he, rfl⟩⟩
        have hl3 : (if p = k - 1 ∧ k - 1 = k - 1 then (1 : ZMod 2) else 0) = if p = k - 1 then 1 else 0 := by simp [and_true]
        have hr2 : (if k - 1 + 1 = p then (1 : ZMod 2) else 0) = 0 := if_neg (by omega)
        have hr3 : (if p = k - 1 ∧ k - 1 = 0 then (1 : ZMod 2) else 0) = 0 := if_neg (by omega)
        have hr4 : (if k - 1 = k - 1 ∧ p = 0 then (1 : ZMod 2) else 0) = if p = 0 then 1 else 0 := by simp [true_and]
        rw [h1, h2, hl3, hr2, hr3, add_zero, add_zero, hr4]
        by_cases hp0 : p = 0
        · subst hp0
          rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl, zero_add, add_zero]
        · by_cases hpk1 : p = k - 1
          · subst hpk1
            rw [if_pos ⟨by omega, by omega⟩, if_neg (by omega), if_pos rfl, if_neg (by omega), if_neg (by omega), add_zero, zero_add, z2_11]
          · by_cases hpk2 : p = k - 2
            · subst hpk2
              rw [if_pos ⟨by omega, by omega⟩, if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega), add_zero, add_zero]
            · rw [if_pos ⟨by omega, by omega⟩, if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), add_zero, add_zero, z2_11]
    · -- E != univ -> lim = k
      have hlim_k : lim k E = k := by simp [lim, hE]
      have hq_even : (q - start k hk E q) % 2 = 0 := by
        by_contra h1; apply hact; exact ⟨by omega, Or.inl (by omega)⟩
      have hq_notE : ofPos k hk E q ∉ E := by
        by_cases hqk1 : q = k - 1
        · rw [hqk1]; exact ofPos_tail_not_mem k hk E hE
        · intro hqE; apply hact; refine ⟨by omega, Or.inr ⟨by omega, (start_succ_eq k hk E q).mpr hqE⟩⟩
      have hga_nonu : ∀ r < k, (G k hk E * A k hk E) (ofPos k hk E r) (ofPos k hk E q) =
          if r < q ∧ start k hk E r = start k hk E q ∧ (r - start k hk E q) % 2 = 0 then 1 else 0 := by
        intro r hr
        rw [GA_ofPos_eq k hk E hk3 hr hq]
        by_cases hc : r < q ∧ start k hk E r = start k hk E q ∧ (r - start k hk E q) % 2 = 0
        · rw [if_pos hc, if_pos]
          have hr1_eq : start k hk E (r + 1) = start k hk E r := by
            have h1 := start_mono k hk E (show r ≤ r + 1 by omega)
            have h2 := start_mono k hk E (show r + 1 ≤ q by omega)
            omega
          have hr_act : active k hk E r := ⟨by omega, Or.inr ⟨by omega, hr1_eq⟩⟩
          refine ⟨hr_act, ?_⟩
          rw [if_neg (by rw [hc.2.1]; omega)]
          exact Or.inr ⟨hc.2.1.symm, hact, by omega⟩
        · rw [if_neg hc, if_neg]
          rintro ⟨hr_act, hcond⟩
          split_ifs at hcond with hpar
          · rcases hcond with rfl | ⟨hE', _⟩
            · exact hact hr_act
            · exact hE hE'
          · rcases hcond with rfl | ⟨hsq, _, _⟩
            · exact hact hr_act
            · have hr_lt_q : r < q := by
                by_contra hge
                have hqr : q < r := by
                  by_contra hle
                  have hqp' : q = r := by omega
                  subst hqp'
                  exact hact hr_act
                have hst1 : start k hk E (q + 1) = start k hk E q := by
                  have h1 := start_mono k hk E (show q ≤ q + 1 by omega)
                  have h2 := start_mono k hk E (show q + 1 ≤ r by omega)
                  omega
                exact hq_notE ((start_succ_eq k hk E q).mp hst1)
              exact hc ⟨hr_lt_q, hsq.symm, by rw [← hsq] at hpar; have := start_le k hk E r; omega⟩
      have hT3 : (if E = Finset.univ ∧ p = 0 then (G k hk E * A k hk E) (ofPos k hk E (k - 1)) (ofPos k hk E q) else 0) = 0 := by
        rw [if_neg]; intro h; exact hE h.1
      have hT4 : (if E = Finset.univ ∧ p = k - 1 then (G k hk E * A k hk E) (ofPos k hk E 0) (ofPos k hk E q) else 0) = 0 := by
        rw [if_neg]; intro h; exact hE h.1
      rw [hT3, hT4, add_zero, add_zero]
      simp only [hE, false_and, if_neg, not_false_eq_true, add_zero]
      have hRHS_eq : (if p + 1 = q ∧ ofPos k hk E p ∈ E then (1 : ZMod 2) else 0) +
          (if q + 1 = p ∧ ofPos k hk E q ∈ E then 1 else 0) =
          if p + 1 = q ∧ ofPos k hk E p ∈ E then 1 else 0 := by
        have : ¬ (q + 1 = p ∧ ofPos k hk E q ∈ E) := fun h => hq_notE h.2
        rw [if_neg this, add_zero]
      rw [hRHS_eq]
      by_cases hlt_s : p + 1 = q ∧ ofPos k hk E p ∈ E
      · rw [if_pos hlt_s]
        have hT2 : (if p + 1 < k ∧ ofPos k hk E p ∈ E then (G k hk E * A k hk E) (ofPos k hk E (p + 1)) (ofPos k hk E q) else 0) = 0 := by
          rw [if_pos ⟨by omega, hlt_s.2⟩, hga_nonu (p + 1) (by omega), if_neg]; omega
        have hT1 : (if 0 < p ∧ ofPos k hk E (p - 1) ∈ E then (G k hk E * A k hk E) (ofPos k hk E (p - 1)) (ofPos k hk E q) else 0) = 1 := by
          have hs_eq : start k hk E q = start k hk E p := by rw [← hlt_s.1, (start_succ_eq k hk E p).mpr hlt_s.2]
          have hsq_le : start k hk E q ≤ p := by rw [hs_eq]; exact start_le k hk E p
          have hsq_lt : start k hk E q < p := by have := hq_even; omega
          have hsm1 : start k hk E (p - 1) = start k hk E q := start_eq_of_le k hk E (by omega) (by rw [hs_eq]; omega)
          have hpmE : ofPos k hk E (p - 1) ∈ E := mem_E_of_start_eq k hk E (u := p - 1) (v := q) (by omega) hsm1
          rw [if_pos ⟨by omega, hpmE⟩, hga_nonu (p - 1) (by omega), if_pos ⟨by omega, hsm1, by omega⟩]
        rw [hT1, hT2, add_zero]
      · rw [if_neg hlt_s]
        have hT1_eq : (if 0 < p ∧ ofPos k hk E (p - 1) ∈ E then (G k hk E * A k hk E) (ofPos k hk E (p - 1)) (ofPos k hk E q) else 0) =
            if 0 < p ∧ ofPos k hk E (p - 1) ∈ E ∧ p - 1 < q ∧ start k hk E (p - 1) = start k hk E q ∧ (p - 1 - start k hk E q) % 2 = 0 then 1 else 0 := by
          by_cases h1 : 0 < p ∧ ofPos k hk E (p - 1) ∈ E
          · rw [if_pos h1, hga_nonu (p - 1) (by omega)]; simp [h1]
          · rw [if_neg h1, if_neg]; intro h; exact h1 ⟨h.1, h.2.1⟩
        have hT2_eq : (if p + 1 < k ∧ ofPos k hk E p ∈ E then (G k hk E * A k hk E) (ofPos k hk E (p + 1)) (ofPos k hk E q) else 0) =
            if p + 1 < k ∧ ofPos k hk E p ∈ E ∧ p + 1 < q ∧ start k hk E (p + 1) = start k hk E q ∧ (p + 1 - start k hk E q) % 2 = 0 then 1 else 0 := by
          by_cases h1 : p + 1 < k ∧ ofPos k hk E p ∈ E
          · rw [if_pos h1, hga_nonu (p + 1) h1.1]; simp [h1]
          · rw [if_neg h1, if_neg]; intro h; exact h1 ⟨h.1, h.2.1⟩
        rw [hT1_eq, hT2_eq]
        refine z2_ite_add_eq_zero ?_
        constructor
        · rintro ⟨hp0, hpmE, hpmq, hsm, hparm⟩
          have hsp1_le : start k hk E (p - 1) ≤ p - 1 := start_le k hk E (p - 1)
          have hsp : start k hk E p = start k hk E q := by
            have := (start_succ_eq k hk E (p - 1)).mpr hpmE
            rw [show p - 1 + 1 = p by omega] at this
            rw [this, hsm]
          have hp_lt_q : p < q := by omega
          have hpE : ofPos k hk E p ∈ E := mem_E_of_start_eq k hk E (u := p) (v := q) hp_lt_q hsp
          have hp1_lt_q : p + 1 < q := by
            by_contra hge
            have hpq1 : p + 1 = q := by omega
            exact hlt_s ⟨hpq1, hpE⟩
          have hs1 : start k hk E (p + 1) = start k hk E q := by rw [(start_succ_eq k hk E p).mpr hpE, hsp]
          exact ⟨by omega, hpE, hp1_lt_q, hs1, by omega⟩
        · rintro ⟨hp1k, hpE, hp1q, hs1, hpar1⟩
          have hsp : start k hk E p = start k hk E q := by rw [← (start_succ_eq k hk E p).mpr hpE, hs1]
          have hsq_le_p : start k hk E q ≤ p := by rw [← hsp]; exact start_le k hk E p
          have hsq_lt_p : start k hk E q < p :=
            lt_of_le_of_ne hsq_le_p (fun hps => by rw [← hps] at hpar1; omega)
          have hsm : start k hk E (p - 1) = start k hk E q :=
            start_eq_of_le k hk E (by omega) (by rw [← hsp]; have := start_le k hk E p; omega)
          have hpmE : ofPos k hk E (p - 1) ∈ E :=
            mem_E_of_start_eq k hk E (u := p - 1) (v := p) (by omega) (by rw [hsm, hsp])
          exact ⟨by omega, hpmE, by omega, hsm, by omega⟩

lemma AGA_eq_A (hk3 : 3 ≤ k) : A k hk E * G k hk E * A k hk E = A k hk E := by
  rw [Matrix.mul_assoc]
  ext i j
  rw [← ofPos_pos k hk E i, ← ofPos_pos k hk E j]
  exact AGA_ofPos k hk E hk3 (pos_lt k hk E i) (pos_lt k hk E j)

lemma nxt_injective : Function.Injective (nxt k hk) := by
  intro i j hij
  have hv : (i.val + 1) % k = (j.val + 1) % k := congrArg Fin.val hij
  apply Fin.ext
  have hi := i.isLt; have hj := j.isLt
  by_cases hi1 : i.val + 1 < k <;> by_cases hj1 : j.val + 1 < k
  · rw [Nat.mod_eq_of_lt hi1, Nat.mod_eq_of_lt hj1] at hv; omega
  · rw [Nat.mod_eq_of_lt hi1, show j.val + 1 = k by omega, Nat.mod_self] at hv; omega
  · rw [show i.val + 1 = k by omega, Nat.mod_self, Nat.mod_eq_of_lt hj1] at hv; omega
  · omega

lemma rank_eq_2b (hk3 : 3 ≤ k) :
    let m := (E.powerset.filter (fun M => ∀ i ∈ M, nxt k hk i ∉ M)).sup Finset.card
    let b := if E = Finset.univ ∧ k % 2 = 0 then m - 1 else m
    (A k hk E).rank = 2 * b := by
  classical
  intro m b
  let R_act : Finset (Fin k) := Finset.univ.filter fun i => active k hk E (pos k hk E i)
  have hG_col_zero : ∀ i : Fin k, i ∉ R_act → (G k hk E).col i = 0 := by
    intro i hi
    have hna : ¬ active k hk E (pos k hk E i) := by simpa [R_act] using hi
    ext j
    rw [Matrix.col_apply, Pi.zero_apply, ← ofPos_pos k hk E j, ← ofPos_pos k hk E i]
    rw [show G k hk E (ofPos k hk E (pos k hk E j)) (ofPos k hk E (pos k hk E i)) =
        G k hk E (ofPos k hk E (pos k hk E i)) (ofPos k hk E (pos k hk E j)) by
      rw [← Matrix.transpose_apply (G k hk E), symm_G_loc]]
    exact G_eq_zero_of_not_active k hk E (pos_lt k hk E i) (pos_lt k hk E j) hna
  have hGrk_le : (G k hk E).rank ≤ R_act.card := by
    rw [Matrix.rank_eq_finrank_span_cols]
    have hsub : Submodule.span (ZMod 2) (Set.range (G k hk E).col) ≤
        Submodule.span (ZMod 2) (Set.range fun i : R_act => (G k hk E).col i.1) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      by_cases hi : i ∈ R_act
      · exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
      · rw [hG_col_zero i hi]
        exact Submodule.zero_mem _
    have h1 := Submodule.finrank_mono hsub
    have h2 : finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range fun i : R_act => (G k hk E).col i.1)) ≤
        Fintype.card R_act := by
      refine (finrank_span_le_card _).trans ?_
      rw [Set.toFinset_range]
      exact Finset.card_image_le.trans (by simp)
    simpa [Fintype.card_coe] using h1.trans h2
  have hArk_le : (A k hk E).rank ≤ R_act.card := by
    have hAGA := AGA_eq_A k hk E hk3
    calc (A k hk E).rank = (A k hk E * (G k hk E * A k hk E)).rank := by rw [← Matrix.mul_assoc, hAGA]
      _ ≤ (G k hk E * A k hk E).rank := Matrix.rank_mul_le_right _ _
      _ ≤ (G k hk E).rank := Matrix.rank_mul_le_left _ _
      _ ≤ R_act.card := hGrk_le
  have hle_Ark : R_act.card ≤ (A k hk E).rank := by
    let extR : (R_act → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) :=
      { toFun := fun v i => if h : i ∈ R_act then v ⟨i, h⟩ else 0
        map_add' := fun u v => by ext i; by_cases h : i ∈ R_act <;> simp [h]
        map_smul' := fun r v => by ext i; by_cases h : i ∈ R_act <;> simp [h] }
    let compL : (R_act → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) := (A k hk E).mulVecLin.comp extR
    have hinj : Function.Injective compL := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro v hv
      have hAv : A k hk E *ᵥ extR v = 0 := hv
      have hGAv : (G k hk E * A k hk E) *ᵥ extR v = 0 := by
        rw [← Matrix.mulVec_mulVec, hAv, Matrix.mulVec_zero]
      ext i
      have hi_mem : i.1 ∈ R_act := i.2
      have hact : active k hk E (pos k hk E i.1) := (Finset.mem_filter.mp hi_mem).2
      have hi0 := congrFun hGAv i.1
      rw [Pi.zero_apply, Matrix.mulVec] at hi0
      change (∑ j : Fin k, (G k hk E * A k hk E) i.1 j * extR v j) = 0 at hi0
      have hterm : ∀ j : Fin k, (G k hk E * A k hk E) i.1 j * extR v j =
          if j = i.1 then v i else 0 := by
        intro j
        by_cases hj : j ∈ R_act
        · have hjact : active k hk E (pos k hk E j) := (Finset.mem_filter.mp hj).2
          have hGAij : (G k hk E * A k hk E) i.1 j = if pos k hk E i.1 = pos k hk E j then 1 else 0 := by
            have hGA := GA_eq_single_of_active k hk E hk3 (pos_lt k hk E i.1) (pos_lt k hk E j) hjact
            rwa [ofPos_pos k hk E i.1, ofPos_pos k hk E j] at hGA
          rw [hGAij]
          by_cases hji : j = i.1
          · subst hji; simp [extR, hi_mem]
          · have hpne : pos k hk E i.1 ≠ pos k hk E j := by
              intro hpeq; apply hji; rw [← ofPos_pos k hk E i.1, ← ofPos_pos k hk E j, hpeq]
            simp [hji, hpne]
        · rw [if_neg (fun (heq : j = i.1) => hj (heq ▸ hi_mem))]
          simp [extR, hj]
      simp [hterm] at hi0
      exact hi0
    have h1 : finrank (ZMod 2) (R_act → ZMod 2) = Fintype.card R_act := Module.finrank_pi (ZMod 2)
    have h2 := LinearMap.finrank_range_of_inj hinj
    have h3 : LinearMap.range compL ≤ LinearMap.range (A k hk E).mulVecLin := by
      rintro y ⟨v, rfl⟩; exact ⟨extR v, rfl⟩
    have h4 := Submodule.finrank_mono h3
    rw [Matrix.rank] at *
    simpa [Fintype.card_coe, h1, h2] using h4
  let E_act : Finset (Fin k) := R_act.filter fun i => (pos k hk E i - start k hk E (pos k hk E i)) % 2 = 0
  let O_act : Finset (Fin k) := R_act.filter fun i => (pos k hk E i - start k hk E (pos k hk E i)) % 2 = 1
  have hEO_sum : E_act.card + O_act.card = R_act.card := by
    have hu : E_act ∪ O_act = R_act := by
      ext i
      simp only [Finset.mem_union, E_act, O_act, Finset.mem_filter]
      have hmod := Nat.mod_two_eq_zero_or_one (pos k hk E i - start k hk E (pos k hk E i))
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro hi
        rcases hmod with h0 | h1
        · exact Or.inl ⟨hi, h0⟩
        · exact Or.inr ⟨hi, h1⟩
    have hd : Disjoint E_act O_act := by
      rw [Finset.disjoint_left]; intro i h1 h2
      simp only [E_act, O_act, Finset.mem_filter] at h1 h2; omega
    rw [← Finset.card_union_of_disjoint hd, hu]
  have hmem_E : ∀ x, x ∈ E_act ↔ active k hk E (pos k hk E x) ∧ (pos k hk E x - start k hk E (pos k hk E x)) % 2 = 0 :=
    fun x => by simp [E_act, R_act]
  have hmem_O : ∀ x, x ∈ O_act ↔ active k hk E (pos k hk E x) ∧ (pos k hk E x - start k hk E (pos k hk E x)) % 2 = 1 :=
    fun x => by simp [O_act, R_act]
  have hEO_eq : E_act.card = O_act.card := by
    refine Finset.card_bij (fun i _ => nxt k hk i) ?_ ?_ ?_
    · intro i hi
      rw [hmem_E] at hi
      rw [hmem_O]
      dsimp only [active]
      rcases hi with ⟨⟨hlim, hor⟩, hpar⟩
      have hp1 : pos k hk E i + 1 < lim k E ∧ start k hk E (pos k hk E i + 1) = start k hk E (pos k hk E i) := by
        rcases hor with h1 | h2
        · omega
        · exact h2
      have hlimk := lim_le k E
      have hpos_nxt : pos k hk E (nxt k hk i) = pos k hk E i + 1 := by
        conv_lhs => rw [← ofPos_pos k hk E i, nxt_ofPos, pos_ofPos k hk E (by omega)]
      rw [hpos_nxt, hp1.2]
      have := start_le k hk E (pos k hk E i)
      exact ⟨⟨hp1.1, Or.inl (by omega)⟩, by omega⟩
    · intro i _ j _ hij; exact nxt_injective k hk hij
    · intro j hj
      rw [hmem_O] at hj
      rcases hj with ⟨⟨hjlim, _⟩, hjpar⟩
      have hlimk := lim_le k E
      have hsj := start_le k hk E (pos k hk E j)
      have hsj_lt : start k hk E (pos k hk E j) < pos k hk E j := by omega
      let i := ofPos k hk E (pos k hk E j - 1)
      have hpi : pos k hk E i = pos k hk E j - 1 := pos_ofPos k hk E (by omega)
      have hsi : start k hk E (pos k hk E i) = start k hk E (pos k hk E j) := by
        rw [hpi]; exact start_eq_of_le k hk E (by omega) (by omega)
      have hsi' : start k hk E (pos k hk E j - 1) = start k hk E (pos k hk E j) := hpi ▸ hsi
      refine ⟨i, ?_, ?_⟩
      · rw [hmem_E]
        dsimp only [active]
        rw [hpi, hsi']
        refine ⟨⟨by omega, Or.inr ⟨by omega, ?_⟩⟩, by omega⟩
        rw [show pos k hk E j - 1 + 1 = pos k hk E j by omega]
      · dsimp only [i]
        rw [nxt_ofPos, show pos k hk E j - 1 + 1 = pos k hk E j by omega, ofPos_pos]
  have hR_twice : R_act.card = 2 * E_act.card := by omega
  have hE_valid : E_act ∈ E.powerset.filter (fun M => ∀ i ∈ M, nxt k hk i ∉ M) := by
    simp only [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [hmem_E] at hi
      rcases hi with ⟨⟨hlim, hor⟩, hpar⟩
      have hp1 : pos k hk E i + 1 < lim k E ∧ start k hk E (pos k hk E i + 1) = start k hk E (pos k hk E i) := by
        rcases hor with h1 | h2
        · omega
        · exact h2
      rw [← ofPos_pos k hk E i]
      exact (start_succ_eq k hk E (pos k hk E i)).mp hp1.2
    · intro i hi hnxt
      rw [hmem_E] at hi hnxt
      dsimp only [active] at hnxt
      have hlimk := lim_le k E
      have hp1 : pos k hk E i + 1 < lim k E ∧ start k hk E (pos k hk E i + 1) = start k hk E (pos k hk E i) := by
        rcases hi.1.2 with h1 | h2
        · omega
        · exact h2
      have hpos_nxt : pos k hk E (nxt k hk i) = pos k hk E i + 1 := by
        conv_lhs => rw [← ofPos_pos k hk E i, nxt_ofPos, pos_ofPos k hk E (by omega)]
      rw [hpos_nxt, hp1.2] at hnxt
      have := start_le k hk E (pos k hk E i)
      omega
  have hm_ge : E_act.card ≤ m := Finset.le_sup (f := Finset.card) hE_valid
  have hdisj_card : ∀ M : Finset (Fin k), (∀ i ∈ M, nxt k hk i ∉ M) →
      (M ∪ M.image (nxt k hk)).card = 2 * M.card := by
    intro M hM
    have hd : Disjoint M (M.image (nxt k hk)) := by
      rw [Finset.disjoint_left]
      intro x hx hximg
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hximg
      exact hM i hi hx
    rw [Finset.card_union_of_disjoint hd, Finset.card_image_of_injective _ (nxt_injective k hk)]
    omega
  have hRb : R_act.card = 2 * b := by
    by_cases hE : E = Finset.univ
    · have hst := start_univ k hk E hE
      by_cases hk2 : k % 2 = 0
      · have hlim2 : lim k E = k - 2 := by simp [lim, hE, hk2]
        have hb_eq : b = m - 1 := by simp [b, hE, hk2]
        let M_even : Finset (Fin k) := Finset.univ.filter fun i => pos k hk E i % 2 = 0
        have hMe_valid : M_even ∈ E.powerset.filter (fun M => ∀ i ∈ M, nxt k hk i ∉ M) := by
          simp only [Finset.mem_filter, Finset.mem_powerset]
          refine ⟨fun i _ => by rw [hE]; exact Finset.mem_univ _, ?_⟩
          intro i hi hnxt
          simp only [M_even, Finset.mem_filter, Finset.mem_univ, true_and] at hi hnxt
          have hpos_nxt : pos k hk E (nxt k hk i) = (pos k hk E i + 1) % k := by
            conv_lhs => rw [← ofPos_pos k hk E i, nxt_ofPos]
            by_cases hlt : pos k hk E i + 1 < k
            · rw [pos_ofPos k hk E hlt, Nat.mod_eq_of_lt hlt]
            · have hpk : pos k hk E i + 1 = k := by have := pos_lt k hk E i; omega
              rw [hpk, show ofPos k hk E k = ofPos k hk E 0 by unfold ofPos ix; apply Fin.ext; simp,
                pos_ofPos k hk E hk, Nat.mod_self]
          rw [hpos_nxt] at hnxt
          by_cases hlt : pos k hk E i + 1 < k
          · rw [Nat.mod_eq_of_lt hlt] at hnxt; omega
          · have hpk : pos k hk E i + 1 = k := by have := pos_lt k hk E i; omega
            omega
        have hm_ge2 : M_even.card ≤ m := Finset.le_sup (f := Finset.card) hMe_valid
        have hm_le2 : m ≤ M_even.card := by
          apply Finset.sup_le
          intro M hM
          simp only [Finset.mem_filter, Finset.mem_powerset] at hM
          have hM_le : 2 * M.card ≤ k := by
            rw [← hdisj_card M hM.2]
            calc (M ∪ M.image (nxt k hk)).card ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_le_univ _
              _ = k := Fintype.card_fin k
          have hMe_full : (M_even ∪ M_even.image (nxt k hk)) = Finset.univ := by
            ext x
            simp only [Finset.mem_union, Finset.mem_image, M_even, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
            rcases Nat.mod_two_eq_zero_or_one (pos k hk E x) with hx0 | hx1
            · exact Or.inl hx0
            · right
              have hx_pos := pos_lt k hk E x
              let y := ofPos k hk E (pos k hk E x - 1)
              have hpy : pos k hk E y = pos k hk E x - 1 := pos_ofPos k hk E (by omega)
              refine ⟨y, by rw [hpy]; omega, ?_⟩
              dsimp only [y]; rw [nxt_ofPos, show pos k hk E x - 1 + 1 = pos k hk E x by omega, ofPos_pos]
          have hMe_card : 2 * M_even.card = k := by
            have hnv : ∀ i ∈ M_even, nxt k hk i ∉ M_even := (Finset.mem_filter.mp hMe_valid).2
            rw [← hdisj_card M_even hnv, hMe_full, Finset.card_univ, Fintype.card_fin]
          omega
        have hMe_eq_Eact : M_even = insert (ofPos k hk E (k - 2)) E_act := by
          ext x
          simp only [Finset.mem_insert, M_even, E_act, R_act, Finset.mem_filter, Finset.mem_univ, true_and, hst, Nat.sub_zero, active, hlim2]
          constructor
          · intro hx0
            by_cases hx2 : pos k hk E x = k - 2
            · left; rw [← hx2, ofPos_pos]
            · right
              have hxlt := pos_lt k hk E x
              have hx_lim : pos k hk E x < k - 2 := by omega
              exact ⟨⟨hx_lim, Or.inr ⟨by omega, trivial⟩⟩, hx0⟩
          · rintro (rfl | ⟨⟨_, _⟩, hx0⟩)
            · rw [pos_ofPos k hk E (by omega)]; omega
            · exact hx0
        have hnot_in : ofPos k hk E (k - 2) ∉ E_act := by
          simp only [E_act, R_act, Finset.mem_filter, Finset.mem_univ, true_and, active, hlim2]
          rw [pos_ofPos k hk E (by omega)]; omega
        have hm_eq : m = E_act.card + 1 := by
          have := Finset.card_insert_of_notMem hnot_in
          rw [← hMe_eq_Eact] at this
          omega
        rw [hb_eq, hm_eq, hR_twice]
        omega
      · have hlim1 : lim k E = k - 1 := by simp [lim, hE, hk2]
        have hb_eq : b = m := by simp [b, hE, hk2]
        have hm_le : m ≤ E_act.card := by
          apply Finset.sup_le
          intro M hM
          simp only [Finset.mem_filter, Finset.mem_powerset] at hM
          have hM_le : 2 * M.card ≤ k := by
            rw [← hdisj_card M hM.2]
            exact (Finset.card_le_univ _).trans (by simp)
          have hR_eq : R_act = Finset.univ.erase (ofPos k hk E (k - 1)) := by
            ext x
            simp only [R_act, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true, active, hlim1, hst, Nat.sub_zero]
            have hxlt := pos_lt k hk E x
            constructor
            · rintro ⟨hlt, _⟩ heq
              have := congrArg (pos k hk E) heq
              rw [pos_ofPos k hk E (by omega)] at this
              omega
            · intro hne
              have hxlt1 : pos k hk E x < k - 1 := by
                by_contra hge; apply hne; rw [← ofPos_pos k hk E x, show pos k hk E x = k - 1 by omega]
              rcases Nat.mod_two_eq_zero_or_one (pos k hk E x) with h0 | h1
              · exact ⟨hxlt1, Or.inr (by omega)⟩
              · exact ⟨hxlt1, Or.inl h1⟩
          have hR_card1 : R_act.card = k - 1 := by
            rw [hR_eq, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
          omega
        have hm_eq : m = E_act.card := le_antisymm hm_le hm_ge
        rw [hb_eq, hm_eq, hR_twice]
    · have hlim_k : lim k E = k := by simp [lim, hE]
      have hb_eq : b = m := by simp [b, hE]
      have hm_le : m ≤ E_act.card := by
        apply Finset.sup_le
        intro M hM
        simp only [Finset.mem_filter, Finset.mem_powerset] at hM
        let f : Fin k → Fin k := fun y =>
          if (pos k hk E y - start k hk E (pos k hk E y)) % 2 = 0 then nxt k hk y else y
        have hmaps : ∀ y ∈ M, f y ∈ O_act := by
          intro y hyM
          have hyE : y ∈ E := hM.1 hyM
          have hne : pos k hk E y ≠ k - 1 := by
            intro hpeq; apply ofPos_tail_not_mem k hk E hE; rw [← hpeq, ofPos_pos]; exact hyE
          have hylt := pos_lt k hk E y
          have hsy := start_le k hk E (pos k hk E y)
          by_cases hev : (pos k hk E y - start k hk E (pos k hk E y)) % 2 = 0
          · have hf : f y = nxt k hk y := if_pos hev
            rw [hf]
            have hst1 := (start_succ_eq k hk E (pos k hk E y)).mpr (by rwa [ofPos_pos])
            have hpos_nxt : pos k hk E (nxt k hk y) = pos k hk E y + 1 := by
              conv_lhs => rw [← ofPos_pos k hk E y, nxt_ofPos, pos_ofPos k hk E (by omega)]
            simp only [O_act, R_act, Finset.mem_filter, Finset.mem_univ, true_and, active, hlim_k, hpos_nxt]
            rw [hst1]
            exact ⟨⟨by omega, Or.inl (by omega)⟩, by omega⟩
          · have hf : f y = y := if_neg hev
            rw [hf]
            simp only [O_act, R_act, Finset.mem_filter, Finset.mem_univ, true_and, active, hlim_k]
            exact ⟨⟨hylt, Or.inl (by omega)⟩, by omega⟩
        have hinj_on : Set.InjOn f M := by
          intro y₁ hy₁ y₂ hy₂ hfeq
          dsimp only [f] at hfeq
          split_ifs at hfeq with h1 h2
          · exact nxt_injective k hk hfeq
          · exfalso; rw [← hfeq] at hy₂; exact hM.2 y₁ hy₁ hy₂
          · exfalso; rw [hfeq] at hy₁; exact hM.2 y₂ hy₂ hy₁
          · exact hfeq
        have hM_le_O : M.card ≤ O_act.card := by
          rw [← Finset.card_image_of_injOn hinj_on]
          refine Finset.card_le_card ?_
          intro z hz
          obtain ⟨y, hyM, rfl⟩ := Finset.mem_image.mp hz
          exact hmaps y hyM
        omega
      have hm_eq : m = E_act.card := le_antisymm hm_le hm_ge
      rw [hb_eq, hm_eq, hR_twice]
  rw [← hRb]
  exact le_antisymm hArk_le hle_Ark

end All

end LargeK
end PEqualNP.Outside.L_lib_1041

open PEqualNP.Outside.L_lib_1041 in
theorem PEqualNP.Outside.L_lib_1041 :
    ∀ (k : Nat) (hk : 0 < k),
      let F := ZMod 2
      let W := Fin k → F
      let ix := fun n : Nat => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
      ∀ E : Finset (Fin k),
        let nxt := fun i : Fin k => ix (i.val+1)
        let miss := Finset.univ \ E
        let base := if h : miss.Nonempty then (nxt (miss.min' h)).val else 0
        let pos := fun i : Fin k => (i.val+k-base) % k
        let start := fun u : Nat => ((Finset.range (u+1)).filter (fun j =>
          j = 0 ∨ ix (base+(j-1)) ∉ E)).sup id
        let lim := if E = Finset.univ then k - (if k % 2 = 0 then 2 else 1) else k
        let A : Matrix (Fin k) (Fin k) F := fun i j =>
          (if i ∈ E ∧ nxt i = j then 1 else 0) + (if j ∈ E ∧ nxt j = i then 1 else 0)
        let G : Matrix (Fin k) (Fin k) F := fun i j =>
          let u := min (pos i) (pos j)
          let v := max (pos i) (pos j)
          if v < lim ∧ start u = start v ∧ (u-start u)%2 = 0 ∧ (v-start v)%2 = 1 then 1 else 0
        let m := (E.powerset.filter (fun M => ∀ i ∈ M, nxt i ∉ M)).sup Finset.card
        let b := if E = Finset.univ ∧ k % 2 = 0 then m-1 else m
        A*G*A = A ∧ A.rank = 2*b ∧
          ∀ (n : Nat) (P : Matrix (Fin k) (Fin n) F),
            let T := (Finset.univ : Finset W).filter (fun c =>
              P.transpose.mulVec c = 0 ∧ A.mulVec (G.mulVec c) = c)
            let R := T.filter (fun c => ∀ z ∈ T, dotProduct (G.mulVec c) z = 0)
            2^(P.transpose*A*P).rank * T.card * R.card = 2^(2*b) := by
  intro k hk F W ix E nxt miss base pos start lim A G m b
  have hSym : A.transpose = A := symm_A k hk E
  have hAGA_rk : A * G * A = A ∧ A.rank = 2 * b := by
    by_cases hk2 : k ≤ 2
    · exact small_k k hk hk2 E
    · have hk3 : 3 ≤ k := by omega
      exact ⟨AGA_eq_A k hk E hk3, rank_eq_2b k hk E hk3⟩
  refine ⟨hAGA_rk.1, hAGA_rk.2, fun n P => ?_⟩
  exact part3_abstract k n b A G P hAGA_rk.1 hSym hAGA_rk.2
