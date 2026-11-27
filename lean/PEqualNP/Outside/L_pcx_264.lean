import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_264_aux

lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> rfl

lemma zmod2_mul_self (a : ZMod 2) : a * a = a := by
  fin_cases a <;> rfl

lemma zmod2_eq_one_of_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact absurd rfl h
  · rfl

lemma card_low_eq_volume (k d : ℕ) :
    (Finset.univ.filter (fun S : Finset (Fin k) => S.card ≤ d)).card =
      ∑ j ∈ Finset.range (min k d + 1), k.choose j := by
  have hbi : Finset.univ.filter (fun S : Finset (Fin k) => S.card ≤ d) =
      (Finset.range (min k d + 1)).biUnion
        (fun j => Finset.powersetCard j (Finset.univ : Finset (Fin k))) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_powersetCard, Finset.subset_univ]
    constructor
    · intro hle
      have hk : S.card ≤ k := by simpa using Finset.card_le_univ S
      exact ⟨S.card, by omega, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      omega
  rw [hbi, Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp [Finset.card_powersetCard]
  · intro j1 _ j2 _ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro S h1 h2
    rw [Finset.mem_powersetCard] at h1 h2
    exact hne (h1.2.symm.trans h2.2)

lemma prod_insert_zmod2 {k : ℕ} (S : Finset (Fin k)) (j : Fin k) (y : Fin k → ZMod 2) :
    (∏ i ∈ insert j S, y i) = (∏ i ∈ S, y i) * y j := by
  by_cases hj : j ∈ S
  · rw [Finset.insert_eq_of_mem hj]
    have hsplit : (∏ i ∈ S, y i) = y j * ∏ i ∈ S.erase j, y i :=
      (Finset.mul_prod_erase S y hj).symm
    rw [hsplit]
    calc
      y j * ∏ i ∈ S.erase j, y i = (y j * y j) * ∏ i ∈ S.erase j, y i := by rw [zmod2_mul_self]
      _ = y j * (∏ i ∈ S.erase j, y i) * y j := by ring
  · rw [Finset.prod_insert hj, mul_comm]

lemma prod_affine_poly_deg {k : ℕ} :
    ∀ (m : ℕ) (c0 : Fin m → ZMod 2) (M : Fin m → Fin k → ZMod 2),
      ∃ coeff : Finset (Fin k) → ZMod 2, ∀ y : Fin k → ZMod 2,
        (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin k) => S.card ≤ m),
          coeff S * ∏ j ∈ S, y j) =
        ∏ t : Fin m, (c0 t + ∑ j : Fin k, M t j * y j) := by
  intro m
  induction m with
  | zero =>
    intro c0 M
    refine ⟨fun S => if S = ∅ then 1 else 0, fun y => ?_⟩
    rw [Finset.sum_eq_single (∅ : Finset (Fin k))]
    · simp
    · intro S _ hne; simp [hne]
    · intro h; exfalso; apply h; simp
  | succ m ih =>
    intro c0 M
    rcases ih (fun t => c0 t.castSucc) (fun t => M t.castSucc) with ⟨coeff, hcoeff⟩
    let lowm := Finset.univ.filter (fun S : Finset (Fin k) => S.card ≤ m)
    let low1 := Finset.univ.filter (fun S : Finset (Fin k) => S.card ≤ m + 1)
    let a0 : ZMod 2 := c0 (Fin.last m)
    let a : Fin k → ZMod 2 := M (Fin.last m)
    let coeff' : Finset (Fin k) → ZMod 2 := fun T =>
      (if T.card ≤ m then coeff T * a0 else 0) +
        ∑ S ∈ lowm, ∑ j : Fin k, if insert j S = T then coeff S * a j else 0
    refine ⟨coeff', fun y => ?_⟩
    rw [Fin.prod_univ_castSucc, ← hcoeff y]
    change (∑ T ∈ low1, coeff' T * ∏ i ∈ T, y i) =
      (∑ S ∈ lowm, coeff S * ∏ i ∈ S, y i) * (a0 + ∑ j : Fin k, a j * y j)
    simp only [coeff']
    simp_rw [add_mul, Finset.sum_add_distrib]
    rw [mul_add]
    congr 1
    · have hsub : lowm ⊆ low1 := by
        intro T hT
        simp only [lowm, low1, Finset.mem_filter, Finset.mem_univ, true_and] at hT ⊢
        omega
      have hfilt : (∑ T ∈ low1, (if T.card ≤ m then coeff T * a0 else 0) * ∏ i ∈ T, y i) =
          ∑ T ∈ low1.filter (fun T => T.card ≤ m), coeff T * a0 * ∏ i ∈ T, y i := by
        conv_rhs => rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun T _ => ?_
        split_ifs <;> simp
      have hfeq : low1.filter (fun T => T.card ≤ m) = lowm := by
        ext T
        simp only [low1, lowm, Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      rw [hfilt, hfeq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun S _ => by ring
    · have hswap :
          (∑ T ∈ low1, (∑ S ∈ lowm, ∑ j : Fin k, if insert j S = T then coeff S * a j else 0) *
              ∏ i ∈ T, y i) =
          ∑ S ∈ lowm, ∑ j : Fin k,
            ∑ T ∈ low1, (if insert j S = T then coeff S * a j else 0) * ∏ i ∈ T, y i := by
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [Finset.sum_comm]
      rw [hswap]
      have hinner : ∀ S ∈ lowm, ∀ j : Fin k,
          (∑ T ∈ low1, (if insert j S = T then coeff S * a j else 0) * ∏ i ∈ T, y i) =
            (coeff S * ∏ i ∈ S, y i) * (a j * y j) := by
        intro S hS j
        have hmem : insert j S ∈ low1 := by
          simp only [lowm, low1, Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
          have hcard := Finset.card_insert_le j S
          omega
        rw [Finset.sum_eq_single (insert j S)]
        · simp only [↓reduceIte, prod_insert_zmod2]
          ring
        · intro T _ hne
          simp [Ne.symm hne]
        · intro h; exact absurd hmem h
      have hsum_eq :
          (∑ S ∈ lowm, ∑ j : Fin k,
            ∑ T ∈ low1, (if insert j S = T then coeff S * a j else 0) * ∏ i ∈ T, y i) =
          ∑ S ∈ lowm, ∑ j : Fin k, (coeff S * ∏ i ∈ S, y i) * (a j * y j) := by
        refine Finset.sum_congr rfl fun S hS => Finset.sum_congr rfl fun j _ => hinner S hS j
      rw [hsum_eq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun S _ => ?_
      rw [Finset.mul_sum]

lemma affine_indicator_poly {k r : ℕ} (A : (Fin r → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2))
    (hAinj : Function.Injective A) (v : Fin k → ZMod 2) :
    ∃ coeff : Finset (Fin k) → ZMod 2, ∀ y : Fin k → ZMod 2,
      (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin k) => S.card ≤ k - r),
        coeff S * ∏ j ∈ S, y j) =
      (if y ∈ Finset.univ.image (fun z : Fin r → ZMod 2 => A z + v) then (1 : ZMod 2) else 0) := by
  let R := LinearMap.range A
  have hrR : Module.finrank (ZMod 2) R = r := by
    have hr := LinearMap.finrank_range_add_finrank_ker A
    rw [LinearMap.ker_eq_bot.mpr hAinj, finrank_bot, add_zero] at hr
    simpa [R] using hr
  have hdimQ : Module.finrank (ZMod 2) ((Fin k → ZMod 2) ⧸ R) = k - r := by
    have hq := Submodule.finrank_quotient_add_finrank R
    have hdimX : Module.finrank (ZMod 2) (Fin k → ZMod 2) = k := by simp
    rw [hdimX, hrR] at hq
    omega
  let bQ := Module.finBasisOfFinrankEq (ZMod 2) ((Fin k → ZMod 2) ⧸ R) hdimQ
  let L : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin (k - r) → ZMod 2) :=
    bQ.equivFun.toLinearMap.comp R.mkQ
  have hkerL : LinearMap.ker L = R := by
    ext x
    simp only [LinearMap.mem_ker, L, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.map_eq_zero_iff]
    exact Submodule.Quotient.mk_eq_zero R
  let c0 : Fin (k - r) → ZMod 2 := fun t => 1 + L v t
  let M : Fin (k - r) → Fin k → ZMod 2 := fun t j => L (Pi.single (M := fun _ => ZMod 2) j 1) t
  have hL_eval : ∀ (y : Fin k → ZMod 2) (t : Fin (k - r)),
      L y t = ∑ j : Fin k, M t j * y j := by
    intro y t
    have hy : y = ∑ j : Fin k, y j • Pi.single (M := fun _ => ZMod 2) j 1 := by
      ext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single j]
      · simp
      · intro j' _ hj'; simp [Pi.single_eq_of_ne (Ne.symm hj')]
      · intro h; exact absurd (Finset.mem_univ j) h
    conv_lhs => rw [hy]
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, M]
    ring
  rcases prod_affine_poly_deg (k - r) c0 M with ⟨coeff, hcoeff⟩
  refine ⟨coeff, fun y => ?_⟩
  rw [hcoeff y]
  have hiff : y ∈ Finset.univ.image (fun z : Fin r → ZMod 2 => A z + v) ↔ L (y + v) = 0 := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    rw [← LinearMap.mem_ker, hkerL]
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨z, ?_⟩
      rw [← hz]
      ext j
      simp only [Pi.add_apply]
      calc
        A z j = A z j + (v j + v j) := by rw [zmod2_add_self, add_zero]
        _ = A z j + v j + v j := by ring
    · rintro ⟨z, hz⟩
      refine ⟨z, ?_⟩
      ext j
      have hj := congrFun hz j
      simp only [Pi.add_apply] at hj
      calc
        A z j + v j = (y j + v j) + v j := by rw [hj]
        _ = y j + (v j + v j) := by ring
        _ = y j := by rw [zmod2_add_self, add_zero]
  by_cases hmem : y ∈ Finset.univ.image (fun z : Fin r → ZMod 2 => A z + v)
  · simp only [hmem, ↓reduceIte]
    have h0 : L (y + v) = 0 := hiff.mp hmem
    refine Finset.prod_eq_one fun t _ => ?_
    rw [← hL_eval y t]
    have ht : L y t + L v t = 0 := by
      have h1 := congrFun h0 t
      rw [map_add, Pi.add_apply, Pi.zero_apply] at h1
      exact h1
    calc
      c0 t + L y t = 1 + (L y t + L v t) := by dsimp only [c0]; ring
      _ = 1 + 0 := by rw [ht]
      _ = 1 := add_zero 1
  · simp only [hmem, ↓reduceIte]
    have hne : L (y + v) ≠ 0 := mt hiff.mpr hmem
    have hex : ∃ t : Fin (k - r), L (y + v) t ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hne (funext hall)
    rcases hex with ⟨t, ht⟩
    refine Finset.prod_eq_zero (Finset.mem_univ t) ?_
    rw [← hL_eval y t]
    have ht1 : L y t + L v t = 1 := by
      have h1 : L y t + L v t ≠ 0 := by
        rw [map_add, Pi.add_apply] at ht
        exact ht
      exact zmod2_eq_one_of_ne_zero h1
    calc
      c0 t + L y t = 1 + (L y t + L v t) := by dsimp only [c0]; ring
      _ = 1 + 1 := by rw [ht1]
      _ = 0 := zmod2_add_self 1

end PEqualNP.Outside.L_pcx_264_aux

open PEqualNP.Outside.L_pcx_264_aux in
theorem PEqualNP.Outside.L_pcx_264 :
    ∀ (k r c : ℕ),
  let F := ZMod 2
  let X := Fin k → F
  let Z := Fin r → F
  let W := X × Z
  ∀ (send : W → X) (tag : W → Fin c → Bool),
    (∀ a b t : W, a.1 = b.1 → send b = send t → tag t = tag a → a = b ∧ b = t) →
    let volume := fun d : ℕ => ∑ j ∈ Finset.range (min k d + 1), k.choose j
    (∀ d : ℕ,
      (∀ u : X, ∃ coeff : Finset (Fin k) → F, ∀ y : X,
        (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin k) => S.card ≤ d),
          coeff S * ∏ j ∈ S, y j) =
        (if y ∈ Finset.univ.image (fun z : Z => send (u,z)) then (1 : F) else 0)) →
      (∀ h : Fin c → Bool, (Finset.univ.filter (fun w : W => tag w = h)).card ≤ volume d) ∧
      2^(k+r) ≤ 2^c * volume d) ∧
    ((∀ u : X, ∃ (A : Z →ₗ[F] X) (v : X), ∀ z : Z, send (u,z) = A z + v) →
      r ≤ k ∧ 2^(k+r) ≤ 2^c * volume (k-r)) := by
  intro k r c F X Z W send tag huniq volume
  have hpart1 : ∀ d : ℕ,
      (∀ u : X, ∃ coeff : Finset (Fin k) → F, ∀ y : X,
        (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin k) => S.card ≤ d),
          coeff S * ∏ j ∈ S, y j) =
        (if y ∈ Finset.univ.image (fun z : Z => send (u,z)) then (1 : F) else 0)) →
      (∀ h : Fin c → Bool, (Finset.univ.filter (fun w : W => tag w = h)).card ≤ volume d) ∧
      2^(k+r) ≤ 2^c * volume d := by
    intro d hdeg
    let low := Finset.univ.filter (fun S : Finset (Fin k) => S.card ≤ d)
    have hlow_card : low.card = volume d := card_low_eq_volume k d
    have hfiber : ∀ h : Fin c → Bool,
        (Finset.univ.filter (fun w : W => tag w = h)).card ≤ volume d := by
      intro h
      let H := Finset.univ.filter (fun w : W => tag w = h)
      choose coeff hcoeff using hdeg
      let vec : ↥H → (↥low → ZMod 2) := fun a S => coeff a.1.1 S.1
      let evalVec : ↥H → (↥low → ZMod 2) := fun t S => ∏ j ∈ S.1, send t.1 j
      have hdelta : ∀ a t : ↥H, dotProduct (vec a) (evalVec t) = if a = t then 1 else 0 := by
        intro a t
        have hsum : dotProduct (vec a) (evalVec t) =
            ∑ S ∈ low, coeff a.1.1 S * ∏ j ∈ S, send t.1 j := by
          simp only [dotProduct, vec, evalVec]
          exact (Finset.sum_subtype low (p := fun S => S ∈ low) (fun _ => Iff.rfl)
            (fun S => coeff a.1.1 S * ∏ j ∈ S, send t.1 j)).symm
        rw [hsum, hcoeff a.1.1 (send t.1)]
        have hmem_iff : send t.1 ∈ Finset.univ.image (fun z : Z => send (a.1.1, z)) ↔ a = t := by
          constructor
          · intro hmem
            rw [Finset.mem_image] at hmem
            rcases hmem with ⟨z, _, hz⟩
            have hta : tag t.1 = tag a.1 := by
              have ha := (Finset.mem_filter.mp a.2).2
              have ht := (Finset.mem_filter.mp t.2).2
              rw [ht, ha]
            have hres := huniq a.1 (a.1.1, z) t.1 rfl hz hta
            exact Subtype.ext (hres.1.trans hres.2)
          · rintro rfl
            rw [Finset.mem_image]
            exact ⟨a.1.2, Finset.mem_univ _, rfl⟩
        by_cases hat : a = t
        · have hm := hmem_iff.mpr hat
          simp only [hm, ↓reduceIte]
          simp only [hat, ↓reduceIte]
        · have hm : send t.1 ∉ Finset.univ.image (fun z : Z => send (a.1.1, z)) := mt hmem_iff.mp hat
          simp only [hm, ↓reduceIte]
          simp only [hat, ↓reduceIte]
      have hli : LinearIndependent (ZMod 2) vec := by
        rw [Fintype.linearIndependent_iff]
        intro g hg t
        have hdot : dotProduct (∑ a : ↥H, g a • vec a) (evalVec t) = 0 := by
          rw [hg, zero_dotProduct]
        rw [sum_dotProduct] at hdot
        simp_rw [smul_dotProduct, smul_eq_mul, hdelta] at hdot
        rw [Finset.sum_eq_single t] at hdot
        · simpa using hdot
        · intro a _ hat; simp [hat]
        · intro h; exact absurd (Finset.mem_univ t) h
      have hcard_le : Fintype.card ↥H ≤ Module.finrank (ZMod 2) (↥low → ZMod 2) :=
        hli.fintype_card_le_finrank
      have hdim : Module.finrank (ZMod 2) (↥low → ZMod 2) = low.card := by simp
      have hHcard : Fintype.card ↥H = H.card := Fintype.card_coe H
      rw [hHcard, hdim, hlow_card] at hcard_le
      exact hcard_le
    refine ⟨hfiber, ?_⟩
    have hcardW : Fintype.card W = 2 ^ (k + r) := by
      simp [W, X, Z, F, pow_add]
    have hsum_part : Fintype.card W =
        ∑ h : Fin c → Bool, (Finset.univ.filter (fun w : W => tag w = h)).card := by
      rw [← Finset.card_univ]
      exact Finset.card_eq_sum_card_fiberwise fun w _ => Finset.mem_univ (tag w)
    have hle : (∑ h : Fin c → Bool, (Finset.univ.filter (fun w : W => tag w = h)).card) ≤
        ∑ _h : Fin c → Bool, volume d := Finset.sum_le_sum fun h _ => hfiber h
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hle
    have hcardC : Fintype.card (Fin c → Bool) = 2 ^ c := by simp
    rw [hcardC] at hle
    rw [← hcardW, hsum_part]
    exact hle
  refine ⟨hpart1, ?_⟩
  intro haff
  have hinj_all : ∀ u : X, ∃ (A : Z →ₗ[F] X) (v : X),
      Function.Injective A ∧ ∀ z : Z, send (u, z) = A z + v := by
    intro u
    rcases haff u with ⟨A, v, hAv⟩
    refine ⟨A, v, ?_, hAv⟩
    intro z1 z2 heq
    have hsend : send (u, z2) = send (u, z1) := by rw [hAv z2, hAv z1, heq]
    have hres := huniq (u, z1) (u, z2) (u, z1) rfl hsend rfl
    exact congrArg Prod.snd hres.1
  have hrk : r ≤ k := by
    rcases hinj_all 0 with ⟨A, _, hAinj, _⟩
    have hle := LinearMap.finrank_le_finrank_of_injective hAinj
    have hZ : Module.finrank (ZMod 2) Z = r := by simp [Z, F]
    have hX : Module.finrank (ZMod 2) X = k := by simp [X, F]
    dsimp only [F] at hle
    rw [hZ, hX] at hle
    exact hle
  refine ⟨hrk, ?_⟩
  have hdeg_kr : ∀ u : X, ∃ coeff : Finset (Fin k) → F, ∀ y : X,
      (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin k) => S.card ≤ k - r),
        coeff S * ∏ j ∈ S, y j) =
      (if y ∈ Finset.univ.image (fun z : Z => send (u,z)) then (1 : F) else 0) := by
    intro u
    rcases hinj_all u with ⟨A, v, hAinj, hAv⟩
    rcases affine_indicator_poly A hAinj v with ⟨coeff, hcoeff⟩
    refine ⟨coeff, fun y => ?_⟩
    have himg : Finset.univ.image (fun z : Z => send (u, z)) =
        Finset.univ.image (fun z : Fin r → ZMod 2 => A z + v) := by
      ext w
      simp only [Finset.mem_image, Finset.mem_univ, true_and, hAv]
      rfl
    rw [himg]
    exact hcoeff y
  exact (hpart1 (k - r) hdeg_kr).2
