import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_275_aux

open Finset

theorem greedy {α : Type*} [DecidableEq α] {F : Type*} [Field F] [DecidableEq F]
    (B : α → α → F) (S : Finset α) (hdiag : ∀ t ∈ S, B t t ≠ 0) :
    ∀ U ⊆ S, ∃ (m : ℕ) (x : Fin m → α), (∀ a, x a ∈ U) ∧
      (∀ a b : Fin m, a < b → B (x a) (x b) = 0) ∧
      ∑ t ∈ U, (1:ℝ) / ((S.filter (fun t' => B t t' ≠ 0)).card : ℝ) ≤ m := by
  intro U
  induction U using Finset.strongInduction with
  | H U ih =>
    intro hU
    rcases U.eq_empty_or_nonempty with hE | hne
    · subst hE
      exact ⟨0, Fin.elim0, fun a => a.elim0, fun a => a.elim0, by simp⟩
    · obtain ⟨i, hiU, hmin⟩ :=
        U.exists_min_image (fun t => (U.filter (fun t' => B t t' ≠ 0)).card) hne
      set T := U.filter (fun t' => B i t' ≠ 0) with hT
      have hiT : i ∈ T := by
        rw [hT, mem_filter]
        exact ⟨hiU, hdiag i (hU hiU)⟩
      have hTU : T ⊆ U := filter_subset _ _
      have hsub : U \ T ⊂ U := by
        refine ⟨sdiff_subset, fun h => ?_⟩
        have := h hiU
        rw [mem_sdiff] at this
        exact this.2 hiT
      obtain ⟨m, x, hxU, htri, hsum⟩ := ih (U \ T) hsub (sdiff_subset.trans hU)
      refine ⟨m+1, Fin.cons i x, ?_, ?_, ?_⟩
      · intro a
        induction a using Fin.cases with
        | zero => simpa using hiU
        | succ a' =>
          simp only [Fin.cons_succ]
          exact sdiff_subset (hxU a')
      · intro a b hab
        induction a using Fin.cases with
        | zero =>
          induction b using Fin.cases with
          | zero => exact absurd hab (lt_irrefl _)
          | succ b' =>
            simp only [Fin.cons_zero, Fin.cons_succ]
            have h1 := hxU b'
            rw [mem_sdiff] at h1
            have h2 : x b' ∉ T := h1.2
            rw [hT, mem_filter] at h2
            by_contra h3
            exact h2 ⟨h1.1, h3⟩
        | succ a' =>
          induction b using Fin.cases with
          | zero => exact absurd hab (Fin.not_lt_zero _)
          | succ b' =>
            simp only [Fin.cons_succ]
            exact htri a' b' (Fin.succ_lt_succ_iff.mp hab)
      · have hTpos : (0:ℝ) < T.card := by
          exact_mod_cast card_pos.mpr ⟨i, hiT⟩
        have hT1 : ∑ t ∈ T, (1:ℝ) / ((S.filter (fun t' => B t t' ≠ 0)).card : ℝ) ≤ 1 := by
          have hle : ∀ t ∈ T, (1:ℝ) / ((S.filter (fun t' => B t t' ≠ 0)).card : ℝ)
              ≤ 1 / (T.card : ℝ) := by
            intro t ht
            have htU : t ∈ U := hTU ht
            have h1 : T.card ≤ (U.filter (fun t' => B t t' ≠ 0)).card := hmin t htU
            have h2 : (U.filter (fun t' => B t t' ≠ 0)).card
                ≤ (S.filter (fun t' => B t t' ≠ 0)).card :=
              card_le_card (filter_subset_filter _ hU)
            have h3 : (T.card : ℝ) ≤ (S.filter (fun t' => B t t' ≠ 0)).card := by
              exact_mod_cast h1.trans h2
            exact one_div_le_one_div_of_le hTpos h3
          calc ∑ t ∈ T, (1:ℝ) / ((S.filter (fun t' => B t t' ≠ 0)).card : ℝ)
              ≤ ∑ t ∈ T, (1:ℝ) / (T.card : ℝ) := sum_le_sum hle
            _ = 1 := by
              rw [sum_const, nsmul_eq_mul]
              field_simp
        rw [← sum_sdiff hTU]
        push_cast
        linarith

theorem tri_le {α : Type*} {F : Type*} [Field F] {ι : Type*} [Fintype ι]
    (B : α → α → F) (φ ψ : α → ι → F) (m : ℕ) (x : Fin m → α)
    (hB : ∀ a b : Fin m, B (x a) (x b) = ∑ i, φ (x a) i * ψ (x b) i)
    (hdiag : ∀ a, B (x a) (x a) ≠ 0)
    (htri : ∀ a b : Fin m, a < b → B (x a) (x b) = 0) : m ≤ Fintype.card ι := by
  classical
  have hli : LinearIndependent F (fun a => φ (x a)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have key : ∀ b, ∑ a, g a * B (x a) (x b) = 0 := by
      intro b
      have : ∑ i, (∑ a, g a • φ (x a)) i * ψ (x b) i = 0 := by
        rw [hg]
        simp
      rw [← this]
      simp only [hB, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun a _ => ?_))
      ring
    by_contra hne
    push_neg at hne
    have hP : (Finset.univ.filter (fun b => g b ≠ 0)).Nonempty := by
      obtain ⟨b, hb⟩ := hne
      exact ⟨b, by simp [hb]⟩
    set b := (Finset.univ.filter (fun b => g b ≠ 0)).max' hP with hbdef
    have hbmem := Finset.max'_mem _ hP
    rw [← hbdef] at hbmem
    have hgb : g b ≠ 0 := (mem_filter.mp hbmem).2
    have hcol := key b
    rw [Finset.sum_eq_single b] at hcol
    · exact hgb ((mul_eq_zero.mp hcol).resolve_right (hdiag b))
    · intro a _ hab
      rcases lt_or_gt_of_ne hab with h | h
      · rw [htri a b h, mul_zero]
      · have : g a = 0 := by
          by_contra hga
          have hmem : a ∈ Finset.univ.filter (fun b => g b ≠ 0) := by simp [hga]
          have := Finset.le_max' _ a hmem
          rw [← hbdef] at this
          exact absurd h (not_lt.mpr this)
        rw [this, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ b) h
  have := hli.fintype_card_le_finrank
  simpa [Module.finrank_fintype_fun_eq_card] using this

theorem tangent (s q : ℕ) (hs : 0 < s) :
    (2*(q:ℝ)+1) - ((q:ℝ)*(q+1)) / (s:ℝ) ≤ s := by
  have hs' : (0:ℝ) < s := by exact_mod_cast hs
  have key : (2*(q:ℝ)+1)*s - q*(q+1) ≤ s*s := by
    rcases Nat.lt_or_ge q s with h | h
    · have h' : (q:ℝ) + 1 ≤ s := by exact_mod_cast h
      nlinarith
    · have h' : (s:ℝ) ≤ q := by exact_mod_cast h
      nlinarith
  have e : (2*(q:ℝ)+1) - ((q:ℝ)*(q+1)) / (s:ℝ) = ((2*(q:ℝ)+1)*s - q*(q+1)) / s := by
    field_simp
  rw [e, div_le_iff₀ hs']
  linarith

theorem floor_le {α : Type*} (S : Finset α) (s : α → ℕ) (hs : ∀ t ∈ S, 0 < s t) (R : ℕ)
    (hR : 0 < R) (hsum : ∑ t ∈ S, (1:ℝ) / (s t : ℝ) ≤ R) :
    (R - S.card % R) * (S.card / R)^2 + (S.card % R) * (S.card / R + 1)^2 ≤ ∑ t ∈ S, s t := by
  have hu : S.card % R < R := Nat.mod_lt _ hR
  have hdm := Nat.div_add_mod S.card R
  set q := S.card / R
  set u := S.card % R
  have hM : (S.card : ℝ) = R*q + u := by exact_mod_cast hdm.symm
  have h1 : ∑ t ∈ S, ((2*(q:ℝ)+1) - ((q:ℝ)*(q+1)) / (s t : ℝ)) ≤ ∑ t ∈ S, (s t : ℝ) :=
    sum_le_sum (fun t ht => tangent (s t) q (hs t ht))
  have h2 : ∑ t ∈ S, ((2*(q:ℝ)+1) - ((q:ℝ)*(q+1)) / (s t : ℝ))
      = (2*(q:ℝ)+1) * S.card - ((q:ℝ)*(q+1)) * ∑ t ∈ S, (1:ℝ) / (s t : ℝ) := by
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul, mul_sum]
    congr 1
    · ring
    · refine sum_congr rfl (fun t _ => ?_)
      ring
  have h3 : ((q:ℝ)*(q+1)) * ∑ t ∈ S, (1:ℝ) / (s t : ℝ) ≤ ((q:ℝ)*(q+1)) * R :=
    mul_le_mul_of_nonneg_left hsum (by positivity)
  have goal : (((R - u) * q^2 + u * (q + 1)^2 : ℕ) : ℝ) ≤ ((∑ t ∈ S, s t : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub hu.le]
    nlinarith
  exact_mod_cast goal

theorem floor_ge {M R : ℕ} (hR : 0 < R) :
    2 * M ≤ (R - M % R) * (M / R)^2 + (M % R) * (M / R + 1)^2 + R := by
  have hu : M % R < R := Nat.mod_lt _ hR
  have hdm := Nat.div_add_mod M R
  set q := M / R
  set u := M % R
  zify [hu.le]
  have hdm' : (M:ℤ) = R*q + u := by exact_mod_cast hdm.symm
  rw [hdm']
  have h1 : (0:ℤ) ≤ ((R:ℤ) - u) * ((q:ℤ) - 1)^2 := by
    apply mul_nonneg
    · have : (u:ℤ) < R := by exact_mod_cast hu
      linarith
    · positivity
  nlinarith [sq_nonneg (q:ℤ), (Nat.cast_nonneg u : (0:ℤ) ≤ u)]

theorem card_small (k d : ℕ) :
    (Finset.univ.filter (fun S : Finset (Fin k) => S.card ≤ d)).card
      = ∑ j ∈ Finset.range (min k d + 1), k.choose j := by
  rw [card_eq_sum_card_fiberwise (f := Finset.card) (t := Finset.range (min k d + 1))]
  · refine sum_congr rfl (fun j hj => ?_)
    rw [mem_range] at hj
    have : (Finset.univ.filter (fun S : Finset (Fin k) => S.card ≤ d)).filter (fun S => S.card = j)
        = Finset.powersetCard j (Finset.univ : Finset (Fin k)) := by
      ext S
      simp only [mem_filter, mem_univ, true_and, mem_powersetCard, subset_univ]
      constructor
      · rintro ⟨_, h⟩
        exact h
      · intro h
        refine ⟨?_, h⟩
        have := Nat.le_of_lt_succ hj
        have := min_le_right k d
        omega
    rw [this, card_powersetCard, card_univ, Fintype.card_fin]
  · intro S hS
    simp only [Finset.mem_coe, mem_filter, mem_univ, true_and, coe_filter,
      Set.mem_setOf_eq] at hS
    simp only [Finset.mem_coe, mem_range, coe_range, Set.mem_Iio]
    have h1 : S.card ≤ k := by
      have := card_le_univ S
      simpa using this
    have : S.card ≤ min k d := le_min h1 hS
    omega

theorem main : ∀ (k r c d : ℕ),
  let F := ZMod 2
  let X := Fin k → F
  let Z := Fin r → F
  let W := X × Z
  ∀ (send : W → X) (tag : W → Fin c → Bool) (prefixes : Finset X),
    let count := fun (u y : X) => (Finset.univ.filter (fun z : Z => send (u,z) = y)).card
    (∀ u ∈ prefixes, ∃ coeff : Finset (Fin k) → F, ∀ y : X,
      (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin k) => S.card ≤ d),
        coeff S * ∏ j ∈ S, y j) = (count u y : F)) →
    let M := (Finset.univ.filter (fun w : W =>
      w.1 ∈ prefixes ∧ count w.1 (send w) % 2 = 1)).card
    let R := 2^c * ∑ j ∈ Finset.range (min k d + 1), k.choose j
    let q := M/R
    let u := M%R
    let floorSum := (R-u)*q^2 + u*(q+1)^2
    let repeats := ∑ a : W, (count a.1 (send a) - 1)
    let errors := (Finset.univ.filter (fun v : Fin 3 → W =>
      (v 0).1 = (v 1).1 ∧ send (v 1) = send (v 2) ∧ tag (v 2) = tag (v 0) ∧
      ¬(v 0 = v 1 ∧ v 1 = v 2))).card
    repeats + (floorSum-M) ≤ errors ∧ 2^r * prefixes.card ≤ R + errors := by
  intro k r c d F X Z W send tag prefixes count hpoly M R q u floorSum repeats errors
  classical
  choose! coeff hcoeff using hpoly
  set S := (Finset.univ.filter (fun w : W =>
      w.1 ∈ prefixes ∧ count w.1 (send w) % 2 = 1)) with hS
  have hMS : M = S.card := rfl
  let B : W → W → F := fun a t => ((count a.1 (send t) : ℕ) : F) * (if tag a = tag t then 1 else 0)
  let ι := (Fin c → Bool) × {T : Finset (Fin k) // T.card ≤ d}
  let φ : W → ι → F := fun a i => if tag a = i.1 then coeff a.1 i.2.1 else 0
  let ψ : W → ι → F := fun t i => if tag t = i.1 then ∏ j ∈ i.2.1, send t j else 0
  have hB : ∀ a ∈ S, ∀ t, B a t = ∑ i, φ a i * ψ t i := by
    intro a ha t
    have hpa : a.1 ∈ prefixes := (mem_filter.mp ha).2.1
    rw [Fintype.sum_prod_type]
    have inner : ∀ τ : Fin c → Bool, ∑ T : {T : Finset (Fin k) // T.card ≤ d}, φ a (τ, T) * ψ t (τ, T)
        = if tag a = τ ∧ tag t = τ then ((count a.1 (send t) : ℕ) : F) else 0 := by
      intro τ
      by_cases h1 : tag a = τ
      · by_cases h2 : tag t = τ
        · simp only [φ, ψ, h1, h2, if_true, and_self]
          rw [← hcoeff a.1 hpa (send t)]
          exact (Finset.sum_subtype (Finset.univ.filter (fun T : Finset (Fin k) => T.card ≤ d))
            (fun T => by simp) (fun T => coeff a.1 T * ∏ j ∈ T, send t j)).symm
        · simp [φ, ψ, h2]
      · simp [φ, ψ, h1]
    simp only [inner]
    by_cases h : tag a = tag t
    · simp [B, h]
    · simp only [B, h, if_false, mul_zero]
      refine (Finset.sum_eq_zero (fun τ _ => ?_)).symm
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact h (h1.trans h2.symm)
  have hcardι : Fintype.card ι = R := by
    simp only [ι, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    rw [Fintype.card_subtype, card_small]
  have hRpos : 0 < R := by
    apply Nat.mul_pos (by positivity)
    apply Finset.sum_pos'
    · intro j _
      exact Nat.zero_le _
    · exact ⟨0, by simp, by simp⟩
  have hodd : ∀ n : ℕ, n % 2 = 1 → ((n : ℕ) : F) ≠ 0 := by
    intro n hn h
    rw [ZMod.natCast_eq_zero_iff] at h
    omega
  have hdiag : ∀ t ∈ S, B t t ≠ 0 := by
    intro t ht
    have := (mem_filter.mp ht).2.2
    simp only [B, if_true, mul_one]
    exact hodd _ this
  obtain ⟨m, x, hxS, htri, hsum⟩ := greedy B S hdiag S subset_rfl
  have hmR : m ≤ R := by
    rw [← hcardι]
    exact tri_le B φ ψ m x (fun a b => hB (x a) (hxS a) (x b)) (fun a => hdiag (x a) (hxS a)) htri
  set sz : W → ℕ := fun t => (S.filter (fun t' => B t t' ≠ 0)).card with hsz
  have hszpos : ∀ t ∈ S, 0 < sz t := by
    intro t ht
    exact card_pos.mpr ⟨t, mem_filter.mpr ⟨ht, hdiag t ht⟩⟩
  have hsum' : ∑ t ∈ S, (1:ℝ) / (sz t : ℝ) ≤ R := by
    have : (m:ℝ) ≤ R := by exact_mod_cast hmR
    exact hsum.trans this
  have hfl := floor_le S sz hszpos R hRpos hsum'
  have hfloor : floorSum ≤ ∑ t ∈ S, sz t := by
    rw [← hMS] at hfl
    exact hfl
  set Pairs := (S ×ˢ S).filter (fun p : W × W => B p.1 p.2 ≠ 0) with hPairs
  set Offd := Pairs.filter (fun p : W × W => p.1 ≠ p.2) with hOffd
  have hPcard : (Pairs.card : ℕ) = ∑ t ∈ S, sz t := by
    rw [hPairs, card_filter, sum_product]
    refine sum_congr rfl (fun t _ => ?_)
    simp only [hsz, card_filter]
  have hdiagcard : (Pairs.filter (fun p : W × W => ¬ p.1 ≠ p.2)).card ≤ M := by
    rw [hMS]
    calc (Pairs.filter (fun p : W × W => ¬ p.1 ≠ p.2)).card
        ≤ (S.image (fun t => (t, t))).card := by
          apply card_le_card
          intro p hp
          rw [mem_filter, hPairs, mem_filter, mem_product] at hp
          rw [mem_image]
          refine ⟨p.1, hp.1.1.1, ?_⟩
          have : p.1 = p.2 := not_not.mp hp.2
          exact Prod.ext rfl this
      _ ≤ S.card := card_image_le
  have hsplit := card_filter_add_card_filter_not (s := Pairs) (fun p : W × W => p.1 ≠ p.2)
  have hOffbound : floorSum ≤ M + Offd.card := by
    have : Pairs.card ≤ M + Offd.card := by
      rw [← hsplit, hOffd]
      omega
    omega
  set Err := (Finset.univ.filter (fun v : Fin 3 → W =>
      (v 0).1 = (v 1).1 ∧ send (v 1) = send (v 2) ∧ tag (v 2) = tag (v 0) ∧
      ¬(v 0 = v 1 ∧ v 1 = v 2))) with hErr
  have hErrc : errors = Err.card := rfl
  set E1 := Err.filter (fun v => v 0 = v 2) with hE1
  set E2 := Err.filter (fun v => ¬ v 0 = v 2) with hE2
  have hE12 : E1.card + E2.card = Err.card := card_filter_add_card_filter_not _
  set Rp := (Finset.univ : Finset (W × Z)).filter
    (fun p => p.2 ≠ p.1.2 ∧ send (p.1.1, p.2) = send p.1) with hRp
  have hcount_ge : ∀ a : W, 1 ≤ count a.1 (send a) := by
    intro a
    apply card_pos.mpr
    exact ⟨a.2, by simp⟩
  have hRpcard : Rp.card = repeats := by
    have : ∀ a : W, ((Finset.univ : Finset Z).filter
        (fun z => z ≠ a.2 ∧ send (a.1, z) = send a)).card = count a.1 (send a) - 1 := by
      intro a
      have hmem : a.2 ∈ (Finset.univ : Finset Z).filter (fun z => send (a.1, z) = send a) := by
        simp
      have e : (Finset.univ : Finset Z).filter (fun z => z ≠ a.2 ∧ send (a.1, z) = send a)
          = ((Finset.univ : Finset Z).filter (fun z => send (a.1, z) = send a)).erase a.2 := by
        ext z
        simp [and_comm]
      rw [e, card_erase_of_mem hmem]
    rw [hRp, card_filter, Fintype.sum_prod_type]
    refine sum_congr rfl (fun a _ => ?_)
    rw [← this a, card_filter]
  have hE1ge : repeats ≤ E1.card := by
    rw [← hRpcard]
    apply card_le_card_of_injOn (fun p : W × Z => ![p.1, (p.1.1, p.2), p.1])
    · intro p hp
      rw [Finset.mem_coe, hRp, mem_filter] at hp
      rw [Finset.mem_coe, hE1, mem_filter, hErr, mem_filter]
      refine ⟨⟨mem_univ _, rfl, hp.2.2, rfl, ?_⟩, rfl⟩
      rintro ⟨h, _⟩
      exact hp.2.1 (congrArg Prod.snd h).symm
    · intro p _ p' _ h
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h0 h1
      have := congrArg Prod.snd h1
      exact Prod.ext h0 this
  have hE2ge : Offd.card ≤ E2.card := by
    let zc : W × W → Z := fun p =>
      if h : ∃ z, send (p.1.1, z) = send p.2 then h.choose else 0
    apply card_le_card_of_injOn (fun p : W × W => ![p.1, (p.1.1, zc p), p.2])
    · intro p hp
      rw [Finset.mem_coe, hOffd, mem_filter, hPairs, mem_filter, mem_product] at hp
      obtain ⟨⟨⟨_, _⟩, hBne⟩, hne⟩ := hp
      have htag : tag p.1 = tag p.2 := by
        by_contra h
        apply hBne
        show _ * _ = 0
        rw [if_neg h, mul_zero]
      have hex : ∃ z, send (p.1.1, z) = send p.2 := by
        by_contra h
        push_neg at h
        apply hBne
        have : count p.1.1 (send p.2) = 0 := by
          apply card_eq_zero.mpr
          ext z
          simp [h z]
        show _ * _ = 0
        rw [this, Nat.cast_zero, zero_mul]
      have hz : send (p.1.1, zc p) = send p.2 := by
        simp only [zc, dif_pos hex]
        exact hex.choose_spec
      rw [Finset.mem_coe, hE2, mem_filter, hErr, mem_filter]
      refine ⟨⟨mem_univ _, rfl, hz, htag.symm, ?_⟩, hne⟩
      rintro ⟨h1, h2⟩
      exact hne (h1.trans h2)
    · intro p _ p' _ h
      have h0 := congrFun h 0
      have h2 := congrFun h 2
      simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons] at h0 h2
      exact Prod.ext h0 h2
  have hfirst : repeats + (floorSum - M) ≤ errors := by
    rw [hErrc, ← hE12]
    omega
  refine ⟨hfirst, ?_⟩
  have hpre : 2^r * prefixes.card
      = ((Finset.univ : Finset W).filter (fun w => w.1 ∈ prefixes)).card := by
    have e : (Finset.univ : Finset W).filter (fun w => w.1 ∈ prefixes)
        = prefixes ×ˢ (Finset.univ : Finset Z) := by
      ext w
      rw [mem_filter, mem_product]
      simp
    rw [e, card_product, card_univ]
    simp only [Z, F, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    ring
  set Ev := (Finset.univ : Finset W).filter
    (fun w => w.1 ∈ prefixes ∧ ¬ count w.1 (send w) % 2 = 1) with hEv
  have hsplitW : ((Finset.univ : Finset W).filter (fun w => w.1 ∈ prefixes)).card
      = M + Ev.card := by
    have := card_filter_add_card_filter_not
      (s := (Finset.univ : Finset W).filter (fun w => w.1 ∈ prefixes))
      (fun w => count w.1 (send w) % 2 = 1)
    rw [filter_filter, filter_filter] at this
    rw [← this]
  have hEvle : Ev.card ≤ repeats := by
    calc Ev.card = ∑ a ∈ Ev, 1 := card_eq_sum_ones _
      _ ≤ ∑ a ∈ Ev, (count a.1 (send a) - 1) := by
        refine sum_le_sum (fun a ha => ?_)
        rw [hEv, mem_filter] at ha
        have h1 := hcount_ge a
        have h2 := ha.2.2
        omega
      _ ≤ ∑ a : W, (count a.1 (send a) - 1) :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
  have hfg := floor_ge (M := M) hRpos
  have hfs : floorSum = (R - M % R) * (M / R)^2 + (M % R) * (M / R + 1)^2 := rfl
  rw [hpre, hsplitW, hErrc, ← hE12]
  omega

end PEqualNP.Outside.L_pcx_275_aux

theorem PEqualNP.Outside.L_pcx_275 : ∀ (k r c d : ℕ),
  let F := ZMod 2
  let X := Fin k → F
  let Z := Fin r → F
  let W := X × Z
  ∀ (send : W → X) (tag : W → Fin c → Bool) (prefixes : Finset X),
    let count := fun (u y : X) => (Finset.univ.filter (fun z : Z => send (u,z) = y)).card
    (∀ u ∈ prefixes, ∃ coeff : Finset (Fin k) → F, ∀ y : X,
      (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin k) => S.card ≤ d),
        coeff S * ∏ j ∈ S, y j) = (count u y : F)) →
    let M := (Finset.univ.filter (fun w : W =>
      w.1 ∈ prefixes ∧ count w.1 (send w) % 2 = 1)).card
    let R := 2^c * ∑ j ∈ Finset.range (min k d + 1), k.choose j
    let q := M/R
    let u := M%R
    let floorSum := (R-u)*q^2 + u*(q+1)^2
    let repeats := ∑ a : W, (count a.1 (send a) - 1)
    let errors := (Finset.univ.filter (fun v : Fin 3 → W =>
      (v 0).1 = (v 1).1 ∧ send (v 1) = send (v 2) ∧ tag (v 2) = tag (v 0) ∧
      ¬(v 0 = v 1 ∧ v 1 = v 2))).card
    repeats + (floorSum-M) ≤ errors ∧ 2^r * prefixes.card ≤ R + errors :=
  PEqualNP.Outside.L_pcx_275_aux.main
