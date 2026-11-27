import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25734_aux

abbrev F2 := ZMod 2

private def dotF {d : ℕ} (x y : Fin d → F2) : F2 :=
  ∑ j : Fin d, x j * y j

private lemma exists_good_v_ge16 (a : ℕ) (ha : 16 ≤ a) :
    let n := 2 ^ a
    let d := 32 * a
    let W := Fin d → F2
    ∃ v : Fin n → W,
      ∀ T : Finset (Fin n), T.card = 32 * a →
        ∃ I : Finset (Fin n), I ⊆ T ∧ I.card = 8 * a ∧
          LinearIndependent F2 (fun x : I => v x.val) := by
  intro n d W
  classical
  let badSet : Finset (Fin n → W) :=
    Finset.univ.filter (fun v =>
      ∃ T : Finset (Fin n), T.card = 32 * a ∧
        ∀ I : Finset (Fin n), I ⊆ T → I.card = 8 * a →
          ¬ LinearIndependent F2 (fun x : I => v x.val))
  have h24_le : 24 * a ≤ n := by
    have hpow : ∀ k, 8 ≤ k → 24 * k ≤ 2 ^ k := by
      intro k
      induction k with
      | zero => omega
      | succ k ih =>
        intro hk
        by_cases hk7 : k = 7
        · subst hk7; decide
        · have := ih (by omega)
          have h2k : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
          omega
    exact hpow a (by omega)
  have hcover : ∀ v ∈ badSet,
      ∃ (T : Finset (Fin n)) (B : Finset (Fin n)),
        T.card = 32 * a ∧ B ⊆ T ∧ B.card = 8 * a ∧
        ∀ x ∈ T \ B, ∃ c : B → F2, v x = ∑ y : B, c y • v y.val := by
    intro v hv
    simp only [badSet, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    obtain ⟨T, hTcard, hnoI⟩ := hv
    let indSubsets : Finset (Finset (Fin n)) :=
      T.powerset.filter (fun I => LinearIndependent F2 (fun x : I => v x.val))
    have hne : indSubsets.Nonempty := by
      refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset T), ?_⟩⟩
      exact linearIndependent_empty_type
    obtain ⟨B0, hB0mem, hB0max⟩ := Finset.exists_max_image indSubsets Finset.card hne
    have hB0sub : B0 ⊆ T := Finset.mem_powerset.mp (Finset.mem_filter.mp hB0mem).1
    have hB0li : LinearIndependent F2 (fun x : B0 => v x.val) := (Finset.mem_filter.mp hB0mem).2
    have hB0lt : B0.card < 8 * a := by
      by_contra hge
      push_neg at hge
      obtain ⟨I, hIsub, hIcard⟩ := Finset.exists_subset_card_eq hge
      have hIli : LinearIndependent F2 (fun x : I => v x.val) := by
        let incl : I → B0 := fun x => ⟨x.val, hIsub x.property⟩
        have hinj : Function.Injective incl := fun x y h => Subtype.ext (congrArg (fun z : B0 => z.val) h)
        exact hB0li.comp incl hinj
      exact hnoI I (hIsub.trans hB0sub) hIcard hIli
    have hspan_B0 : ∀ x ∈ T, v x ∈ Submodule.span F2 (Set.range (fun y : B0 => v y.val)) := by
      intro x hxT
      by_cases hxB : x ∈ B0
      · exact Submodule.subset_span ⟨⟨x, hxB⟩, rfl⟩
      · by_contra hnot
        let B1 := insert x B0
        have hB1sub : B1 ⊆ T := Finset.insert_subset hxT hB0sub
        have hB1li : LinearIndependent F2 (fun y : B1 => v y.val) := by
          rw [Fintype.linearIndependent_iff]
          intro g hg
          have hg' : g ⟨x, Finset.mem_insert_self x B0⟩ • v x +
              ∑ y : B0, g ⟨y.val, Finset.mem_insert_of_mem y.property⟩ • v y.val = 0 := by
            rw [← hg]
            have h1 : ∑ y : B1, g y • v y.val =
                ∑ y ∈ B1, (if h : y ∈ B1 then g ⟨y, h⟩ • v y else 0) := by
              refine Finset.sum_bij (fun y _ => y.val) (fun y _ => y.property)
                (fun _ _ _ _ h => Subtype.ext h)
                (fun y hy => ⟨⟨y, hy⟩, Finset.mem_univ _, rfl⟩)
                (fun y _ => by simp only [y.property, ↓reduceDIte])
            have h2 : ∑ y : B0, g ⟨y.val, Finset.mem_insert_of_mem y.property⟩ • v y.val =
                ∑ y ∈ B0, (if h : y ∈ B1 then g ⟨y, h⟩ • v y else 0) := by
              refine Finset.sum_bij (fun y _ => y.val) (fun y _ => y.property)
                (fun _ _ _ _ h => Subtype.ext h)
                (fun y hy => ⟨⟨y, hy⟩, Finset.mem_univ _, rfl⟩)
                (fun y _ => by
                  have hyB1 : y.val ∈ B1 := Finset.mem_insert_of_mem y.property
                  simp only [hyB1, ↓reduceDIte])
            rw [h1, Finset.sum_insert hxB]
            have hxB1 : x ∈ B1 := Finset.mem_insert_self x B0
            simp only [hxB1, ↓reduceDIte]
            rw [h2]
          have hgx : g ⟨x, Finset.mem_insert_self x B0⟩ = 0 := by
            by_contra hne0
            have h1 : g ⟨x, Finset.mem_insert_self x B0⟩ = 1 := by
              generalize hz : g ⟨x, Finset.mem_insert_self x B0⟩ = z at hne0 ⊢
              fin_cases z
              · exact absurd rfl hne0
              · rfl
            rw [h1, one_smul] at hg'
            have hvx : v x = ∑ y : B0, g ⟨y.val, Finset.mem_insert_of_mem y.property⟩ • v y.val := by
              have hadd := congrArg (· + ∑ y : B0, g ⟨y.val, Finset.mem_insert_of_mem y.property⟩ • v y.val) hg'
              have h2z : ∀ w : W, w + w = 0 := fun w => by
                funext j; change w j + w j = 0; generalize hw : w j = z; fin_cases z <;> rfl
              rw [add_assoc, h2z, add_zero, zero_add] at hadd
              exact hadd
            apply hnot
            rw [hvx]
            exact Submodule.sum_mem _ fun y _ =>
              Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩)
          rw [hgx, zero_smul, zero_add] at hg'
          have hB0_zero := (Fintype.linearIndependent_iff.mp hB0li) _ hg'
          intro y
          by_cases hyx : y.val = x
          · have : y = ⟨x, Finset.mem_insert_self x B0⟩ := Subtype.ext hyx
            rw [this, hgx]
          · have hyB0 : y.val ∈ B0 := (Finset.mem_insert.mp y.property).resolve_left hyx
            have : y = ⟨y.val, Finset.mem_insert_of_mem hyB0⟩ := Subtype.ext rfl
            rw [this]
            exact hB0_zero ⟨y.val, hyB0⟩
        have hB1mem : B1 ∈ indSubsets := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hB1sub, hB1li⟩
        have hle := hB0max B1 hB1mem
        have hcard1 : B1.card = B0.card + 1 := Finset.card_insert_of_notMem hxB
        omega
    have hneed : 8 * a - B0.card ≤ (T \ B0).card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hB0sub]
      omega
    obtain ⟨E, hEsub, hEcard⟩ := Finset.exists_subset_card_eq hneed
    let B := B0 ∪ E
    have hdisj : Disjoint B0 E := Finset.disjoint_left.mpr fun z hzB hzE =>
      (Finset.mem_sdiff.mp (hEsub hzE)).2 hzB
    have hBsub : B ⊆ T := Finset.union_subset hB0sub (hEsub.trans Finset.sdiff_subset)
    have hBcard : B.card = 8 * a := by
      rw [Finset.card_union_of_disjoint hdisj, hEcard]
      omega
    refine ⟨T, B, hTcard, hBsub, hBcard, ?_⟩
    intro x hx
    have hxT : x ∈ T := (Finset.mem_sdiff.mp hx).1
    have hmem := hspan_B0 x hxT
    rw [Finsupp.mem_span_range_iff_exists_finsupp] at hmem
    obtain ⟨c0, hc0⟩ := hmem
    rw [Finsupp.sum_fintype c0 (fun i a => a • v i.val) (fun _ => zero_smul _ _)] at hc0
    refine ⟨fun y => if hy : y.val ∈ B0 then c0 ⟨y.val, hy⟩ else 0, ?_⟩
    rw [← hc0]
    have hsum1 : ∑ y : B, (if hy : y.val ∈ B0 then c0 ⟨y.val, hy⟩ else 0) • v y.val =
        ∑ y ∈ Finset.univ.filter (fun y : B => y.val ∈ B0),
          (if hy : y.val ∈ B0 then c0 ⟨y.val, hy⟩ else 0) • v y.val := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun y _ => ?_
      split_ifs with hy <;> simp
    rw [hsum1]
    refine Finset.sum_bij (fun y _ => (⟨y.val, Finset.mem_union_left E y.property⟩ : B))
      (fun y _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, y.property⟩)
      (fun _ _ _ _ h => Subtype.ext (congrArg (fun z : B => z.val) h))
      (fun y hy => ⟨⟨y.val, (Finset.mem_filter.mp hy).2⟩, Finset.mem_univ _, Subtype.ext rfl⟩)
      (fun y _ => by simp only [y.property, ↓reduceDIte])
  let pairs : Finset (Finset (Fin n) × Finset (Fin n)) :=
    (Finset.univ.powersetCard (32 * a)).biUnion fun T =>
      (T.powersetCard (8 * a)).image fun B => (T, B)
  let badTB (p : Finset (Fin n) × Finset (Fin n)) : Finset (Fin n → W) :=
    Finset.univ.filter (fun v =>
      ∀ x ∈ p.1 \ p.2, ∃ c : p.2 → F2, v x = ∑ y : p.2, c y • v y.val)
  have hsub_union : badSet ⊆ pairs.biUnion badTB := by
    intro v hv
    obtain ⟨T, B, hT, hBT, hB, hlin⟩ := hcover v hv
    rw [Finset.mem_biUnion]
    refine ⟨(T, B), ?_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlin⟩⟩
    simp only [pairs, Finset.mem_biUnion, Finset.mem_powersetCard, Finset.subset_univ, true_and,
      Finset.mem_image]
    exact ⟨T, hT, B, ⟨hBT, hB⟩, rfl⟩
  have hcard_TB : ∀ p ∈ pairs, (badTB p).card ≤ 2 ^ (d * (n - 24 * a) + 192 * a ^ 2) := by
    intro p hp
    simp only [pairs, Finset.mem_biUnion, Finset.mem_powersetCard, Finset.subset_univ, true_and,
      Finset.mem_image] at hp
    obtain ⟨T, hT, B, ⟨hBT, hB⟩, rfl⟩ := hp
    let D := T \ B
    have hDcard : D.card = 24 * a := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hBT, hT, hB]
      omega
    have hcompl_card : (Finset.univ \ D).card = n - 24 * a := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hDcard]
    let Base := {i : Fin n // i ∉ D} → W
    let Coeffs := D → (B → F2)
    let decode : Base × Coeffs → (Fin n → W) := fun ⟨v0, cs⟩ i =>
      if hi : i ∈ D then ∑ y : B, cs ⟨i, hi⟩ y • v0 ⟨y.val, fun h => (Finset.mem_sdiff.mp h).2 y.property⟩
      else v0 ⟨i, hi⟩
    have hsub_img : badTB (T, B) ⊆ Finset.univ.image decode := by
      intro v hv
      simp only [badTB, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      have hchoose : ∀ x : D, ∃ c : B → F2, v x.val = ∑ y : B, c y • v y.val :=
        fun x => hv x.val x.property
      let cs : Coeffs := fun x => Classical.choose (hchoose x)
      let v0 : Base := fun i => v i.val
      refine Finset.mem_image.mpr ⟨(v0, cs), Finset.mem_univ _, ?_⟩
      funext i
      dsimp only [decode, v0]
      split_ifs with hi
      · exact (Classical.choose_spec (hchoose ⟨i, hi⟩)).symm
      · rfl
    calc (badTB (T, B)).card
        ≤ (Finset.univ.image decode).card := Finset.card_le_card hsub_img
      _ ≤ (Finset.univ : Finset (Base × Coeffs)).card := Finset.card_image_le
      _ = Fintype.card Base * Fintype.card Coeffs := by
          rw [Finset.card_univ, Fintype.card_prod]
      _ = 2 ^ (d * (n - 24 * a) + 192 * a ^ 2) := by
          have hcardW : Fintype.card W = 2 ^ d := by
            simp only [W, F2, Fintype.card_fun, ZMod.card, Fintype.card_fin]
          have hcardBase : Fintype.card Base = (2 ^ d) ^ (n - 24 * a) := by
            simp only [Base, Fintype.card_fun, hcardW]
            congr 1
            have hsub_eq : Fintype.card {i : Fin n // i ∉ D} = (Finset.univ \ D).card := by
              rw [Fintype.card_subtype]
              congr 1
              ext i
              simp
            rw [hsub_eq, hcompl_card]
          have hcardCoeffs : Fintype.card Coeffs = (2 ^ (8 * a)) ^ (24 * a) := by
            simp only [Coeffs, F2, Fintype.card_fun, ZMod.card, Fintype.card_coe, hB, hDcard]
          rw [hcardBase, hcardCoeffs, ← pow_mul, ← pow_mul, ← pow_add]
          congr 1
          ring
  have hpairs_card : pairs.card ≤ 2 ^ (32 * a ^ 2 + 32 * a) := by
    have h1 : pairs.card ≤ ∑ T ∈ Finset.univ.powersetCard (32 * a),
        ((T.powersetCard (8 * a)).image fun B => (T, B)).card := Finset.card_biUnion_le
    have h2 : ∀ T ∈ (Finset.univ : Finset (Fin n)).powersetCard (32 * a),
        ((T.powersetCard (8 * a)).image fun B => (T, B)).card ≤ 2 ^ (32 * a) := by
      intro T hT
      have hTcard : T.card = 32 * a := (Finset.mem_powersetCard.mp hT).2
      calc ((T.powersetCard (8 * a)).image fun B => (T, B)).card
          ≤ (T.powersetCard (8 * a)).card := Finset.card_image_le
        _ ≤ T.powerset.card := Finset.card_le_card (fun S hS => Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hS).1)
        _ = 2 ^ (32 * a) := by rw [Finset.card_powerset, hTcard]
    have h3 : ((Finset.univ : Finset (Fin n)).powersetCard (32 * a)).card ≤ n ^ (32 * a) := by
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
      exact Nat.choose_le_pow _ _
    calc pairs.card
        ≤ ∑ T ∈ Finset.univ.powersetCard (32 * a), 2 ^ (32 * a) :=
          h1.trans (Finset.sum_le_sum h2)
      _ = ((Finset.univ : Finset (Fin n)).powersetCard (32 * a)).card * 2 ^ (32 * a) := by simp
      _ ≤ n ^ (32 * a) * 2 ^ (32 * a) := Nat.mul_le_mul_right _ h3
      _ = 2 ^ (32 * a ^ 2 + 32 * a) := by
          dsimp only [n]
          rw [← pow_mul, ← pow_add]
          congr 1
          ring
  have hbad_lt : badSet.card < (Finset.univ : Finset (Fin n → W)).card := by
    have htot : (Finset.univ : Finset (Fin n → W)).card = 2 ^ (d * n) := by
      simp only [Finset.card_univ, Fintype.card_fun, W, F2, ZMod.card, Fintype.card_fin, ← pow_mul]
    rw [htot]
    have hle1 : badSet.card ≤ pairs.card * 2 ^ (d * (n - 24 * a) + 192 * a ^ 2) := by
      calc badSet.card
          ≤ (pairs.biUnion badTB).card := Finset.card_le_card hsub_union
        _ ≤ ∑ p ∈ pairs, (badTB p).card := Finset.card_biUnion_le
        _ ≤ ∑ _p ∈ pairs, 2 ^ (d * (n - 24 * a) + 192 * a ^ 2) := Finset.sum_le_sum hcard_TB
        _ = pairs.card * 2 ^ (d * (n - 24 * a) + 192 * a ^ 2) := by simp
    have hle2 : badSet.card ≤ 2 ^ (32 * a ^ 2 + 32 * a + (d * (n - 24 * a) + 192 * a ^ 2)) := by
      rw [pow_add]
      exact hle1.trans (Nat.mul_le_mul_right _ hpairs_card)
    have hexp_lt : 32 * a ^ 2 + 32 * a + (d * (n - 24 * a) + 192 * a ^ 2) < d * n := by
      have hdn : d * (n - 24 * a) + d * (24 * a) = d * n := by
        rw [← Nat.mul_add, Nat.sub_add_cancel h24_le]
      have hd_val : d * (24 * a) = 768 * a ^ 2 := by dsimp only [d]; ring
      nlinarith
    exact lt_of_le_of_lt hle2 (Nat.pow_lt_pow_right (by decide : 1 < 2) hexp_lt)
  have hex : (Finset.univ \ badSet).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hsub : Finset.univ ⊆ badSet := Finset.sdiff_eq_empty_iff_subset.mp hemp
    have := Finset.card_le_card hsub
    omega
  obtain ⟨v, hv⟩ := hex
  have hnot : v ∉ badSet := (Finset.mem_sdiff.mp hv).2
  simp only [badSet, Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and, not_forall,
    not_not] at hnot
  exact ⟨v, fun T hT => by obtain ⟨I, h1, h2, h3⟩ := hnot T hT; exact ⟨I, h1, h2, h3⟩⟩

private lemma dot_surj_fiber_card {d : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (vecs : ι → (Fin d → F2)) (hli : LinearIndependent F2 vecs)
    (shift : ι → F2) (y : ι → F2) :
    (Finset.univ.filter (fun w : Fin d → F2 => (fun i => dotF w (vecs i) + shift i) = y)).card *
      2 ^ Fintype.card ι = 2 ^ d := by
  classical
  let W := Fin d → F2
  let eval : W →ₗ[F2] (ι → F2) := {
    toFun := fun w i => dotF w (vecs i)
    map_add' := fun w1 w2 => by
      funext i
      change ∑ j : Fin d, (w1 j + w2 j) * vecs i j =
        ∑ j : Fin d, w1 j * vecs i j + ∑ j : Fin d, w2 j * vecs i j
      simp only [add_mul, Finset.sum_add_distrib]
    map_smul' := fun c w => by
      funext i
      change ∑ j : Fin d, (c * w j) * vecs i j = c * ∑ j : Fin d, w j * vecs i j
      simp only [mul_assoc, Finset.mul_sum]
  }
  have hsurj : Function.Surjective eval := by
    intro target
    let S := Submodule.span F2 (Set.range vecs)
    let b := Module.Basis.span hli
    let φ : S →ₗ[F2] F2 := b.constr F2 target
    obtain ⟨g, hg⟩ := LinearMap.exists_extend φ
    let w : W := fun j => g (Pi.single j 1)
    refine ⟨w, ?_⟩
    funext i
    have hdot : ∀ z : W, dotF w z = g z := by
      intro z
      have hz : z = ∑ j : Fin d, z j • Pi.single j (1 : F2) := by
        funext k
        simp [Finset.sum_apply, Pi.single_apply]
      conv_rhs => rw [hz]
      rw [map_sum]
      unfold dotF
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]
    change dotF w (vecs i) = target i
    rw [hdot (vecs i)]
    have hmem : vecs i ∈ S := Submodule.subset_span ⟨i, rfl⟩
    have h1 := LinearMap.congr_fun hg ⟨vecs i, hmem⟩
    change g (vecs i) = φ ⟨vecs i, hmem⟩ at h1
    rw [h1]
    have hb : b i = ⟨vecs i, hmem⟩ := Module.Basis.span_apply hli i
    rw [← hb]
    exact Module.Basis.constr_basis b F2 target i
  have hfiber_eq : ∀ z : ι → F2,
      (Finset.univ.filter (fun w : W => eval w = z)).card =
        (Finset.univ.filter (fun w : W => eval w = 0)).card := by
    intro z
    obtain ⟨w0, hw0⟩ := hsurj z
    refine Finset.card_bij (fun w _ => w + w0)
      (fun w hw => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
        rw [map_add, hw, hw0]
        funext i
        change z i + z i = 0
        generalize hz : z i = t
        fin_cases t <;> rfl)
      (fun w1 _ w2 _ h => add_right_cancel h)
      (fun u hu => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
        refine ⟨u + w0, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [map_add, hu, hw0, zero_add]
        · funext j
          rw [Pi.add_apply, Pi.add_apply, add_assoc]
          have h2z : w0 j + w0 j = 0 := by generalize hw : w0 j = t; fin_cases t <;> rfl
          rw [h2z, add_zero])
  have hpart : ∑ z : ι → F2, (Finset.univ.filter (fun w : W => eval w = z)).card = 2 ^ d := by
    rw [← Finset.card_biUnion]
    · have hun : (Finset.univ : Finset (ι → F2)).biUnion
          (fun z => Finset.univ.filter (fun w : W => eval w = z)) = Finset.univ := by
        ext w
        simp
      rw [hun, Finset.card_univ]
      simp only [W, F2, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    · intro z1 _ z2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro w h1 h2
      simp only [Finset.mem_filter] at h1 h2
      exact hne (h1.2.symm.trans h2.2)
  have hsum_const : ∑ z : ι → F2, (Finset.univ.filter (fun w : W => eval w = z)).card =
      2 ^ Fintype.card ι * (Finset.univ.filter (fun w : W => eval w = 0)).card := by
    rw [Finset.sum_congr rfl (fun z _ => hfiber_eq z)]
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_fun, F2, ZMod.card]
  have hshift_eq : Finset.univ.filter (fun w : W => (fun i => dotF w (vecs i) + shift i) = y) =
      Finset.univ.filter (fun w : W => eval w = y + shift) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, eval, LinearMap.coe_mk, AddHom.coe_mk]
    constructor
    · intro h
      funext i
      have hi := congrFun h i
      have hadd := congrArg (· + shift i) hi
      have h2z : shift i + shift i = 0 := by generalize hs : shift i = t; fin_cases t <;> rfl
      rw [add_assoc, h2z, add_zero] at hadd
      exact hadd
    · intro h
      funext i
      have hi := congrFun h i
      rw [hi, Pi.add_apply, add_assoc]
      have h2z : shift i + shift i = 0 := by generalize hs : shift i = t; fin_cases t <;> rfl
      rw [h2z, add_zero]
  rw [hshift_eq, hfiber_eq (y + shift), mul_comm]
  rw [← hsum_const, hpart]

private lemma chernoff_16 {α : Type} [Fintype α] [DecidableEq α]
    (m k : ℕ) (hcard : Fintype.card α = 8 * m) :
    (Finset.univ.filter (fun z : α → F2 =>
      (Finset.univ.filter (fun i : α => z i ≠ 0)).card ≤ k)).card * 16 ^ (8 * m - k) ≤ 17 ^ (8 * m) := by
  classical
  let wt : (α → F2) → ℕ := fun z => (Finset.univ.filter (fun i : α => z i ≠ 0)).card
  let wBit : F2 → ℕ := fun b => if b = 0 then 16 else 1
  have hprod_eq : ∀ z : α → F2, ∏ i : α, wBit (z i) = 16 ^ (8 * m - wt z) := by
    intro z
    have hsplit : ∏ i : α, wBit (z i) =
        (∏ i ∈ Finset.univ.filter (fun i : α => z i = 0), wBit (z i)) *
        (∏ i ∈ Finset.univ.filter (fun i : α => z i ≠ 0), wBit (z i)) := by
      rw [← Finset.prod_union]
      · congr 1
        ext i
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        tauto
      · rw [Finset.disjoint_left]
        intro i h1 h2
        simp only [Finset.mem_filter] at h1 h2
        exact h2.2 h1.2
    rw [hsplit]
    have hp0 : ∏ i ∈ Finset.univ.filter (fun i : α => z i = 0), wBit (z i) =
        16 ^ (Finset.univ.filter (fun i : α => z i = 0)).card := by
      have : ∀ i ∈ Finset.univ.filter (fun i : α => z i = 0), wBit (z i) = 16 := by
        intro i hi
        simp only [Finset.mem_filter] at hi
        simp [wBit, hi.2]
      rw [Finset.prod_congr rfl this, Finset.prod_const]
    have hp1 : ∏ i ∈ Finset.univ.filter (fun i : α => z i ≠ 0), wBit (z i) = 1 := by
      have : ∀ i ∈ Finset.univ.filter (fun i : α => z i ≠ 0), wBit (z i) = 1 := by
        intro i hi
        simp only [Finset.mem_filter] at hi
        simp [wBit, hi.2]
      rw [Finset.prod_congr rfl this, Finset.prod_const_one]
    rw [hp0, hp1, mul_one]
    congr 1
    have hadd : (Finset.univ.filter (fun i : α => z i = 0)).card + wt z = 8 * m := by
      rw [← Finset.card_union_of_disjoint]
      · have hun : Finset.univ.filter (fun i : α => z i = 0) ∪
            Finset.univ.filter (fun i : α => z i ≠ 0) = Finset.univ := by
          ext i
          simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
          tauto
        rw [hun, Finset.card_univ, hcard]
      · rw [Finset.disjoint_left]
        intro i h1 h2
        simp only [Finset.mem_filter] at h1 h2
        exact h2.2 h1.2
    omega
  have hsum_all : ∑ z : α → F2, ∏ i : α, wBit (z i) = 17 ^ (8 * m) := by
    have h1 := (Fintype.prod_sum (fun (_ : α) (b : F2) => wBit b)).symm
    rw [h1]
    have h2 : ∑ b : F2, wBit b = 17 := by decide
    simp only [h2, Finset.prod_const, Finset.card_univ, hcard]
  let S := Finset.univ.filter (fun z : α → F2 => wt z ≤ k)
  calc S.card * 16 ^ (8 * m - k)
      = ∑ _z ∈ S, 16 ^ (8 * m - k) := by simp
    _ ≤ ∑ z ∈ S, ∏ i : α, wBit (z i) := by
        refine Finset.sum_le_sum fun z hz => ?_
        rw [hprod_eq z]
        have hle : wt z ≤ k := (Finset.mem_filter.mp hz).2
        exact Nat.pow_le_pow_right (by decide : 0 < 16) (by omega)
    _ ≤ ∑ z : α → F2, ∏ i : α, wBit (z i) :=
        Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
    _ = 17 ^ (8 * m) := hsum_all

private lemma chernoff_tail {α : Type} [Fintype α] [DecidableEq α]
    (m k : ℕ) (hm : 0 < m) (hcard : Fintype.card α = 8 * m) :
    (Finset.univ.filter (fun z : α → F2 =>
      (Finset.univ.filter (fun i : α => z i ≠ 0)).card ≤ k)).card < 2 ^ (m + 4 * k) := by
  have h1 := chernoff_16 (α := α) m k hcard
  have h17 : 17 ^ 8 < 2 * 16 ^ 8 := by decide
  have h17m : 17 ^ (8 * m) < 2 ^ m * 16 ^ (8 * m) := by
    rw [pow_mul, pow_mul, ← mul_pow]
    exact Nat.pow_lt_pow_left h17 (by omega)
  have h16k : 16 ^ k = 2 ^ (4 * k) := by
    rw [pow_mul]
    rfl
  by_cases hkm : k ≤ 8 * m
  · have hmul : (Finset.univ.filter (fun z : α → F2 =>
        (Finset.univ.filter (fun i : α => z i ≠ 0)).card ≤ k)).card * 16 ^ (8 * m) ≤
        17 ^ (8 * m) * 16 ^ k := by
      have : 16 ^ (8 * m) = 16 ^ (8 * m - k) * 16 ^ k := by
        rw [← pow_add, Nat.sub_add_cancel hkm]
      rw [this, ← mul_assoc]
      exact Nat.mul_le_mul_right _ h1
    have hlt : (Finset.univ.filter (fun z : α → F2 =>
        (Finset.univ.filter (fun i : α => z i ≠ 0)).card ≤ k)).card * 16 ^ (8 * m) <
        2 ^ (m + 4 * k) * 16 ^ (8 * m) := by
      have h2 : 17 ^ (8 * m) * 16 ^ k < (2 ^ m * 16 ^ (8 * m)) * 16 ^ k :=
        Nat.mul_lt_mul_of_pos_right h17m (by positivity)
      have h3 : (2 ^ m * 16 ^ (8 * m)) * 16 ^ k = 2 ^ (m + 4 * k) * 16 ^ (8 * m) := by
        rw [h16k, pow_add]; ring
      omega
    exact Nat.lt_of_mul_lt_mul_right hlt
  · have hle : (Finset.univ.filter (fun z : α → F2 =>
        (Finset.univ.filter (fun i : α => z i ≠ 0)).card ≤ k)).card ≤ 2 ^ (8 * m) := by
      calc _ ≤ (Finset.univ : Finset (α → F2)).card := Finset.card_filter_le _ _
        _ = 2 ^ (8 * m) := by simp [F2, hcard]
    have hexp : 8 * m < m + 4 * k := by omega
    exact lt_of_le_of_lt hle (Nat.pow_lt_pow_right (by decide : 1 < 2) hexp)

private lemma powersetCard_mem_count {α : Type} [DecidableEq α]
    (A : Finset α) (k : ℕ) (x : α) (hx : x ∈ A) :
    A.card * ((A.powersetCard k).filter (fun S => x ∈ S)).card = k * (A.powersetCard k).card := by
  have hsymm : ∀ y ∈ A,
      ((A.powersetCard k).filter (fun S => y ∈ S)).card =
        ((A.powersetCard k).filter (fun S => x ∈ S)).card := by
    intro y hy
    let σ := Equiv.swap x y
    refine Finset.card_bij (fun S _ => S.map σ.toEmbedding)
      (fun S hS => by
        simp only [Finset.mem_filter, Finset.mem_powersetCard] at hS ⊢
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · intro z hz
          simp only [Finset.mem_map, Equiv.coe_toEmbedding] at hz
          obtain ⟨w, hwS, rfl⟩ := hz
          by_cases hwx : w = x
          · subst hwx; simp [σ, hy]
          · by_cases hwy : w = y
            · subst hwy; simp [σ, hx]
            · simp [σ, Equiv.swap_apply_of_ne_of_ne hwx hwy, hS.1.1 hwS]
        · rw [Finset.card_map]; exact hS.1.2
        · simp only [Finset.mem_map, Equiv.coe_toEmbedding]
          exact ⟨y, hS.2, by simp [σ]⟩)
      (fun S1 _ S2 _ heq => by
        ext w
        have := Finset.ext_iff.mp heq (σ w)
        simp only [Finset.mem_map, Equiv.coe_toEmbedding, EmbeddingLike.apply_eq_iff_eq,
          exists_eq_right] at this
        exact this)
      (fun S hS => by
        simp only [Finset.mem_filter, Finset.mem_powersetCard] at hS
        refine ⟨S.map σ.toEmbedding, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_powersetCard]
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · intro z hz
            simp only [Finset.mem_map, Equiv.coe_toEmbedding] at hz
            obtain ⟨w, hwS, rfl⟩ := hz
            by_cases hwx : w = x
            · subst hwx; simp [σ, hy]
            · by_cases hwy : w = y
              · subst hwy; simp [σ, hx]
              · simp [σ, Equiv.swap_apply_of_ne_of_ne hwx hwy, hS.1.1 hwS]
          · rw [Finset.card_map]; exact hS.1.2
          · simp only [Finset.mem_map, Equiv.coe_toEmbedding]
            exact ⟨x, hS.2, by simp [σ]⟩
        · ext w
          simp only [Finset.mem_map, Equiv.coe_toEmbedding]
          constructor
          · rintro ⟨z, ⟨u, hu, rfl⟩, rfl⟩
            simpa [σ] using hu
          · intro hw
            exact ⟨σ w, ⟨w, hw, rfl⟩, by simp [σ]⟩)
  have hdouble : ∑ y ∈ A, ((A.powersetCard k).filter (fun S => y ∈ S)).card =
      ∑ S ∈ A.powersetCard k, S.card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun S hS => ?_
    have hSA : S ⊆ A := (Finset.mem_powersetCard.mp hS).1
    rw [← Finset.card_filter]
    congr 1
    ext y
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hSA h, h⟩⟩
  have hlhs : ∑ y ∈ A, ((A.powersetCard k).filter (fun S => y ∈ S)).card =
      A.card * ((A.powersetCard k).filter (fun S => x ∈ S)).card := by
    rw [Finset.sum_congr rfl hsymm]
    simp
  have hrhs : ∑ S ∈ A.powersetCard k, S.card = k * (A.powersetCard k).card := by
    have : ∀ S ∈ A.powersetCard k, S.card = k := fun S hS => (Finset.mem_powersetCard.mp hS).2
    rw [Finset.sum_congr rfl this]
    simp [mul_comm]
  rw [← hlhs, hdouble, hrhs]

private lemma fixed_S_bound (a h n d : ℕ) (ha : 16 ≤ a) (hh_pos : 0 < h) (hh_le : h ≤ n)
    (v : Fin n → (Fin d → F2)) (row col : Fin h ↪ Fin n) (sign : Fin h → F2)
    (Rset : Finset (Fin h)) (hR_card : h ≤ 2 * Rset.card)
    (I_of : Rset → Finset (Fin h))
    (hI_card : ∀ i : Rset, (I_of i).card = 8 * a)
    (hI_disj : ∀ (i : Rset) (j : Fin h), j ∈ I_of i → j ∉ Rset)
    (hI_li : ∀ i : Rset, LinearIndependent F2 (fun j : I_of i => v (col j.val))) :
    let W := Fin d → F2
    let testErr := fun (u : Fin n → W) (i j : Fin h) =>
      dotF (u (row i)) (v (col j)) + dotF (u (row j)) (v (col i)) ≠ sign i + sign j
    let errS := fun u : Fin n → W =>
      ∑ i ∈ Rset.attach, ((I_of i).filter (fun j => testErr u i.val j)).card
    (Finset.univ.filter (fun u : Fin n → W => errS u ≤ a * h / 8)).card *
      2 ^ (3 * a * h) < 2 ^ (d * n) := by
  intro W testErr errS
  classical
  let kMax := a * h / 8
  let Used : Finset (Fin n) := Rset.map row
  let Rest : Finset (Fin n) := Finset.univ \ Used
  have hUsed_card : Used.card = Rset.card := Finset.card_map row
  have hRest_card : Rest.card + Rset.card = n := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hUsed_card]
    have : Rset.card ≤ n := by
      calc Rset.card ≤ (Finset.univ : Finset (Fin h)).card := Finset.card_le_card (Finset.subset_univ _)
        _ = h := by simp
        _ ≤ n := hh_le
    omega
  let URest := Rest → W
  let UUsed := Rset → W
  let combine : URest × UUsed → (Fin n → W) := fun ⟨ur, uu⟩ x =>
    if hx : x ∈ Used then
      let i := Classical.choose (Finset.mem_map.mp hx)
      uu ⟨i, (Classical.choose_spec (Finset.mem_map.mp hx)).1⟩
    else ur ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx⟩⟩
  have hcombine_row : ∀ (ur : URest) (uu : UUsed) (i : Rset),
      combine (ur, uu) (row i.val) = uu i := by
    intro ur uu i
    have hmem : row i.val ∈ Used := Finset.mem_map.mpr ⟨i.val, i.property, rfl⟩
    dsimp only [combine]
    simp only [hmem, ↓reduceDIte]
    have hspec := Classical.choose_spec (Finset.mem_map.mp hmem)
    have heq : Classical.choose (Finset.mem_map.mp hmem) = i.val := row.injective hspec.2
    exact congrArg uu (Subtype.ext heq)
  have hcombine_notUsed : ∀ (ur : URest) (uu : UUsed) (x : Fin n) (hx : x ∉ Used),
      combine (ur, uu) x = ur ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx⟩⟩ := by
    intro ur uu x hx
    dsimp only [combine]
    simp only [hx, ↓reduceDIte]
  have htester_notUsed : ∀ (i : Rset) (j : I_of i), row j.val ∉ Used := by
    intro i j hmem
    rw [Finset.mem_map] at hmem
    obtain ⟨i', hi'R, heq⟩ := hmem
    have hj_eq : i' = j.val := row.injective heq
    subst hj_eq
    exact hI_disj i j.val j.property hi'R
  let Idx := (i : Rset) × I_of i
  have hIdx_card : Fintype.card Idx = 8 * (Rset.card * a) := by
    simp only [Idx, Fintype.card_sigma, Fintype.card_coe, hI_card, Finset.sum_const,
      Finset.card_univ, smul_eq_mul]
    ring
  have hper_ur : ∀ ur : URest,
      (Finset.univ.filter (fun uu : UUsed => errS (combine (ur, uu)) ≤ kMax)).card *
        2 ^ (3 * a * h) < 2 ^ (d * Rset.card) := by
    intro ur
    let shift (i : Rset) (j : I_of i) : F2 :=
      dotF (ur ⟨row j.val, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, htester_notUsed i j⟩⟩) (v (col i.val)) +
        (sign i.val + sign j.val)
    let Φ : UUsed → (Idx → F2) := fun uu p =>
      dotF (uu p.1) (v (col p.2.val)) + shift p.1 p.2
    have herr_eq_wt : ∀ uu : UUsed,
        errS (combine (ur, uu)) = (Finset.univ.filter (fun p : Idx => Φ uu p ≠ 0)).card := by
      intro uu
      dsimp only [errS]
      have h1 : (Finset.univ.filter (fun p : Idx => Φ uu p ≠ 0)).card =
          ∑ i : Rset, ((Finset.univ : Finset (I_of i)).filter (fun j => Φ uu ⟨i, j⟩ ≠ 0)).card := by
        rw [← Finset.card_sigma]
        congr 1
        ext p
        rcases p with ⟨i, j⟩
        rw [Finset.mem_filter, Finset.mem_sigma]
        simp
      rw [h1]
      have hsum_att : ∑ i ∈ Rset.attach,
            ((I_of i).filter (fun j => testErr (combine (ur, uu)) i.val j)).card =
          ∑ i : Rset,
            ((I_of i).filter (fun j => testErr (combine (ur, uu)) i.val j)).card := rfl
      rw [hsum_att]
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.card_bij (fun j hj => (⟨j, (Finset.mem_filter.mp hj).1⟩ : I_of i))
        (fun j hj => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
          dsimp only [Φ, shift, testErr] at hj ⊢
          rw [hcombine_row ur uu i, hcombine_notUsed ur uu (row j) (htester_notUsed i ⟨j, hj.1⟩)] at hj
          intro h0
          apply hj.2
          have hadd := congrArg (· + (sign i.val + sign j)) h0
          have h2z : (sign i.val + sign j) + (sign i.val + sign j) = 0 := by
            generalize hs : sign i.val + sign j = t; fin_cases t <;> rfl
          rw [add_assoc, add_assoc, h2z, add_zero, zero_add] at hadd
          exact hadd)
        (fun _ _ _ _ h => congrArg Subtype.val h)
        (fun j hj => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          refine ⟨j.val, Finset.mem_filter.mpr ⟨j.property, ?_⟩, Subtype.ext rfl⟩
          dsimp only [testErr]
          rw [hcombine_row ur uu i, hcombine_notUsed ur uu (row j.val) (htester_notUsed i j)]
          intro heq
          apply hj
          dsimp only [Φ, shift]
          rw [← add_assoc, heq]
          generalize hs : sign i.val + sign j.val = t; fin_cases t <;> rfl)
    have hfiber_Φ : ∀ z : Idx → F2,
        (Finset.univ.filter (fun uu : UUsed => Φ uu = z)).card * 2 ^ (8 * (Rset.card * a)) =
          2 ^ (d * Rset.card) := by
      intro z
      have hprod_fib : (Finset.univ.filter (fun uu : UUsed => Φ uu = z)).card =
          ∏ i : Rset, (Finset.univ.filter (fun w : W =>
            (fun j : I_of i => dotF w (v (col j.val)) + shift i j) = fun j => z ⟨i, j⟩)).card := by
        rw [← Fintype.card_piFinset]
        refine Finset.card_bij (fun uu _ => uu)
          (fun uu huu => by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at huu
            rw [Fintype.mem_piFinset]
            intro i
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            funext j
            exact congrFun huu ⟨i, j⟩)
          (fun _ _ _ _ h => h)
          (fun uu huu => by
            rw [Fintype.mem_piFinset] at huu
            refine ⟨uu, ?_, rfl⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            funext ⟨i, j⟩
            have hi := (Finset.mem_filter.mp (huu i)).2
            exact congrFun hi j)
      rw [hprod_fib]
      have hmul_prod : (∏ i : Rset, (Finset.univ.filter (fun w : W =>
            (fun j : I_of i => dotF w (v (col j.val)) + shift i j) = fun j => z ⟨i, j⟩)).card) *
          (∏ _i : Rset, 2 ^ (8 * a)) = ∏ _i : Rset, 2 ^ d := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        have hf := dot_surj_fiber_card (fun j : I_of i => v (col j.val)) (hI_li i) (shift i) (fun j => z ⟨i, j⟩)
        simp only [Fintype.card_coe, hI_card] at hf
        exact hf
      have hp1 : ∏ _i : Rset, 2 ^ (8 * a) = 2 ^ (8 * (Rset.card * a)) := by
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_coe, ← pow_mul]
        congr 1; ring
      have hp2 : ∏ _i : Rset, 2 ^ d = 2 ^ (d * Rset.card) := by
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_coe, ← pow_mul]
      rw [← hp1, ← hp2]
      exact hmul_prod
    let Zlow : Finset (Idx → F2) :=
      Finset.univ.filter (fun z => (Finset.univ.filter (fun p : Idx => z p ≠ 0)).card ≤ kMax)
    have hpart_uu : (Finset.univ.filter (fun uu : UUsed => errS (combine (ur, uu)) ≤ kMax)).card =
        ∑ z ∈ Zlow, (Finset.univ.filter (fun uu : UUsed => Φ uu = z)).card := by
      rw [← Finset.card_biUnion]
      · congr 1
        ext uu
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Zlow]
        constructor
        · intro h
          exact ⟨Φ uu, herr_eq_wt uu ▸ h, rfl⟩
        · rintro ⟨z, hz, rfl⟩
          rwa [herr_eq_wt uu]
      · intro z1 _ z2 _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro uu h1 h2
        simp only [Finset.mem_filter] at h1 h2
        exact hne (h1.2.symm.trans h2.2)
    have hR_pos : 0 < Rset.card * a := by
      have h2 : 0 < Rset.card := by omega
      exact Nat.mul_pos h2 (by omega)
    have htail : Zlow.card < 2 ^ (Rset.card * a + 4 * kMax) :=
      chernoff_tail (Rset.card * a) kMax hR_pos hIdx_card
    have hexp_le : Rset.card * a + 4 * kMax + 3 * a * h ≤ 8 * (Rset.card * a) := by
      have h2 : 4 * kMax ≤ a * h / 2 := by dsimp only [kMax]; omega
      have h3 : 7 * (a * h) ≤ 14 * (Rset.card * a) := by nlinarith
      have h4 : 3 * a * h = 3 * (a * h) := by ring
      omega
    have hmul_eq : (Finset.univ.filter (fun uu : UUsed => errS (combine (ur, uu)) ≤ kMax)).card *
        2 ^ (8 * (Rset.card * a)) = Zlow.card * 2 ^ (d * Rset.card) := by
      rw [hpart_uu, Finset.sum_mul]
      rw [Finset.sum_congr rfl (fun z _ => hfiber_Φ z)]
      simp
    have hlt_pow : Zlow.card * 2 ^ (3 * a * h) < 2 ^ (8 * (Rset.card * a)) := by
      calc Zlow.card * 2 ^ (3 * a * h)
          < 2 ^ (Rset.card * a + 4 * kMax) * 2 ^ (3 * a * h) :=
            Nat.mul_lt_mul_of_pos_right htail (by positivity)
        _ = 2 ^ (Rset.card * a + 4 * kMax + 3 * a * h) := (pow_add _ _ _).symm
        _ ≤ 2 ^ (8 * (Rset.card * a)) := Nat.pow_le_pow_right (by decide : 0 < 2) hexp_le
    have hfinal_mul : (Finset.univ.filter (fun uu : UUsed => errS (combine (ur, uu)) ≤ kMax)).card *
        2 ^ (3 * a * h) * 2 ^ (8 * (Rset.card * a)) <
        2 ^ (d * Rset.card) * 2 ^ (8 * (Rset.card * a)) := by
      calc _ = ((Finset.univ.filter (fun uu : UUsed => errS (combine (ur, uu)) ≤ kMax)).card *
              2 ^ (8 * (Rset.card * a))) * 2 ^ (3 * a * h) := by ring
        _ = Zlow.card * 2 ^ (d * Rset.card) * 2 ^ (3 * a * h) := by rw [hmul_eq]
        _ = 2 ^ (d * Rset.card) * (Zlow.card * 2 ^ (3 * a * h)) := by ring
        _ < 2 ^ (d * Rset.card) * 2 ^ (8 * (Rset.card * a)) :=
            Nat.mul_lt_mul_of_pos_left hlt_pow (by positivity)
    exact Nat.lt_of_mul_lt_mul_right hfinal_mul
  have hsplit_u : (Finset.univ.filter (fun u : Fin n → W => errS u ≤ kMax)).card =
      ∑ ur : URest, (Finset.univ.filter (fun uu : UUsed => errS (combine (ur, uu)) ≤ kMax)).card := by
    rw [← Finset.card_sigma]
    refine Finset.card_bij (fun u _ =>
        ⟨fun x => u x.val, fun i => u (row i.val)⟩)
      (fun u hu => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
        simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and]
        have hcomb : combine (fun x => u x.val, fun i => u (row i.val)) = u := by
          funext x
          by_cases hx : x ∈ Used
          · obtain ⟨i, hiR, rfl⟩ := Finset.mem_map.mp hx
            exact hcombine_row (fun x => u x.val) (fun i => u (row i.val)) ⟨i, hiR⟩
          · exact hcombine_notUsed (fun x => u x.val) (fun i => u (row i.val)) x hx
        rwa [hcomb])
      (fun u1 _ u2 _ heq => by
        funext x
        by_cases hx : x ∈ Used
        · obtain ⟨i, hiR, rfl⟩ := Finset.mem_map.mp hx
          have h2 := congrArg (fun p : (ur : URest) × UUsed => p.2 ⟨i, hiR⟩) heq
          exact h2
        · have h1 := congrArg (fun p : (ur : URest) × UUsed =>
            p.1 ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx⟩⟩) heq
          exact h1)
      (fun p hp => by
        simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and] at hp
        refine ⟨combine (p.1, p.2), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩, ?_⟩
        refine Sigma.ext ?_ (heq_of_eq ?_)
        · funext x
          exact hcombine_notUsed p.1 p.2 x.val (Finset.mem_sdiff.mp x.property).2
        · funext i
          exact hcombine_row p.1 p.2 i)
  have hURest_pos : (Finset.univ : Finset URest).Nonempty := Finset.univ_nonempty
  calc (Finset.univ.filter (fun u : Fin n → W => errS u ≤ kMax)).card * 2 ^ (3 * a * h)
      = ∑ ur : URest, (Finset.univ.filter (fun uu : UUsed => errS (combine (ur, uu)) ≤ kMax)).card *
          2 ^ (3 * a * h) := by rw [hsplit_u, Finset.sum_mul]
    _ < ∑ _ur : URest, 2 ^ (d * Rset.card) := Finset.sum_lt_sum_of_nonempty hURest_pos (fun ur _ => hper_ur ur)
    _ = Fintype.card URest * 2 ^ (d * Rset.card) := by simp
    _ = 2 ^ (d * n) := by
        have hcardUR : Fintype.card URest = 2 ^ (d * Rest.card) := by
          simp only [URest, W, F2, Fintype.card_fun, ZMod.card, Fintype.card_fin, Fintype.card_coe, ← pow_mul]
        rw [hcardUR, ← pow_add, ← Nat.mul_add, hRest_card]

private lemma bad_u_count_bound (a : ℕ) (ha : 16 ≤ a)
    (v : Fin (2 ^ a) → (Fin (32 * a) → F2))
    (hv : ∀ T : Finset (Fin (2 ^ a)), T.card = 32 * a →
      ∃ I : Finset (Fin (2 ^ a)), I ⊆ T ∧ I.card = 8 * a ∧
        LinearIndependent F2 (fun x : I => v x.val))
    (row col : Fin (2 ^ a / 2) ↪ Fin (2 ^ a))
    (q : ℕ) (hq : 256 * a * 3 ^ q ≤ 2 ^ a)
    (color : Fin (2 ^ a / 2) → Fin (3 ^ q))
    (sign : Fin (2 ^ a / 2) → F2) :
    let n := 2 ^ a
    let h := n / 2
    let d := 32 * a
    let W := Fin d → F2
    let bad := fun u : Fin n → W =>
      ((Finset.univ : Finset (Fin h × Fin h)).filter (fun z =>
        z.1 < z.2 ∧ color z.1 = color z.2 ∧
          dotF (u (row z.1)) (v (col z.2)) + dotF (u (row z.2)) (v (col z.1)) ≠
            sign z.1 + sign z.2)).card
    (Finset.univ.filter (fun u : Fin n → W => 4096 * 3 ^ q * bad u ≤ h ^ 2)).card *
      2 ^ (3 * a * h) < 2 * 2 ^ (d * n) := by
  intro n h d W bad
  classical
  let C := 3 ^ q
  have hC_pos : 0 < C := by positivity
  have hn_even : 2 * h = n := by
    have : 2 ^ a = 2 * 2 ^ (a - 1) := by
      cases a with
      | zero => omega
      | succ k => simp [pow_succ, mul_comm]
    dsimp only [h, n]
    omega
  have hh_pos : 0 < h := by
    have : 0 < n := by positivity
    omega
  have h128 : 128 * a * C ≤ h := by
    have h2 : 2 * (128 * a * C) = 256 * a * 3 ^ q := by dsimp only [C]; ring
    omega
  let A : Fin C → Finset (Fin h) := fun c => Finset.univ.filter (fun i => color i = c)
  let K : Finset (Fin C) := Finset.univ.filter (fun c => h ≤ 4 * C * (A c).card)
  have hK_size : ∀ c ∈ K, 32 * a ≤ (A c).card := by
    intro c hc
    have h1 : h ≤ 4 * C * (A c).card := (Finset.mem_filter.mp hc).2
    nlinarith
  let L : Finset (Fin h) := Finset.univ.filter (fun i => color i ∈ K)
  have hL_card : 3 * h ≤ 4 * L.card := by
    have hsmall : ∑ c ∈ Finset.univ \ K, (A c).card = (Finset.univ \ L).card := by
      rw [← Finset.card_biUnion]
      · congr 1
        ext i
        simp only [Finset.mem_biUnion, Finset.mem_sdiff, Finset.mem_univ, true_and, A, L,
          Finset.mem_filter]
        constructor
        · rintro ⟨c, hc, hci⟩
          rw [hci]
          exact hc
        · intro hi
          exact ⟨color i, hi, rfl⟩
      · intro c1 _ c2 _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro i h1 h2
        simp only [A, Finset.mem_filter] at h1 h2
        exact hne (h1.2.symm.trans h2.2)
    have h4small : 4 * C * (Finset.univ \ L).card ≤ C * h := by
      rw [← hsmall, Finset.mul_sum]
      calc ∑ c ∈ Finset.univ \ K, 4 * C * (A c).card
          ≤ ∑ _c ∈ Finset.univ \ K, h := by
            refine Finset.sum_le_sum fun c hc => ?_
            have hnot : c ∉ K := (Finset.mem_sdiff.mp hc).2
            simp only [K, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hnot
            omega
        _ = (Finset.univ \ K).card * h := by simp
        _ ≤ C * h := by
            apply Nat.mul_le_mul_right
            calc (Finset.univ \ K).card ≤ (Finset.univ : Finset (Fin C)).card :=
                  Finset.card_le_card Finset.sdiff_subset
              _ = C := by simp
    have hsmall_le : 4 * (Finset.univ \ L).card ≤ h := by nlinarith
    have hadd : L.card + (Finset.univ \ L).card = h := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
      have : L.card ≤ h := by
        calc L.card ≤ (Finset.univ : Finset (Fin h)).card := Finset.card_le_card (Finset.subset_univ _)
          _ = h := by simp
      omega
    omega
  let Ωc : K → Finset (Finset (Fin h)) := fun c => (A c.val).powersetCard (32 * a)
  have hΩc_pos : ∀ c : K, 0 < (Ωc c).card := by
    intro c
    rw [Finset.card_pos]
    obtain ⟨S, hSA, hSc⟩ := Finset.exists_subset_card_eq (hK_size c.val c.property)
    exact ⟨S, Finset.mem_powersetCard.mpr ⟨hSA, hSc⟩⟩
  let Ω := ∀ c : K, {S : Finset (Fin h) // S ∈ Ωc c}
  have hΩ_pos : 0 < Fintype.card Ω := by
    simp only [Ω, Fintype.card_pi, Fintype.card_coe]
    exact Finset.prod_pos fun c _ => hΩc_pos c
  let testers (S : Ω) : Finset (Fin h) := Finset.univ.biUnion fun c : K => (S c).val
  have htesters_sub : ∀ S : Ω, testers S ⊆ L := by
    intro S i hi
    simp only [testers, Finset.mem_biUnion, Finset.mem_univ, true_and] at hi
    obtain ⟨c, hic⟩ := hi
    have hsub : (S c).val ⊆ A c.val := (Finset.mem_powersetCard.mp (S c).property).1
    have hci : color i = c.val := (Finset.mem_filter.mp (hsub hic)).2
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and, hci]
    exact c.property
  have htesters_card : ∀ S : Ω, (testers S).card = K.card * (32 * a) := by
    intro S
    rw [Finset.card_biUnion]
    · have hc : ∀ c : K, (S c).val.card = 32 * a := fun c =>
        (Finset.mem_powersetCard.mp (S c).property).2
      simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul]
    · intro c1 _ c2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro i h1 h2
      have h1' : color i = c1.val :=
        (Finset.mem_filter.mp ((Finset.mem_powersetCard.mp (S c1).property).1 h1)).2
      have h2' : color i = c2.val :=
        (Finset.mem_filter.mp ((Finset.mem_powersetCard.mp (S c2).property).1 h2)).2
      exact hne (Subtype.ext (h1'.symm.trans h2'))
  let R (S : Ω) : Finset (Fin h) := L \ testers S
  have hR_card : ∀ S : Ω, h ≤ 2 * (R S).card := by
    intro S
    have hK_le : K.card ≤ C := by
      calc K.card ≤ (Finset.univ : Finset (Fin C)).card := Finset.card_le_card (Finset.subset_univ _)
        _ = C := by simp
    have hT_le : 4 * (testers S).card ≤ h := by
      rw [htesters_card S]
      nlinarith
    have hR_eq : (R S).card + (testers S).card = L.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (htesters_sub S)]
      have : (testers S).card ≤ L.card := Finset.card_le_card (htesters_sub S)
      omega
    omega
  have hex_I : ∀ (S : Ω) (c : K),
      ∃ I : Finset (Fin h), I ⊆ (S c).val ∧ I.card = 8 * a ∧
        LinearIndependent F2 (fun j : I => v (col j.val)) := by
    intro S c
    have hScard : ((S c).val.map col).card = 32 * a := by
      rw [Finset.card_map]
      exact (Finset.mem_powersetCard.mp (S c).property).2
    obtain ⟨I', hI'sub, hI'card, hI'li⟩ := hv ((S c).val.map col) hScard
    let I : Finset (Fin h) := (S c).val.filter (fun j => col j ∈ I')
    have hImap : I.map col = I' := by
      ext y
      simp only [I, Finset.mem_map, Finset.mem_filter]
      constructor
      · rintro ⟨j, ⟨_, hjI'⟩, rfl⟩; exact hjI'
      · intro hy
        have hyS := hI'sub hy
        rw [Finset.mem_map] at hyS
        obtain ⟨j, hjS, rfl⟩ := hyS
        exact ⟨j, ⟨hjS, hy⟩, rfl⟩
    have hIcard : I.card = 8 * a := by
      rw [← Finset.card_map col, hImap, hI'card]
    have hIli : LinearIndependent F2 (fun j : I => v (col j.val)) := by
      let f : I → I' := fun j => ⟨col j.val, (Finset.mem_filter.mp j.property).2⟩
      have hfinj : Function.Injective f := fun j1 j2 heq =>
        Subtype.ext (col.injective (congrArg Subtype.val heq))
      exact hI'li.comp f hfinj
    exact ⟨I, Finset.filter_subset _ _, hIcard, hIli⟩
  let I_of (S : Ω) (c : K) : Finset (Fin h) := Classical.choose (hex_I S c)
  have hI_sub : ∀ S c, I_of S c ⊆ (S c).val := fun S c => (Classical.choose_spec (hex_I S c)).1
  have hI_card : ∀ S c, (I_of S c).card = 8 * a := fun S c => (Classical.choose_spec (hex_I S c)).2.1
  have hI_li : ∀ S c, LinearIndependent F2 (fun j : I_of S c => v (col j.val)) :=
    fun S c => (Classical.choose_spec (hex_I S c)).2.2
  let testErr (u : Fin n → W) (i j : Fin h) : Prop :=
    dotF (u (row i)) (v (col j)) + dotF (u (row j)) (v (col i)) ≠ sign i + sign j
  let errS (S : Ω) (u : Fin n → W) : ℕ :=
    ∑ i ∈ (R S).attach,
      ((I_of S ⟨color i.val, (Finset.mem_filter.mp (Finset.mem_sdiff.mp i.property).1).2⟩).filter
        (fun j => testErr u i.val j)).card
  let errSFull (S : Ω) (u : Fin n → W) : ℕ :=
    ∑ i ∈ (R S).attach,
      (((S ⟨color i.val, (Finset.mem_filter.mp (Finset.mem_sdiff.mp i.property).1).2⟩).val).filter
        (fun j => testErr u i.val j)).card
  have herr_le_full : ∀ S u, errS S u ≤ errSFull S u := by
    intro S u
    refine Finset.sum_le_sum fun i _ => ?_
    exact Finset.card_le_card (Finset.filter_subset_filter _ (hI_sub S _))
  let badPairs (u : Fin n → W) : Finset (Fin h × Fin h) :=
    Finset.univ.filter (fun z => z.1 < z.2 ∧ color z.1 = color z.2 ∧ testErr u z.1 z.2)
  have hsum_full_le : ∀ u : Fin n → W,
      h * ∑ S : Ω, errSFull S u ≤ 256 * a * C * bad u * Fintype.card Ω := by
    intro u
    have herr_decomp : ∀ S : Ω, errSFull S u ≤
        ∑ z ∈ badPairs u,
          if hc : color z.1 ∈ K then
            if (z.1 ∈ (S ⟨color z.1, hc⟩).val ∧ z.2 ∉ (S ⟨color z.1, hc⟩).val) ∨
               (z.2 ∈ (S ⟨color z.1, hc⟩).val ∧ z.1 ∉ (S ⟨color z.1, hc⟩).val)
            then 1 else 0
          else 0 := by
      intro S
      let Eset : Finset (Fin h × Fin h) :=
        (R S).attach.biUnion fun i =>
          (((S ⟨color i.val, (Finset.mem_filter.mp (Finset.mem_sdiff.mp i.property).1).2⟩).val).filter
            (fun j => testErr u i.val j)).image (fun j => (i.val, j))
      have hEcard : errSFull S u = Eset.card := by
        rw [Finset.card_biUnion]
        · refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.card_image_of_injective _ (fun j1 j2 h => congrArg Prod.snd h)]
        · intro i1 _ i2 _ hne
          change Disjoint _ _
          rw [Finset.disjoint_left]
          intro p h1 h2
          simp only [Finset.mem_image] at h1 h2
          obtain ⟨j1, _, rfl⟩ := h1
          obtain ⟨j2, _, heq⟩ := h2
          exact hne (Subtype.ext (congrArg Prod.fst heq).symm)
      rw [hEcard]
      let target : Finset (Fin h × Fin h) :=
        (badPairs u).filter (fun z =>
          ∃ hc : color z.1 ∈ K,
            (z.1 ∈ (S ⟨color z.1, hc⟩).val ∧ z.2 ∉ (S ⟨color z.1, hc⟩).val) ∨
            (z.2 ∈ (S ⟨color z.1, hc⟩).val ∧ z.1 ∉ (S ⟨color z.1, hc⟩).val))
      have htarget_eq : target.card =
          ∑ z ∈ badPairs u,
            if hc : color z.1 ∈ K then
              if (z.1 ∈ (S ⟨color z.1, hc⟩).val ∧ z.2 ∉ (S ⟨color z.1, hc⟩).val) ∨
                 (z.2 ∈ (S ⟨color z.1, hc⟩).val ∧ z.1 ∉ (S ⟨color z.1, hc⟩).val)
              then 1 else 0
            else 0 := by
        rw [Finset.card_filter]
        refine Finset.sum_congr rfl fun z _ => ?_
        by_cases hc : color z.1 ∈ K
        · simp only [hc, ↓reduceDIte, exists_true_left]
        · simp only [hc, ↓reduceDIte]
          exact ite_eq_right_iff.mpr (fun ⟨h, _⟩ => False.elim h)
      rw [← htarget_eq]
      let orient : Fin h × Fin h → Fin h × Fin h := fun p => if p.1 < p.2 then p else (p.2, p.1)
      have hsub_t : Eset.image orient ⊆ target := by
        intro z hz
        simp only [Finset.mem_image, Eset, Finset.mem_biUnion, Finset.mem_attach, true_and,
          Finset.mem_filter] at hz
        obtain ⟨p, ⟨i, j, ⟨hjS, hjerr⟩, rfl⟩, rfl⟩ := hz
        have hiR : i.val ∈ R S := i.property
        have hiL : i.val ∈ L := (Finset.mem_sdiff.mp hiR).1
        have hiNotT : i.val ∉ testers S := (Finset.mem_sdiff.mp hiR).2
        have hci : color i.val ∈ K := (Finset.mem_filter.mp hiL).2
        have hjT : j ∈ testers S :=
          Finset.mem_biUnion.mpr ⟨⟨color i.val, hci⟩, Finset.mem_univ _, hjS⟩
        have hij_ne : i.val ≠ j := fun heq => hiNotT (heq ▸ hjT)
        have hcj : color j = color i.val := by
          have hsubA := (Finset.mem_powersetCard.mp (S ⟨color i.val, hci⟩).property).1 hjS
          exact (Finset.mem_filter.mp hsubA).2
        have hiNotS : i.val ∉ (S ⟨color i.val, hci⟩).val := fun h =>
          hiNotT (Finset.mem_biUnion.mpr ⟨⟨color i.val, hci⟩, Finset.mem_univ _, h⟩)
        dsimp only [orient]
        split_ifs with hlt
        · simp only [target, badPairs, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨⟨hlt, hcj.symm, hjerr⟩, hci, Or.inr ⟨hjS, hiNotS⟩⟩
        · have hgt : j < i.val := lt_of_le_of_ne (not_lt.mp hlt) hij_ne.symm
          have herr_sym : testErr u j i.val := by
            dsimp only [testErr] at hjerr ⊢
            rw [add_comm (dotF (u (row j)) (v (col i.val))), add_comm (sign j)]
            exact hjerr
          simp only [target, badPairs, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨⟨hgt, hcj, herr_sym⟩, hcj.symm ▸ hci, ?_⟩
          have hceq : (⟨color j, hcj.symm ▸ hci⟩ : K) = ⟨color i.val, hci⟩ := Subtype.ext hcj
          rw [hceq]
          exact Or.inl ⟨hjS, hiNotS⟩
      have hinj_orient : Set.InjOn orient (Eset : Set (Fin h × Fin h)) := by
        intro p1 hp1 p2 hp2 heq
        simp only [Finset.mem_coe, Eset, Finset.mem_biUnion, Finset.mem_attach, true_and,
          Finset.mem_image, Finset.mem_filter] at hp1 hp2
        obtain ⟨i1, j1, ⟨hj1S, _⟩, rfl⟩ := hp1
        obtain ⟨i2, j2, ⟨hj2S, _⟩, rfl⟩ := hp2
        have h1_notT : i1.val ∉ testers S := (Finset.mem_sdiff.mp i1.property).2
        have h2_notT : i2.val ∉ testers S := (Finset.mem_sdiff.mp i2.property).2
        have h1_inT : j1 ∈ testers S := Finset.mem_biUnion.mpr ⟨_, Finset.mem_univ _, hj1S⟩
        have h2_inT : j2 ∈ testers S := Finset.mem_biUnion.mpr ⟨_, Finset.mem_univ _, hj2S⟩
        dsimp only [orient] at heq
        split_ifs at heq with h1 h2
        · exact heq
        · have : i1.val = j2 := congrArg Prod.fst heq
          exact absurd (this ▸ h2_inT) h1_notT
        · have : j1 = i2.val := congrArg Prod.fst heq
          exact absurd (this ▸ h1_inT) h2_notT
        · exact Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq)
      calc Eset.card
          = (Eset.image orient).card := (Finset.card_image_of_injOn hinj_orient).symm
        _ ≤ target.card := Finset.card_le_card hsub_t
    have hpair_avg : ∀ z ∈ badPairs u,
        h * ∑ S : Ω,
          (if hc : color z.1 ∈ K then
            if (z.1 ∈ (S ⟨color z.1, hc⟩).val ∧ z.2 ∉ (S ⟨color z.1, hc⟩).val) ∨
               (z.2 ∈ (S ⟨color z.1, hc⟩).val ∧ z.1 ∉ (S ⟨color z.1, hc⟩).val)
            then 1 else 0
          else 0) ≤ 256 * a * C * Fintype.card Ω := by
      intro z hz
      by_cases hc : color z.1 ∈ K
      · simp only [hc, ↓reduceDIte]
        let c0 : K := ⟨color z.1, hc⟩
        have hz1A : z.1 ∈ A c0.val := Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
        have hz2A : z.2 ∈ A c0.val :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2.2.1.symm⟩
        have hsum_le : ∑ S : Ω,
            (if (z.1 ∈ (S c0).val ∧ z.2 ∉ (S c0).val) ∨ (z.2 ∈ (S c0).val ∧ z.1 ∉ (S c0).val)
              then 1 else 0) ≤
            (Finset.univ.filter (fun S : Ω => z.1 ∈ (S c0).val)).card +
            (Finset.univ.filter (fun S : Ω => z.2 ∈ (S c0).val)).card := by
          rw [← Finset.card_filter]
          calc _ ≤ (Finset.univ.filter (fun S : Ω => z.1 ∈ (S c0).val) ∪
                Finset.univ.filter (fun S : Ω => z.2 ∈ (S c0).val)).card := by
                apply Finset.card_le_card
                intro S hS
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hS ⊢
                tauto
            _ ≤ _ := Finset.card_union_le _ _
        have hproj_card : ∀ w ∈ A c0.val,
            (Finset.univ.filter (fun S : Ω => w ∈ (S c0).val)).card * (Ωc c0).card =
              ((Ωc c0).filter (fun T => w ∈ T)).card * Fintype.card Ω := by
          intro w _
          let Rest := ∀ c : {c : K // c ≠ c0}, {T : Finset (Fin h) // T ∈ Ωc c.val}
          let eqv : Ω ≃ {T // T ∈ Ωc c0} × Rest := {
            toFun := fun S => (S c0, fun c => S c.val)
            invFun := fun p c => if h : c = c0 then h ▸ p.1 else p.2 ⟨c, h⟩
            left_inv := fun S => by
              funext c
              by_cases h : c = c0
              · subst h; simp
              · simp [h]
            right_inv := fun p => Prod.ext (by simp) (by funext c; simp [c.property])
          }
          have hcardΩ : Fintype.card Ω = (Ωc c0).card * Fintype.card Rest := by
            rw [Fintype.card_congr eqv, Fintype.card_prod, Fintype.card_coe]
          have hcardF : (Finset.univ.filter (fun S : Ω => w ∈ (S c0).val)).card =
              ((Ωc c0).filter (fun T => w ∈ T)).card * Fintype.card Rest := by
            have h1 : (Finset.univ.filter (fun S : Ω => w ∈ (S c0).val)).card =
                ((Finset.univ.filter (fun T : {T // T ∈ Ωc c0} => w ∈ T.val)) ×ˢ
                  (Finset.univ : Finset Rest)).card := by
              refine Finset.card_bij (fun S _ => eqv S)
                (fun S hS => by
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
                  exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS⟩,
                    Finset.mem_univ _⟩)
                (fun _ _ _ _ h => eqv.injective h)
                (fun p hp => by
                  obtain ⟨hp1, _⟩ := Finset.mem_product.mp hp
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp1
                  refine ⟨eqv.symm p, ?_, eqv.apply_symm_apply p⟩
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                  have : (eqv (eqv.symm p)).1 = p.1 := congrArg Prod.fst (eqv.apply_symm_apply p)
                  change w ∈ ((eqv (eqv.symm p)).1).val
                  rw [this]
                  exact hp1)
            rw [h1, Finset.card_product, Finset.card_univ]
            congr 1
            refine Finset.card_bij (fun T _ => T.val)
              (fun T hT => Finset.mem_filter.mpr ⟨T.property, (Finset.mem_filter.mp hT).2⟩)
              (fun _ _ _ _ h => Subtype.ext h)
              (fun T hT => ⟨⟨T, (Finset.mem_filter.mp hT).1⟩,
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hT).2⟩, rfl⟩)
          rw [hcardF, hcardΩ]
          ring
        have h1w : ∀ w ∈ A c0.val,
            (A c0.val).card * (Finset.univ.filter (fun S : Ω => w ∈ (S c0).val)).card =
              (32 * a) * Fintype.card Ω := by
          intro w hw
          have hpc := powersetCard_mem_count (A c0.val) (32 * a) w hw
          have hpj := hproj_card w hw
          have hpos : 0 < (Ωc c0).card := hΩc_pos c0
          have hmul : (A c0.val).card * (Finset.univ.filter (fun S : Ω => w ∈ (S c0).val)).card *
              (Ωc c0).card = (32 * a) * Fintype.card Ω * (Ωc c0).card := by
            calc _ = (A c0.val).card * ((Finset.univ.filter (fun S : Ω => w ∈ (S c0).val)).card * (Ωc c0).card) := by ring
              _ = (A c0.val).card * (((Ωc c0).filter (fun T => w ∈ T)).card * Fintype.card Ω) := by rw [hpj]
              _ = ((A c0.val).card * ((Ωc c0).filter (fun T => w ∈ T)).card) * Fintype.card Ω := by ring
              _ = ((32 * a) * (Ωc c0).card) * Fintype.card Ω := by rw [hpc]
              _ = (32 * a) * Fintype.card Ω * (Ωc c0).card := by ring
          exact Nat.eq_of_mul_eq_mul_right hpos hmul
        have hA_ge : h ≤ 4 * C * (A c0.val).card := (Finset.mem_filter.mp hc).2
        have h1 := h1w z.1 hz1A
        have h2 := h1w z.2 hz2A
        calc h * ∑ S : Ω, _
            ≤ (4 * C * (A c0.val).card) *
                ((Finset.univ.filter (fun S : Ω => z.1 ∈ (S c0).val)).card +
                 (Finset.univ.filter (fun S : Ω => z.2 ∈ (S c0).val)).card) :=
              Nat.mul_le_mul hA_ge hsum_le
          _ = 4 * C * ((A c0.val).card * (Finset.univ.filter (fun S : Ω => z.1 ∈ (S c0).val)).card +
                (A c0.val).card * (Finset.univ.filter (fun S : Ω => z.2 ∈ (S c0).val)).card) := by ring
          _ = 4 * C * ((32 * a) * Fintype.card Ω + (32 * a) * Fintype.card Ω) := by rw [h1, h2]
          _ = 256 * a * C * Fintype.card Ω := by ring
      · simp [hc]
    calc h * ∑ S : Ω, errSFull S u
        ≤ h * ∑ S : Ω, ∑ z ∈ badPairs u,
            (if hc : color z.1 ∈ K then
              if (z.1 ∈ (S ⟨color z.1, hc⟩).val ∧ z.2 ∉ (S ⟨color z.1, hc⟩).val) ∨
                 (z.2 ∈ (S ⟨color z.1, hc⟩).val ∧ z.1 ∉ (S ⟨color z.1, hc⟩).val)
              then 1 else 0
            else 0) := Nat.mul_le_mul_left h (Finset.sum_le_sum fun S _ => herr_decomp S)
      _ = ∑ z ∈ badPairs u, h * ∑ S : Ω, _ := by rw [Finset.sum_comm, Finset.mul_sum]
      _ ≤ ∑ _z ∈ badPairs u, (256 * a * C * Fintype.card Ω) := Finset.sum_le_sum hpair_avg
      _ = (badPairs u).card * (256 * a * C * Fintype.card Ω) := by simp
      _ = 256 * a * C * bad u * Fintype.card Ω := by
          change bad u * (256 * a * C * Fintype.card Ω) = _
          ring
  let kMax := a * h / 8
  let Bu : Finset (Fin n → W) := Finset.univ.filter (fun u => 4096 * C * bad u ≤ h ^ 2)
  have hmarkov : ∀ u ∈ Bu, Fintype.card Ω ≤ 2 * (Finset.univ.filter (fun S : Ω => errS S u ≤ kMax)).card := by
    intro u hu
    have hbu : 4096 * C * bad u ≤ h ^ 2 := (Finset.mem_filter.mp hu).2
    have h16 : 16 * ∑ S : Ω, errS S u ≤ a * h * Fintype.card Ω := by
      have h1 := hsum_full_le u
      have h2 : ∑ S : Ω, errS S u ≤ ∑ S : Ω, errSFull S u := Finset.sum_le_sum fun S _ => herr_le_full S u
      have h3 : 16 * h * ∑ S : Ω, errS S u ≤ a * h * h * Fintype.card Ω := by
        calc 16 * h * ∑ S : Ω, errS S u
            = 16 * (h * ∑ S : Ω, errS S u) := by ring
          _ ≤ 16 * (h * ∑ S : Ω, errSFull S u) := Nat.mul_le_mul_left 16 (Nat.mul_le_mul_left h h2)
          _ ≤ 16 * (256 * a * C * bad u * Fintype.card Ω) := Nat.mul_le_mul_left 16 h1
          _ = a * (4096 * C * bad u) * Fintype.card Ω := by ring
          _ ≤ a * (h ^ 2) * Fintype.card Ω := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left a hbu)
          _ = a * h * h * Fintype.card Ω := by ring
      have h3' : h * (16 * ∑ S : Ω, errS S u) ≤ h * (a * h * Fintype.card Ω) := by linarith
      exact Nat.le_of_mul_le_mul_left h3' hh_pos
    let Good := Finset.univ.filter (fun S : Ω => errS S u ≤ kMax)
    let Bad := Finset.univ.filter (fun S : Ω => ¬ (errS S u ≤ kMax))
    have hsplit : Good.card + Bad.card = Fintype.card Ω := by
      rw [← Finset.card_union_of_disjoint]
      · have hun : Good ∪ Bad = Finset.univ := by
          ext S; simp only [Good, Bad, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]; tauto
        rw [hun, Finset.card_univ]
      · rw [Finset.disjoint_left]
        intro S h1 h2
        simp only [Good, Bad, Finset.mem_filter] at h1 h2
        exact h2.2 h1.2
    have hbad_sum : a * h * Bad.card ≤ 8 * ∑ S : Ω, errS S u := by
      calc a * h * Bad.card
          ≤ (8 * (kMax + 1)) * Bad.card := Nat.mul_le_mul_right _ (by dsimp only [kMax]; omega)
        _ = ∑ _S ∈ Bad, 8 * (kMax + 1) := by simp [mul_comm]
        _ ≤ ∑ S ∈ Bad, 8 * errS S u := by
            refine Finset.sum_le_sum fun S hS => ?_
            have : kMax < errS S u := Nat.lt_of_not_le (Finset.mem_filter.mp hS).2
            omega
        _ = 8 * ∑ S ∈ Bad, errS S u := by rw [Finset.mul_sum]
        _ ≤ 8 * ∑ S : Ω, errS S u :=
            Nat.mul_le_mul_left 8 (Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _)
    have h2bad : 2 * (a * h) * Bad.card ≤ (a * h) * Fintype.card Ω := by
      calc 2 * (a * h) * Bad.card
          = 2 * (a * h * Bad.card) := by ring
        _ ≤ 2 * (8 * ∑ S : Ω, errS S u) := Nat.mul_le_mul_left 2 hbad_sum
        _ = 16 * ∑ S : Ω, errS S u := by ring
        _ ≤ a * h * Fintype.card Ω := h16
    have hah_pos : 0 < a * h := Nat.mul_pos (by omega) hh_pos
    have hbad_half : 2 * Bad.card ≤ Fintype.card Ω := by
      have : (a * h) * (2 * Bad.card) ≤ (a * h) * Fintype.card Ω := by linarith
      exact Nat.le_of_mul_le_mul_left this hah_pos
    change Fintype.card Ω ≤ 2 * Good.card
    omega
  have hfixed_S : ∀ S : Ω,
      (Finset.univ.filter (fun u : Fin n → W => errS S u ≤ kMax)).card * 2 ^ (3 * a * h) <
        2 ^ (d * n) := by
    intro S
    exact fixed_S_bound a h n d ha hh_pos (by omega) v row col sign (R S) (hR_card S)
      (fun i => I_of S ⟨color i.val, (Finset.mem_filter.mp (Finset.mem_sdiff.mp i.property).1).2⟩)
      (fun i => hI_card S _)
      (fun i j hj hjR => (Finset.mem_sdiff.mp hjR).2
        (Finset.mem_biUnion.mpr ⟨_, Finset.mem_univ _, hI_sub S _ hj⟩))
      (fun i => hI_li S _)
  have hdouble_le : Bu.card * Fintype.card Ω ≤
      2 * ∑ S : Ω, (Finset.univ.filter (fun u : Fin n → W => errS S u ≤ kMax)).card := by
    calc Bu.card * Fintype.card Ω
        = ∑ _u ∈ Bu, Fintype.card Ω := by simp
      _ ≤ ∑ u ∈ Bu, 2 * (Finset.univ.filter (fun S : Ω => errS S u ≤ kMax)).card :=
          Finset.sum_le_sum hmarkov
      _ = 2 * ∑ u ∈ Bu, (Finset.univ.filter (fun S : Ω => errS S u ≤ kMax)).card := by rw [Finset.mul_sum]
      _ ≤ 2 * ∑ u : Fin n → W, (Finset.univ.filter (fun S : Ω => errS S u ≤ kMax)).card :=
          Nat.mul_le_mul_left 2 (Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _)
      _ = 2 * ∑ S : Ω, (Finset.univ.filter (fun u : Fin n → W => errS S u ≤ kMax)).card := by
          congr 1
          simp only [Finset.card_filter]
          exact Finset.sum_comm
  have hΩ_ne : (Finset.univ : Finset Ω).Nonempty := Fintype.card_pos_iff.mp hΩ_pos |> fun ⟨x⟩ => ⟨x, Finset.mem_univ x⟩
  have htotal_lt : Bu.card * 2 ^ (3 * a * h) * Fintype.card Ω < 2 * 2 ^ (d * n) * Fintype.card Ω := by
    calc Bu.card * 2 ^ (3 * a * h) * Fintype.card Ω
        = (Bu.card * Fintype.card Ω) * 2 ^ (3 * a * h) := by ring
      _ ≤ (2 * ∑ S : Ω, (Finset.univ.filter (fun u : Fin n → W => errS S u ≤ kMax)).card) *
            2 ^ (3 * a * h) := Nat.mul_le_mul_right _ hdouble_le
      _ = 2 * ∑ S : Ω, (Finset.univ.filter (fun u : Fin n → W => errS S u ≤ kMax)).card *
            2 ^ (3 * a * h) := by rw [mul_assoc, Finset.sum_mul]
      _ < 2 * ∑ _S : Ω, 2 ^ (d * n) :=
          Nat.mul_lt_mul_of_pos_left (Finset.sum_lt_sum_of_nonempty hΩ_ne (fun S _ => hfixed_S S)) (by decide)
      _ = 2 * 2 ^ (d * n) * Fintype.card Ω := by simp; ring
  exact Nat.lt_of_mul_lt_mul_right htotal_lt

private theorem solve_25734 (coreBits : ℕ) (ha : 16 ≤ coreBits) :
    let n := 2 ^ coreBits
    let h := n / 2
    let F := ZMod 2
    let W := Fin (32 * coreBits) → F
    ∃ u v : Fin n → W,
      ∀ (row col : Fin h ↪ Fin n) (q : ℕ), 256 * coreBits * 3 ^ q ≤ n →
      ∀ (color : Fin h → Fin (3 ^ q)) (sign : Fin h → F),
        let dot := fun (x y : W) => ∑ j : Fin (32 * coreBits), x j * y j
        let bad := ((Finset.univ : Finset (Fin h × Fin h)).filter (fun z =>
          z.1 < z.2 ∧ color z.1 = color z.2 ∧
            dot (u (row z.1)) (v (col z.2)) + dot (u (row z.2)) (v (col z.1)) ≠
              sign z.1 + sign z.2)).card
        h ^ 2 < 4096 * 3 ^ q * bad := by
  intro n h F W
  classical
  obtain ⟨v, hv⟩ := exists_good_v_ge16 coreBits ha
  let d := 32 * coreBits
  have hn_even : 2 * h = n := by
    have : 2 ^ coreBits = 2 * 2 ^ (coreBits - 1) := by
      cases coreBits with
      | zero => omega
      | succ k => simp [pow_succ, mul_comm]
    dsimp only [h, n]
    omega
  let badForQ (q : ℕ) (hq : 256 * coreBits * 3 ^ q ≤ n) : Finset (Fin n → W) :=
    Finset.univ.filter (fun u =>
      ∃ (row col : Fin h ↪ Fin n) (color : Fin h → Fin (3 ^ q)) (sign : Fin h → F),
        4096 * 3 ^ q *
          ((Finset.univ : Finset (Fin h × Fin h)).filter (fun z =>
            z.1 < z.2 ∧ color z.1 = color z.2 ∧
              dotF (u (row z.1)) (v (col z.2)) + dotF (u (row z.2)) (v (col z.1)) ≠
                sign z.1 + sign z.2)).card ≤ h ^ 2)
  have hbadQ_bound : ∀ (q : ℕ) (hq : 256 * coreBits * 3 ^ q ≤ n),
      (badForQ q hq).card * 2 ^ (3 * coreBits * h) ≤
        2 ^ ((3 * coreBits - 7) * h) * (2 * 2 ^ (d * n)) := by
    intro q hq
    let Cfg := (Fin h ↪ Fin n) × (Fin h ↪ Fin n) × (Fin h → Fin (3 ^ q)) × (Fin h → F)
    let badOne : Cfg → Finset (Fin n → W) := fun ⟨row, col, color, sign⟩ =>
      Finset.univ.filter (fun u =>
        4096 * 3 ^ q *
          ((Finset.univ : Finset (Fin h × Fin h)).filter (fun z =>
            z.1 < z.2 ∧ color z.1 = color z.2 ∧
              dotF (u (row z.1)) (v (col z.2)) + dotF (u (row z.2)) (v (col z.1)) ≠
                sign z.1 + sign z.2)).card ≤ h ^ 2)
    have hsub : badForQ q hq ⊆ (Finset.univ : Finset Cfg).biUnion badOne := by
      intro u hu
      simp only [badForQ, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      obtain ⟨row, col, color, sign, hle⟩ := hu
      rw [Finset.mem_biUnion]
      exact ⟨(row, col, color, sign), Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩⟩
    have h3q_le : 3 ^ q ≤ 2 ^ (coreBits - 8) := by
      have h256 : 256 * 2 ^ (coreBits - 8) = n := by
        dsimp only [n]
        have : 256 = 2 ^ 8 := by decide
        rw [this, ← pow_add, Nat.add_sub_of_le (by omega)]
      have h1 : 256 * 1 * 3 ^ q ≤ 256 * coreBits * 3 ^ q :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 256 (by omega))
      omega
    have hCfg_card : Fintype.card Cfg ≤ 2 ^ ((3 * coreBits - 7) * h) := by
      have hemb_le : Fintype.card (Fin h ↪ Fin n) ≤ n ^ h := by
        calc Fintype.card (Fin h ↪ Fin n)
            ≤ Fintype.card (Fin h → Fin n) :=
              Fintype.card_le_of_injective (fun f : Fin h ↪ Fin n => (f : Fin h → Fin n))
                (fun _ _ h => Function.Embedding.ext (congrFun h))
          _ = n ^ h := by simp
      have hcol_le : Fintype.card (Fin h → Fin (3 ^ q)) ≤ (2 ^ (coreBits - 8)) ^ h := by
        simp only [Fintype.card_fun, Fintype.card_fin]
        exact Nat.pow_le_pow_left h3q_le h
      have hsign_eq : Fintype.card (Fin h → F) = 2 ^ h := by
        simp only [F, Fintype.card_fun, ZMod.card, Fintype.card_fin]
      calc Fintype.card Cfg
          = Fintype.card (Fin h ↪ Fin n) * Fintype.card (Fin h ↪ Fin n) *
              Fintype.card (Fin h → Fin (3 ^ q)) * Fintype.card (Fin h → F) := by
            simp only [Cfg, Fintype.card_prod]; ring
        _ ≤ n ^ h * n ^ h * (2 ^ (coreBits - 8)) ^ h * 2 ^ h := by
            apply Nat.mul_le_mul
            · apply Nat.mul_le_mul
              · exact Nat.mul_le_mul hemb_le hemb_le
              · exact hcol_le
            · exact le_of_eq hsign_eq
        _ = 2 ^ ((3 * coreBits - 7) * h) := by
            dsimp only [n]
            rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add, ← pow_add]
            congr 1
            have h1 : (coreBits - 8) * h + 8 * h = coreBits * h := by
              rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
            have h2 : (3 * coreBits - 7) * h + 7 * h = 3 * (coreBits * h) := by
              rw [← Nat.add_mul, Nat.sub_add_cancel (by omega), mul_assoc]
            omega
    calc (badForQ q hq).card * 2 ^ (3 * coreBits * h)
        ≤ ((Finset.univ : Finset Cfg).biUnion badOne).card * 2 ^ (3 * coreBits * h) :=
          Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
      _ ≤ (∑ c : Cfg, (badOne c).card) * 2 ^ (3 * coreBits * h) :=
          Nat.mul_le_mul_right _ Finset.card_biUnion_le
      _ = ∑ c : Cfg, (badOne c).card * 2 ^ (3 * coreBits * h) := Finset.sum_mul _ _ _
      _ ≤ ∑ _c : Cfg, (2 * 2 ^ (d * n)) :=
          Finset.sum_le_sum fun ⟨row, col, color, sign⟩ _ =>
            le_of_lt (bad_u_count_bound coreBits ha v hv row col q hq color sign)
      _ = Fintype.card Cfg * (2 * 2 ^ (d * n)) := by simp
      _ ≤ 2 ^ ((3 * coreBits - 7) * h) * (2 * 2 ^ (d * n)) := Nat.mul_le_mul_right _ hCfg_card
  let validQ : Finset ℕ := (Finset.range coreBits).filter (fun q => 256 * coreBits * 3 ^ q ≤ n)
  let badAll : Finset (Fin n → W) :=
    validQ.attach.biUnion fun q => badForQ q.val (Finset.mem_filter.mp q.property).2
  have hbadAll_lt : badAll.card < (Finset.univ : Finset (Fin n → W)).card := by
    have htot : (Finset.univ : Finset (Fin n → W)).card = 2 ^ (d * n) := by
      simp only [Finset.card_univ, Fintype.card_fun, W, F, ZMod.card, Fintype.card_fin, ← pow_mul]
      rfl
    rw [htot]
    have hmul_lt : badAll.card * 2 ^ (3 * coreBits * h) < 2 ^ (d * n) * 2 ^ (3 * coreBits * h) := by
      have hle1 : badAll.card * 2 ^ (3 * coreBits * h) ≤
          validQ.card * (2 ^ ((3 * coreBits - 7) * h) * (2 * 2 ^ (d * n))) := by
        calc badAll.card * 2 ^ (3 * coreBits * h)
            ≤ (∑ q ∈ validQ.attach, (badForQ q.val (Finset.mem_filter.mp q.property).2).card) *
                2 ^ (3 * coreBits * h) := Nat.mul_le_mul_right _ Finset.card_biUnion_le
          _ = ∑ q ∈ validQ.attach,
                (badForQ q.val (Finset.mem_filter.mp q.property).2).card * 2 ^ (3 * coreBits * h) :=
              Finset.sum_mul _ _ _
          _ ≤ ∑ _q ∈ validQ.attach, (2 ^ ((3 * coreBits - 7) * h) * (2 * 2 ^ (d * n))) :=
              Finset.sum_le_sum fun q _ => hbadQ_bound q.val (Finset.mem_filter.mp q.property).2
          _ = validQ.card * (2 ^ ((3 * coreBits - 7) * h) * (2 * 2 ^ (d * n))) := by simp
      have hvalid_le : validQ.card ≤ coreBits := by
        calc validQ.card ≤ (Finset.range coreBits).card := Finset.card_filter_le _ _
          _ = coreBits := Finset.card_range coreBits
      have h2a_lt : 2 * coreBits < 2 ^ (7 * h) := by
        have h1 : coreBits < 2 ^ coreBits := Nat.lt_two_pow_self
        have h2 : 2 * coreBits < 2 ^ (coreBits + 1) := by
          have : 2 ^ (coreBits + 1) = 2 * 2 ^ coreBits := by ring
          omega
        have h3 : coreBits + 1 ≤ 7 * h := by
          have : coreBits < n := Nat.lt_two_pow_self
          omega
        exact lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by decide : 0 < 2) h3)
      have hpow_split : 2 ^ ((3 * coreBits - 7) * h) * 2 ^ (7 * h) = 2 ^ (3 * coreBits * h) := by
        rw [← pow_add, ← Nat.add_mul, Nat.sub_add_cancel (by omega)]
      calc badAll.card * 2 ^ (3 * coreBits * h)
          ≤ coreBits * (2 ^ ((3 * coreBits - 7) * h) * (2 * 2 ^ (d * n))) :=
            hle1.trans (Nat.mul_le_mul_right _ hvalid_le)
        _ = (2 * coreBits) * 2 ^ ((3 * coreBits - 7) * h) * 2 ^ (d * n) := by ring
        _ < 2 ^ (7 * h) * 2 ^ ((3 * coreBits - 7) * h) * 2 ^ (d * n) := by
            apply Nat.mul_lt_mul_of_pos_right _ (by positivity)
            exact Nat.mul_lt_mul_of_pos_right h2a_lt (by positivity)
        _ = 2 ^ (d * n) * 2 ^ (3 * coreBits * h) := by
            rw [mul_comm (2 ^ (7 * h)), hpow_split, mul_comm]
    exact Nat.lt_of_mul_lt_mul_right hmul_lt
  have hex : (Finset.univ \ badAll).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hsub : Finset.univ ⊆ badAll := Finset.sdiff_eq_empty_iff_subset.mp hemp
    have := Finset.card_le_card hsub
    omega
  obtain ⟨u, hu⟩ := hex
  have hnot : u ∉ badAll := (Finset.mem_sdiff.mp hu).2
  refine ⟨u, v, ?_⟩
  intro row col q hq color sign dot bad
  by_contra hle
  push_neg at hle
  have hq_lt : q < coreBits := by
    have h2q : 2 ^ q ≤ 3 ^ q := Nat.pow_le_pow_left (by decide : 2 ≤ 3) q
    have hlt : 2 ^ q < 2 ^ coreBits := by
      have : 256 * coreBits * 2 ^ q ≤ 2 ^ coreBits := (Nat.mul_le_mul_left _ h2q).trans hq
      have : 2 ^ q < 256 * coreBits * 2 ^ q := by
        have hp : 0 < 2 ^ q := by positivity
        nlinarith
      omega
    exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hlt
  have hq_mem : q ∈ validQ := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hq_lt, hq⟩
  apply hnot
  rw [Finset.mem_biUnion]
  refine ⟨⟨q, hq_mem⟩, Finset.mem_attach _ _, ?_⟩
  simp only [badForQ, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨row, col, color, sign, hle⟩

end PEqualNP.Outside.L_meta_25734_aux

theorem PEqualNP.Outside.L_meta_25734 : ∀ coreBits : ℕ, 16 ≤ coreBits →
  let n := 2^coreBits
  let h := n/2
  let F := ZMod 2
  let W := Fin (32*coreBits) → F
  ∃ u v : Fin n → W,
    ∀ (row col : Fin h ↪ Fin n) (q : ℕ), 256*coreBits*3^q ≤ n →
    ∀ (color : Fin h → Fin (3^q)) (sign : Fin h → F),
      let dot := fun (x y : W) => ∑ j : Fin (32*coreBits), x j * y j
      let bad := ((Finset.univ : Finset (Fin h × Fin h)).filter (fun z =>
        z.1 < z.2 ∧ color z.1 = color z.2 ∧
          dot (u (row z.1)) (v (col z.2)) + dot (u (row z.2)) (v (col z.1)) ≠
            sign z.1 + sign z.2)).card
      h^2 < 4096*3^q*bad := by
  intro coreBits ha
  exact PEqualNP.Outside.L_meta_25734_aux.solve_25734 coreBits ha
