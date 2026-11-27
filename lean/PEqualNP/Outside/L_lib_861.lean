import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_861_aux

abbrev F := ZMod 2
abbrev W (d : Nat) := Fin d → F

def evalDual {d : Nat} (O : Submodule F (W d)) : W d →ₗ[F] Module.Dual F O where
  toFun y :=
    { toFun := fun v => dotProduct v.1 y
      map_add' := fun u v => by
        show dotProduct (u.1 + v.1) y = dotProduct u.1 y + dotProduct v.1 y
        exact add_dotProduct u.1 v.1 y
      map_smul' := fun c v => by
        show dotProduct (c • v.1) y = c • dotProduct v.1 y
        exact smul_dotProduct c v.1 y }
  map_add' a b := by
    ext v
    exact dotProduct_add v.1 a b
  map_smul' c a := by
    ext v
    exact dotProduct_smul c v.1 a

def ortho {d : Nat} (O : Submodule F (W d)) : Submodule F (W d) :=
  LinearMap.ker (evalDual O)

lemma mem_ortho {d : Nat} (O : Submodule F (W d)) (y : W d) :
    y ∈ ortho O ↔ ∀ v ∈ O, dotProduct v y = 0 := by
  simp only [ortho, LinearMap.mem_ker]
  constructor
  · intro h v hv
    exact LinearMap.congr_fun h ⟨v, hv⟩
  · intro h
    ext v
    exact h v.1 v.2

lemma ker_evalDual {d : Nat} (O : Submodule F (W d)) :
    LinearMap.ker (evalDual O) = ortho O := rfl

lemma evalDual_top_surjective (d : Nat) :
    Function.Surjective (evalDual (⊤ : Submodule F (W d))) := by
  intro f
  refine ⟨fun i => f ⟨Pi.single i 1, trivial⟩, ?_⟩
  ext ⟨v, _⟩
  show dotProduct v (fun i => f ⟨Pi.single i 1, trivial⟩) = f ⟨v, trivial⟩
  have hv : (⟨v, trivial⟩ : (⊤ : Submodule F (W d))) =
      ∑ i : Fin d, v i • (⟨Pi.single i 1, trivial⟩ : (⊤ : Submodule F (W d))) := by
    apply Subtype.ext
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hv]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, dotProduct]

lemma evalDual_surjective {d : Nat} (O : Submodule F (W d)) :
    Function.Surjective (evalDual O) := by
  intro g
  obtain ⟨p, hp⟩ := Submodule.exists_isCompl O
  let proj : W d →ₗ[F] O := Submodule.projectionOnto O p hp
  let gTop : Module.Dual F (⊤ : Submodule F (W d)) :=
    { toFun := fun v => g (proj v.1)
      map_add' := fun a b => by simp [map_add]
      map_smul' := fun c a => by simp [map_smul] }
  obtain ⟨y, hy⟩ := evalDual_top_surjective d gTop
  refine ⟨y, ?_⟩
  ext v
  have h1 := LinearMap.congr_fun hy ⟨v.1, trivial⟩
  have h2 : proj v.1 = v := Submodule.projectionOnto_apply_left hp v
  simpa [evalDual, gTop, h2] using h1

lemma finrank_add_ortho {d : Nat} (O : Submodule F (W d)) :
    Module.finrank F O + Module.finrank F (ortho O) = d := by
  have h := LinearMap.finrank_range_add_finrank_ker (evalDual O)
  rw [LinearMap.range_eq_top.mpr (evalDual_surjective O), finrank_top,
    Subspace.dual_finrank_eq, ker_evalDual, Module.finrank_fin_fun] at h
  exact h

lemma finrank_le_d {d : Nat} (O : Submodule F (W d)) :
    Module.finrank F O ≤ d := by
  have h := finrank_add_ortho O
  omega

lemma card_piece {d : Nat} (O : Submodule F (W d)) (x : W d)
    [DecidablePred (fun y : W d => ∀ v ∈ O, dotProduct v (y - x) = 0)] :
    ((Finset.univ : Finset (W d)).filter (fun y => ∀ v ∈ O, dotProduct v (y - x) = 0)).card =
      2 ^ (d - Module.finrank F O) := by
  have : Fintype (ortho O) := Fintype.ofFinite _
  have hcardO : Fintype.card (ortho O) = 2 ^ (Module.finrank F (ortho O)) := by
    have h1 := Module.card_eq_pow_finrank (K := F) (V := ortho O)
    have h2 : Fintype.card F = 2 := ZMod.card 2
    rw [h2] at h1
    exact h1
  have hdim : Module.finrank F (ortho O) = d - Module.finrank F O := by
    have h := finrank_add_ortho O
    omega
  rw [← hdim, ← hcardO]
  have heq :
      (Finset.univ : Finset (W d)).filter (fun y => ∀ v ∈ O, dotProduct v (y - x) = 0) =
        Finset.univ.image (fun z : ortho O => z.1 + x) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hy
      refine ⟨⟨y - x, (mem_ortho O (y - x)).mpr hy⟩, ?_⟩
      simp
    · rintro ⟨⟨z, hz⟩, rfl⟩
      have h' := (mem_ortho O z).mp hz
      simpa using h'
  rw [heq, Finset.card_image_of_injective]
  · simp
  · intro a b hab
    exact Subtype.ext (add_right_cancel hab)

lemma cover_sum_ge {d n : Nat}
    (masks : Fin n → Submodule F (W d)) (rep : Fin n → W d)
    (hcov : ∀ y : W d, ∃ i : Fin n, ∀ v ∈ masks i, dotProduct v (y - rep i) = 0) :
    2 ^ d ≤ ∑ i : Fin n, 2 ^ (d - Module.finrank F (masks i)) := by
  classical
  let P : Fin n → Finset (W d) := fun i =>
    Finset.univ.filter (fun y : W d => ∀ v ∈ masks i, dotProduct v (y - rep i) = 0)
  have hcardW : (Finset.univ : Finset (W d)).card = 2 ^ d := by
    simp [ZMod.card]
  have hunion : (Finset.univ : Finset (W d)) = Finset.univ.biUnion P := by
    ext y
    simp only [Finset.mem_univ, Finset.mem_biUnion, P, Finset.mem_filter, true_and, true_iff]
    exact hcov y
  calc
    2 ^ d = (Finset.univ : Finset (W d)).card := hcardW.symm
    _ = (Finset.univ.biUnion P).card := by rw [hunion]
    _ ≤ ∑ i : Fin n, (P i).card := Finset.card_biUnion_le
    _ = ∑ i : Fin n, 2 ^ (d - Module.finrank F (masks i)) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      exact card_piece (masks i) (rep i)

lemma cover_sum_eq_iff_disjoint {d n : Nat}
    (masks : Fin n → Submodule F (W d)) (rep : Fin n → W d)
    (hcov : ∀ y : W d, ∃ i : Fin n, ∀ v ∈ masks i, dotProduct v (y - rep i) = 0) :
    (∑ i : Fin n, 2 ^ (d - Module.finrank F (masks i)) = 2 ^ d) ↔
      (∀ i j : Fin n, i ≠ j →
        Disjoint {y : W d | ∀ v ∈ masks i, dotProduct v (y - rep i) = 0}
          {y : W d | ∀ v ∈ masks j, dotProduct v (y - rep j) = 0}) := by
  classical
  let P : Fin n → Finset (W d) := fun i =>
    Finset.univ.filter (fun y : W d => ∀ v ∈ masks i, dotProduct v (y - rep i) = 0)
  have hcardW : (Finset.univ : Finset (W d)).card = 2 ^ d := by
    simp [ZMod.card]
  have hunion : (Finset.univ : Finset (W d)) = Finset.univ.biUnion P := by
    ext y
    simp only [Finset.mem_univ, Finset.mem_biUnion, P, Finset.mem_filter, true_and, true_iff]
    exact hcov y
  have hsumP : ∑ i : Fin n, 2 ^ (d - Module.finrank F (masks i)) = ∑ i : Fin n, (P i).card := by
    refine Finset.sum_congr rfl ?_
    intro i _
    exact (card_piece (masks i) (rep i)).symm
  rw [hsumP, ← hcardW, hunion]
  constructor
  · intro heq i j hij
    rw [Set.disjoint_left]
    intro y hyi hyj
    have hmemi : y ∈ P i := Finset.mem_filter.mpr ⟨Finset.mem_univ y, hyi⟩
    have hmemj : y ∈ P j := Finset.mem_filter.mpr ⟨Finset.mem_univ y, hyj⟩
    have hpair : (P i ∪ P j).card < (P i).card + (P j).card := by
      have h1 := Finset.card_union_add_card_inter (P i) (P j)
      have hpos : 0 < (P i ∩ P j).card :=
        Finset.card_pos.mpr ⟨y, Finset.mem_inter.mpr ⟨hmemi, hmemj⟩⟩
      omega
    have hsplit : (Finset.univ : Finset (Fin n)) = {i, j} ∪ (Finset.univ \ {i, j}) := by
      ext k
      simp
    have hdisj : Disjoint ({i, j} : Finset (Fin n)) (Finset.univ \ {i, j}) :=
      disjoint_sdiff_self_right
    have hle1 : (Finset.univ.biUnion P).card ≤
        (P i ∪ P j).card + ∑ k ∈ Finset.univ \ {i, j}, (P k).card := by
      calc
        (Finset.univ.biUnion P).card
            = (({i, j} : Finset (Fin n)).biUnion P ∪ (Finset.univ \ {i, j}).biUnion P).card := by
              rw [← Finset.union_biUnion, ← hsplit]
        _ ≤ (({i, j} : Finset (Fin n)).biUnion P).card +
              ((Finset.univ \ {i, j}).biUnion P).card := Finset.card_union_le _ _
        _ ≤ (P i ∪ P j).card + ∑ k ∈ Finset.univ \ {i, j}, (P k).card := by
              have hbi : ({i, j} : Finset (Fin n)).biUnion P = P i ∪ P j := by
                ext z
                simp
              rw [hbi]
              exact Nat.add_le_add_left Finset.card_biUnion_le _
    have hsumsplit : ∑ k : Fin n, (P k).card =
        (P i).card + (P j).card + ∑ k ∈ Finset.univ \ {i, j}, (P k).card := by
      conv_lhs => rw [hsplit, Finset.sum_union hdisj]
      rw [Finset.sum_pair hij]
    omega
  · intro hdisj
    symm
    apply Finset.card_biUnion
    intro i _ j _ hij
    show Disjoint (P i) (P j)
    rw [Finset.disjoint_left]
    intro y hyi hyj
    have h1 := (Finset.mem_filter.mp hyi).2
    have h2 := (Finset.mem_filter.mp hyj).2
    exact Set.disjoint_left.mp (hdisj i j hij) h1 h2

lemma exists_coset_cover {d : Nat} (O : Submodule F (W d)) :
    ∃ rep : Fin (2 ^ (Module.finrank F O)) → W d,
      ∀ y : W d, ∃ i : Fin (2 ^ (Module.finrank F O)),
        ∀ v ∈ O, dotProduct v (y - rep i) = 0 := by
  classical
  have : Finite (Module.Dual F O) :=
    Finite.of_injective (fun f : Module.Dual F O => (f : O → F)) DFunLike.coe_injective
  have : Fintype (Module.Dual F O) := Fintype.ofFinite _
  have hcard : Fintype.card (Module.Dual F O) = 2 ^ (Module.finrank F O) := by
    have h1 := Module.card_eq_pow_finrank (K := F) (V := Module.Dual F O)
    have h2 : Fintype.card F = 2 := ZMod.card 2
    rw [h2, Subspace.dual_finrank_eq] at h1
    exact h1
  let e : Fin (2 ^ (Module.finrank F O)) ≃ Module.Dual F O :=
    (Fintype.equivFinOfCardEq hcard).symm
  have hsurj := evalDual_surjective O
  choose rep hrep using fun i => hsurj (e i)
  refine ⟨rep, ?_⟩
  intro y
  refine ⟨e.symm (evalDual O y), ?_⟩
  have hker : y - rep (e.symm (evalDual O y)) ∈ ortho O := by
    rw [← ker_evalDual, LinearMap.mem_ker, map_sub, hrep, Equiv.apply_symm_apply, sub_self]
  exact (mem_ortho O _).mp hker

lemma finrank_map_mkQ_add_inf {d : Nat} (O B : Submodule F (W d)) :
    Module.finrank F (B.map O.mkQ) + Module.finrank F ((O ⊓ B : Submodule F (W d))) =
      Module.finrank F B := by
  let f : B →ₗ[F] W d ⧸ O := O.mkQ.comp B.subtype
  have hrange : LinearMap.range f = B.map O.mkQ := by
    ext q
    simp [f, Submodule.mem_map]
  have hker : Module.finrank F (LinearMap.ker f) =
      Module.finrank F ((O ⊓ B : Submodule F (W d))) := by
    let e : LinearMap.ker f ≃ₗ[F] (O ⊓ B : Submodule F (W d)) :=
      { toFun := fun x => ⟨x.1.1, by
          have hx : O.mkQ x.1.1 = 0 := x.2
          rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx
          exact ⟨hx, x.1.2⟩⟩
        map_add' := fun a b => rfl
        map_smul' := fun c a => rfl
        invFun := fun y => ⟨⟨y.1, y.2.2⟩, by
          show O.mkQ y.1 = 0
          rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
          exact y.2.1⟩
        left_inv := fun x => by ext; rfl
        right_inv := fun y => by ext; rfl }
    exact e.finrank_eq
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, hker] at hrn
  exact hrn

lemma finrank_profile_bot {d : Nat} (A B : Submodule F (W d)) :
    Module.finrank F
        ((A.map (⊥ : Submodule F (W d)).mkQ) ⊓ (B.map (⊥ : Submodule F (W d)).mkQ) :
          Submodule F (W d ⧸ (⊥ : Submodule F (W d)))) =
      Module.finrank F ((A ⊓ B : Submodule F (W d))) := by
  have hinj : Function.Injective (⊥ : Submodule F (W d)).mkQ := by
    rw [← LinearMap.ker_eq_bot, Submodule.ker_mkQ]
  have hmap : (A.map (⊥ : Submodule F (W d)).mkQ) ⊓ (B.map (⊥ : Submodule F (W d)).mkQ) =
      (A ⊓ B).map (⊥ : Submodule F (W d)).mkQ :=
    (Submodule.map_inf (⊥ : Submodule F (W d)).mkQ hinj).symm
  rw [hmap]
  have hrn := finrank_map_mkQ_add_inf (⊥ : Submodule F (W d)) (A ⊓ B)
  have hbot : Module.finrank F (((⊥ : Submodule F (W d)) ⊓ (A ⊓ B) : Submodule F (W d))) = 0 := by
    simp
  omega

lemma map_mkQ_inf_eq_of_le {d : Nat} (O A B : Submodule F (W d)) (hOA : O ≤ A) :
    (A.map O.mkQ) ⊓ (B.map O.mkQ) = (A ⊓ B).map O.mkQ := by
  apply le_antisymm
  · intro q hq
    rcases hq with ⟨⟨a, ha, rfl⟩, ⟨b, hb, hba⟩⟩
    have hsub : O.mkQ (b - a) = 0 := by
      rw [map_sub, hba, sub_self]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hsub
    have hbA : b ∈ A := by
      have : b = a + (b - a) := by abel
      rw [this]
      exact A.add_mem ha (hOA hsub)
    exact ⟨b, ⟨hbA, hb⟩, hba⟩
  · exact Submodule.map_inf_le O.mkQ

lemma profile_ge_sub_inf {d : Nat} (O A B : Submodule F (W d)) :
    Module.finrank F ((A ⊓ B : Submodule F (W d))) ≤
      Module.finrank F ((A.map O.mkQ) ⊓ (B.map O.mkQ) : Submodule F (W d ⧸ O)) +
        Module.finrank F ((O ⊓ (A ⊓ B) : Submodule F (W d))) := by
  have h1 : Module.finrank F ((A ⊓ B).map O.mkQ) ≤
      Module.finrank F ((A.map O.mkQ) ⊓ (B.map O.mkQ) : Submodule F (W d ⧸ O)) :=
    Submodule.finrank_mono (Submodule.map_inf_le O.mkQ)
  have h2 := finrank_map_mkQ_add_inf O (A ⊓ B)
  omega

end PEqualNP.Outside.L_lib_861_aux

theorem PEqualNP.Outside.L_lib_861 : ∀ (d l h e : Nat),
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let F := ZMod 2
  let W := Fin d → F
  ∀ (leaf : Fin l → Submodule F W) (cut : Fin h → Fin e → Fin l → Bool),
    let side := fun (t : Fin h) (j : Fin e) (c : Bool) =>
      Submodule.span F {v : W | ∃ i : Fin l, cut t j i = c ∧ v ∈ leaf i}
    let boundary := fun (t : Fin h) (j : Fin e) => side t j true ⊓ side t j false
    let profile := fun (O : Submodule F W) (t : Fin h) (j : Fin e) =>
      Module.finrank F (((side t j true).map O.mkQ) ⊓ ((side t j false).map O.mkQ) : Submodule F (W ⧸ O))
    let peak := fun (O : Submodule F W) (t : Fin h) =>
      (Finset.univ : Finset (Fin e)).sup (profile O t)
    (∀ (t : Fin h) (i j : Fin e), ∃ a b : Bool,
      ∀ u : Fin l, cut t i u = a → cut t j u = b) →
    ∀ (w : Nat), IsLeast {z : Nat | ∃ t : Fin h, peak ⊥ t = z} w →
    let piece := fun (O : Submodule F W) (x : W) =>
      {y : W | ∀ v ∈ O, dotProduct v (y-x) = 0}
    (∀ (charge : (Fin e → Nat) → Nat) (budget : Nat),
      ((∃ (n : Nat) (masks : Fin n → Submodule F W) (rep : Fin n → W) (layout : Fin n → Fin h),
          (∀ y : W, ∃ i : Fin n, y ∈ piece (masks i) (rep i)) ∧
          (∑ i : Fin n, charge (profile (masks i) (layout i))) ≤ budget) ↔
        ∃ (O : Submodule F W) (t : Fin h),
          2^(Module.finrank F O) * charge (profile O t) ≤ budget)) ∧
    (∀ (n : Nat) (masks : Fin n → Submodule F W) (rep : Fin n → W) (layout : Fin n → Fin h),
      (∀ y : W, ∃ i : Fin n, y ∈ piece (masks i) (rep i)) →
      let total := ∑ i : Fin n, 2^(peak (masks i) (layout i))
      2^w ≤ total ∧
      (total = 2^w ↔
        (∀ i j : Fin n, i ≠ j → Disjoint (piece (masks i) (rep i)) (piece (masks j) (rep j))) ∧
        ∀ i : Fin n, let O := masks i; let t := layout i; let s := Module.finrank F O
          s ≤ w ∧ peak ⊥ t = w ∧ ∀ j : Fin e, s + Module.finrank F (boundary t j) ≤
            w + Module.finrank F ((O ⊓ boundary t j) : Submodule F W))) := by
  intro d l h e
  dsimp only
  intro leaf cut
  set side := fun (t : Fin h) (j : Fin e) (c : Bool) =>
    Submodule.span (ZMod 2) {v : Fin d → ZMod 2 | ∃ i : Fin l, cut t j i = c ∧ v ∈ leaf i}
  set boundary := fun (t : Fin h) (j : Fin e) => side t j true ⊓ side t j false
  set profile := fun (O : Submodule (ZMod 2) (Fin d → ZMod 2)) (t : Fin h) (j : Fin e) =>
    Module.finrank (ZMod 2)
      (((side t j true).map O.mkQ) ⊓ ((side t j false).map O.mkQ) :
        Submodule (ZMod 2) ((Fin d → ZMod 2) ⧸ O))
  set peak := fun (O : Submodule (ZMod 2) (Fin d → ZMod 2)) (t : Fin h) =>
    (Finset.univ : Finset (Fin e)).sup (profile O t)
  intro hlam w hw
  set piece := fun (O : Submodule (ZMod 2) (Fin d → ZMod 2)) (x : Fin d → ZMod 2) =>
    {y : Fin d → ZMod 2 | ∀ v ∈ O, dotProduct v (y - x) = 0}
  have hprof_bot : ∀ (t : Fin h) (j : Fin e),
      profile ⊥ t j = Module.finrank (ZMod 2) (boundary t j) := fun t j =>
    PEqualNP.Outside.L_lib_861_aux.finrank_profile_bot (side t j true) (side t j false)
  have hpeak_le : ∀ (O : Submodule (ZMod 2) (Fin d → ZMod 2)) (t : Fin h),
      peak ⊥ t ≤ peak O t + Module.finrank (ZMod 2) O := by
    intro O t
    apply Finset.sup_le
    intro j _
    rw [hprof_bot t j]
    have h1 : Module.finrank (ZMod 2) (boundary t j) ≤
        profile O t j +
          Module.finrank (ZMod 2) ((O ⊓ boundary t j : Submodule (ZMod 2) (Fin d → ZMod 2))) :=
      PEqualNP.Outside.L_lib_861_aux.profile_ge_sub_inf O (side t j true) (side t j false)
    have h2 : Module.finrank (ZMod 2) ((O ⊓ boundary t j : Submodule (ZMod 2) (Fin d → ZMod 2))) ≤
        Module.finrank (ZMod 2) O := Submodule.finrank_mono inf_le_left
    have h3 : profile O t j ≤ peak O t := Finset.le_sup (Finset.mem_univ j)
    omega
  have hw_le_peak_bot : ∀ t : Fin h, w ≤ peak ⊥ t := fun t => hw.2 ⟨t, rfl⟩
  constructor
  · intro charge budget
    constructor
    · rintro ⟨n, masks, rep, layout, hcov, hsum⟩
      by_contra hnone
      push Not at hnone
      have hcov_ge := PEqualNP.Outside.L_lib_861_aux.cover_sum_ge masks rep hcov
      have hterm : ∀ i : Fin n,
          2 ^ (d - Module.finrank (ZMod 2) (masks i)) * (budget + 1) ≤
            2 ^ d * charge (profile (masks i) (layout i)) := by
        intro i
        have hi := hnone (masks i) (layout i)
        have hle : Module.finrank (ZMod 2) (masks i) ≤ d :=
          PEqualNP.Outside.L_lib_861_aux.finrank_le_d (masks i)
        have hpow : 2 ^ (d - Module.finrank (ZMod 2) (masks i)) *
            2 ^ (Module.finrank (ZMod 2) (masks i)) = 2 ^ d := by
          rw [← pow_add, Nat.sub_add_cancel hle]
        calc
          2 ^ (d - Module.finrank (ZMod 2) (masks i)) * (budget + 1)
              ≤ 2 ^ (d - Module.finrank (ZMod 2) (masks i)) *
                  (2 ^ (Module.finrank (ZMod 2) (masks i)) *
                    charge (profile (masks i) (layout i))) :=
                Nat.mul_le_mul_left _ hi
          _ = (2 ^ (d - Module.finrank (ZMod 2) (masks i)) *
                2 ^ (Module.finrank (ZMod 2) (masks i))) *
                charge (profile (masks i) (layout i)) := (Nat.mul_assoc _ _ _).symm
          _ = 2 ^ d * charge (profile (masks i) (layout i)) := by rw [hpow]
      have hsum_le :
          (∑ i : Fin n, 2 ^ (d - Module.finrank (ZMod 2) (masks i))) * (budget + 1) ≤
            2 ^ d * (∑ i : Fin n, charge (profile (masks i) (layout i))) := by
        rw [Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_le_sum (fun i _ => hterm i)
      have h1 : 2 ^ d * (budget + 1) ≤ 2 ^ d * budget :=
        le_trans (Nat.mul_le_mul_right _ hcov_ge)
          (le_trans hsum_le (Nat.mul_le_mul_left _ hsum))
      have hpos : 0 < 2 ^ d := pow_pos (by decide) d
      have h2 : budget + 1 ≤ budget := Nat.le_of_mul_le_mul_left h1 hpos
      omega
    · rintro ⟨O, t, hOt⟩
      obtain ⟨rep, hrep⟩ := PEqualNP.Outside.L_lib_861_aux.exists_coset_cover O
      refine ⟨2 ^ (Module.finrank (ZMod 2) O), fun _ => O, rep, fun _ => t, hrep, ?_⟩
      simpa using hOt
  · intro n masks rep layout hcov
    have hcov_ge := PEqualNP.Outside.L_lib_861_aux.cover_sum_ge masks rep hcov
    have hterm : ∀ i : Fin n,
        2 ^ (d - Module.finrank (ZMod 2) (masks i)) * 2 ^ w ≤
          2 ^ d * 2 ^ (peak (masks i) (layout i)) := by
      intro i
      have hle : Module.finrank (ZMod 2) (masks i) ≤ d :=
        PEqualNP.Outside.L_lib_861_aux.finrank_le_d (masks i)
      have hw_le : w ≤ peak (masks i) (layout i) + Module.finrank (ZMod 2) (masks i) :=
        le_trans (hw_le_peak_bot (layout i)) (hpeak_le (masks i) (layout i))
      have hpow : 2 ^ (d - Module.finrank (ZMod 2) (masks i)) *
          2 ^ (peak (masks i) (layout i) + Module.finrank (ZMod 2) (masks i)) =
            2 ^ d * 2 ^ (peak (masks i) (layout i)) := by
        rw [← pow_add, ← pow_add]
        congr 1
        omega
      calc
        2 ^ (d - Module.finrank (ZMod 2) (masks i)) * 2 ^ w
            ≤ 2 ^ (d - Module.finrank (ZMod 2) (masks i)) *
                2 ^ (peak (masks i) (layout i) + Module.finrank (ZMod 2) (masks i)) :=
              Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hw_le)
        _ = 2 ^ d * 2 ^ (peak (masks i) (layout i)) := hpow
    have hsum_chain :
        (∑ i : Fin n, 2 ^ (d - Module.finrank (ZMod 2) (masks i))) * 2 ^ w ≤
          2 ^ d * (∑ i : Fin n, 2 ^ (peak (masks i) (layout i))) := by
      rw [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_le_sum (fun i _ => hterm i)
    have hpos_d : 0 < 2 ^ d := pow_pos (by decide) d
    have hge : 2 ^ w ≤ ∑ i : Fin n, 2 ^ (peak (masks i) (layout i)) := by
      have h1 : 2 ^ d * 2 ^ w ≤ 2 ^ d * (∑ i : Fin n, 2 ^ (peak (masks i) (layout i))) :=
        le_trans (Nat.mul_le_mul_right _ hcov_ge) hsum_chain
      exact Nat.le_of_mul_le_mul_left h1 hpos_d
    refine ⟨hge, ?_⟩
    constructor
    · intro htot
      have hchain_eq :
          (∑ i : Fin n, 2 ^ (d - Module.finrank (ZMod 2) (masks i))) * 2 ^ w =
            2 ^ d * 2 ^ w := by
        have h1 : 2 ^ d * 2 ^ w ≤ (∑ i : Fin n, 2 ^ (d - Module.finrank (ZMod 2) (masks i))) * 2 ^ w :=
          Nat.mul_le_mul_right _ hcov_ge
        have h2 : (∑ i : Fin n, 2 ^ (d - Module.finrank (ZMod 2) (masks i))) * 2 ^ w ≤ 2 ^ d * 2 ^ w := by
          have htot' : (∑ i : Fin n, 2 ^ (peak (masks i) (layout i))) = 2 ^ w := htot
          have hsc := hsum_chain
          rw [htot'] at hsc
          exact hsc
        omega
      have hcov_eq : ∑ i : Fin n, 2 ^ (d - Module.finrank (ZMod 2) (masks i)) = 2 ^ d :=
        Nat.eq_of_mul_eq_mul_right (pow_pos (by decide) w) hchain_eq
      have hdisj := (PEqualNP.Outside.L_lib_861_aux.cover_sum_eq_iff_disjoint masks rep hcov).mp hcov_eq
      have hsum_eq :
          ∑ i : Fin n, 2 ^ (d - Module.finrank (ZMod 2) (masks i)) * 2 ^ w =
            ∑ i : Fin n, 2 ^ d * 2 ^ (peak (masks i) (layout i)) := by
        have htot' : (∑ i : Fin n, 2 ^ (peak (masks i) (layout i))) = 2 ^ w := htot
        rw [← Finset.sum_mul, ← Finset.mul_sum, htot', hchain_eq]
      refine ⟨hdisj, ?_⟩
      intro i
      have hi_eq :
          2 ^ (d - Module.finrank (ZMod 2) (masks i)) * 2 ^ w =
            2 ^ d * 2 ^ (peak (masks i) (layout i)) := by
        by_contra hne
        have hlt : 2 ^ (d - Module.finrank (ZMod 2) (masks i)) * 2 ^ w <
            2 ^ d * 2 ^ (peak (masks i) (layout i)) :=
          lt_of_le_of_ne (hterm i) hne
        have hsum_lt :
            ∑ k : Fin n, 2 ^ (d - Module.finrank (ZMod 2) (masks k)) * 2 ^ w <
              ∑ k : Fin n, 2 ^ d * 2 ^ (peak (masks k) (layout k)) :=
          Finset.sum_lt_sum (fun k _ => hterm k) ⟨i, Finset.mem_univ i, hlt⟩
        omega
      have hle : Module.finrank (ZMod 2) (masks i) ≤ d :=
        PEqualNP.Outside.L_lib_861_aux.finrank_le_d (masks i)
      have hpow_eq :
          2 ^ (d - Module.finrank (ZMod 2) (masks i)) * 2 ^ w =
            2 ^ (d - Module.finrank (ZMod 2) (masks i)) *
              2 ^ (peak (masks i) (layout i) + Module.finrank (ZMod 2) (masks i)) := by
        rw [hi_eq, ← pow_add, ← pow_add]
        congr 1
        omega
      have hpow2 : 2 ^ w = 2 ^ (peak (masks i) (layout i) + Module.finrank (ZMod 2) (masks i)) :=
        Nat.eq_of_mul_eq_mul_left (pow_pos (by decide) _) hpow_eq
      have hw_eq : w = peak (masks i) (layout i) + Module.finrank (ZMod 2) (masks i) :=
        Nat.pow_right_injective (by decide : 1 < 2) hpow2
      have hpeak_bot_eq : peak ⊥ (layout i) = w := by
        have h1 := hw_le_peak_bot (layout i)
        have h2 := hpeak_le (masks i) (layout i)
        omega
      refine ⟨by omega, hpeak_bot_eq, ?_⟩
      intro j
      have h1 : Module.finrank (ZMod 2) (boundary (layout i) j) ≤
          profile (masks i) (layout i) j +
            Module.finrank (ZMod 2)
              ((masks i ⊓ boundary (layout i) j : Submodule (ZMod 2) (Fin d → ZMod 2))) :=
        PEqualNP.Outside.L_lib_861_aux.profile_ge_sub_inf
          (masks i) (side (layout i) j true) (side (layout i) j false)
      have h2 : profile (masks i) (layout i) j ≤ peak (masks i) (layout i) :=
        Finset.le_sup (Finset.mem_univ j)
      show Module.finrank (ZMod 2) (masks i) + Module.finrank (ZMod 2) (boundary (layout i) j) ≤
        w + Module.finrank (ZMod 2)
          ((masks i ⊓ boundary (layout i) j : Submodule (ZMod 2) (Fin d → ZMod 2)))
      omega
    · rintro ⟨hdisj, hcond⟩
      have hcov_eq := (PEqualNP.Outside.L_lib_861_aux.cover_sum_eq_iff_disjoint masks rep hcov).mpr hdisj
      have hterm_eq : ∀ i : Fin n,
          2 ^ d * 2 ^ (peak (masks i) (layout i)) =
            2 ^ (d - Module.finrank (ZMod 2) (masks i)) * 2 ^ w := by
        intro i
        obtain ⟨hs_le, hpeak_bot_eq, hbd⟩ := hcond i
        set O := masks i
        set t := layout i
        set s := Module.finrank (ZMod 2) O
        have hpeak_add_eq : peak O t + s = w := by
          have hge_w : w ≤ peak O t + s := le_trans (hw_le_peak_bot t) (hpeak_le O t)
          have hle_w : peak O t + s ≤ w := by
            by_cases he0 : (Finset.univ : Finset (Fin e)).Nonempty
            · obtain ⟨j1, _, hj1⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin e)) he0 (profile ⊥ t)
              have hj1_w : Module.finrank (ZMod 2) (boundary t j1) = w := by
                rw [← hprof_bot t j1, ← hj1, hpeak_bot_eq]
              have hO_le_bd : O ≤ boundary t j1 := by
                have hbd1 : s + Module.finrank (ZMod 2) (boundary t j1) ≤
                    w + Module.finrank (ZMod 2) ((O ⊓ boundary t j1 : Submodule (ZMod 2) (Fin d → ZMod 2))) :=
                  hbd j1
                rw [hj1_w] at hbd1
                have hfin : Module.finrank (ZMod 2) O ≤
                    Module.finrank (ZMod 2) ((O ⊓ boundary t j1 : Submodule (ZMod 2) (Fin d → ZMod 2))) := by
                  omega
                have heq_inf : (O ⊓ boundary t j1 : Submodule (ZMod 2) (Fin d → ZMod 2)) = O :=
                  Submodule.eq_of_le_of_finrank_le inf_le_left hfin
                rw [← heq_inf]
                exact inf_le_right
              have hprof_le : ∀ j : Fin e, profile O t j + s ≤ w := by
                intro j
                obtain ⟨a, b, hab⟩ := hlam t j1 j
                have hside_le : side t j1 a ≤ side t j b := by
                  apply Submodule.span_mono
                  rintro v ⟨u, hu1, huv⟩
                  exact ⟨u, hab u hu1, huv⟩
                have hO_side_a : O ≤ side t j1 a := by
                  cases a
                  · exact le_trans hO_le_bd inf_le_right
                  · exact le_trans hO_le_bd inf_le_left
                have hO_side_b : O ≤ side t j b := le_trans hO_side_a hside_le
                have hmap_eq :
                    ((side t j true).map O.mkQ) ⊓ ((side t j false).map O.mkQ) =
                      (boundary t j).map O.mkQ := by
                  cases b
                  · rw [inf_comm, PEqualNP.Outside.L_lib_861_aux.map_mkQ_inf_eq_of_le O
                      (side t j false) (side t j true) hO_side_b, inf_comm]
                  · exact PEqualNP.Outside.L_lib_861_aux.map_mkQ_inf_eq_of_le O
                      (side t j true) (side t j false) hO_side_b
                have hprof_eq : profile O t j = Module.finrank (ZMod 2) ((boundary t j).map O.mkQ) := by
                  show Module.finrank (ZMod 2)
                    (((side t j true).map O.mkQ) ⊓ ((side t j false).map O.mkQ) :
                      Submodule (ZMod 2) ((Fin d → ZMod 2) ⧸ O)) = _
                  rw [hmap_eq]
                have hrn : Module.finrank (ZMod 2) ((boundary t j).map O.mkQ) +
                    Module.finrank (ZMod 2) ((O ⊓ boundary t j : Submodule (ZMod 2) (Fin d → ZMod 2))) =
                      Module.finrank (ZMod 2) (boundary t j) :=
                  PEqualNP.Outside.L_lib_861_aux.finrank_map_mkQ_add_inf O (boundary t j)
                have hbdj : s + Module.finrank (ZMod 2) (boundary t j) ≤
                    w + Module.finrank (ZMod 2) ((O ⊓ boundary t j : Submodule (ZMod 2) (Fin d → ZMod 2))) :=
                  hbd j
                omega
              have hsup_le : peak O t ≤ w - s := by
                apply Finset.sup_le
                intro j _
                have := hprof_le j
                omega
              omega
            · rw [Finset.not_nonempty_iff_eq_empty] at he0
              have hp0 : peak O t = 0 := by
                show (Finset.univ : Finset (Fin e)).sup (profile O t) = 0
                rw [he0]
                rfl
              omega
          omega
        have hle : s ≤ d := PEqualNP.Outside.L_lib_861_aux.finrank_le_d O
        rw [← pow_add, ← pow_add]
        congr 1
        omega
      have hmul_eq : 2 ^ d * (∑ i : Fin n, 2 ^ (peak (masks i) (layout i))) = 2 ^ d * 2 ^ w := by
        rw [Finset.mul_sum]
        calc
          ∑ i : Fin n, 2 ^ d * 2 ^ (peak (masks i) (layout i))
              = ∑ i : Fin n, 2 ^ (d - Module.finrank (ZMod 2) (masks i)) * 2 ^ w :=
                Finset.sum_congr rfl (fun i _ => hterm_eq i)
          _ = (∑ i : Fin n, 2 ^ (d - Module.finrank (ZMod 2) (masks i))) * 2 ^ w :=
                (Finset.sum_mul _ _ _).symm
          _ = 2 ^ d * 2 ^ w := by rw [hcov_eq]
      exact Nat.eq_of_mul_eq_mul_left hpos_d hmul_eq
