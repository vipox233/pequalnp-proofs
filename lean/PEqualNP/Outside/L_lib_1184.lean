import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1184_aux

private abbrev Loc (n : Nat) := Finset (Fin n)
private abbrev Wrd (n r : Nat) := Fin r → Loc n

private def xorL {n : Nat} (x y : Loc n) : Loc n :=
  (x \ y) ∪ (y \ x)

private lemma mem_xorL {n : Nat} (x y : Loc n) (u : Fin n) :
    u ∈ xorL x y ↔ (u ∈ x ↔ u ∉ y) := by
  simp only [xorL, Finset.mem_union, Finset.mem_sdiff]
  tauto

private lemma xorL_invol {n : Nat} (x y : Loc n) : xorL (xorL x y) y = x := by
  ext u
  simp only [mem_xorL]
  tauto

private lemma xorL_comm {n : Nat} (x y : Loc n) : xorL x y = xorL y x := by
  ext u
  simp only [mem_xorL]
  tauto

private lemma xorL_self {n : Nat} (x : Loc n) : xorL x x = ∅ := by
  ext u
  simp [mem_xorL]

private lemma xorL_empty {n : Nat} (x : Loc n) : xorL x ∅ = x := by
  ext u
  simp [mem_xorL]

private lemma xorL_eq_empty_iff {n : Nat} (x y : Loc n) : xorL x y = ∅ ↔ x = y := by
  constructor
  · intro h
    have h1 := congrArg (fun z => xorL z y) h
    rw [xorL_invol] at h1
    rw [h1]
    ext u; simp [mem_xorL]
  · intro h; subst h; exact xorL_self x

private lemma inter_xorL {n : Nat} (E x y : Loc n) :
    xorL x y ∩ E = xorL (x ∩ E) (y ∩ E) := by
  ext u
  simp only [Finset.mem_inter, mem_xorL]
  tauto

private lemma card_xorL_add {n : Nat} (a b : Loc n) :
    (xorL a b).card + 2 * (a ∩ b).card = a.card + b.card := by
  have hdisj : Disjoint (xorL a b) (a ∩ b) := by
    rw [Finset.disjoint_left]
    intro u h1 h2
    simp only [mem_xorL, Finset.mem_inter] at h1 h2
    tauto
  have hunion : xorL a b ∪ (a ∩ b) = a ∪ b := by
    ext u
    simp only [Finset.mem_union, mem_xorL, Finset.mem_inter]
    tauto
  have h1 : (xorL a b).card + (a ∩ b).card = (a ∪ b).card := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  have h2 := Finset.card_union_add_card_inter a b
  omega

private def shatters {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (T : Finset α) : Prop :=
  ∀ U ⊆ T, ∃ A ∈ F, A ∩ T = U

private noncomputable def shat {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset (Finset α)) : Finset (Finset α) := by
  classical
  exact (Finset.univ : Finset (Finset α)).filter (shatters F)

private lemma mem_shat {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset (Finset α)) (T : Finset α) :
    T ∈ shat F ↔ shatters F T := by
  classical
  simp [shat]

private lemma shat_mono {α : Type*} [Fintype α] [DecidableEq α]
    {F1 F2 : Finset (Finset α)} (hsub : F1 ⊆ F2) : shat F1 ⊆ shat F2 := by
  intro T hT
  rw [mem_shat] at hT ⊢
  intro U hU
  rcases hT U hU with ⟨A, hA, hAU⟩
  exact ⟨A, hsub hA, hAU⟩

private lemma pajor_aux {α : Type*} [Fintype α] [DecidableEq α] :
    ∀ (k : Nat) (F : Finset (Finset α)), F.card = k → F.card ≤ (shat F).card := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro F hFcard
    by_cases hk0 : k = 0
    · omega
    by_cases hk1 : k = 1
    · have hpos : 0 < F.card := by omega
      obtain ⟨A, hA⟩ := Finset.card_pos.mp hpos
      have hemp : (∅ : Finset α) ∈ shat F := by
        rw [mem_shat]
        intro U hU
        have hU0 : U = ∅ := Finset.subset_empty.mp hU
        subst hU0
        exact ⟨A, hA, by simp⟩
      have hge1 : 1 ≤ (shat F).card := Finset.card_pos.mpr ⟨∅, hemp⟩
      omega
    · have hgt1 : 1 < F.card := by omega
      obtain ⟨A, hA, B, hB, hAB⟩ := Finset.one_lt_card.mp hgt1
      have hexv : ∃ v : α, (v ∈ A ∧ v ∉ B) ∨ (v ∈ B ∧ v ∉ A) := by
        by_contra h
        push Not at h
        apply hAB
        ext v
        have hv := h v
        tauto
      rcases hexv with ⟨v, hv⟩
      let F0 := F.filter (fun X => v ∉ X)
      let F1 := F.filter (fun X => v ∈ X)
      have hdisjF : Disjoint F0 F1 := by
        rw [Finset.disjoint_left]
        intro X h0 h1
        simp only [F0, F1, Finset.mem_filter] at h0 h1
        exact h0.2 h1.2
      have hunionF : F0 ∪ F1 = F := by
        ext X
        simp only [F0, F1, Finset.mem_union, Finset.mem_filter]
        tauto
      have hcardF : F0.card + F1.card = F.card := by
        rw [← Finset.card_union_of_disjoint hdisjF, hunionF]
      have hF0ne : F0.Nonempty := by
        rcases hv with ⟨_, hvB⟩ | ⟨_, hvA⟩
        · exact ⟨B, by simp [F0, hB, hvB]⟩
        · exact ⟨A, by simp [F0, hA, hvA]⟩
      have hF1ne : F1.Nonempty := by
        rcases hv with ⟨hvA, _⟩ | ⟨hvB, _⟩
        · exact ⟨A, by simp [F1, hA, hvA]⟩
        · exact ⟨B, by simp [F1, hB, hvB]⟩
      have h0pos : 0 < F0.card := Finset.card_pos.mpr hF0ne
      have h1pos : 0 < F1.card := Finset.card_pos.mpr hF1ne
      have hle0 : F0.card ≤ (shat F0).card := ih F0.card (by omega) F0 rfl
      have hle1 : F1.card ≤ (shat F1).card := ih F1.card (by omega) F1 rfl
      have hnot0 : ∀ T ∈ shat F0, v ∉ T := by
        intro T hT hvT
        rw [mem_shat] at hT
        rcases hT {v} (Finset.singleton_subset_iff.mpr hvT) with ⟨X, hX, hXT⟩
        have hvX : v ∈ X := by
          have : v ∈ X ∩ T := by rw [hXT]; simp
          exact (Finset.mem_inter.mp this).1
        simp only [F0, Finset.mem_filter] at hX
        exact hX.2 hvX
      have hnot1 : ∀ T ∈ shat F1, v ∉ T := by
        intro T hT hvT
        rw [mem_shat] at hT
        rcases hT ∅ (Finset.empty_subset T) with ⟨X, hX, hXT⟩
        simp only [F1, Finset.mem_filter] at hX
        have hvXT : v ∈ X ∩ T := Finset.mem_inter.mpr ⟨hX.2, hvT⟩
        rw [hXT] at hvXT
        exact Finset.notMem_empty v hvXT
      let U := shat F0 ∪ shat F1
      let I := shat F0 ∩ shat F1
      let I' := I.image (insert v)
      have hUsub : U ⊆ shat F :=
        Finset.union_subset (shat_mono (Finset.filter_subset _ F)) (shat_mono (Finset.filter_subset _ F))
      have hI'sub : I' ⊆ shat F := by
        intro T' hT'
        rcases Finset.mem_image.mp hT' with ⟨T, hTI, rfl⟩
        have hT0 : T ∈ shat F0 := (Finset.mem_inter.mp hTI).1
        have hT1 : T ∈ shat F1 := (Finset.mem_inter.mp hTI).2
        rw [mem_shat] at hT0 hT1 ⊢
        intro W hW
        by_cases hvW : v ∈ W
        · have hWsub : W.erase v ⊆ T := by
            intro u hu
            have hu1 := Finset.mem_erase.mp hu
            have hu2 := hW hu1.2
            simp only [Finset.mem_insert] at hu2
            rcases hu2 with rfl | huT
            · exact (hu1.1 rfl).elim
            · exact huT
          rcases hT1 (W.erase v) hWsub with ⟨X, hX, hXT⟩
          simp only [F1, Finset.mem_filter] at hX
          refine ⟨X, hX.1, ?_⟩
          ext u
          simp only [Finset.mem_inter, Finset.mem_insert]
          by_cases huv : u = v
          · subst huv
            simp [hX.2, hvW]
          · have hiff : u ∈ X ∩ T ↔ u ∈ W.erase v := by rw [hXT]
            simp only [Finset.mem_inter, Finset.mem_erase, huv, ne_eq, not_false_eq_true, true_and] at hiff
            simp [huv, hiff]
        · have hWsub : W ⊆ T := by
            intro u hu
            have hu2 := hW hu
            simp only [Finset.mem_insert] at hu2
            rcases hu2 with rfl | huT
            · exact (hvW hu).elim
            · exact huT
          rcases hT0 W hWsub with ⟨X, hX, hXT⟩
          simp only [F0, Finset.mem_filter] at hX
          refine ⟨X, hX.1, ?_⟩
          ext u
          simp only [Finset.mem_inter, Finset.mem_insert]
          by_cases huv : u = v
          · subst huv
            simp [hX.2, hvW]
          · have hiff : u ∈ X ∩ T ↔ u ∈ W := by rw [hXT]
            simp only [Finset.mem_inter] at hiff
            simp [huv, hiff]
      have hdisjUI : Disjoint U I' := by
        rw [Finset.disjoint_left]
        intro S hSU hSI
        rcases Finset.mem_image.mp hSI with ⟨T, _, rfl⟩
        have hvS : v ∈ insert v T := Finset.mem_insert_self v T
        rcases Finset.mem_union.mp hSU with h0 | h1
        · exact hnot0 _ h0 hvS
        · exact hnot1 _ h1 hvS
      have hI'card : I'.card = I.card := by
        refine Finset.card_image_of_injOn ?_
        intro T1 hT1 T2 hT2 heq
        have hv1 : v ∉ T1 := hnot0 T1 (Finset.mem_inter.mp hT1).1
        have hv2 : v ∉ T2 := hnot0 T2 (Finset.mem_inter.mp hT2).1
        have h1 : (insert v T1).erase v = (insert v T2).erase v := congrArg (fun S => S.erase v) heq
        simpa [Finset.erase_insert hv1, Finset.erase_insert hv2] using h1
      have hsub : U ∪ I' ⊆ shat F := Finset.union_subset hUsub hI'sub
      have hcard_le := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hdisjUI, hI'card] at hcard_le
      dsimp only [U, I] at hcard_le
      have hUI := Finset.card_union_add_card_inter (shat F0) (shat F1)
      omega

private lemma card_ball2 (n : Nat) :
    ((Finset.univ : Finset (Loc n)).filter (fun y => y.card ≤ 2)).card =
      1 + n + Nat.choose n 2 := by
  let L0 := (Finset.univ : Finset (Fin n)).powersetCard 0
  let L1 := (Finset.univ : Finset (Fin n)).powersetCard 1
  let L2 := (Finset.univ : Finset (Fin n)).powersetCard 2
  have heq : (Finset.univ : Finset (Loc n)).filter (fun y => y.card ≤ 2) = L0 ∪ L1 ∪ L2 := by
    ext y
    simp only [L0, L1, L2, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_powersetCard, Finset.subset_univ]
    omega
  have hd01 : Disjoint L0 L1 := by
    rw [Finset.disjoint_left]
    intro y h0 h1
    rw [Finset.mem_powersetCard] at h0 h1
    omega
  have hd012 : Disjoint (L0 ∪ L1) L2 := by
    rw [Finset.disjoint_left]
    intro y h01 h2
    rw [Finset.mem_powersetCard] at h2
    rcases Finset.mem_union.mp h01 with h0 | h1
    · rw [Finset.mem_powersetCard] at h0; omega
    · rw [Finset.mem_powersetCard] at h1; omega
  rw [heq, Finset.card_union_of_disjoint hd012, Finset.card_union_of_disjoint hd01]
  simp [L0, L1, L2, Finset.card_powersetCard]

private lemma card_word (n r : Nat) :
    (Finset.univ : Finset (Wrd n r)).card = 2 ^ (n * r) := by
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_finset, Fintype.card_fin]
  rw [← pow_mul]

private lemma card_physical_coord_le (n : Nat) (s : Loc n → Loc n) :
    ((Finset.univ : Finset (Loc n)).filter (fun y =>
      ∀ E ∈ (Finset.univ : Finset (Fin n)).powersetCard 3, y ∩ E ≠ s E ∩ E)).card ≤
      1 + n + Nat.choose n 2 := by
  let R := (Finset.univ : Finset (Loc n)).filter (fun y =>
    ∀ E ∈ (Finset.univ : Finset (Fin n)).powersetCard 3, y ∩ E ≠ s E ∩ E)
  have hpaj := pajor_aux R.card R rfl
  have hsub : shat R ⊆ (Finset.univ : Finset (Loc n)).filter (fun T => T.card ≤ 2) := by
    intro T hT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra hgt
    have hge : 3 ≤ T.card := by omega
    obtain ⟨E, hET, hEcard⟩ := Finset.exists_subset_card_eq hge
    have hE3 : E ∈ (Finset.univ : Finset (Fin n)).powersetCard 3 :=
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ E, hEcard⟩
    rw [mem_shat] at hT
    rcases hT (s E ∩ E) ((Finset.inter_subset_right).trans hET) with ⟨y, hyR, hyT⟩
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hyR
    apply hyR E hE3
    have hinter : y ∩ E = (y ∩ T) ∩ E := by
      ext u
      simp only [Finset.mem_inter]
      exact ⟨fun ⟨h1, h2⟩ => ⟨⟨h1, hET h2⟩, h2⟩, fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩⟩
    rw [hinter, hyT, Finset.inter_assoc, Finset.inter_self]
  exact hpaj.trans ((Finset.card_le_card hsub).trans (le_of_eq (card_ball2 n)))

private lemma card_filter_pi {n r : Nat} (P : Fin r → Loc n → Prop) [∀ j, DecidablePred (P j)] :
    ((Finset.univ : Finset (Wrd n r)).filter (fun x => ∀ j, P j (x j))).card =
      ∏ j : Fin r, ((Finset.univ : Finset (Loc n)).filter (fun y => P j y)).card := by
  have heq : (Finset.univ : Finset (Wrd n r)).filter (fun x => ∀ j, P j (x j)) =
      Fintype.piFinset (fun j => (Finset.univ : Finset (Loc n)).filter (fun y => P j y)) := by
    ext x
    simp [Fintype.mem_piFinset]
  rw [heq, Fintype.card_piFinset]

private lemma card_radial_coord (n : Nat) (c : Loc n) :
    ((Finset.univ : Finset (Loc n)).filter (fun y => (xorL y c).card ≤ 2)).card =
      1 + n + Nat.choose n 2 := by
  have hbij : ((Finset.univ : Finset (Loc n)).filter (fun y => (xorL y c).card ≤ 2)).card =
      ((Finset.univ : Finset (Loc n)).filter (fun z => z.card ≤ 2)).card := by
    refine Finset.card_nbij (fun y => xorL y c) ?_ ?_ ?_
    · intro y hy
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      exact hy
    · intro y1 _ y2 _ h
      have h1 := congrArg (fun z => xorL z c) h
      simpa [xorL_invol] using h1
    · intro z hz
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      refine ⟨xorL z c, ?_, xorL_invol z c⟩
      simp [xorL_invol, hz]
  rw [hbij, card_ball2]

private lemma good_implies_uniform {n r N V : Nat}
    (tests : Fin N → Wrd n r → Bool)
    (hsz : ∀ i : Fin N, ((Finset.univ : Finset (Wrd n r)).filter (fun x => tests i x = true)).card ≤ V ^ r)
    (hgood : ∃ answer : Fin N → Bool → Bool,
      (∀ i, answer i false = false) ∧ ∀ A : Finset (Wrd n r), A.Nonempty →
        V ^ r * N ≤ 2 ^ (n * r) * ((Finset.univ : Finset (Fin N)).filter (fun i =>
          answer i (A.toList.any (tests i)))).card) :
    ∀ x : Wrd n r,
      2 ^ (n * r) * ((Finset.univ : Finset (Fin N)).filter (fun i => tests i x = true)).card =
        V ^ r * N := by
  rcases hgood with ⟨answer, hfalse, hspec⟩
  let deg : Wrd n r → Nat := fun x =>
    ((Finset.univ : Finset (Fin N)).filter (fun i => tests i x = true)).card
  have hge : ∀ x : Wrd n r, V ^ r * N ≤ 2 ^ (n * r) * deg x := by
    intro x
    have h1 := hspec {x} (Finset.singleton_nonempty x)
    have hsub :
        (Finset.univ : Finset (Fin N)).filter (fun i => answer i (({x} : Finset (Wrd n r)).toList.any (tests i)) = true) ⊆
        (Finset.univ : Finset (Fin N)).filter (fun i => tests i x = true) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      have hany : ({x} : Finset (Wrd n r)).toList.any (tests i) = tests i x := by
        apply Bool.eq_iff_iff.mpr
        simp [List.any_eq_true, Finset.mem_toList]
      rw [hany] at hi
      cases ht : tests i x
      · rw [ht, hfalse i] at hi; exact Bool.noConfusion hi
      · rfl
    exact h1.trans (Nat.mul_le_mul_left _ (Finset.card_le_card hsub))
  have hsum_deg : ∑ x : Wrd n r, deg x ≤ N * V ^ r := by
    have hswap : ∑ x : Wrd n r, deg x =
        ∑ i : Fin N, ((Finset.univ : Finset (Wrd n r)).filter (fun x => tests i x = true)).card := by
      calc
        ∑ x : Wrd n r, deg x
          = ∑ x : Wrd n r, ∑ i : Fin N, (if tests i x = true then 1 else 0) := by
            refine Finset.sum_congr rfl (fun x _ => ?_)
            exact Finset.card_filter _ _
        _ = ∑ i : Fin N, ∑ x : Wrd n r, (if tests i x = true then 1 else 0) := Finset.sum_comm
        _ = ∑ i : Fin N, ((Finset.univ : Finset (Wrd n r)).filter (fun x => tests i x = true)).card := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            exact (Finset.card_filter _ _).symm
    rw [hswap]
    calc
      ∑ i : Fin N, ((Finset.univ : Finset (Wrd n r)).filter (fun x => tests i x = true)).card
        ≤ ∑ _i : Fin N, V ^ r := Finset.sum_le_sum (fun i _ => hsz i)
      _ = N * V ^ r := by simp
  have hsum_le : ∑ x : Wrd n r, (2 ^ (n * r) * deg x) ≤ ∑ _x : Wrd n r, (V ^ r * N) := by
    rw [← Finset.mul_sum, Finset.sum_const, card_word, smul_eq_mul]
    calc
      2 ^ (n * r) * ∑ x : Wrd n r, deg x ≤ 2 ^ (n * r) * (N * V ^ r) :=
        Nat.mul_le_mul_left _ hsum_deg
      _ = 2 ^ (n * r) * (V ^ r * N) := by ring
  intro x
  have hsplit1 : 2 ^ (n * r) * deg x + ((Finset.univ : Finset (Wrd n r)).erase x).sum (fun y => 2 ^ (n * r) * deg y) =
      ∑ y : Wrd n r, (2 ^ (n * r) * deg y) :=
    Finset.add_sum_erase Finset.univ (fun y => 2 ^ (n * r) * deg y) (Finset.mem_univ x)
  have hsplit2 : V ^ r * N + ((Finset.univ : Finset (Wrd n r)).erase x).sum (fun _ => V ^ r * N) =
      ∑ _y : Wrd n r, (V ^ r * N) :=
    Finset.add_sum_erase Finset.univ (fun _ => V ^ r * N) (Finset.mem_univ x)
  have hrest : ((Finset.univ : Finset (Wrd n r)).erase x).sum (fun _ => V ^ r * N) ≤
      ((Finset.univ : Finset (Wrd n r)).erase x).sum (fun y => 2 ^ (n * r) * deg y) :=
    Finset.sum_le_sum (fun y _ => hge y)
  have hxge := hge x
  change 2 ^ (n * r) * deg x = V ^ r * N
  omega

private lemma uniform_implies_good {n r N V : Nat}
    (tests : Fin N → Wrd n r → Bool)
    (hunif : ∀ x : Wrd n r,
      V ^ r * N ≤ 2 ^ (n * r) * ((Finset.univ : Finset (Fin N)).filter (fun i => tests i x = true)).card) :
    ∃ answer : Fin N → Bool → Bool,
      (∀ i, answer i false = false) ∧ ∀ A : Finset (Wrd n r), A.Nonempty →
        V ^ r * N ≤ 2 ^ (n * r) * ((Finset.univ : Finset (Fin N)).filter (fun i =>
          answer i (A.toList.any (tests i)))).card := by
  refine ⟨fun _ b => b, fun _ => rfl, ?_⟩
  intro A hAne
  obtain ⟨x0, hx0⟩ := hAne
  have hsub :
      (Finset.univ : Finset (Fin N)).filter (fun i => tests i x0 = true) ⊆
      (Finset.univ : Finset (Fin N)).filter (fun i => A.toList.any (tests i) = true) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact List.any_eq_true.mpr ⟨x0, Finset.mem_toList.mpr hx0, hi⟩
  exact (hunif x0).trans (Nat.mul_le_mul_left _ (Finset.card_le_card hsub))

private lemma exists_balanced_physical_single (n : Nat) (hn : 3 ≤ n)
    (hV4 : (1 + n + Nat.choose n 2) % 4 = 2) :
    ∃ sFam : Finset (Fin (n - 1)) → Loc n → Loc n,
      ∀ y : Loc n,
        ((Finset.univ : Finset (Finset (Fin (n - 1)))).filter (fun t =>
          ∀ E ∈ (Finset.univ : Finset (Fin n)).powersetCard 3, y ∩ E ≠ sFam t E ∩ E)).card =
        (1 + n + Nat.choose n 2) / 2 := by
  let m := n - 1
  have hmn : m + 1 = n := by omega
  let e : Option (Fin m) ≃ Fin n :=
    (Equiv.optionCongr (Equiv.refl (Fin m))).trans
      { toFun := fun o => match o with
          | none => ⟨m, by omega⟩
          | some i => ⟨i.val, by omega⟩
        invFun := fun u => if h : u.val < m then some ⟨u.val, h⟩ else none
        left_inv := fun o => by
          cases o with
          | none => simp
          | some i => simp [i.isLt]
        right_inv := fun u => by
          by_cases h : u.val < m
          · simp [h]
          · have hu : u.val = m := by omega
            simp [h]
            exact Fin.ext hu.symm }
  let lastV : Fin n := e none
  let castV : Fin m → Fin n := fun i => e (some i)
  have hcast_inj : Function.Injective castV := fun i j h => Option.some.inj (e.injective h)
  have hcast_ne_last : ∀ i : Fin m, castV i ≠ lastV := fun i h => by
    have h1 := e.injective h
    cases h1
  let enc : Finset (Fin m) → Bool → Loc n := fun x b =>
    if b then insert lastV (x.image castV) else x.image castV
  let proj : Loc n → Finset (Fin m) := fun y =>
    (Finset.univ : Finset (Fin m)).filter (fun i => castV i ∈ y)
  have hmem_enc_last : ∀ x b, lastV ∈ enc x b ↔ b = true := by
    intro x b
    have hnot : lastV ∉ x.image castV := by
      intro h; rcases Finset.mem_image.mp h with ⟨i, _, hi⟩; exact hcast_ne_last i hi
    cases b <;> simp [enc, hnot]
  have hmem_enc_cast : ∀ x b (i : Fin m), castV i ∈ enc x b ↔ i ∈ x := by
    intro x b i
    have hne := hcast_ne_last i
    cases b
    · simp only [enc, Bool.false_eq_true, ite_false, Finset.mem_image]
      exact ⟨fun ⟨j, hj, h⟩ => by rw [← hcast_inj h]; exact hj, fun hi => ⟨i, hi, rfl⟩⟩
    · simp only [enc, ite_true, Finset.mem_insert, Finset.mem_image, hne, false_or]
      exact ⟨fun ⟨j, hj, h⟩ => by rw [← hcast_inj h]; exact hj, fun hi => ⟨i, hi, rfl⟩⟩
  have henc_proj : ∀ y : Loc n, enc (proj y) (decide (lastV ∈ y)) = y := by
    intro y
    ext u
    rcases e.surjective u with ⟨o, rfl⟩
    cases o with
    | none => simp [lastV, hmem_enc_last]
    | some i =>
      change castV i ∈ enc (proj y) (decide (lastV ∈ y)) ↔ castV i ∈ y
      rw [hmem_enc_cast]
      simp [proj]
  have hcard_enc : ∀ x b, (enc x b).card = x.card + if b then 1 else 0 := by
    intro x b
    have himg : (x.image castV).card = x.card := Finset.card_image_of_injective x hcast_inj
    have hnot : lastV ∉ x.image castV := by
      intro h; rcases Finset.mem_image.mp h with ⟨i, _, hi⟩; exact hcast_ne_last i hi
    cases b
    · simp [enc, himg]
    · simp only [enc, ite_true]
      rw [Finset.card_insert_eq_ite]
      simp [hnot, himg]
  let wordsM := (Finset.univ : Finset (Finset (Fin m)))
  let small := wordsM.filter (fun x => x.card < 2)
  let shell := wordsM.filter (fun x => x.card = 2)
  have hsmall_card : small.card = n := by
    have heq : small = insert (∅ : Finset (Fin m)) ((Finset.univ : Finset (Fin m)).image (fun i => {i})) := by
      ext x
      simp only [small, wordsM, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_image]
      constructor
      · intro hlt
        by_cases h0 : x.card = 0
        · exact Or.inl (Finset.card_eq_zero.mp h0)
        · have h1 : x.card = 1 := by omega
          rcases Finset.card_eq_one.mp h1 with ⟨i, rfl⟩
          exact Or.inr ⟨i, rfl⟩
      · rintro (rfl | ⟨i, rfl⟩) <;> simp
    rw [heq, Finset.card_insert_eq_ite]
    have hnot : (∅ : Finset (Fin m)) ∉ (Finset.univ : Finset (Fin m)).image (fun i => {i}) := by simp
    have himg : ((Finset.univ : Finset (Fin m)).image (fun i => ({i} : Finset (Fin m)))).card = m := by
      rw [Finset.card_image_of_injective _ Finset.singleton_injective]; simp
    simp [hnot, himg, hmn]
  have hshell_card : shell.card = Nat.choose m 2 := by
    have heq : shell = (Finset.univ : Finset (Fin m)).powersetCard 2 := by
      ext x; simp [shell, wordsM, Finset.mem_powersetCard]
    rw [heq, Finset.card_powersetCard]
    simp
  have hV_eq : 1 + n + Nat.choose n 2 = 2 * n + shell.card := by
    have hch : Nat.choose n 2 = Nat.choose m 2 + Nat.choose m 1 := by
      rw [← hmn, Nat.choose_succ_succ]
      ring
    rw [hch, Nat.choose_one_right, hshell_card]
    omega
  have hshell_even : shell.card % 2 = 0 := by omega
  have hhalf_le : shell.card / 2 ≤ shell.card := Nat.div_le_self _ _
  obtain ⟨F, hFsub, hFcard⟩ := Finset.exists_subset_card_eq hhalf_le
  let sBase : Loc n → Loc n := fun E =>
    if lastV ∈ E then enc (proj E) (!(decide (proj E ∈ F))) else E
  let RBase : Finset (Loc n) :=
    (Finset.univ : Finset (Loc n)).filter (fun y =>
      ∀ E ∈ (Finset.univ : Finset (Fin n)).powersetCard 3, y ∩ E ≠ sBase E ∩ E)
  have hRBase_iff : ∀ y : Loc n,
      y ∈ RBase ↔ proj y ∈ small ∨ (proj y ∈ shell ∧ decide (lastV ∈ y) = decide (proj y ∈ F)) := by
    intro y
    simp only [RBase, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hforb
      have hyle : (proj y).card ≤ 2 := by
        by_contra hgt
        have hge : 3 ≤ (proj y).card := by omega
        obtain ⟨x, hxy, hxcard⟩ := Finset.exists_subset_card_eq hge
        let E := enc x false
        have hE3 : E ∈ (Finset.univ : Finset (Fin n)).powersetCard 3 := by
          rw [Finset.mem_powersetCard]
          refine ⟨Finset.subset_univ E, ?_⟩
          rw [hcard_enc]; simp [hxcard]
        have hnot : lastV ∉ E := by simp [E, hmem_enc_last]
        have hsE : sBase E = E := by simp [sBase, hnot]
        apply hforb E hE3
        rw [hsE, Finset.inter_self]
        apply Finset.inter_eq_right.mpr
        intro u hu
        rcases Finset.mem_image.mp hu with ⟨i, hi, rfl⟩
        exact (Finset.mem_filter.mp (hxy hi)).2
      by_cases hlt : (proj y).card < 2
      · exact Or.inl (by simp only [small, wordsM, Finset.mem_filter, Finset.mem_univ, true_and]; exact hlt)
      · have hy2 : (proj y).card = 2 := by omega
        refine Or.inr ⟨by simp [shell, wordsM, hy2], ?_⟩
        let E := enc (proj y) true
        have hE3 : E ∈ (Finset.univ : Finset (Fin n)).powersetCard 3 := by
          rw [Finset.mem_powersetCard]
          refine ⟨Finset.subset_univ E, ?_⟩
          rw [hcard_enc]; simp [hy2]
        have hlast : lastV ∈ E := (hmem_enc_last (proj y) true).mpr rfl
        have hprojE : proj E = proj y := by
          ext i; simp [proj, E, hmem_enc_cast]
        have hsE : sBase E = enc (proj y) (!(decide (proj y ∈ F))) := by
          simp only [sBase, hlast, ite_true, hprojE]
        have hsubE : ∀ c : Bool, enc (proj y) c ⊆ E := by
          intro c u hu
          rcases e.surjective u with ⟨o, rfl⟩
          cases o with
          | none => exact hlast
          | some i =>
            change castV i ∈ E
            rw [hmem_enc_cast]
            exact (hmem_enc_cast (proj y) c i).mp hu
        have hne := hforb E hE3
        have hy_eq : y = enc (proj y) (decide (lastV ∈ y)) := (henc_proj y).symm
        rw [hy_eq, hsE, Finset.inter_eq_left.mpr (hsubE _), Finset.inter_eq_left.mpr (hsubE _)] at hne
        cases hb : decide (lastV ∈ y) <;> cases hF : decide (proj y ∈ F)
        · rfl
        · exfalso; apply hne; simp [hb, hF]
        · exfalso; apply hne; simp [hb, hF]
        · rfl
    · intro hmem E hE3 heq
      rw [Finset.mem_powersetCard] at hE3
      have hEcard := hE3.2
      by_cases hlast : lastV ∈ E
      · have hEeq : E = enc (proj E) true := by
          have h1 := henc_proj E
          simpa [hlast] using h1.symm
        have hpEcard : (proj E).card = 2 := by
          have hc : E.card = (proj E).card + 1 := by
            conv_lhs => rw [hEeq]
            rw [hcard_enc]
            simp
          omega
        have hsE : sBase E = enc (proj E) (!(decide (proj E ∈ F))) := by
          simp only [sBase, hlast, ite_true]
        have hsubE : enc (proj E) (!(decide (proj E ∈ F))) ⊆ E := by
          intro u hu
          rcases e.surjective u with ⟨o, rfl⟩
          cases o with
          | none => exact hlast
          | some i =>
            have hi := (hmem_enc_cast (proj E) _ i).mp hu
            exact (Finset.mem_filter.mp hi).2
        rw [hsE, Finset.inter_eq_left.mpr hsubE] at heq
        have hsub : proj E ⊆ proj y := by
          intro i hi
          have hm1 : castV i ∈ enc (proj E) (!(decide (proj E ∈ F))) := (hmem_enc_cast _ _ i).mpr hi
          rw [← heq] at hm1
          simp only [proj, Finset.mem_filter, Finset.mem_univ, true_and]
          exact (Finset.mem_inter.mp hm1).1
        have hbl : decide (lastV ∈ y) = !(decide (proj E ∈ F)) := by
          have hm : lastV ∈ y ∩ E ↔ lastV ∈ enc (proj E) (!(decide (proj E ∈ F))) := by rw [heq]
          simp only [Finset.mem_inter, hlast, and_true, hmem_enc_last] at hm
          exact Bool.eq_iff_iff.mpr (by simpa using hm)
        rcases hmem with hsm | ⟨hsh, hbf⟩
        · simp only [small, wordsM, Finset.mem_filter, Finset.mem_univ, true_and] at hsm
          have := Finset.card_le_card hsub
          omega
        · simp only [shell, wordsM, Finset.mem_filter, Finset.mem_univ, true_and] at hsh
          have hpeq : proj E = proj y := Finset.eq_of_subset_of_card_le hsub (by omega)
          rw [hpeq, hbf] at hbl
          cases hdec : decide (proj y ∈ F) <;> simp [hdec] at hbl
      · have hsE : sBase E = E := by simp [sBase, hlast]
        rw [hsE, Finset.inter_self] at heq
        have hsub : E ⊆ y := Finset.inter_eq_right.mp heq
        have hEeq : E = enc (proj E) false := by
          have h1 := henc_proj E
          simpa [hlast] using h1.symm
        have hpEcard : (proj E).card = 3 := by
          have hc : E.card = (proj E).card := by
            conv_lhs => rw [hEeq]
            rw [hcard_enc]
            simp
          omega
        have hsubp : proj E ⊆ proj y := by
          intro i hi
          simp only [proj, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
          exact hsub hi
        have := Finset.card_le_card hsubp
        rcases hmem with hsm | ⟨hsh, _⟩
        · simp only [small, wordsM, Finset.mem_filter, Finset.mem_univ, true_and] at hsm; omega
        · simp only [shell, wordsM, Finset.mem_filter, Finset.mem_univ, true_and] at hsh; omega
  have hcount_b : ∀ b : Bool,
      (wordsM.filter (fun x => enc x b ∈ RBase)).card = (1 + n + Nat.choose n 2) / 2 := by
    intro b
    have hfilt : wordsM.filter (fun x => enc x b ∈ RBase) =
        small ∪ (if b then F else shell \ F) := by
      ext x
      have hpx : proj (enc x b) = x := by
        ext i; simp [proj, hmem_enc_cast]
      simp only [Finset.mem_filter, wordsM, Finset.mem_univ, true_and, hRBase_iff, hpx,
        hmem_enc_last, Finset.mem_union]
      cases b
      · simp only [Bool.false_eq_true, decide_false, ite_false, Finset.mem_sdiff]
        constructor
        · rintro (hsm | ⟨hsh, hdec⟩)
          · exact Or.inl hsm
          · refine Or.inr ⟨hsh, ?_⟩
            intro hxF; simp [hxF] at hdec
        · rintro (hsm | ⟨hsh, hnotF⟩)
          · exact Or.inl hsm
          · exact Or.inr ⟨hsh, by simp [hnotF]⟩
      · simp only [decide_true, ite_true]
        constructor
        · rintro (hsm | ⟨_, hdec⟩)
          · exact Or.inl hsm
          · exact Or.inr (of_decide_eq_true hdec.symm)
        · rintro (hsm | hxF)
          · exact Or.inl hsm
          · exact Or.inr ⟨hFsub hxF, by simp [hxF]⟩
    have hdisj : Disjoint small (if b then F else shell \ F) := by
      rw [Finset.disjoint_left]
      intro x hsm h2
      have hsh : x ∈ shell := by
        cases b
        · simp only [Bool.false_eq_true, ite_false, Finset.mem_sdiff] at h2; exact h2.1
        · simp only [ite_true] at h2; exact hFsub h2
      simp only [small, shell, wordsM, Finset.mem_filter, Finset.mem_univ, true_and] at hsm hsh
      omega
    rw [hfilt, Finset.card_union_of_disjoint hdisj, hsmall_card]
    cases b
    · simp only [Bool.false_eq_true, ite_false]
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hFsub, hFcard]
      omega
    · simp only [ite_true, hFcard]
      omega
  let sFam : Finset (Fin m) → Loc n → Loc n := fun t E => xorL (sBase E) (enc t false)
  refine ⟨sFam, ?_⟩
  intro y
  have hpass_iff : ∀ t : Finset (Fin m),
      (∀ E ∈ (Finset.univ : Finset (Fin n)).powersetCard 3, y ∩ E ≠ sFam t E ∩ E) ↔
      xorL y (enc t false) ∈ RBase := by
    intro t
    simp only [RBase, Finset.mem_filter, Finset.mem_univ, true_and]
    refine forall₂_congr (fun E _ => ?_)
    simp only [sFam, inter_xorL, ne_eq]
    constructor
    · intro h heq
      apply h
      have h1 := congrArg (fun z => xorL z (enc t false ∩ E)) heq
      simpa [xorL_invol] using h1
    · intro h heq
      apply h
      have h1 := congrArg (fun z => xorL z (enc t false ∩ E)) heq
      simpa [xorL_invol] using h1
  have hxor_enc : ∀ t : Finset (Fin m),
      xorL y (enc t false) = enc (xorL (proj y) t) (decide (lastV ∈ y)) := by
    intro t
    ext u
    rcases e.surjective u with ⟨o, rfl⟩
    cases o with
    | none =>
      change lastV ∈ xorL y (enc t false) ↔ lastV ∈ enc (xorL (proj y) t) (decide (lastV ∈ y))
      rw [mem_xorL, hmem_enc_last, hmem_enc_last]
      simp
    | some i =>
      change castV i ∈ xorL y (enc t false) ↔ castV i ∈ enc (xorL (proj y) t) (decide (lastV ∈ y))
      rw [mem_xorL, hmem_enc_cast, hmem_enc_cast, mem_xorL]
      simp [proj]
  have hbij :
      ((Finset.univ : Finset (Finset (Fin m))).filter (fun t =>
        ∀ E ∈ (Finset.univ : Finset (Fin n)).powersetCard 3, y ∩ E ≠ sFam t E ∩ E)).card =
      (wordsM.filter (fun x => enc x (decide (lastV ∈ y)) ∈ RBase)).card := by
    refine Finset.card_nbij (fun t => xorL (proj y) t) ?_ ?_ ?_
    · intro t ht
      simp only [Finset.mem_coe, wordsM, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      rw [← hxor_enc t]
      exact (hpass_iff t).mp ht
    · intro t1 _ t2 _ h
      dsimp only at h
      have h1 := congrArg (fun z => xorL z (proj y)) h
      rw [xorL_comm (proj y) t1, xorL_comm (proj y) t2, xorL_invol, xorL_invol] at h1
      exact h1
    · intro x hx
      simp only [Finset.mem_coe, wordsM, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      refine ⟨xorL (proj y) x, ?_, ?_⟩
      · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hpass_iff, hxor_enc]
        have hinv : xorL (proj y) (xorL (proj y) x) = x := by
          rw [xorL_comm (proj y) x, xorL_comm (proj y) (xorL x (proj y)), xorL_invol]
        rw [hinv]
        exact hx
      · dsimp only
        rw [xorL_comm (proj y) x, xorL_comm (proj y) (xorL x (proj y)), xorL_invol]
  rw [hbij, hcount_b]

private def chi1 {n : Nat} (u v : Loc n) : Int :=
  (-1 : Int) ^ (u ∩ v).card

private def chi {n r : Nat} (a b : Wrd n r) : Int :=
  ∏ j : Fin r, chi1 (a j) (b j)

private lemma chi1_comm {n : Nat} (u v : Loc n) : chi1 u v = chi1 v u := by
  simp [chi1, Finset.inter_comm]

private lemma chi_comm {n r : Nat} (a b : Wrd n r) : chi a b = chi b a := by
  unfold chi
  exact Finset.prod_congr rfl (fun j _ => chi1_comm (a j) (b j))

private lemma chi1_empty_left {n : Nat} (v : Loc n) : chi1 ∅ v = 1 := by
  simp [chi1]

private lemma chi_zero_left {n r : Nat} (b : Wrd n r) : chi (fun _ => ∅) b = 1 := by
  simp [chi, chi1_empty_left]

private lemma chi1_xorL {n : Nat} (u x y : Loc n) :
    chi1 u (xorL x y) = chi1 u x * chi1 u y := by
  unfold chi1
  have h1 : u ∩ xorL x y = xorL (u ∩ x) (u ∩ y) := by
    rw [Finset.inter_comm, inter_xorL, Finset.inter_comm x u, Finset.inter_comm y u]
  rw [h1, ← pow_add]
  have hcard := card_xorL_add (u ∩ x) (u ∩ y)
  rw [← hcard, pow_add, pow_mul]
  norm_num

private lemma chi_xorW {n r : Nat} (a x y : Wrd n r) :
    chi a (fun j => xorL (x j) (y j)) = chi a x * chi a y := by
  unfold chi
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun j _ => chi1_xorL (a j) (x j) (y j))

private lemma sum_chi1 {n : Nat} (u : Loc n) :
    ∑ x : Loc n, chi1 u x = if u = ∅ then (2 ^ n : Int) else 0 := by
  by_cases hu : u = ∅
  · subst hu
    simp [chi1_empty_left]
  · simp only [hu, ite_false]
    obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hu
    have hflip : ∀ x : Loc n, chi1 u (xorL x {v}) = - chi1 u x := by
      intro x
      rw [chi1_xorL]
      have h1 : (u ∩ {v}).card = 1 := by
        have heq : u ∩ {v} = {v} := by
          ext w; simp only [Finset.mem_inter, Finset.mem_singleton]
          exact ⟨fun h => h.2, fun h => ⟨h ▸ hv, h⟩⟩
        rw [heq]; simp
      simp [chi1, h1]
    have hsum_eq : ∑ x : Loc n, chi1 u x = ∑ x : Loc n, chi1 u (xorL x {v}) := by
      refine Fintype.sum_equiv (Equiv.mk (fun x => xorL x {v}) (fun x => xorL x {v})
        (fun x => xorL_invol x {v}) (fun x => xorL_invol x {v})) _ _ (fun x => ?_)
      simp [xorL_invol]
    have hneg : ∑ x : Loc n, chi1 u x = - ∑ x : Loc n, chi1 u x := by
      conv_lhs => rw [hsum_eq]
      simp [hflip]
    omega

private lemma sum_chi {n r : Nat} (a : Wrd n r) :
    ∑ x : Wrd n r, chi a x = if a = (fun _ => ∅) then (2 ^ (n * r) : Int) else 0 := by
  have hprod : ∑ x : Wrd n r, chi a x = ∏ j : Fin r, ∑ y : Loc n, chi1 (a j) y := by
    unfold chi
    exact (Fintype.prod_sum (fun j y => chi1 (a j) y)).symm
  rw [hprod]
  by_cases ha : a = (fun _ => ∅)
  · subst ha
    simp only [ite_true, sum_chi1, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← pow_mul]
  · simp only [ha, ite_false]
    have hex : ∃ j : Fin r, a j ≠ ∅ := by
      by_contra hall
      push Not at hall
      exact ha (funext hall)
    rcases hex with ⟨j0, hj0⟩
    refine Finset.prod_eq_zero (Finset.mem_univ j0) ?_
    rw [sum_chi1]
    simp [hj0]

private def lam {n : Nat} (u : Loc n) : Int :=
  ∑ y ∈ (Finset.univ : Finset (Loc n)).filter (fun y => y.card ≤ 2), chi1 u y

private lemma two_mul_lam {n : Nat} (hn : 3 ≤ n) (u : Loc n) :
    2 * lam u = ((n : Int) - 2 * (u.card : Int) + 1) ^ 2 - ((n - 1 : Nat) : Int) := by
  unfold lam
  let L0 := (Finset.univ : Finset (Fin n)).powersetCard 0
  let L1 := (Finset.univ : Finset (Fin n)).powersetCard 1
  let L2 := (Finset.univ : Finset (Fin n)).powersetCard 2
  have heq : (Finset.univ : Finset (Loc n)).filter (fun y => y.card ≤ 2) = L0 ∪ L1 ∪ L2 := by
    ext y
    simp only [L0, L1, L2, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_powersetCard, Finset.subset_univ]
    omega
  have hd01 : Disjoint L0 L1 := by
    rw [Finset.disjoint_left]; intro y h0 h1
    rw [Finset.mem_powersetCard] at h0 h1; omega
  have hd012 : Disjoint (L0 ∪ L1) L2 := by
    rw [Finset.disjoint_left]; intro y h01 h2
    rw [Finset.mem_powersetCard] at h2
    rcases Finset.mem_union.mp h01 with h0 | h1 <;> (rw [Finset.mem_powersetCard] at *; omega)
  rw [heq, Finset.sum_union hd012, Finset.sum_union hd01]
  have hS0 : ∑ y ∈ L0, chi1 u y = 1 := by
    have hL0 : L0 = {∅} := by
      ext y; simp [L0, Finset.mem_powersetCard]
    rw [hL0, Finset.sum_singleton]
    simp [chi1]
  have hchi_sing : ∀ i : Fin n, chi1 u {i} = if i ∈ u then -1 else 1 := by
    intro i
    by_cases hi : i ∈ u
    · have hinter : u ∩ {i} = {i} := by
        ext w; simp only [Finset.mem_inter, Finset.mem_singleton]
        exact ⟨fun h => h.2, fun h => ⟨h ▸ hi, h⟩⟩
      simp [chi1, hinter, hi]
    · have hinter : u ∩ {i} = ∅ := by
        ext w; simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
        rintro ⟨hw, rfl⟩; exact hi hw
      simp [chi1, hinter, hi]
  have hS1_fin : ∑ i : Fin n, chi1 u {i} = (n : Int) - 2 * (u.card : Int) := by
    have h1 : ∑ i : Fin n, chi1 u {i} = ∑ i : Fin n, (if i ∈ u then (-1 : Int) else 1) :=
      Finset.sum_congr rfl (fun i _ => hchi_sing i)
    rw [h1, Finset.sum_ite]
    have hf1 : ((Finset.univ : Finset (Fin n)).filter (fun i => i ∈ u)).card = u.card := by
      congr 1; ext i; simp
    have hf2 : ((Finset.univ : Finset (Fin n)).filter (fun i => i ∉ u)).card = n - u.card := by
      have hpart := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n))) (p := fun i => i ∈ u)
      rw [hf1] at hpart
      simp only [Finset.card_univ, Fintype.card_fin] at hpart
      omega
    simp only [Finset.sum_const, nsmul_eq_mul, mul_neg, mul_one, hf1, hf2]
    have hle : u.card ≤ n := by
      have := Finset.card_le_univ u
      simpa using this
    omega
  have hS1 : ∑ y ∈ L1, chi1 u y = (n : Int) - 2 * (u.card : Int) := by
    have hL1 : L1 = (Finset.univ : Finset (Fin n)).image (fun i => {i}) := by
      ext y
      simp only [L1, Finset.mem_powersetCard, Finset.subset_univ, true_and, Finset.mem_image,
        Finset.mem_univ, Finset.card_eq_one]
      exact ⟨fun ⟨a, ha⟩ => ⟨a, ha.symm⟩, fun ⟨a, ha⟩ => ⟨a, ha.symm⟩⟩
    rw [hL1, Finset.sum_image (fun _ _ _ _ h => Finset.singleton_injective h), hS1_fin]
  have hS2 : 2 * ∑ y ∈ L2, chi1 u y = ((n : Int) - 2 * (u.card : Int)) ^ 2 - (n : Int) := by
    let offDiag := (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 ≠ p.2)
    have h2 : ∑ p ∈ offDiag, chi1 u {p.1, p.2} = 2 * ∑ y ∈ L2, chi1 u y := by
      have hfib : ∑ p ∈ offDiag, chi1 u {p.1, p.2} =
          ∑ y ∈ L2, ∑ p ∈ offDiag.filter (fun p => ({p.1, p.2} : Loc n) = y), chi1 u {p.1, p.2} := by
        rw [Finset.sum_fiberwise_of_maps_to]
        intro p hp
        simp only [offDiag, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        rw [Finset.mem_powersetCard]
        exact ⟨Finset.subset_univ _, Finset.card_pair hp⟩
      rw [hfib, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun y hy => ?_)
      rw [Finset.mem_powersetCard] at hy
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hy.2
      have hset : offDiag.filter (fun p => ({p.1, p.2} : Loc n) = {a, b}) = {(a, b), (b, a)} := by
        ext ⟨p1, p2⟩
        simp only [offDiag, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, Prod.mk.injEq]
        constructor
        · rintro ⟨hne, heq⟩
          have h1 : p1 ∈ ({a, b} : Loc n) := by rw [← heq]; simp
          have h2 : p2 ∈ ({a, b} : Loc n) := by rw [← heq]; simp
          simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
          rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
          · exact (hne rfl).elim
          · exact Or.inl ⟨rfl, rfl⟩
          · exact Or.inr ⟨rfl, rfl⟩
          · exact (hne rfl).elim
        · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
          · exact ⟨hab, rfl⟩
          · exact ⟨hab.symm, Finset.pair_comm _ _⟩
      rw [hset, Finset.sum_pair (fun h => hab (Prod.mk.inj h).1)]
      have hcomm : ({b, a} : Loc n) = {a, b} := Finset.pair_comm b a
      rw [hcomm]
      ring
    have hoff : ∑ p ∈ offDiag, chi1 u {p.1, p.2} =
        (∑ i : Fin n, chi1 u {i}) ^ 2 - (n : Int) := by
      have hprod_eq : ∀ p ∈ offDiag, chi1 u {p.1, p.2} = chi1 u {p.1} * chi1 u {p.2} := by
        intro p hp
        simp only [offDiag, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        have hxor : ({p.1, p.2} : Loc n) = xorL {p.1} {p.2} := by
          ext w
          simp only [Finset.mem_insert, Finset.mem_singleton, mem_xorL]
          by_cases h1 : w = p.1 <;> by_cases h2 : w = p.2
          · subst h1; exact (hp h2).elim
          · simp [h1, h2, hp, hp.symm]
          · simp [h1, h2, hp, hp.symm]
          · simp [h1, h2]
        rw [hxor, chi1_xorL]
      rw [Finset.sum_congr rfl hprod_eq]
      have hdiag_sum :
          ∑ p ∈ offDiag, chi1 u {p.1} * chi1 u {p.2} +
          ∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 = p.2), chi1 u {p.1} * chi1 u {p.2} =
          ∑ p : Fin n × Fin n, chi1 u {p.1} * chi1 u {p.2} := by
        have h1 := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin n × Fin n))
          (fun p => p.1 ≠ p.2) (fun p => chi1 u {p.1} * chi1 u {p.2})
        simpa [offDiag] using h1
      have htot : ∑ p : Fin n × Fin n, chi1 u {p.1} * chi1 u {p.2} = (∑ i : Fin n, chi1 u {i}) ^ 2 := by
        rw [sq, Fintype.sum_prod_type, Finset.sum_mul_sum]
      have hdiag : ∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 = p.2),
          chi1 u {p.1} * chi1 u {p.2} = (n : Int) := by
        have heq_d : (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 = p.2) =
            (Finset.univ : Finset (Fin n)).image (fun i => (i, i)) := by
          ext ⟨a, b⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq]
          exact ⟨fun h => ⟨a, rfl, h⟩, fun ⟨i, h1, h2⟩ => h1.symm.trans h2⟩
        rw [heq_d, Finset.sum_image (fun _ _ _ _ h => (Prod.mk.inj h).1)]
        have hsq : ∀ i : Fin n, chi1 u {i} * chi1 u {i} = 1 := by
          intro i; rw [hchi_sing i]; split_ifs <;> norm_num
        simp [Finset.sum_congr rfl (fun i _ => hsq i)]
      omega
    rw [← h2, hoff, hS1_fin]
  have hn1 : ((n - 1 : Nat) : Int) = (n : Int) - 1 := by omega
  rw [hS0, hS1]
  linarith

private lemma lam_ne_zero {n : Nat} (hn : 3 ≤ n) (hnsq : ¬ ∃ m : Nat, m * m = n - 1)
    (u : Loc n) : lam u ≠ 0 := by
  intro h0
  have h := two_mul_lam hn u
  rw [h0, mul_zero] at h
  have hsq : ((n : Int) - 2 * (u.card : Int) + 1) ^ 2 = ((n - 1 : Nat) : Int) := by linarith
  let m : Nat := ((n : Int) - 2 * (u.card : Int) + 1).natAbs
  have hm_int : ((m * m : Nat) : Int) = ((n - 1 : Nat) : Int) := by
    push_cast [m]
    rw [← sq, sq_abs]
    exact hsq
  exact hnsq ⟨m, Int.ofNat.inj hm_int⟩

private lemma radial_implies_dvd {n r N : Nat} (hn : 3 ≤ n)
    (hnsq : ¬ ∃ m : Nat, m * m = n - 1)
    (c : Fin N → Wrd n r)
    (hunif : ∀ x : Wrd n r,
      2 ^ (n * r) * ((Finset.univ : Finset (Fin N)).filter (fun i =>
        (List.finRange r).all (fun j => decide ((xorL (x j) (c i j)).card ≤ 2)) = true)).card =
      (1 + n + Nat.choose n 2) ^ r * N) :
    2 ^ (n * r) ∣ N := by
  let mult : Wrd n r → Int := fun z =>
    (((Finset.univ : Finset (Fin N)).filter (fun i => c i = z)).card : Int)
  have hsum_mult : ∑ z : Wrd n r, mult z = (N : Int) := by
    have hnat : ∑ z : Wrd n r, ((Finset.univ : Finset (Fin N)).filter (fun i => c i = z)).card = N := by
      have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin N)))
        (t := (Finset.univ : Finset (Wrd n r))) (f := c) (fun _ _ => Finset.mem_univ _)
      simpa using h.symm
    dsimp only [mult]
    exact_mod_cast hnat
  let K : Int := (((Finset.univ : Finset (Fin N)).filter (fun i =>
    (List.finRange r).all (fun j => decide ((xorL (∅ : Loc n) (c i j)).card ≤ 2)) = true)).card : Int)
  have hconv : ∀ x : Wrd n r,
      ∑ z : Wrd n r, mult z * (if ∀ j : Fin r, (xorL (x j) (z j)).card ≤ 2 then (1 : Int) else 0) = K := by
    intro x
    have hdeg_eq :
        ((Finset.univ : Finset (Fin N)).filter (fun i =>
          (List.finRange r).all (fun j => decide ((xorL (x j) (c i j)).card ≤ 2)) = true)).card =
        ((Finset.univ : Finset (Fin N)).filter (fun i =>
          (List.finRange r).all (fun j => decide ((xorL (∅ : Loc n) (c i j)).card ≤ 2)) = true)).card := by
      have hx := hunif x
      have h0 := hunif (fun _ => ∅)
      have hpos : 0 < 2 ^ (n * r) := by positivity
      exact Nat.eq_of_mul_eq_mul_left hpos (hx.trans h0.symm)
    have hfib :
        ((Finset.univ : Finset (Fin N)).filter (fun i =>
          (List.finRange r).all (fun j => decide ((xorL (x j) (c i j)).card ≤ 2)) = true)).card =
        ∑ z : Wrd n r, ((Finset.univ : Finset (Fin N)).filter (fun i => c i = z)).card *
          (if ∀ j : Fin r, (xorL (x j) (z j)).card ≤ 2 then 1 else 0) := by
      rw [Finset.card_eq_sum_card_fiberwise (f := c) (t := (Finset.univ : Finset (Wrd n r)))
        (fun _ _ => Finset.mem_univ _)]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      have hall_iff : ((List.finRange r).all (fun j => decide ((xorL (x j) (z j)).card ≤ 2)) = true) ↔
          ∀ j : Fin r, (xorL (x j) (z j)).card ≤ 2 := by
        simp [List.all_eq_true, List.mem_finRange]
      by_cases hz : ∀ j : Fin r, (xorL (x j) (z j)).card ≤ 2
      · rw [if_pos hz, mul_one]
        congr 1; ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun ⟨_, h2⟩ => h2, fun h => ⟨by rw [h]; exact hall_iff.mpr hz, h⟩⟩
      · rw [if_neg hz, mul_zero, Finset.card_eq_zero]
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        rintro ⟨h1, h2⟩
        rw [h2] at h1
        exact hz (hall_iff.mp h1)
    have hnat : ∑ z : Wrd n r, ((Finset.univ : Finset (Fin N)).filter (fun i => c i = z)).card *
        (if ∀ j : Fin r, (xorL (x j) (z j)).card ≤ 2 then 1 else 0) =
        ((Finset.univ : Finset (Fin N)).filter (fun i =>
          (List.finRange r).all (fun j => decide ((xorL (∅ : Loc n) (c i j)).card ≤ 2)) = true)).card :=
      hfib.symm.trans hdeg_eq
    have hint : ((∑ z : Wrd n r, ((Finset.univ : Finset (Fin N)).filter (fun i => c i = z)).card *
        (if ∀ j : Fin r, (xorL (x j) (z j)).card ≤ 2 then 1 else 0) : Nat) : Int) = K := by
      dsimp only [K]
      exact_mod_cast hnat
    simpa [mult] using hint
  have hfourier0 : ∀ a : Wrd n r, a ≠ (fun _ => ∅) → ∑ z : Wrd n r, mult z * chi a z = 0 := by
    intro a ha
    have hlhs : ∑ x : Wrd n r, K * chi a x = 0 := by
      rw [← Finset.mul_sum, sum_chi]
      simp [ha]
    have hball_sum : ∑ y : Wrd n r, (if ∀ j : Fin r, (y j).card ≤ 2 then (1 : Int) else 0) * chi a y =
        ∏ j : Fin r, lam (a j) := by
      have heq : ∑ y : Wrd n r, (if ∀ j : Fin r, (y j).card ≤ 2 then (1 : Int) else 0) * chi a y =
          ∑ y : Wrd n r, ∏ j : Fin r, (if (y j).card ≤ 2 then chi1 (a j) (y j) else 0) := by
        refine Finset.sum_congr rfl (fun y _ => ?_)
        by_cases hy : ∀ j : Fin r, (y j).card ≤ 2
        · rw [if_pos hy, one_mul]
          unfold chi
          exact Finset.prod_congr rfl (fun j _ => by rw [if_pos (hy j)])
        · rw [if_neg hy, zero_mul]
          push Not at hy
          rcases hy with ⟨j0, hj0⟩
          symm
          exact Finset.prod_eq_zero (Finset.mem_univ j0) (by simp [hj0])
      rw [heq, ← Fintype.prod_sum (fun j y => if y.card ≤ 2 then chi1 (a j) y else 0)]
      refine Finset.prod_congr rfl (fun j _ => ?_)
      unfold lam
      rw [Finset.sum_filter]
    have hrhs : ∑ x : Wrd n r, K * chi a x =
        (∑ z : Wrd n r, mult z * chi a z) * (∏ j : Fin r, lam (a j)) := by
      calc
        ∑ x : Wrd n r, K * chi a x
          = ∑ x : Wrd n r, (∑ z : Wrd n r, mult z * (if ∀ j : Fin r, (xorL (x j) (z j)).card ≤ 2 then (1 : Int) else 0)) * chi a x := by
            refine Finset.sum_congr rfl (fun x _ => by rw [hconv x])
        _ = ∑ x : Wrd n r, ∑ z : Wrd n r, mult z * (if ∀ j : Fin r, (xorL (x j) (z j)).card ≤ 2 then (1 : Int) else 0) * chi a x := by
            refine Finset.sum_congr rfl (fun x _ => Finset.sum_mul _ _ _)
        _ = ∑ z : Wrd n r, ∑ x : Wrd n r, mult z * (if ∀ j : Fin r, (xorL (x j) (z j)).card ≤ 2 then (1 : Int) else 0) * chi a x :=
            Finset.sum_comm
        _ = ∑ z : Wrd n r, mult z * (chi a z * (∏ j : Fin r, lam (a j))) := by
            refine Finset.sum_congr rfl (fun z _ => ?_)
            have hshift :
                ∑ x : Wrd n r, mult z * (if ∀ j : Fin r, (xorL (x j) (z j)).card ≤ 2 then (1 : Int) else 0) * chi a x =
                mult z * ∑ y : Wrd n r, (if ∀ j : Fin r, (y j).card ≤ 2 then (1 : Int) else 0) * (chi a z * chi a y) := by
              rw [Finset.mul_sum]
              let eZ : Wrd n r ≃ Wrd n r :=
                { toFun := fun x j => xorL (x j) (z j)
                  invFun := fun y j => xorL (y j) (z j)
                  left_inv := fun x => funext (fun j => xorL_invol (x j) (z j))
                  right_inv := fun y => funext (fun j => xorL_invol (y j) (z j)) }
              refine Fintype.sum_equiv eZ _ _ (fun x => ?_)
              have hx_eq : x = fun j => xorL (z j) (eZ x j) := by
                funext j
                dsimp only [eZ, Equiv.coe_fn_mk]
                rw [xorL_comm (z j), xorL_invol]
              have hch : chi a x = chi a z * chi a (eZ x) := by
                conv_lhs => rw [hx_eq]
                exact chi_xorW a z (eZ x)
              rw [hch]
              dsimp only [eZ, Equiv.coe_fn_mk]
              ring
            rw [hshift, ← hball_sum]
            congr 1
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun y _ => by ring)
        _ = (∑ z : Wrd n r, mult z * chi a z) * (∏ j : Fin r, lam (a j)) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl (fun z _ => by ring)
    have hprod0 : (∑ z : Wrd n r, mult z * chi a z) * (∏ j : Fin r, lam (a j)) = 0 :=
      hrhs.symm.trans hlhs
    have hlam_ne : (∏ j : Fin r, lam (a j)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun j _ => lam_ne_zero hn hnsq (a j))
    exact (mul_eq_zero.mp hprod0).resolve_right hlam_ne
  have hinv : ∑ a : Wrd n r, ∑ z : Wrd n r, mult z * chi a z = (N : Int) := by
    rw [Finset.sum_eq_single (fun _ => ∅)]
    · simpa [chi_zero_left] using hsum_mult
    · intro a _ ha
      exact hfourier0 a ha
    · intro h; exact (h (Finset.mem_univ _)).elim
  have hswap : ∑ a : Wrd n r, ∑ z : Wrd n r, mult z * chi a z = mult (fun _ => ∅) * (2 ^ (n * r) : Int) := by
    rw [Finset.sum_comm]
    calc
      ∑ z : Wrd n r, ∑ a : Wrd n r, mult z * chi a z
        = ∑ z : Wrd n r, mult z * ∑ a : Wrd n r, chi z a := by
          refine Finset.sum_congr rfl (fun z _ => ?_)
          rw [← Finset.mul_sum]
          congr 1
          exact Finset.sum_congr rfl (fun a _ => chi_comm a z)
      _ = ∑ z : Wrd n r, mult z * (if z = (fun _ => ∅) then (2 ^ (n * r) : Int) else 0) := by
          refine Finset.sum_congr rfl (fun z _ => by rw [sum_chi])
      _ = mult (fun _ => ∅) * (2 ^ (n * r) : Int) := by
          rw [Finset.sum_eq_single (fun _ => ∅)]
          · simp
          · intro z _ hz; simp [hz]
          · intro h; exact (h (Finset.mem_univ _)).elim
  have hmul_int : (((Finset.univ : Finset (Fin N)).filter (fun i => c i = (fun _ => ∅))).card * 2 ^ (n * r) : Nat) =
      (N : Int) := by
    have h := hswap.symm.trans hinv
    simpa [mult] using h
  refine ⟨((Finset.univ : Finset (Fin N)).filter (fun i => c i = (fun _ => ∅))).card, ?_⟩
  have hnat : ((Finset.univ : Finset (Fin N)).filter (fun i => c i = (fun _ => ∅))).card * 2 ^ (n * r) = N :=
    Int.ofNat.inj hmul_int
  linarith

private lemma main_aux :
∀ (n r N : Nat), 3 ≤ n → 0 < N →
  let V := 1 + n + Nat.choose n 2
  let P := 2 ^ (n * r)
  let Site := Fin n
  let Local := Finset Site
  let Word := Fin r → Local
  let triples := (Finset.univ : Finset Site).powersetCard 3
  let physical := fun (s : Fin r → Local → Local) (x : Word) =>
    (List.finRange r).all (fun j => triples.toList.all (fun E => x j ∩ E != s j E ∩ E))
  let radial := fun (c x : Word) => (List.finRange r).all (fun j =>
    decide (((x j \ c j) ∪ (c j \ x j)).card ≤ 2))
  let good := fun (tests : Fin N → Word → Bool) => ∃ answer : Fin N → Bool → Bool,
    (∀ i, answer i false = false) ∧ ∀ A : Finset Word, A.Nonempty →
      V ^ r * N ≤ P * ((Finset.univ : Finset (Fin N)).filter (fun i =>
        answer i (A.toList.any (tests i)))).card
  V % 4 = 2 → (¬ ∃ m : Nat, m * m = n - 1) →
    (((∃ s : Fin N → Fin r → Local → Local, good (fun i => physical (s i))) ↔
      2 ^ ((n - 1) * r) ∣ N) ∧
     ((∃ c : Fin N → Word, good (fun i => radial (c i))) ↔ P ∣ N)) := by
  intro n r N hn hN V P Site Local Word triples physical radial good hV4 hnsq
  have hphys_iff : ∀ (s : Fin r → Local → Local) (x : Word),
      (physical s x = true) ↔ ∀ j : Fin r, ∀ E ∈ triples, x j ∩ E ≠ s j E ∩ E := by
    intro s x
    simp [physical, List.all_eq_true, List.mem_finRange, Finset.mem_toList, bne_iff_ne]
  have hrad_iff : ∀ (c x : Word),
      (radial c x = true) ↔ ∀ j : Fin r, (xorL (x j) (c j)).card ≤ 2 := by
    intro c x
    simp [radial, List.all_eq_true, List.mem_finRange, xorL]
  have hphys_sz : ∀ (s : Fin r → Local → Local),
      ((Finset.univ : Finset Word).filter (fun x => physical s x = true)).card ≤ V ^ r := by
    intro s
    have heq : (Finset.univ : Finset Word).filter (fun x => physical s x = true) =
        (Finset.univ : Finset Word).filter (fun x => ∀ j : Fin r, ∀ E ∈ triples, x j ∩ E ≠ s j E ∩ E) := by
      ext x; simp [hphys_iff]
    rw [heq]
    dsimp only [Word, Local, Site]
    rw [card_filter_pi (P := fun j y => ∀ E ∈ triples, y ∩ E ≠ s j E ∩ E)]
    calc
      ∏ j : Fin r, ((Finset.univ : Finset Local).filter (fun y => ∀ E ∈ triples, y ∩ E ≠ s j E ∩ E)).card
        ≤ ∏ _j : Fin r, V := Finset.prod_le_prod' (fun j _ => card_physical_coord_le n (s j))
      _ = V ^ r := by simp
  have hrad_sz : ∀ (c : Word),
      ((Finset.univ : Finset Word).filter (fun x => radial c x = true)).card = V ^ r := by
    intro c
    have heq : (Finset.univ : Finset Word).filter (fun x => radial c x = true) =
        (Finset.univ : Finset Word).filter (fun x => ∀ j : Fin r, (xorL (x j) (c j)).card ≤ 2) := by
      ext x; simp [hrad_iff]
    rw [heq]
    dsimp only [Word, Local, Site]
    rw [card_filter_pi (P := fun j y => (xorL y (c j)).card ≤ 2)]
    calc
      ∏ j : Fin r, ((Finset.univ : Finset Local).filter (fun y => (xorL y (c j)).card ≤ 2)).card
        = ∏ _j : Fin r, V := Finset.prod_congr rfl (fun j _ => card_radial_coord n (c j))
      _ = V ^ r := by simp
  constructor
  · constructor
    · rintro ⟨s, hgood⟩
      have hunif := good_implies_uniform (fun i => physical (s i)) (fun i => hphys_sz (s i)) hgood
      have h0 := hunif (fun _ => ∅)
      have hdvd : 2 ^ (n * r) ∣ V ^ r * N := ⟨_, h0.symm⟩
      have hV2 : V = 2 * (V / 2) := by omega
      have hVodd : (V / 2) % 2 = 1 := by omega
      have hnr : n * r = r + (n - 1) * r := by
        have : n = 1 + (n - 1) := by omega
        conv_lhs => rw [this, Nat.add_mul, one_mul]
      rw [hnr, pow_add, hV2, mul_pow, mul_assoc] at hdvd
      have h2r : 0 < 2 ^ r := by positivity
      have hdvd2 : 2 ^ ((n - 1) * r) ∣ (V / 2) ^ r * N :=
        (Nat.mul_dvd_mul_iff_left h2r).mp hdvd
      have hcop1 : Nat.Coprime 2 (V / 2) := by
        rw [Nat.coprime_two_left]
        exact Nat.odd_iff.mpr hVodd
      have hcop : Nat.Coprime (2 ^ ((n - 1) * r)) ((V / 2) ^ r) :=
        (hcop1.pow_left _).pow_right _
      exact hcop.dvd_of_dvd_mul_left hdvd2
    · rintro ⟨q, hNq⟩
      obtain ⟨sFam, hsFam⟩ := exists_balanced_physical_single n hn hV4
      let T := Fin r → Finset (Fin (n - 1))
      have hTcard : Fintype.card T = 2 ^ ((n - 1) * r) := by
        simp only [T, Fintype.card_fun, Fintype.card_finset, Fintype.card_fin]
        rw [← pow_mul]
      have hcardN : Fintype.card (T × Fin q) = N := by
        rw [Fintype.card_prod, hTcard, Fintype.card_fin, hNq]
      let eN : Fin N ≃ T × Fin q := (Fintype.equivFinOfCardEq hcardN).symm
      let s : Fin N → Fin r → Local → Local := fun i j => sFam ((eN i).1 j)
      refine ⟨s, uniform_implies_good (fun i => physical (s i)) ?_⟩
      intro x
      have hdeg : ((Finset.univ : Finset (Fin N)).filter (fun i => physical (s i) x = true)).card =
          (V / 2) ^ r * q := by
        have hbij :
            ((Finset.univ : Finset (Fin N)).filter (fun i => physical (s i) x = true)).card =
            ((Finset.univ : Finset (T × Fin q)).filter (fun p =>
              ∀ j : Fin r, ∀ E ∈ triples, x j ∩ E ≠ sFam (p.1 j) E ∩ E)).card := by
          refine Finset.card_nbij eN ?_ ?_ ?_
          · intro i hi
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
            exact (hphys_iff (s i) x).mp hi
          · intro i1 _ i2 _ h; exact eN.injective h
          · intro p hp
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp
            refine ⟨eN.symm p, ?_, eN.apply_symm_apply p⟩
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
            rw [hphys_iff]
            simpa [s] using hp
        rw [hbij]
        have hprod :
            (Finset.univ : Finset (T × Fin q)).filter (fun p =>
              ∀ j : Fin r, ∀ E ∈ triples, x j ∩ E ≠ sFam (p.1 j) E ∩ E) =
            ((Finset.univ : Finset T).filter (fun t =>
              ∀ j : Fin r, ∀ E ∈ triples, x j ∩ E ≠ sFam (t j) E ∩ E)) ×ˢ (Finset.univ : Finset (Fin q)) := by
          ext ⟨t, k⟩; simp
        rw [hprod, Finset.card_product, Finset.card_univ, Fintype.card_fin]
        have hpi :
            ((Finset.univ : Finset T).filter (fun t =>
              ∀ j : Fin r, ∀ E ∈ triples, x j ∩ E ≠ sFam (t j) E ∩ E)).card =
            ∏ j : Fin r, ((Finset.univ : Finset (Finset (Fin (n - 1)))).filter (fun t =>
              ∀ E ∈ triples, x j ∩ E ≠ sFam t E ∩ E)).card := by
          have heq : (Finset.univ : Finset T).filter (fun t =>
                ∀ j : Fin r, ∀ E ∈ triples, x j ∩ E ≠ sFam (t j) E ∩ E) =
              Fintype.piFinset (fun j => (Finset.univ : Finset (Finset (Fin (n - 1)))).filter (fun t =>
                ∀ E ∈ triples, x j ∩ E ≠ sFam t E ∩ E)) := by
            ext t
            dsimp only [T]
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
          rw [heq, Fintype.card_piFinset]
        rw [hpi]
        have hprodV : ∏ j : Fin r, ((Finset.univ : Finset (Finset (Fin (n - 1)))).filter (fun t =>
            ∀ E ∈ triples, x j ∩ E ≠ sFam t E ∩ E)).card = (V / 2) ^ r := by
          calc
            _ = ∏ _j : Fin r, (V / 2) := Finset.prod_congr rfl (fun j _ => hsFam (x j))
            _ = (V / 2) ^ r := by simp
        rw [hprodV]
      rw [hdeg]
      have hV2 : 2 * (V / 2) = V := by omega
      have hnr : n * r = r + (n - 1) * r := by
        have : n = 1 + (n - 1) := by omega
        conv_lhs => rw [this, Nat.add_mul, one_mul]
      have heq_all : P * ((V / 2) ^ r * q) = V ^ r * N := by
        dsimp only [P]
        rw [hNq, hnr, pow_add]
        calc
          2 ^ r * 2 ^ ((n - 1) * r) * ((V / 2) ^ r * q)
            = (2 * (V / 2)) ^ r * (2 ^ ((n - 1) * r) * q) := by rw [mul_pow]; ring
          _ = V ^ r * (2 ^ ((n - 1) * r) * q) := by rw [hV2]
      exact le_of_eq heq_all.symm
  · constructor
    · rintro ⟨c, hgood⟩
      have hunif := good_implies_uniform (fun i => radial (c i)) (fun i => le_of_eq (hrad_sz (c i))) hgood
      exact radial_implies_dvd hn hnsq c hunif
    · rintro ⟨q, hNq⟩
      have hcardN : Fintype.card (Word × Fin q) = N := by
        rw [Fintype.card_prod, ← Finset.card_univ, card_word, Fintype.card_fin, hNq]
      let eN : Fin N ≃ Word × Fin q := (Fintype.equivFinOfCardEq hcardN).symm
      let c : Fin N → Word := fun i => (eN i).1
      refine ⟨c, uniform_implies_good (fun i => radial (c i)) ?_⟩
      intro x
      have hdeg : ((Finset.univ : Finset (Fin N)).filter (fun i => radial (c i) x = true)).card =
          V ^ r * q := by
        have hbij :
            ((Finset.univ : Finset (Fin N)).filter (fun i => radial (c i) x = true)).card =
            ((Finset.univ : Finset (Word × Fin q)).filter (fun p => radial p.1 x = true)).card := by
          refine Finset.card_nbij eN ?_ ?_ ?_
          · intro i hi
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
            exact hi
          · intro i1 _ i2 _ h; exact eN.injective h
          · intro p hp
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp
            refine ⟨eN.symm p, ?_, eN.apply_symm_apply p⟩
            simp [c, hp]
        rw [hbij]
        have hprod :
            (Finset.univ : Finset (Word × Fin q)).filter (fun p => radial p.1 x = true) =
            ((Finset.univ : Finset Word).filter (fun z => radial z x = true)) ×ˢ (Finset.univ : Finset (Fin q)) := by
          ext ⟨z, k⟩; simp
        rw [hprod, Finset.card_product, Finset.card_univ, Fintype.card_fin]
        have hsym : ((Finset.univ : Finset Word).filter (fun z => radial z x = true)).card =
            ((Finset.univ : Finset Word).filter (fun z => radial x z = true)).card := by
          congr 1; ext z
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hrad_iff]
          exact forall_congr' (fun j => by rw [xorL_comm])
        rw [hsym, hrad_sz x]
      rw [hdeg, hNq]
      have heq_all : V ^ r * (P * q) = P * (V ^ r * q) := by ring
      exact le_of_eq heq_all

end PEqualNP.Outside.L_lib_1184_aux

theorem PEqualNP.Outside.L_lib_1184 :
∀ (n r N : Nat), 3 ≤ n → 0 < N →
  let V := 1 + n + Nat.choose n 2
  let P := 2 ^ (n * r)
  let Site := Fin n
  let Local := Finset Site
  let Word := Fin r → Local
  let triples := (Finset.univ : Finset Site).powersetCard 3
  let physical := fun (s : Fin r → Local → Local) (x : Word) =>
    (List.finRange r).all (fun j => triples.toList.all (fun E => x j ∩ E != s j E ∩ E))
  let radial := fun (c x : Word) => (List.finRange r).all (fun j =>
    decide (((x j \ c j) ∪ (c j \ x j)).card ≤ 2))
  let good := fun (tests : Fin N → Word → Bool) => ∃ answer : Fin N → Bool → Bool,
    (∀ i, answer i false = false) ∧ ∀ A : Finset Word, A.Nonempty →
      V ^ r * N ≤ P * ((Finset.univ : Finset (Fin N)).filter (fun i =>
        answer i (A.toList.any (tests i)))).card
  V % 4 = 2 → (¬ ∃ m : Nat, m * m = n - 1) →
    (((∃ s : Fin N → Fin r → Local → Local, good (fun i => physical (s i))) ↔
      2 ^ ((n - 1) * r) ∣ N) ∧
     ((∃ c : Fin N → Word, good (fun i => radial (c i))) ↔ P ∣ N)) :=
  PEqualNP.Outside.L_lib_1184_aux.main_aux
