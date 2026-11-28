import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1182_aux

private abbrev Site (m : Nat) := Option (Fin m)
private abbrev Word (m : Nat) := Finset (Fin m)
private abbrev Scope (m : Nat) := Finset (Site m)

private def enc {m : Nat} (x : Word m) (b : Bool) : Scope m :=
  let old := x.image (fun i => (some i : Site m))
  if b then insert none old else old

private def dec {m : Nat} (A : Scope m) : Word m × Bool :=
  ((Finset.univ : Finset (Fin m)).filter (fun i => (some i : Site m) ∈ A),
   decide ((none : Site m) ∈ A))

private lemma mem_enc_none {m : Nat} (x : Word m) (b : Bool) :
    (none : Site m) ∈ enc x b ↔ b = true := by
  cases b <;> simp [enc]

private lemma mem_enc_some {m : Nat} (x : Word m) (b : Bool) (i : Fin m) :
    (some i : Site m) ∈ enc x b ↔ i ∈ x := by
  cases b <;> simp [enc]

private lemma enc_dec {m : Nat} (A : Scope m) : enc (dec A).1 (dec A).2 = A := by
  ext s
  cases s with
  | none =>
    simp [dec, mem_enc_none]
  | some i =>
    simp [dec, mem_enc_some]

private lemma dec_enc {m : Nat} (p : Word m × Bool) : dec (enc p.1 p.2) = p := by
  rcases p with ⟨x, b⟩
  apply Prod.ext
  · ext i
    simp [dec, mem_enc_some]
  · simp [dec, mem_enc_none]

private lemma enc_injective {m : Nat} :
    Function.Injective (fun p : Word m × Bool => enc p.1 p.2) := by
  intro p1 p2 h
  have h1 := congrArg dec h
  simpa [dec_enc] using h1

private lemma card_enc {m : Nat} (x : Word m) (b : Bool) :
    (enc x b).card = x.card + if b then 1 else 0 := by
  have himg : (x.image (fun i => (some i : Site m))).card = x.card :=
    Finset.card_image_of_injective x (Option.some_injective (Fin m))
  have hnot : (none : Site m) ∉ x.image (fun i => (some i : Site m)) := by
    simp
  cases b
  · simp [enc, himg]
  · simp only [enc, ite_true]
    rw [Finset.card_insert_eq_ite]
    simp [hnot, himg]

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
        have hvT : v ∉ T := hnot0 T hT0
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

private lemma card_lift {m h : Nat} (F : Finset (Word m)) :
    let words := (Finset.univ : Finset (Word m))
    let small := words.filter (fun x => x.card < h)
    let shell := words.filter (fun x => x.card = h)
    let domain := (Finset.univ : Finset (Word m × Bool))
    let lift := fun (G : Finset (Word m)) => domain.filter (fun xb =>
      xb.1 ∈ small ∨ (xb.1 ∈ shell ∧ xb.2 = decide (xb.1 ∈ G)))
    (lift F).card = 2 * small.card + shell.card := by
  intro words small shell domain lift
  let P1 : Finset (Word m × Bool) := small ×ˢ (Finset.univ : Finset Bool)
  let P2 : Finset (Word m × Bool) := shell.image (fun x => (x, decide (x ∈ F)))
  have hdisj : Disjoint P1 P2 := by
    rw [Finset.disjoint_left]
    intro xb h1 h2
    simp only [P1, Finset.mem_product, Finset.mem_univ, and_true, small, words,
      Finset.mem_filter, true_and] at h1
    rcases Finset.mem_image.mp h2 with ⟨x, hx, rfl⟩
    dsimp only at h1
    simp only [shell, words, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    omega
  have heq : lift F = P1 ∪ P2 := by
    ext xb
    rcases xb with ⟨x, b⟩
    simp only [lift, domain, P1, P2, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_product, and_true, Finset.mem_image]
    constructor
    · rintro (hsm | ⟨hsh, hb⟩)
      · exact Or.inl hsm
      · exact Or.inr ⟨x, hsh, by simp [hb]⟩
    · rintro (hsm | ⟨y, hy, hxy⟩)
      · exact Or.inl hsm
      · rcases Prod.mk.inj hxy with ⟨rfl, rfl⟩
        exact Or.inr ⟨hy, rfl⟩
  have hP1 : P1.card = 2 * small.card := by
    rw [Finset.card_product]
    simp only [Finset.card_univ, Fintype.card_bool]
    ring
  have hP2 : P2.card = shell.card := by
    refine Finset.card_image_of_injective shell ?_
    intro x1 x2 h12
    exact (Prod.mk.inj h12).1
  rw [heq, Finset.card_union_of_disjoint hdisj, hP1, hP2]

private lemma card_scopes_le {m h : Nat} :
    let words := (Finset.univ : Finset (Word m))
    let small := words.filter (fun x => x.card < h)
    let shell := words.filter (fun x => x.card = h)
    ((Finset.univ : Finset (Scope m)).filter (fun A => A.card ≤ h)).card =
      2 * small.card + shell.card := by
  intro words small shell
  let domain := (Finset.univ : Finset (Word m × Bool))
  let L0 := domain.filter (fun xb => xb.1 ∈ small ∨ (xb.1 ∈ shell ∧ xb.2 = decide (xb.1 ∈ (∅ : Finset (Word m)))))
  have hbij :
      ((Finset.univ : Finset (Scope m)).filter (fun A => A.card ≤ h)).card = L0.card := by
    symm
    refine Finset.card_nbij (fun xb : Word m × Bool => enc xb.1 xb.2) ?_ ?_ ?_
    · intro xb hxb
      simp only [Finset.mem_coe, L0, domain, small, shell, words, Finset.mem_filter,
        Finset.mem_univ, true_and, Finset.notMem_empty, decide_false] at hxb ⊢
      rw [card_enc]
      rcases xb with ⟨x, b⟩
      cases b <;> simp at hxb ⊢ <;> omega
    · intro p1 _ p2 _ heq
      exact enc_injective heq
    · intro A hA
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hA
      refine ⟨dec A, ?_, enc_dec A⟩
      simp only [Finset.mem_coe, L0, domain, small, shell, words, Finset.mem_filter,
        Finset.mem_univ, true_and, Finset.notMem_empty, decide_false]
      have hc : (enc (dec A).1 (dec A).2).card ≤ h := by
        rw [enc_dec]
        exact hA
      rw [card_enc] at hc
      cases hb : (dec A).2 <;> simp [hb] at hc ⊢ <;> omega
  rw [hbij]
  exact card_lift (∅ : Finset (Word m))

private lemma main_aux :
∀ (m h : Nat),
  let Site := Option (Fin m)
  let Word := Finset (Fin m)
  let Scope := Finset Site
  let scopes := (Finset.univ : Finset Site).powersetCard (h + 1)
  let words := (Finset.univ : Finset Word)
  let small := words.filter (fun x => x.card < h)
  let shell := words.filter (fun x => x.card = h)
  let encode := fun (x : Word) (b : Bool) =>
    let old := x.image (fun i => (some i : Site))
    if b then insert none old else old
  let domain := (Finset.univ : Finset (Word × Bool))
  let region := fun (s : Scope → Scope) => domain.filter (fun xb =>
    ∀ E ∈ scopes, encode xb.1 xb.2 ∩ E ≠ s E ∩ E)
  let allRegions := (Finset.univ : Finset (Scope → Scope)).image region
  let family := allRegions.filter (fun R =>
    R.image Prod.fst = small ∪ shell ∧ ∀ x ∈ small, (x, false) ∈ R ∧ (x, true) ∈ R)
  let lift := fun (F : Finset Word) => domain.filter (fun xb =>
    xb.1 ∈ small ∨ (xb.1 ∈ shell ∧ xb.2 = decide (xb.1 ∈ F)))
  (∀ R ∈ allRegions, R.card ≤ 2 * small.card + shell.card) ∧
  family = shell.powerset.image lift ∧
  (∀ R ∈ family, R.card = 2 * small.card + shell.card) ∧
  (∀ j : Nat, (family.filter (fun R =>
    (R.filter (fun xb => xb.2 = true)).card = small.card + j)).card = Nat.choose shell.card j) := by
  intro m h Site Word Scope scopes words small shell encode domain region allRegions family lift
  have henc_eq : ∀ x b, encode x b = enc x b := fun _ _ => rfl
  have hpart1 : ∀ R ∈ allRegions, R.card ≤ 2 * small.card + shell.card := by
    intro R hR
    rcases Finset.mem_image.mp hR with ⟨s, _, rfl⟩
    let F : Finset (Scope) := (region s).image (fun xb => encode xb.1 xb.2)
    have hFcard : F.card = (region s).card :=
      Finset.card_image_of_injective (region s) enc_injective
    have hpaj : F.card ≤ (shat F).card := pajor_aux F.card F rfl
    have hshat_sub : shat F ⊆ (Finset.univ : Finset Scope).filter (fun A => A.card ≤ h) := by
      intro T hT
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_contra hgt
      have hge : h + 1 ≤ T.card := by omega
      obtain ⟨E, hET, hEcard⟩ := Finset.exists_subset_card_eq hge
      have hEsc : E ∈ scopes := by
        simp only [scopes, Finset.mem_powersetCard, Finset.subset_univ, true_and]
        exact hEcard
      rw [mem_shat] at hT
      have hUsub : s E ∩ E ⊆ T := (Finset.inter_subset_right).trans hET
      rcases hT (s E ∩ E) hUsub with ⟨A, hAF, hAT⟩
      rcases Finset.mem_image.mp hAF with ⟨xb, hxb, rfl⟩
      simp only [region, domain, Finset.mem_filter, Finset.mem_univ, true_and] at hxb
      apply hxb E hEsc
      have hinter : encode xb.1 xb.2 ∩ E = (encode xb.1 xb.2 ∩ T) ∩ E := by
        ext u
        simp only [Finset.mem_inter]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨⟨h1, hET h2⟩, h2⟩
        · rintro ⟨⟨h1, _⟩, h2⟩
          exact ⟨h1, h2⟩
      rw [hinter, hAT, Finset.inter_assoc, Finset.inter_self]
    have hshat_le : (shat F).card ≤ 2 * small.card + shell.card := by
      have h1 := Finset.card_le_card hshat_sub
      exact h1.trans (le_of_eq card_scopes_le)
    omega
  have hpart2 : family = shell.powerset.image lift := by
    ext R
    constructor
    · intro hR
      simp only [family, Finset.mem_filter] at hR
      rcases hR with ⟨hRall, hRimg, hRsmall⟩
      rcases Finset.mem_image.mp hRall with ⟨s, _, rfl⟩
      have hshell_not_both : ∀ x ∈ shell, ¬ ((x, false) ∈ region s ∧ (x, true) ∈ region s) := by
        intro x hx hboth
        let E : Scope := insert none (x.image (fun i => (some i : Site)))
        have hEsc : E ∈ scopes := by
          dsimp only [scopes]
          rw [Finset.mem_powersetCard]
          refine ⟨Finset.subset_univ E, ?_⟩
          have h1 : E = enc x true := rfl
          rw [h1, card_enc]
          simp only [shell, words, Finset.mem_filter, Finset.mem_univ, true_and] at hx
          simp [hx]
        let T : Scope := s E ∩ E
        let p := dec T
        have hTenc : encode p.1 p.2 = T := enc_dec T
        have hTsub : T ⊆ E := Finset.inter_subset_right
        have hp1sub : p.1 ⊆ x := by
          intro i hi
          have hmem : (some i : Site) ∈ T := by
            rw [← hTenc]
            exact (mem_enc_some p.1 p.2 i).mpr hi
          have hmemE := hTsub hmem
          exact (mem_enc_some x true i).mp hmemE
        have hpR : p ∈ region s := by
          by_cases hpeq : p.1 = x
          · cases hb : p.2
            · have hp' : p = (x, false) := Prod.ext hpeq hb
              rw [hp']
              exact hboth.1
            · have hp' : p = (x, true) := Prod.ext hpeq hb
              rw [hp']
              exact hboth.2
          · have hlt : p.1.card < x.card :=
              Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hp1sub, hpeq⟩)
            simp only [shell, words, Finset.mem_filter, Finset.mem_univ, true_and] at hx
            have hp1sm : p.1 ∈ small := by
              simp only [small, words, Finset.mem_filter, Finset.mem_univ, true_and]
              omega
            cases hb : p.2
            · have hp' : p = (p.1, false) := Prod.ext rfl hb
              rw [hp']
              exact (hRsmall p.1 hp1sm).1
            · have hp' : p = (p.1, true) := Prod.ext rfl hb
              rw [hp']
              exact (hRsmall p.1 hp1sm).2
        simp only [region, domain, Finset.mem_filter, Finset.mem_univ, true_and] at hpR
        apply hpR E hEsc
        rw [hTenc]
        exact Finset.inter_eq_left.mpr hTsub
      let F : Finset Word := shell.filter (fun x => (x, true) ∈ region s)
      have hFsub : F ⊆ shell := Finset.filter_subset _ shell
      refine Finset.mem_image.mpr ⟨F, Finset.mem_powerset.mpr hFsub, ?_⟩
      ext xb
      rcases xb with ⟨x, b⟩
      simp only [lift, domain, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro (hsm | ⟨hsh, hb⟩)
        · cases b
          · exact (hRsmall x hsm).1
          · exact (hRsmall x hsm).2
        · by_cases hxF : x ∈ F
          · have hbT : b = true := by simpa [hxF] using hb
            subst hbT
            exact (Finset.mem_filter.mp hxF).2
          · have hbF : b = false := by simpa [hxF] using hb
            subst hbF
            have hximg : x ∈ (region s).image Prod.fst := by
              rw [hRimg]
              exact Finset.mem_union_right small hsh
            rcases Finset.mem_image.mp hximg with ⟨p, hpR, rfl⟩
            cases hp2 : p.2
            · exact hp2 ▸ hpR
            · have hpt : (p.1, true) ∈ region s := hp2 ▸ hpR
              have : p.1 ∈ F := Finset.mem_filter.mpr ⟨hsh, hpt⟩
              exact (hxF this).elim
      · intro hxb
        have hximg : x ∈ small ∪ shell := by
          rw [← hRimg]
          exact Finset.mem_image.mpr ⟨(x, b), hxb, rfl⟩
        rcases Finset.mem_union.mp hximg with hsm | hsh
        · exact Or.inl hsm
        · refine Or.inr ⟨hsh, ?_⟩
          cases b
          · have hnot : x ∉ F := by
              intro hxF
              have hxt : (x, true) ∈ region s := (Finset.mem_filter.mp hxF).2
              exact hshell_not_both x hsh ⟨hxb, hxt⟩
            simp [hnot]
          · have hxF : x ∈ F := Finset.mem_filter.mpr ⟨hsh, hxb⟩
            simp [hxF]
    · intro hR
      rcases Finset.mem_image.mp hR with ⟨F, hFpow, rfl⟩
      have hFsub : F ⊆ shell := Finset.mem_powerset.mp hFpow
      let s : Scope → Scope := fun E =>
        if (none : Site) ∈ E then
          let x : Word := (Finset.univ : Finset (Fin m)).filter (fun i => (some i : Site) ∈ E)
          encode x (!(decide (x ∈ F)))
        else E
      have hreg : region s = lift F := by
        ext xb
        rcases xb with ⟨y, b⟩
        simp only [region, lift, domain, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hforb
          have hyle : y.card ≤ h := by
            by_contra hgt
            have hge : h + 1 ≤ y.card := by omega
            obtain ⟨x, hxy, hxcard⟩ := Finset.exists_subset_card_eq hge
            let E : Scope := x.image (fun i => (some i : Site))
            have hEsc : E ∈ scopes := by
              dsimp only [scopes]
              rw [Finset.mem_powersetCard]
              refine ⟨Finset.subset_univ E, ?_⟩
              dsimp only [E]
              rw [Finset.card_image_of_injective x (Option.some_injective (Fin m))]
              exact hxcard
            have hnone : (none : Site) ∉ E := by
              intro hmem
              have h1 : (none : Option (Fin m)) ∈ enc x false := hmem
              have h2 := (mem_enc_none x false).mp h1
              exact Bool.noConfusion h2
            have hsE : s E = E := by simp [s, hnone]
            apply hforb E hEsc
            rw [hsE, Finset.inter_self]
            apply Finset.inter_eq_right.mpr
            intro u hu
            rcases Finset.mem_image.mp hu with ⟨i, hi, rfl⟩
            exact (mem_enc_some y b i).mpr (hxy hi)
          by_cases hlt : y.card < h
          · left
            simp only [small, words, Finset.mem_filter, Finset.mem_univ, true_and]
            exact hlt
          · have hycard : y.card = h := by omega
            have hysh : y ∈ shell := by
              simp only [shell, words, Finset.mem_filter, Finset.mem_univ, true_and]
              exact hycard
            refine Or.inr ⟨hysh, ?_⟩
            let E : Scope := insert none (y.image (fun i => (some i : Site)))
            have hEsc : E ∈ scopes := by
              dsimp only [scopes]
              rw [Finset.mem_powersetCard]
              refine ⟨Finset.subset_univ E, ?_⟩
              have h1 : E = enc y true := rfl
              rw [h1, card_enc]
              simp [hycard]
            have hnone : (none : Site) ∈ E := Finset.mem_insert_self _ _
            have hxE : (Finset.univ : Finset (Fin m)).filter (fun i => (some i : Site) ∈ E) = y := by
              ext i
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              exact mem_enc_some y true i
            have hsE : s E = encode y (!(decide (y ∈ F))) := by
              simp only [s, hnone, ite_true, hxE]
            have hsubE : ∀ c : Bool, encode y c ⊆ E := by
              intro c u hu
              cases u with
              | none => exact Finset.mem_insert_self _ _
              | some i =>
                have hi := (mem_enc_some y c i).mp hu
                exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hi)
            have hne := hforb E hEsc
            rw [hsE, Finset.inter_eq_left.mpr (hsubE b), Finset.inter_eq_left.mpr (hsubE _)] at hne
            cases hb : b <;> cases hF : decide (y ∈ F)
            · rfl
            · exfalso; apply hne; simp [hb, hF]
            · exfalso; apply hne; simp [hb, hF]
            · rfl
        · intro hmem E hEsc heq
          simp only [scopes, Finset.mem_powersetCard, Finset.subset_univ, true_and] at hEsc
          by_cases hnone : (none : Site) ∈ E
          · let x : Word := (Finset.univ : Finset (Fin m)).filter (fun i => (some i : Site) ∈ E)
            have hEeq : E = enc x true := by
              ext u
              cases u with
              | none => simp [enc, hnone]
              | some i =>
                simp only [enc, ite_true, Finset.mem_insert, Finset.mem_image, x, Finset.mem_filter,
                  Finset.mem_univ, true_and]
                constructor
                · intro h
                  exact Or.inr ⟨i, h, rfl⟩
                · rintro (h | ⟨a, ha, heq⟩)
                  · cases h
                  · cases heq
                    exact ha
            have hxcard : x.card = h := by
              have hc : E.card = x.card + 1 := by
                rw [hEeq, card_enc]
                simp
              omega
            have hsE : s E = encode x (!(decide (x ∈ F))) := by
              simp only [s, hnone, ite_true, x]
            have hsubE : encode x (!(decide (x ∈ F))) ⊆ E := by
              intro u hu
              cases u with
              | none => exact hnone
              | some i =>
                have hi := (mem_enc_some x _ i).mp hu
                exact (Finset.mem_filter.mp hi).2
            rw [hsE, Finset.inter_eq_left.mpr hsubE] at heq
            have hxy : x ⊆ y := by
              intro i hi
              have hm1 : (some i : Site) ∈ encode x (!(decide (x ∈ F))) :=
                (mem_enc_some x _ i).mpr hi
              rw [← heq] at hm1
              exact (mem_enc_some y b i).mp (Finset.mem_inter.mp hm1).1
            have hb_eq : b = !(decide (x ∈ F)) := by
              have hm : (none : Site) ∈ encode y b ∩ E ↔ (none : Site) ∈ encode x (!(decide (x ∈ F))) := by
                rw [heq]
              simp only [Finset.mem_inter, hnone, and_true, henc_eq, mem_enc_none] at hm
              exact Bool.eq_iff_iff.mpr hm
            rcases hmem with hsm | ⟨hsh, hbf⟩
            · simp only [small, words, Finset.mem_filter, Finset.mem_univ, true_and] at hsm
              have hle := Finset.card_le_card hxy
              omega
            · simp only [shell, words, Finset.mem_filter, Finset.mem_univ, true_and] at hsh
              have hxy_eq : x = y := Finset.eq_of_subset_of_card_le hxy (by omega)
              subst hxy_eq
              rw [hbf] at hb_eq
              cases hdec : decide (x ∈ F) <;> simp [hdec] at hb_eq
          · have hsE : s E = E := by simp [s, hnone]
            rw [hsE, Finset.inter_self] at heq
            have hsub : E ⊆ encode y b := Finset.inter_eq_right.mp heq
            let x : Word := (Finset.univ : Finset (Fin m)).filter (fun i => (some i : Site) ∈ E)
            have hEeq : E = enc x false := by
              ext u
              cases u with
              | none => simp [enc, hnone]
              | some i =>
                simp only [enc, Bool.false_eq_true, ite_false, Finset.mem_image, x, Finset.mem_filter,
                  Finset.mem_univ, true_and]
                constructor
                · intro h
                  exact ⟨i, h, rfl⟩
                · rintro ⟨a, ha, heq⟩
                  cases heq
                  exact ha
            have hxcard : x.card = h + 1 := by
              have hc : E.card = x.card := by
                rw [hEeq, card_enc]
                simp
              omega
            have hxy : x ⊆ y := by
              intro i hi
              have hmE : (some i : Site) ∈ E := (Finset.mem_filter.mp hi).2
              exact (mem_enc_some y b i).mp (hsub hmE)
            have hle := Finset.card_le_card hxy
            rcases hmem with hsm | ⟨hsh, _⟩
            · simp only [small, words, Finset.mem_filter, Finset.mem_univ, true_and] at hsm
              omega
            · simp only [shell, words, Finset.mem_filter, Finset.mem_univ, true_and] at hsh
              omega
      simp only [family, Finset.mem_filter]
      refine ⟨Finset.mem_image.mpr ⟨s, Finset.mem_univ s, hreg⟩, ?_, ?_⟩
      · ext x
        simp only [Finset.mem_image, lift, domain, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_union]
        constructor
        · rintro ⟨⟨y, b⟩, hmem, rfl⟩
          rcases hmem with hsm | ⟨hsh, _⟩
          · exact Or.inl hsm
          · exact Or.inr hsh
        · rintro (hsm | hsh)
          · exact ⟨(x, false), Or.inl hsm, rfl⟩
          · exact ⟨(x, decide (x ∈ F)), Or.inr ⟨hsh, rfl⟩, rfl⟩
      · intro x hsm
        simp only [lift, domain, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨Or.inl hsm, Or.inl hsm⟩
  have hpart3 : ∀ R ∈ family, R.card = 2 * small.card + shell.card := by
    intro R hR
    rw [hpart2] at hR
    rcases Finset.mem_image.mp hR with ⟨F, _, rfl⟩
    exact card_lift F
  have hpart4 : ∀ j : Nat, (family.filter (fun R =>
      (R.filter (fun xb => xb.2 = true)).card = small.card + j)).card = Nat.choose shell.card j := by
    intro j
    have hlift_true : ∀ F ⊆ shell, ((lift F).filter (fun xb => xb.2 = true)).card = small.card + F.card := by
      intro F hFsub
      let A1 : Finset (Word × Bool) := small.image (fun x => (x, true))
      let A2 : Finset (Word × Bool) := F.image (fun x => (x, true))
      have hdisj : Disjoint A1 A2 := by
        rw [Finset.disjoint_left]
        intro xb h1 h2
        rcases Finset.mem_image.mp h1 with ⟨x1, hx1, rfl⟩
        rcases Finset.mem_image.mp h2 with ⟨x2, hx2, heq⟩
        rcases Prod.mk.inj heq with ⟨rfl, _⟩
        have hx2sh := hFsub hx2
        simp only [small, shell, words, Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2sh
        omega
      have heq : (lift F).filter (fun xb => xb.2 = true) = A1 ∪ A2 := by
        ext xb
        rcases xb with ⟨x, b⟩
        simp only [lift, domain, A1, A2, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_union, Finset.mem_image]
        constructor
        · rintro ⟨hsm | ⟨_, hbf⟩, rfl⟩
          · exact Or.inl ⟨x, hsm, rfl⟩
          · have hxF : x ∈ F := by
              by_contra hnot
              simp [hnot] at hbf
            exact Or.inr ⟨x, hxF, rfl⟩
        · rintro (⟨y, hy, hxy⟩ | ⟨y, hy, hxy⟩)
          · rcases Prod.mk.inj hxy with ⟨rfl, rfl⟩
            exact ⟨Or.inl hy, rfl⟩
          · rcases Prod.mk.inj hxy with ⟨rfl, rfl⟩
            exact ⟨Or.inr ⟨hFsub hy, by simp [hy]⟩, rfl⟩
      have hA1 : A1.card = small.card :=
        Finset.card_image_of_injective small (fun _ _ h => (Prod.mk.inj h).1)
      have hA2 : A2.card = F.card :=
        Finset.card_image_of_injective F (fun _ _ h => (Prod.mk.inj h).1)
      rw [heq, Finset.card_union_of_disjoint hdisj, hA1, hA2]
    have hbij :
        (family.filter (fun R => (R.filter (fun xb => xb.2 = true)).card = small.card + j)).card =
        (shell.powersetCard j).card := by
      symm
      refine Finset.card_nbij lift ?_ ?_ ?_
      · intro F hF
        simp only [Finset.mem_coe, Finset.mem_powersetCard] at hF
        simp only [Finset.mem_coe, Finset.mem_filter]
        refine ⟨?_, ?_⟩
        · rw [hpart2]
          exact Finset.mem_image_of_mem lift (Finset.mem_powerset.mpr hF.1)
        · rw [hlift_true F hF.1, hF.2]
      · intro F1 hF1 F2 hF2 heq
        simp only [Finset.mem_coe, Finset.mem_powersetCard] at hF1 hF2
        ext x
        constructor
        · intro hx1
          have hxsh := hF1.1 hx1
          have hm1 : (x, true) ∈ lift F1 := by
            simp only [lift, domain, Finset.mem_filter, Finset.mem_univ, true_and]
            exact Or.inr ⟨hxsh, by simp [hx1]⟩
          rw [heq] at hm1
          simp only [lift, domain, Finset.mem_filter, Finset.mem_univ, true_and] at hm1
          rcases hm1 with hsm | ⟨_, hdec⟩
          · simp only [small, shell, words, Finset.mem_filter, Finset.mem_univ, true_and] at hsm hxsh
            omega
          · by_contra hx2
            simp [hx2] at hdec
        · intro hx2
          have hxsh := hF2.1 hx2
          have hm2 : (x, true) ∈ lift F2 := by
            simp only [lift, domain, Finset.mem_filter, Finset.mem_univ, true_and]
            exact Or.inr ⟨hxsh, by simp [hx2]⟩
          rw [← heq] at hm2
          simp only [lift, domain, Finset.mem_filter, Finset.mem_univ, true_and] at hm2
          rcases hm2 with hsm | ⟨_, hdec⟩
          · simp only [small, shell, words, Finset.mem_filter, Finset.mem_univ, true_and] at hsm hxsh
            omega
          · by_contra hx1
            simp [hx1] at hdec
      · intro R hR
        simp only [Finset.mem_coe, Finset.mem_filter] at hR
        rw [hpart2] at hR
        rcases Finset.mem_image.mp hR.1 with ⟨F, hFpow, rfl⟩
        have hFsub := Finset.mem_powerset.mp hFpow
        have hFcard : F.card = j := by
          have h1 := hR.2
          rw [hlift_true F hFsub] at h1
          omega
        exact ⟨F, by simp [Finset.mem_powersetCard, hFsub, hFcard], rfl⟩
    rw [hbij, Finset.card_powersetCard]
  exact ⟨hpart1, hpart2, hpart3, hpart4⟩

end PEqualNP.Outside.L_lib_1182_aux

theorem PEqualNP.Outside.L_lib_1182 :
∀ (m h : Nat),
  let Site := Option (Fin m)
  let Word := Finset (Fin m)
  let Scope := Finset Site
  let scopes := (Finset.univ : Finset Site).powersetCard (h + 1)
  let words := (Finset.univ : Finset Word)
  let small := words.filter (fun x => x.card < h)
  let shell := words.filter (fun x => x.card = h)
  let encode := fun (x : Word) (b : Bool) =>
    let old := x.image (fun i => (some i : Site))
    if b then insert none old else old
  let domain := (Finset.univ : Finset (Word × Bool))
  let region := fun (s : Scope → Scope) => domain.filter (fun xb =>
    ∀ E ∈ scopes, encode xb.1 xb.2 ∩ E ≠ s E ∩ E)
  let allRegions := (Finset.univ : Finset (Scope → Scope)).image region
  let family := allRegions.filter (fun R =>
    R.image Prod.fst = small ∪ shell ∧ ∀ x ∈ small, (x, false) ∈ R ∧ (x, true) ∈ R)
  let lift := fun (F : Finset Word) => domain.filter (fun xb =>
    xb.1 ∈ small ∨ (xb.1 ∈ shell ∧ xb.2 = decide (xb.1 ∈ F)))
  (∀ R ∈ allRegions, R.card ≤ 2 * small.card + shell.card) ∧
  family = shell.powerset.image lift ∧
  (∀ R ∈ family, R.card = 2 * small.card + shell.card) ∧
  (∀ j : Nat, (family.filter (fun R =>
    (R.filter (fun xb => xb.2 = true)).card = small.card + j)).card = Nat.choose shell.card j) :=
  PEqualNP.Outside.L_lib_1182_aux.main_aux
