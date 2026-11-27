import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset

namespace PEqualNP.Outside.L_lib_645

private def binSet {bigCount m : Nat} (w : Fin m → Fin (bigCount + 2)) : Finset (Fin m) :=
  Finset.univ.filter (fun i => (w i).val < 2)

private def ontoSet (bigCount n : Nat) : Finset (Fin n → Fin bigCount) :=
  (Finset.univ : Finset (Fin n → Fin bigCount)).filter
    (fun word => ∀ symbol, ∃ pos, word pos = symbol)

private def imSet {m k : Nat} (rows : Fin k → Fin m → Bool) (S : Finset (Fin m)) :
    Finset (S → Bool) :=
  (Finset.univ : Finset (Fin k)).image (fun j => fun i : S => rows j i.val)

private lemma card_univ_bool_fun {m : Nat} (S : Finset (Fin m)) :
    (Finset.univ : Finset (S → Bool)).card = 2 ^ S.card := by
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]

private lemma seen_le {m k : Nat} (rows : Fin k → Fin m → Bool) (S : Finset (Fin m)) :
    (imSet rows S).card ≤ 2 ^ S.card := by
  rw [← card_univ_bool_fun S]
  exact Finset.card_le_univ _

private lemma onto_eq_zero_of_lt {bigCount n : Nat} (h : n < bigCount) :
    (ontoSet bigCount n).card = 0 := by
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro word hword
  have hsurj : Function.Surjective word := (Finset.mem_filter.mp hword).2
  have hle : Fintype.card (Fin bigCount) ≤ Fintype.card (Fin n) :=
    Fintype.card_le_of_surjective word hsurj
  rw [Fintype.card_fin, Fintype.card_fin] at hle
  exact Nat.not_lt.mpr hle h

private lemma onto_pos_self (bigCount : Nat) :
    0 < (ontoSet bigCount bigCount).card :=
  Finset.card_pos.mpr ⟨id, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun s => ⟨s, rfl⟩⟩⟩

private lemma seen_eq_pow_of_subset {m k : Nat} (rows : Fin k → Fin m → Bool)
    {S T : Finset (Fin m)} (hST : S ⊆ T) (hT : (imSet rows T).card = 2 ^ T.card) :
    (imSet rows S).card = 2 ^ S.card := by
  have hTuniv : imSet rows T = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      (by rw [hT, card_univ_bool_fun])
  have hSuniv : imSet rows S = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro f
    let g : T → Bool := fun i => if h : i.val ∈ S then f ⟨i.val, h⟩ else false
    have hg : g ∈ imSet rows T := by
      rw [hTuniv]
      exact Finset.mem_univ g
    rcases Finset.mem_image.mp hg with ⟨j, _, hj⟩
    refine Finset.mem_image.mpr ⟨j, Finset.mem_univ j, ?_⟩
    funext i
    have hji := congrFun hj ⟨i.val, hST i.property⟩
    simpa [g, i.property] using hji
  rw [hSuniv, card_univ_bool_fun]

private lemma fiber_card {bigCount m k : Nat} (rows : Fin k → Fin m → Bool)
    (S : Finset (Fin m)) :
    (((Finset.univ : Finset (Fin m → Fin (bigCount + 2))).filter
      (fun w =>
        ¬ ((∃ c : Fin bigCount, ∀ i, (w i).val ≠ c.val + 2) ∨
           (∃ j : Fin k, ∀ i, (w i).val ≠ (rows j i).toNat)))).filter
      (fun w => binSet w = S)).card =
    (2 ^ S.card - (imSet rows S).card) * (ontoSet bigCount (m - S.card)).card := by
  have hcard : Fintype.card ↥(Sᶜ) = m - S.card := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
  let e : ↥(Sᶜ) ≃ Fin (m - S.card) := Fintype.equivFinOfCardEq hcard
  let ofPair : (S → Bool) × (Fin (m - S.card) → Fin bigCount) →
      Fin m → Fin (bigCount + 2) :=
    fun p i =>
      if hi : i ∈ S then
        ⟨(! p.1 ⟨i, hi⟩).toNat, by cases p.1 ⟨i, hi⟩ <;> simp⟩
      else
        ⟨(p.2 (e ⟨i, Finset.mem_compl.mpr hi⟩)).val + 2,
          Nat.add_lt_add_right (p.2 (e ⟨i, Finset.mem_compl.mpr hi⟩)).isLt 2⟩
  have hbin : ∀ p, binSet (ofPair p) = S := by
    intro p
    ext i
    simp only [binSet, Finset.mem_filter, Finset.mem_univ, true_and, ofPair]
    split_ifs with hi
    · refine ⟨fun _ => hi, fun _ => ?_⟩
      cases p.1 ⟨i, hi⟩ <;> simp
    · exact ⟨fun h => absurd h (Nat.not_lt.mpr (Nat.le_add_left 2 _)), fun h => absurd h hi⟩
  have hprod :
      ((imSet rows S)ᶜ ×ˢ ontoSet bigCount (m - S.card)).card =
      (2 ^ S.card - (imSet rows S).card) * (ontoSet bigCount (m - S.card)).card := by
    rw [Finset.card_product, Finset.card_compl, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_coe]
  rw [← hprod]
  symm
  refine Finset.card_bij (fun p _ => ofPair p) ?_ ?_ ?_
  · intro p hp
    rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
    have hpat : p.1 ∉ imSet rows S := Finset.mem_compl.mp hp1
    have hword : ∀ symbol, ∃ pos, p.2 pos = symbol := (Finset.mem_filter.mp hp2).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hbin p⟩
    rintro (⟨c, hc⟩ | ⟨j, hj⟩)
    · rcases hword c with ⟨pos, hpos⟩
      have hne := hc (e.symm pos).val
      have hni : (e.symm pos).val ∉ S := Finset.mem_compl.mp (e.symm pos).property
      have hev : (ofPair p (e.symm pos).val).val = c.val + 2 := by
        simp only [ofPair, hni, ↓reduceDIte, Subtype.coe_eta, e.apply_symm_apply, hpos]
      exact hne hev
    · apply hpat
      refine Finset.mem_image.mpr ⟨j, Finset.mem_univ j, ?_⟩
      funext i
      have hne := hj i.val
      simp only [ofPair, i.property, ↓reduceDIte] at hne
      cases h1 : rows j i.val <;> cases h2 : p.1 i <;> simp [h1, h2] at hne ⊢
  · intro p₁ _ p₂ _ heq
    apply Prod.ext
    · funext i
      have hval := congrArg Fin.val (congrFun heq i.val)
      simp only [ofPair, i.property, ↓reduceDIte] at hval
      cases h1 : p₁.1 i <;> cases h2 : p₂.1 i <;> simp [h1, h2] at hval ⊢
    · funext pos
      have hval := congrArg Fin.val (congrFun heq (e.symm pos).val)
      have hni : (e.symm pos).val ∉ S := Finset.mem_compl.mp (e.symm pos).property
      simp only [ofPair, hni, ↓reduceDIte, Subtype.coe_eta, e.apply_symm_apply] at hval
      exact Fin.ext (Nat.add_right_cancel hval)
  · intro w hw
    rcases Finset.mem_filter.mp hw with ⟨hwm, hwS⟩
    have hnot := (Finset.mem_filter.mp hwm).2
    have hnotConst : ¬ ∃ c : Fin bigCount, ∀ i, (w i).val ≠ c.val + 2 := fun h => hnot (Or.inl h)
    have hnotRow : ¬ ∃ j : Fin k, ∀ i, (w i).val ≠ (rows j i).toNat := fun h => hnot (Or.inr h)
    let pat : S → Bool := fun i => decide ((w i.val).val = 0)
    let word : Fin (m - S.card) → Fin bigCount := fun pos =>
      ⟨(w (e.symm pos).val).val - 2, by
        have hni : (e.symm pos).val ∉ S := Finset.mem_compl.mp (e.symm pos).property
        have hni' : (e.symm pos).val ∉ binSet w := fun h => hni (hwS ▸ h)
        have hge : 2 ≤ (w (e.symm pos).val).val :=
          Nat.le_of_not_lt (fun hlt => hni' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩))
        have hlt := (w (e.symm pos).val).isLt
        omega⟩
    refine ⟨(pat, word), Finset.mem_product.mpr ⟨Finset.mem_compl.mpr ?_, ?_⟩, ?_⟩
    · intro hmem
      rcases Finset.mem_image.mp hmem with ⟨j, _, hj⟩
      apply hnotRow
      refine ⟨j, fun i => ?_⟩
      by_cases hi : i ∈ S
      · have hlt : (w i).val < 2 := by
          have hi' : i ∈ binSet w := hwS.symm ▸ hi
          exact (Finset.mem_filter.mp hi').2
        have hji : rows j i = decide ((w i).val = 0) := congrFun hj ⟨i, hi⟩
        rw [hji]
        cases hw0 : (w i).val with
        | zero => decide
        | succ n =>
          have hn : n = 0 := by omega
          subst hn
          decide
      · have hge : 2 ≤ (w i).val := by
          have hi' : i ∉ binSet w := fun h => hi (hwS ▸ h)
          exact Nat.le_of_not_lt (fun hlt => hi' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩))
        cases rows j i <;> dsimp [Bool.toNat] <;> omega
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun c => ?_⟩
      have hex : ∃ i : Fin m, (w i).val = c.val + 2 := by
        by_contra hall
        apply hnotConst
        refine ⟨c, fun i hi => hall ⟨i, hi⟩⟩
      rcases hex with ⟨i, hi⟩
      have hni : i ∉ S := by
        intro hmem
        have hmem' : i ∈ binSet w := hwS.symm ▸ hmem
        have hlt : (w i).val < 2 := (Finset.mem_filter.mp hmem').2
        omega
      refine ⟨e ⟨i, Finset.mem_compl.mpr hni⟩, Fin.ext ?_⟩
      simp only [word, e.symm_apply_apply, hi, Nat.add_sub_cancel]
    · funext i
      apply Fin.ext
      by_cases hi : i ∈ S
      · have hi' : i ∈ binSet w := hwS.symm ▸ hi
        have hlt : (w i).val < 2 := (Finset.mem_filter.mp hi').2
        simp only [ofPair, hi, ↓reduceDIte, pat]
        cases hw0 : (w i).val with
        | zero => rfl
        | succ n =>
          have hn : n = 0 := by omega
          subst hn
          rfl
      · have hge : 2 ≤ (w i).val := by
          have hi' : i ∉ binSet w := fun h => hi (hwS ▸ h)
          exact Nat.le_of_not_lt (fun hlt => hi' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩))
        simp only [ofPair, hi, ↓reduceDIte, word, e.symm_apply_apply, Nat.sub_add_cancel hge]

private lemma main_lemma (bigCount m k : Nat) (hm : bigCount + 2 ≤ m)
    (rows : Fin k → Fin m → Bool) :
    let A := Fin (bigCount + 2)
    let W := Fin m → A
    let onto := fun (n : Nat) =>
      ((Finset.univ : Finset (Fin n → Fin bigCount)).filter
        (fun word => ∀ symbol, ∃ pos, word pos = symbol)).card
    let hit := fun (w : W) =>
      (∃ c : Fin bigCount, ∀ i, (w i).val ≠ c.val + 2) ∨
      (∃ j : Fin k, ∀ i, (w i).val ≠ (rows j i).toNat)
    let seen := fun (S : Finset (Fin m)) =>
      ((Finset.univ : Finset (Fin k)).image (fun j => fun i : S => rows j i.val)).card
    let missing := (Finset.univ : Finset W).filter (fun w => ¬ hit w)
    missing.card =
      (Finset.univ : Finset (Finset (Fin m))).sum (fun S =>
        (2 ^ S.card - seen S) * onto (m - S.card)) ∧
    (missing = ∅ ↔ ∀ S : Finset (Fin m), S.card = m - bigCount → seen S = 2 ^ S.card) := by
  intro A W onto hit seen missing
  have hcount : missing.card =
      (Finset.univ : Finset (Finset (Fin m))).sum (fun S =>
        (2 ^ S.card - seen S) * onto (m - S.card)) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := binSet) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    exact Finset.sum_congr rfl fun S _ => fiber_card rows S
  refine ⟨hcount, ?_⟩
  constructor
  · intro hEmpty S hS
    have hsum0 : (Finset.univ : Finset (Finset (Fin m))).sum (fun T =>
        (2 ^ T.card - seen T) * onto (m - T.card)) = 0 := by
      rw [← hcount, hEmpty, Finset.card_empty]
    have hterm : (2 ^ S.card - seen S) * onto (m - S.card) = 0 :=
      Finset.sum_eq_zero_iff.mp hsum0 S (Finset.mem_univ S)
    have hsub : m - S.card = bigCount := by omega
    have hpos : 0 < onto (m - S.card) := by
      rw [hsub]
      exact onto_pos_self bigCount
    have hdiff : 2 ^ S.card - seen S = 0 :=
      (Nat.mul_eq_zero.mp hterm).resolve_right (Nat.ne_of_gt hpos)
    have hle : seen S ≤ 2 ^ S.card := seen_le rows S
    omega
  · intro hAll
    rw [← Finset.card_eq_zero, hcount]
    apply Finset.sum_eq_zero
    intro S _
    rcases Nat.lt_or_ge (m - S.card) bigCount with hlt | hge
    · have ho : onto (m - S.card) = 0 := onto_eq_zero_of_lt hlt
      rw [ho, Nat.mul_zero]
    · have hSm : S.card ≤ m := by
        simpa [Fintype.card_fin] using Finset.card_le_univ S
      have hScard : S.card ≤ m - bigCount := by omega
      have hUcard : m - bigCount ≤ Fintype.card (Fin m) := by
        rw [Fintype.card_fin]
        omega
      rcases Finset.exists_superset_card_eq hScard hUcard with ⟨T, hST, hTcard⟩
      have hS : seen S = 2 ^ S.card := seen_eq_pow_of_subset rows hST (hAll T hTcard)
      rw [hS, Nat.sub_self, Nat.zero_mul]

end PEqualNP.Outside.L_lib_645

theorem PEqualNP.Outside.L_lib_645 :
    ∀ (bigCount m k : Nat), bigCount+2 ≤ m →
      let A := Fin (bigCount+2)
      let W := Fin m → A
      let onto := fun (n : Nat) =>
        ((Finset.univ : Finset (Fin n → Fin bigCount)).filter (fun word => ∀ symbol, ∃ pos, word pos = symbol)).card
      ∀ rows : Fin k → Fin m → Bool,
        let hit := fun (w : W) =>
          (∃ c : Fin bigCount, ∀ i, (w i).val ≠ c.val+2) ∨
          (∃ j : Fin k, ∀ i, (w i).val ≠ (rows j i).toNat)
        let seen := fun (S : Finset (Fin m)) =>
          ((Finset.univ : Finset (Fin k)).image (fun j => fun i : S => rows j i.val)).card
        let missing := (Finset.univ : Finset W).filter (fun w => ¬ hit w)
        missing.card =
          (Finset.univ : Finset (Finset (Fin m))).sum (fun S =>
            (2^S.card - seen S) * onto (m-S.card)) ∧
        (missing = ∅ ↔ ∀ S : Finset (Fin m), S.card = m-bigCount → seen S = 2^S.card) :=
  fun bigCount m k hm rows => PEqualNP.Outside.L_lib_645.main_lemma bigCount m k hm rows
