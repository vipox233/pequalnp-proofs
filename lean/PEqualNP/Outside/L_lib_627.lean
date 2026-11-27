import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi

namespace PEqualNP.Outside.L_lib_627

private def occ (alphabet labels width : Nat) : Nat :=
  ((Finset.univ : Finset (Fin width → Fin alphabet)).filter (fun word =>
    ∀ a : Fin labels, ∃ i, (word i).val = a.val)).card

private def hit {q m L : Nat} (menu : Fin m → Fin L → Fin q) : Nat :=
  ((Finset.univ : Finset (Fin m → Fin q)).filter (fun input =>
    ∃ a, ∀ i, input i ≠ menu i a)).card

private def stdCol {q L : Nat} (hLq : L ≤ q) : Fin L → Fin q :=
  fun a => ⟨a.val, Nat.lt_of_lt_of_le a.isLt hLq⟩

private lemma stdCol_injective {q L : Nat} (hLq : L ≤ q) :
    Function.Injective (stdCol hLq) := fun _ _ h =>
  Fin.ext (congrArg (Fin.val (n := q)) h)

private def stdMenu {q m L : Nat} (hLq : L ≤ q) : Fin m → Fin L → Fin q :=
  fun _ => stdCol hLq

private def skipIdx {m : Nat} (k : Fin m) (j : Fin (m - 1)) : Fin m :=
  if h : j.val < k.val then ⟨j.val, by omega⟩ else ⟨j.val + 1, by omega⟩

private lemma skipIdx_ne {m : Nat} (k : Fin m) (j : Fin (m - 1)) : skipIdx k j ≠ k := by
  unfold skipIdx
  split_ifs with h
  · intro heq; have := congrArg Fin.val heq; dsimp at this; omega
  · intro heq; have := congrArg Fin.val heq; dsimp at this; omega

private def joinCol {q m : Nat} (k : Fin m) (y : Fin (m - 1) → Fin q) (c : Fin q) :
    Fin m → Fin q :=
  fun i =>
    if h : i = k then c
    else if hlt : i.val < k.val then y ⟨i.val, by omega⟩
    else y ⟨i.val - 1, by omega⟩

private def splitCol {q m : Nat} (k : Fin m) (x : Fin m → Fin q) :
    (Fin (m - 1) → Fin q) × Fin q :=
  (fun j => x (skipIdx k j), x k)

private lemma joinCol_self {q m : Nat} (k : Fin m) (y : Fin (m - 1) → Fin q) (c : Fin q) :
    joinCol k y c k = c := by
  simp [joinCol]

private lemma joinCol_skipIdx {q m : Nat} (k : Fin m) (y : Fin (m - 1) → Fin q) (c : Fin q)
    (j : Fin (m - 1)) : joinCol k y c (skipIdx k j) = y j := by
  have hne := skipIdx_ne k j
  unfold joinCol
  simp only [hne, ↓reduceDIte]
  by_cases h : j.val < k.val
  · have hs : skipIdx k j = ⟨j.val, by omega⟩ := by unfold skipIdx; simp only [h, ↓reduceDIte]
    simp only [hs, h, ↓reduceDIte]
  · have hs : skipIdx k j = ⟨j.val + 1, by omega⟩ := by unfold skipIdx; simp only [h, ↓reduceDIte]
    have hge : ¬ j.val + 1 < k.val := by omega
    simp only [hs, hge, ↓reduceDIte]
    exact congrArg y (Fin.ext (Nat.add_sub_cancel j.val 1))

private lemma joinCol_splitCol {q m : Nat} (k : Fin m) (x : Fin m → Fin q) :
    joinCol k (splitCol k x).1 (splitCol k x).2 = x := by
  funext i
  unfold joinCol splitCol
  dsimp
  split_ifs with h1 h2
  · rw [h1]
  · congr 1
    unfold skipIdx
    simp only [h2, ↓reduceDIte]
  · congr 1
    unfold skipIdx
    have hge : ¬ i.val - 1 < k.val := by
      have : i.val ≠ k.val := fun hv => h1 (Fin.ext hv)
      omega
    simp only [hge, ↓reduceDIte]
    apply Fin.ext
    dsimp
    omega

private lemma splitCol_joinCol {q m : Nat} (k : Fin m) (y : Fin (m - 1) → Fin q) (c : Fin q) :
    splitCol k (joinCol k y c) = (y, c) := by
  apply Prod.ext
  · funext j; exact joinCol_skipIdx k y c j
  · exact joinCol_self k y c

private lemma card_univ_fun (q m : Nat) :
    (Finset.univ : Finset (Fin m → Fin q)).card = q ^ m := by
  induction m with
  | zero =>
    have h : (Finset.univ : Finset (Fin 0 → Fin q)) = {Fin.elim0} := by
      ext f; simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      funext i; exact Fin.elim0 i
    rw [h, Finset.card_singleton, Nat.pow_zero]
  | succ m ih =>
    let k : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
    have hbij :
        ((Finset.univ : Finset (Fin m → Fin q)) ×ˢ (Finset.univ : Finset (Fin q))).card =
        (Finset.univ : Finset (Fin (m + 1) → Fin q)).card := by
      refine Finset.card_bij (fun p _ => joinCol k p.1 p.2)
        (fun _ _ => Finset.mem_univ _) ?_ ?_
      · intro p₁ _ p₂ _ heq
        have h := congrArg (splitCol k) heq
        rw [splitCol_joinCol, splitCol_joinCol] at h
        exact h
      · intro x _
        exact ⟨splitCol k x, Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
          joinCol_splitCol k x⟩
    rw [← hbij, Finset.card_product, ih, Finset.card_univ, Fintype.card_fin, Nat.pow_succ]

private lemma hit_stdMenu {q m L : Nat} (hLq : L ≤ q) :
    hit (stdMenu (m := m) hLq) = q ^ m - occ q L m := by
  classical
  have htot : (Finset.univ : Finset (Fin m → Fin q)).card = q ^ m := card_univ_fun q m
  let p : (Fin m → Fin q) → Prop := fun input => ∃ a : Fin L, ∀ i : Fin m, input i ≠ stdMenu hLq i a
  have hpart :
      ((Finset.univ : Finset (Fin m → Fin q)).filter p).card +
      ((Finset.univ : Finset (Fin m → Fin q)).filter (fun input => ¬ p input)).card =
      (Finset.univ : Finset (Fin m → Fin q)).card := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.card_eq_sum_ones, Finset.sum_filter,
      ← Finset.sum_add_distrib, Finset.card_eq_sum_ones]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : ∃ a : Fin L, ∀ i : Fin m, x i ≠ stdMenu hLq i a
    · simp only [p, hx, ↓reduceIte, not_true_eq_false, Nat.add_zero]
    · simp only [p, hx, ↓reduceIte, not_false_eq_true, Nat.zero_add]
  have hneg :
      ((Finset.univ : Finset (Fin m → Fin q)).filter (fun input => ¬ p input)).card = occ q L m := by
    unfold occ
    apply congrArg Finset.card
    ext input
    simp only [p, Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_forall, not_not]
    constructor
    · intro h a
      obtain ⟨i, hi⟩ := h a
      exact ⟨i, congrArg Fin.val hi⟩
    · intro h a
      obtain ⟨i, hi⟩ := h a
      exact ⟨i, Fin.ext hi⟩
  have hhit :
      ((Finset.univ : Finset (Fin m → Fin q)).filter p).card =
      hit (stdMenu (m := m) hLq) := by
    unfold hit
    apply congrArg Finset.card
    ext input
    simp only [p, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hhit, hneg, htot] at hpart
  omega

private def colHit {q L : Nat} (col : Fin L → Fin q) (S : Finset (Fin L)) : Finset (Fin q) :=
  Finset.univ.filter (fun c => ∃ a ∈ S, c ≠ col a)

private def isBad {q L : Nat} (col : Fin L → Fin q) (S : Finset (Fin L)) : Prop :=
  ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ ∀ x ∈ S, col x = col a

private lemma colHit_eq_univ {q L : Nat} (col : Fin L → Fin q) (S : Finset (Fin L))
    {a b : Fin L} (ha : a ∈ S) (hb : b ∈ S) (hne : col a ≠ col b) :
    colHit col S = Finset.univ := by
  ext c
  simp only [colHit, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  by_cases hc : c = col a
  · exact ⟨b, hb, hc ▸ hne⟩
  · exact ⟨a, ha, hc⟩

private lemma colHit_eq_erase {q L : Nat} (col : Fin L → Fin q) (S : Finset (Fin L))
    {a : Fin L} (ha : a ∈ S) (hconst : ∀ x ∈ S, col x = col a) :
    colHit col S = Finset.univ.erase (col a) := by
  ext c
  simp only [colHit, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
  constructor
  · rintro ⟨x, hx, hcx⟩
    rwa [hconst x hx] at hcx
  · intro hca
    exact ⟨a, ha, hca⟩

private lemma card_colHit_eq {q L : Nat} (hq : 0 < q)
    (col col' : Fin L → Fin q) (hcol' : Function.Injective col')
    (S : Finset (Fin L)) [Decidable (isBad col S)] :
    (colHit col S).card + (if isBad col S then 1 else 0) = (colHit col' S).card := by
  by_cases hne : S.Nonempty
  · obtain ⟨a, ha⟩ := hne
    by_cases hsing : ∀ b ∈ S, b = a
    · have hnb : ¬ isBad col S := by
        rintro ⟨u, hu, v, hv, huv, _⟩
        exact huv ((hsing u hu).trans (hsing v hv).symm)
      have hc1 : colHit col S = Finset.univ.erase (col a) :=
        colHit_eq_erase col S ha (fun x hx => by rw [hsing x hx])
      have hc2 : colHit col' S = Finset.univ.erase (col' a) :=
        colHit_eq_erase col' S ha (fun x hx => by rw [hsing x hx])
      simp only [hnb, ↓reduceIte, Nat.add_zero, hc1, hc2,
        Finset.card_erase_of_mem (Finset.mem_univ _)]
    · have ⟨b, hb, hba⟩ : ∃ b ∈ S, b ≠ a := by
        by_contra h
        exact hsing (fun b hb => by by_contra hba; exact h ⟨b, hb, hba⟩)
      have hc2 : colHit col' S = Finset.univ :=
        colHit_eq_univ col' S ha hb (fun h => hba (hcol' h).symm)
      by_cases hconst : ∀ x ∈ S, col x = col a
      · have hbad : isBad col S := ⟨a, ha, b, hb, hba.symm, hconst⟩
        have hc1 : colHit col S = Finset.univ.erase (col a) :=
          colHit_eq_erase col S ha hconst
        simp only [hbad, ↓reduceIte, hc1, hc2,
          Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
        omega
      · have ⟨x, hx, hxa⟩ : ∃ x ∈ S, col x ≠ col a := by
          by_contra h
          exact hconst (fun x hx => by by_contra hxa; exact h ⟨x, hx, hxa⟩)
        have hnb : ¬ isBad col S := by
          rintro ⟨u, _, _, _, _, hall⟩
          exact hxa ((hall x hx).trans (hall a ha).symm)
        have hc1 : colHit col S = Finset.univ := colHit_eq_univ col S ha hx hxa.symm
        simp only [hnb, ↓reduceIte, Nat.add_zero, hc1, hc2]
  · have hS : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst hS
    have hnb : ¬ isBad col ∅ := by simp [isBad]
    have h0 : ∀ f : Fin L → Fin q, colHit f ∅ = ∅ := fun f => by
      ext c; simp [colHit]
    simp only [hnb, ↓reduceIte, Nat.add_zero, h0]

private def surv {q m L : Nat} (table : Fin m → Fin L → Fin q) (k : Fin m)
    (y : Fin (m - 1) → Fin q) : Finset (Fin L) :=
  Finset.univ.filter (fun a => ∀ j : Fin (m - 1), y j ≠ table (skipIdx k j) a)

private lemma hit_eq_sum_colHit {q m L : Nat} (table : Fin m → Fin L → Fin q) (k : Fin m) :
    hit table = ∑ y : Fin (m - 1) → Fin q, (colHit (table k) (surv table k y)).card := by
  classical
  rw [← Finset.card_sigma]
  unfold hit
  symm
  refine Finset.card_bij (fun p _ => joinCol k p.1 p.2) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and, colHit, Finset.mem_filter,
      surv] at hp
    obtain ⟨a, ha, hne⟩ := hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨a, fun i => ?_⟩
    by_cases hik : i = k
    · subst hik; rw [joinCol_self]; exact hne
    · have hex : ∃ j : Fin (m - 1), skipIdx k j = i := by
        by_cases hlt : i.val < k.val
        · refine ⟨⟨i.val, by omega⟩, ?_⟩
          unfold skipIdx; simp only [hlt, ↓reduceDIte]
        · have hv : i.val ≠ k.val := fun hv => hik (Fin.ext hv)
          refine ⟨⟨i.val - 1, by omega⟩, ?_⟩
          unfold skipIdx
          have hge : ¬ i.val - 1 < k.val := by omega
          simp only [hge, ↓reduceDIte]
          apply Fin.ext; dsimp; omega
      obtain ⟨j, rfl⟩ := hex
      rw [joinCol_skipIdx]
      exact ha j
  · intro p₁ _ p₂ _ heq
    have h := congrArg (splitCol k) heq
    rw [splitCol_joinCol, splitCol_joinCol] at h
    cases p₁; cases p₂
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    dsimp at h1 h2
    subst h1; subst h2; rfl
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨a, ha⟩ := hx
    refine ⟨⟨(splitCol k x).1, (splitCol k x).2⟩, ?_, joinCol_splitCol k x⟩
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and, colHit, Finset.mem_filter, surv]
    exact ⟨a, fun j => ha (skipIdx k j), ha k⟩

private lemma hit_update_eq {q m L : Nat} (hq : 0 < q)
    (table : Fin m → Fin L → Fin q) (k : Fin m)
    (col' : Fin L → Fin q) (hcol' : Function.Injective col')
    [DecidablePred (fun y => isBad (table k) (surv table k y))] :
    hit table + ((Finset.univ : Finset (Fin (m - 1) → Fin q)).filter
      (fun y => isBad (table k) (surv table k y))).card =
    hit (Function.update table k col') := by
  rw [hit_eq_sum_colHit table k, hit_eq_sum_colHit (Function.update table k col') k]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hsurv : surv (Function.update table k col') k y = surv table k y := by
    ext a
    simp only [surv, Finset.mem_filter, Finset.mem_univ, true_and]
    refine forall_congr' fun j => ?_
    rw [Function.update_of_ne (skipIdx_ne k j)]
  rw [hsurv, Function.update_self]
  exact card_colHit_eq hq (table k) col' hcol' (surv table k y)

private lemma hit_update_le {q m L : Nat} (hq : 0 < q)
    (table : Fin m → Fin L → Fin q) (k : Fin m)
    (col' : Fin L → Fin q) (hcol' : Function.Injective col') :
    hit table ≤ hit (Function.update table k col') := by
  classical
  have h := hit_update_eq hq table k col' hcol'
  omega

private lemma hit_update_eq_of_inj {q m L : Nat} (hq : 0 < q)
    (table : Fin m → Fin L → Fin q) (k : Fin m)
    (hk : Function.Injective (table k))
    (col' : Fin L → Fin q) (hcol' : Function.Injective col') :
    hit table = hit (Function.update table k col') := by
  classical
  have h := hit_update_eq hq table k col' hcol'
  have hzero : ((Finset.univ : Finset (Fin (m - 1) → Fin q)).filter
      (fun y => isBad (table k) (surv table k y))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro y _ hbad
    obtain ⟨a, _, b, hb, hab, hall⟩ := hbad
    exact hab (hk (hall b hb).symm)
  omega

private lemma hit_le_stdMenu {q m L : Nat} (hq : 0 < q) (hLq : L ≤ q)
    (table : Fin m → Fin L → Fin q) :
    hit table ≤ hit (stdMenu (m := m) hLq) := by
  suffices h : ∀ r, r ≤ m →
      hit table ≤ hit (fun i : Fin m => if i.val < r then stdCol hLq else table i) by
    have hm := h m (le_refl m)
    have heq : (fun i : Fin m => if i.val < m then stdCol hLq else table i) = stdMenu hLq := by
      funext i; simp [stdMenu, i.isLt]
    rwa [heq] at hm
  intro r hr
  induction r with
  | zero =>
    have heq : (fun i : Fin m => if i.val < 0 then stdCol hLq else table i) = table := by
      funext i; simp
    rw [heq]
  | succ r ih =>
    have hstep :
        (fun i : Fin m => if i.val < r + 1 then stdCol hLq else table i) =
        Function.update (fun i : Fin m => if i.val < r then stdCol hLq else table i)
          ⟨r, by omega⟩ (stdCol hLq) := by
      funext i
      by_cases hi : i = ⟨r, by omega⟩
      · subst hi; simp
      · rw [Function.update_of_ne hi]
        have hv : i.val ≠ r := fun hv => hi (Fin.ext hv)
        by_cases hlt : i.val < r
        · have hlt' : i.val < r + 1 := by omega
          simp [hlt, hlt']
        · have hlt' : ¬ i.val < r + 1 := by omega
          simp [hlt, hlt']
    rw [hstep]
    exact (ih (by omega)).trans (hit_update_le hq _ ⟨r, by omega⟩ (stdCol hLq) (stdCol_injective hLq))

private lemma hit_eq_stdMenu_of_distinct {q m L : Nat} (hq : 0 < q) (hLq : L ≤ q)
    (table : Fin m → Fin L → Fin q) (hdist : ∀ i, Function.Injective (table i)) :
    hit table = hit (stdMenu (m := m) hLq) := by
  suffices h : ∀ r, r ≤ m →
      hit table = hit (fun i : Fin m => if i.val < r then stdCol hLq else table i) by
    have hm := h m (le_refl m)
    have heq : (fun i : Fin m => if i.val < m then stdCol hLq else table i) = stdMenu hLq := by
      funext i; simp [stdMenu, i.isLt]
    rwa [heq] at hm
  intro r hr
  induction r with
  | zero =>
    have heq : (fun i : Fin m => if i.val < 0 then stdCol hLq else table i) = table := by
      funext i; simp
    rw [heq]
  | succ r ih =>
    have hstep :
        (fun i : Fin m => if i.val < r + 1 then stdCol hLq else table i) =
        Function.update (fun i : Fin m => if i.val < r then stdCol hLq else table i)
          ⟨r, by omega⟩ (stdCol hLq) := by
      funext i
      by_cases hi : i = ⟨r, by omega⟩
      · subst hi; simp
      · rw [Function.update_of_ne hi]
        have hv : i.val ≠ r := fun hv => hi (Fin.ext hv)
        by_cases hlt : i.val < r
        · have hlt' : i.val < r + 1 := by omega
          simp [hlt, hlt']
        · have hlt' : ¬ i.val < r + 1 := by omega
          simp [hlt, hlt']
    rw [hstep]
    have hinj : Function.Injective
        ((fun i : Fin m => if i.val < r then stdCol hLq else table i) ⟨r, by omega⟩) := by
      simp [hdist ⟨r, by omega⟩]
    exact (ih (by omega)).trans
      (hit_update_eq_of_inj hq _ ⟨r, by omega⟩ hinj (stdCol hLq) (stdCol_injective hLq))

private lemma hit_le_update_stdMenu {q m L : Nat} (hq : 0 < q) (hLq : L ≤ q)
    (table : Fin m → Fin L → Fin q) (k : Fin m) :
    hit table ≤ hit (Function.update (stdMenu hLq) k (table k)) := by
  suffices h : ∀ r, r ≤ m →
      hit table ≤ hit (fun i : Fin m => if i ≠ k ∧ i.val < r then stdCol hLq else table i) by
    have hm := h m (le_refl m)
    have heq :
        (fun i : Fin m => if i ≠ k ∧ i.val < m then stdCol hLq else table i) =
        Function.update (stdMenu hLq) k (table k) := by
      funext i
      by_cases hik : i = k
      · subst hik; simp
      · simp [hik, i.isLt, stdMenu]
    rwa [heq] at hm
  intro r hr
  induction r with
  | zero =>
    have heq : (fun i : Fin m => if i ≠ k ∧ i.val < 0 then stdCol hLq else table i) = table := by
      funext i; simp
    rw [heq]
  | succ r ih =>
    by_cases hrk : (⟨r, by omega⟩ : Fin m) = k
    · have heq :
          (fun i : Fin m => if i ≠ k ∧ i.val < r + 1 then stdCol hLq else table i) =
          (fun i : Fin m => if i ≠ k ∧ i.val < r then stdCol hLq else table i) := by
        funext i
        by_cases hik : i = k
        · simp [hik]
        · have hv : i.val ≠ r := fun hv => hik (by rw [← hrk]; exact Fin.ext hv)
          have hiff : i.val < r + 1 ↔ i.val < r := by omega
          simp [hik, hiff]
      rw [heq]
      exact ih (by omega)
    · have hstep :
          (fun i : Fin m => if i ≠ k ∧ i.val < r + 1 then stdCol hLq else table i) =
          Function.update
            (fun i : Fin m => if i ≠ k ∧ i.val < r then stdCol hLq else table i)
            ⟨r, by omega⟩ (stdCol hLq) := by
        funext i
        by_cases hi : i = ⟨r, by omega⟩
        · subst hi; simp [hrk]
        · rw [Function.update_of_ne hi]
          have hv : i.val ≠ r := fun hv => hi (Fin.ext hv)
          have hiff : i.val < r + 1 ↔ i.val < r := by omega
          simp [hiff]
      rw [hstep]
      exact (ih (by omega)).trans
        (hit_update_le hq _ ⟨r, by omega⟩ (stdCol hLq) (stdCol_injective hLq))

private def skip2 (u v x : Nat) : Nat :=
  if x < u then x else if x + 1 < v then x + 1 else x + 2

private def unskip2 (u v y : Nat) : Nat :=
  if y < u then y else if y < v then y - 1 else y - 2

private lemma card_surv_pair_eq_occ {q m L : Nat} (hLq : L ≤ q)
    (a₁ a₂ : Fin L) (hlt : a₁.val < a₂.val) :
    ((Finset.univ : Finset (Fin (m - 1) → Fin q)).filter (fun y =>
      ∀ a : Fin L, (∀ j : Fin (m - 1), (y j).val ≠ a.val) ↔ a = a₁ ∨ a = a₂)).card =
    occ (q - 2) (L - 2) (m - 1) := by
  classical
  have ha₁ : a₁.val < L := a₁.isLt
  have ha₂ : a₂.val < L := a₂.isLt
  unfold occ
  symm
  refine Finset.card_bij
    (fun (w : Fin (m - 1) → Fin (q - 2)) _ =>
      fun j => ⟨skip2 a₁.val a₂.val (w j).val, by
        unfold skip2; split_ifs <;> have := (w j).isLt <;> omega⟩) ?_ ?_ ?_
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    intro a
    constructor
    · intro hne
      by_contra hnot
      have hne1 : a.val ≠ a₁.val := fun hv => hnot (Or.inl (Fin.ext hv))
      have hne2 : a.val ≠ a₂.val := fun hv => hnot (Or.inr (Fin.ext hv))
      let b : Fin (L - 2) := ⟨unskip2 a₁.val a₂.val a.val, by
        unfold unskip2; split_ifs <;> have := a.isLt <;> omega⟩
      obtain ⟨j, hj⟩ := hw b
      have hval : skip2 a₁.val a₂.val (w j).val = a.val := by
        rw [hj]
        change skip2 a₁.val a₂.val (unskip2 a₁.val a₂.val a.val) = a.val
        unfold skip2 unskip2; split_ifs <;> omega
      exact hne j hval
    · rintro (rfl | rfl) j
      · unfold skip2; split_ifs <;> omega
      · unfold skip2; split_ifs <;> omega
  · intro w₁ _ w₂ _ heq
    funext j
    have hv := congrArg Fin.val (congrFun heq j)
    dsimp at hv
    apply Fin.ext
    unfold skip2 at hv
    split_ifs at hv <;> omega
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    have hno1 : ∀ j, (y j).val ≠ a₁.val := (hy a₁).mpr (Or.inl rfl)
    have hno2 : ∀ j, (y j).val ≠ a₂.val := (hy a₂).mpr (Or.inr rfl)
    let w : Fin (m - 1) → Fin (q - 2) := fun j =>
      ⟨unskip2 a₁.val a₂.val (y j).val, by
        have hj1 := hno1 j; have hj2 := hno2 j; have hltq := (y j).isLt
        unfold unskip2; split_ifs <;> omega⟩
    refine ⟨w, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro b
      let a : Fin L := ⟨skip2 a₁.val a₂.val b.val, by
        have := b.isLt; unfold skip2; split_ifs <;> omega⟩
      have hna1 : a ≠ a₁ := by
        intro h; have hv := congrArg Fin.val h; dsimp [a] at hv
        unfold skip2 at hv; split_ifs at hv <;> omega
      have hna2 : a ≠ a₂ := by
        intro h; have hv := congrArg Fin.val h; dsimp [a] at hv
        unfold skip2 at hv; split_ifs at hv <;> omega
      have hnotall : ¬ ∀ j : Fin (m - 1), (y j).val ≠ a.val := by
        intro hall
        rcases (hy a).mp hall with h1 | h2
        · exact hna1 h1
        · exact hna2 h2
      obtain ⟨j, hj⟩ : ∃ j, (y j).val = a.val := by
        by_contra h
        exact hnotall (fun j hj => h ⟨j, hj⟩)
      refine ⟨j, ?_⟩
      change unskip2 a₁.val a₂.val (y j).val = b.val
      rw [hj]
      change unskip2 a₁.val a₂.val (skip2 a₁.val a₂.val b.val) = b.val
      unfold unskip2 skip2; split_ifs <;> omega
    · funext j
      apply Fin.ext
      change skip2 a₁.val a₂.val (unskip2 a₁.val a₂.val (y j).val) = (y j).val
      have hj1 := hno1 j; have hj2 := hno2 j
      unfold skip2 unskip2; split_ifs <;> omega

private lemma occ_gap_pos {q m L : Nat} (hLq : L ≤ q) (h3q : 3 ≤ q) (h2L : 2 ≤ L)
    (hm : L - 1 ≤ m) : 0 < occ (q - 2) (L - 2) (m - 1) := by
  unfold occ
  refine Finset.card_pos.mpr ⟨fun j =>
    if h : j.val < L - 2 then ⟨j.val, by omega⟩ else ⟨0, by omega⟩, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  intro a
  refine ⟨⟨a.val, by have := a.isLt; omega⟩, ?_⟩
  simp [a.isLt]

private lemma hit_add_gap_le {q m L : Nat} (hq : 0 < q) (hLq : L ≤ q)
    (table : Fin m → Fin L → Fin q) (hnd : ¬ ∀ i, Function.Injective (table i)) :
    hit table + occ (q - 2) (L - 2) (m - 1) ≤ hit (stdMenu (m := m) hLq) := by
  classical
  have ⟨k, hnk⟩ : ∃ k, ¬ Function.Injective (table k) := by
    by_contra h
    exact hnd (fun k => by by_contra hnk; exact h ⟨k, hnk⟩)
  have ⟨u, v, huv_eq, huv_ne⟩ : ∃ u v : Fin L, table k u = table k v ∧ u ≠ v := by
    by_contra h
    exact hnk (fun u v heq => by by_contra hne; exact h ⟨u, v, heq, hne⟩)
  have ⟨a₁, a₂, heq_a, hlt_a⟩ : ∃ a₁ a₂ : Fin L, table k a₁ = table k a₂ ∧ a₁.val < a₂.val := by
    rcases Nat.lt_or_gt_of_ne (fun hv => huv_ne (Fin.ext hv)) with hlt | hgt
    · exact ⟨u, v, huv_eq, hlt⟩
    · exact ⟨v, u, huv_eq.symm, hgt⟩
  have hle1 : hit table ≤ hit (Function.update (stdMenu hLq) k (table k)) :=
    hit_le_update_stdMenu hq hLq table k
  have hrep := hit_update_eq hq (Function.update (stdMenu hLq) k (table k)) k
    (stdCol hLq) (stdCol_injective hLq)
  have hupd_eq :
      Function.update (Function.update (stdMenu hLq) k (table k)) k (stdCol hLq) =
      stdMenu hLq := by
    funext i
    by_cases hik : i = k
    · subst hik; simp [stdMenu]
    · simp [hik]
  rw [hupd_eq, Function.update_self] at hrep
  have hsub :
      (Finset.univ : Finset (Fin (m - 1) → Fin q)).filter (fun y =>
        ∀ a : Fin L, (∀ j : Fin (m - 1), (y j).val ≠ a.val) ↔ a = a₁ ∨ a = a₂) ⊆
      (Finset.univ : Finset (Fin (m - 1) → Fin q)).filter (fun y =>
        isBad (table k) (surv (Function.update (stdMenu hLq) k (table k)) k y)) := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    have hmem : ∀ a : Fin L,
        a ∈ surv (Function.update (stdMenu hLq) k (table k)) k y ↔ a = a₁ ∨ a = a₂ := by
      intro a
      simp only [surv, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hy a]
      refine forall_congr' fun j => ?_
      rw [Function.update_of_ne (skipIdx_ne k j)]
      simp only [stdMenu, stdCol, ne_eq, Fin.ext_iff]
    refine ⟨a₁, (hmem a₁).mpr (Or.inl rfl), a₂, (hmem a₂).mpr (Or.inr rfl),
      fun h => by have := congrArg Fin.val h; omega, ?_⟩
    intro x hx
    rcases (hmem x).mp hx with rfl | rfl
    · rfl
    · exact heq_a.symm
  have hcard : occ (q - 2) (L - 2) (m - 1) ≤
      ((Finset.univ : Finset (Fin (m - 1) → Fin q)).filter (fun y =>
        isBad (table k) (surv (Function.update (stdMenu hLq) k (table k)) k y))).card := by
    rw [← card_surv_pair_eq_occ hLq a₁ a₂ hlt_a]
    exact Finset.card_le_card hsub
  omega

private lemma exists_attaining_gap {q m L : Nat} (hq : 0 < q) (hLq : L ≤ q)
    (h2L : 2 ≤ L) (hm : L - 1 ≤ m) :
    ∃ table : Fin m → Fin L → Fin q,
      (¬ ∀ i, Function.Injective (table i)) ∧
      hit table + occ (q - 2) (L - 2) (m - 1) = hit (stdMenu (m := m) hLq) := by
  classical
  let k₀ : Fin m := ⟨0, by omega⟩
  let a₁ : Fin L := ⟨L - 2, by omega⟩
  let a₂ : Fin L := ⟨L - 1, by omega⟩
  let mergeCol : Fin L → Fin q := fun a =>
    if a.val = L - 1 then ⟨L - 2, by omega⟩ else ⟨a.val, by have := a.isLt; omega⟩
  let table : Fin m → Fin L → Fin q := Function.update (stdMenu hLq) k₀ mergeCol
  have hmerge12 : mergeCol a₁ = mergeCol a₂ := by
    have h1 : a₁.val ≠ L - 1 := by dsimp [a₁]; omega
    have h2 : a₂.val = L - 1 := rfl
    simp only [mergeCol, h1, h2, ↓reduceIte]
    rfl
  refine ⟨table, ?_, ?_⟩
  · intro hinj
    have h0 := hinj k₀
    have heq : table k₀ a₁ = table k₀ a₂ := by
      simp only [table, Function.update_self, hmerge12]
    have hne : a₁ ≠ a₂ := by intro h; have := congrArg Fin.val h; dsimp [a₁, a₂] at this; omega
    exact hne (h0 heq)
  · have hrep := hit_update_eq hq table k₀ (stdCol hLq) (stdCol_injective hLq)
    have hupd_eq : Function.update table k₀ (stdCol hLq) = stdMenu hLq := by
      funext i
      by_cases hik : i = k₀
      · subst hik; simp [table, stdMenu]
      · simp [table, hik]
    rw [hupd_eq] at hrep
    have htk : table k₀ = mergeCol := Function.update_self k₀ mergeCol (stdMenu hLq)
    rw [htk] at hrep
    have hfilt :
        ((Finset.univ : Finset (Fin (m - 1) → Fin q)).filter (fun y =>
          isBad mergeCol (surv table k₀ y))).card =
        occ (q - 2) (L - 2) (m - 1) := by
      have hlt : a₁.val < a₂.val := by dsimp [a₁, a₂]; omega
      rw [← card_surv_pair_eq_occ hLq a₁ a₂ hlt]
      apply congrArg Finset.card
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hmem : ∀ a : Fin L,
          a ∈ surv table k₀ y ↔ ∀ j : Fin (m - 1), (y j).val ≠ a.val := by
        intro a
        simp only [surv, Finset.mem_filter, Finset.mem_univ, true_and]
        refine forall_congr' fun j => ?_
        simp only [table, Function.update_of_ne (skipIdx_ne k₀ j), stdMenu, stdCol, ne_eq,
          Fin.ext_iff]
      have hmerge_val : ∀ x : Fin L, (mergeCol x).val = if x.val = L - 1 then L - 2 else x.val :=
        fun x => by dsimp [mergeCol]; split_ifs <;> rfl
      constructor
      · rintro ⟨u, hu, v, hv, huv, hall⟩
        have hcol_uv : mergeCol v = mergeCol u := hall v hv
        have huv_pair : (u = a₁ ∧ v = a₂) ∨ (u = a₂ ∧ v = a₁) := by
          have hv1 := congrArg Fin.val hcol_uv
          rw [hmerge_val v, hmerge_val u] at hv1
          have huv_val : u.val ≠ v.val := fun h => huv (Fin.ext h)
          have hu_lt := u.isLt
          have hv_lt := v.isLt
          split_ifs at hv1 with h1 h2 h3
          · omega
          · left; exact ⟨Fin.ext (by dsimp [a₁]; omega), Fin.ext (by dsimp [a₂]; omega)⟩
          · right; exact ⟨Fin.ext (by dsimp [a₂]; omega), Fin.ext (by dsimp [a₁]; omega)⟩
          · omega
        have hmu : (mergeCol u).val = L - 2 := by
          rw [hmerge_val u]
          rcases huv_pair with ⟨rfl, _⟩ | ⟨rfl, _⟩
          · dsimp [a₁]; split_ifs <;> omega
          · dsimp [a₂]; split_ifs <;> omega
        have ha1_mem : a₁ ∈ surv table k₀ y := by
          rcases huv_pair with ⟨rfl, _⟩ | ⟨_, rfl⟩ <;> assumption
        have ha2_mem : a₂ ∈ surv table k₀ y := by
          rcases huv_pair with ⟨_, rfl⟩ | ⟨rfl, _⟩ <;> assumption
        intro a
        rw [← hmem a]
        constructor
        · intro ha
          have hma := congrArg Fin.val (hall a ha)
          rw [hmerge_val a, hmu] at hma
          split_ifs at hma with h1
          · exact Or.inr (Fin.ext (by dsimp [a₂]; omega))
          · exact Or.inl (Fin.ext (by dsimp [a₁]; omega))
        · rintro (rfl | rfl)
          · exact ha1_mem
          · exact ha2_mem
      · intro hy
        refine ⟨a₁, (hmem a₁).mpr ((hy a₁).mpr (Or.inl rfl)),
          a₂, (hmem a₂).mpr ((hy a₂).mpr (Or.inr rfl)),
          fun h => by have := congrArg Fin.val h; dsimp [a₁, a₂] at this; omega, ?_⟩
        intro x hx
        rcases (hy x).mp ((hmem x).mp hx) with rfl | rfl
        · rfl
        · exact hmerge12.symm
    rw [hfilt] at hrep
    exact hrep

private lemma main (q m L : Nat) (hq : 0 < q) (hLq : L ≤ q) :
    let best := q ^ m - occ q L m
    let Menu := Fin m → Fin L → Fin q
    let distinct := fun (table : Menu) => ∀ i, Function.Injective (table i)
    (∀ table : Menu, hit table ≤ best) ∧
    (∀ table : Menu, distinct table → hit table = best) ∧
    (∃ table : Menu, distinct table) ∧
    (3 ≤ q → 2 ≤ L → L - 1 ≤ m →
      let gap := occ (q - 2) (L - 2) (m - 1)
      0 < gap ∧
      (∀ table : Menu, ¬ distinct table → hit table + gap ≤ best) ∧
      ∃ table : Menu, ¬ distinct table ∧ hit table + gap = best) := by
  have hstd : hit (stdMenu (m := m) hLq) = q ^ m - occ q L m := hit_stdMenu hLq
  refine ⟨fun table => hstd ▸ hit_le_stdMenu hq hLq table,
    fun table hd => hstd ▸ hit_eq_stdMenu_of_distinct hq hLq table hd,
    ⟨stdMenu hLq, fun _ => stdCol_injective hLq⟩,
    fun h3q h2L hm => ⟨occ_gap_pos hLq h3q h2L hm,
      fun table hnd => hstd ▸ hit_add_gap_le hq hLq table hnd,
      by
        obtain ⟨table, hnd, heq⟩ := exists_attaining_gap hq hLq h2L hm
        exact ⟨table, hnd, hstd ▸ heq⟩⟩⟩

end PEqualNP.Outside.L_lib_627

theorem PEqualNP.Outside.L_lib_627 :
    ∀ (q m L : Nat), 0 < q → L ≤ q →
      let occ := fun (alphabet labels width : Nat) =>
        ((Finset.univ : Finset (Fin width → Fin alphabet)).filter (fun word =>
          ∀ a : Fin labels, ∃ i, (word i).val = a.val)).card
      let best := q^m - occ q L m
      let Menu := Fin m → Fin L → Fin q
      let hit := fun (menu : Menu) =>
        ((Finset.univ : Finset (Fin m → Fin q)).filter (fun input =>
          ∃ a, ∀ i, input i ≠ menu i a)).card
      let distinct := fun (table : Menu) => ∀ i, Function.Injective (table i)
      (∀ table : Menu, hit table ≤ best) ∧
      (∀ table : Menu, distinct table → hit table = best) ∧
      (∃ table : Menu, distinct table) ∧
      (3 ≤ q → 2 ≤ L → L-1 ≤ m →
        let gap := occ (q-2) (L-2) (m-1)
        0 < gap ∧
        (∀ table : Menu, ¬ distinct table → hit table + gap ≤ best) ∧
        ∃ table : Menu, ¬ distinct table ∧ hit table + gap = best) :=
  PEqualNP.Outside.L_lib_627.main
