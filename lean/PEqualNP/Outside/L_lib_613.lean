import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_613_aux

open PEqualNP.CircuitLowerBounds

private def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

private def z2b (z : ZMod 2) : Bool := decide (z ≠ 0)

private lemma zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

private lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;> decide

private lemma b2z_z2b (z : ZMod 2) : b2z (z2b z) = z := by
  rcases zmod2_eq_zero_or_one z with rfl | rfl <;> simp [b2z, z2b]

private lemma z2b_b2z (b : Bool) : z2b (b2z b) = b := by
  cases b <;> decide

private lemma b2z_xor (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by
  cases a <;> cases b <;> decide

private lemma b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by
  cases a <;> cases b <;> decide

private lemma b2z_not (a : Bool) : b2z (!a) = 1 + b2z a := by
  cases a <;> decide

private lemma zmod2_add_eq_zero_iff (a b : ZMod 2) : a + b = 0 ↔ a = b := by
  constructor
  · intro h
    calc a = a + (b + b) := by rw [zmod2_add_self, add_zero]
      _ = (a + b) + b := (add_assoc a b b).symm
      _ = b := by rw [h, zero_add]
  · rintro rfl
    exact zmod2_add_self a

private lemma z2b_eq_true_iff (z : ZMod 2) : z2b z = true ↔ z = 1 := by
  rcases zmod2_eq_zero_or_one z with rfl | rfl <;> simp [z2b]

private lemma z2b_eq_false_iff (z : ZMod 2) : z2b z = false ↔ z = 0 := by
  rcases zmod2_eq_zero_or_one z with rfl | rfl <;> simp [z2b]

private lemma b2z_eq_one_iff (b : Bool) : b2z b = 1 ↔ b = true := by
  cases b <;> decide

private lemma b2z_eq_zero_iff (b : Bool) : b2z b = 0 ↔ b = false := by
  cases b <;> decide

private def iterFin {α : Type*} : ∀ (m : ℕ), (Fin m → α → α) → α → α
  | 0, _, a => a
  | m + 1, f, a => f (Fin.last m) (iterFin m (fun i => f i.castSucc) a)

private def firstOk {n : ℕ} (ok : Fin n → Bool) (m : Fin n) : Bool :=
  ok m && !(((List.finRange n).filter (fun m' => decide (m'.val < m.val))).any ok)

private lemma firstOk_eq_true_iff {n : ℕ} (ok : Fin n → Bool) (m : Fin n) :
    firstOk ok m = true ↔ ok m = true ∧ ∀ m' : Fin n, m'.val < m.val → ok m' = false := by
  unfold firstOk
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false, List.mem_filter,
    List.mem_finRange, true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨hm, hprev⟩
    refine ⟨hm, fun m' hlt => ?_⟩
    cases h : ok m'
    · rfl
    · exact absurd h (hprev m' hlt)
  · rintro ⟨hm, hprev⟩
    refine ⟨hm, fun m' hlt => ?_⟩
    rw [hprev m' hlt]
    decide

private lemma firstOk_unique {n : ℕ} (ok : Fin n → Bool) {m1 m2 : Fin n}
    (h1 : firstOk ok m1 = true) (h2 : firstOk ok m2 = true) : m1 = m2 := by
  rw [firstOk_eq_true_iff] at h1 h2
  ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have := h2.2 m1 hlt
    rw [h1.1] at this
    exact Bool.noConfusion this
  · have := h1.2 m2 hgt
    rw [h2.1] at this
    exact Bool.noConfusion this

private lemma exists_firstOk {n : ℕ} (ok : Fin n → Bool) (hex : ∃ m : Fin n, ok m = true) :
    ∃ m : Fin n, firstOk ok m = true := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter (fun m => ok m = true)
  have hne : s.Nonempty := by
    rcases hex with ⟨m, hm⟩
    exact ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ m, hm⟩⟩
  let m0 := s.min' hne
  refine ⟨m0, (firstOk_eq_true_iff ok m0).mpr ⟨(Finset.mem_filter.mp (Finset.min'_mem s hne)).2, ?_⟩⟩
  intro m' hlt
  by_contra hne_f
  have ht : ok m' = true := by
    cases h : ok m'
    · exact absurd h hne_f
    · rfl
  have hmem : m' ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ m', ht⟩
  have hle : m0 ≤ m' := Finset.min'_le s m' hmem
  exact Nat.not_lt.mpr hle hlt

private lemma firstOk_all_false {n : ℕ} (ok : Fin n → Bool) (h : ∀ m : Fin n, ok m = false)
    (m : Fin n) : firstOk ok m = false := by
  unfold firstOk
  simp [h m]

private def IsCleanBasis {n : ℕ} (T : Fin n → Fin n → ZMod 2) : Prop :=
  (∀ c : Fin n, T c c = 0 → ∀ j : Fin n, T c j = 0) ∧
  (∀ r c : Fin n, T c c = 1 → r ≠ c → T r c = 0)

private def rowSpan {n : ℕ} (T : Fin n → Fin n → ZMod 2) : Submodule (ZMod 2) (Fin n → ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range T)

private def zeroMat (n : ℕ) : Fin n → Fin n → ZMod 2 := fun _ _ => 0

private lemma isCleanBasis_zeroMat (n : ℕ) : IsCleanBasis (zeroMat n) := by
  refine ⟨fun _ _ _ => rfl, fun _ _ h _ => by simp [zeroMat] at h⟩

private lemma rowSpan_zeroMat (n : ℕ) : rowSpan (zeroMat n) = ⊥ := by
  unfold rowSpan zeroMat
  rw [Submodule.span_eq_bot]
  rintro x ⟨r, rfl⟩
  rfl

private def reduceVec {n : ℕ} (T : Fin n → Fin n → ZMod 2) (w : Fin n → ZMod 2) : Fin n → ZMod 2 :=
  fun j => w j + ∑ c : Fin n, w c * T c j

private def insertRow {n : ℕ} (T : Fin n → Fin n → ZMod 2) (w : Fin n → ZMod 2) :
    Fin n → Fin n → ZMod 2 :=
  let w' := reduceVec T w
  let piv := firstOk (fun c => z2b (w' c))
  let hit := fun r => ∑ p : Fin n, b2z (piv p) * T r p
  fun r j => if piv r then w' j else T r j + hit r * w' j

private lemma reduceVec_at_pivot {n : ℕ} {T : Fin n → Fin n → ZMod 2} (hT : IsCleanBasis T)
    (w : Fin n → ZMod 2) {c : Fin n} (hc : T c c = 1) :
    reduceVec T w c = 0 := by
  unfold reduceVec
  rw [Finset.sum_eq_single c]
  · rw [hc, mul_one, zmod2_add_self]
  · intro r _ hne
    rw [hT.2 r c hc hne, mul_zero]
  · intro hnot
    exact absurd (Finset.mem_univ c) hnot

private lemma isCleanBasis_insertRow {n : ℕ} {T : Fin n → Fin n → ZMod 2} (hT : IsCleanBasis T)
    (w : Fin n → ZMod 2) : IsCleanBasis (insertRow T w) := by
  set w' := reduceVec T w
  set piv := firstOk (fun c => z2b (w' c))
  by_cases hex : ∃ c : Fin n, z2b (w' c) = true
  · rcases exists_firstOk (fun c => z2b (w' c)) hex with ⟨p, hp0⟩
    have hp : piv p = true := hp0
    have hwp1 : w' p = 1 := (z2b_eq_true_iff _).mp ((firstOk_eq_true_iff _ _).mp hp0).1
    have hTpp0 : T p p = 0 := by
      rcases zmod2_eq_zero_or_one (T p p) with h0 | h1
      · exact h0
      · have hw'p : w' p = 0 := reduceVec_at_pivot hT w h1
        rw [hw'p] at hwp1
        exact absurd hwp1 (by decide)
    have hpiv_iff : ∀ r, piv r = true ↔ r = p := fun r =>
      ⟨fun hr => firstOk_unique _ hr hp0, fun hr => hr ▸ hp⟩
    have hhit : ∀ r, (∑ q : Fin n, b2z (piv q) * T r q) = T r p := by
      intro r
      rw [Finset.sum_eq_single p]
      · simp [hp, b2z]
      · intro q _ hne
        have hqf : piv q = false := by
          cases hq : piv q
          · rfl
          · exact absurd ((hpiv_iff q).mp hq) hne
        simp [hqf, b2z]
      · intro hnot
        exact absurd (Finset.mem_univ p) hnot
    have hval : ∀ r j, insertRow T w r j = if r = p then w' j else T r j + T r p * w' j := by
      intro r j
      unfold insertRow
      dsimp only
      change (if piv r then w' j else T r j + (∑ q : Fin n, b2z (piv q) * T r q) * w' j) = _
      rw [hhit r]
      by_cases hrp : r = p
      · subst hrp; simp [hp]
      · have hrf : piv r = false := by
          cases hr : piv r
          · rfl
          · exact absurd ((hpiv_iff r).mp hr) hrp
        simp [hrp, hrf]
    refine ⟨?_, ?_⟩
    · intro r hr0 j
      rw [hval r r] at hr0
      rw [hval r j]
      by_cases hrp : r = p
      · subst hrp
        simp only [↓reduceIte] at hr0
        rw [hwp1] at hr0
        exact absurd hr0 (by decide)
      · simp only [hrp, ↓reduceIte] at hr0 ⊢
        rcases zmod2_eq_zero_or_one (T r r) with h0 | h1
        · rw [hT.1 r h0 j, hT.1 r h0 p, zero_mul, add_zero]
        · have hw'r : w' r = 0 := reduceVec_at_pivot hT w h1
          rw [hw'r, mul_zero, add_zero, h1] at hr0
          exact absurd hr0 (by decide)
    · intro r c hc1 hrc
      rw [hval c c] at hc1
      rw [hval r c]
      by_cases hcp : c = p
      · subst hcp
        have hrp : r ≠ c := hrc
        simp only [hrp, ↓reduceIte, hwp1, mul_one, zmod2_add_self]
      · simp only [hcp, ↓reduceIte] at hc1
        have hTcc1 : T c c = 1 := by
          rcases zmod2_eq_zero_or_one (T c c) with h0 | h1
          · rw [h0, hT.1 c h0 p, zero_mul, add_zero] at hc1
            exact absurd hc1 (by decide)
          · exact h1
        have hwc0 : w' c = 0 := reduceVec_at_pivot hT w hTcc1
        by_cases hrp : r = p
        · simp [hrp, hwc0]
        · simp [hrp, hwc0, hT.2 r c hTcc1 hrc]
  · have hw'0 : ∀ c, w' c = 0 := by
      intro c
      have hf : z2b (w' c) = false := by
        cases h : z2b (w' c)
        · rfl
        · exact absurd ⟨c, h⟩ hex
      exact (z2b_eq_false_iff _).mp hf
    have hpiv0 : ∀ c, piv c = false := firstOk_all_false _ (fun c => (z2b_eq_false_iff _).mpr (hw'0 c))
    have heq : insertRow T w = T := by
      funext r j
      unfold insertRow
      dsimp only
      change (if piv r then w' j else T r j + (∑ q : Fin n, b2z (piv q) * T r q) * w' j) = T r j
      simp [hpiv0 r, hw'0 j]
    rw [heq]
    exact hT

private lemma rowSpan_insertRow {n : ℕ} {T : Fin n → Fin n → ZMod 2} (hT : IsCleanBasis T)
    (w : Fin n → ZMod 2) :
    rowSpan (insertRow T w) = rowSpan T ⊔ Submodule.span (ZMod 2) {w} := by
  set w' := reduceVec T w
  set piv := firstOk (fun c => z2b (w' c))
  have hw'_mem : w' ∈ rowSpan T ⊔ Submodule.span (ZMod 2) {w} := by
    have hdecomp : w' = w + ∑ c : Fin n, w c • T c := by
      funext j
      simp [w', reduceVec, Finset.sum_apply, smul_eq_mul]
    rw [hdecomp]
    refine Submodule.add_mem _ (Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton w))) ?_
    refine Submodule.mem_sup_left (Submodule.sum_mem _ fun c _ => ?_)
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)
  have hw_from_w' : w = w' + ∑ c : Fin n, w c • T c := by
    funext j
    simp only [w', reduceVec, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [add_assoc, zmod2_add_self, add_zero]
  by_cases hex : ∃ c : Fin n, z2b (w' c) = true
  · rcases exists_firstOk (fun c => z2b (w' c)) hex with ⟨p, hp0⟩
    have hp : piv p = true := hp0
    have hwp1 : w' p = 1 := (z2b_eq_true_iff _).mp ((firstOk_eq_true_iff _ _).mp hp0).1
    have hTpp0 : T p p = 0 := by
      rcases zmod2_eq_zero_or_one (T p p) with h0 | h1
      · exact h0
      · have hw'p : w' p = 0 := reduceVec_at_pivot hT w h1
        rw [hw'p] at hwp1
        exact absurd hwp1 (by decide)
    have hTp0 : T p = 0 := funext (hT.1 p hTpp0)
    have hpiv_iff : ∀ r, piv r = true ↔ r = p := fun r =>
      ⟨fun hr => firstOk_unique _ hr hp0, fun hr => hr ▸ hp⟩
    have hhit : ∀ r, (∑ q : Fin n, b2z (piv q) * T r q) = T r p := by
      intro r
      rw [Finset.sum_eq_single p]
      · simp [hp, b2z]
      · intro q _ hne
        have hqf : piv q = false := by
          cases hq : piv q
          · rfl
          · exact absurd ((hpiv_iff q).mp hq) hne
        simp [hqf, b2z]
      · intro hnot
        exact absurd (Finset.mem_univ p) hnot
    have hrow : ∀ r, insertRow T w r = if r = p then w' else T r + T r p • w' := by
      intro r
      funext j
      unfold insertRow
      dsimp only
      change (if piv r then w' j else T r j + (∑ q : Fin n, b2z (piv q) * T r q) * w' j) = _
      rw [hhit r]
      by_cases hrp : r = p
      · subst hrp; simp [hp]
      · have hrf : piv r = false := by
          cases hr : piv r
          · rfl
          · exact absurd ((hpiv_iff r).mp hr) hrp
        simp [hrp, hrf, smul_eq_mul]
    apply le_antisymm
    · rw [rowSpan, Submodule.span_le]
      rintro v ⟨r, rfl⟩
      rw [hrow r]
      by_cases hrp : r = p
      · simp [hrp, hw'_mem]
      · simp only [hrp, ↓reduceIte]
        exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.subset_span ⟨r, rfl⟩))
          (Submodule.smul_mem _ _ hw'_mem)
    · have hw'_in : w' ∈ rowSpan (insertRow T w) := by
        have hp_eq : insertRow T w p = w' := by simp [hrow p]
        rw [← hp_eq]
        exact Submodule.subset_span ⟨p, rfl⟩
      have hT_le : rowSpan T ≤ rowSpan (insertRow T w) := by
        rw [rowSpan, Submodule.span_le]
        rintro v ⟨r, rfl⟩
        by_cases hrp : r = p
        · subst hrp; rw [hTp0]; exact Submodule.zero_mem _
        · have heq : T r = insertRow T w r + T r p • w' := by
            rw [hrow r]
            simp only [hrp, ↓reduceIte]
            funext j
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            rw [add_assoc, zmod2_add_self, add_zero]
          rw [heq]
          exact Submodule.add_mem _ (Submodule.subset_span ⟨r, rfl⟩) (Submodule.smul_mem _ _ hw'_in)
      refine sup_le hT_le ?_
      rw [Submodule.span_singleton_le_iff_mem]
      have hw_in : w' + ∑ c : Fin n, w c • T c ∈ rowSpan (insertRow T w) :=
        Submodule.add_mem _ hw'_in
          (Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hT_le (Submodule.subset_span ⟨c, rfl⟩)))
      rwa [← hw_from_w'] at hw_in
  · have hw'0 : w' = 0 := by
      funext c
      have hf : z2b (w' c) = false := by
        cases h : z2b (w' c)
        · rfl
        · exact absurd ⟨c, h⟩ hex
      exact (z2b_eq_false_iff _).mp hf
    have hpiv0 : ∀ c, piv c = false := firstOk_all_false _ (fun c => (z2b_eq_false_iff _).mpr (congrFun hw'0 c))
    have heq : insertRow T w = T := by
      funext r j
      unfold insertRow
      dsimp only
      change (if piv r then w' j else T r j + (∑ q : Fin n, b2z (piv q) * T r q) * w' j) = T r j
      simp [hpiv0 r, congrFun hw'0 j]
    rw [heq]
    have hw_in : w ∈ rowSpan T := by
      rw [hw_from_w', hw'0, zero_add]
      exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)
    exact (sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem w (rowSpan T)).mpr hw_in)).symm

private def insertMany {n : ℕ} (m : ℕ) (rows : Fin m → Fin n → ZMod 2)
    (T : Fin n → Fin n → ZMod 2) : Fin n → Fin n → ZMod 2 :=
  iterFin m (fun i acc => insertRow acc (rows i)) T

private lemma insertMany_succ {n m : ℕ} (rows : Fin (m + 1) → Fin n → ZMod 2)
    (T : Fin n → Fin n → ZMod 2) :
    insertMany (m + 1) rows T =
      insertRow (insertMany m (fun i => rows i.castSucc) T) (rows (Fin.last m)) := rfl

private lemma isCleanBasis_insertMany {n : ℕ} (m : ℕ) (rows : Fin m → Fin n → ZMod 2)
    {T : Fin n → Fin n → ZMod 2} (hT : IsCleanBasis T) :
    IsCleanBasis (insertMany m rows T) := by
  induction m with
  | zero => exact hT
  | succ m ih =>
    rw [insertMany_succ]
    exact isCleanBasis_insertRow (ih (fun i => rows i.castSucc)) (rows (Fin.last m))

private lemma rowSpan_insertMany {n : ℕ} (m : ℕ) (rows : Fin m → Fin n → ZMod 2)
    {T : Fin n → Fin n → ZMod 2} (hT : IsCleanBasis T) :
    rowSpan (insertMany m rows T) = rowSpan T ⊔ Submodule.span (ZMod 2) (Set.range rows) := by
  induction m with
  | zero =>
    unfold insertMany iterFin
    have hrange : Set.range rows = ∅ := Set.range_eq_empty_iff.mpr inferInstance
    rw [hrange, Submodule.span_empty, sup_bot_eq]
  | succ m ih =>
    rw [insertMany_succ]
    have hcl : IsCleanBasis (insertMany m (fun i => rows i.castSucc) T) :=
      isCleanBasis_insertMany m (fun i => rows i.castSucc) hT
    rw [rowSpan_insertRow hcl (rows (Fin.last m)), ih (fun i => rows i.castSucc), sup_assoc]
    congr 1
    rw [← Submodule.span_union]
    congr 1
    ext v
    simp only [Set.mem_union, Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro (⟨i, rfl⟩ | rfl)
      · exact ⟨i.castSucc, rfl⟩
      · exact ⟨Fin.last m, rfl⟩
    · rintro ⟨i, rfl⟩
      refine Fin.lastCases ?_ ?_ i
      · right; rfl
      · intro j; left; exact ⟨j, rfl⟩

private def rankClean {n : ℕ} (T : Fin n → Fin n → ZMod 2) : ℕ :=
  (Finset.univ.filter (fun c : Fin n => T c c = 1)).card

private lemma rankClean_eq_finrank {n : ℕ} {T : Fin n → Fin n → ZMod 2} (hT : IsCleanBasis T) :
    rankClean T = Module.finrank (ZMod 2) (rowSpan T) := by
  classical
  let P : Finset (Fin n) := Finset.univ.filter (fun c : Fin n => T c c = 1)
  have hspan : rowSpan T = Submodule.span (ZMod 2) (Set.range (fun c : P => T c.1)) := by
    apply le_antisymm
    · rw [rowSpan, Submodule.span_le]
      rintro v ⟨r, rfl⟩
      rcases zmod2_eq_zero_or_one (T r r) with h0 | h1
      · have hr0 : T r = 0 := funext (hT.1 r h0)
        rw [hr0]
        exact Submodule.zero_mem _
      · exact Submodule.subset_span ⟨⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ r, h1⟩⟩, rfl⟩
    · rw [Submodule.span_le]
      rintro v ⟨c, rfl⟩
      exact Submodule.subset_span ⟨c.1, rfl⟩
  have hli : LinearIndependent (ZMod 2) (fun c : P => T c.1) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg c
    have hc1 : T c.1 c.1 = 1 := (Finset.mem_filter.mp c.2).2
    have hval := congrFun hg c.1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hval
    rw [Finset.sum_eq_single c] at hval
    · simpa [hc1] using hval
    · intro r _ hne
      have hne' : r.1 ≠ c.1 := fun h => hne (Subtype.ext h)
      rw [hT.2 r.1 c.1 hc1 hne', mul_zero]
    · intro hnot
      exact absurd (Finset.mem_univ c) hnot
  rw [hspan, finrank_span_eq_card hli, Fintype.card_coe]
  rfl

private def kernelSub {n : ℕ} (T : Fin n → Fin n → ZMod 2) : Submodule (ZMod 2) (Fin n → ZMod 2) :=
  { carrier := {v | ∀ r : Fin n, ∑ j : Fin n, T r j * v j = 0}, add_mem' := by
      intro u v hu hv r
      simp only [Set.mem_ofPred_eq, Pi.add_apply] at hu hv ⊢
      calc ∑ j : Fin n, T r j * (u j + v j)
          = (∑ j : Fin n, T r j * u j) + ∑ j : Fin n, T r j * v j := by
              rw [← Finset.sum_add_distrib]
              exact Finset.sum_congr rfl (fun j _ => mul_add _ _ _)
        _ = 0 := by rw [hu r, hv r, add_zero]
    zero_mem' := by intro r; simp
    smul_mem' := by
      intro a v hv r
      simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul] at hv ⊢
      calc ∑ j : Fin n, T r j * (a * v j)
          = a * ∑ j : Fin n, T r j * v j := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun j _ => by ring)
        _ = 0 := by rw [hv r, mul_zero] }

private lemma mem_kernelSub_iff_orth_rowSpan {n : ℕ} (T : Fin n → Fin n → ZMod 2)
    (v : Fin n → ZMod 2) :
    v ∈ kernelSub T ↔ ∀ u ∈ rowSpan T, ∑ j : Fin n, u j * v j = 0 := by
  constructor
  · intro hv u hu
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨r, rfl⟩; exact hv r
    · simp
    · intro x y _ _ hx hy
      calc ∑ j : Fin n, (x + y) j * v j
          = (∑ j : Fin n, x j * v j) + ∑ j : Fin n, y j * v j := by
              rw [← Finset.sum_add_distrib]
              exact Finset.sum_congr rfl (fun j _ => add_mul _ _ _)
        _ = 0 := by rw [hx, hy, add_zero]
    · intro a x _ hx
      calc ∑ j : Fin n, (a • x) j * v j
          = a * ∑ j : Fin n, x j * v j := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun j _ => by simp [mul_assoc])
        _ = 0 := by rw [hx, mul_zero]
  · intro h r
    exact h (T r) (Submodule.subset_span ⟨r, rfl⟩)

private def kernelBasis {n : ℕ} (T : Fin n → Fin n → ZMod 2) : Fin n → Fin n → ZMod 2 :=
  fun k j => if j = k then b2z (!(z2b (T k k))) else b2z (!(z2b (T k k))) * T j k

private lemma kernelBasis_mem {n : ℕ} {T : Fin n → Fin n → ZMod 2} (hT : IsCleanBasis T)
    (k : Fin n) : kernelBasis T k ∈ kernelSub T := by
  intro r
  rcases zmod2_eq_zero_or_one (T k k) with hk0 | hk1
  · have hfk : b2z (!(z2b (T k k))) = 1 := by rw [hk0]; decide
    rcases zmod2_eq_zero_or_one (T r r) with hr0 | hr1
    · refine Finset.sum_eq_zero fun j _ => ?_
      rw [hT.1 r hr0 j, zero_mul]
    · have hrk : r ≠ k := by
        intro heq; subst heq; rw [hk0] at hr1; exact absurd hr1 (by decide)
      have hterm : ∀ j : Fin n, T r j * kernelBasis T k j =
          if j = k then T r k else if j = r then T r k else 0 := by
        intro j
        unfold kernelBasis
        rw [hfk, one_mul]
        by_cases hjk : j = k
        · subst hjk; simp [mul_one]
        · simp only [hjk, ↓reduceIte]
          by_cases hjr : j = r
          · subst hjr; simp [hr1]
          · simp only [hjr, ↓reduceIte]
            rcases zmod2_eq_zero_or_one (T j j) with hj0 | hj1
            · rw [hT.1 j hj0 k, mul_zero]
            · rw [hT.2 r j hj1 (Ne.symm hjr), zero_mul]
      rw [Finset.sum_congr rfl (fun j _ => hterm j)]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
      simp only [↓reduceIte]
      have hrest : (∑ j ∈ Finset.univ.erase k, if j = k then T r k else if j = r then T r k else 0) = T r k := by
        have heq : (∑ j ∈ Finset.univ.erase k, if j = k then T r k else if j = r then T r k else 0) =
            ∑ j ∈ Finset.univ.erase k, if j = r then T r k else 0 := by
          refine Finset.sum_congr rfl fun j hj => ?_
          simp [(Finset.mem_erase.mp hj).1]
        rw [heq, Finset.sum_ite_eq' (Finset.univ.erase k) r]
        simp [hrk]
      rw [hrest, zmod2_add_self]
  · have hfk : b2z (!(z2b (T k k))) = 0 := by rw [hk1]; decide
    refine Finset.sum_eq_zero fun j _ => ?_
    unfold kernelBasis
    rw [hfk]
    split_ifs <;> simp

private lemma span_kernelBasis_eq {n : ℕ} {T : Fin n → Fin n → ZMod 2} (hT : IsCleanBasis T) :
    Submodule.span (ZMod 2) (Set.range (kernelBasis T)) = kernelSub T := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro v ⟨k, rfl⟩
    exact kernelBasis_mem hT k
  · intro v hv
    have hdecomp : v = ∑ k : Fin n, v k • kernelBasis T k := by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rcases zmod2_eq_zero_or_one (T j j) with hj0 | hj1
      · rw [Finset.sum_eq_single j]
        · unfold kernelBasis
          simp [hj0, z2b, b2z]
        · intro k _ hne
          unfold kernelBasis
          simp [Ne.symm hne, hT.1 j hj0 k]
        · intro hnot
          exact absurd (Finset.mem_univ j) hnot
      · have hvj : ∑ k : Fin n, T j k * v k = 0 := hv j
        have hsum : (∑ k : Fin n, v k * kernelBasis T k j) =
            ∑ k : Fin n, (if k = j then 0 else T j k * v k) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          unfold kernelBasis
          by_cases hkj : k = j
          · subst hkj
            simp [hj1, z2b, b2z]
          · simp only [Ne.symm hkj, ↓reduceIte, hkj]
            rcases zmod2_eq_zero_or_one (T k k) with hk0 | hk1
            · have hfk : b2z (!(z2b (T k k))) = 1 := by rw [hk0]; decide
              rw [hfk, one_mul, mul_comm]
            · have hfk : b2z (!(z2b (T k k))) = 0 := by rw [hk1]; decide
              rw [hfk, zero_mul, mul_zero, hT.2 j k hk1 (Ne.symm hkj), zero_mul]
        rw [hsum]
        have hsplit : (∑ k : Fin n, T j k * v k) =
            T j j * v j + ∑ k : Fin n, (if k = j then 0 else T j k * v k) := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
          congr 1
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
          simp only [↓reduceIte, zero_add]
          refine Finset.sum_congr rfl fun k hk => ?_
          simp [(Finset.mem_erase.mp hk).1]
        rw [hsplit, hj1, one_mul] at hvj
        exact (zmod2_add_eq_zero_iff _ _).mp hvj
    rw [hdecomp]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

private def quadEval {n : ℕ} (lrow : Fin n → ZMod 2) (amat : Matrix (Fin n) (Fin n) (ZMod 2))
    (x : Fin n → ZMod 2) : ZMod 2 :=
  (∑ i : Fin n, lrow i * x i) + ∑ i : Fin n, ∑ b : Fin n, amat i b * x i * x b

private def symRow {n : ℕ} (amat : Matrix (Fin n) (Fin n) (ZMod 2)) (b : Fin n) :
    Fin n → ZMod 2 :=
  fun i => amat i b + amat b i

private lemma quadEval_zero {n : ℕ} (lrow : Fin n → ZMod 2)
    (amat : Matrix (Fin n) (Fin n) (ZMod 2)) : quadEval lrow amat 0 = 0 := by
  simp [quadEval]

private lemma quadEval_add {n : ℕ} (lrow : Fin n → ZMod 2)
    (amat : Matrix (Fin n) (Fin n) (ZMod 2)) (x v : Fin n → ZMod 2) :
    quadEval lrow amat (x + v) =
      quadEval lrow amat x + quadEval lrow amat v +
        ∑ b : Fin n, x b * (∑ i : Fin n, symRow amat b i * v i) := by
  unfold quadEval symRow
  have hlin : (∑ i : Fin n, lrow i * (x + v) i) =
      (∑ i : Fin n, lrow i * x i) + ∑ i : Fin n, lrow i * v i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => mul_add _ _ _
  have hquad : (∑ i : Fin n, ∑ b : Fin n, amat i b * (x + v) i * (x + v) b) =
      (∑ i : Fin n, ∑ b : Fin n, amat i b * x i * x b) +
      (∑ i : Fin n, ∑ b : Fin n, amat i b * v i * v b) +
      (∑ i : Fin n, ∑ b : Fin n, amat i b * x i * v b) +
      (∑ i : Fin n, ∑ b : Fin n, amat i b * v i * x b) := by
    have hstep : ∀ i : Fin n, (∑ b : Fin n, amat i b * (x i + v i) * (x b + v b)) =
        (∑ b : Fin n, amat i b * x i * x b) + (∑ b : Fin n, amat i b * v i * v b) +
        (∑ b : Fin n, amat i b * x i * v b) + (∑ b : Fin n, amat i b * v i * x b) := by
      intro i
      simp only [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => by ring
    simp only [Pi.add_apply, hstep, Finset.sum_add_distrib]
  have hcross1 : (∑ i : Fin n, ∑ b : Fin n, amat i b * x i * v b) =
      ∑ b : Fin n, ∑ i : Fin n, amat b i * x b * v i := by
    rw [Finset.sum_comm]
  have hcross2 : (∑ i : Fin n, ∑ b : Fin n, amat i b * v i * x b) =
      ∑ b : Fin n, ∑ i : Fin n, amat i b * x b * v i := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => by ring
  have hcross : (∑ i : Fin n, ∑ b : Fin n, amat i b * x i * v b) +
      (∑ i : Fin n, ∑ b : Fin n, amat i b * v i * x b) =
      ∑ b : Fin n, x b * (∑ i : Fin n, (amat i b + amat b i) * v i) := by
    rw [hcross1, hcross2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [hlin, hquad]
  have hr : ∀ A B C D E F : ZMod 2, (A + B) + (C + D + E + F) = (A + C) + (B + D) + (E + F) := by
    intros; ring
  rw [hr, hcross]

private lemma quadEval_period_iff {n : ℕ} (lrow : Fin n → ZMod 2)
    (amat : Matrix (Fin n) (Fin n) (ZMod 2)) (v : Fin n → ZMod 2) :
    (∀ x : Fin n → ZMod 2, quadEval lrow amat (x + v) = quadEval lrow amat x) ↔
      quadEval lrow amat v = 0 ∧ ∀ b : Fin n, ∑ i : Fin n, symRow amat b i * v i = 0 := by
  constructor
  · intro h
    have hv0 : quadEval lrow amat v = 0 := by
      have h0 := h 0
      rw [zero_add, quadEval_zero] at h0
      exact h0
    refine ⟨hv0, fun b => ?_⟩
    have hb := h (Pi.single b 1)
    rw [quadEval_add, hv0, add_zero] at hb
    have hsum : (∑ c : Fin n, (Pi.single b (1 : ZMod 2) : Fin n → ZMod 2) c *
        (∑ i : Fin n, symRow amat c i * v i)) = ∑ i : Fin n, symRow amat b i * v i := by
      rw [Finset.sum_eq_single b]
      · simp
      · intro c _ hne; simp [Pi.single_eq_of_ne hne]
      · intro hnot; exact absurd (Finset.mem_univ b) hnot
    rw [hsum] at hb
    have := (zmod2_add_eq_zero_iff _ _).mpr hb
    have hcancel : quadEval lrow amat (Pi.single b 1) +
        (quadEval lrow amat (Pi.single b 1) + ∑ i : Fin n, symRow amat b i * v i) =
        ∑ i : Fin n, symRow amat b i * v i := by
      rw [← add_assoc, zmod2_add_self, zero_add]
    rw [add_comm, hcancel] at this
    exact this
  · rintro ⟨hv0, hrad⟩ x
    rw [quadEval_add, hv0, add_zero]
    have h0 : (∑ b : Fin n, x b * ∑ i : Fin n, symRow amat b i * v i) = 0 :=
      Finset.sum_eq_zero fun b _ => by rw [hrad b, mul_zero]
    rw [h0, add_zero]

private def radicalSub {n t : ℕ} (owner : Fin t → Fin 3)
    (a : Fin t → Matrix (Fin n) (Fin n) (ZMod 2)) (g : Fin 3) :
    Submodule (ZMod 2) (Fin n → ZMod 2) :=
  { carrier := {v | ∀ j : Fin t, owner j = g → ∀ b : Fin n, ∑ i : Fin n, symRow (a j) b i * v i = 0}, add_mem' := by
      intro u v hu hv j hj b
      simp only [Set.mem_ofPred_eq, Pi.add_apply] at hu hv ⊢
      calc ∑ i : Fin n, symRow (a j) b i * (u i + v i)
          = (∑ i : Fin n, symRow (a j) b i * u i) + ∑ i : Fin n, symRow (a j) b i * v i := by
              rw [← Finset.sum_add_distrib]
              exact Finset.sum_congr rfl fun i _ => mul_add _ _ _
        _ = 0 := by rw [hu j hj b, hv j hj b, add_zero]
    zero_mem' := by intro j _ b; simp
    smul_mem' := by
      intro c v hv j hj b
      simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul] at hv ⊢
      calc ∑ i : Fin n, symRow (a j) b i * (c * v i)
          = c * ∑ i : Fin n, symRow (a j) b i * v i := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun i _ => by ring
        _ = 0 := by rw [hv j hj b, mul_zero] }

private lemma quadEval_add_on_radical {n t : ℕ} (owner : Fin t → Fin 3)
    (l : Fin t → Fin n → ZMod 2) (a : Fin t → Matrix (Fin n) (Fin n) (ZMod 2))
    {g : Fin 3} {u v : Fin n → ZMod 2}
    (hv : v ∈ radicalSub owner a g) {j : Fin t} (hj : owner j = g) :
    quadEval (l j) (a j) (u + v) = quadEval (l j) (a j) u + quadEval (l j) (a j) v := by
  rw [quadEval_add]
  have h0 : (∑ b : Fin n, u b * ∑ i : Fin n, symRow (a j) b i * v i) = 0 :=
    Finset.sum_eq_zero fun b _ => by rw [hv j hj b, mul_zero]
  rw [h0, add_zero]

private lemma quadEval_smul {n : ℕ} (lrow : Fin n → ZMod 2)
    (amat : Matrix (Fin n) (Fin n) (ZMod 2)) (c : ZMod 2) (v : Fin n → ZMod 2) :
    quadEval lrow amat (c • v) = c * quadEval lrow amat v := by
  rcases zmod2_eq_zero_or_one c with rfl | rfl
  · simp [quadEval_zero]
  · simp

private lemma quadEval_sum_on_radical {n t m : ℕ} (owner : Fin t → Fin 3)
    (l : Fin t → Fin n → ZMod 2) (a : Fin t → Matrix (Fin n) (Fin n) (ZMod 2))
    {g : Fin 3} (E : Fin m → Fin n → ZMod 2) (hE : ∀ k, E k ∈ radicalSub owner a g)
    (c : Fin m → ZMod 2) {j : Fin t} (hj : owner j = g) :
    quadEval (l j) (a j) (∑ k : Fin m, c k • E k) =
      ∑ k : Fin m, c k * quadEval (l j) (a j) (E k) := by
  classical
  have hfin : ∀ s : Finset (Fin m),
      quadEval (l j) (a j) (∑ k ∈ s, c k • E k) =
        ∑ k ∈ s, c k * quadEval (l j) (a j) (E k) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [quadEval_zero]
    | @insert a0 s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have hmem : (∑ k ∈ s, c k • E k) ∈ radicalSub owner a g :=
        Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hE k)
      rw [quadEval_add_on_radical owner l a hmem hj, quadEval_smul, ih]
  exact hfin Finset.univ

private def periodSub {n t : ℕ} (owner : Fin t → Fin 3)
    (l : Fin t → Fin n → ZMod 2) (a : Fin t → Matrix (Fin n) (Fin n) (ZMod 2)) (g : Fin 3) :
    Submodule (ZMod 2) (Fin n → ZMod 2) :=
  { carrier := {v | v ∈ radicalSub owner a g ∧ ∀ j : Fin t, owner j = g → quadEval (l j) (a j) v = 0}, add_mem' := by
      intro u v hu hv
      refine ⟨Submodule.add_mem _ hu.1 hv.1, fun j hj => ?_⟩
      rw [quadEval_add_on_radical owner l a hv.1 hj, hu.2 j hj, hv.2 j hj, add_zero]
    zero_mem' := ⟨Submodule.zero_mem _, fun _ _ => quadEval_zero _ _⟩
    smul_mem' := by
      intro c v hv
      refine ⟨Submodule.smul_mem _ c hv.1, fun j hj => ?_⟩
      rw [quadEval_smul, hv.2 j hj, mul_zero] }

private lemma mem_periodSub_iff {n t : ℕ} (owner : Fin t → Fin 3)
    (l : Fin t → Fin n → ZMod 2) (a : Fin t → Matrix (Fin n) (Fin n) (ZMod 2))
    (g : Fin 3) (v : Fin n → ZMod 2) :
    v ∈ periodSub owner l a g ↔
      ∀ (j : Fin t), owner j = g → ∀ x : Fin n → ZMod 2,
        quadEval (l j) (a j) (x + v) = quadEval (l j) (a j) x := by
  constructor
  · intro hv j hj x
    exact (quadEval_period_iff (l j) (a j) v).mpr ⟨hv.2 j hj, hv.1 j hj⟩ x
  · intro h
    refine ⟨fun j hj => ((quadEval_period_iff (l j) (a j) v).mp (h j hj)).2,
            fun j hj => ((quadEval_period_iff (l j) (a j) v).mp (h j hj)).1⟩

private def radicalTable {n t : ℕ} (owner : Fin t → Fin 3)
    (a : Fin t → Matrix (Fin n) (Fin n) (ZMod 2)) (g : Fin 3) : Fin n → Fin n → ZMod 2 :=
  iterFin t (fun j acc => if owner j == g then insertMany n (symRow (a j)) acc else acc) (zeroMat n)

private lemma radicalTable_succ {n t : ℕ} (owner : Fin (t + 1) → Fin 3)
    (a : Fin (t + 1) → Matrix (Fin n) (Fin n) (ZMod 2)) (g : Fin 3) :
    radicalTable owner a g =
      if owner (Fin.last t) == g then
        insertMany n (symRow (a (Fin.last t)))
          (radicalTable (fun j => owner j.castSucc) (fun j => a j.castSucc) g)
      else radicalTable (fun j => owner j.castSucc) (fun j => a j.castSucc) g := rfl

private lemma isCleanBasis_radicalTable {n t : ℕ} (owner : Fin t → Fin 3)
    (a : Fin t → Matrix (Fin n) (Fin n) (ZMod 2)) (g : Fin 3) :
    IsCleanBasis (radicalTable owner a g) := by
  induction t with
  | zero => exact isCleanBasis_zeroMat n
  | succ t ih =>
    rw [radicalTable_succ]
    have hprev := ih (fun j => owner j.castSucc) (fun j => a j.castSucc)
    split_ifs
    · exact isCleanBasis_insertMany n (symRow (a (Fin.last t))) hprev
    · exact hprev

private lemma kernelSub_radicalTable {n t : ℕ} (owner : Fin t → Fin 3)
    (a : Fin t → Matrix (Fin n) (Fin n) (ZMod 2)) (g : Fin 3) :
    kernelSub (radicalTable owner a g) = radicalSub owner a g := by
  have hspan : ∀ (m : ℕ) (ow : Fin m → Fin 3) (am : Fin m → Matrix (Fin n) (Fin n) (ZMod 2)),
      rowSpan (radicalTable ow am g) =
        Submodule.span (ZMod 2) {u | ∃ (j : Fin m) (b : Fin n), ow j = g ∧ symRow (am j) b = u} := by
    intro m
    induction m with
    | zero =>
      intro ow am
      unfold radicalTable iterFin
      rw [rowSpan_zeroMat]
      symm
      rw [Submodule.span_eq_bot]
      rintro u ⟨j, _⟩
      exact j.elim0
    | succ m ih =>
      intro ow am
      rw [radicalTable_succ]
      have hcl := isCleanBasis_radicalTable (fun j => ow j.castSucc) (fun j => am j.castSucc) g
      have hih := ih (fun j => ow j.castSucc) (fun j => am j.castSucc)
      by_cases hlast : ow (Fin.last m) = g
      · have hbeq : (ow (Fin.last m) == g) = true := beq_iff_eq.mpr hlast
        simp only [hbeq, ↓reduceIte]
        rw [rowSpan_insertMany n (symRow (am (Fin.last m))) hcl, hih, ← Submodule.span_union]
        congr 1
        ext u
        simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_range]
        constructor
        · rintro (⟨j, b, hj, rfl⟩ | ⟨b, rfl⟩)
          · exact ⟨j.castSucc, b, hj, rfl⟩
          · exact ⟨Fin.last m, b, hlast, rfl⟩
        · rintro ⟨j, b, hj, rfl⟩
          refine Fin.lastCases ?_ ?_ j hj
          · intro _; right; exact ⟨b, rfl⟩
          · intro j' hj'; left; exact ⟨j', b, hj', rfl⟩
      · have hbeq : (ow (Fin.last m) == g) = false := beq_false_of_ne hlast
        simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
        rw [hih]
        congr 1
        ext u
        simp only [Set.mem_ofPred_eq]
        constructor
        · rintro ⟨j, b, hj, rfl⟩
          exact ⟨j.castSucc, b, hj, rfl⟩
        · rintro ⟨j, b, hj, rfl⟩
          refine Fin.lastCases ?_ ?_ j hj
          · intro hl; exact absurd hl hlast
          · intro j' hj'; exact ⟨j', b, hj', rfl⟩
  ext v
  rw [mem_kernelSub_iff_orth_rowSpan, hspan t owner a]
  constructor
  · intro h j hj b
    exact h (symRow (a j) b) (Submodule.subset_span ⟨j, b, hj, rfl⟩)
  · intro hv u hu
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨j, b, hj, rfl⟩; exact hv j hj b
    · simp
    · intro x y _ _ hx hy
      calc ∑ i : Fin n, (x + y) i * v i
          = (∑ i : Fin n, x i * v i) + ∑ i : Fin n, y i * v i := by
              rw [← Finset.sum_add_distrib]
              exact Finset.sum_congr rfl fun i _ => add_mul _ _ _
        _ = 0 := by rw [hx, hy, add_zero]
    · intro c x _ hx
      calc ∑ i : Fin n, (c • x) i * v i
          = c * ∑ i : Fin n, x i * v i := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun i _ => by simp [mul_assoc]
        _ = 0 := by rw [hx, mul_zero]

private def evalTable {n t : ℕ} (owner : Fin t → Fin 3)
    (l : Fin t → Fin n → ZMod 2) (a : Fin t → Matrix (Fin n) (Fin n) (ZMod 2))
    (g : Fin 3) (E : Fin n → Fin n → ZMod 2) : Fin n → Fin n → ZMod 2 :=
  iterFin t (fun j acc =>
    if owner j == g then insertRow acc (fun k => quadEval (l j) (a j) (E k)) else acc) (zeroMat n)

private lemma evalTable_succ {n t : ℕ} (owner : Fin (t + 1) → Fin 3)
    (l : Fin (t + 1) → Fin n → ZMod 2) (a : Fin (t + 1) → Matrix (Fin n) (Fin n) (ZMod 2))
    (g : Fin 3) (E : Fin n → Fin n → ZMod 2) :
    evalTable owner l a g E =
      if owner (Fin.last t) == g then
        insertRow (evalTable (fun j => owner j.castSucc) (fun j => l j.castSucc)
          (fun j => a j.castSucc) g E) (fun k => quadEval (l (Fin.last t)) (a (Fin.last t)) (E k))
      else evalTable (fun j => owner j.castSucc) (fun j => l j.castSucc)
        (fun j => a j.castSucc) g E := rfl

private lemma isCleanBasis_evalTable {n t : ℕ} (owner : Fin t → Fin 3)
    (l : Fin t → Fin n → ZMod 2) (a : Fin t → Matrix (Fin n) (Fin n) (ZMod 2))
    (g : Fin 3) (E : Fin n → Fin n → ZMod 2) :
    IsCleanBasis (evalTable owner l a g E) := by
  induction t with
  | zero => exact isCleanBasis_zeroMat n
  | succ t ih =>
    rw [evalTable_succ]
    have hprev := ih (fun j => owner j.castSucc) (fun j => l j.castSucc) (fun j => a j.castSucc)
    split_ifs
    · exact isCleanBasis_insertRow hprev _
    · exact hprev

private lemma mem_kernelSub_evalTable_iff {n t : ℕ} (owner : Fin t → Fin 3)
    (l : Fin t → Fin n → ZMod 2) (a : Fin t → Matrix (Fin n) (Fin n) (ZMod 2))
    (g : Fin 3) (E : Fin n → Fin n → ZMod 2) (c : Fin n → ZMod 2) :
    c ∈ kernelSub (evalTable owner l a g E) ↔
      ∀ j : Fin t, owner j = g → ∑ k : Fin n, quadEval (l j) (a j) (E k) * c k = 0 := by
  have hspan : ∀ (m : ℕ) (ow : Fin m → Fin 3) (lm : Fin m → Fin n → ZMod 2)
      (am : Fin m → Matrix (Fin n) (Fin n) (ZMod 2)),
      rowSpan (evalTable ow lm am g E) =
        Submodule.span (ZMod 2) {u | ∃ j : Fin m, ow j = g ∧ (fun k => quadEval (lm j) (am j) (E k)) = u} := by
    intro m
    induction m with
    | zero =>
      intro ow lm am
      unfold evalTable iterFin
      rw [rowSpan_zeroMat]
      symm
      rw [Submodule.span_eq_bot]
      rintro u ⟨j, _⟩
      exact j.elim0
    | succ m ih =>
      intro ow lm am
      rw [evalTable_succ]
      have hcl := isCleanBasis_evalTable (fun j => ow j.castSucc) (fun j => lm j.castSucc)
        (fun j => am j.castSucc) g E
      have hih := ih (fun j => ow j.castSucc) (fun j => lm j.castSucc) (fun j => am j.castSucc)
      by_cases hlast : ow (Fin.last m) = g
      · have hbeq : (ow (Fin.last m) == g) = true := beq_iff_eq.mpr hlast
        simp only [hbeq, ↓reduceIte]
        rw [rowSpan_insertRow hcl, hih, ← Submodule.span_union]
        congr 1
        ext u
        simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_singleton_iff]
        constructor
        · rintro (⟨j, hj, rfl⟩ | rfl)
          · exact ⟨j.castSucc, hj, rfl⟩
          · exact ⟨Fin.last m, hlast, rfl⟩
        · rintro ⟨j, hj, rfl⟩
          refine Fin.lastCases ?_ ?_ j hj
          · intro _; right; rfl
          · intro j' hj'; left; exact ⟨j', hj', rfl⟩
      · have hbeq : (ow (Fin.last m) == g) = false := beq_false_of_ne hlast
        simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
        rw [hih]
        congr 1
        ext u
        simp only [Set.mem_ofPred_eq]
        constructor
        · rintro ⟨j, hj, rfl⟩
          exact ⟨j.castSucc, hj, rfl⟩
        · rintro ⟨j, hj, rfl⟩
          refine Fin.lastCases ?_ ?_ j hj
          · intro hl; exact absurd hl hlast
          · intro j' hj'; exact ⟨j', hj', rfl⟩
  rw [mem_kernelSub_iff_orth_rowSpan, hspan t owner l a]
  constructor
  · intro h j hj
    exact h (fun k => quadEval (l j) (a j) (E k)) (Submodule.subset_span ⟨j, hj, rfl⟩)
  · intro hc u hu
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨j, hj, rfl⟩; exact hc j hj
    · simp
    · intro x y _ _ hx hy
      calc ∑ k : Fin n, (x + y) k * c k
          = (∑ k : Fin n, x k * c k) + ∑ k : Fin n, y k * c k := by
              rw [← Finset.sum_add_distrib]
              exact Finset.sum_congr rfl fun k _ => add_mul _ _ _
        _ = 0 := by rw [hx, hy, add_zero]
    · intro a0 x _ hx
      calc ∑ k : Fin n, (a0 • x) k * c k
          = a0 * ∑ k : Fin n, x k * c k := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun k _ => by simp [mul_assoc]
        _ = 0 := by rw [hx, mul_zero]

private def periodBasis {n t : ℕ} (owner : Fin t → Fin 3)
    (l : Fin t → Fin n → ZMod 2) (a : Fin t → Matrix (Fin n) (Fin n) (ZMod 2))
    (g : Fin 3) : Fin n → Fin n → ZMod 2 :=
  let E := kernelBasis (radicalTable owner a g)
  let C := kernelBasis (evalTable owner l a g E)
  fun m i => ∑ k : Fin n, C m k * E k i

private lemma span_periodBasis_eq {n t : ℕ} (owner : Fin t → Fin 3)
    (l : Fin t → Fin n → ZMod 2) (a : Fin t → Matrix (Fin n) (Fin n) (ZMod 2))
    (g : Fin 3) :
    Submodule.span (ZMod 2) (Set.range (periodBasis owner l a g)) = periodSub owner l a g := by
  set E := kernelBasis (radicalTable owner a g)
  set C := kernelBasis (evalTable owner l a g E)
  have hE_span : Submodule.span (ZMod 2) (Set.range E) = radicalSub owner a g := by
    rw [span_kernelBasis_eq (isCleanBasis_radicalTable owner a g), kernelSub_radicalTable]
  have hE_mem : ∀ k : Fin n, E k ∈ radicalSub owner a g := fun k => by
    rw [← hE_span]; exact Submodule.subset_span ⟨k, rfl⟩
  have hC_span : Submodule.span (ZMod 2) (Set.range C) = kernelSub (evalTable owner l a g E) :=
    span_kernelBasis_eq (isCleanBasis_evalTable owner l a g E)
  have hC_mem : ∀ m : Fin n, C m ∈ kernelSub (evalTable owner l a g E) := fun m => by
    rw [← hC_span]; exact Submodule.subset_span ⟨m, rfl⟩
  have hB_eq : ∀ m : Fin n, periodBasis owner l a g m = ∑ k : Fin n, C m k • E k := by
    intro m; funext i; simp [periodBasis, E, C, Finset.sum_apply, smul_eq_mul]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro v ⟨m, rfl⟩
    rw [hB_eq m]
    refine ⟨Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hE_mem k), fun j hj => ?_⟩
    rw [quadEval_sum_on_radical owner l a E hE_mem (C m) hj]
    have h0 := (mem_kernelSub_evalTable_iff owner l a g E (C m)).mp (hC_mem m) j hj
    simpa [mul_comm] using h0
  · intro v hv
    have hv_rad : v ∈ Submodule.span (ZMod 2) (Set.range E) := by
      rw [hE_span]; exact hv.1
    rw [Submodule.mem_span_range_iff_exists_fun] at hv_rad
    rcases hv_rad with ⟨c, rfl⟩
    have hc_ker : c ∈ kernelSub (evalTable owner l a g E) := by
      rw [mem_kernelSub_evalTable_iff]
      intro j hj
      have h0 := hv.2 j hj
      rw [quadEval_sum_on_radical owner l a E hE_mem c hj] at h0
      simpa [mul_comm] using h0
    rw [← hC_span, Submodule.mem_span_range_iff_exists_fun] at hc_ker
    rcases hc_ker with ⟨d, hd⟩
    have hv_eq : (∑ k : Fin n, c k • E k) = ∑ m : Fin n, d m • periodBasis owner l a g m := by
      funext i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, periodBasis, E]
      calc ∑ k : Fin n, c k * E k i
          = ∑ k : Fin n, (∑ m : Fin n, d m * C m k) * E k i := by
              refine Finset.sum_congr rfl fun k _ => ?_
              have hck := congrFun hd k
              simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hck
              rw [← hck]
        _ = ∑ m : Fin n, d m * ∑ k : Fin n, C m k * E k i := by
              simp_rw [Finset.sum_mul, Finset.mul_sum]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => by ring
    rw [hv_eq]
    exact Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)

private def allSubsets3 : List (Finset (Fin 3)) :=
  [∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}]

private def subsetsWithout (g : Fin 3) : List (Finset (Fin 3)) :=
  allSubsets3.filter (fun S => decide (g ∉ S))

private lemma mem_allSubsets3 (S : Finset (Fin 3)) : S ∈ allSubsets3 := by
  decide +revert

private lemma mem_subsetsWithout_iff (g : Fin 3) (S : Finset (Fin 3)) :
    S ∈ subsetsWithout g ↔ g ∉ S := by
  simp [subsetsWithout, mem_allSubsets3]

private def insertSubsets {n : ℕ} (B : Fin 3 → Fin n → Fin n → ZMod 2)
    (S : Finset (Fin 3)) (T : Fin n → Fin n → ZMod 2) : Fin n → Fin n → ZMod 2 :=
  iterFin 3 (fun c acc => if decide (c ∈ S) then insertMany n (B c) acc else acc) T

private lemma isCleanBasis_insertSubsets {n : ℕ} (B : Fin 3 → Fin n → Fin n → ZMod 2)
    (S : Finset (Fin 3)) {T : Fin n → Fin n → ZMod 2} (hT : IsCleanBasis T) :
    IsCleanBasis (insertSubsets B S T) := by
  unfold insertSubsets
  have hstep : ∀ (c : Fin 3) (acc : Fin n → Fin n → ZMod 2),
      IsCleanBasis acc →
      IsCleanBasis (if decide (c ∈ S) then insertMany n (B c) acc else acc) := by
    intro c acc hacc
    split_ifs
    · exact isCleanBasis_insertMany n (B c) hacc
    · exact hacc
  exact hstep 2 _ (hstep 1 _ (hstep 0 T hT))

private lemma rowSpan_insertSubsets {n : ℕ} (B : Fin 3 → Fin n → Fin n → ZMod 2)
    (S : Finset (Fin 3)) {T : Fin n → Fin n → ZMod 2} (hT : IsCleanBasis T) :
    rowSpan (insertSubsets B S T) =
      rowSpan T ⊔ ⨆ c ∈ S, Submodule.span (ZMod 2) (Set.range (B c)) := by
  let P : Fin 3 → Submodule (ZMod 2) (Fin n → ZMod 2) :=
    fun c => Submodule.span (ZMod 2) (Set.range (B c))
  let stepFn : Fin 3 → (Fin n → Fin n → ZMod 2) → (Fin n → Fin n → ZMod 2) :=
    fun c acc => if decide (c ∈ S) then insertMany n (B c) acc else acc
  have hclStep : ∀ c acc, IsCleanBasis acc → IsCleanBasis (stepFn c acc) := by
    intro c acc hacc
    dsimp only [stepFn]
    split_ifs
    · exact isCleanBasis_insertMany n (B c) hacc
    · exact hacc
  have hspanStep : ∀ c acc, IsCleanBasis acc →
      rowSpan (stepFn c acc) = rowSpan acc ⊔ (if c ∈ S then P c else ⊥) := by
    intro c acc hacc
    dsimp only [stepFn]
    by_cases hc : c ∈ S
    · simp only [hc, decide_true, ↓reduceIte]
      exact rowSpan_insertMany n (B c) hacc
    · simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte, sup_bot_eq]
  have hunfold : insertSubsets B S T = stepFn 2 (stepFn 1 (stepFn 0 T)) := rfl
  have h0 : IsCleanBasis (stepFn 0 T) := hclStep 0 T hT
  have h1 : IsCleanBasis (stepFn 1 (stepFn 0 T)) := hclStep 1 _ h0
  rw [hunfold, hspanStep 2 _ h1, hspanStep 1 _ h0, hspanStep 0 T hT]
  have hsup : (⨆ c ∈ S, P c) =
      (if (0 : Fin 3) ∈ S then P 0 else ⊥) ⊔
      (if (1 : Fin 3) ∈ S then P 1 else ⊥) ⊔
      (if (2 : Fin 3) ∈ S then P 2 else ⊥) := by
    apply le_antisymm
    · refine iSup₂_le fun c hc => ?_
      fin_cases c
      · change (0 : Fin 3) ∈ S at hc
        simp only [hc, ↓reduceIte]
        exact le_sup_of_le_left le_sup_left
      · change (1 : Fin 3) ∈ S at hc
        simp only [hc, ↓reduceIte]
        exact le_sup_of_le_left le_sup_right
      · change (2 : Fin 3) ∈ S at hc
        simp only [hc, ↓reduceIte]
        exact le_sup_right
    · refine sup_le (sup_le ?_ ?_) ?_
      · by_cases h : (0 : Fin 3) ∈ S
        · simp only [h, ↓reduceIte]; exact le_iSup₂_of_le 0 h le_rfl
        · simp [h]
      · by_cases h : (1 : Fin 3) ∈ S
        · simp only [h, ↓reduceIte]; exact le_iSup₂_of_le 1 h le_rfl
        · simp [h]
      · by_cases h : (2 : Fin 3) ∈ S
        · simp only [h, ↓reduceIte]; exact le_iSup₂_of_le 2 h le_rfl
        · simp [h]
  rw [hsup]
  ac_rfl

private def RadoOK {n : ℕ} (P : Fin 3 → Submodule (ZMod 2) (Fin n → ZMod 2))
    (U : Submodule (ZMod 2) (Fin n → ZMod 2)) (k : ℕ) (q : Fin 3 → ℕ) : Prop :=
  Module.finrank (ZMod 2) U = k ∧
  ∀ S : Finset (Fin 3), k + ∑ c ∈ S, q c ≤ Module.finrank (ZMod 2) ↥(U ⊔ ⨆ c ∈ S, P c)

private lemma rado_step_iff {n : ℕ} (P : Fin 3 → Submodule (ZMod 2) (Fin n → ZMod 2))
    (U : Submodule (ZMod 2) (Fin n → ZMod 2)) (k : ℕ) (q : Fin 3 → ℕ)
    (hR : RadoOK P U k q) (g : Fin 3) (hqg : 0 < q g)
    {w : Fin n → ZMod 2} (hw : w ∈ P g) :
    let q' := fun c : Fin 3 => if c = g then q g - 1 else q c
    RadoOK P (U ⊔ Submodule.span (ZMod 2) {w}) (k + 1) q' ↔
      ∀ S : Finset (Fin 3), g ∉ S →
        (k + 1) + ∑ c ∈ S, q' c ≤
          Module.finrank (ZMod 2) ↥((U ⊔ Submodule.span (ZMod 2) {w}) ⊔ ⨆ c ∈ S, P c) := by
  intro q'
  constructor
  · intro h S _; exact h.2 S
  · intro h
    have hfin_le : Module.finrank (ZMod 2) ↥(U ⊔ Submodule.span (ZMod 2) {w}) ≤ k + 1 := by
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq U (Submodule.span (ZMod 2) {w})
      have h2 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {w}) ≤ 1 := by
        have := finrank_span_le_card (R := ZMod 2) ({w} : Set (Fin n → ZMod 2))
        simpa using this
      have hUk : Module.finrank (ZMod 2) U = k := hR.1
      omega
    have hfin_ge : k + 1 ≤ Module.finrank (ZMod 2) ↥(U ⊔ Submodule.span (ZMod 2) {w}) := by
      have h0 := h ∅ (Finset.notMem_empty g)
      have hem : (⨆ c ∈ (∅ : Finset (Fin 3)), P c) = ⊥ := by simp
      rw [hem, sup_bot_eq, Finset.sum_empty, add_zero] at h0
      exact h0
    have hfin_eq : Module.finrank (ZMod 2) ↥(U ⊔ Submodule.span (ZMod 2) {w}) = k + 1 :=
      le_antisymm hfin_le hfin_ge
    refine ⟨hfin_eq, fun S => ?_⟩
    by_cases hgS : g ∈ S
    · have hspan_le : Submodule.span (ZMod 2) {w} ≤ ⨆ c ∈ S, P c := by
        rw [Submodule.span_singleton_le_iff_mem]
        have hle : P g ≤ ⨆ c ∈ S, P c := le_iSup₂_of_le g hgS le_rfl
        exact hle hw
      have hsup_eq : (U ⊔ Submodule.span (ZMod 2) {w}) ⊔ (⨆ c ∈ S, P c) =
          U ⊔ ⨆ c ∈ S, P c := by
        rw [sup_assoc, sup_eq_right.mpr hspan_le]
      rw [hsup_eq]
      have hsum_eq : (k + 1) + ∑ c ∈ S, q' c = k + ∑ c ∈ S, q c := by
        rw [← Finset.add_sum_erase _ _ hgS, ← Finset.add_sum_erase _ _ hgS]
        have herase : ∑ c ∈ S.erase g, q' c = ∑ c ∈ S.erase g, q c := by
          refine Finset.sum_congr rfl fun c hc => ?_
          have hne : c ≠ g := (Finset.mem_erase.mp hc).1
          simp [q', hne]
        rw [herase]
        simp only [q', ↓reduceIte]
        omega
      rw [hsum_eq]
      exact hR.2 S
    · exact h S hgS

private lemma rado_exists_step {n : ℕ} (P : Fin 3 → Submodule (ZMod 2) (Fin n → ZMod 2))
    (B : Fin n → Fin n → ZMod 2) (hB : Submodule.span (ZMod 2) (Set.range B) = P g)
    (U : Submodule (ZMod 2) (Fin n → ZMod 2)) (k : ℕ) (q : Fin 3 → ℕ)
    (hR : RadoOK P U k q) (hqg : 0 < q g) :
    let q' := fun c : Fin 3 => if c = g then q g - 1 else q c
    ∃ m : Fin n, ∀ S : Finset (Fin 3), g ∉ S →
      (k + 1) + ∑ c ∈ S, q' c ≤
        Module.finrank (ZMod 2) ↥((U ⊔ Submodule.span (ZMod 2) {B m}) ⊔ ⨆ c ∈ S, P c) := by
  classical
  intro q'
  let M : Finset (Fin 3) → Submodule (ZMod 2) (Fin n → ZMod 2) :=
    fun S => U ⊔ ⨆ c ∈ S, P c
  let isTight : Finset (Fin 3) → Prop :=
    fun S => g ∉ S ∧ Module.finrank (ZMod 2) (M S) = k + ∑ c ∈ S, q c
  have hM_union : ∀ S1 S2 : Finset (Fin 3), M (S1 ∪ S2) = M S1 ⊔ M S2 := by
    intro S1 S2
    simp only [M]
    have hbi : (⨆ c ∈ S1 ∪ S2, P c) = (⨆ c ∈ S1, P c) ⊔ (⨆ c ∈ S2, P c) := by
      apply le_antisymm
      · refine iSup₂_le fun c hc => ?_
        rcases Finset.mem_union.mp hc with h1 | h2
        · exact le_sup_of_le_left (le_iSup₂_of_le c h1 le_rfl)
        · exact le_sup_of_le_right (le_iSup₂_of_le c h2 le_rfl)
      · refine sup_le (iSup₂_le fun c hc => le_iSup₂_of_le c (Finset.mem_union_left S2 hc) le_rfl)
          (iSup₂_le fun c hc => le_iSup₂_of_le c (Finset.mem_union_right S1 hc) le_rfl)
    rw [hbi]
    ac_rfl
  have hM_inter : ∀ S1 S2 : Finset (Fin 3), M (S1 ∩ S2) ≤ M S1 ⊓ M S2 := by
    intro S1 S2
    refine le_inf ?_ ?_
    · refine sup_le le_sup_left (le_sup_of_le_right (iSup₂_le fun c hc =>
        le_iSup₂_of_le c (Finset.mem_inter.mp hc).1 le_rfl))
    · refine sup_le le_sup_left (le_sup_of_le_right (iSup₂_le fun c hc =>
        le_iSup₂_of_le c (Finset.mem_inter.mp hc).2 le_rfl))
  have htight_empty : isTight ∅ := by
    refine ⟨Finset.notMem_empty g, ?_⟩
    have hM0 : M ∅ = U := by
      dsimp only [M]
      have hem : (⨆ c ∈ (∅ : Finset (Fin 3)), P c) = ⊥ := by simp
      rw [hem, sup_bot_eq]
    rw [hM0, hR.1, Finset.sum_empty, add_zero]
  have htight_union : ∀ S1 S2 : Finset (Fin 3), isTight S1 → isTight S2 → isTight (S1 ∪ S2) := by
    intro S1 S2 h1 h2
    refine ⟨by simp [h1.1, h2.1], ?_⟩
    have hsubmod := Submodule.finrank_sup_add_finrank_inf_eq (M S1) (M S2)
    have hinf_ge : k + ∑ c ∈ S1 ∩ S2, q c ≤ Module.finrank (ZMod 2) ↥(M S1 ⊓ M S2) :=
      le_trans (hR.2 (S1 ∩ S2)) (Submodule.finrank_mono (hM_inter S1 S2))
    have hsum_ui := Finset.sum_union_inter (s₁ := S1) (s₂ := S2) (f := q)
    have hle : Module.finrank (ZMod 2) (M (S1 ∪ S2)) ≤ k + ∑ c ∈ S1 ∪ S2, q c := by
      rw [hM_union]
      omega
    exact le_antisymm hle (hR.2 (S1 ∪ S2))
  let tightFam : Finset (Finset (Fin 3)) := Finset.univ.filter isTight
  let Tstar : Finset (Fin 3) := tightFam.biUnion id
  have hTstar : isTight Tstar := by
    have haux : ∀ F : Finset (Finset (Fin 3)), (∀ S ∈ F, isTight S) → isTight (F.biUnion id) := by
      intro F
      induction F using Finset.induction_on with
      | empty => intro _; simpa using htight_empty
      | @insert S F hSF ih =>
        intro hF
        rw [Finset.biUnion_insert]
        exact htight_union S (F.biUnion id) (hF S (Finset.mem_insert_self S F))
          (ih fun S' hS' => hF S' (Finset.mem_insert_of_mem hS'))
    exact haux tightFam (fun S hS => (Finset.mem_filter.mp hS).2)
  have hex_not_mem : ∃ m : Fin n, B m ∉ M Tstar := by
    by_contra hall
    push Not at hall
    have hPg_le : P g ≤ M Tstar := by
      rw [← hB, Submodule.span_le]
      rintro v ⟨m, rfl⟩
      exact hall m
    have hM_ins : M (insert g Tstar) = M Tstar := by
      apply le_antisymm
      · refine sup_le le_sup_left (iSup₂_le fun c hc => ?_)
        rcases Finset.mem_insert.mp hc with rfl | hcT
        · exact hPg_le
        · exact le_sup_of_le_right (le_iSup₂_of_le c hcT le_rfl)
      · refine sup_le le_sup_left (le_sup_of_le_right (iSup₂_le fun c hc =>
          le_iSup₂_of_le c (Finset.mem_insert_of_mem hc) le_rfl))
    have hge : k + ∑ c ∈ insert g Tstar, q c ≤ Module.finrank (ZMod 2) (M (insert g Tstar)) :=
      hR.2 (insert g Tstar)
    rw [hM_ins, hTstar.2, Finset.sum_insert hTstar.1] at hge
    omega
  rcases hex_not_mem with ⟨m, hm⟩
  refine ⟨m, fun S hgS => ?_⟩
  have hsum_q : ∑ c ∈ S, q' c = ∑ c ∈ S, q c := by
    refine Finset.sum_congr rfl fun c hc => ?_
    have hne : c ≠ g := fun h => hgS (h ▸ hc)
    simp [q', hne]
  rw [hsum_q]
  have htarget_eq : (U ⊔ Submodule.span (ZMod 2) {B m}) ⊔ (⨆ c ∈ S, P c) =
      M S ⊔ Submodule.span (ZMod 2) {B m} := by
    simp only [M]; ac_rfl
  rw [htarget_eq]
  by_cases ht : isTight S
  · have hsub : S ⊆ Tstar := by
      intro c hc
      exact Finset.mem_biUnion.mpr ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ S, ht⟩, hc⟩
    have hMS_le : M S ≤ M Tstar :=
      sup_le le_sup_left (le_sup_of_le_right (iSup₂_le fun c hc => le_iSup₂_of_le c (hsub hc) le_rfl))
    have hBm_not : B m ∉ M S := fun h => hm (hMS_le h)
    have hlt : M S < M S ⊔ Submodule.span (ZMod 2) {B m} := by
      refine lt_of_le_of_ne le_sup_left ?_
      intro heq
      have hmem : B m ∈ M S ⊔ Submodule.span (ZMod 2) {B m} :=
        Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _))
      rw [← heq] at hmem
      exact hBm_not hmem
    have hrank_lt := Submodule.finrank_lt_finrank_of_lt hlt
    rw [ht.2] at hrank_lt
    omega
  · have hge : k + ∑ c ∈ S, q c ≤ Module.finrank (ZMod 2) (M S) := hR.2 S
    have hne : Module.finrank (ZMod 2) (M S) ≠ k + ∑ c ∈ S, q c := fun heq => ht ⟨hgS, heq⟩
    have hmono : Module.finrank (ZMod 2) (M S) ≤
        Module.finrank (ZMod 2) ↥(M S ⊔ Submodule.span (ZMod 2) {B m}) :=
      Submodule.finrank_mono le_sup_left
    omega

private def checkSubsets {n : ℕ} (B : Fin 3 → Fin n → Fin n → ZMod 2)
    (T : Fin n → Fin n → ZMod 2) (k : ℕ) (q : Fin 3 → ℕ)
    (subs : List (Finset (Fin 3))) : Bool :=
  subs.all (fun S => decide (k + ∑ c ∈ S, q c ≤ rankClean (insertSubsets B S T)))

private def remQuota (h k : ℕ) (c : Fin 3) : ℕ :=
  if k ≤ c.val * h then h
  else if k < (c.val + 1) * h then (c.val + 1) * h - k
  else 0

private def gOf (h k : ℕ) : Fin 3 :=
  if hlt : k / h < 3 then ⟨k / h, hlt⟩ else 0

private lemma remQuota_zero (h : ℕ) (c : Fin 3) : remQuota h 0 c = h := by
  simp [remQuota]

private lemma remQuota_step {h k : ℕ} (hh : 0 < h) (hk : k < 3 * h) :
    0 < remQuota h k (gOf h k) ∧
    ∀ c : Fin 3, remQuota h (k + 1) c =
      if c = gOf h k then remQuota h k (gOf h k) - 1 else remQuota h k c := by
  have hdiv_lt : k / h < 3 := Nat.div_lt_of_lt_mul (by omega)
  have hg_val : (gOf h k).val = k / h := by simp [gOf, hdiv_lt]
  have hmul_le : (gOf h k).val * h ≤ k := by
    rw [hg_val, mul_comm]; exact Nat.mul_div_le k h
  have hlt_next : k < ((gOf h k).val + 1) * h := by
    rw [hg_val, add_mul, one_mul]
    have hmod := Nat.div_add_mod k h
    have hmlt := Nat.mod_lt k hh
    nlinarith
  have hpos : 0 < remQuota h k (gOf h k) := by
    unfold remQuota
    split_ifs <;> omega
  have hg_add : (gOf h k).val * h + h = ((gOf h k).val + 1) * h := by ring
  refine ⟨hpos, fun c => ?_⟩
  by_cases hcg : c = gOf h k
  · subst hcg
    unfold remQuota
    split_ifs <;> omega
  · have hne : c.val ≠ (gOf h k).val := fun h => hcg (Fin.ext h)
    have hc_add : c.val * h + h = (c.val + 1) * h := by ring
    simp only [hcg, ↓reduceIte]
    unfold remQuota
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h1 : (c.val + 1) * h ≤ (gOf h k).val * h := Nat.mul_le_mul_right h (by omega)
      split_ifs <;> omega
    · have h1 : ((gOf h k).val + 1) * h ≤ c.val * h := Nat.mul_le_mul_right h (by omega)
      split_ifs <;> omega

private def greedyStep {n : ℕ} (B : Fin 3 → Fin n → Fin n → ZMod 2)
    (g : Fin 3) (k : ℕ) (q' : Fin 3 → ℕ) (T : Fin n → Fin n → ZMod 2) :
    (Fin n → Fin n → ZMod 2) × (Fin n → ZMod 2) :=
  let ok := fun m : Fin n => checkSubsets B (insertRow T (B g m)) (k + 1) q' (subsetsWithout g)
  let pick := firstOk ok
  let v := fun pos : Fin n => ∑ m : Fin n, b2z (pick m) * B g m pos
  (insertRow T v, v)

private def greedyRun {n : ℕ} (B : Fin 3 → Fin n → Fin n → ZMod 2) (h : ℕ) :
    ∀ (k : ℕ), (Fin n → Fin n → ZMod 2) × (Fin k → Fin n → ZMod 2)
  | 0 => (zeroMat n, Fin.elim0)
  | k + 1 =>
    let prev := greedyRun B h k
    let step := greedyStep B (gOf h k) k (remQuota h (k + 1)) prev.1
    (step.1, Fin.snoc prev.2 step.2)

private lemma greedyStep_spec {n : ℕ} (B : Fin 3 → Fin n → Fin n → ZMod 2)
    (P : Fin 3 → Submodule (ZMod 2) (Fin n → ZMod 2))
    (hB : ∀ c : Fin 3, Submodule.span (ZMod 2) (Set.range (B c)) = P c)
    {T : Fin n → Fin n → ZMod 2} (hT : IsCleanBasis T)
    (g : Fin 3) (k : ℕ) (q : Fin 3 → ℕ) (hR : RadoOK P (rowSpan T) k q) (hqg : 0 < q g) :
    let q' := fun c : Fin 3 => if c = g then q g - 1 else q c
    let res := greedyStep B g k q' T
    IsCleanBasis res.1 ∧
    res.2 ∈ P g ∧
    rowSpan res.1 = rowSpan T ⊔ Submodule.span (ZMod 2) {res.2} ∧
    RadoOK P (rowSpan res.1) (k + 1) q' := by
  intro q' res
  set ok := fun m : Fin n => checkSubsets B (insertRow T (B g m)) (k + 1) q' (subsetsWithout g)
  have hok_iff : ∀ m : Fin n, ok m = true ↔
      ∀ S : Finset (Fin 3), g ∉ S →
        (k + 1) + ∑ c ∈ S, q' c ≤
          Module.finrank (ZMod 2) ↥((rowSpan T ⊔ Submodule.span (ZMod 2) {B g m}) ⊔ ⨆ c ∈ S, P c) := by
    intro m
    simp only [ok, checkSubsets, List.all_eq_true, decide_eq_true_eq, mem_subsetsWithout_iff]
    constructor <;> intro h S hgS
    · have h1 := h S hgS
      have hcl := isCleanBasis_insertRow hT (B g m)
      have hsup : (rowSpan T ⊔ Submodule.span (ZMod 2) {B g m}) ⊔
          (⨆ c ∈ S, Submodule.span (ZMod 2) (Set.range (B c))) =
          (rowSpan T ⊔ Submodule.span (ZMod 2) {B g m}) ⊔ ⨆ c ∈ S, P c := by
        congr 1
        exact iSup_congr fun c => iSup_congr fun _ => hB c
      rw [rankClean_eq_finrank (isCleanBasis_insertSubsets B S hcl),
        rowSpan_insertSubsets B S hcl, rowSpan_insertRow hT (B g m), hsup] at h1
      exact h1
    · have hcl := isCleanBasis_insertRow hT (B g m)
      have hsup : (rowSpan T ⊔ Submodule.span (ZMod 2) {B g m}) ⊔
          (⨆ c ∈ S, Submodule.span (ZMod 2) (Set.range (B c))) =
          (rowSpan T ⊔ Submodule.span (ZMod 2) {B g m}) ⊔ ⨆ c ∈ S, P c := by
        congr 1
        exact iSup_congr fun c => iSup_congr fun _ => hB c
      rw [rankClean_eq_finrank (isCleanBasis_insertSubsets B S hcl),
        rowSpan_insertSubsets B S hcl, rowSpan_insertRow hT (B g m), hsup]
      exact h S hgS
  have hex : ∃ m : Fin n, ok m = true := by
    rcases rado_exists_step P (B g) (hB g) (rowSpan T) k q hR hqg with ⟨m, hm⟩
    exact ⟨m, (hok_iff m).mpr hm⟩
  rcases exists_firstOk ok hex with ⟨m0, hm0⟩
  have hm0_ok : ok m0 = true := ((firstOk_eq_true_iff ok m0).mp hm0).1
  have hv_eq : res.2 = B g m0 := by
    funext pos
    change (∑ m : Fin n, b2z (firstOk ok m) * B g m pos) = B g m0 pos
    rw [Finset.sum_eq_single m0]
    · simp [hm0, b2z]
    · intro m _ hne
      have hf : firstOk ok m = false := by
        cases h : firstOk ok m
        · rfl
        · exact absurd (firstOk_unique ok h hm0) hne
      simp [hf, b2z]
    · intro hnot
      exact absurd (Finset.mem_univ m0) hnot
  have hBm0_mem : B g m0 ∈ P g := by
    rw [← hB g]; exact Submodule.subset_span ⟨m0, rfl⟩
  have hres1 : res.1 = insertRow T (B g m0) := by
    change insertRow T res.2 = insertRow T (B g m0)
    rw [hv_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hres1]; exact isCleanBasis_insertRow hT (B g m0)
  · rw [hv_eq]; exact hBm0_mem
  · rw [hres1, hv_eq]; exact rowSpan_insertRow hT (B g m0)
  · rw [hres1, rowSpan_insertRow hT (B g m0)]
    exact (rado_step_iff P (rowSpan T) k q hR g hqg hBm0_mem).mpr ((hok_iff m0).mp hm0_ok)

private lemma greedyRun_spec {n : ℕ} (B : Fin 3 → Fin n → Fin n → ZMod 2)
    (P : Fin 3 → Submodule (ZMod 2) (Fin n → ZMod 2))
    (hB : ∀ c : Fin 3, Submodule.span (ZMod 2) (Set.range (B c)) = P c)
    {h : ℕ} (hh : 0 < h)
    (hinit : RadoOK P ⊥ 0 (fun _ => h)) :
    ∀ k : ℕ, k ≤ 3 * h →
      let res := greedyRun B h k
      IsCleanBasis res.1 ∧
      rowSpan res.1 = Submodule.span (ZMod 2) (Set.range res.2) ∧
      RadoOK P (rowSpan res.1) k (remQuota h k) ∧
      ∀ idx : Fin k, res.2 idx ∈ P (gOf h idx.val) := by
  intro k
  induction k with
  | zero =>
    intro _
    dsimp only [greedyRun]
    refine ⟨isCleanBasis_zeroMat n, ?_, ?_, fun idx => idx.elim0⟩
    · rw [rowSpan_zeroMat]
      symm
      rw [Submodule.span_eq_bot]
      rintro _ ⟨idx, _⟩
      exact idx.elim0
    · rw [rowSpan_zeroMat]
      have hq : remQuota h 0 = fun _ => h := funext (remQuota_zero h)
      rw [hq]
      exact hinit
  | succ k ih =>
    intro hle
    have hlt : k < 3 * h := by omega
    rcases ih (by omega) with ⟨hT, hspan, hR, hmem⟩
    rcases remQuota_step hh hlt with ⟨hqg, hqstep⟩
    have hq_eq : remQuota h (k + 1) = fun c =>
        if c = gOf h k then remQuota h k (gOf h k) - 1 else remQuota h k c :=
      funext hqstep
    have hst := greedyStep_spec B P hB hT (gOf h k) k (remQuota h k) hR hqg
    dsimp only [greedyRun]
    rw [hq_eq]
    refine ⟨hst.1, ?_, hst.2.2.2, ?_⟩
    · rw [hst.2.2.1, hspan, ← Submodule.span_union]
      congr 1
      ext v
      simp only [Set.mem_union, Set.mem_range, Set.mem_singleton_iff]
      constructor
      · rintro (⟨i, rfl⟩ | rfl)
        · exact ⟨i.castSucc, by simp [Fin.snoc]⟩
        · exact ⟨Fin.last k, by simp [Fin.snoc]⟩
      · rintro ⟨i, rfl⟩
        refine Fin.lastCases ?_ ?_ i
        · right; simp [Fin.snoc]
        · intro j; left; exact ⟨j, by simp [Fin.snoc]⟩
    · intro idx
      refine Fin.lastCases ?_ ?_ idx
      · simpa [Fin.snoc] using hst.2.1
      · intro j; simpa [Fin.snoc] using hmem j

private lemma linearIndependent_of_finrank_span {ι : Type*} [Fintype ι] {n : ℕ}
    (v : ι → Fin n → ZMod 2)
    (hcard : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range v)) = Fintype.card ι) :
    LinearIndependent (ZMod 2) v := by
  let U := Submodule.span (ZMod 2) (Set.range v)
  let φ : (ι → ZMod 2) →ₗ[ZMod 2] U :=
    { toFun := fun c => ⟨∑ i : ι, c i • v i,
        Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)⟩
      map_add' := fun c1 c2 => by
        ext pos
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, Submodule.coe_add]
      map_smul' := fun a c => by
        ext pos
        simp only [Pi.smul_apply, RingHom.id_apply, SetLike.val_smul, Finset.sum_apply,
          smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring }
  have hsurj : Function.Surjective φ := by
    rintro ⟨u, hu⟩
    rw [Submodule.mem_span_range_iff_exists_fun] at hu
    rcases hu with ⟨c, rfl⟩
    exact ⟨c, rfl⟩
  have hfin_eq : Module.finrank (ZMod 2) (ι → ZMod 2) = Module.finrank (ZMod 2) U := by
    rw [Module.finrank_pi, hcard]
  have hinj : Function.Injective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin_eq).mpr hsurj
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hφ : φ c = φ 0 := by
    ext pos
    simpa [φ] using congrFun hc pos
  have hc0 := hinj hφ
  exact fun i => congrFun hc0 i

private def slotIdx (h : ℕ) (slot : Fin 3 × Fin h) : Fin (3 * h) :=
  ⟨slot.1.val * h + slot.2.val, by
    have h1 : slot.1.val ≤ 2 := by omega
    have h2 : slot.2.val < h := slot.2.isLt
    nlinarith⟩

private lemma slotIdx_bijective (h : ℕ) : Function.Bijective (slotIdx h) := by
  refine ⟨?_, ?_⟩
  · intro s1 s2 heq
    have hv : s1.1.val * h + s1.2.val = s2.1.val * h + s2.2.val := congrArg Fin.val heq
    have hh : 0 < h := Nat.pos_of_ne_zero (by intro h0; subst h0; exact s1.2.elim0)
    have hq : s1.1.val = s2.1.val := by
      have h1 : (s1.1.val * h + s1.2.val) / h = s1.1.val := by
        rw [mul_comm, Nat.mul_add_div hh, Nat.div_eq_of_lt s1.2.isLt, add_zero]
      have h2 : (s2.1.val * h + s2.2.val) / h = s2.1.val := by
        rw [mul_comm, Nat.mul_add_div hh, Nat.div_eq_of_lt s2.2.isLt, add_zero]
      rw [hv] at h1
      omega
    have hr : s1.2.val = s2.2.val := by nlinarith
    exact Prod.ext (Fin.ext hq) (Fin.ext hr)
  · intro idx
    have hh : 0 < h := Nat.pos_of_ne_zero (by intro h0; subst h0; exact Nat.not_lt_zero _ idx.isLt)
    have hq : idx.val / h < 3 := Nat.div_lt_of_lt_mul (by omega)
    refine ⟨(⟨idx.val / h, hq⟩, ⟨idx.val % h, Nat.mod_lt _ hh⟩), ?_⟩
    ext
    simp only [slotIdx]
    have := Nat.div_add_mod idx.val h
    nlinarith

private lemma gOf_slotIdx {h : ℕ} (slot : Fin 3 × Fin h) :
    gOf h (slotIdx h slot).val = slot.1 := by
  have hh : 0 < h := Nat.pos_of_ne_zero (by intro h0; subst h0; exact slot.2.elim0)
  have hdiv : (slot.1.val * h + slot.2.val) / h = slot.1.val := by
    rw [mul_comm, Nat.mul_add_div hh, Nat.div_eq_of_lt slot.2.isLt, add_zero]
  unfold gOf slotIdx
  simp only [hdiv, slot.1.isLt, ↓reduceDIte]

private def solveFlag {n t : ℕ} (owner : Fin t → Fin 3)
    (l : Fin t → Fin n → ZMod 2) (a : Fin t → Matrix (Fin n) (Fin n) (ZMod 2))
    (h : ℕ) : Bool :=
  let B := fun g => periodBasis owner l a g
  checkSubsets B (zeroMat n) 0 (fun _ => h) allSubsets3

private def solveOut {n t : ℕ} (owner : Fin t → Fin 3)
    (l : Fin t → Fin n → ZMod 2) (a : Fin t → Matrix (Fin n) (Fin n) (ZMod 2))
    (h : ℕ) : (Fin 3 × Fin h) → Fin n → ZMod 2 :=
  let B := fun g => periodBasis owner l a g
  fun slot => (greedyRun B h (3 * h)).2 (slotIdx h slot)

private lemma solveFlag_eq_true_iff_rado {n t : ℕ} (owner : Fin t → Fin 3)
    (l : Fin t → Fin n → ZMod 2) (a : Fin t → Matrix (Fin n) (Fin n) (ZMod 2))
    (h : ℕ) :
    solveFlag owner l a h = true ↔
      RadoOK (periodSub owner l a) ⊥ 0 (fun _ => h) := by
  let B := fun g => periodBasis owner l a g
  have hB : ∀ c : Fin 3, Submodule.span (ZMod 2) (Set.range (B c)) = periodSub owner l a c :=
    fun c => span_periodBasis_eq owner l a c
  simp only [solveFlag, checkSubsets, List.all_eq_true, decide_eq_true_eq, RadoOK, finrank_bot,
    true_and]
  constructor
  · intro hS S
    have h1 := hS S (mem_allSubsets3 S)
    have hsup : (⊥ : Submodule (ZMod 2) (Fin n → ZMod 2)) ⊔
        (⨆ c ∈ S, Submodule.span (ZMod 2) (Set.range (B c))) =
        ⊥ ⊔ ⨆ c ∈ S, periodSub owner l a c := by
      congr 1
      exact iSup_congr fun c => iSup_congr fun _ => hB c
    rw [rankClean_eq_finrank (isCleanBasis_insertSubsets B S (isCleanBasis_zeroMat n)),
      rowSpan_insertSubsets B S (isCleanBasis_zeroMat n), rowSpan_zeroMat, hsup] at h1
    exact h1
  · intro hS S _
    have hsup : (⊥ : Submodule (ZMod 2) (Fin n → ZMod 2)) ⊔
        (⨆ c ∈ S, Submodule.span (ZMod 2) (Set.range (B c))) =
        ⊥ ⊔ ⨆ c ∈ S, periodSub owner l a c := by
      congr 1
      exact iSup_congr fun c => iSup_congr fun _ => hB c
    rw [rankClean_eq_finrank (isCleanBasis_insertSubsets B S (isCleanBasis_zeroMat n)),
      rowSpan_insertSubsets B S (isCleanBasis_zeroMat n), rowSpan_zeroMat, hsup]
    exact hS S

private lemma rado_of_valid {n t h : ℕ} (owner : Fin t → Fin 3)
    (l : Fin t → Fin n → ZMod 2) (a : Fin t → Matrix (Fin n) (Fin n) (ZMod 2))
    (v : (Fin 3 × Fin h) → Fin n → ZMod 2)
    (hli : LinearIndependent (ZMod 2) v)
    (hper : ∀ (j : Fin t) (s : Fin h) (x : Fin n → ZMod 2),
      quadEval (l j) (a j) (x + v (owner j, s)) = quadEval (l j) (a j) x) :
    RadoOK (periodSub owner l a) ⊥ 0 (fun _ => h) := by
  classical
  refine ⟨finrank_bot _ _, fun S => ?_⟩
  simp only [zero_add, Finset.sum_const, smul_eq_mul]
  let idxSet : Finset (Fin 3 × Fin h) := S ×ˢ Finset.univ
  have hli_sub : LinearIndependent (ZMod 2) (fun p : idxSet => v p.1) :=
    hli.comp Subtype.val Subtype.val_injective
  have hle_sub : Submodule.span (ZMod 2) (Set.range (fun p : idxSet => v p.1)) ≤
      ⊥ ⊔ ⨆ c ∈ S, periodSub owner l a c := by
    rw [bot_sup_eq, Submodule.span_le]
    rintro _ ⟨⟨⟨c, s⟩, hp⟩, rfl⟩
    have hcS : c ∈ S := (Finset.mem_product.mp hp).1
    have hv_mem : v (c, s) ∈ periodSub owner l a c := by
      rw [mem_periodSub_iff]
      intro j hj x
      subst hj
      exact hper j s x
    have hle : periodSub owner l a c ≤ ⨆ c ∈ S, periodSub owner l a c :=
      le_iSup₂_of_le c hcS le_rfl
    exact hle hv_mem
  have hrank := Submodule.finrank_mono hle_sub
  rw [finrank_span_eq_card hli_sub, Fintype.card_coe] at hrank
  have hcard : idxSet.card = S.card * h := by
    simp [idxSet, Finset.card_product]
  rwa [hcard] at hrank

private lemma solveOut_valid {n t h : ℕ} (hh : 0 < h) (owner : Fin t → Fin 3)
    (l : Fin t → Fin n → ZMod 2) (a : Fin t → Matrix (Fin n) (Fin n) (ZMod 2))
    (hflag : solveFlag owner l a h = true) :
    LinearIndependent (ZMod 2) (solveOut owner l a h) ∧
    ∀ (j : Fin t) (s : Fin h) (x : Fin n → ZMod 2),
      quadEval (l j) (a j) (x + solveOut owner l a h (owner j, s)) = quadEval (l j) (a j) x := by
  let B := fun g => periodBasis owner l a g
  have hB : ∀ c : Fin 3, Submodule.span (ZMod 2) (Set.range (B c)) = periodSub owner l a c :=
    fun c => span_periodBasis_eq owner l a c
  have hinit := (solveFlag_eq_true_iff_rado owner l a h).mp hflag
  rcases greedyRun_spec B (periodSub owner l a) hB hh hinit (3 * h) le_rfl with
    ⟨_, hspan, hR, hmem⟩
  have hrange : Set.range (solveOut owner l a h) = Set.range (greedyRun B h (3 * h)).2 := by
    ext v
    simp only [Set.mem_range, solveOut, B]
    constructor
    · rintro ⟨slot, rfl⟩; exact ⟨slotIdx h slot, rfl⟩
    · rintro ⟨idx, rfl⟩
      rcases (slotIdx_bijective h).2 idx with ⟨slot, rfl⟩
      exact ⟨slot, rfl⟩
  have hcard : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (solveOut owner l a h))) =
      Fintype.card (Fin 3 × Fin h) := by
    rw [hrange, ← hspan, hR.1]
    simp [Fintype.card_prod]
  refine ⟨linearIndependent_of_finrank_span _ hcard, fun j s x => ?_⟩
  have hv_mem : solveOut owner l a h (owner j, s) ∈ periodSub owner l a (owner j) := by
    have hm := hmem (slotIdx h (owner j, s))
    rw [gOf_slotIdx] at hm
    exact hm
  exact (mem_periodSub_iff owner l a (owner j) _).mp hv_mem j rfl x

private def Good (inputs : ℕ) (gs : List Gate) : Prop :=
  PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩ ∧
  PEqualNP.MetaComplexity.NestedCover.ReadsBack inputs ⟨gs, 0⟩

private def evalWires (gs : List Gate) (x : List Bool) : List Bool :=
  (Circuit.mk gs 0).wires x

private def wireAt (gs : List Gate) (x : List Bool) (w : ℕ) : Bool :=
  (evalWires gs x).getD w false

private def Extends (gs1 gs2 : List Gate) : Prop :=
  ∃ extra, gs2 = gs1 ++ extra

private lemma extends_refl (gs : List Gate) : Extends gs gs :=
  ⟨[], (List.append_nil gs).symm⟩

private lemma extends_trans {gs1 gs2 gs3 : List Gate}
    (h1 : Extends gs1 gs2) (h2 : Extends gs2 gs3) : Extends gs1 gs3 := by
  rcases h1 with ⟨e1, rfl⟩
  rcases h2 with ⟨e2, rfl⟩
  exact ⟨e1 ++ e2, List.append_assoc gs1 e1 e2⟩

private lemma extends_length_le {gs1 gs2 : List Gate} (h : Extends gs1 gs2) :
    gs1.length ≤ gs2.length := by
  rcases h with ⟨e, rfl⟩
  simp

private lemma getD_append_lt {α : Type*} (l1 l2 : List α) {i : ℕ} (hi : i < l1.length) (d : α) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma getD_append_ge {α : Type*} (l1 l2 : List α) {i : ℕ} (hi : l1.length ≤ i) (d : α) :
    (l1 ++ l2).getD i d = l2.getD (i - l1.length) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

private lemma foldl_wires_append (gs : List Gate) (acc : List Bool) :
    ∃ tail : List Bool,
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc =
        acc ++ tail := by
  induction gs generalizing acc with
  | nil => exact ⟨[], (List.append_nil acc).symm⟩
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rcases ih (acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) with ⟨tail, htail⟩
    exact ⟨[g.op.eval (g.inputs.map fun i => acc.getD i false)] ++ tail, by
      rw [htail, List.append_assoc]⟩

private lemma foldl_wires_length (gs : List Gate) (acc : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc).length =
      acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, List.length_append, List.length_singleton]
    omega

private lemma evalWires_length (gs : List Gate) (x : List Bool) :
    (evalWires gs x).length = x.length + gs.length :=
  foldl_wires_length gs x

private lemma evalWires_append (gs1 gs2 : List Gate) (x : List Bool) :
    evalWires (gs1 ++ gs2) x =
      gs2.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (evalWires gs1 x) := by
  unfold evalWires Circuit.wires
  exact List.foldl_append

private lemma evalWires_append_one (gs : List Gate) (g : Gate) (x : List Bool) :
    evalWires (gs ++ [g]) x = evalWires gs x ++ [g.op.eval (g.inputs.map (wireAt gs x))] := by
  rw [evalWires_append]
  rfl

private lemma wireAt_extends {gs1 gs2 : List Gate} (hext : Extends gs1 gs2)
    (x : List Bool) {w : ℕ} (hw : w < x.length + gs1.length) :
    wireAt gs2 x w = wireAt gs1 x w := by
  rcases hext with ⟨extra, rfl⟩
  unfold wireAt
  rw [evalWires_append]
  rcases foldl_wires_append extra (evalWires gs1 x) with ⟨tail, htail⟩
  rw [htail, getD_append_lt]
  rw [evalWires_length]
  exact hw

private lemma wireAt_append_one_last {inputs : ℕ} (gs : List Gate) (g : Gate)
    {x : List Bool} (hx : x.length = inputs) :
    wireAt (gs ++ [g]) x (inputs + gs.length) = g.op.eval (g.inputs.map (wireAt gs x)) := by
  unfold wireAt
  rw [evalWires_append_one]
  have hlen : (evalWires gs x).length = inputs + gs.length := by
    rw [evalWires_length, hx]
  rw [getD_append_ge _ _ (by omega), hlen, Nat.sub_self, List.getD_cons_zero]
  rfl

private lemma wireAt_input (gs : List Gate) (x : List Bool) {w : ℕ} (hw : w < x.length) :
    wireAt gs x w = x.getD w false := by
  have h := wireAt_extends (gs1 := []) (gs2 := gs) ⟨gs, rfl⟩ x (by simpa using hw)
  exact h

private lemma good_nil (inputs : ℕ) : Good inputs [] := by
  refine ⟨fun g hg => False.elim (List.not_mem_nil hg), fun j hj => False.elim (Nat.not_lt_zero j hj)⟩

private lemma good_append_one {inputs : ℕ} {gs : List Gate} (hG : Good inputs gs) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2)
    (hback : ∀ i ∈ g.inputs, i < inputs + gs.length) :
    Good inputs (gs ++ [g]) := by
  refine ⟨?_, ?_⟩
  · intro g' hg'
    rcases List.mem_append.mp hg' with h1 | h2
    · exact hG.1 g' h1
    · rw [List.mem_singleton.mp h2]
      exact ⟨hop, hlen⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hi
    dsimp only at hi
    by_cases hlt : j < gs.length
    · rw [getD_append_lt _ _ hlt] at hi
      exact hG.2 j hlt i hi
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [getD_append_ge _ _ le_rfl] at hi
      simp only [Nat.sub_self, List.getD_cons_zero] at hi
      exact hback i hi

private abbrev CG (α : Type) := List Gate → List Gate × α

private def addGate (inputs : ℕ) (g : Gate) : CG ℕ :=
  fun gs => (gs ++ [g], inputs + gs.length)

private def mkConst (inputs : ℕ) (c : Bool) : CG ℕ :=
  addGate inputs ⟨if c then GateOp.and else GateOp.or, []⟩

private def mkNot (inputs : ℕ) (u : ℕ) : CG ℕ :=
  addGate inputs ⟨GateOp.not, [u]⟩

private def mkAnd (inputs : ℕ) (u v : ℕ) : CG ℕ :=
  addGate inputs ⟨GateOp.and, [u, v]⟩

private def mkOr (inputs : ℕ) (u v : ℕ) : CG ℕ :=
  addGate inputs ⟨GateOp.or, [u, v]⟩

private def mkXor (inputs : ℕ) (u v : ℕ) : CG ℕ := fun gs =>
  let (gs1, o) := mkOr inputs u v gs
  let (gs2, a) := mkAnd inputs u v gs1
  let (gs3, na) := mkNot inputs a gs2
  mkAnd inputs o na gs3

private def mkMux (inputs : ℕ) (sel a b : ℕ) : CG ℕ := fun gs =>
  let (gs1, ns) := mkNot inputs sel gs
  let (gs2, x1) := mkAnd inputs sel a gs1
  let (gs3, x2) := mkAnd inputs ns b gs2
  mkOr inputs x1 x2 gs3

private lemma mkConst_spec {inputs : ℕ} (c : Bool) {gs : List Gate} (hG : Good inputs gs) :
    let res := mkConst inputs c gs
    Extends gs res.1 ∧ res.1.length = gs.length + 1 ∧ Good inputs res.1 ∧
    res.2 < inputs + res.1.length ∧
    ∀ x : List Bool, x.length = inputs → wireAt res.1 x res.2 = c := by
  have hop : (if c then GateOp.and else GateOp.or) ∈
      ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) := by
    cases c <;> simp
  refine ⟨⟨_, rfl⟩, by simp [mkConst, addGate],
    good_append_one hG _ hop (by simp) (by simp), by simp [mkConst, addGate], fun x hx => ?_⟩
  dsimp only [mkConst, addGate]
  rw [wireAt_append_one_last gs _ hx]
  cases c <;> simp [GateOp.eval]

private lemma mkNot_spec {inputs : ℕ} (u : ℕ) {gs : List Gate} (hG : Good inputs gs)
    (hu : u < inputs + gs.length) :
    let res := mkNot inputs u gs
    Extends gs res.1 ∧ res.1.length = gs.length + 1 ∧ Good inputs res.1 ∧
    res.2 < inputs + res.1.length ∧
    ∀ x : List Bool, x.length = inputs → wireAt res.1 x res.2 = !(wireAt gs x u) := by
  refine ⟨⟨_, rfl⟩, by simp [mkNot, addGate],
    good_append_one hG _ (by simp) (by simp) (by intro i hi; simp at hi; subst hi; exact hu),
    by simp [mkNot, addGate], fun x hx => ?_⟩
  dsimp only [mkNot, addGate]
  rw [wireAt_append_one_last gs _ hx]
  rfl

private lemma mkAnd_spec {inputs : ℕ} (u v : ℕ) {gs : List Gate} (hG : Good inputs gs)
    (hu : u < inputs + gs.length) (hv : v < inputs + gs.length) :
    let res := mkAnd inputs u v gs
    Extends gs res.1 ∧ res.1.length = gs.length + 1 ∧ Good inputs res.1 ∧
    res.2 < inputs + res.1.length ∧
    ∀ x : List Bool, x.length = inputs → wireAt res.1 x res.2 = (wireAt gs x u && wireAt gs x v) := by
  refine ⟨⟨_, rfl⟩, by simp [mkAnd, addGate],
    good_append_one hG _ (by simp) (by simp) (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption),
    by simp [mkAnd, addGate], fun x hx => ?_⟩
  dsimp only [mkAnd, addGate]
  rw [wireAt_append_one_last gs _ hx]
  simp [GateOp.eval]

private lemma mkOr_spec {inputs : ℕ} (u v : ℕ) {gs : List Gate} (hG : Good inputs gs)
    (hu : u < inputs + gs.length) (hv : v < inputs + gs.length) :
    let res := mkOr inputs u v gs
    Extends gs res.1 ∧ res.1.length = gs.length + 1 ∧ Good inputs res.1 ∧
    res.2 < inputs + res.1.length ∧
    ∀ x : List Bool, x.length = inputs → wireAt res.1 x res.2 = (wireAt gs x u || wireAt gs x v) := by
  refine ⟨⟨_, rfl⟩, by simp [mkOr, addGate],
    good_append_one hG _ (by simp) (by simp) (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption),
    by simp [mkOr, addGate], fun x hx => ?_⟩
  dsimp only [mkOr, addGate]
  rw [wireAt_append_one_last gs _ hx]
  simp [GateOp.eval]

private lemma mkXor_spec {inputs : ℕ} (u v : ℕ) {gs : List Gate} (hG : Good inputs gs)
    (hu : u < inputs + gs.length) (hv : v < inputs + gs.length) :
    let res := mkXor inputs u v gs
    Extends gs res.1 ∧ res.1.length = gs.length + 4 ∧ Good inputs res.1 ∧
    res.2 < inputs + res.1.length ∧
    ∀ x : List Bool, x.length = inputs → wireAt res.1 x res.2 = xor (wireAt gs x u) (wireAt gs x v) := by
  rcases h1 : mkOr inputs u v gs with ⟨gs1, o⟩
  have s1 := mkOr_spec u v hG hu hv
  simp only [h1] at s1
  rcases s1 with ⟨e1, l1, g1, wo, ev1⟩
  rcases h2 : mkAnd inputs u v gs1 with ⟨gs2, a⟩
  have s2 := mkAnd_spec u v g1 (by omega) (by omega)
  simp only [h2] at s2
  rcases s2 with ⟨e2, l2, g2, wa, ev2⟩
  rcases h3 : mkNot inputs a gs2 with ⟨gs3, na⟩
  have s3 := mkNot_spec a g2 wa
  simp only [h3] at s3
  rcases s3 with ⟨e3, l3, g3, wna, ev3⟩
  rcases h4 : mkAnd inputs o na gs3 with ⟨gs4, out⟩
  have s4 := mkAnd_spec o na g3 (by omega) wna
  simp only [h4] at s4
  rcases s4 with ⟨e4, l4, g4, wout, ev4⟩
  have hres : mkXor inputs u v gs = (gs4, out) := by
    simp only [mkXor, h1, h2, h3, h4]
  simp only [hres]
  refine ⟨extends_trans e1 (extends_trans e2 (extends_trans e3 e4)), by omega, g4, wout, fun x hx => ?_⟩
  rw [ev4 x hx, wireAt_extends (extends_trans e2 e3) x (by omega), ev1 x hx, ev3 x hx, ev2 x hx,
    wireAt_extends e1 x (by omega), wireAt_extends e1 x (by omega)]
  cases wireAt gs x u <;> cases wireAt gs x v <;> decide

private lemma mkMux_spec {inputs : ℕ} (sel a b : ℕ) {gs : List Gate} (hG : Good inputs gs)
    (hs : sel < inputs + gs.length) (ha : a < inputs + gs.length) (hb : b < inputs + gs.length) :
    let res := mkMux inputs sel a b gs
    Extends gs res.1 ∧ res.1.length = gs.length + 4 ∧ Good inputs res.1 ∧
    res.2 < inputs + res.1.length ∧
    ∀ x : List Bool, x.length = inputs →
      wireAt res.1 x res.2 = if wireAt gs x sel then wireAt gs x a else wireAt gs x b := by
  rcases h1 : mkNot inputs sel gs with ⟨gs1, ns⟩
  have s1 := mkNot_spec sel hG hs
  simp only [h1] at s1
  rcases s1 with ⟨e1, l1, g1, wns, ev1⟩
  rcases h2 : mkAnd inputs sel a gs1 with ⟨gs2, x1⟩
  have s2 := mkAnd_spec sel a g1 (by omega) (by omega)
  simp only [h2] at s2
  rcases s2 with ⟨e2, l2, g2, wx1, ev2⟩
  rcases h3 : mkAnd inputs ns b gs2 with ⟨gs3, x2⟩
  have s3 := mkAnd_spec ns b g2 (by omega) (by omega)
  simp only [h3] at s3
  rcases s3 with ⟨e3, l3, g3, wx2, ev3⟩
  rcases h4 : mkOr inputs x1 x2 gs3 with ⟨gs4, out⟩
  have s4 := mkOr_spec x1 x2 g3 (by omega) wx2
  simp only [h4] at s4
  rcases s4 with ⟨e4, l4, g4, wout, ev4⟩
  have hres : mkMux inputs sel a b gs = (gs4, out) := by
    simp only [mkMux, h1, h2, h3, h4]
  simp only [hres]
  refine ⟨extends_trans e1 (extends_trans e2 (extends_trans e3 e4)), by omega, g4, wout, fun x hx => ?_⟩
  rw [ev4 x hx, wireAt_extends e3 x (by omega), ev2 x hx, ev3 x hx,
    wireAt_extends e2 x (by omega), ev1 x hx,
    wireAt_extends e1 x (by omega), wireAt_extends e1 x (by omega),
    wireAt_extends (extends_trans e1 e2) x (by omega)]
  cases wireAt gs x sel <;> cases wireAt gs x a <;> cases wireAt gs x b <;> decide

private def mkListOr (inputs : ℕ) : List ℕ → CG ℕ
  | [], gs => (gs, 0)
  | w :: ws, gs =>
    let (gs1, r) := mkListOr inputs ws gs
    mkOr inputs w r gs1

private lemma mkListOr_spec {inputs : ℕ} (h0 : 0 < inputs) (ws : List ℕ)
    {gs : List Gate} (hG : Good inputs gs) (hws : ∀ w ∈ ws, w < inputs + gs.length) :
    let res := mkListOr inputs ws gs
    Extends gs res.1 ∧ res.1.length = gs.length + ws.length ∧ Good inputs res.1 ∧
    res.2 < inputs + res.1.length ∧
    ∀ x : List Bool, x.length = inputs → x.getD 0 false = false →
      wireAt res.1 x res.2 = ws.any (wireAt gs x) := by
  induction ws with
  | nil =>
    refine ⟨extends_refl gs, by simp [mkListOr], hG, by simp [mkListOr]; omega, fun x hx hx0 => ?_⟩
    dsimp only [mkListOr]
    rw [wireAt_input gs x (by omega), hx0]
    rfl
  | cons w ws ih =>
    rcases h1 : mkListOr inputs ws gs with ⟨gs1, r⟩
    have s1 := ih (fun u hu => hws u (List.mem_cons_of_mem w hu))
    simp only [h1] at s1
    rcases s1 with ⟨e1, l1, g1, wr, ev1⟩
    have hw : w < inputs + gs.length := hws w List.mem_cons_self
    rcases h2 : mkOr inputs w r gs1 with ⟨gs2, out⟩
    have s2 := mkOr_spec w r g1 (by omega) wr
    simp only [h2] at s2
    rcases s2 with ⟨e2, l2, g2, wout, ev2⟩
    have hres : mkListOr inputs (w :: ws) gs = (gs2, out) := by
      simp only [mkListOr, h1, h2]
    simp only [hres]
    refine ⟨extends_trans e1 e2, by simp; omega, g2, wout, fun x hx hx0 => ?_⟩
    rw [ev2 x hx, wireAt_extends e1 x (by omega), ev1 x hx hx0]
    rfl

private def mkListAnd (inputs : ℕ) : List ℕ → CG ℕ
  | [], gs => mkConst inputs true gs
  | w :: ws, gs =>
    let (gs1, r) := mkListAnd inputs ws gs
    mkAnd inputs w r gs1

private lemma mkListAnd_spec {inputs : ℕ} (ws : List ℕ)
    {gs : List Gate} (hG : Good inputs gs) (hws : ∀ w ∈ ws, w < inputs + gs.length) :
    let res := mkListAnd inputs ws gs
    Extends gs res.1 ∧ res.1.length = gs.length + (ws.length + 1) ∧ Good inputs res.1 ∧
    res.2 < inputs + res.1.length ∧
    ∀ x : List Bool, x.length = inputs → wireAt res.1 x res.2 = ws.all (wireAt gs x) := by
  induction ws with
  | nil =>
    simpa [mkListAnd] using mkConst_spec true hG
  | cons w ws ih =>
    rcases h1 : mkListAnd inputs ws gs with ⟨gs1, r⟩
    have s1 := ih (fun u hu => hws u (List.mem_cons_of_mem w hu))
    simp only [h1] at s1
    rcases s1 with ⟨e1, l1, g1, wr, ev1⟩
    have hw : w < inputs + gs.length := hws w List.mem_cons_self
    rcases h2 : mkAnd inputs w r gs1 with ⟨gs2, out⟩
    have s2 := mkAnd_spec w r g1 (by omega) wr
    simp only [h2] at s2
    rcases s2 with ⟨e2, l2, g2, wout, ev2⟩
    have hres : mkListAnd inputs (w :: ws) gs = (gs2, out) := by
      simp only [mkListAnd, h1, h2]
    simp only [hres]
    refine ⟨extends_trans e1 e2, by simp; omega, g2, wout, fun x hx => ?_⟩
    rw [ev2 x hx, wireAt_extends e1 x (by omega), ev1 x hx]
    rfl

private def mkListXor (inputs : ℕ) : List ℕ → CG ℕ
  | [], gs => (gs, 0)
  | w :: ws, gs =>
    let (gs1, r) := mkListXor inputs ws gs
    mkXor inputs w r gs1

private lemma mkListXor_spec {inputs : ℕ} (h0 : 0 < inputs) (ws : List ℕ)
    {gs : List Gate} (hG : Good inputs gs) (hws : ∀ w ∈ ws, w < inputs + gs.length) :
    let res := mkListXor inputs ws gs
    Extends gs res.1 ∧ res.1.length = gs.length + 4 * ws.length ∧ Good inputs res.1 ∧
    res.2 < inputs + res.1.length ∧
    ∀ x : List Bool, x.length = inputs → x.getD 0 false = false →
      b2z (wireAt res.1 x res.2) = (ws.map (fun w => b2z (wireAt gs x w))).sum := by
  induction ws with
  | nil =>
    refine ⟨extends_refl gs, by simp [mkListXor], hG, by simp [mkListXor]; omega, fun x hx hx0 => ?_⟩
    dsimp only [mkListXor]
    rw [wireAt_input gs x (by omega), hx0]
    rfl
  | cons w ws ih =>
    rcases h1 : mkListXor inputs ws gs with ⟨gs1, r⟩
    have s1 := ih (fun u hu => hws u (List.mem_cons_of_mem w hu))
    simp only [h1] at s1
    rcases s1 with ⟨e1, l1, g1, wr, ev1⟩
    have hw : w < inputs + gs.length := hws w List.mem_cons_self
    rcases h2 : mkXor inputs w r gs1 with ⟨gs2, out⟩
    have s2 := mkXor_spec w r g1 (by omega) wr
    simp only [h2] at s2
    rcases s2 with ⟨e2, l2, g2, wout, ev2⟩
    have hres : mkListXor inputs (w :: ws) gs = (gs2, out) := by
      simp only [mkListXor, h1, h2]
    simp only [hres]
    refine ⟨extends_trans e1 e2, by simp; omega, g2, wout, fun x hx hx0 => ?_⟩
    rw [ev2 x hx, b2z_xor, wireAt_extends e1 x (by omega), ev1 x hx hx0]
    simp

private def mkVec {α : Type} : ∀ (m : ℕ), (Fin m → CG α) → CG (Fin m → α)
  | 0, _, gs => (gs, Fin.elim0)
  | m + 1, f, gs =>
    let (gs1, prev) := mkVec m (fun i => f i.castSucc) gs
    let (gs2, last) := f (Fin.last m) gs1
    (gs2, Fin.snoc prev last)

private lemma mkVec_spec {inputs m cost : ℕ} {α β : Type}
    (WValid : ℕ → α → Prop)
    (hmono : ∀ L1 L2 a, L1 ≤ L2 → WValid L1 a → WValid L2 a)
    (WSem : List Gate → List Bool → α → β → Prop)
    (hextSem : ∀ gs1 gs2 x a b, x.length = inputs → Extends gs1 gs2 →
      WValid (inputs + gs1.length) a → WSem gs1 x a b → WSem gs2 x a b)
    (f : Fin m → CG α) (target : List Bool → Fin m → β)
    {gs0 : List Gate} (hG0 : Good inputs gs0)
    (hf : ∀ (i : Fin m) (gs : List Gate), Good inputs gs → Extends gs0 gs →
      let r := f i gs
      Extends gs r.1 ∧ r.1.length ≤ gs.length + cost ∧ Good inputs r.1 ∧
      WValid (inputs + r.1.length) r.2 ∧
      ∀ x : List Bool, x.length = inputs → x.getD 0 false = false → WSem r.1 x r.2 (target x i)) :
    let res := mkVec m f gs0
    Extends gs0 res.1 ∧ res.1.length ≤ gs0.length + m * cost ∧ Good inputs res.1 ∧
    (∀ i : Fin m, WValid (inputs + res.1.length) (res.2 i)) ∧
    ∀ x : List Bool, x.length = inputs → x.getD 0 false = false →
      ∀ i : Fin m, WSem res.1 x (res.2 i) (target x i) := by
  induction m with
  | zero =>
    refine ⟨extends_refl gs0, by simp [mkVec], hG0, fun i => i.elim0, fun _ _ _ i => i.elim0⟩
  | succ m ih =>
    rcases h1 : mkVec m (fun i => f i.castSucc) gs0 with ⟨gs1, prev⟩
    have s1 := ih (fun i => f i.castSucc) (fun x i => target x i.castSucc)
      (fun i gs hG hE => hf i.castSucc gs hG hE)
    simp only [h1] at s1
    rcases s1 with ⟨e1, l1, g1, v1, sem1⟩
    rcases h2 : f (Fin.last m) gs1 with ⟨gs2, last⟩
    have s2 := hf (Fin.last m) gs1 g1 e1
    simp only [h2] at s2
    rcases s2 with ⟨e2, l2, g2, v2, sem2⟩
    have hres : mkVec (m + 1) f gs0 = (gs2, Fin.snoc prev last) := by
      simp only [mkVec, h1, h2]
    simp only [hres]
    have hlen12 : gs1.length ≤ gs2.length := extends_length_le e2
    refine ⟨extends_trans e1 e2, ?_, g2, ?_, ?_⟩
    · have : (m + 1) * cost = m * cost + cost := Nat.succ_mul m cost
      omega
    · intro i
      refine Fin.lastCases ?_ ?_ i
      · simpa [Fin.snoc] using v2
      · intro j; simpa [Fin.snoc] using hmono _ _ _ (by omega) (v1 j)
    · intro x hx hx0 i
      refine Fin.lastCases ?_ ?_ i
      · simpa [Fin.snoc] using sem2 x hx hx0
      · intro j
        simpa [Fin.snoc] using hextSem gs1 gs2 x (prev j) (target x j.castSucc) hx e2 (v1 j) (sem1 x hx hx0 j)

private def mkIter {α : Type} : ∀ (m : ℕ), (Fin m → α → CG α) → α → CG α
  | 0, _, a, gs => (gs, a)
  | m + 1, f, a, gs =>
    let (gs1, prev) := mkIter m (fun i => f i.castSucc) a gs
    f (Fin.last m) prev gs1

private lemma mkIter_spec {inputs m cost : ℕ} {α β : Type}
    (WValid : ℕ → α → Prop)
    (WSem : List Gate → List Bool → α → β → Prop)
    (f : Fin m → α → CG α) (pf : List Bool → Fin m → β → β)
    (a0 : α) (b0 : List Bool → β)
    {gs0 : List Gate} (hG0 : Good inputs gs0)
    (ha0 : WValid (inputs + gs0.length) a0)
    (hsem0 : ∀ x : List Bool, x.length = inputs → x.getD 0 false = false → WSem gs0 x a0 (b0 x))
    (hf : ∀ (i : Fin m) (gs : List Gate) (a : α),
      Good inputs gs → Extends gs0 gs → WValid (inputs + gs.length) a →
      ∀ (b : List Bool → β),
      (∀ x : List Bool, x.length = inputs → x.getD 0 false = false → WSem gs x a (b x)) →
      let r := f i a gs
      Extends gs r.1 ∧ r.1.length ≤ gs.length + cost ∧ Good inputs r.1 ∧
      WValid (inputs + r.1.length) r.2 ∧
      ∀ x : List Bool, x.length = inputs → x.getD 0 false = false → WSem r.1 x r.2 (pf x i (b x))) :
    let res := mkIter m f a0 gs0
    Extends gs0 res.1 ∧ res.1.length ≤ gs0.length + m * cost ∧ Good inputs res.1 ∧
    WValid (inputs + res.1.length) res.2 ∧
    ∀ x : List Bool, x.length = inputs → x.getD 0 false = false →
      WSem res.1 x res.2 (iterFin m (pf x) (b0 x)) := by
  induction m with
  | zero =>
    exact ⟨extends_refl gs0, by simp [mkIter], hG0, ha0, hsem0⟩
  | succ m ih =>
    rcases h1 : mkIter m (fun i => f i.castSucc) a0 gs0 with ⟨gs1, prev⟩
    have s1 := ih (fun i => f i.castSucc) (fun x i => pf x i.castSucc)
      (fun i gs a hG hE hV b hS => hf i.castSucc gs a hG hE hV b hS)
    simp only [h1] at s1
    rcases s1 with ⟨e1, l1, g1, v1, sem1⟩
    rcases h2 : f (Fin.last m) prev gs1 with ⟨gs2, out⟩
    have s2 := hf (Fin.last m) gs1 prev g1 e1 v1 (fun x => iterFin m (fun i => pf x i.castSucc) (b0 x)) sem1
    simp only [h2] at s2
    rcases s2 with ⟨e2, l2, g2, v2, sem2⟩
    have hres : mkIter (m + 1) f a0 gs0 = (gs2, out) := by
      simp only [mkIter, h1, h2]
    simp only [hres]
    refine ⟨extends_trans e1 e2, ?_, g2, v2, sem2⟩
    have : (m + 1) * cost = m * cost + cost := Nat.succ_mul m cost
    omega

private def VecValid {m : ℕ} (L : ℕ) (v : Fin m → ℕ) : Prop := ∀ i, v i < L

private def MatValid {m k : ℕ} (L : ℕ) (M : Fin m → Fin k → ℕ) : Prop := ∀ r j, M r j < L

private def VecZSem {m : ℕ} (gs : List Gate) (x : List Bool) (vW : Fin m → ℕ) (v : Fin m → ZMod 2) : Prop :=
  ∀ i, b2z (wireAt gs x (vW i)) = v i

private def MatZSem {m k : ℕ} (gs : List Gate) (x : List Bool) (MW : Fin m → Fin k → ℕ)
    (M : Fin m → Fin k → ZMod 2) : Prop :=
  ∀ r j, b2z (wireAt gs x (MW r j)) = M r j

private def VecBSem {m : ℕ} (gs : List Gate) (x : List Bool) (vW : Fin m → ℕ) (v : Fin m → Bool) : Prop :=
  ∀ i, wireAt gs x (vW i) = v i

private lemma wireSem_ext {inputs : ℕ} (gs1 gs2 : List Gate) (x : List Bool) (w : ℕ) (b : Bool)
    (hx : x.length = inputs) (he : Extends gs1 gs2) (hw : w < inputs + gs1.length)
    (hs : wireAt gs1 x w = b) : wireAt gs2 x w = b := by
  rw [wireAt_extends he x (by omega), hs]

private lemma wireZSem_ext {inputs : ℕ} (gs1 gs2 : List Gate) (x : List Bool) (w : ℕ) (z : ZMod 2)
    (hx : x.length = inputs) (he : Extends gs1 gs2) (hw : w < inputs + gs1.length)
    (hs : b2z (wireAt gs1 x w) = z) : b2z (wireAt gs2 x w) = z := by
  rw [wireAt_extends he x (by omega), hs]

private lemma vecZSem_ext {inputs m : ℕ} (gs1 gs2 : List Gate) (x : List Bool)
    (vW : Fin m → ℕ) (v : Fin m → ZMod 2)
    (hx : x.length = inputs) (he : Extends gs1 gs2) (hv : VecValid (inputs + gs1.length) vW)
    (hs : VecZSem gs1 x vW v) : VecZSem gs2 x vW v := fun i =>
  wireZSem_ext gs1 gs2 x (vW i) (v i) hx he (hv i) (hs i)

private lemma matZSem_ext {inputs m k : ℕ} (gs1 gs2 : List Gate) (x : List Bool)
    (MW : Fin m → Fin k → ℕ) (M : Fin m → Fin k → ZMod 2)
    (hx : x.length = inputs) (he : Extends gs1 gs2) (hM : MatValid (inputs + gs1.length) MW)
    (hs : MatZSem gs1 x MW M) : MatZSem gs2 x MW M := fun r j =>
  wireZSem_ext gs1 gs2 x (MW r j) (M r j) hx he (hM r j) (hs r j)

private def mkDot (inputs n : ℕ) (u v : Fin n → ℕ) : CG ℕ := fun gs =>
  let (gs1, prods) := mkVec n (fun i => mkAnd inputs (u i) (v i)) gs
  mkListXor inputs (List.ofFn prods) gs1

private lemma mkDot_spec {inputs n : ℕ} (h0 : 0 < inputs) (u v : Fin n → ℕ)
    {gs : List Gate} (hG : Good inputs gs)
    (hu : VecValid (inputs + gs.length) u) (hv : VecValid (inputs + gs.length) v) :
    let res := mkDot inputs n u v gs
    Extends gs res.1 ∧ res.1.length ≤ gs.length + 5 * n ∧ Good inputs res.1 ∧
    res.2 < inputs + res.1.length ∧
    ∀ x : List Bool, x.length = inputs → x.getD 0 false = false →
      b2z (wireAt res.1 x res.2) = ∑ i : Fin n, b2z (wireAt gs x (u i)) * b2z (wireAt gs x (v i)) := by
  rcases h1 : mkVec n (fun i => mkAnd inputs (u i) (v i)) gs with ⟨gs1, prods⟩
  have s1 := mkVec_spec (inputs := inputs) (cost := 1)
    (WValid := fun L w => w < L) (fun _ _ _ hle hw => lt_of_lt_of_le hw hle)
    (WSem := fun g x w b => wireAt g x w = b)
    (fun g1 g2 x w b hx he hw hs => wireSem_ext g1 g2 x w b hx he hw hs)
    (fun i => mkAnd inputs (u i) (v i))
    (fun x i => wireAt gs x (u i) && wireAt gs x (v i)) hG
    (fun i g hg he => by
      have hlen := extends_length_le he
      have hui := hu i
      have hvi := hv i
      rcases mkAnd_spec (u i) (v i) hg (lt_of_lt_of_le hui (by omega)) (lt_of_lt_of_le hvi (by omega)) with
        ⟨e, l, g', w', ev⟩
      refine ⟨e, by omega, g', w', fun x hx _ => ?_⟩
      rw [ev x hx, wireAt_extends he x (by omega), wireAt_extends he x (by omega)])
  simp only [h1] at s1
  rcases s1 with ⟨e1, l1, g1, vp, semp⟩
  rcases h2 : mkListXor inputs (List.ofFn prods) gs1 with ⟨gs2, out⟩
  have hmem : ∀ w ∈ List.ofFn prods, w < inputs + gs1.length := by
    intro w hw
    rcases List.mem_ofFn.mp hw with ⟨i, rfl⟩
    exact vp i
  have s2 := mkListXor_spec h0 (List.ofFn prods) g1 hmem
  simp only [h2] at s2
  rcases s2 with ⟨e2, l2, g2, wout, ev2⟩
  have hres : mkDot inputs n u v gs = (gs2, out) := by
    simp only [mkDot, h1, h2]
  simp only [hres]
  refine ⟨extends_trans e1 e2, by rw [List.length_ofFn] at l2; omega, g2, wout, fun x hx hx0 => ?_⟩
  rw [ev2 x hx hx0, List.map_ofFn, List.sum_ofFn]
  refine Finset.sum_congr rfl fun i _ => ?_
  dsimp only [Function.comp]
  rw [semp x hx hx0 i, b2z_and]

private def mkFirstOk (inputs n : ℕ) (okW : Fin n → ℕ) : CG (Fin n → ℕ) :=
  mkVec n (fun m gs =>
    let prevW := ((List.finRange n).filter (fun m' => decide (m'.val < m.val))).map okW
    let (gs1, anyPrev) := mkListOr inputs prevW gs
    let (gs2, noPrev) := mkNot inputs anyPrev gs1
    mkAnd inputs (okW m) noPrev gs2)

private lemma mkFirstOk_spec {inputs n : ℕ} (h0 : 0 < inputs) (okW : Fin n → ℕ)
    {gs : List Gate} (hG : Good inputs gs) (hok : VecValid (inputs + gs.length) okW) :
    let res := mkFirstOk inputs n okW gs
    Extends gs res.1 ∧ res.1.length ≤ gs.length + n * (n + 2) ∧ Good inputs res.1 ∧
    VecValid (inputs + res.1.length) res.2 ∧
    ∀ x : List Bool, x.length = inputs → x.getD 0 false = false →
      VecBSem res.1 x res.2 (firstOk (fun c => wireAt gs x (okW c))) := by
  refine mkVec_spec (inputs := inputs) (cost := n + 2)
    (WValid := fun L w => w < L) (fun _ _ _ hle hw => lt_of_lt_of_le hw hle)
    (WSem := fun g x w b => wireAt g x w = b)
    (fun g1 g2 x w b hx he hw hs => wireSem_ext g1 g2 x w b hx he hw hs)
    (fun m g =>
      let prevW := ((List.finRange n).filter (fun m' => decide (m'.val < m.val))).map okW
      let (g1, anyPrev) := mkListOr inputs prevW g
      let (g2, noPrev) := mkNot inputs anyPrev g1
      mkAnd inputs (okW m) noPrev g2)
    (fun x m => firstOk (fun c => wireAt gs x (okW c)) m) hG ?_
  intro m g hg he
  have hlen := extends_length_le he
  set prevL := (List.finRange n).filter (fun m' => decide (m'.val < m.val))
  set prevW := prevL.map okW
  have hplen : prevW.length ≤ n := by
    calc prevW.length = prevL.length := List.length_map _
      _ ≤ (List.finRange n).length := List.length_filter_le _ _
      _ = n := List.length_finRange
  have hpv : ∀ w ∈ prevW, w < inputs + g.length := by
    intro w hw
    rcases List.mem_map.mp hw with ⟨m', _, rfl⟩
    exact lt_of_lt_of_le (hok m') (by omega)
  rcases h1 : mkListOr inputs prevW g with ⟨g1, anyPrev⟩
  have s1 := mkListOr_spec h0 prevW hg hpv
  simp only [h1] at s1
  rcases s1 with ⟨e1, l1, g1G, w1, ev1⟩
  rcases h2 : mkNot inputs anyPrev g1 with ⟨g2, noPrev⟩
  have s2 := mkNot_spec anyPrev g1G w1
  simp only [h2] at s2
  rcases s2 with ⟨e2, l2, g2G, w2, ev2⟩
  rcases h3 : mkAnd inputs (okW m) noPrev g2 with ⟨g3, out⟩
  have hokm : okW m < inputs + g2.length := lt_of_lt_of_le (hok m) (by omega)
  have s3 := mkAnd_spec (okW m) noPrev g2G hokm w2
  simp only [h3] at s3
  rcases s3 with ⟨e3, l3, g3G, w3, ev3⟩
  dsimp only
  simp only [h1, h2, h3]
  refine ⟨extends_trans e1 (extends_trans e2 e3), by omega, g3G, w3, fun x hx hx0 => ?_⟩
  have hokm0 := hok m
  rw [ev3 x hx, wireAt_extends (extends_trans he (extends_trans e1 e2)) x (by omega),
    ev2 x hx, ev1 x hx hx0]
  unfold firstOk
  congr 2
  rw [List.any_map]
  have hfn : (wireAt g x ∘ okW) = fun c => wireAt gs x (okW c) := by
    funext c
    have hokc := hok c
    exact wireAt_extends he x (by omega)
  rw [hfn]

private def mkInsertRow (inputs n : ℕ) (T : Fin n → Fin n → ℕ) (w : Fin n → ℕ) :
    CG (Fin n → Fin n → ℕ) := fun gs =>
  let (gs1, w') := mkVec n (fun j gs' =>
    let (g1, d) := mkDot inputs n w (fun c => T c j) gs'
    mkXor inputs (w j) d g1) gs
  let (gs2, piv) := mkFirstOk inputs n w' gs1
  let (gs3, hit) := mkVec n (fun r => mkDot inputs n piv (T r)) gs2
  mkVec n (fun r => mkVec n (fun j gs' =>
    let (g1, hw) := mkAnd inputs (hit r) (w' j) gs'
    let (g2, upd) := mkXor inputs (T r j) hw g1
    mkMux inputs (piv r) (w' j) upd g2)) gs3

private lemma mkInsertRow_spec {inputs n : ℕ} (h0 : 0 < inputs)
    (T : Fin n → Fin n → ℕ) (w : Fin n → ℕ)
    {gs : List Gate} (hG : Good inputs gs)
    (hT : MatValid (inputs + gs.length) T) (hw : VecValid (inputs + gs.length) w) :
    let res := mkInsertRow inputs n T w gs
    Extends gs res.1 ∧ res.1.length ≤ gs.length + 26 * (n + 1) ^ 2 ∧ Good inputs res.1 ∧
    MatValid (inputs + res.1.length) res.2 ∧
    ∀ x : List Bool, x.length = inputs → x.getD 0 false = false →
      MatZSem res.1 x res.2
        (insertRow (fun r j => b2z (wireAt gs x (T r j))) (fun j => b2z (wireAt gs x (w j)))) := by
  rcases h1 : mkVec n (fun j gs' =>
      let (g1, d) := mkDot inputs n w (fun c => T c j) gs'
      mkXor inputs (w j) d g1) gs with ⟨gs1, w'⟩
  have s1 := mkVec_spec (inputs := inputs) (cost := 5 * n + 4)
    (WValid := fun L u => u < L) (fun _ _ _ hle hu => lt_of_lt_of_le hu hle)
    (WSem := fun g x u z => b2z (wireAt g x u) = z)
    (fun g1 g2 x u z hx he hu hs => wireZSem_ext g1 g2 x u z hx he hu hs)
    (fun j gs' =>
      let (g1, d) := mkDot inputs n w (fun c => T c j) gs'
      mkXor inputs (w j) d g1)
    (fun x j => reduceVec (fun r c => b2z (wireAt gs x (T r c))) (fun c => b2z (wireAt gs x (w c))) j) hG
    (fun j g hg he => by
      have hlen := extends_length_le he
      rcases hd : mkDot inputs n w (fun c => T c j) g with ⟨g1, d⟩
      have sd := mkDot_spec h0 w (fun c => T c j) hg
        (fun c => lt_of_lt_of_le (hw c) (by omega))
        (fun c => lt_of_lt_of_le (hT c j) (by omega))
      simp only [hd] at sd
      rcases sd with ⟨ed, ld, gd, wd, evd⟩
      have hlend := extends_length_le ed
      rcases hx0 : mkXor inputs (w j) d g1 with ⟨g2, out⟩
      have sx := mkXor_spec (w j) d gd (lt_of_lt_of_le (hw j) (by omega)) wd
      simp only [hx0] at sx
      rcases sx with ⟨ex, lx, gx, wx, evx⟩
      simp only [hx0]
      refine ⟨extends_trans ed ex, by omega, gx, wx, fun x hx h0x => ?_⟩
      have hwj := hw j
      rw [evx x hx, b2z_xor, wireAt_extends (extends_trans he ed) x (by omega), evd x hx h0x]
      unfold reduceVec
      congr 1
      refine Finset.sum_congr rfl fun c _ => ?_
      have hwc := hw c
      have hTcj := hT c j
      rw [wireAt_extends he x (by omega), wireAt_extends he x (by omega)])
  simp only [h1] at s1
  rcases s1 with ⟨e1, l1, g1, vw', semw'⟩
  rcases h2 : mkFirstOk inputs n w' gs1 with ⟨gs2, piv⟩
  have s2 := mkFirstOk_spec h0 w' g1 vw'
  simp only [h2] at s2
  rcases s2 with ⟨e2, l2, g2, vpiv, sempiv⟩
  rcases h3 : mkVec n (fun r => mkDot inputs n piv (T r)) gs2 with ⟨gs3, hit⟩
  have hlen1 := extends_length_le e1
  have hlen2 := extends_length_le e2
  have s3 := mkVec_spec (inputs := inputs) (cost := 5 * n)
    (WValid := fun L u => u < L) (fun _ _ _ hle hu => lt_of_lt_of_le hu hle)
    (WSem := fun g x u z => b2z (wireAt g x u) = z)
    (fun g1 g2 x u z hx he hu hs => wireZSem_ext g1 g2 x u z hx he hu hs)
    (fun r => mkDot inputs n piv (T r))
    (fun x r => ∑ p : Fin n, b2z (firstOk (fun c => z2b (reduceVec
      (fun a b => b2z (wireAt gs x (T a b))) (fun a => b2z (wireAt gs x (w a))) c)) p) *
      b2z (wireAt gs x (T r p))) g2
    (fun r g hg he => by
      have hle := extends_length_le he
      rcases hd : mkDot inputs n piv (T r) g with ⟨g', d⟩
      have sd := mkDot_spec h0 piv (T r) hg
        (fun p => lt_of_lt_of_le (vpiv p) (by omega))
        (fun p => lt_of_lt_of_le (hT r p) (by omega))
      simp only [hd] at sd
      rcases sd with ⟨ed, ld, gd, wd, evd⟩
      refine ⟨ed, ld, gd, wd, fun x hx h0x => ?_⟩
      rw [evd x hx h0x]
      refine Finset.sum_congr rfl fun p _ => ?_
      have hvp := vpiv p
      have hTrp := hT r p
      rw [wireAt_extends he x (by omega), sempiv x hx h0x p,
        wireAt_extends (extends_trans e1 (extends_trans e2 he)) x (by omega)]
      have hfn : (fun c => wireAt gs1 x (w' c)) =
          (fun c => z2b (reduceVec (fun a b => b2z (wireAt gs x (T a b)))
            (fun a => b2z (wireAt gs x (w a))) c)) := by
        funext c
        rw [← semw' x hx h0x c, z2b_b2z]
      rw [hfn])
  simp only [h3] at s3
  rcases s3 with ⟨e3, l3, g3, vhit, semhit⟩
  have hlen3 := extends_length_le e3
  rcases h4 : mkVec n (fun r => mkVec n (fun j gs' =>
      let (g1, hw0) := mkAnd inputs (hit r) (w' j) gs'
      let (g2, upd) := mkXor inputs (T r j) hw0 g1
      mkMux inputs (piv r) (w' j) upd g2)) gs3 with ⟨gs4, T'⟩
  have s4 := mkVec_spec (inputs := inputs) (cost := n * 9)
    (WValid := fun L v => VecValid L v)
    (fun _ _ _ hle hv j => lt_of_lt_of_le (hv j) hle)
    (WSem := fun g x vW v => VecZSem g x vW v)
    (fun g1 g2 x vW v hx he hv hs => vecZSem_ext g1 g2 x vW v hx he hv hs)
    (fun r => mkVec n (fun j gs' =>
      let (g1, hw0) := mkAnd inputs (hit r) (w' j) gs'
      let (g2, upd) := mkXor inputs (T r j) hw0 g1
      mkMux inputs (piv r) (w' j) upd g2))
    (fun x r => insertRow (fun a b => b2z (wireAt gs x (T a b)))
      (fun a => b2z (wireAt gs x (w a))) r) g3
    (fun r g hg he => by
      have hle := extends_length_le he
      refine mkVec_spec (inputs := inputs) (cost := 9)
        (WValid := fun L u => u < L) (fun _ _ _ hle' hu => lt_of_lt_of_le hu hle')
        (WSem := fun g' x u z => b2z (wireAt g' x u) = z)
        (fun g1 g2 x u z hx he' hu hs => wireZSem_ext g1 g2 x u z hx he' hu hs)
        (fun j gs' =>
          let (g1, hw0) := mkAnd inputs (hit r) (w' j) gs'
          let (g2, upd) := mkXor inputs (T r j) hw0 g1
          mkMux inputs (piv r) (w' j) upd g2)
        (fun x j => insertRow (fun a b => b2z (wireAt gs x (T a b)))
          (fun a => b2z (wireAt gs x (w a))) r j) hg ?_
      intro j g' hg' he'
      have hle' := extends_length_le he'
      rcases ha : mkAnd inputs (hit r) (w' j) g' with ⟨ga, hw0⟩
      have sa := mkAnd_spec (hit r) (w' j) hg' (lt_of_lt_of_le (vhit r) (by omega))
        (lt_of_lt_of_le (vw' j) (by omega))
      simp only [ha] at sa
      rcases sa with ⟨ea, la, gaG, wa, eva⟩
      rcases hx1 : mkXor inputs (T r j) hw0 ga with ⟨gx, upd⟩
      have sx := mkXor_spec (T r j) hw0 gaG (lt_of_lt_of_le (hT r j) (by omega)) wa
      simp only [hx1] at sx
      rcases sx with ⟨ex, lx, gxG, wx, evx⟩
      rcases hm : mkMux inputs (piv r) (w' j) upd gx with ⟨gm, out⟩
      have sm := mkMux_spec (piv r) (w' j) upd gxG (lt_of_lt_of_le (vpiv r) (by omega))
        (lt_of_lt_of_le (vw' j) (by omega)) wx
      simp only [hm] at sm
      rcases sm with ⟨em, lm, gmG, wm, evm⟩
      simp only [hx1, hm]
      refine ⟨extends_trans ea (extends_trans ex em), by omega, gmG, wm, fun x hx h0x => ?_⟩
      have hvpr := vpiv r
      have hvwj := vw' j
      have hTrj := hT r j
      have hvhr := vhit r
      rw [evm x hx,
        wireAt_extends (extends_trans e3 (extends_trans he (extends_trans he' (extends_trans ea ex)))) x (by omega),
        sempiv x hx h0x r,
        wireAt_extends (extends_trans e2 (extends_trans e3 (extends_trans he (extends_trans he' (extends_trans ea ex))))) x (by omega),
        evx x hx,
        wireAt_extends (extends_trans e1 (extends_trans e2 (extends_trans e3 (extends_trans he (extends_trans he' ea))))) x (by omega),
        eva x hx,
        wireAt_extends (extends_trans he he') x (by omega),
        wireAt_extends (extends_trans e2 (extends_trans e3 (extends_trans he he'))) x (by omega)]
      have hfn : (fun c => wireAt gs1 x (w' c)) =
          (fun c => z2b (reduceVec (fun a b => b2z (wireAt gs x (T a b)))
            (fun a => b2z (wireAt gs x (w a))) c)) := by
        funext c
        rw [← semw' x hx h0x c, z2b_b2z]
      unfold insertRow
      dsimp only
      rw [hfn]
      split_ifs
      · exact semw' x hx h0x j
      · rw [b2z_xor, b2z_and, semhit x hx h0x r, semw' x hx h0x j])
  simp only [h4] at s4
  rcases s4 with ⟨e4, l4, g4, v4, sem4⟩
  have hres : mkInsertRow inputs n T w gs = (gs4, T') := by
    simp only [mkInsertRow, h1, h2, h3, h4]
  simp only [hres]
  refine ⟨extends_trans e1 (extends_trans e2 (extends_trans e3 e4)), ?_, g4, v4, sem4⟩
  nlinarith

private def mkInsertMany (inputs n m : ℕ) (rows : Fin m → Fin n → ℕ)
    (T : Fin n → Fin n → ℕ) : CG (Fin n → Fin n → ℕ) :=
  mkIter m (fun i acc => mkInsertRow inputs n acc (rows i)) T

private lemma mkInsertMany_spec {inputs n m : ℕ} (h0 : 0 < inputs)
    (rows : Fin m → Fin n → ℕ) (T : Fin n → Fin n → ℕ)
    {gs : List Gate} (hG : Good inputs gs)
    (hrows : MatValid (inputs + gs.length) rows) (hT : MatValid (inputs + gs.length) T) :
    let res := mkInsertMany inputs n m rows T gs
    Extends gs res.1 ∧ res.1.length ≤ gs.length + m * (26 * (n + 1) ^ 2) ∧ Good inputs res.1 ∧
    MatValid (inputs + res.1.length) res.2 ∧
    ∀ x : List Bool, x.length = inputs → x.getD 0 false = false →
      MatZSem res.1 x res.2
        (insertMany m (fun i j => b2z (wireAt gs x (rows i j))) (fun r j => b2z (wireAt gs x (T r j)))) := by
  refine mkIter_spec (inputs := inputs) (cost := 26 * (n + 1) ^ 2)
    (WValid := MatValid) (WSem := MatZSem)
    (fun i acc => mkInsertRow inputs n acc (rows i))
    (fun x i acc => insertRow acc (fun j => b2z (wireAt gs x (rows i j))))
    T (fun x r j => b2z (wireAt gs x (T r j))) hG hT (fun _ _ _ _ _ => rfl) ?_
  intro i g acc hg he hacc b hsem
  have hlen := extends_length_le he
  have hri : VecValid (inputs + g.length) (rows i) := fun j => lt_of_lt_of_le (hrows i j) (by omega)
  rcases h1 : mkInsertRow inputs n acc (rows i) g with ⟨g', T'⟩
  have s1 := mkInsertRow_spec h0 acc (rows i) hg hacc hri
  simp only [h1] at s1
  rcases s1 with ⟨e1, l1, g1G, v1, sem1⟩
  refine ⟨e1, l1, g1G, v1, fun x hx h0x r j => ?_⟩
  have heq := sem1 x hx h0x r j
  have hacc_eq : (fun a c => b2z (wireAt g x (acc a c))) = b x := by
    funext a c; exact hsem x hx h0x a c
  have hrow_eq : (fun c => b2z (wireAt g x (rows i c))) = (fun c => b2z (wireAt gs x (rows i c))) := by
    funext c; have hric := hrows i c; rw [wireAt_extends he x (by omega)]
  rw [hacc_eq, hrow_eq] at heq
  exact heq

private def mkKernel (inputs n : ℕ) (T : Fin n → Fin n → ℕ) : CG (Fin n → Fin n → ℕ) := fun gs =>
  let (gs1, free) := mkVec n (fun k => mkNot inputs (T k k)) gs
  mkVec n (fun k => mkVec n (fun j =>
    if j = k then fun g => (g, free k) else mkAnd inputs (free k) (T j k))) gs1

private lemma mkKernel_spec {inputs n : ℕ} (T : Fin n → Fin n → ℕ)
    {gs : List Gate} (hG : Good inputs gs) (hT : MatValid (inputs + gs.length) T) :
    let res := mkKernel inputs n T gs
    Extends gs res.1 ∧ res.1.length ≤ gs.length + 2 * (n + 1) ^ 2 ∧ Good inputs res.1 ∧
    MatValid (inputs + res.1.length) res.2 ∧
    ∀ x : List Bool, x.length = inputs → x.getD 0 false = false →
      MatZSem res.1 x res.2 (kernelBasis (fun r j => b2z (wireAt gs x (T r j)))) := by
  rcases h1 : mkVec n (fun k => mkNot inputs (T k k)) gs with ⟨gs1, free⟩
  have s1 := mkVec_spec (inputs := inputs) (cost := 1)
    (WValid := fun L w => w < L) (fun _ _ _ hle hw => lt_of_lt_of_le hw hle)
    (WSem := fun g x w b => wireAt g x w = b)
    (fun g1 g2 x w b hx he hw hs => wireSem_ext g1 g2 x w b hx he hw hs)
    (fun k => mkNot inputs (T k k)) (fun x k => !(wireAt gs x (T k k))) hG
    (fun k g hg he => by
      have hlen := extends_length_le he
      have hTkk := hT k k
      rcases mkNot_spec (T k k) hg (lt_of_lt_of_le hTkk (by omega)) with ⟨e, l, g', w', ev⟩
      refine ⟨e, by omega, g', w', fun x hx _ => ?_⟩
      rw [ev x hx, wireAt_extends he x (by omega)])
  simp only [h1] at s1
  rcases s1 with ⟨e1, l1, g1G, vfree, semfree⟩
  have hlen1 := extends_length_le e1
  rcases h2 : mkVec n (fun k => mkVec n (fun j =>
      if j = k then fun g => (g, free k) else mkAnd inputs (free k) (T j k))) gs1 with ⟨gs2, K⟩
  have s2 := mkVec_spec (inputs := inputs) (cost := n * 1)
    (WValid := fun L v => VecValid L v)
    (fun _ _ _ hle hv j => lt_of_lt_of_le (hv j) hle)
    (WSem := fun g x vW v => VecZSem g x vW v)
    (fun g1 g2 x vW v hx he hv hs => vecZSem_ext g1 g2 x vW v hx he hv hs)
    (fun k => mkVec n (fun j =>
      if j = k then fun g => (g, free k) else mkAnd inputs (free k) (T j k)))
    (fun x k => kernelBasis (fun r j => b2z (wireAt gs x (T r j))) k) g1G
    (fun k g hg he => by
      have hle := extends_length_le he
      refine mkVec_spec (inputs := inputs) (cost := 1)
        (WValid := fun L w => w < L) (fun _ _ _ hle' hw => lt_of_lt_of_le hw hle')
        (WSem := fun g' x w z => b2z (wireAt g' x w) = z)
        (fun g1 g2 x w z hx he' hw hs => wireZSem_ext g1 g2 x w z hx he' hw hs)
        (fun j => if j = k then fun g0 => (g0, free k) else mkAnd inputs (free k) (T j k))
        (fun x j => kernelBasis (fun r c => b2z (wireAt gs x (T r c))) k j) hg ?_
      intro j g' hg' he'
      have hle' := extends_length_le he'
      have hfk := vfree k
      by_cases hjk : j = k
      · simp only [hjk, ↓reduceIte]
        refine ⟨extends_refl g', by omega, hg', lt_of_lt_of_le hfk (by omega), fun x hx h0x => ?_⟩
        rw [wireAt_extends (extends_trans he he') x (by omega), semfree x hx h0x k]
        unfold kernelBasis
        simp [z2b_b2z]
      · simp only [hjk, ↓reduceIte]
        have hTjk := hT j k
        rcases ha : mkAnd inputs (free k) (T j k) g' with ⟨ga, out⟩
        have sa := mkAnd_spec (free k) (T j k) hg' (lt_of_lt_of_le hfk (by omega))
          (lt_of_lt_of_le hTjk (by omega))
        simp only [ha] at sa
        rcases sa with ⟨ea, la, gaG, wa, eva⟩
        dsimp only
        refine ⟨ea, by omega, gaG, wa, fun x hx h0x => ?_⟩
        rw [eva x hx, b2z_and, wireAt_extends (extends_trans he he') x (by omega),
          semfree x hx h0x k,
          wireAt_extends (extends_trans e1 (extends_trans he he')) x (by omega)]
        unfold kernelBasis
        simp [hjk, z2b_b2z])
  simp only [h2] at s2
  rcases s2 with ⟨e2, l2, g2G, v2, sem2⟩
  have hres : mkKernel inputs n T gs = (gs2, K) := by
    simp only [mkKernel, h1, h2]
  simp only [hres]
  refine ⟨extends_trans e1 e2, ?_, g2G, v2, sem2⟩
  nlinarith

private def wireL (n : ℕ) {t : ℕ} (j : Fin t) (i : Fin n) : ℕ :=
  1 + j.val * n + i.val

private def wireA (n t : ℕ) (j : Fin t) (i b : Fin n) : ℕ :=
  1 + t * n + j.val * (n * n) + i.val * n + b.val

private lemma wireL_lt {n t : ℕ} (j : Fin t) (i : Fin n) :
    wireL n j i < 1 + t * n + t * n * n := by
  unfold wireL
  have hj : j.val + 1 ≤ t := j.isLt
  have hi : i.val < n := i.isLt
  have hmul : (j.val + 1) * n ≤ t * n := Nat.mul_le_mul_right n hj
  have hadd : j.val * n + n = (j.val + 1) * n := by ring
  omega

private lemma wireA_lt {n t : ℕ} (j : Fin t) (i b : Fin n) :
    wireA n t j i b < 1 + t * n + t * n * n := by
  unfold wireA
  have hj : j.val + 1 ≤ t := j.isLt
  have hi : i.val + 1 ≤ n := i.isLt
  have hb : b.val < n := b.isLt
  have h1 : (i.val + 1) * n ≤ n * n := Nat.mul_le_mul_right n hi
  have h2 : (j.val + 1) * (n * n) ≤ t * (n * n) := Nat.mul_le_mul_right (n * n) hj
  have h3 : t * (n * n) = t * n * n := (Nat.mul_assoc t n n).symm
  have h4 : i.val * n + n = (i.val + 1) * n := by ring
  have h5 : j.val * (n * n) + n * n = (j.val + 1) * (n * n) := by ring
  omega

private def packRow {n : ℕ} (row : Fin n → ZMod 2) : List Bool :=
  List.ofFn (fun bit : Fin n => decide (row bit ≠ 0))

private def encBits {n t : ℕ} (l : Fin t → Fin n → ZMod 2)
    (a : Fin t → Matrix (Fin n) (Fin n) (ZMod 2)) : List Bool :=
  [false] ++ (List.ofFn (fun linearRow => packRow (l linearRow))).flatten ++
    (List.ofFn (fun quadRow => (List.ofFn (fun coord => packRow (a quadRow coord))).flatten)).flatten

private lemma length_flatten_ofFn {α : Type*} (m k : ℕ) (f : Fin m → List α)
    (hf : ∀ i, (f i).length = k) :
    (List.ofFn f).flatten.length = m * k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.ofFn_succ, List.flatten_cons, List.length_append, hf 0, ih (fun i => f i.succ) (fun i => hf i.succ)]
    ring

private lemma getD_flatten_ofFn {α : Type*} (m k : ℕ) (f : Fin m → List α)
    (hf : ∀ i, (f i).length = k) (i : Fin m) {j : ℕ} (hj : j < k) (d : α) :
    (List.ofFn f).flatten.getD (i.val * k + j) d = (f i).getD j d := by
  induction m with
  | zero => exact i.elim0
  | succ m ih =>
    rw [List.ofFn_succ, List.flatten_cons]
    refine Fin.cases ?_ ?_ i
    · simp only [Fin.val_zero, zero_mul, zero_add]
      rw [getD_append_lt _ _ (by rw [hf 0]; exact hj)]
    · intro i'
      simp only [Fin.val_succ]
      have hidx : (i'.val + 1) * k + j = k + (i'.val * k + j) := by ring
      rw [hidx, getD_append_ge _ _ (by rw [hf 0]; omega), hf 0, Nat.add_sub_cancel_left]
      exact ih (fun r => f r.succ) (fun r => hf r.succ) i'

private lemma length_packRow {n : ℕ} (row : Fin n → ZMod 2) : (packRow row).length = n :=
  List.length_ofFn

private lemma encBits_length {n t : ℕ} (l : Fin t → Fin n → ZMod 2)
    (a : Fin t → Matrix (Fin n) (Fin n) (ZMod 2)) :
    (encBits l a).length = 1 + t * n + t * n * n := by
  unfold encBits
  rw [List.length_append, List.length_append, List.length_singleton]
  have h1 : (List.ofFn (fun linearRow => packRow (l linearRow))).flatten.length = t * n :=
    length_flatten_ofFn t n (fun linearRow => packRow (l linearRow)) (fun _ => length_packRow _)
  have h2 : (List.ofFn (fun quadRow =>
      (List.ofFn (fun coord => packRow (a quadRow coord))).flatten)).flatten.length = t * (n * n) :=
    length_flatten_ofFn t (n * n)
      (fun quadRow => (List.ofFn (fun coord => packRow (a quadRow coord))).flatten)
      (fun q => length_flatten_ofFn n n (fun coord => packRow (a q coord)) (fun _ => length_packRow _))
  rw [h1, h2, Nat.mul_assoc]

private lemma encBits_getD_zero {n t : ℕ} (l : Fin t → Fin n → ZMod 2)
    (a : Fin t → Matrix (Fin n) (Fin n) (ZMod 2)) :
    (encBits l a).getD 0 false = false := by
  unfold encBits
  simp

private lemma encBits_getD_wireL {n t : ℕ} (l : Fin t → Fin n → ZMod 2)
    (a : Fin t → Matrix (Fin n) (Fin n) (ZMod 2)) (j : Fin t) (i : Fin n) :
    (encBits l a).getD (wireL n j i) false = z2b (l j i) := by
  unfold encBits wireL
  have h1len : (List.ofFn (fun linearRow => packRow (l linearRow))).flatten.length = t * n :=
    length_flatten_ofFn t n (fun linearRow => packRow (l linearRow)) (fun _ => length_packRow _)
  have hlt1 : 1 + j.val * n + i.val < ([false] ++
      (List.ofFn (fun linearRow => packRow (l linearRow))).flatten).length := by
    rw [List.length_append, List.length_singleton, h1len]
    have hj : j.val + 1 ≤ t := j.isLt
    have hi : i.val < n := i.isLt
    have hmul : (j.val + 1) * n ≤ t * n := Nat.mul_le_mul_right n hj
    have hadd : j.val * n + n = (j.val + 1) * n := by ring
    omega
  rw [getD_append_lt _ _ hlt1, getD_append_ge _ _ (by simp; omega)]
  simp only [List.length_singleton, show 1 + j.val * n + i.val - 1 = j.val * n + i.val by omega]
  rw [getD_flatten_ofFn t n (fun linearRow => packRow (l linearRow)) (fun _ => length_packRow _) j i.isLt]
  unfold packRow z2b
  simp [List.getD_eq_getElem?_getD, i.isLt]

private lemma encBits_getD_wireA {n t : ℕ} (l : Fin t → Fin n → ZMod 2)
    (a : Fin t → Matrix (Fin n) (Fin n) (ZMod 2)) (j : Fin t) (i b : Fin n) :
    (encBits l a).getD (wireA n t j i b) false = z2b (a j i b) := by
  unfold encBits wireA
  have h1len : ([false] ++ (List.ofFn (fun linearRow => packRow (l linearRow))).flatten).length =
      1 + t * n := by
    rw [List.length_append, List.length_singleton,
      length_flatten_ofFn t n (fun linearRow => packRow (l linearRow)) (fun _ => length_packRow _)]
  rw [getD_append_ge _ _ (by omega), h1len]
  have hsub : 1 + t * n + j.val * (n * n) + i.val * n + b.val - (1 + t * n) =
      j.val * (n * n) + (i.val * n + b.val) := by omega
  rw [hsub]
  have hib : i.val * n + b.val < n * n := by
    have hi : i.val + 1 ≤ n := i.isLt
    have hb : b.val < n := b.isLt
    have h1 : (i.val + 1) * n ≤ n * n := Nat.mul_le_mul_right n hi
    have hadd : i.val * n + n = (i.val + 1) * n := by ring
    omega
  rw [getD_flatten_ofFn t (n * n)
    (fun quadRow => (List.ofFn (fun coord => packRow (a quadRow coord))).flatten)
    (fun q => length_flatten_ofFn n n (fun coord => packRow (a q coord)) (fun _ => length_packRow _)) j hib]
  rw [getD_flatten_ofFn n n (fun coord => packRow (a j coord)) (fun _ => length_packRow _) i b.isLt]
  unfold packRow z2b
  simp [List.getD_eq_getElem?_getD, b.isLt]

private def mkEvalQuad (n t : ℕ) (j : Fin t) (v : Fin n → ℕ) : CG ℕ := fun gs =>
  let inputs := 1 + t * n + t * n * n
  let (gs1, lin) := mkDot inputs n (wireL n j) v gs
  let (gs2, quadTerms) := mkVec n (fun i gs' =>
    let (g1, d) := mkDot inputs n (wireA n t j i) v gs'
    mkAnd inputs (v i) d g1) gs1
  let (gs3, quadSum) := mkListXor inputs (List.ofFn quadTerms) gs2
  mkXor inputs lin quadSum gs3

private lemma mkEvalQuad_spec {n t : ℕ} (j : Fin t) (v : Fin n → ℕ)
    {gs : List Gate} (hG : Good (1 + t * n + t * n * n) gs)
    (hv : VecValid (1 + t * n + t * n * n + gs.length) v) :
    let inputs := 1 + t * n + t * n * n
    let res := mkEvalQuad n t j v gs
    Extends gs res.1 ∧ res.1.length ≤ gs.length + 19 * (n + 1) ^ 2 ∧ Good inputs res.1 ∧
    res.2 < inputs + res.1.length ∧
    ∀ (l : Fin t → Fin n → ZMod 2) (a : Fin t → Matrix (Fin n) (Fin n) (ZMod 2)),
      b2z (wireAt res.1 (encBits l a) res.2) =
        quadEval (l j) (a j) (fun i => b2z (wireAt gs (encBits l a) (v i))) := by
  set inputs := 1 + t * n + t * n * n
  have h0 : 0 < inputs := by omega
  have hL : VecValid (inputs + gs.length) (wireL n j) := fun i => lt_of_lt_of_le (wireL_lt j i) (by omega)
  rcases h1 : mkDot inputs n (wireL n j) v gs with ⟨gs1, lin⟩
  have s1 := mkDot_spec h0 (wireL n j) v hG hL hv
  simp only [h1] at s1
  rcases s1 with ⟨e1, l1, g1G, wlin, ev1⟩
  have hlen1 := extends_length_le e1
  rcases h2 : mkVec n (fun i gs' =>
      let (g1, d) := mkDot inputs n (wireA n t j i) v gs'
      mkAnd inputs (v i) d g1) gs1 with ⟨gs2, quadTerms⟩
  have s2 := mkVec_spec (inputs := inputs) (cost := 5 * n + 1)
    (WValid := fun L w => w < L) (fun _ _ _ hle hw => lt_of_lt_of_le hw hle)
    (WSem := fun g x w z => b2z (wireAt g x w) = z)
    (fun g1 g2 x w z hx he hw hs => wireZSem_ext g1 g2 x w z hx he hw hs)
    (fun i gs' =>
      let (g1, d) := mkDot inputs n (wireA n t j i) v gs'
      mkAnd inputs (v i) d g1)
    (fun x i => b2z (wireAt gs x (v i)) * ∑ b : Fin n, b2z (x.getD (wireA n t j i b) false) * b2z (wireAt gs x (v b))) g1G
    (fun i g hg he => by
      have hle := extends_length_le he
      rcases hd : mkDot inputs n (wireA n t j i) v g with ⟨gd1, d⟩
      have sd := mkDot_spec h0 (wireA n t j i) v hg
        (fun b => lt_of_lt_of_le (wireA_lt j i b) (by omega))
        (fun b => lt_of_lt_of_le (hv b) (by omega))
      simp only [hd] at sd
      rcases sd with ⟨ed, ld, gdG, wd, evd⟩
      have hled := extends_length_le ed
      rcases ha : mkAnd inputs (v i) d gd1 with ⟨ga, out⟩
      have hvi := hv i
      have sa := mkAnd_spec (v i) d gdG (lt_of_lt_of_le hvi (by omega)) wd
      simp only [ha] at sa
      rcases sa with ⟨ea, la, gaG, wa, eva⟩
      simp only [ha]
      refine ⟨extends_trans ed ea, by omega, gaG, wa, fun x hx h0x => ?_⟩
      rw [eva x hx, b2z_and, wireAt_extends (extends_trans e1 (extends_trans he ed)) x (by omega),
        evd x hx h0x]
      congr 1
      refine Finset.sum_congr rfl fun b _ => ?_
      have hvb := hv b
      rw [wireAt_input g x (by rw [hx]; exact wireA_lt j i b),
        wireAt_extends (extends_trans e1 he) x (by omega)])
  simp only [h2] at s2
  rcases s2 with ⟨e2, l2, g2G, vq, semq⟩
  rcases h3 : mkListXor inputs (List.ofFn quadTerms) gs2 with ⟨gs3, quadSum⟩
  have hmem : ∀ w ∈ List.ofFn quadTerms, w < inputs + gs2.length := by
    intro w hw; rcases List.mem_ofFn.mp hw with ⟨i, rfl⟩; exact vq i
  have s3 := mkListXor_spec h0 (List.ofFn quadTerms) g2G hmem
  simp only [h3] at s3
  rcases s3 with ⟨e3, l3, g3G, wqs, ev3⟩
  have hlen2 := extends_length_le e2
  have hlen3 := extends_length_le e3
  rcases h4 : mkXor inputs lin quadSum gs3 with ⟨gs4, out⟩
  have s4 := mkXor_spec lin quadSum g3G (lt_of_lt_of_le wlin (by omega)) wqs
  simp only [h4] at s4
  rcases s4 with ⟨e4, l4, g4G, wout, ev4⟩
  have hres : mkEvalQuad n t j v gs = (gs4, out) := by
    simp only [mkEvalQuad, inputs, h1, h2, h3, h4]
  simp only [hres]
  refine ⟨extends_trans e1 (extends_trans e2 (extends_trans e3 e4)), ?_, g4G, wout, fun l a => ?_⟩
  · rw [List.length_ofFn] at l3; nlinarith
  · have hx : (encBits l a).length = inputs := encBits_length l a
    have h0x : (encBits l a).getD 0 false = false := encBits_getD_zero l a
    rw [ev4 _ hx, b2z_xor,
      wireAt_extends (extends_trans e2 e3) _ (by omega), ev1 _ hx h0x, ev3 _ hx h0x,
      List.map_ofFn, List.sum_ofFn]
    unfold quadEval
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [wireAt_input gs _ (by rw [hx]; exact wireL_lt j i), encBits_getD_wireL, b2z_z2b]
    · refine Finset.sum_congr rfl fun i _ => ?_
      dsimp only [Function.comp]
      rw [semq _ hx h0x i, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [encBits_getD_wireA, b2z_z2b]
      ring

private def zeroMatW (n : ℕ) : Fin n → Fin n → ℕ := fun _ _ => 0

private def mkRadicalTable (n t : ℕ) (owner : Fin t → Fin 3) (g : Fin 3) :
    CG (Fin n → Fin n → ℕ) :=
  let inputs := 1 + t * n + t * n * n
  mkIter t (fun j acc gs =>
    if owner j == g then
      let (gs1, symM) := mkVec n (fun b => mkVec n (fun i =>
        mkXor inputs (wireA n t j i b) (wireA n t j b i))) gs
      mkInsertMany inputs n n symM acc gs1
    else (gs, acc)) (zeroMatW n)

private lemma mkRadicalTable_spec {n t : ℕ} (owner : Fin t → Fin 3) (g : Fin 3)
    {gs : List Gate} (hG : Good (1 + t * n + t * n * n) gs) :
    let inputs := 1 + t * n + t * n * n
    let res := mkRadicalTable n t owner g gs
    Extends gs res.1 ∧ res.1.length ≤ gs.length + t * (30 * (n + 1) ^ 3) ∧ Good inputs res.1 ∧
    MatValid (inputs + res.1.length) res.2 ∧
    ∀ (l : Fin t → Fin n → ZMod 2) (a : Fin t → Matrix (Fin n) (Fin n) (ZMod 2)),
      MatZSem res.1 (encBits l a) res.2 (radicalTable owner a g) := by
  set inputs := 1 + t * n + t * n * n
  have h0 : 0 < inputs := by omega
  have hbase : ∀ (m : ℕ) (ow : Fin m → Fin 3) (jMap : Fin m → Fin t),
      let r := mkIter m (fun j acc g0 =>
        if ow j == g then
          let (g1, symM) := mkVec n (fun b => mkVec n (fun i =>
            mkXor inputs (wireA n t (jMap j) i b) (wireA n t (jMap j) b i))) g0
          mkInsertMany inputs n n symM acc g1
        else (g0, acc)) (zeroMatW n) gs
      Extends gs r.1 ∧ r.1.length ≤ gs.length + m * (30 * (n + 1) ^ 3) ∧ Good inputs r.1 ∧
      MatValid (inputs + r.1.length) r.2 ∧
      ∀ (l : Fin t → Fin n → ZMod 2) (a : Fin t → Matrix (Fin n) (Fin n) (ZMod 2)),
        MatZSem r.1 (encBits l a) r.2 (radicalTable ow (fun j => a (jMap j)) g) := by
    intro m
    induction m with
    | zero =>
      intro ow jMap
      dsimp only [mkIter]
      refine ⟨extends_refl gs, by omega, hG, fun _ _ => by dsimp only [zeroMatW]; omega,
        fun l a r c => ?_⟩
      dsimp only [radicalTable, iterFin, zeroMat, zeroMatW]
      rw [wireAt_input gs _ (by rw [encBits_length]; omega), encBits_getD_zero]
      rfl
    | succ m ih =>
      intro ow jMap
      rcases h1 : mkIter m (fun j acc g0 =>
          if ow j.castSucc == g then
            let (g1, symM) := mkVec n (fun b => mkVec n (fun i =>
              mkXor inputs (wireA n t (jMap j.castSucc) i b) (wireA n t (jMap j.castSucc) b i))) g0
            mkInsertMany inputs n n symM acc g1
          else (g0, acc)) (zeroMatW n) gs with ⟨gs1, prev⟩
      have s1 := ih (fun j => ow j.castSucc) (fun j => jMap j.castSucc)
      simp only [h1] at s1
      rcases s1 with ⟨e1, l1, g1G, v1, sem1⟩
      dsimp only [mkIter]
      simp only [h1]
      by_cases hown : (ow (Fin.last m) == g) = true
      · simp only [hown, ↓reduceIte]
        set j0 := jMap (Fin.last m)
        rcases hsym : mkVec n (fun b => mkVec n (fun i =>
            mkXor inputs (wireA n t j0 i b) (wireA n t j0 b i))) gs1 with ⟨gs2, symM⟩
        have ssym := mkVec_spec (inputs := inputs) (cost := n * 4)
          (WValid := fun L v => VecValid L v)
          (fun _ _ _ hle hv i => lt_of_lt_of_le (hv i) hle)
          (WSem := fun g0 x vW v => VecZSem g0 x vW v)
          (fun g1 g2 x vW v hx he hv hs => vecZSem_ext g1 g2 x vW v hx he hv hs)
          (fun b => mkVec n (fun i => mkXor inputs (wireA n t j0 i b) (wireA n t j0 b i)))
          (fun x b i => b2z (x.getD (wireA n t j0 i b) false) + b2z (x.getD (wireA n t j0 b i) false)) g1G
          (fun b g0 hg0 _ => by
            refine mkVec_spec (inputs := inputs) (cost := 4)
              (WValid := fun L w => w < L) (fun _ _ _ hle hw => lt_of_lt_of_le hw hle)
              (WSem := fun g' x w z => b2z (wireAt g' x w) = z)
              (fun g1 g2 x w z hx he' hw hs => wireZSem_ext g1 g2 x w z hx he' hw hs)
              (fun i => mkXor inputs (wireA n t j0 i b) (wireA n t j0 b i))
              (fun x i => b2z (x.getD (wireA n t j0 i b) false) + b2z (x.getD (wireA n t j0 b i) false)) hg0 ?_
            intro i g' hg' _
            rcases mkXor_spec (wireA n t j0 i b) (wireA n t j0 b i) hg'
              (lt_of_lt_of_le (wireA_lt j0 i b) (by omega))
              (lt_of_lt_of_le (wireA_lt j0 b i) (by omega)) with ⟨ex, lx, gx, wx, evx⟩
            refine ⟨ex, by omega, gx, wx, fun x hx _ => ?_⟩
            rw [evx x hx, b2z_xor, wireAt_input g' x (by rw [hx]; exact wireA_lt j0 i b),
              wireAt_input g' x (by rw [hx]; exact wireA_lt j0 b i)])
        simp only [hsym] at ssym
        rcases ssym with ⟨es, ls, gsG, vs, sems⟩
        have hlens := extends_length_le es
        rcases hins : mkInsertMany inputs n n symM prev gs2 with ⟨gs3, out⟩
        have sins := mkInsertMany_spec h0 symM prev gsG vs (fun r c => lt_of_lt_of_le (v1 r c) (by omega))
        simp only [hins] at sins
        rcases sins with ⟨ei, li, giG, vi, semi⟩
        simp only [j0] at hsym
        dsimp only
        refine ⟨extends_trans e1 (extends_trans es ei), ?_, giG, vi, fun l a r c => ?_⟩
        · have hstep_bound : n * (n * 4) + n * (26 * (n + 1) ^ 2) ≤ 30 * (n + 1) ^ 3 := by nlinarith
          have hmul : (m + 1) * (30 * (n + 1) ^ 3) = m * (30 * (n + 1) ^ 3) + 30 * (n + 1) ^ 3 :=
            Nat.succ_mul m _
          omega
        · rw [radicalTable_succ]
          simp only [hown, ↓reduceIte]
          have hx : (encBits l a).length = inputs := encBits_length l a
          have h0x : (encBits l a).getD 0 false = false := encBits_getD_zero l a
          have heq := semi _ hx h0x r c
          have hsym_eq : (fun b i => b2z (wireAt gs2 (encBits l a) (symM b i))) = symRow (a j0) := by
            funext b i
            rw [sems _ hx h0x b i]
            dsimp only
            rw [encBits_getD_wireA, encBits_getD_wireA, b2z_z2b, b2z_z2b]
            rfl
          have hprev_eq : (fun r0 c0 => b2z (wireAt gs2 (encBits l a) (prev r0 c0))) =
              radicalTable (fun j => ow j.castSucc) (fun j => a (jMap j.castSucc)) g := by
            funext r0 c0
            rw [wireAt_extends es _ (by rw [hx]; exact v1 r0 c0)]
            exact sem1 l a r0 c0
          rw [hsym_eq, hprev_eq] at heq
          exact heq
      · have hownf : (ow (Fin.last m) == g) = false := Bool.eq_false_iff.mpr hown
        simp only [hownf, Bool.false_eq_true, ↓reduceIte]
        refine ⟨e1, ?_, g1G, v1, fun l a r c => ?_⟩
        · have hmul : (m + 1) * (30 * (n + 1) ^ 3) = m * (30 * (n + 1) ^ 3) + 30 * (n + 1) ^ 3 :=
            Nat.succ_mul m _
          omega
        · rw [radicalTable_succ]
          simp only [hownf, Bool.false_eq_true, ↓reduceIte]
          exact sem1 l a r c
  simpa [mkRadicalTable] using hbase t owner id

private def mkEvalTable (n t : ℕ) (owner : Fin t → Fin 3) (g : Fin 3) (E : Fin n → Fin n → ℕ) :
    CG (Fin n → Fin n → ℕ) :=
  let inputs := 1 + t * n + t * n * n
  mkIter t (fun j acc gs =>
    if owner j == g then
      let (gs1, row) := mkVec n (fun k => mkEvalQuad n t j (E k)) gs
      mkInsertRow inputs n acc row gs1
    else (gs, acc)) (zeroMatW n)

private lemma mkEvalTable_spec {n t : ℕ} (owner : Fin t → Fin 3) (g : Fin 3)
    (E : Fin n → Fin n → ℕ)
    {gs : List Gate} (hG : Good (1 + t * n + t * n * n) gs)
    (hE : MatValid (1 + t * n + t * n * n + gs.length) E) :
    let inputs := 1 + t * n + t * n * n
    let res := mkEvalTable n t owner g E gs
    Extends gs res.1 ∧ res.1.length ≤ gs.length + t * (45 * (n + 1) ^ 3) ∧ Good inputs res.1 ∧
    MatValid (inputs + res.1.length) res.2 ∧
    ∀ (l : Fin t → Fin n → ZMod 2) (a : Fin t → Matrix (Fin n) (Fin n) (ZMod 2)),
      MatZSem res.1 (encBits l a) res.2
        (evalTable owner l a g (fun k i => b2z (wireAt gs (encBits l a) (E k i)))) := by
  set inputs := 1 + t * n + t * n * n
  have h0 : 0 < inputs := by omega
  have hbase : ∀ (m : ℕ) (ow : Fin m → Fin 3) (jMap : Fin m → Fin t),
      let r := mkIter m (fun j acc g0 =>
        if ow j == g then
          let (g1, row) := mkVec n (fun k => mkEvalQuad n t (jMap j) (E k)) g0
          mkInsertRow inputs n acc row g1
        else (g0, acc)) (zeroMatW n) gs
      Extends gs r.1 ∧ r.1.length ≤ gs.length + m * (45 * (n + 1) ^ 3) ∧ Good inputs r.1 ∧
      MatValid (inputs + r.1.length) r.2 ∧
      ∀ (l : Fin t → Fin n → ZMod 2) (a : Fin t → Matrix (Fin n) (Fin n) (ZMod 2)),
        MatZSem r.1 (encBits l a) r.2
          (evalTable ow (fun j => l (jMap j)) (fun j => a (jMap j)) g
            (fun k i => b2z (wireAt gs (encBits l a) (E k i)))) := by
    intro m
    induction m with
    | zero =>
      intro ow jMap
      dsimp only [mkIter]
      refine ⟨extends_refl gs, by omega, hG, fun _ _ => by dsimp only [zeroMatW]; omega,
        fun l a r c => ?_⟩
      dsimp only [evalTable, iterFin, zeroMat, zeroMatW]
      rw [wireAt_input gs _ (by rw [encBits_length]; omega), encBits_getD_zero]
      rfl
    | succ m ih =>
      intro ow jMap
      rcases h1 : mkIter m (fun j acc g0 =>
          if ow j.castSucc == g then
            let (g1, row) := mkVec n (fun k => mkEvalQuad n t (jMap j.castSucc) (E k)) g0
            mkInsertRow inputs n acc row g1
          else (g0, acc)) (zeroMatW n) gs with ⟨gs1, prev⟩
      have s1 := ih (fun j => ow j.castSucc) (fun j => jMap j.castSucc)
      simp only [h1] at s1
      rcases s1 with ⟨e1, l1, g1G, v1, sem1⟩
      have hlen1 := extends_length_le e1
      dsimp only [mkIter]
      simp only [h1]
      by_cases hown : (ow (Fin.last m) == g) = true
      · simp only [hown, ↓reduceIte]
        set j0 := jMap (Fin.last m)
        rcases hrow : mkVec n (fun k => mkEvalQuad n t j0 (E k)) gs1 with ⟨gs2, row⟩
        have srow := mkVec_spec (inputs := inputs) (cost := 19 * (n + 1) ^ 2)
          (WValid := fun L w => w < L) (fun _ _ _ hle hw => lt_of_lt_of_le hw hle)
          (WSem := fun g0 x w z => ∀ (l : Fin t → Fin n → ZMod 2)
            (a : Fin t → Matrix (Fin n) (Fin n) (ZMod 2)),
            x = encBits l a → b2z (wireAt g0 x w) = z l a)
          (fun g1 g2 x w z hx he hw hs l a hxeq => by
            rw [wireAt_extends he x (by omega)]
            exact hs l a hxeq)
          (fun k => mkEvalQuad n t j0 (E k))
          (fun _ k l a => quadEval (l j0) (a j0) (fun i => b2z (wireAt gs (encBits l a) (E k i)))) g1G
          (fun k g0 hg0 he0 => by
            have hle0 := extends_length_le he0
            rcases hq : mkEvalQuad n t j0 (E k) g0 with ⟨gq, out⟩
            have sq := mkEvalQuad_spec j0 (E k) hg0 (fun i => lt_of_lt_of_le (hE k i) (by omega))
            simp only [hq] at sq
            rcases sq with ⟨eq, lq, gqG, wq, evq⟩
            refine ⟨eq, lq, gqG, wq, fun x _ _ l a hxeq => ?_⟩
            subst hxeq
            rw [evq l a]
            congr 1
            funext i
            rw [wireAt_extends (extends_trans e1 he0) _ (by rw [encBits_length]; exact hE k i)])
        simp only [hrow] at srow
        rcases srow with ⟨er, lr, grG, vr, semr⟩
        have hlenr := extends_length_le er
        rcases hins : mkInsertRow inputs n prev row gs2 with ⟨gs3, out⟩
        have sins := mkInsertRow_spec h0 prev row grG
          (fun r c => lt_of_lt_of_le (v1 r c) (by omega)) vr
        simp only [hins] at sins
        rcases sins with ⟨ei, li, giG, vi, semi⟩
        simp only [j0] at hrow
        dsimp only
        refine ⟨extends_trans e1 (extends_trans er ei), ?_, giG, vi, fun l a r c => ?_⟩
        · have hstep : n * (19 * (n + 1) ^ 2) + 26 * (n + 1) ^ 2 ≤ 45 * (n + 1) ^ 3 := by nlinarith
          have hmul : (m + 1) * (45 * (n + 1) ^ 3) = m * (45 * (n + 1) ^ 3) + 45 * (n + 1) ^ 3 :=
            Nat.succ_mul m _
          omega
        · rw [evalTable_succ]
          simp only [hown, ↓reduceIte]
          have hx : (encBits l a).length = inputs := encBits_length l a
          have h0x : (encBits l a).getD 0 false = false := encBits_getD_zero l a
          have heq := semi _ hx h0x r c
          have hprev_eq : (fun r0 c0 => b2z (wireAt gs2 (encBits l a) (prev r0 c0))) =
              evalTable (fun j => ow j.castSucc) (fun j => l (jMap j.castSucc))
                (fun j => a (jMap j.castSucc)) g
                (fun k i => b2z (wireAt gs (encBits l a) (E k i))) := by
            funext r0 c0
            rw [wireAt_extends er _ (by rw [hx]; exact v1 r0 c0)]
            exact sem1 l a r0 c0
          have hrow_eq : (fun k => b2z (wireAt gs2 (encBits l a) (row k))) =
              (fun k => quadEval (l j0) (a j0) (fun i => b2z (wireAt gs (encBits l a) (E k i)))) := by
            funext k
            exact semr _ hx h0x k l a rfl
          rw [hprev_eq, hrow_eq] at heq
          exact heq
      · have hownf : (ow (Fin.last m) == g) = false := Bool.eq_false_iff.mpr hown
        simp only [hownf, Bool.false_eq_true, ↓reduceIte]
        refine ⟨e1, ?_, g1G, v1, fun l a r c => ?_⟩
        · have hmul : (m + 1) * (45 * (n + 1) ^ 3) = m * (45 * (n + 1) ^ 3) + 45 * (n + 1) ^ 3 :=
            Nat.succ_mul m _
          omega
        · rw [evalTable_succ]
          simp only [hownf, Bool.false_eq_true, ↓reduceIte]
          exact sem1 l a r c
  simpa [mkEvalTable] using hbase t owner id

private def mkPeriodBasis (n t : ℕ) (owner : Fin t → Fin 3) (g : Fin 3) :
    CG (Fin n → Fin n → ℕ) := fun gs =>
  let inputs := 1 + t * n + t * n * n
  let (gs1, Trad) := mkRadicalTable n t owner g gs
  let (gs2, E) := mkKernel inputs n Trad gs1
  let (gs3, Teval) := mkEvalTable n t owner g E gs2
  let (gs4, C) := mkKernel inputs n Teval gs3
  mkVec n (fun m => mkVec n (fun i => mkDot inputs n (C m) (fun k => E k i))) gs4

private lemma mkPeriodBasis_spec {n t : ℕ} (owner : Fin t → Fin 3) (g : Fin 3)
    {gs : List Gate} (hG : Good (1 + t * n + t * n * n) gs) :
    let inputs := 1 + t * n + t * n * n
    let res := mkPeriodBasis n t owner g gs
    Extends gs res.1 ∧ res.1.length ≤ gs.length + (75 * t + 9) * (n + 1) ^ 3 ∧ Good inputs res.1 ∧
    MatValid (inputs + res.1.length) res.2 ∧
    ∀ (l : Fin t → Fin n → ZMod 2) (a : Fin t → Matrix (Fin n) (Fin n) (ZMod 2)),
      MatZSem res.1 (encBits l a) res.2 (periodBasis owner l a g) := by
  set inputs := 1 + t * n + t * n * n
  have h0 : 0 < inputs := by omega
  rcases h1 : mkRadicalTable n t owner g gs with ⟨gs1, Trad⟩
  have s1 := mkRadicalTable_spec owner g hG
  simp only [h1] at s1
  rcases s1 with ⟨e1, l1, g1G, v1, sem1⟩
  rcases h2 : mkKernel inputs n Trad gs1 with ⟨gs2, E⟩
  have s2 := mkKernel_spec Trad g1G v1
  simp only [inputs] at h2
  simp only [h2] at s2
  rcases s2 with ⟨e2, l2, g2G, v2, sem2⟩
  rcases h3 : mkEvalTable n t owner g E gs2 with ⟨gs3, Teval⟩
  have s3 := mkEvalTable_spec owner g E g2G v2
  simp only [h3] at s3
  rcases s3 with ⟨e3, l3, g3G, v3, sem3⟩
  rcases h4 : mkKernel inputs n Teval gs3 with ⟨gs4, C⟩
  have s4 := mkKernel_spec Teval g3G v3
  simp only [inputs] at h4
  simp only [h4] at s4
  rcases s4 with ⟨e4, l4, g4G, v4, sem4⟩
  have hlen3 := extends_length_le e3
  have hlen4 := extends_length_le e4
  rcases h5 : mkVec n (fun m => mkVec n (fun i => mkDot inputs n (C m) (fun k => E k i))) gs4 with ⟨gs5, B⟩
  have s5 := mkVec_spec (inputs := inputs) (cost := n * (5 * n))
    (WValid := fun L v => VecValid L v)
    (fun _ _ _ hle hv i => lt_of_lt_of_le (hv i) hle)
    (WSem := fun g0 x vW v => VecZSem g0 x vW v)
    (fun g1 g2 x vW v hx he hv hs => vecZSem_ext g1 g2 x vW v hx he hv hs)
    (fun m => mkVec n (fun i => mkDot inputs n (C m) (fun k => E k i)))
    (fun x m i => ∑ k : Fin n, b2z (wireAt gs4 x (C m k)) * b2z (wireAt gs2 x (E k i))) g4G
    (fun m g0 hg0 he0 => by
      have hle0 := extends_length_le he0
      refine mkVec_spec (inputs := inputs) (cost := 5 * n)
        (WValid := fun L w => w < L) (fun _ _ _ hle' hw => lt_of_lt_of_le hw hle')
        (WSem := fun g' x w z => b2z (wireAt g' x w) = z)
        (fun g1 g2 x w z hx he' hw hs => wireZSem_ext g1 g2 x w z hx he' hw hs)
        (fun i => mkDot inputs n (C m) (fun k => E k i))
        (fun x i => ∑ k : Fin n, b2z (wireAt gs4 x (C m k)) * b2z (wireAt gs2 x (E k i))) hg0 ?_
      intro i g' hg' he'
      have hle' := extends_length_le he'
      rcases hd : mkDot inputs n (C m) (fun k => E k i) g' with ⟨gd, d⟩
      have sd := mkDot_spec h0 (C m) (fun k => E k i) hg'
        (fun k => lt_of_lt_of_le (v4 m k) (by omega))
        (fun k => lt_of_lt_of_le (v2 k i) (by omega))
      simp only [hd] at sd
      rcases sd with ⟨ed, ld, gdG, wd, evd⟩
      refine ⟨ed, ld, gdG, wd, fun x hx h0x => ?_⟩
      rw [evd x hx h0x]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hv4 := v4 m k
      have hv2 := v2 k i
      rw [wireAt_extends (extends_trans he0 he') x (by omega),
        wireAt_extends (extends_trans e3 (extends_trans e4 (extends_trans he0 he'))) x (by omega)])
  simp only [h5] at s5
  rcases s5 with ⟨e5, l5, g5G, v5, sem5⟩
  have hres : mkPeriodBasis n t owner g gs = (gs5, B) := by
    simp only [mkPeriodBasis, h1, h2, h3, h4]
    simpa only [inputs] using h5
  simp only [hres]
  refine ⟨extends_trans e1 (extends_trans e2 (extends_trans e3 (extends_trans e4 e5))), ?_, g5G, v5, fun l a m i => ?_⟩
  · have hcube : 4 * (n + 1) ^ 2 + n * (n * (5 * n)) ≤ 9 * (n + 1) ^ 3 := by nlinarith
    have ht : t * (30 * (n + 1) ^ 3) + t * (45 * (n + 1) ^ 3) = 75 * t * (n + 1) ^ 3 := by ring
    have hall : (75 * t + 9) * (n + 1) ^ 3 = 75 * t * (n + 1) ^ 3 + 9 * (n + 1) ^ 3 := by ring
    omega
  · have hx : (encBits l a).length = inputs := encBits_length l a
    have h0x : (encBits l a).getD 0 false = false := encBits_getD_zero l a
    rw [sem5 _ hx h0x m i]
    have hE_eq : (fun k c => b2z (wireAt gs2 (encBits l a) (E k c))) =
        kernelBasis (radicalTable owner a g) := by
      funext k c
      rw [sem2 _ hx h0x k c]
      congr 1
      funext r0 c0
      exact sem1 l a r0 c0
    have hC_eq : (fun m0 k => b2z (wireAt gs4 (encBits l a) (C m0 k))) =
        kernelBasis (evalTable owner l a g (kernelBasis (radicalTable owner a g))) := by
      funext m0 k
      rw [sem4 _ hx h0x m0 k]
      congr 1
      funext r0 c0
      rw [sem3 l a r0 c0, hE_eq]
    unfold periodBasis
    dsimp only
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← congrFun (congrFun hC_eq m) k, ← congrFun (congrFun hE_eq k) i]

private def rankDPStep (target : ℕ) (b : Bool) (dp : Fin (target + 1) → Bool) :
    Fin (target + 1) → Bool :=
  fun k =>
    match k with
    | ⟨0, _⟩ => true
    | ⟨m + 1, hm⟩ => dp ⟨m + 1, hm⟩ || (dp ⟨m, Nat.lt_of_succ_lt hm⟩ && b)

private def rankDPInit (target : ℕ) : Fin (target + 1) → Bool :=
  fun k => decide (k.val = 0)

private def rankDP {n : ℕ} (target : ℕ) (bits : Fin n → Bool) : Fin (target + 1) → Bool :=
  iterFin n (fun i acc => rankDPStep target (bits i) acc) (rankDPInit target)

private lemma rankDP_eq (target : ℕ) : ∀ (n : ℕ) (bits : Fin n → Bool) (k : Fin (target + 1)),
    rankDP target bits k =
      decide (k.val ≤ (Finset.univ.filter (fun i : Fin n => bits i = true)).card) := by
  intro n
  induction n with
  | zero =>
    intro bits k
    unfold rankDP iterFin rankDPInit
    simp only [Finset.univ_eq_empty, Finset.filter_empty, Finset.card_empty, Nat.le_zero]
  | succ n ih =>
    intro bits k
    have hstep : rankDP target bits =
        rankDPStep target (bits (Fin.last n)) (rankDP target (fun i => bits i.castSucc)) := rfl
    rw [hstep]
    have hcard : (Finset.univ.filter (fun i : Fin (n + 1) => bits i = true)).card =
        (Finset.univ.filter (fun i : Fin n => bits i.castSucc = true)).card +
        (if bits (Fin.last n) = true then 1 else 0) := by
      simp only [Finset.card_filter, Fin.sum_univ_castSucc]
    rw [hcard]
    set c := (Finset.univ.filter (fun i : Fin n => bits i.castSucc = true)).card
    rcases k with ⟨kv, hkv⟩
    cases kv with
    | zero =>
      simp [rankDPStep]
    | succ m =>
      unfold rankDPStep
      dsimp only
      have ih1 : rankDP target (fun i => bits i.castSucc) ⟨m + 1, hkv⟩ = decide (m + 1 ≤ c) :=
        ih (fun i => bits i.castSucc) ⟨m + 1, hkv⟩
      have ih2 : rankDP target (fun i => bits i.castSucc) ⟨m, Nat.lt_of_succ_lt hkv⟩ = decide (m ≤ c) :=
        ih (fun i => bits i.castSucc) ⟨m, Nat.lt_of_succ_lt hkv⟩
      rw [ih1, ih2]
      cases hb : bits (Fin.last n)
      · simp
      · simp only [Bool.and_true, ↓reduceIte]
        by_cases h1 : m + 1 ≤ c
        · have h2 : m + 1 ≤ c + 1 := by omega
          rw [decide_eq_true h1, decide_eq_true h2]
          rfl
        · by_cases h2 : m ≤ c
          · have h3 : m + 1 ≤ c + 1 := by omega
            rw [decide_eq_false h1, decide_eq_true h2, decide_eq_true h3]
            rfl
          · have h3 : ¬ m + 1 ≤ c + 1 := by omega
            rw [decide_eq_false h1, decide_eq_false h2, decide_eq_false h3]
            rfl

private def mkRankGe (inputs n : ℕ) (T : Fin n → Fin n → ℕ) (target : ℕ) : CG ℕ := fun gs =>
  if target ≤ n then
    let (gs1, oneW) := mkConst inputs true gs
    let dp0 : Fin (target + 1) → ℕ := fun k => if k.val = 0 then oneW else 0
    let (gs2, dpFinal) := mkIter n (fun i dp =>
      mkVec (target + 1) (fun k =>
        match k with
        | ⟨0, _⟩ => fun g => (g, oneW)
        | ⟨m + 1, hm⟩ => fun g =>
          let (g1, a) := mkAnd inputs (dp ⟨m, Nat.lt_of_succ_lt hm⟩) (T i i) g
          mkOr inputs (dp ⟨m + 1, hm⟩) a g1)) dp0 gs1
    (gs2, dpFinal ⟨target, Nat.lt_succ_self target⟩)
  else (gs, 0)

private lemma mkRankGe_spec {inputs n : ℕ} (h0 : 0 < inputs)
    (T : Fin n → Fin n → ℕ) (target : ℕ)
    {gs : List Gate} (hG : Good inputs gs) (hT : MatValid (inputs + gs.length) T) :
    let res := mkRankGe inputs n T target gs
    Extends gs res.1 ∧ res.1.length ≤ gs.length + 3 * (n + 1) ^ 2 ∧ Good inputs res.1 ∧
    res.2 < inputs + res.1.length ∧
    ∀ x : List Bool, x.length = inputs → x.getD 0 false = false →
      wireAt res.1 x res.2 = decide (target ≤ rankClean (fun r c => b2z (wireAt gs x (T r c)))) := by
  by_cases htn : target ≤ n
  · rcases h1 : mkConst inputs true gs with ⟨gs1, oneW⟩
    have s1 := mkConst_spec true hG
    simp only [h1] at s1
    rcases s1 with ⟨e1, l1, g1G, wone, ev1⟩
    set dp0 : Fin (target + 1) → ℕ := fun k => if k.val = 0 then oneW else 0
    have hdp0 : VecValid (inputs + gs1.length) dp0 := fun k => by
      dsimp only [dp0]; split_ifs
      · exact wone
      · omega
    have hsem0 : ∀ x : List Bool, x.length = inputs → x.getD 0 false = false →
        VecBSem gs1 x dp0 (rankDPInit target) := fun x hx h0x k => by
      dsimp only [dp0, rankDPInit]
      by_cases hk0 : k.val = 0
      · simp only [hk0, ↓reduceIte, decide_true]; exact ev1 x hx
      · simp only [hk0, ↓reduceIte, decide_false]
        rw [wireAt_input gs1 x (by omega), h0x]
    let stepCG : Fin n → (Fin (target + 1) → ℕ) → CG (Fin (target + 1) → ℕ) :=
      fun i dp => mkVec (target + 1) (fun k =>
        match k with
        | ⟨0, _⟩ => fun g => (g, oneW)
        | ⟨m + 1, hm⟩ => fun g =>
          let (g1, a) := mkAnd inputs (dp ⟨m, Nat.lt_of_succ_lt hm⟩) (T i i) g
          mkOr inputs (dp ⟨m + 1, hm⟩) a g1)
    rcases h2 : mkIter n stepCG dp0 gs1 with ⟨gs2, dpFinal⟩
    have s2 := mkIter_spec (inputs := inputs) (cost := (target + 1) * 2)
      (WValid := VecValid) (WSem := VecBSem)
      stepCG (fun x i dp => rankDPStep target (wireAt gs x (T i i)) dp)
      dp0 (fun _ => rankDPInit target) g1G hdp0 hsem0
      (fun i g dp hg he hdp b hsem => by
        have hle := extends_length_le he
        refine mkVec_spec (inputs := inputs) (cost := 2)
          (WValid := fun L w => w < L) (fun _ _ _ hle' hw => lt_of_lt_of_le hw hle')
          (WSem := fun g' x w bv => wireAt g' x w = bv)
          (fun g1 g2 x w bv hx he' hw hs => wireSem_ext g1 g2 x w bv hx he' hw hs)
          (fun k =>
            match k with
            | ⟨0, _⟩ => fun g0 => (g0, oneW)
            | ⟨m + 1, hm⟩ => fun g0 =>
              let (g1, a) := mkAnd inputs (dp ⟨m, Nat.lt_of_succ_lt hm⟩) (T i i) g0
              mkOr inputs (dp ⟨m + 1, hm⟩) a g1)
          (fun x k => rankDPStep target (wireAt gs x (T i i)) (b x) k) hg ?_
        intro k g' hg' he'
        have hle' := extends_length_le he'
        rcases k with ⟨kv, hkv⟩
        cases kv with
        | zero =>
          dsimp only
          refine ⟨extends_refl g', by omega, hg', lt_of_lt_of_le wone (by omega), fun x hx _ => ?_⟩
          rw [wireAt_extends (extends_trans he he') x (by omega), ev1 x hx]
          rfl
        | succ m =>
          have hdm := hdp ⟨m, Nat.lt_of_succ_lt hkv⟩
          have hdm1 := hdp ⟨m + 1, hkv⟩
          have hTii := hT i i
          have hlen1 := extends_length_le e1
          rcases ha : mkAnd inputs (dp ⟨m, Nat.lt_of_succ_lt hkv⟩) (T i i) g' with ⟨ga, a⟩
          have sa := mkAnd_spec (dp ⟨m, Nat.lt_of_succ_lt hkv⟩) (T i i) hg'
            (lt_of_lt_of_le hdm (by omega))
            (lt_of_lt_of_le hTii (by omega))
          simp only [ha] at sa
          rcases sa with ⟨ea, la, gaG, wa, eva⟩
          rcases ho : mkOr inputs (dp ⟨m + 1, hkv⟩) a ga with ⟨go, out⟩
          have so := mkOr_spec (dp ⟨m + 1, hkv⟩) a gaG
            (lt_of_lt_of_le hdm1 (by omega)) wa
          simp only [ho] at so
          rcases so with ⟨eo, lo, goG, wo, evo⟩
          simp only [ha, ho]
          refine ⟨extends_trans ea eo, by omega, goG, wo, fun x hx h0x => ?_⟩
          rw [evo x hx, wireAt_extends (extends_trans he' ea) x (by omega),
            hsem x hx h0x ⟨m + 1, hkv⟩, eva x hx,
            wireAt_extends he' x (by omega), hsem x hx h0x ⟨m, Nat.lt_of_succ_lt hkv⟩,
            wireAt_extends (extends_trans e1 (extends_trans he he')) x (by omega)]
          rfl)
    simp only [h2] at s2
    rcases s2 with ⟨e2, l2, g2G, v2, sem2⟩
    have hres : mkRankGe inputs n T target gs = (gs2, dpFinal ⟨target, Nat.lt_succ_self target⟩) := by
      simp only [mkRankGe, htn, ↓reduceIte, h1]
      exact congrArg (fun p => (p.1, p.2 ⟨target, Nat.lt_succ_self target⟩)) h2
    simp only [hres]
    refine ⟨extends_trans e1 e2, ?_, g2G, v2 _, fun x hx h0x => ?_⟩
    · nlinarith
    · have hd := sem2 x hx h0x ⟨target, Nat.lt_succ_self target⟩
      have heq := rankDP_eq target n (fun i => wireAt gs x (T i i)) ⟨target, Nat.lt_succ_self target⟩
      rw [hd]
      change rankDP target (fun i => wireAt gs x (T i i)) ⟨target, Nat.lt_succ_self target⟩ = _
      rw [heq]
      dsimp only
      congr 1
      unfold rankClean
      have hf : Finset.univ.filter (fun i : Fin n => wireAt gs x (T i i) = true) =
          Finset.univ.filter (fun c : Fin n => b2z (wireAt gs x (T c c)) = 1) := by
        ext c
        simp [b2z_eq_one_iff]
      rw [hf]
  · have hres : mkRankGe inputs n T target gs = (gs, 0) := by
      simp only [mkRankGe, htn, ↓reduceIte]
    simp only [hres]
    refine ⟨extends_refl gs, by omega, hG, by omega, fun x hx h0x => ?_⟩
    rw [wireAt_input gs x (by omega), h0x]
    have hle : rankClean (fun r c => b2z (wireAt gs x (T r c))) ≤ n := by
      calc (Finset.univ.filter (fun c : Fin n => b2z (wireAt gs x (T c c)) = 1)).card
          ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
        _ = n := Finset.card_fin n
    have hnot : ¬ target ≤ rankClean (fun r c => b2z (wireAt gs x (T r c))) := by omega
    simp [hnot]

private def mkInsertSubsets (inputs n : ℕ) (B : Fin 3 → Fin n → Fin n → ℕ)
    (S : Finset (Fin 3)) (T : Fin n → Fin n → ℕ) : CG (Fin n → Fin n → ℕ) :=
  mkIter 3 (fun c acc gs =>
    if decide (c ∈ S) then mkInsertMany inputs n n (B c) acc gs else (gs, acc)) T

private lemma mkInsertSubsets_spec {inputs n : ℕ} (h0 : 0 < inputs)
    (B : Fin 3 → Fin n → Fin n → ℕ) (S : Finset (Fin 3)) (T : Fin n → Fin n → ℕ)
    {gs : List Gate} (hG : Good inputs gs)
    (hB : ∀ c : Fin 3, MatValid (inputs + gs.length) (B c))
    (hT : MatValid (inputs + gs.length) T) :
    let res := mkInsertSubsets inputs n B S T gs
    Extends gs res.1 ∧ res.1.length ≤ gs.length + 78 * (n + 1) ^ 3 ∧ Good inputs res.1 ∧
    MatValid (inputs + res.1.length) res.2 ∧
    ∀ x : List Bool, x.length = inputs → x.getD 0 false = false →
      MatZSem res.1 x res.2
        (insertSubsets (fun c r j => b2z (wireAt gs x (B c r j))) S
          (fun r j => b2z (wireAt gs x (T r j)))) := by
  have s := mkIter_spec (inputs := inputs) (cost := n * (26 * (n + 1) ^ 2))
    (WValid := MatValid) (WSem := MatZSem)
    (fun c acc g0 => if decide (c ∈ S) then mkInsertMany inputs n n (B c) acc g0 else (g0, acc))
    (fun x c acc => if decide (c ∈ S) then insertMany n (fun r j => b2z (wireAt gs x (B c r j))) acc else acc)
    T (fun x r j => b2z (wireAt gs x (T r j))) hG hT (fun _ _ _ _ _ => rfl)
    (fun c g0 acc hg0 he0 hacc b hsem => by
      have hlen0 := extends_length_le he0
      by_cases hc : decide (c ∈ S) = true
      · simp only [hc, ↓reduceIte]
        rcases hm : mkInsertMany inputs n n (B c) acc g0 with ⟨g', T'⟩
        have sm := mkInsertMany_spec h0 (B c) acc hg0
          (fun r j => lt_of_lt_of_le (hB c r j) (by omega)) hacc
        simp only [hm] at sm
        rcases sm with ⟨em, lm, gmG, vm, semm⟩
        refine ⟨em, lm, gmG, vm, fun x hx h0x r j => ?_⟩
        have heq := semm x hx h0x r j
        have hBc : (fun r0 j0 => b2z (wireAt g0 x (B c r0 j0))) =
            (fun r0 j0 => b2z (wireAt gs x (B c r0 j0))) := by
          funext r0 j0; have hB0 := hB c r0 j0; rw [wireAt_extends he0 x (by omega)]
        have hacc_eq : (fun r0 j0 => b2z (wireAt g0 x (acc r0 j0))) = b x := by
          funext r0 j0; exact hsem x hx h0x r0 j0
        rw [hBc, hacc_eq] at heq
        exact heq
      · have hcf : decide (c ∈ S) = false := Bool.eq_false_iff.mpr hc
        simp only [hcf, Bool.false_eq_true, ↓reduceIte]
        exact ⟨extends_refl g0, by omega, hg0, hacc, hsem⟩)
  rcases s with ⟨e, l, gG, v, sem⟩
  dsimp only [mkInsertSubsets]
  refine ⟨e, ?_, gG, v, sem⟩
  have hbound : 3 * (n * (26 * (n + 1) ^ 2)) ≤ 78 * (n + 1) ^ 3 := by nlinarith
  omega

private def mkCheckSubsets (inputs n : ℕ) (B : Fin 3 → Fin n → Fin n → ℕ)
    (T : Fin n → Fin n → ℕ) (k : ℕ) (q : Fin 3 → ℕ)
    (subs : List (Finset (Fin 3))) : CG ℕ := fun gs =>
  let rec go : List (Finset (Fin 3)) → List Gate → List Gate × List ℕ
    | [], g => (g, [])
    | S :: rest, g =>
      let (g1, TS) := mkInsertSubsets inputs n B S T g
      let (g2, okS) := mkRankGe inputs n TS (k + ∑ c ∈ S, q c) g1
      let (g3, ws) := go rest g2
      (g3, okS :: ws)
  let (gs1, ws) := go subs gs
  mkListAnd inputs ws gs1

private lemma mkCheckSubsets_spec {inputs n : ℕ} (h0 : 0 < inputs)
    (B : Fin 3 → Fin n → Fin n → ℕ) (T : Fin n → Fin n → ℕ) (k : ℕ) (q : Fin 3 → ℕ)
    (subs : List (Finset (Fin 3)))
    {gs : List Gate} (hG : Good inputs gs)
    (hB : ∀ c : Fin 3, MatValid (inputs + gs.length) (B c))
    (hT : MatValid (inputs + gs.length) T) :
    let res := mkCheckSubsets inputs n B T k q subs gs
    Extends gs res.1 ∧ res.1.length ≤ gs.length + (subs.length + 1) * (82 * (n + 1) ^ 3) ∧
    Good inputs res.1 ∧ res.2 < inputs + res.1.length ∧
    ∀ x : List Bool, x.length = inputs → x.getD 0 false = false →
      wireAt res.1 x res.2 =
        checkSubsets (fun c r j => b2z (wireAt gs x (B c r j)))
          (fun r j => b2z (wireAt gs x (T r j))) k q subs := by
  have hgo : ∀ (ss : List (Finset (Fin 3))) (g0 : List Gate),
      Good inputs g0 → Extends gs g0 →
      let r := mkCheckSubsets.go inputs n B T k q ss g0
      Extends g0 r.1 ∧ r.1.length ≤ g0.length + ss.length * (81 * (n + 1) ^ 3) ∧ Good inputs r.1 ∧
      r.2.length = ss.length ∧
      (∀ w ∈ r.2, w < inputs + r.1.length) ∧
      ∀ x : List Bool, x.length = inputs → x.getD 0 false = false →
        r.2.all (wireAt r.1 x) =
          checkSubsets (fun c r j => b2z (wireAt gs x (B c r j)))
            (fun r j => b2z (wireAt gs x (T r j))) k q ss := by
    intro ss
    induction ss with
    | nil =>
      intro g0 hg0 _
      exact ⟨extends_refl g0, by simp [mkCheckSubsets.go], hg0, rfl,
        fun _ hw => False.elim (List.not_mem_nil hw), fun _ _ _ => rfl⟩
    | cons S rest ih =>
      intro g0 hg0 he0
      have hlen0 := extends_length_le he0
      rcases h1 : mkInsertSubsets inputs n B S T g0 with ⟨g1, TS⟩
      have s1 := mkInsertSubsets_spec h0 B S T hg0
        (fun c r j => lt_of_lt_of_le (hB c r j) (by omega))
        (fun r j => lt_of_lt_of_le (hT r j) (by omega))
      simp only [h1] at s1
      rcases s1 with ⟨e1, l1, g1G, vTS, semTS⟩
      rcases h2 : mkRankGe inputs n TS (k + ∑ c ∈ S, q c) g1 with ⟨g2, okS⟩
      have s2 := mkRankGe_spec h0 TS (k + ∑ c ∈ S, q c) g1G vTS
      simp only [h2] at s2
      rcases s2 with ⟨e2, l2, g2G, wokS, semokS⟩
      rcases h3 : mkCheckSubsets.go inputs n B T k q rest g2 with ⟨g3, ws⟩
      have s3 := ih g2 g2G (extends_trans he0 (extends_trans e1 e2))
      simp only [h3] at s3
      rcases s3 with ⟨e3, l3, g3G, lws, vws, semws⟩
      have hlen3 := extends_length_le e3
      have hres : mkCheckSubsets.go inputs n B T k q (S :: rest) g0 = (g3, okS :: ws) := by
        simp only [mkCheckSubsets.go, h1, h2, h3]
      simp only [hres]
      refine ⟨extends_trans e1 (extends_trans e2 e3), ?_, g3G, by simp [lws], ?_, fun x hx h0x => ?_⟩
      · simp only [List.length_cons]
        have hpow : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
        have hstep : 78 * (n + 1) ^ 3 + 3 * (n + 1) ^ 2 ≤ 81 * (n + 1) ^ 3 := by omega
        have hmul : (rest.length + 1) * (81 * (n + 1) ^ 3) =
            rest.length * (81 * (n + 1) ^ 3) + 81 * (n + 1) ^ 3 := Nat.succ_mul _ _
        omega
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hmem
        · exact lt_of_lt_of_le wokS (by omega)
        · exact vws w hmem
      · simp only [List.all_cons, checkSubsets]
        rw [wireAt_extends e3 x (by omega), semokS x hx h0x, semws x hx h0x]
        congr 2
        have hTS_eq : (fun r c => b2z (wireAt g1 x (TS r c))) =
            insertSubsets (fun c r j => b2z (wireAt gs x (B c r j))) S
              (fun r j => b2z (wireAt gs x (T r j))) := by
          funext r c
          rw [semTS x hx h0x r c]
          have hB_eq : (fun c0 r0 j0 => b2z (wireAt g0 x (B c0 r0 j0))) =
              (fun c0 r0 j0 => b2z (wireAt gs x (B c0 r0 j0))) := by
            funext c0 r0 j0; have hB0 := hB c0 r0 j0; rw [wireAt_extends he0 x (by omega)]
          have hT_eq : (fun r0 j0 => b2z (wireAt g0 x (T r0 j0))) =
              (fun r0 j0 => b2z (wireAt gs x (T r0 j0))) := by
            funext r0 j0; have hT0 := hT r0 j0; rw [wireAt_extends he0 x (by omega)]
          rw [hB_eq, hT_eq]
        rw [hTS_eq]
  rcases h1 : mkCheckSubsets.go inputs n B T k q subs gs with ⟨gs1, ws⟩
  have s1 := hgo subs gs hG (extends_refl gs)
  simp only [h1] at s1
  rcases s1 with ⟨e1, l1, g1G, lws, vws, semws⟩
  rcases h2 : mkListAnd inputs ws gs1 with ⟨gs2, out⟩
  have s2 := mkListAnd_spec ws g1G vws
  simp only [h2] at s2
  rcases s2 with ⟨e2, l2, g2G, wout, ev2⟩
  have hres : mkCheckSubsets inputs n B T k q subs gs = (gs2, out) := by
    simp only [mkCheckSubsets, h1, h2]
  simp only [hres]
  refine ⟨extends_trans e1 e2, ?_, g2G, wout, fun x hx h0x => ?_⟩
  · have hcube : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow 3 _ (by omega)
    rw [lws] at l2
    nlinarith
  · rw [ev2 x hx, semws x hx h0x]

private def mkGreedyStep (inputs n : ℕ) (B : Fin 3 → Fin n → Fin n → ℕ)
    (g : Fin 3) (k : ℕ) (q' : Fin 3 → ℕ) (T : Fin n → Fin n → ℕ) :
    CG ((Fin n → Fin n → ℕ) × (Fin n → ℕ)) := fun gs =>
  let (gs1, okW) := mkVec n (fun m g0 =>
    let (g1, Tcand) := mkInsertRow inputs n T (B g m) g0
    mkCheckSubsets inputs n B Tcand (k + 1) q' (subsetsWithout g) g1) gs
  let (gs2, pick) := mkFirstOk inputs n okW gs1
  let (gs3, vW) := mkVec n (fun pos => mkDot inputs n pick (fun m => B g m pos)) gs2
  let (gs4, T') := mkInsertRow inputs n T vW gs3
  (gs4, (T', vW))

private lemma subsetsWithout_length (g : Fin 3) : (subsetsWithout g).length = 4 := by
  fin_cases g <;> decide

private lemma mkGreedyStep_spec {inputs n : ℕ} (h0 : 0 < inputs)
    (B : Fin 3 → Fin n → Fin n → ℕ) (g : Fin 3) (k : ℕ) (q' : Fin 3 → ℕ)
    (T : Fin n → Fin n → ℕ)
    {gs : List Gate} (hG : Good inputs gs)
    (hB : ∀ c : Fin 3, MatValid (inputs + gs.length) (B c))
    (hT : MatValid (inputs + gs.length) T) :
    let res := mkGreedyStep inputs n B g k q' T gs
    Extends gs res.1 ∧ res.1.length ≤ gs.length + 470 * (n + 1) ^ 4 ∧ Good inputs res.1 ∧
    MatValid (inputs + res.1.length) res.2.1 ∧ VecValid (inputs + res.1.length) res.2.2 ∧
    ∀ x : List Bool, x.length = inputs → x.getD 0 false = false →
      let st := greedyStep (fun c r j => b2z (wireAt gs x (B c r j))) g k q'
        (fun r j => b2z (wireAt gs x (T r j)))
      MatZSem res.1 x res.2.1 st.1 ∧ VecZSem res.1 x res.2.2 st.2 := by
  rcases h1 : mkVec n (fun m g0 =>
      let (g1, Tcand) := mkInsertRow inputs n T (B g m) g0
      mkCheckSubsets inputs n B Tcand (k + 1) q' (subsetsWithout g) g1) gs with ⟨gs1, okW⟩
  have s1 := mkVec_spec (inputs := inputs) (cost := 26 * (n + 1) ^ 2 + 5 * (82 * (n + 1) ^ 3))
    (WValid := fun L w => w < L) (fun _ _ _ hle hw => lt_of_lt_of_le hw hle)
    (WSem := fun g0 x w bv => wireAt g0 x w = bv)
    (fun g1 g2 x w bv hx he hw hs => wireSem_ext g1 g2 x w bv hx he hw hs)
    (fun m g0 =>
      let (g1, Tcand) := mkInsertRow inputs n T (B g m) g0
      mkCheckSubsets inputs n B Tcand (k + 1) q' (subsetsWithout g) g1)
    (fun x m => checkSubsets (fun c r j => b2z (wireAt gs x (B c r j)))
        (insertRow (fun r j => b2z (wireAt gs x (T r j))) (fun j => b2z (wireAt gs x (B g m j))))
        (k + 1) q' (subsetsWithout g)) hG
    (fun m g0 hg0 he0 => by
      have hle0 := extends_length_le he0
      rcases hi : mkInsertRow inputs n T (B g m) g0 with ⟨g1, Tcand⟩
      have si := mkInsertRow_spec h0 T (B g m) hg0
        (fun r j => lt_of_lt_of_le (hT r j) (by omega))
        (fun j => lt_of_lt_of_le (hB g m j) (by omega))
      simp only [hi] at si
      rcases si with ⟨ei, li, giG, vTcand, semTcand⟩
      have hlei := extends_length_le ei
      rcases hc : mkCheckSubsets inputs n B Tcand (k + 1) q' (subsetsWithout g) g1 with ⟨g2, okm⟩
      have sc := mkCheckSubsets_spec h0 B Tcand (k + 1) q' (subsetsWithout g) giG
        (fun c r j => lt_of_lt_of_le (hB c r j) (by omega)) vTcand
      simp only [hc] at sc
      rcases sc with ⟨ec, lc, gcG, wokm, semokm⟩
      simp only [hc]
      refine ⟨extends_trans ei ec, ?_, gcG, wokm, fun x hx h0x => ?_⟩
      · rw [subsetsWithout_length] at lc; omega
      · rw [semokm x hx h0x]
        have hB_eq : (fun c r j => b2z (wireAt g1 x (B c r j))) =
            (fun c r j => b2z (wireAt gs x (B c r j))) := by
          funext c r j; have hB0 := hB c r j; rw [wireAt_extends (extends_trans he0 ei) x (by omega)]
        have hT_eq : (fun r j => b2z (wireAt g1 x (Tcand r j))) =
            insertRow (fun r j => b2z (wireAt gs x (T r j))) (fun j => b2z (wireAt gs x (B g m j))) := by
          funext r j
          rw [semTcand x hx h0x r j]
          have hT0 : (fun r0 j0 => b2z (wireAt g0 x (T r0 j0))) =
              (fun r0 j0 => b2z (wireAt gs x (T r0 j0))) := by
            funext r0 j0; have hT0' := hT r0 j0; rw [wireAt_extends he0 x (by omega)]
          have hBm0 : (fun j0 => b2z (wireAt g0 x (B g m j0))) =
              (fun j0 => b2z (wireAt gs x (B g m j0))) := by
            funext j0; have hBm0' := hB g m j0; rw [wireAt_extends he0 x (by omega)]
          rw [hT0, hBm0]
        rw [hB_eq, hT_eq])
  simp only [h1] at s1
  rcases s1 with ⟨e1, l1, g1G, vok, semok⟩
  rcases h2 : mkFirstOk inputs n okW gs1 with ⟨gs2, pick⟩
  have s2 := mkFirstOk_spec h0 okW g1G vok
  simp only [h2] at s2
  rcases s2 with ⟨e2, l2, g2G, vpick, sempick⟩
  have hlen1 := extends_length_le e1
  have hlen2 := extends_length_le e2
  rcases h3 : mkVec n (fun pos => mkDot inputs n pick (fun m => B g m pos)) gs2 with ⟨gs3, vW⟩
  have s3 := mkVec_spec (inputs := inputs) (cost := 5 * n)
    (WValid := fun L w => w < L) (fun _ _ _ hle hw => lt_of_lt_of_le hw hle)
    (WSem := fun g0 x w z => b2z (wireAt g0 x w) = z)
    (fun g1 g2 x w z hx he hw hs => wireZSem_ext g1 g2 x w z hx he hw hs)
    (fun pos => mkDot inputs n pick (fun m => B g m pos))
    (fun x pos => (greedyStep (fun c r j => b2z (wireAt gs x (B c r j))) g k q'
      (fun r j => b2z (wireAt gs x (T r j)))).2 pos) g2G
    (fun pos g0 hg0 he0 => by
      have hle0 := extends_length_le he0
      rcases hd : mkDot inputs n pick (fun m => B g m pos) g0 with ⟨gd, d⟩
      have sd := mkDot_spec h0 pick (fun m => B g m pos) hg0
        (fun m => lt_of_lt_of_le (vpick m) (by omega))
        (fun m => lt_of_lt_of_le (hB g m pos) (by omega))
      simp only [hd] at sd
      rcases sd with ⟨ed, ld, gdG, wd, evd⟩
      refine ⟨ed, ld, gdG, wd, fun x hx h0x => ?_⟩
      rw [evd x hx h0x]
      unfold greedyStep
      dsimp only
      refine Finset.sum_congr rfl fun m _ => ?_
      have hpm := vpick m
      have hBm := hB g m pos
      rw [wireAt_extends he0 x (by omega), sempick x hx h0x m,
        wireAt_extends (extends_trans e1 (extends_trans e2 he0)) x (by omega)]
      have hfn : (fun c => wireAt gs1 x (okW c)) =
          (fun c => checkSubsets (fun c0 r j => b2z (wireAt gs x (B c0 r j)))
            (insertRow (fun r j => b2z (wireAt gs x (T r j))) (fun j => b2z (wireAt gs x (B g c j))))
            (k + 1) q' (subsetsWithout g)) := by
        funext c; exact semok x hx h0x c
      rw [hfn])
  simp only [h3] at s3
  rcases s3 with ⟨e3, l3, g3G, vv, semv⟩
  have hlen3 := extends_length_le e3
  rcases h4 : mkInsertRow inputs n T vW gs3 with ⟨gs4, T'⟩
  have s4 := mkInsertRow_spec h0 T vW g3G
    (fun r j => lt_of_lt_of_le (hT r j) (by omega)) vv
  simp only [h4] at s4
  rcases s4 with ⟨e4, l4, g4G, vT', semT'⟩
  have hlen4 := extends_length_le e4
  have hres : mkGreedyStep inputs n B g k q' T gs = (gs4, (T', vW)) := by
    simp only [mkGreedyStep, h1, h2, h3, h4]
  simp only [hres]
  refine ⟨extends_trans e1 (extends_trans e2 (extends_trans e3 e4)), ?_, g4G, vT',
    fun pos => lt_of_lt_of_le (vv pos) (by omega), fun x hx h0x => ?_⟩
  · nlinarith
  · refine ⟨fun r j => ?_, fun pos => ?_⟩
    · have heq := semT' x hx h0x r j
      have hT_eq : (fun r0 j0 => b2z (wireAt gs3 x (T r0 j0))) =
          (fun r0 j0 => b2z (wireAt gs x (T r0 j0))) := by
        funext r0 j0
        have hT0 := hT r0 j0
        rw [wireAt_extends (extends_trans e1 (extends_trans e2 e3)) x (by omega)]
      have hv_eq : (fun pos => b2z (wireAt gs3 x (vW pos))) =
          (greedyStep (fun c r0 j0 => b2z (wireAt gs x (B c r0 j0))) g k q'
            (fun r0 j0 => b2z (wireAt gs x (T r0 j0)))).2 := by
        funext pos; exact semv x hx h0x pos
      rw [hT_eq, hv_eq] at heq
      exact heq
    · have hvv := vv pos
      rw [wireAt_extends e4 x (by omega)]
      exact semv x hx h0x pos

private def mkGreedyRun (inputs n : ℕ) (B : Fin 3 → Fin n → Fin n → ℕ) (h : ℕ) :
    ∀ (k : ℕ), CG ((Fin n → Fin n → ℕ) × (Fin k → Fin n → ℕ))
  | 0, gs => (gs, (zeroMatW n, Fin.elim0))
  | k + 1, gs =>
    let (gs1, (Tprev, outPrev)) := mkGreedyRun inputs n B h k gs
    let (gs2, (Tnext, vnext)) := mkGreedyStep inputs n B (gOf h k) k (remQuota h (k + 1)) Tprev gs1
    (gs2, (Tnext, Fin.snoc outPrev vnext))

private lemma mkGreedyRun_spec {inputs n : ℕ} (h0 : 0 < inputs)
    (B : Fin 3 → Fin n → Fin n → ℕ) (h k : ℕ)
    {gs : List Gate} (hG : Good inputs gs)
    (hB : ∀ c : Fin 3, MatValid (inputs + gs.length) (B c)) :
    let res := mkGreedyRun inputs n B h k gs
    Extends gs res.1 ∧ res.1.length ≤ gs.length + k * (470 * (n + 1) ^ 4) ∧ Good inputs res.1 ∧
    MatValid (inputs + res.1.length) res.2.1 ∧
    (∀ idx : Fin k, VecValid (inputs + res.1.length) (res.2.2 idx)) ∧
    ∀ x : List Bool, x.length = inputs → x.getD 0 false = false →
      let gr := greedyRun (fun c r j => b2z (wireAt gs x (B c r j))) h k
      MatZSem res.1 x res.2.1 gr.1 ∧ ∀ idx : Fin k, VecZSem res.1 x (res.2.2 idx) (gr.2 idx) := by
  induction k with
  | zero =>
    refine ⟨extends_refl gs, by simp [mkGreedyRun], hG, fun _ _ => by simp [mkGreedyRun, zeroMatW]; omega,
      fun idx => idx.elim0, fun x hx h0x => ⟨fun r c => ?_, fun idx => idx.elim0⟩⟩
    dsimp only [mkGreedyRun, zeroMatW, greedyRun, zeroMat]
    rw [wireAt_input gs x (by omega), h0x]
    rfl
  | succ k ih =>
    rcases h1 : mkGreedyRun inputs n B h k gs with ⟨gs1, ⟨Tprev, outPrev⟩⟩
    simp only [h1] at ih
    rcases ih with ⟨e1, l1, g1G, vT1, vout1, sem1⟩
    have hlen1 := extends_length_le e1
    rcases h2 : mkGreedyStep inputs n B (gOf h k) k (remQuota h (k + 1)) Tprev gs1 with ⟨gs2, ⟨Tnext, vnext⟩⟩
    have s2 := mkGreedyStep_spec h0 B (gOf h k) k (remQuota h (k + 1)) Tprev g1G
      (fun c r j => lt_of_lt_of_le (hB c r j) (by omega)) vT1
    simp only [h2] at s2
    rcases s2 with ⟨e2, l2, g2G, vT2, vv2, sem2⟩
    have hlen2 := extends_length_le e2
    have hres : mkGreedyRun inputs n B h (k + 1) gs = (gs2, (Tnext, Fin.snoc outPrev vnext)) := by
      simp only [mkGreedyRun, h1, h2]
    simp only [hres]
    refine ⟨extends_trans e1 e2, ?_, g2G, vT2, ?_, fun x hx h0x => ?_⟩
    · have hmul : (k + 1) * (470 * (n + 1) ^ 4) = k * (470 * (n + 1) ^ 4) + 470 * (n + 1) ^ 4 :=
        Nat.succ_mul k _
      omega
    · intro idx
      refine Fin.lastCases ?_ ?_ idx
      · simpa [Fin.snoc] using vv2
      · intro j pos; simpa [Fin.snoc] using lt_of_lt_of_le (vout1 j pos) (by omega)
    · rcases sem1 x hx h0x with ⟨semT1, semout1⟩
      rcases sem2 x hx h0x with ⟨semT2, semv2⟩
      have hB_eq : (fun c r j => b2z (wireAt gs1 x (B c r j))) =
          (fun c r j => b2z (wireAt gs x (B c r j))) := by
        funext c r j; have hB0 := hB c r j; rw [wireAt_extends e1 x (by omega)]
      have hT_eq : (fun r j => b2z (wireAt gs1 x (Tprev r j))) =
          (greedyRun (fun c r j => b2z (wireAt gs x (B c r j))) h k).1 := by
        funext r j; exact semT1 r j
      rw [hB_eq, hT_eq] at semT2 semv2
      refine ⟨semT2, fun idx => ?_⟩
      refine Fin.lastCases ?_ ?_ idx
      · simpa [Fin.snoc, greedyRun] using semv2
      · intro j pos
        have hv1 := vout1 j pos
        simp only [Fin.snoc_castSucc, greedyRun]
        rw [wireAt_extends e2 x (by omega)]
        exact semout1 j pos

private lemma size_bound_main (n t h : ℕ) (h3h : 3 * h ≤ n) :
    3 * ((75 * t + 9) * (n + 1) ^ 3) + 9 * (82 * (n + 1) ^ 3) +
      (3 * h) * (470 * (n + 1) ^ 4) ≤ 2 ^ 20 * (n + t + h + 2) ^ 10 := by
  set M := n + t + h + 2
  have hM1 : n + 1 ≤ M := by omega
  have hM2 : t + 1 ≤ M := by omega
  have hM_pos : 1 ≤ M := by omega
  have h3 : (n + 1) ^ 3 ≤ M ^ 3 := Nat.pow_le_pow_left hM1 3
  have h4 : (n + 1) ^ 4 ≤ M ^ 4 := Nat.pow_le_pow_left hM1 4
  have h5 : M ^ 5 ≤ M ^ 10 := Nat.pow_le_pow_right hM_pos (by omega)
  have h45 : M ^ 4 ≤ M ^ 5 := Nat.pow_le_pow_right hM_pos (by omega)
  have h35 : M ^ 3 ≤ M ^ 5 := Nat.pow_le_pow_right hM_pos (by omega)
  have h1 : 3 * ((75 * t + 9) * (n + 1) ^ 3) ≤ 225 * M ^ 4 := by
    have ha : 3 * (75 * t + 9) ≤ 225 * M := by omega
    have hb : 3 * ((75 * t + 9) * (n + 1) ^ 3) = (3 * (75 * t + 9)) * (n + 1) ^ 3 := by ring
    rw [hb]
    calc (3 * (75 * t + 9)) * (n + 1) ^ 3 ≤ (225 * M) * M ^ 3 := Nat.mul_le_mul ha h3
      _ = 225 * M ^ 4 := by ring
  have h2 : 9 * (82 * (n + 1) ^ 3) ≤ 738 * M ^ 3 := by nlinarith
  have h3' : (3 * h) * (470 * (n + 1) ^ 4) ≤ 470 * M ^ 5 := by
    have ha : 3 * h ≤ M := by omega
    calc (3 * h) * (470 * (n + 1) ^ 4) = 470 * ((3 * h) * (n + 1) ^ 4) := by ring
      _ ≤ 470 * (M * M ^ 4) := Nat.mul_le_mul_left 470 (Nat.mul_le_mul ha h4)
      _ = 470 * M ^ 5 := by ring
  calc 3 * ((75 * t + 9) * (n + 1) ^ 3) + 9 * (82 * (n + 1) ^ 3) + (3 * h) * (470 * (n + 1) ^ 4)
      ≤ 225 * M ^ 4 + 738 * M ^ 3 + 470 * M ^ 5 := by omega
    _ ≤ 225 * M ^ 5 + 738 * M ^ 5 + 470 * M ^ 5 := by omega
    _ = 1433 * M ^ 5 := by ring
    _ ≤ 2 ^ 20 * M ^ 10 := Nat.mul_le_mul (by decide) h5

end PEqualNP.Outside.L_lib_613_aux

theorem PEqualNP.Outside.L_lib_613 : (∀ (n t h : ℕ) (owner : Fin t → Fin 3),
  let F := ZMod 2
  let X := Fin n → F
  let Slots := Fin 3 × Fin h
  let inputs := 1+t*n+t*n*n
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (flag : Fin (inputs+C.size))
    (out : Slots → Fin n → Fin (inputs+C.size)),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack inputs C ∧
    C.size ≤ 2^20 * (n+t+h+2)^10 ∧
    ∀ (l : Fin t → X) (a : Fin t → Matrix (Fin n) (Fin n) F),
      let eval := fun (j : Fin t) (x : X) =>
        (∑ i : Fin n, l j i*x i) + ∑ i : Fin n, ∑ b : Fin n, a j i b*x i*x b
      let valid := fun v : Slots → X =>
        LinearIndependent F v ∧
        ∀ (j : Fin t) (s : Fin h) (x : X), eval j (x+v (owner j,s)) = eval j x
      let pack := fun row : X => List.ofFn (fun bit : Fin n => decide (row bit ≠ 0))
      let bits := [false] ++ (List.ofFn (fun linearRow => pack (l linearRow))).flatten ++
        (List.ofFn (fun quadRow => (List.ofFn (fun coord => pack (a quadRow coord))).flatten)).flatten
      let wire := fun i : Fin (inputs+C.size) => (C.wires bits).getD i.val false
      (wire flag = true ↔ ∃ v, valid v) ∧
      (wire flag = true → valid (fun slot pos => if wire (out slot pos) then 1 else 0))) := by
  intro n t h owner F X Slots inputs
  by_cases hh0 : h = 0
  · subst hh0
    let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩], 0⟩
    have hsz : C.size = 1 := rfl
    refine ⟨C, ⟨inputs, by omega⟩, fun slot => slot.2.elim0, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [C, List.mem_singleton] at hg
      subst hg
      exact ⟨by simp, by simp⟩
    · intro j hj i hi
      simp only [C, List.length_singleton, Nat.lt_one_iff] at hj
      subst hj
      simp [PEqualNP.MetaComplexity.NestedCover.gateAt, C] at hi
    · have hpow : 1 ≤ (n + t + 0 + 2) ^ 10 := Nat.one_le_pow 10 _ (by omega)
      have : 1 ≤ 2 ^ 20 * (n + t + 0 + 2) ^ 10 := by nlinarith
      simpa [hsz] using this
    · intro l a eval valid pack bits wire
      have hbits_eq : bits = PEqualNP.Outside.L_lib_613_aux.encBits l a := rfl
      have hflag : wire ⟨inputs, by omega⟩ = true := by
        change PEqualNP.Outside.L_lib_613_aux.wireAt C.gates bits inputs = true
        rw [hbits_eq]
        have h := PEqualNP.Outside.L_lib_613_aux.wireAt_append_one_last []
          ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩
          (PEqualNP.Outside.L_lib_613_aux.encBits_length l a)
        simpa [C, inputs, PEqualNP.CircuitLowerBounds.GateOp.eval] using h
      refine ⟨?_, ?_⟩
      · constructor
        · intro _
          exact ⟨fun slot => slot.2.elim0, linearIndependent_empty_type, fun _ s => s.elim0⟩
        · intro _; exact hflag
      · intro _
        exact ⟨linearIndependent_empty_type, fun _ s => s.elim0⟩
  · have hh : 0 < h := Nat.pos_of_ne_zero hh0
    by_cases h3h : 3 * h ≤ n
    · have h0 : 0 < inputs := by omega
      rcases hB : PEqualNP.Outside.L_lib_613_aux.mkVec 3
          (fun g => PEqualNP.Outside.L_lib_613_aux.mkPeriodBasis n t owner g) [] with ⟨gs1, BW⟩
      have sB := PEqualNP.Outside.L_lib_613_aux.mkVec_spec (inputs := inputs)
        (cost := (75 * t + 9) * (n + 1) ^ 3)
        (WValid := PEqualNP.Outside.L_lib_613_aux.MatValid)
        (fun _ _ _ hle hM r c => lt_of_lt_of_le (hM r c) hle)
        (WSem := fun gs0 x MW target => ∀ (l : Fin t → X) (a : Fin t → Matrix (Fin n) (Fin n) F),
          x = PEqualNP.Outside.L_lib_613_aux.encBits l a →
          PEqualNP.Outside.L_lib_613_aux.MatZSem gs0 x MW (target l a))
        (fun g1 g2 x MW target hx he hM hs l a hxeq =>
          PEqualNP.Outside.L_lib_613_aux.matZSem_ext g1 g2 x MW (target l a) hx he hM (hs l a hxeq))
        (fun g => PEqualNP.Outside.L_lib_613_aux.mkPeriodBasis n t owner g)
        (fun _ g l a => PEqualNP.Outside.L_lib_613_aux.periodBasis owner l a g)
        (PEqualNP.Outside.L_lib_613_aux.good_nil inputs)
        (fun g gs0 hG0 _ => by
          rcases hp : PEqualNP.Outside.L_lib_613_aux.mkPeriodBasis n t owner g gs0 with ⟨gs', B0⟩
          have sp := PEqualNP.Outside.L_lib_613_aux.mkPeriodBasis_spec owner g hG0
          simp only [hp] at sp
          rcases sp with ⟨ep, lp, gpG, vp, semp⟩
          exact ⟨ep, lp, gpG, vp, fun x _ _ l a hxeq => hxeq ▸ semp l a⟩)
      simp only [hB] at sB
      rcases sB with ⟨e1, l1, g1G, vB, semB⟩
      rcases hF : PEqualNP.Outside.L_lib_613_aux.mkCheckSubsets inputs n BW
          (PEqualNP.Outside.L_lib_613_aux.zeroMatW n) 0 (fun _ => h)
          PEqualNP.Outside.L_lib_613_aux.allSubsets3 gs1 with ⟨gs2, flagW⟩
      have sF := PEqualNP.Outside.L_lib_613_aux.mkCheckSubsets_spec h0 BW
        (PEqualNP.Outside.L_lib_613_aux.zeroMatW n) 0 (fun _ => h)
        PEqualNP.Outside.L_lib_613_aux.allSubsets3 g1G vB
        (fun _ _ => by simp [PEqualNP.Outside.L_lib_613_aux.zeroMatW]; omega)
      simp only [hF] at sF
      rcases sF with ⟨e2, l2, g2G, wflag, semF⟩
      have hlen2 := PEqualNP.Outside.L_lib_613_aux.extends_length_le e2
      rcases hG : PEqualNP.Outside.L_lib_613_aux.mkGreedyRun inputs n BW h (3 * h) gs2 with ⟨gs3, ⟨_, outW⟩⟩
      have sG := PEqualNP.Outside.L_lib_613_aux.mkGreedyRun_spec h0 BW h (3 * h) g2G
        (fun c r j => lt_of_lt_of_le (vB c r j) (by omega))
      simp only [hG] at sG
      rcases sG with ⟨e3, l3, g3G, _, vout, semG⟩
      have hlen3 := PEqualNP.Outside.L_lib_613_aux.extends_length_le e3
      let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gs3, flagW⟩
      have hC_size : C.size = gs3.length := rfl
      refine ⟨C, ⟨flagW, lt_of_lt_of_le wflag (by omega)⟩,
        fun slot pos => ⟨outW (PEqualNP.Outside.L_lib_613_aux.slotIdx h slot) pos,
          vout (PEqualNP.Outside.L_lib_613_aux.slotIdx h slot) pos⟩,
        g3G.1, g3G.2, ?_, ?_⟩
      · rw [hC_size]
        have hlen_all : PEqualNP.Outside.L_lib_613_aux.allSubsets3.length = 8 := rfl
        rw [hlen_all] at l2
        simp only [List.length_nil, zero_add] at l1
        have htot : gs3.length ≤ 3 * ((75 * t + 9) * (n + 1) ^ 3) +
            9 * (82 * (n + 1) ^ 3) + (3 * h) * (470 * (n + 1) ^ 4) := by omega
        exact le_trans htot (PEqualNP.Outside.L_lib_613_aux.size_bound_main n t h h3h)
      · intro l a eval valid pack bits wire
        have hbits_eq : bits = PEqualNP.Outside.L_lib_613_aux.encBits l a := rfl
        have hx : bits.length = inputs := by
          rw [hbits_eq]; exact PEqualNP.Outside.L_lib_613_aux.encBits_length l a
        have h0x : bits.getD 0 false = false := by
          rw [hbits_eq]; exact PEqualNP.Outside.L_lib_613_aux.encBits_getD_zero l a
        have hB1 : ∀ c, (fun r j => PEqualNP.Outside.L_lib_613_aux.b2z
            (PEqualNP.Outside.L_lib_613_aux.wireAt gs1 bits (BW c r j))) =
            PEqualNP.Outside.L_lib_613_aux.periodBasis owner l a c := fun c => by
          funext r j
          exact semB bits hx h0x c l a hbits_eq r j
        have hflag_eq : wire ⟨flagW, lt_of_lt_of_le wflag (by omega)⟩ =
            PEqualNP.Outside.L_lib_613_aux.solveFlag owner l a h := by
          change PEqualNP.Outside.L_lib_613_aux.wireAt gs3 bits flagW = _
          rw [PEqualNP.Outside.L_lib_613_aux.wireAt_extends e3 bits (by omega),
            semF bits hx h0x]
          unfold PEqualNP.Outside.L_lib_613_aux.solveFlag
          dsimp only
          have hB_eq : (fun c r j => PEqualNP.Outside.L_lib_613_aux.b2z
              (PEqualNP.Outside.L_lib_613_aux.wireAt gs1 bits (BW c r j))) =
              (fun c => PEqualNP.Outside.L_lib_613_aux.periodBasis owner l a c) := by
            funext c; exact hB1 c
          have hZ_eq : (fun r j => PEqualNP.Outside.L_lib_613_aux.b2z
              (PEqualNP.Outside.L_lib_613_aux.wireAt gs1 bits
                (PEqualNP.Outside.L_lib_613_aux.zeroMatW n r j))) =
              PEqualNP.Outside.L_lib_613_aux.zeroMat n := by
            funext r j
            dsimp only [PEqualNP.Outside.L_lib_613_aux.zeroMatW, PEqualNP.Outside.L_lib_613_aux.zeroMat]
            rw [PEqualNP.Outside.L_lib_613_aux.wireAt_input gs1 bits (by omega), h0x]
            rfl
          rw [hB_eq, hZ_eq]
        have hout_eq : (fun slot pos => if wire ⟨outW (PEqualNP.Outside.L_lib_613_aux.slotIdx h slot) pos,
              vout (PEqualNP.Outside.L_lib_613_aux.slotIdx h slot) pos⟩ then (1 : ZMod 2) else 0) =
            PEqualNP.Outside.L_lib_613_aux.solveOut owner l a h := by
          funext slot pos
          change PEqualNP.Outside.L_lib_613_aux.b2z
            (PEqualNP.Outside.L_lib_613_aux.wireAt gs3 bits
              (outW (PEqualNP.Outside.L_lib_613_aux.slotIdx h slot) pos)) = _
          have hsem := (semG bits hx h0x).2 (PEqualNP.Outside.L_lib_613_aux.slotIdx h slot) pos
          have hB2 : (fun c r j => PEqualNP.Outside.L_lib_613_aux.b2z
              (PEqualNP.Outside.L_lib_613_aux.wireAt gs2 bits (BW c r j))) =
              (fun c => PEqualNP.Outside.L_lib_613_aux.periodBasis owner l a c) := by
            funext c r j
            rw [PEqualNP.Outside.L_lib_613_aux.wireAt_extends e2 bits (by rw [hx]; exact vB c r j)]
            exact congrFun (congrFun (hB1 c) r) j
          rw [hB2] at hsem
          exact hsem
        refine ⟨?_, ?_⟩
        · rw [hflag_eq]
          constructor
          · intro hfl
            exact ⟨PEqualNP.Outside.L_lib_613_aux.solveOut owner l a h,
              PEqualNP.Outside.L_lib_613_aux.solveOut_valid hh owner l a hfl⟩
          · rintro ⟨v, hli, hper⟩
            exact (PEqualNP.Outside.L_lib_613_aux.solveFlag_eq_true_iff_rado owner l a h).mpr
              (PEqualNP.Outside.L_lib_613_aux.rado_of_valid owner l a v hli hper)
        · intro hfl
          rw [hflag_eq] at hfl
          rw [hout_eq]
          exact PEqualNP.Outside.L_lib_613_aux.solveOut_valid hh owner l a hfl
    · let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[], 0⟩
      refine ⟨C, ⟨0, by omega⟩, fun _ _ => ⟨0, by omega⟩,
        (PEqualNP.Outside.L_lib_613_aux.good_nil inputs).1,
        (PEqualNP.Outside.L_lib_613_aux.good_nil inputs).2,
        Nat.zero_le _, ?_⟩
      intro l a eval valid pack bits wire
      have hflag : wire ⟨0, by omega⟩ = false := by
        change (C.wires bits).getD 0 false = false
        simp [C, PEqualNP.CircuitLowerBounds.Circuit.wires, bits]
      refine ⟨?_, ?_⟩
      · constructor
        · intro h; rw [hflag] at h; exact Bool.noConfusion h
        · rintro ⟨v, hli, _⟩
          have hle := hli.fintype_card_le_finrank
          simp only [Slots, X, F, Fintype.card_prod, Fintype.card_fin, Module.finrank_pi] at hle
          omega
      · intro h; rw [hflag] at h; exact Bool.noConfusion h
