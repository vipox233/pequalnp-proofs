import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5884_aux
def zeroSet {n : Nat} (L : Fin n → Finset (Fin n)) (Y : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun p => ∀ t∈Y, p∉L t)
end PEqualNP.Outside.L_meta_5884_aux

namespace PEqualNP.Outside.L_meta_5884_aux.Protocol

open PEqualNP.MetaComplexity

private def leafLabel {n : ℕ} : (F : DMFormula n) → Fin F.leaves → Fin n
  | .lit i _, _ => i
  | .and a b, x => Fin.addCases (leafLabel a) (leafLabel b) x
  | .or a b, x => Fin.addCases (leafLabel a) (leafLabel b) x

private lemma partition_splitUnique {m n : ℕ} {P : Fin (m + n) → Prop}
    (h : ((∃! i : Fin m, P (Fin.castAdd n i)) ∧ (∀ j : Fin n, ¬ P (Fin.natAdd m j))) ∨
      ((∀ i : Fin m, ¬ P (Fin.castAdd n i)) ∧ (∃! j : Fin n, P (Fin.natAdd m j)))) :
    ∃! i, P i := by
  rcases h with ⟨⟨i, hi, hunique⟩, hnone⟩ | ⟨hnone, ⟨j, hj, hunique⟩⟩
  · refine ⟨Fin.castAdd n i, hi, ?_⟩
    intro k
    refine Fin.addCases (motive := fun k => P k → k = Fin.castAdd n i) ?_ ?_ k
    · intro k hk
      exact congrArg (Fin.castAdd n) (hunique k hk)
    · intro k hk
      exact (hnone k hk).elim
  · refine ⟨Fin.natAdd m j, hj, ?_⟩
    intro k
    refine Fin.addCases (motive := fun k => P k → k = Fin.natAdd m j) ?_ ?_ k
    · intro k hk
      exact (hnone k hk).elim
    · intro k hk
      exact congrArg (Fin.natAdd m) (hunique k hk)

private lemma partition_formulaRectanglesStrong {n : ℕ}
    (φ : PEqualNP.MetaComplexity.DMFormula n)
    (mono : PEqualNP.MetaComplexity.DMFormula.rec
      (motive := fun _ : PEqualNP.MetaComplexity.DMFormula n => Prop)
      (fun (_ : Fin n) (c : Bool) => c = true) (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) φ) :
    ∃ (X Y : Fin φ.leaves → (Fin n → Bool) → Prop) (label : Fin φ.leaves → Fin n),
      (∀ x y, φ.eval x = true → φ.eval y = false → ∃! i, X i x ∧ Y i y) ∧
        (∀ i x, X i x → φ.eval x = true ∧ x (label i) = true) ∧
        (∀ i y, Y i y → φ.eval y = false ∧ y (label i) = false) ∧
        label = leafLabel φ := by
  induction φ with
  | lit v c =>
      change c = true at mono
      subst c
      refine ⟨fun _ x => x v = true, fun _ y => y v = false, fun _ => v, ?_, ?_, ?_, rfl⟩
      · intro x y hx hy
        change ∃! _i : Fin 1, x v = true ∧ y v = false
        exact ⟨0, ⟨by simpa [PEqualNP.MetaComplexity.DMFormula.eval] using hx,
          by simpa [PEqualNP.MetaComplexity.DMFormula.eval] using hy⟩,
          fun i _ => Subsingleton.elim i 0⟩
      · intro i x hx
        exact ⟨by simpa [PEqualNP.MetaComplexity.DMFormula.eval] using hx, hx⟩
      · intro i y hy
        exact ⟨by simpa [PEqualNP.MetaComplexity.DMFormula.eval] using hy, hy⟩
  | and a b ihA ihB =>
      obtain ⟨XA, YA, LA, totalA, xA, yA, eqA⟩ := ihA mono.1
      obtain ⟨XB, YB, LB, totalB, xB, yB, eqB⟩ := ihB mono.2
      let X : Fin (a.leaves + b.leaves) → (Fin n → Bool) → Prop :=
        Fin.addCases (fun i x => XA i x ∧ b.eval x = true) (fun i x => XB i x ∧ a.eval x = true)
      let Y : Fin (a.leaves + b.leaves) → (Fin n → Bool) → Prop :=
        Fin.addCases YA (fun i y => YB i y ∧ a.eval y = true)
      let label : Fin (a.leaves + b.leaves) → Fin n := Fin.addCases LA LB
      refine ⟨X, Y, label, ?_, ?_, ?_, ?_⟩
      · intro x y hx hy
        have hx' : a.eval x = true ∧ b.eval x = true := by
          simpa only [PEqualNP.MetaComplexity.DMFormula.eval, Bool.and_eq_true_iff] using hx
        apply partition_splitUnique
        cases ha : a.eval y with
        | false =>
            left
            constructor
            · simpa [X, Y, hx'.2] using totalA x y hx'.1 ha
            · intro i
              simp [X, Y, ha, Fin.addCases_right]
        | true =>
            right
            have hb : b.eval y = false := by
              simpa [PEqualNP.MetaComplexity.DMFormula.eval, ha] using hy
            constructor
            · intro i hi
              have hLeft : YA i y := by simpa [Y] using hi.2
              have hFalse := (yA i y hLeft).1
              simp [ha] at hFalse
            · simpa [X, Y, hx'.1, ha, Fin.addCases_right] using totalB x y hx'.2 hb
      · intro i
        induction i using Fin.addCases with
        | left i =>
            intro x hx
            have h : XA i x ∧ b.eval x = true := by simpa [X] using hx
            obtain ⟨ha, hv⟩ := xA i x h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, ha, h.2],
              by simpa [label] using hv⟩
        | right i =>
            intro x hx
            have h : XB i x ∧ a.eval x = true := by simpa [X, Fin.addCases_right] using hx
            obtain ⟨hb, hv⟩ := xB i x h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, hb, h.2],
              by simpa [label, Fin.addCases_right] using hv⟩
      · intro i
        induction i using Fin.addCases with
        | left i =>
            intro y hy
            have h : YA i y := by simpa [Y] using hy
            obtain ⟨ha, hv⟩ := yA i y h
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, ha],
              by simpa [label] using hv⟩
        | right i =>
            intro y hy
            have h : YB i y ∧ a.eval y = true := by simpa [Y, Fin.addCases_right] using hy
            obtain ⟨hb, hv⟩ := yB i y h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, hb],
              by simpa [label, Fin.addCases_right] using hv⟩
      · simp only [label, leafLabel, eqA, eqB]; rfl
  | or a b ihA ihB =>
      obtain ⟨XA, YA, LA, totalA, xA, yA, eqA⟩ := ihA mono.1
      obtain ⟨XB, YB, LB, totalB, xB, yB, eqB⟩ := ihB mono.2
      let X : Fin (a.leaves + b.leaves) → (Fin n → Bool) → Prop :=
        Fin.addCases XA (fun i x => XB i x ∧ a.eval x = false)
      let Y : Fin (a.leaves + b.leaves) → (Fin n → Bool) → Prop :=
        Fin.addCases (fun i y => YA i y ∧ b.eval y = false) (fun i y => YB i y ∧ a.eval y = false)
      let label : Fin (a.leaves + b.leaves) → Fin n := Fin.addCases LA LB
      refine ⟨X, Y, label, ?_, ?_, ?_, ?_⟩
      · intro x y hx hy
        have hy' : a.eval y = false ∧ b.eval y = false := by
          simpa only [PEqualNP.MetaComplexity.DMFormula.eval, Bool.or_eq_false_iff] using hy
        apply partition_splitUnique
        cases ha : a.eval x with
        | false =>
            right
            have hb : b.eval x = true := by
              simpa [PEqualNP.MetaComplexity.DMFormula.eval, ha] using hx
            constructor
            · intro i hi
              have hLeft : XA i x := by simpa [X] using hi.1
              have hTrue := (xA i x hLeft).1
              simp [ha] at hTrue
            · simpa [X, Y, hy'.1, ha, Fin.addCases_right] using totalB x y hb hy'.2
        | true =>
            left
            constructor
            · simpa [X, Y, hy'.2] using totalA x y ha hy'.1
            · intro i
              simp [X, Y, ha, Fin.addCases_right]
      · intro i
        induction i using Fin.addCases with
        | left i =>
            intro x hx
            have h : XA i x := by simpa [X] using hx
            obtain ⟨ha, hv⟩ := xA i x h
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, ha],
              by simpa [label] using hv⟩
        | right i =>
            intro x hx
            have h : XB i x ∧ a.eval x = false := by simpa [X, Fin.addCases_right] using hx
            obtain ⟨hb, hv⟩ := xB i x h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, hb],
              by simpa [label, Fin.addCases_right] using hv⟩
      · intro i
        induction i using Fin.addCases with
        | left i =>
            intro y hy
            have h : YA i y ∧ b.eval y = false := by simpa [Y] using hy
            obtain ⟨ha, hv⟩ := yA i y h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, ha, h.2],
              by simpa [label] using hv⟩
        | right i =>
            intro y hy
            have h : YB i y ∧ a.eval y = false := by simpa [Y, Fin.addCases_right] using hy
            obtain ⟨hb, hv⟩ := yB i y h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, hb, h.2],
              by simpa [label, Fin.addCases_right] using hv⟩
      · simp only [label, leafLabel, eqA, eqB]; rfl

noncomputable def degree {n : ℕ} (i : Fin n) (F : DMFormula n) : ℕ :=
  DMFormula.rec (motive := fun _ => ℕ) (fun j _ => if j = i then 1 else 0)
    (fun _ _ a b => a + b) (fun _ _ a b => max a b) F

noncomputable def positive {n : ℕ} (F : DMFormula n) : Bool :=
  DMFormula.rec (motive := fun _ => Bool) (fun _ b => b)
    (fun _ _ a b => a && b) (fun _ _ a b => a && b) F

private lemma mono_of_positive {n : ℕ} (F : DMFormula n) (hp : positive F = true) :
    DMFormula.rec (motive := fun _ : DMFormula n => Prop)
      (fun (_ : Fin n) (c : Bool) => c = true) (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) F := by
  induction F with
  | lit _ _ => exact hp
  | and _ _ ihA ihB =>
    exact ⟨ihA (Bool.and_eq_true_iff.mp hp).1, ihB (Bool.and_eq_true_iff.mp hp).2⟩
  | or _ _ ihA ihB =>
    exact ⟨ihA (Bool.and_eq_true_iff.mp hp).1, ihB (Bool.and_eq_true_iff.mp hp).2⟩

private lemma degree_le_labels {n : ℕ} (F : DMFormula n) (i : Fin n) :
    degree i F ≤ Fintype.card {j : Fin F.leaves // leafLabel F j = i} := by
  have count (m : ℕ) (f : Fin m → Fin n) :
      Fintype.card {j : Fin m // f j = i} = ∑ j : Fin m, if f j = i then 1 else 0 := by
    rw [Fintype.card_subtype, Finset.card_filter]
  simp only [count]
  induction F with
  | lit j b =>
    change (if j = i then 1 else 0) ≤ ∑ _ : Fin 1, if j = i then 1 else 0
    simp
  | and a b ihA ihB =>
    change degree i a + degree i b ≤ ∑ j : Fin (a.leaves + b.leaves),
      if Fin.addCases (leafLabel a) (leafLabel b) j = i then 1 else 0
    rw [Fin.sum_univ_add]
    simpa only [Fin.addCases_left, Fin.addCases_right] using Nat.add_le_add ihA ihB
  | or a b ihA ihB =>
    change max (degree i a) (degree i b) ≤ ∑ j : Fin (a.leaves + b.leaves),
      if Fin.addCases (leafLabel a) (leafLabel b) j = i then 1 else 0
    rw [Fin.sum_univ_add]
    have sumBound := Nat.add_le_add ihA ihB
    exact (max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)).trans
      (by simpa only [Fin.addCases_left, Fin.addCases_right] using sumBound)

lemma partitionFormula (n : ℕ) (F : DMFormula n) (hp : positive F = true) :
    ∃ (A B : Fin F.leaves → (Fin n → Bool) → Prop) (tag : Fin F.leaves → Fin n),
      (∀ i x, A i x → x (tag i) = true) ∧
      (∀ i y, B i y → y (tag i) = false) ∧
      (∀ x y, F.eval x = true → F.eval y = false → ∃! i, A i x ∧ B i y) ∧
      (∀ v, degree v F ≤ Fintype.card {i : Fin F.leaves // tag i = v}) := by
  obtain ⟨A, B, label, partition, hA, hB, eq⟩ :=
    partition_formulaRectanglesStrong F (mono_of_positive F hp)
  exact ⟨A, B, label, (fun i x hx => (hA i x hx).2), (fun i y hy => (hB i y hy).2),
    partition, (fun v => by rw [eq]; exact degree_le_labels F v)⟩


def countLab {n : ℕ} (v : Fin n) : DMFormula n → ℕ
  | .lit j _ => if j = v then 1 else 0
  | .and a b => countLab v a + countLab v b
  | .or a b => countLab v a + countLab v b

private lemma countLab_eq_labels {n : ℕ} (F : DMFormula n) (i : Fin n) :
    countLab i F = Fintype.card {j : Fin F.leaves // leafLabel F j = i} := by
  have count (m : ℕ) (f : Fin m → Fin n) :
      Fintype.card {j : Fin m // f j = i} = ∑ j : Fin m, if f j = i then 1 else 0 := by
    rw [Fintype.card_subtype, Finset.card_filter]
  simp only [count]
  induction F with
  | lit j b =>
    change (if j = i then 1 else 0) = ∑ _ : Fin 1, if j = i then 1 else 0
    simp
  | and a b ihA ihB =>
    change countLab i a + countLab i b = ∑ j : Fin (a.leaves + b.leaves),
      if Fin.addCases (leafLabel a) (leafLabel b) j = i then 1 else 0
    rw [Fin.sum_univ_add]
    simpa only [Fin.addCases_left, Fin.addCases_right] using congrArg₂ (· + ·) ihA ihB
  | or a b ihA ihB =>
    change countLab i a + countLab i b = ∑ j : Fin (a.leaves + b.leaves),
      if Fin.addCases (leafLabel a) (leafLabel b) j = i then 1 else 0
    rw [Fin.sum_univ_add]
    simpa only [Fin.addCases_left, Fin.addCases_right] using congrArg₂ (· + ·) ihA ihB

lemma partitionFormulaExact (n : ℕ) (F : DMFormula n) (hp : positive F = true) :
    ∃ (A B : Fin F.leaves → (Fin n → Bool) → Prop) (tag : Fin F.leaves → Fin n),
      (∀ i x, A i x → x (tag i) = true) ∧
      (∀ i y, B i y → y (tag i) = false) ∧
      (∀ x y, F.eval x = true → F.eval y = false → ∃! i, A i x ∧ B i y) ∧
      (∀ v, degree v F ≤ Fintype.card {i : Fin F.leaves // tag i = v}) ∧
      (∀ v, countLab v F = Fintype.card {i : Fin F.leaves // tag i = v}) := by
  obtain ⟨A, B, label, partition, hA, hB, eq⟩ :=
    partition_formulaRectanglesStrong F (mono_of_positive F hp)
  exact ⟨A, B, label, (fun i x hx => (hA i x hx).2), (fun i y hy => (hB i y hy).2),
    partition, (fun v => by rw [eq]; exact degree_le_labels F v),
    (fun v => by rw [eq]; exact countLab_eq_labels F v)⟩
end PEqualNP.Outside.L_meta_5884_aux.Protocol

namespace PEqualNP.Outside.L_meta_5884_aux.Table


private def inc (p l : Fin 7) : Prop := p = l ∨ p = l + 1 ∨ p = l + 3
private def lines (l : Fin 7) : Finset (Fin 7) :=
  Finset.univ.filter (fun p => p = l ∨ p = l + 1 ∨ p = l + 3)

private def pointData : ℕ := 0x6435360d1d6a22c8
private def lineData : ℕ := 0x6dadb246da489200
private def starData : ℕ := 0x2939460f7358b5250731483104148ae0e4354549c53311e30c980
private def masksData : ℕ := 0x2081840a409112818bc08308409902a5a0c086224cac2822e461439197177f
private def weightData : ℕ := 0x145965965965a75a769a5964539d35919d35935935935930114d64545164534535939d30116969d65964d65965a74d65964d65a76935915144564d64d14c04e745a9d65935965965935965939d65939d15966945165a75965965a759a4534d14c04d16a75935965935964e75934565145969d14d14d30134565965969d669a5964e75a74d65935964d15945114405935934e74d15934d64e74d16969d65965969d65965966965145965914da5969d35969d65965a76914d34c04675935964d64d64545164535966a75964d65a74d14d30115965969da5964d69d35935915144564d64da5a75965910135934e74564d34e74569d65965965966945165965a75a759659a4534da5a75964404d34d14d34d15a75965965145914d69d10134d34565936965a75969d65966934d34675965965945115934405a74d34d159359a9d65965a74d34d159659a5965a759651459659a5914d39d65965a75a75966914d35a75804d34534d15965945115936a75964d65965939d10134d15964d65969d659a4d34675965145914da5964d65a75914c05a74d34564d69d65a74d345659a5965945166965964674d35965965914d39d65969e759a4d359601345345651459a5914d65964e75914e75964d65964e70134564d65a759a4d15945116a75935964d65965935964d65964530274d14d69d69d34566965146965919d65964d35965964674d35965964d35969e76934d601145451a4675965935964d65964d65964d64539d64d64e70115935a76915146965965914e74d65919d35964d65964d64d65930274535969d1694
private def criticalData : ℕ := 0x569c4db84c4973dd7ca51618d383209

private def pointAt (r : Fin 21) : Fin 7 := ⟨((pointData >>> (3 * r.val)) % 8) % 7, Nat.mod_lt _ (by decide)⟩
private def lineAt (r : Fin 21) : Fin 7 := ⟨((lineData >>> (3 * r.val)) % 8) % 7, Nat.mod_lt _ (by decide)⟩
private def rowAt (v : Fin 14) (i : Fin 3) : Fin 21 :=
  ⟨((starData >>> (5 * (3 * v.val + i.val))) % 32) % 21, Nat.mod_lt _ (by decide)⟩
private def columnAt (c : Fin 37) : Finset (Fin 7) :=
  Finset.univ.filter fun l => (masksData >>> (7 * c.val)).testBit l.val
private def criticalAt (r : Fin 21) : Fin 37 :=
  ⟨((criticalData >>> (6 * r.val)) % 64) % 37, Nat.mod_lt _ (by decide)⟩
private def positive (r : Fin 21) (i : Fin 14) : Bool :=
  decide (i = Fin.castAdd 7 (pointAt r) ∨ i = Fin.natAdd 7 (lineAt r))
private def negative (c : Fin 37) : Fin 14 → Bool :=
  Fin.append (fun p => decide (p ∈ zeroSet lines (columnAt c))) (fun l => decide (l ∈ columnAt c))
private def weight (r : Fin 21) (c : Fin 37) : ℤ :=
  Int.ofNat ((weightData >>> (6 * (37 * r.val + c.val))) % 64) - 20
private def maskRows (v : Fin 14) (M : Finset (Fin 3)) : Finset (Fin 21) :=
  M.image (rowAt v)
private def mass (v : Fin 14) (M : Finset (Fin 3)) (c : Fin 37) : ℤ :=
  ∑ r ∈ maskRows v M, weight r c

set_option maxHeartbeats 0 in
private lemma edges_exact :
    (∀ r, inc (pointAt r) (lineAt r)) ∧
    ∀ p l, p = l ∨ p = l + 1 ∨ p = l + 3 →
      ∃ r, pointAt r = p ∧ lineAt r = l := by
  unfold inc
  decide +kernel

set_option maxHeartbeats 0 in
private lemma stars_exact :
    ∀ v r, positive r v = true ↔ ∃ a : Fin 3, rowAt v a = r := by
  decide +kernel

set_option maxHeartbeats 0 in
private lemma columns_maximal : ∀ c, ∀ l ∉ columnAt c,
    ∃ p ∈ zeroSet lines (columnAt c), p = l ∨ p = l + 1 ∨ p = l + 3 := by
  decide +kernel

set_option maxHeartbeats 0 in
private lemma total_weight : (∑ r : Fin 21, ∑ c : Fin 37, weight r c) = 1680 := by
  decide +kernel

set_option maxHeartbeats 0 in
private lemma pattern_bound : ∀ (v : Fin 14) (M : Finset (Fin 3)),
    (∑ c : Fin 37, if negative c v = false then max 0 (mass v M c) else 0) ≤ 60 := by
  decide +kernel

set_option maxHeartbeats 0 in
private lemma critical_pattern : ∀ (r : Fin 21) (v : Fin 14) (M : Finset (Fin 3)),
    r ∈ maskRows v M → negative (criticalAt r) v = false →
      0 ≤ mass v M (criticalAt r) → M = Finset.univ := by
  decide +kernel

set_option maxHeartbeats 0 in
private lemma overlap : ∀ (v : Fin 14) (M : Finset (Fin 3)), M.Nonempty →
    ∃ (a : Fin 3) (c : Fin 37), a ∈ M ∧ negative c v = false ∧
      0 < mass v M c ∧ 0 < mass v Finset.univ c := by
  decide +kernel

lemma verifyPartition_lower (k : ℕ) (A B : Fin k → (Fin 14 → Bool) → Prop)
    (tag : Fin k → Fin 14)
    (supportsA : ∀ i x, A i x → x (tag i) = true)
    (supportsB : ∀ i y, B i y → y (tag i) = false)
    (covers : ∀ r c, ∃! i, A i (positive r) ∧ B i (negative c)) : 28≤k := by
  classical
  let M (i : Fin k) : Finset (Fin 3) := Finset.univ.filter (fun a => A i (positive (rowAt (tag i) a)))
  let rows (i : Fin k) : Finset (Fin 21) := Finset.univ.filter (fun r => A i (positive r))
  have rows_eq (i : Fin k) : rows i = maskRows (tag i) (M i) := by
    ext r
    simp only [rows, M, maskRows, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hr
      obtain ⟨a, ha⟩ := (stars_exact (tag i) r).mp (supportsA i (positive r) hr)
      exact ⟨a, ha.symm ▸ hr, ha⟩
    · rintro ⟨a, ha, rfl⟩
      exact ha
  let actual (i : Fin k) (c : Fin 37) : ℤ :=
    if B i (negative c) then mass (tag i) (M i) c else 0
  let allowance (i : Fin k) (c : Fin 37) : ℤ :=
    if negative c (tag i) = false then max 0 (mass (tag i) (M i) c) else 0
  let total (i : Fin k) : ℤ := ∑ c : Fin 37, actual i c
  have pointwise (i : Fin k) (c : Fin 37) : actual i c ≤ allowance i c := by
    by_cases hb : B i (negative c)
    · simp only [actual, allowance, hb, supportsB i _ hb, ite_true]
      exact le_max_right _ _
    · unfold actual allowance
      rw [ite_eq_right hb]
      split <;> simp
  have each (i : Fin k) : total i ≤ 60 :=
    (Finset.sum_le_sum fun c _ => pointwise i c).trans (pattern_bound (tag i) (M i))
  have expand (i : Fin k) (c : Fin 37) :
      actual i c = ∑ r : Fin 21, if A i (positive r) ∧ B i (negative c) then weight r c else 0 := by
    by_cases hb : B i (negative c)
    · simp only [actual, hb, ite_true, and_true]
      change (∑ r ∈ maskRows (tag i) (M i), weight r c) = _
      rw [← rows_eq]
      change (∑ r ∈ Finset.univ.filter (fun r => A i (positive r)), weight r c) = _
      rw [Finset.sum_filter]
    · simp [actual, hb]
  have one (r : Fin 21) (c : Fin 37) :
      (∑ i : Fin k, if A i (positive r) ∧ B i (negative c) then weight r c else 0) = weight r c := by
    obtain ⟨i, hi, unique⟩ := covers r c
    rw [Finset.sum_eq_single i]
    · exact ite_eq_left hi
    · intro j _ neq
      exact ite_eq_right (fun hj => neq (unique j hj))
    · simp
  have total_eq : (∑ i : Fin k, total i) = 1680 := by
    calc
      (∑ i : Fin k, total i) =
          ∑ i : Fin k, ∑ c : Fin 37, ∑ r : Fin 21,
            if A i (positive r) ∧ B i (negative c) then weight r c else 0 := by
        simp only [total, expand]
      _ = ∑ c : Fin 37, ∑ r : Fin 21, ∑ i : Fin k,
            if A i (positive r) ∧ B i (negative c) then weight r c else 0 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro c _
        rw [Finset.sum_comm]
      _ = 1680 := by
        simp only [one]
        rw [Finset.sum_comm]
        exact total_weight
  have bound : (∑ i : Fin k, total i) ≤ ∑ _i : Fin k, (60 : ℤ) := Finset.sum_le_sum (fun i _ => each i)
  rw [total_eq] at bound
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at bound
  have lower : (28 : ℤ)≤(k : ℤ) := by omega
  exact_mod_cast lower

lemma verifyPartition (k : ℕ) (A B : Fin k → (Fin 14 → Bool) → Prop)
    (tag : Fin k → Fin 14) (limit : k ≤ 28)
    (supportsA : ∀ i x, A i x → x (tag i) = true)
    (supportsB : ∀ i y, B i y → y (tag i) = false)
    (covers : ∀ r c, ∃! i, A i (positive r) ∧ B i (negative c)) :
    ∀ p l, inc p l →
      Fintype.card {i : Fin k // tag i = Fin.castAdd 7 p} ≤ 1 ∨
      Fintype.card {i : Fin k // tag i = Fin.natAdd 7 l} ≤ 1 := by
  classical
  let M (i : Fin k) : Finset (Fin 3) := Finset.univ.filter (fun a => A i (positive (rowAt (tag i) a)))
  let rows (i : Fin k) : Finset (Fin 21) := Finset.univ.filter (fun r => A i (positive r))
  have rows_eq (i : Fin k) : rows i = maskRows (tag i) (M i) := by
    ext r
    simp only [rows, M, maskRows, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hr
      obtain ⟨a, ha⟩ := (stars_exact (tag i) r).mp (supportsA i (positive r) hr)
      exact ⟨a, ha.symm ▸ hr, ha⟩
    · rintro ⟨a, ha, rfl⟩
      exact ha
  let actual (i : Fin k) (c : Fin 37) : ℤ :=
    if B i (negative c) then mass (tag i) (M i) c else 0
  let allowance (i : Fin k) (c : Fin 37) : ℤ :=
    if negative c (tag i) = false then max 0 (mass (tag i) (M i) c) else 0
  let total (i : Fin k) : ℤ := ∑ c : Fin 37, actual i c
  have pointwise (i : Fin k) (c : Fin 37) : actual i c ≤ allowance i c := by
    by_cases hb : B i (negative c)
    · simp only [actual, allowance, hb, supportsB i _ hb, ite_true]
      exact le_max_right _ _
    · unfold actual allowance
      rw [ite_eq_right hb]
      split <;> simp
  have each (i : Fin k) : total i ≤ 60 :=
    (Finset.sum_le_sum fun c _ => pointwise i c).trans (pattern_bound (tag i) (M i))
  have expand (i : Fin k) (c : Fin 37) :
      actual i c = ∑ r : Fin 21, if A i (positive r) ∧ B i (negative c) then weight r c else 0 := by
    by_cases hb : B i (negative c)
    · simp only [actual, hb, ite_true, and_true]
      change (∑ r ∈ maskRows (tag i) (M i), weight r c) = _
      rw [← rows_eq]
      change (∑ r ∈ Finset.univ.filter (fun r => A i (positive r)), weight r c) = _
      rw [Finset.sum_filter]
    · simp [actual, hb]
  have one (r : Fin 21) (c : Fin 37) :
      (∑ i : Fin k, if A i (positive r) ∧ B i (negative c) then weight r c else 0) = weight r c := by
    obtain ⟨i, hi, unique⟩ := covers r c
    rw [Finset.sum_eq_single i]
    · exact ite_eq_left hi
    · intro j _ neq
      exact ite_eq_right (fun hj => neq (unique j hj))
    · simp
  have total_eq : (∑ i : Fin k, total i) = 1680 := by
    calc
      (∑ i : Fin k, total i) =
          ∑ i : Fin k, ∑ c : Fin 37, ∑ r : Fin 21,
            if A i (positive r) ∧ B i (negative c) then weight r c else 0 := by
        simp only [total, expand]
      _ = ∑ c : Fin 37, ∑ r : Fin 21, ∑ i : Fin k,
            if A i (positive r) ∧ B i (negative c) then weight r c else 0 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro c _
        rw [Finset.sum_comm]
      _ = 1680 := by
        simp only [one]
        rw [Finset.sum_comm]
        exact total_weight
  have totals_tight (i : Fin k) : total i = 60 := by
    have k' : (k : ℤ) ≤ 28 := by exact_mod_cast limit
    have noSlack : (∑ j : Fin k, ((60 : ℤ) - total j)) ≤ 0 := by
      rw [Finset.sum_sub_distrib, total_eq]
      simp
      omega
    have localSlack : 60 - total i ≤ ∑ j : Fin k, (60 - total j) :=
      Finset.single_le_sum (fun j _ => sub_nonneg.mpr (each j)) (Finset.mem_univ i)
    have bound := each i
    omega
  have tight (i : Fin k) (c : Fin 37) : actual i c = allowance i c := by
    have noSlack : (∑ j : Fin 37, (allowance i j - actual i j)) ≤ 0 := by
      rw [Finset.sum_sub_distrib]
      change (∑ j : Fin 37, allowance i j) - total i ≤ 0
      have upper := pattern_bound (tag i) (M i)
      change (∑ j : Fin 37, allowance i j) ≤ 60 at upper
      rw [totals_tight]
      omega
    have localSlack : allowance i c - actual i c ≤
        ∑ j : Fin 37, (allowance i j - actual i j) :=
      Finset.single_le_sum (fun j _ => sub_nonneg.mpr (pointwise i j)) (Finset.mem_univ c)
    have bound := pointwise i c
    omega
  have must (i : Fin k) (c : Fin 37) (legal : negative c (tag i) = false)
      (pos : 0 < mass (tag i) (M i) c) : B i (negative c) := by
    by_contra no
    have equal := tight i c
    simp only [actual, allowance, no, legal, ite_true, ite_false, max_eq_right pos.le] at equal
    omega
  have nonempty (i : Fin k) : (M i).Nonempty := by
    by_contra no
    have hempty : M i = ∅ := Finset.not_nonempty_iff_eq_empty.mp no
    have t := totals_tight i
    simp [total, actual, mass, maskRows, hempty] at t
  have singleton (i : Fin k) (full : M i = Finset.univ) :
      Fintype.card {j : Fin k // tag j = tag i} ≤ 1 := by
    rw [Fintype.card_subtype, Finset.card_le_one]
    have only (j : Fin k) (hj : tag j = tag i) : j = i := by
      obtain ⟨a, c, ha, legal, posJ, posI⟩ := overlap (tag j) (M j) (nonempty j)
      have hbJ := must j c legal posJ
      have hbI : B i (negative c) := must i c (by simpa only [hj] using legal)
        (by simpa only [hj, full] using posI)
      let r := rowAt (tag j) a
      have hAj : A j (positive r) := (Finset.mem_filter.mp ha).2
      have hAi : A i (positive r) := by
        have hr : r ∈ maskRows (tag i) (M i) := by
          rw [full]
          exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, by simp [r, hj]⟩
        rw [← rows_eq] at hr
        exact (Finset.mem_filter.mp hr).2
      obtain ⟨s, _, choose⟩ := covers r c
      exact (choose j ⟨hAj, hbJ⟩).trans (choose i ⟨hAi, hbI⟩).symm
    intro j hj j' hj'
    exact (only j (Finset.mem_filter.mp hj).2).trans (only j' (Finset.mem_filter.mp hj').2).symm
  intro p l flag
  obtain ⟨r, hp, hl⟩ := edges_exact.2 p l flag
  let c := criticalAt r
  obtain ⟨i, ⟨ha, hb⟩, _⟩ := covers r c
  have legal := supportsB i (negative c) hb
  have hr : r ∈ maskRows (tag i) (M i) := by
    rw [← rows_eq]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩
  have value := tight i c
  simp only [actual, allowance, hb, legal, ite_true] at value
  have nonnegative : (0 : ℤ) ≤ mass (tag i) (M i) c :=
    (le_max_left _ _).trans_eq value.symm
  have full : M i = Finset.univ := critical_pattern r (tag i) (M i) hr legal nonnegative
  have lim := singleton i full
  have sees := supportsA i (positive r) ha
  simp only [positive, hp, hl, decide_eq_true_eq] at sees
  rcases sees with hit | hit
  · exact Or.inl (by simpa only [hit] using lim)
  · exact Or.inr (by simpa only [hit] using lim)

lemma rectangleRigidity (k : ℕ) (A B : Fin k → (Fin 14 → Bool) → Prop)
    (tag : Fin k → Fin 14) (limit : k ≤ 28)
    (supportsA : ∀ i x, A i x → x (tag i) = true)
    (supportsB : ∀ i y, B i y → y (tag i) = false)
    (covers : ∀ a b : Fin 7, inc a b → ∀ Y : Finset (Fin 7),
      let X := zeroSet lines Y
      (∀ v ∉ Y, ∃ u ∈ X, inc u v) →
      ∃! i, A i (fun j => decide (j = Fin.castAdd 7 a ∨ j = Fin.natAdd 7 b)) ∧
        B i (Fin.append (fun u => decide (u ∈ X)) (fun v => decide (v ∈ Y)))) :
    ∀ p l : Fin 7, inc p l →
      Fintype.card {i : Fin k // tag i = Fin.castAdd 7 p} ≤ 1 ∨
      Fintype.card {i : Fin k // tag i = Fin.natAdd 7 l} ≤ 1 := by
  apply verifyPartition k A B tag limit supportsA supportsB
  intro r c
  exact covers (pointAt r) (lineAt r) (edges_exact.1 r) (columnAt c) (columns_maximal c)

lemma rectangleLowerBound (k : ℕ) (A B : Fin k → (Fin 14 → Bool) → Prop)
    (tag : Fin k → Fin 14)
    (supportsA : ∀ i x, A i x → x (tag i) = true)
    (supportsB : ∀ i y, B i y → y (tag i) = false)
    (covers : ∀ a b : Fin 7, inc a b → ∀ Y : Finset (Fin 7),
      let X := zeroSet lines Y
      (∀ v ∉ Y, ∃ u ∈ X, inc u v) →
      ∃! i, A i (fun j => decide (j = Fin.castAdd 7 a ∨ j = Fin.natAdd 7 b)) ∧
        B i (Fin.append (fun u => decide (u ∈ X)) (fun v => decide (v ∈ Y)))) : 28≤k := by
  apply verifyPartition_lower k A B tag supportsA supportsB
  intro r c
  exact covers (pointAt r) (lineAt r) (edges_exact.1 r) (columnAt c) (columns_maximal c)

end PEqualNP.Outside.L_meta_5884_aux.Table

namespace PEqualNP.Outside.L_meta_5884_aux.SeedUnfold

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

def df (gs : List Gate) (d : List ℕ) : List ℕ :=
  gs.foldl (fun d g => d ++ [g.lineDegree d]) d

def cf (n : ℕ) (gs : List Gate) : List (List ℕ) :=
  gs.foldl (coneStep n) []

lemma getD_snoc_lt {α : Type} (L : List α) (a d : α) (k : ℕ) (h : k < L.length) :
    (L ++ [a]).getD k d = L.getD k d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_snoc_eq {α : Type} (L : List α) (a d : α) :
    (L ++ [a]).getD L.length d = a := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_snoc_gt {α : Type} (L : List α) (a d : α) (k : ℕ) (h : L.length < k) :
    (L ++ [a]).getD k d = d := by
  rw [List.getD_eq_default]; simp; omega

lemma wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

lemma df_len (gs : List Gate) : ∀ d : List ℕ, (df gs d).length = d.length + gs.length := by
  induction gs with
  | nil => intro d; simp [df]
  | cons g gs ih =>
    intro d
    have := ih (d ++ [g.lineDegree d])
    simp only [df, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

lemma wf_getD_lt (gs : List Gate) : ∀ (w : List Bool) (k : ℕ), k < w.length →
    (wf gs w).getD k false = w.getD k false := by
  induction gs with
  | nil => intro w k _; simp [wf]
  | cons g gs ih =>
    intro w k hk
    have h1 := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) k (by simp; omega)
    simp only [wf, List.foldl_cons] at h1 ⊢
    rw [h1, getD_snoc_lt w _ false k hk]

lemma df_getD_lt (gs : List Gate) : ∀ (d : List ℕ) (k : ℕ), k < d.length →
    (df gs d).getD k 0 = d.getD k 0 := by
  induction gs with
  | nil => intro d k _; simp [df]
  | cons g gs ih =>
    intro d k hk
    have h1 := ih (d ++ [g.lineDegree d]) k (by simp; omega)
    simp only [df, List.foldl_cons] at h1 ⊢
    rw [h1, getD_snoc_lt d _ 0 k hk]

lemma wf_append (gs1 gs2 : List Gate) (w : List Bool) :
    wf (gs1 ++ gs2) w = wf gs2 (wf gs1 w) := by
  simp [wf, List.foldl_append]

lemma df_append (gs1 gs2 : List Gate) (d : List ℕ) :
    df (gs1 ++ gs2) d = df gs2 (df gs1 d) := by
  simp [df, List.foldl_append]

lemma mem_le_sum (l : List ℕ) (a : ℕ) (ha : a ∈ l) : a ≤ l.sum := by
  induction l with
  | nil => simp at ha
  | cons b t ih =>
    simp only [List.mem_cons] at ha
    simp only [List.sum_cons]
    rcases ha with rfl | ht
    · omega
    · have := ih ht; omega

lemma mem_le_foldr_max (l : List ℕ) (a : ℕ) (ha : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at ha
  | cons b t ih =>
    simp only [List.mem_cons] at ha
    simp only [List.foldr_cons]
    rcases ha with rfl | ht
    · exact le_max_left _ _
    · exact le_trans (ih ht) (le_max_right _ _)

lemma mem_le_lineDegree (g : Gate) (d : List ℕ) (w : ℕ) (hw : w ∈ g.inputs) :
    d.getD w 0 ≤ g.lineDegree d := by
  unfold Gate.lineDegree
  split_ifs
  · exact mem_le_sum _ _ (List.mem_map.mpr ⟨w, hw, rfl⟩)
  · exact mem_le_foldr_max _ _ (List.mem_map.mpr ⟨w, hw, rfl⟩)

lemma cones_mono (n : ℕ) (gs : List Gate) :
    (cf n gs).length = gs.length ∧
    ∀ (d0 : List ℕ), d0.length = n →
      ∀ j < gs.length, ∀ i ∈ (cf n gs).getD j [],
        i < j ∧ (df gs d0).getD (n + i) 0 ≤ (df gs d0).getD (n + j) 0 := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨by simp [cf], ?_⟩
    intro d0 _ j hj
    simp at hj
  | append_singleton gs g ih =>
    obtain ⟨hlen, hmono⟩ := ih
    have hcf : cf n (gs ++ [g]) = coneStep n (cf n gs) g := by
      simp [cf, List.foldl_append]
    have hlen' : (cf n (gs ++ [g])).length = (gs ++ [g]).length := by
      rw [hcf]; simp [coneStep, hlen]
    refine ⟨hlen', ?_⟩
    intro d0 hd0 j hj i hi
    have hdl : (df gs d0).length = n + gs.length := by rw [df_len, hd0]
    have hdf : df (gs ++ [g]) d0 = df gs d0 ++ [g.lineDegree (df gs d0)] := by
      simp [df, List.foldl_append]
    rw [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [hcf, coneStep, getD_snoc_lt _ _ _ j (by omega)] at hi
      obtain ⟨hij, hle⟩ := hmono d0 hd0 j hlt i hi
      refine ⟨hij, ?_⟩
      rw [hdf, getD_snoc_lt _ _ 0 (n + i) (by omega), getD_snoc_lt _ _ 0 (n + j) (by omega)]
      exact hle
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [hcf, coneStep, ← hlen, getD_snoc_eq] at hi
      simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq] at hi
      obtain ⟨w, ⟨hw_in, hnw, hwlt⟩, hwi⟩ := hi
      rw [hlen] at hwlt
      have hdeg_w : (df gs d0).getD w 0 ≤ g.lineDegree (df gs d0) :=
        mem_le_lineDegree g (df gs d0) w hw_in
      have htop : (df (gs ++ [g]) d0).getD (n + gs.length) 0 = g.lineDegree (df gs d0) := by
        rw [hdf, ← hdl, getD_snoc_eq]
      simp only [List.mem_cons] at hwi
      rcases hwi with rfl | hwi
      · refine ⟨by omega, ?_⟩
        rw [htop, hdf, getD_snoc_lt _ _ 0 (n + (w - n)) (by omega)]
        have hw_eq : n + (w - n) = w := by omega
        rw [hw_eq]
        exact hdeg_w
      · obtain ⟨hij, hle⟩ := hmono d0 hd0 (w - n) (by omega) i hwi
        refine ⟨by omega, ?_⟩
        rw [htop, hdf, getD_snoc_lt _ _ 0 (n + i) (by omega)]
        have hw_eq : n + (w - n) = w := by omega
        rw [hw_eq] at hle
        exact le_trans hle hdeg_w

lemma zero_deg_indep (n : ℕ) (S : Finset ℕ) (x y : List Bool) (hx : x.length = n) (hy : y.length = n)
    (hxy : ∀ i < n, i ∉ S → x.getD i false = y.getD i false) (gs : List Gate) :
    let d0 := (List.range n).map fun i => if i ∈ S then 1 else 0
    ∀ w, (df gs d0).getD w 0 = 0 → (wf gs x).getD w false = (wf gs y).getD w false := by
  intro d0
  have hd0 : d0.length = n := by simp [d0]
  induction gs using List.reverseRecOn with
  | nil =>
    intro w hw
    simp only [wf, df, List.foldl_nil] at hw ⊢
    by_cases hwn : w < n
    · have hdw : d0.getD w 0 = if w ∈ S then 1 else 0 := by
        rw [List.getD_eq_getElem _ _ (by omega)]
        simp [d0]
      rw [hdw] at hw
      have hwS : w ∉ S := by
        intro hmem
        simp [hmem] at hw
      exact hxy w hwn hwS
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  | append_singleton gs g ih =>
    intro w hw
    have hdl : (df gs d0).length = n + gs.length := by rw [df_len, hd0]
    have hxl : (wf gs x).length = n + gs.length := by rw [wf_len, hx]
    have hyl : (wf gs y).length = n + gs.length := by rw [wf_len, hy]
    have hdf : df (gs ++ [g]) d0 = df gs d0 ++ [g.lineDegree (df gs d0)] := by
      simp [df, List.foldl_append]
    have hwfx : wf (gs ++ [g]) x = wf gs x ++ [g.op.eval (g.inputs.map fun i => (wf gs x).getD i false)] := by
      simp [wf, List.foldl_append]
    have hwfy : wf (gs ++ [g]) y = wf gs y ++ [g.op.eval (g.inputs.map fun i => (wf gs y).getD i false)] := by
      simp [wf, List.foldl_append]
    rw [hdf] at hw
    rw [hwfx, hwfy]
    rcases Nat.lt_trichotomy w (n + gs.length) with hlt | heq | hgt
    · rw [getD_snoc_lt _ _ 0 w (by omega)] at hw
      rw [getD_snoc_lt _ _ false w (by omega), getD_snoc_lt _ _ false w (by omega)]
      exact ih w hw
    · subst heq
      rw [← hdl, getD_snoc_eq] at hw
      have hx_eq : (wf gs x ++ [g.op.eval (g.inputs.map fun i => (wf gs x).getD i false)]).getD (n + gs.length) false =
          g.op.eval (g.inputs.map fun i => (wf gs x).getD i false) := by
        rw [← hxl, getD_snoc_eq]
      have hy_eq : (wf gs y ++ [g.op.eval (g.inputs.map fun i => (wf gs y).getD i false)]).getD (n + gs.length) false =
          g.op.eval (g.inputs.map fun i => (wf gs y).getD i false) := by
        rw [← hyl, getD_snoc_eq]
      rw [hx_eq, hy_eq]
      congr 1
      apply List.map_congr_left
      intro u hu
      have hdu : (df gs d0).getD u 0 = 0 := by
        have hle := mem_le_lineDegree g (df gs d0) u hu
        omega
      exact ih u hdu
    · rw [getD_snoc_gt _ _ false w (by omega), getD_snoc_gt _ _ false w (by omega)]

lemma gate_and_eval (n : ℕ) (C : Circuit) (j a b : ℕ) (g : Gate)
    (hget : C.gates[j]? = some g) (hop : g.op = GateOp.and)
    (hin : g.inputs = [a, b]) (ha : a < n + j) (hb : b < n + j) (x : Fin n → Bool) :
    gateVal n C j x = (wireVal n C a x && wireVal n C b x) := by
  have hj : j < C.gates.length := (List.getElem?_eq_some_iff.mp hget).1
  have hsplit : C.gates = C.gates.take j ++ [g] ++ C.gates.drop (j + 1) := by
    have h2 : C.gates.drop j = g :: C.gates.drop (j + 1) := by
      rw [List.drop_eq_getElem_cons hj]
      have hg : C.gates[j] = g := (List.getElem?_eq_some_iff.mp hget).2
      rw [hg]
    conv_lhs => rw [← List.take_append_drop j C.gates]
    rw [h2]
    simp [List.append_assoc]
  have htake_len : (C.gates.take j).length = j := by simp [hj.le]
  let lx := List.ofFn x
  have hlx : lx.length = n := by simp [lx]
  let L1 := wf (C.gates.take j) lx
  have hL1_len : L1.length = n + j := by rw [wf_len, hlx, htake_len]
  have hcw : C.wires lx = wf (C.gates.drop (j + 1)) (L1 ++ [g.op.eval (g.inputs.map fun i => L1.getD i false)]) := by
    change wf C.gates lx = _
    conv_lhs => rw [hsplit]
    rw [wf_append, wf_append]
    simp [L1, wf]
  have hwire_lt : ∀ k < n + j, (C.wires lx).getD k false = L1.getD k false := by
    intro k hk
    rw [hcw, wf_getD_lt _ _ k (by simp [hL1_len]; omega), getD_snoc_lt _ _ false k (by omega)]
  have hgate : (C.wires lx).getD (n + j) false = g.op.eval (g.inputs.map fun i => L1.getD i false) := by
    rw [hcw, wf_getD_lt _ _ (n + j) (by simp [hL1_len]), ← hL1_len, getD_snoc_eq]
  change (C.wires lx).getD (n + j) false = ((C.wires lx).getD a false && (C.wires lx).getD b false)
  rw [hgate, hwire_lt a ha, hwire_lt b hb, hop, hin]
  simp [GateOp.eval]

lemma gate_and_deg (n : ℕ) (S : Finset ℕ) (C : Circuit) (j a b : ℕ) (g : Gate)
    (hget : C.gates[j]? = some g) (hop : g.op = GateOp.and)
    (hin : g.inputs = [a, b]) (ha : a < n + j) (hb : b < n + j) :
    (C.lineDegrees n S).getD (n + j) 0 =
      (C.lineDegrees n S).getD a 0 + (C.lineDegrees n S).getD b 0 := by
  have hj : j < C.gates.length := (List.getElem?_eq_some_iff.mp hget).1
  have hsplit : C.gates = C.gates.take j ++ [g] ++ C.gates.drop (j + 1) := by
    have h2 : C.gates.drop j = g :: C.gates.drop (j + 1) := by
      rw [List.drop_eq_getElem_cons hj]
      have hg : C.gates[j] = g := (List.getElem?_eq_some_iff.mp hget).2
      rw [hg]
    conv_lhs => rw [← List.take_append_drop j C.gates]
    rw [h2]
    simp [List.append_assoc]
  have htake_len : (C.gates.take j).length = j := by simp [hj.le]
  let d0 := (List.range n).map fun i => if i ∈ S then 1 else 0
  have hd0 : d0.length = n := by simp [d0]
  let D1 := df (C.gates.take j) d0
  have hD1_len : D1.length = n + j := by rw [df_len, hd0, htake_len]
  have hcd : C.lineDegrees n S = df (C.gates.drop (j + 1)) (D1 ++ [g.lineDegree D1]) := by
    change df C.gates d0 = _
    conv_lhs => rw [hsplit]
    rw [df_append, df_append]
    simp [D1, df]
  have hdeg_lt : ∀ k < n + j, (C.lineDegrees n S).getD k 0 = D1.getD k 0 := by
    intro k hk
    rw [hcd, df_getD_lt _ _ k (by simp [hD1_len]; omega), getD_snoc_lt _ _ 0 k (by omega)]
  have hdeg_j : (C.lineDegrees n S).getD (n + j) 0 = g.lineDegree D1 := by
    rw [hcd, df_getD_lt _ _ (n + j) (by simp [hD1_len]), ← hD1_len, getD_snoc_eq]
  rw [hdeg_j, hdeg_lt a ha, hdeg_lt b hb]
  simp [Gate.lineDegree, hop, hin]

lemma contra_one (C : Circuit)
    (hshape : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j)
    (hout_ge : 14 ≤ C.output) (hout_lt : C.output < 14 + C.gates.length)
    (m : ℕ) (p : Fin 14) (j : ℕ)
    (hdeg : HasLineDegree 14 {m} C 1)
    (hagree : ∀ i : Fin 14, i.val ≠ m → pairInput (0 : Fin 14) 7 i = pairInput p p i)
    (hj_and : (gateAt C j).op = GateOp.and)
    (hj_cone : 14 + j = C.output ∨ InCone 14 C j (C.output - 14))
    (hj_true : gateVal 14 C j (pairInput (0 : Fin 14) 7) = true)
    (hj_opnd : ∀ b : Fin 2, wireVal 14 C (opnd C j b) (pairInput p p) = false) :
    False := by
  have hmono := cones_mono 14 C.gates
  have hj_lt_and_le : j < C.gates.length ∧ (C.lineDegrees 14 {m}).getD (14 + j) 0 ≤ C.lineDeg 14 {m} := by
    rcases hj_cone with heq | hcone
    · refine ⟨by omega, ?_⟩
      rw [heq]
      exact le_refl _
    · have hout_sub : C.output - 14 < C.gates.length := by omega
      have h0 : ((List.range 14).map fun i => if i ∈ ({m} : Finset ℕ) then 1 else 0).length = 14 := by simp
      obtain ⟨hjl, hle⟩ := hmono.2 _ h0 (C.output - 14) hout_sub j hcone
      have h14 : 14 + (C.output - 14) = C.output := by omega
      refine ⟨by omega, ?_⟩
      change (df C.gates _).getD (14 + j) 0 ≤ (df C.gates _).getD C.output 0
      rw [← h14]
      exact hle
  obtain ⟨hj_lt, hdeg_j_le⟩ := hj_lt_and_le
  have hdeg_j : (C.lineDegrees 14 {m}).getD (14 + j) 0 ≤ 1 := le_trans hdeg_j_le hdeg
  let g := C.gates[j]
  have hget : C.gates[j]? = some g := List.getElem?_eq_getElem hj_lt
  have hgat : gateAt C j = g := by
    simp [gateAt, List.getD_eq_getElem?_getD, hget]
  have hop : g.op = GateOp.and := by rwa [← hgat]
  obtain ⟨_, a, b, hin, _, ha, hb⟩ := hshape j g hget
  have hop0 : opnd C j 0 = a := by simp [opnd, hgat, hin]
  have hop1 : opnd C j 1 = b := by simp [opnd, hgat, hin]
  have hev := gate_and_eval 14 C j a b g hget hop hin ha hb (pairInput (0 : Fin 14) 7)
  rw [hj_true] at hev
  obtain ⟨hwa, hwb⟩ := Bool.and_eq_true_iff.mp hev.symm
  have hdg := gate_and_deg 14 {m} C j a b g hget hop hin ha hb
  have hsum : (C.lineDegrees 14 {m}).getD a 0 + (C.lineDegrees 14 {m}).getD b 0 ≤ 1 := by omega
  have hind : ∀ w, (C.lineDegrees 14 {m}).getD w 0 = 0 →
      wireVal 14 C w (pairInput (0 : Fin 14) 7) = wireVal 14 C w (pairInput p p) := by
    intro w hw
    apply zero_deg_indep 14 {m} (List.ofFn (pairInput (0 : Fin 14) 7)) (List.ofFn (pairInput p p))
      (by simp) (by simp) _ C.gates w hw
    intro i hi hni
    have hne : i ≠ m := by simpa using hni
    rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getD_eq_getElem _ _ (by simp [hi])]
    simp only [List.getElem_ofFn]
    exact hagree ⟨i, hi⟩ hne
  have hzero : (C.lineDegrees 14 {m}).getD a 0 = 0 ∨ (C.lineDegrees 14 {m}).getD b 0 = 0 := by omega
  rcases hzero with hza | hzb
  · have h1 := hind a hza
    have h2 := hj_opnd 0
    rw [hop0] at h2
    rw [hwa, h2] at h1
    cases h1
  · have h1 := hind b hzb
    have h2 := hj_opnd 1
    rw [hop1] at h2
    rw [hwb, h2] at h1
    cases h1

noncomputable def degree14 (i : Fin 14) (F : DMFormula 14) : ℕ :=
  DMFormula.rec (motive := fun _ => ℕ) (fun j _ => if j = i then 1 else 0)
    (fun _ _ a b => a + b) (fun _ _ a b => max a b) F

noncomputable def pos15 (F : DMFormula 15) : Bool :=
  DMFormula.rec (motive := fun _ => Bool) (fun _ b => b)
    (fun _ _ a b => a && b) (fun _ _ a b => a && b) F

noncomputable def pos14 (F : DMFormula 14) : Bool :=
  DMFormula.rec (motive := fun _ => Bool) (fun _ b => b)
    (fun _ _ a b => a && b) (fun _ _ a b => a && b) F

def seedVal (u0 v0 : Fin 14) (isAnd : Bool) (x : Fin 14 → Bool) : Bool :=
  if isAnd = true then x u0 && x v0 else x u0 || x v0

def ext15 (u0 v0 : Fin 14) (isAnd : Bool) (x : Fin 14 → Bool) : Fin 15 → Bool :=
  Fin.snoc x (seedVal u0 v0 isAnd x)

def substZ (u0 v0 : Fin 14) (isAnd : Bool) : DMFormula 15 → DMFormula 14
  | .lit i b =>
      if h : i.val < 14 then .lit ⟨i.val, h⟩ b
      else if isAnd = true then .and (.lit u0 true) (.lit v0 true)
      else .or (.lit u0 true) (.lit v0 true)
  | .and a b => .and (substZ u0 v0 isAnd a) (substZ u0 v0 isAnd b)
  | .or a b => .or (substZ u0 v0 isAnd a) (substZ u0 v0 isAnd b)

lemma substZ_pos (u0 v0 : Fin 14) (isAnd : Bool) (F : DMFormula 15) (hp : pos15 F = true) :
    pos14 (substZ u0 v0 isAnd F) = true := by
  induction F with
  | lit i b =>
    change b = true at hp
    subst b
    unfold substZ
    split_ifs <;> rfl
  | and a b ihA ihB =>
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hp
    simpa [substZ, pos14] using Bool.and_eq_true_iff.mpr ⟨ihA ha, ihB hb⟩
  | or a b ihA ihB =>
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hp
    simpa [substZ, pos14] using Bool.and_eq_true_iff.mpr ⟨ihA ha, ihB hb⟩

lemma substZ_eval (u0 v0 : Fin 14) (isAnd : Bool) (F : DMFormula 15) (hp : pos15 F = true)
    (x : Fin 14 → Bool) :
    (substZ u0 v0 isAnd F).eval x = F.eval (ext15 u0 v0 isAnd x) := by
  induction F with
  | lit i b =>
    change b = true at hp
    subst b
    unfold substZ
    by_cases h : i.val < 14
    · rw [dif_pos h]
      simp only [DMFormula.eval]
      have he : ext15 u0 v0 isAnd x i = x ⟨i.val, h⟩ := by
        simp [ext15, Fin.snoc, h, Fin.castLT]
      exact he.symm
    · rw [dif_neg h]
      have hi : i = Fin.last 14 := by apply Fin.ext; have := i.isLt; simp; omega
      have he : ext15 u0 v0 isAnd x i = seedVal u0 v0 isAnd x := by
        rw [hi]; exact Fin.snoc_last _ _
      change (if isAnd = true then DMFormula.and (.lit u0 true) (.lit v0 true)
        else DMFormula.or (.lit u0 true) (.lit v0 true)).eval x = ext15 u0 v0 isAnd x i
      rw [he]
      cases isAnd <;> simp [DMFormula.eval, seedVal]
  | and a b ihA ihB =>
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hp
    simp [substZ, DMFormula.eval, ihA ha, ihB hb]
  | or a b ihA ihB =>
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hp
    simp [substZ, DMFormula.eval, ihA ha, ihB hb]

lemma substZ_leaves (u0 v0 : Fin 14) (isAnd : Bool) (F : DMFormula 15) :
    (substZ u0 v0 isAnd F).leaves = F.leaves + PEqualNP.Outside.L_meta_5884_aux.Protocol.countLab (14 : Fin 15) F := by
  induction F with
  | lit i b =>
    unfold substZ PEqualNP.Outside.L_meta_5884_aux.Protocol.countLab
    by_cases h : i.val < 14
    · rw [dif_pos h]
      have hne : i ≠ (14 : Fin 15) := by intro he; rw [he] at h; simp at h
      simp [hne, DMFormula.leaves]
    · rw [dif_neg h]
      have heq : i = (14 : Fin 15) := by apply Fin.ext; have := i.isLt; simp; omega
      subst heq
      cases isAnd <;> simp [DMFormula.leaves]
  | and a b ihA ihB =>
    simp only [substZ, DMFormula.leaves, PEqualNP.Outside.L_meta_5884_aux.Protocol.countLab]
    omega
  | or a b ihA ihB =>
    simp only [substZ, DMFormula.leaves, PEqualNP.Outside.L_meta_5884_aux.Protocol.countLab]
    omega

def shaped14 (gs : List Gate) : Prop :=
  ∀ j g, gs[j]? = some g →
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
    ∃ a b, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j

def leafAt15 (T : List (DMFormula 15)) (i : ℕ) : ℕ :=
  (T[i]?.map DMFormula.leaves).getD 0

def leafSum15 (T : List (DMFormula 15)) (R : List ℕ) : ℕ :=
  (R.map (leafAt15 T)).sum

def countNe (g0 m : ℕ) : ℕ :=
  if g0 < m then m - 1 else m

lemma leafSum15_append (T : List (DMFormula 15)) (R S : List ℕ) :
    leafSum15 T (R ++ S) = leafSum15 T R + leafSum15 T S := by
  simp [leafSum15]

lemma leafSum15_old (T : List (DMFormula 15)) (F : DMFormula 15)
    (R : List ℕ) (h : ∀ i ∈ R, i < T.length) :
    leafSum15 (T ++ [F]) R = leafSum15 T R := by
  unfold leafSum15
  congr 1
  apply List.map_congr_left
  intro i hi
  simp only [leafAt15, List.getElem?_append_left (h i hi)]

lemma leafAt15_last (T : List (DMFormula 15)) (F : DMFormula 15) :
    leafAt15 (T ++ [F]) T.length = F.leaves := by
  simp [leafAt15]

lemma getMap15 {α : Type} {T : List (DMFormula 15)} {i : ℕ} {F : DMFormula 15}
    (h : T[i]? = some F) (f : DMFormula 15 → α) (base : α) :
    (T.map f).getD i base = f F := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, h]

lemma filter_ne_count (x : ℕ) : ∀ R : List ℕ,
    R.length = (R.filter (fun r => r != x)).length + R.count x := by
  intro R
  induction R with
  | nil => simp
  | cons a t ih =>
    by_cases h : a = x
    · subst h; simp [List.count_cons]; omega
    · have hb : (a != x) = true := by simp [h]
      simp [hb, List.count_cons, beq_false_of_ne h]; omega

lemma leafSum15_snoc_unit (T : List (DMFormula 15)) (F : DMFormula 15) (hF : F.leaves = 1) :
    ∀ R : List ℕ, (∀ r ∈ R, r < (T ++ [F]).length) →
      leafSum15 (T ++ [F]) R = leafSum15 T (R.filter (fun r => r != T.length)) + R.count T.length := by
  intro R
  induction R with
  | nil => intro _; simp [leafSum15]
  | cons a t ih =>
    intro hvalid
    have ha := hvalid a (by simp)
    have ht := ih (fun r hr => hvalid r (by simp [hr]))
    by_cases he : a = T.length
    · subst he
      have h1 : leafAt15 (T ++ [F]) T.length = 1 := by rw [leafAt15_last, hF]
      simp only [leafSum15, List.map_cons, List.sum_cons, h1, List.filter_cons, bne_self_eq_false,
        Bool.false_eq_true, ite_false, List.count_cons_self] at ht ⊢
      omega
    · have hlt : a < T.length := by simp at ha; omega
      have h1 : leafAt15 (T ++ [F]) a = leafAt15 T a := by
        simp [leafAt15, List.getElem?_append_left hlt]
      have hb : (a != T.length) = true := by simp [he]
      simp only [leafSum15, List.map_cons, List.sum_cons, h1, List.filter_cons, hb, ite_true,
        List.count_cons, beq_false_of_ne he, Bool.false_eq_true, ite_false] at ht ⊢
      omega

lemma snocBudgetSeed (g0 : ℕ) (gs : List Gate) (g : Gate)
    (T : List (DMFormula 15)) (F : DMFormula 15) (a b : ℕ)
    (len : T.length = 14 + gs.length) (inputs : g.inputs = [a, b])
    (oldA : a < T.length) (oldB : b < T.length)
    (hstep : (gs.length = g0 ∧ F.leaves = 1) ∨ (gs.length ≠ g0 ∧ F.leaves = leafAt15 T a + leafAt15 T b))
    (earlier : ∀ R : List ℕ,
      ((R ++ gs.flatMap Gate.inputs).filter (fun i => decide (14 ≤ i) && (i != 14 + g0))).Nodup →
      (∀ r ∈ R, r < T.length) → leafSum15 T R ≤ R.length + countNe g0 gs.length) :
    ∀ R : List ℕ,
      ((R ++ (gs ++ [g]).flatMap Gate.inputs).filter (fun i => decide (14 ≤ i) && (i != 14 + g0))).Nodup →
      (∀ r ∈ R, r < (T ++ [F]).length) →
      leafSum15 (T ++ [F]) R ≤ R.length + countNe g0 (gs ++ [g]).length := by
  intro R unique valid
  let p := fun i : ℕ => decide (14 ≤ i) && (i != 14 + g0)
  let prev := (gs.flatMap Gate.inputs).filter p
  let pair := ([a, b] : List ℕ).filter p
  have packed : (R.filter p ++ (prev ++ pair)).Nodup := by
    simpa only [p, prev, pair, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, inputs, List.filter_append] using unique
  rcases hstep with ⟨hge, hF1⟩ | ⟨hgne, newLeaves⟩
  · let R' := R.filter (fun r => r != T.length)
    have hR'valid : ∀ r ∈ R', r < T.length := by
      intro r hr
      obtain ⟨hrR, hrne⟩ := List.mem_filter.mp hr
      have hb := valid r hrR
      have hne : r ≠ T.length := by simpa using hrne
      simp at hb
      omega
    have hR'filt : R'.filter p = R.filter p := by
      rw [List.filter_filter]
      apply List.filter_congr
      intro r _
      simp only [p, len, hge]
      cases h1 : decide (14 ≤ r) <;> cases h2 : (r != 14 + g0) <;> rfl
    have hR'nodup : ((R' ++ gs.flatMap Gate.inputs).filter p).Nodup := by
      have hinit : ((R.filter p ++ prev) ++ pair).Nodup := by
        simpa only [List.append_assoc] using packed
      have h1 := (List.nodup_append.mp hinit).1
      simpa only [List.filter_append, hR'filt, prev] using h1
    have hbound := earlier R' hR'nodup hR'valid
    have hls : leafSum15 (T ++ [F]) R = leafSum15 T R' + R.count T.length :=
      leafSum15_snoc_unit T F hF1 R valid
    have hlenR : R.length = R'.length + R.count T.length := filter_ne_count T.length R
    have hcne : countNe g0 (gs ++ [g]).length = countNe g0 gs.length := by
      simp [countNe, hge]
    rw [hls, hcne]
    omega
  · by_cases hR : T.length ∈ R
    · obtain ⟨L, S, rfl⟩ := List.append_of_mem hR
      have pop : p T.length = true := by
        simp [p, len, hgne]
      have packSplit : (L.filter p ++ T.length :: (S.filter p ++ (prev ++ pair))).Nodup := by
        simpa only [List.filter_append, List.filter_cons, pop, ite_true, List.append_assoc, List.cons_append] using packed
      have htail := (List.nodup_append.mp packSplit).2.1
      have noLeft : T.length ∉ L := by
        intro h
        have disjoint := (List.nodup_append.mp packSplit).2.2
        exact disjoint _ (List.mem_filter.mpr ⟨h, pop⟩) _ (by simp) rfl
      have noRight : T.length ∉ S := by
        intro h
        have miss := (List.nodup_cons.mp htail).1
        exact miss (List.mem_append_left _ (List.mem_filter.mpr ⟨h, pop⟩))
      have validL : ∀ i ∈ L, i < T.length := by
        intro i hi
        have inR : i ∈ L ++ T.length :: S := List.mem_append_left _ hi
        have bound := valid i inR
        have different : i ≠ T.length := fun he => noLeft (he ▸ hi)
        simp at bound
        omega
      have validS : ∀ i ∈ S, i < T.length := by
        intro i hi
        have inR : i ∈ L ++ T.length :: S := List.mem_append_right _ (List.mem_cons_of_mem _ hi)
        have bound := valid i inR
        have different : i ≠ T.length := fun he => noRight (he ▸ hi)
        simp at bound
        omega
      let R' := (L ++ S) ++ [a, b]
      have deleted : ((L.filter p ++ S.filter p) ++ (prev ++ pair)).Nodup := by
        rw [List.append_assoc]
        exact ((List.sublist_cons_self _ _).append_left _).nodup packSplit
      have swapped : ((L.filter p ++ S.filter p) ++ (pair ++ prev)).Nodup :=
        (List.Perm.append_left _ List.perm_append_comm).nodup_iff.mp deleted
      have earlierNodup : ((R' ++ gs.flatMap Gate.inputs).filter p).Nodup := by
        simpa only [R', prev, pair, List.filter_append, List.append_assoc] using swapped
      have earlierValid : ∀ i ∈ R', i < T.length := by
        intro i hi
        simp only [R', List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with (h | h) | rfl | rfl
        · exact validL i h
        · exact validS i h
        · exact oldA
        · exact oldB
      have earlierBound := earlier R' earlierNodup earlierValid
      have comparison : leafSum15 (T ++ [F]) (L ++ T.length :: S) = leafSum15 T R' := by
        rw [leafSum15_append, leafSum15_old _ _ _ validL]
        have one : (T.length :: S) = [T.length] ++ S := rfl
        rw [one, leafSum15_append, leafSum15_old _ _ _ validS]
        simp only [R', leafSum15_append]
        have hsingle : leafSum15 (T ++ [F]) [T.length] = F.leaves := by
          simpa [leafSum15] using leafAt15_last T F
        rw [hsingle, newLeaves]
        simp [leafSum15]
        omega
      have hcne : countNe g0 (gs ++ [g]).length = countNe g0 gs.length + 1 := by
        simp only [countNe, List.length_append, List.length_singleton]
        split_ifs <;> omega
      rw [comparison, hcne]
      simp only [R', List.length_append, List.length_cons, List.length_nil] at earlierBound ⊢
      omega
    · have validOld : ∀ i ∈ R, i < T.length := by
        intro i hi
        have bound := valid i hi
        have different : i ≠ T.length := fun he => hR (he ▸ hi)
        simp at bound
        omega
      have simpler : ((R ++ gs.flatMap Gate.inputs).filter p).Nodup := by
        have initialPart : ((R.filter p ++ prev) ++ pair).Nodup := by
          simpa only [List.append_assoc] using packed
        simpa only [prev, List.filter_append] using (List.nodup_append.mp initialPart).1
      rw [leafSum15_old _ _ _ validOld]
      have bound := earlier R simpler validOld
      have hcne : countNe g0 gs.length ≤ countNe g0 (gs ++ [g]).length := by
        simp only [countNe, List.length_append, List.length_singleton]
        split_ifs <;> omega
      omega

lemma expandWithSeed (g0 : ℕ) (u0 v0 : Fin 14) (isAnd : Bool) (gs : List Gate)
    (ok : shaped14 gs)
    (hg0 : ∀ g, gs[g0]? = some g → g.inputs = [u0.val, v0.val] ∧ (g.op = GateOp.and ↔ isAnd = true)) :
    ∃ T : List (DMFormula 15), T.length = 14 + gs.length ∧
      (∀ (i : ℕ) (F : DMFormula 15), T[i]? = some F → pos15 F = true) ∧
      (∀ x : Fin 14 → Bool, T.map (fun F => F.eval (ext15 u0 v0 isAnd x)) = (Circuit.mk gs 0).wires (List.ofFn x)) ∧
      (∀ i : Fin 14, T.map (fun F => degree14 i (substZ u0 v0 isAnd F)) = (Circuit.mk gs 0).lineDegrees 14 {i.val}) ∧
      ∀ R : List ℕ, ((R ++ gs.flatMap Gate.inputs).filter (fun i => decide (14 ≤ i) && (i != 14 + g0))).Nodup →
        (∀ r ∈ R, r < T.length) → leafSum15 T R ≤ R.length + countNe g0 gs.length := by
  induction gs using List.reverseRecOn with
  | nil =>
    let T := List.ofFn (fun i : Fin 14 => DMFormula.lit (Fin.castSucc i) true)
    have hTlen : T.length = 14 := List.length_ofFn
    refine ⟨T, hTlen, ?_, ?_, ?_, ?_⟩
    · intro i F hi
      obtain ⟨bound, rfl⟩ := List.getElem?_eq_some_iff.mp hi
      have payload : T[i] = DMFormula.lit (Fin.castSucc ⟨i, hTlen ▸ bound⟩) true :=
        List.getElem_ofFn _
      rw [payload]; rfl
    · intro x
      apply List.ext_getElem
      · simp [hTlen, Circuit.wires]
      · intro j hj hj'
        have j14 : j < 14 := by simp [hTlen] at hj; exact hj
        simp only [Circuit.wires, List.foldl_nil, List.getElem_map]
        rw [show T[j]'(hTlen.symm ▸ j14) = DMFormula.lit (Fin.castSucc ⟨j, j14⟩) true from List.getElem_ofFn _]
        rw [List.getElem_ofFn]
        simp [DMFormula.eval, ext15, Fin.snoc, j14, Fin.castLT]
    · intro i
      apply List.ext_getElem
      · simp [Circuit.lineDegrees, hTlen]
      · intro j hj hj'
        have j14 : j < 14 := by simp [hTlen] at hj; exact hj
        simp only [Circuit.lineDegrees, List.foldl_nil, List.getElem_map, List.getElem_range]
        rw [show T[j]'(hTlen.symm ▸ j14) = DMFormula.lit (Fin.castSucc ⟨j, j14⟩) true from List.getElem_ofFn _]
        have hlt : (Fin.castSucc (⟨j, j14⟩ : Fin 14)).val < 14 := j14
        unfold substZ
        rw [dif_pos hlt]
        simp [degree14, Fin.ext_iff]
    · intro R _ valid
      have single (r : ℕ) (hr : r ∈ R) : leafAt15 T r = 1 := by
        have br := valid r hr
        have eqn : T[r] = DMFormula.lit (Fin.castSucc ⟨r, hTlen ▸ br⟩) true := List.getElem_ofFn _
        simp [leafAt15, List.getElem?_eq_getElem br, eqn, DMFormula.leaves]
      have eqn : R.map (leafAt15 T) = R.map (fun _ => 1) := List.map_congr_left single
      simp [leafSum15, eqn, countNe]
  | append_singleton gs g ih =>
    have early : shaped14 gs := by
      intro j h atj
      have bound := (List.getElem?_eq_some_iff.mp atj).1
      apply ok j h
      rwa [List.getElem?_append_left bound]
    have early_g0 : ∀ h, gs[g0]? = some h → h.inputs = [u0.val, v0.val] ∧ (h.op = GateOp.and ↔ isAnd = true) := by
      intro h atg0
      have bound := (List.getElem?_eq_some_iff.mp atg0).1
      exact hg0 h (by rwa [List.getElem?_append_left bound])
    obtain ⟨T, len, pos, evals, degs, budget⟩ := ih early early_g0
    have gateAtLast : (gs ++ [g])[gs.length]? = some g := by simp
    obtain ⟨operator, a, b, inputs, _, ha, hb⟩ := ok gs.length g gateAtLast
    have ba : a < T.length := len.symm ▸ ha
    have bb : b < T.length := len.symm ▸ hb
    let A := T[a]
    let B := T[b]
    have aAt : T[a]? = some A := List.getElem?_eq_getElem ba
    have bAt : T[b]? = some B := List.getElem?_eq_getElem bb
    let F : DMFormula 15 :=
      if gs.length = g0 then DMFormula.lit (14 : Fin 15) true
      else match g.op with
        | GateOp.and => DMFormula.and A B
        | _ => DMFormula.or A B
    have posF : pos15 F = true := by
      by_cases hge : gs.length = g0
      · simp [F, hge, pos15]
      · simp only [F, hge, ite_false]
        rcases operator with op | op <;>
          simpa [op, pos15] using Bool.and_eq_true_iff.mpr ⟨pos a A aAt, pos b B bAt⟩
    have hstep : (gs.length = g0 ∧ F.leaves = 1) ∨ (gs.length ≠ g0 ∧ F.leaves = leafAt15 T a + leafAt15 T b) := by
      by_cases hge : gs.length = g0
      · left; exact ⟨hge, by simp [F, hge, DMFormula.leaves]⟩
      · right
        refine ⟨hge, ?_⟩
        simp only [F, hge, ite_false]
        rcases operator with op | op <;> simp [op, DMFormula.leaves, leafAt15, aAt, bAt]
    refine ⟨T ++ [F], by simp [len, Nat.add_assoc], ?_, ?_, ?_,
      snocBudgetSeed g0 gs g T F a b len inputs ba bb hstep budget⟩
    · intro j H h
      by_cases before : j < T.length
      · rw [List.getElem?_append_left before] at h
        exact pos j H h
      · have inside := (List.getElem?_eq_some_iff.mp h).1
        have equality : j = T.length := by simp at inside; omega
        subst j
        simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
          List.getElem?_cons_zero, Option.some.injEq] at h
        exact h ▸ posF
    · intro x
      simp only [List.map_append, List.map_cons, List.map_nil]
      have unfoldStep :
          (Circuit.mk (gs ++ [g]) 0).wires (List.ofFn x) =
            (Circuit.mk gs 0).wires (List.ofFn x) ++
              [g.op.eval (g.inputs.map fun j => ((Circuit.mk gs 0).wires (List.ofFn x)).getD j false)] := by
        simp [Circuit.wires, List.foldl_append]
      rw [unfoldStep, ← evals x]
      by_cases hge : gs.length = g0
      · have ⟨hg_in, hg_op⟩ := hg0 g (by rw [← hge]; exact gateAtLast)
        have hwa : ∀ u : Fin 14, ((Circuit.mk gs 0).wires (List.ofFn x)).getD u.val false = x u := by
          intro u
          change (wf gs (List.ofFn x)).getD u.val false = x u
          rw [wf_getD_lt gs (List.ofFn x) u.val (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
        rw [evals x, hg_in]
        simp only [List.map_cons, List.map_nil, hwa u0, hwa v0]
        have hF_eq : F = DMFormula.lit (14 : Fin 15) true := by simp [F, hge]
        rw [hF_eq]
        have h14 : (14 : Fin 15) = Fin.last 14 := rfl
        rw [h14]
        simp only [DMFormula.eval, ext15, Fin.snoc_last, seedVal]
        rcases operator with op | op
        · have his : isAnd = true := hg_op.mp op
          simp [op, his, GateOp.eval]
        · have his : isAnd = false := by
            cases hc : isAnd
            · rfl
            · have := hg_op.mpr hc; rw [op] at this; cases this
          simp [op, his, GateOp.eval]
      · rw [inputs]
        simp only [F, hge, ite_false, List.map_cons, List.map_nil, getMap15 aAt, getMap15 bAt]
        rcases operator with op | op <;> simp [op, DMFormula.eval, GateOp.eval]
    · intro i
      simp only [List.map_append, List.map_cons, List.map_nil]
      have unfoldStep :
          (Circuit.mk (gs ++ [g]) 0).lineDegrees 14 {i.val} =
            (Circuit.mk gs 0).lineDegrees 14 {i.val} ++
              [g.lineDegree ((Circuit.mk gs 0).lineDegrees 14 {i.val})] := by
        simp [Circuit.lineDegrees, List.foldl_append]
      rw [unfoldStep, ← degs i]
      by_cases hge : gs.length = g0
      · have ⟨hg_in, hg_op⟩ := hg0 g (by rw [← hge]; exact gateAtLast)
        have hda : ∀ u : Fin 14, ((Circuit.mk gs 0).lineDegrees 14 {i.val}).getD u.val 0 =
            if u = i then 1 else 0 := by
          intro u
          change (df gs ((List.range 14).map fun k => if k ∈ ({i.val} : Finset ℕ) then 1 else 0)).getD u.val 0 = _
          rw [df_getD_lt _ _ u.val (by simp), List.getD_eq_getElem _ _ (by simp)]
          simp [Fin.ext_iff]
        rw [degs i]
        have hF_eq : F = DMFormula.lit (14 : Fin 15) true := by simp [F, hge]
        rw [hF_eq]
        have hnotlt : ¬ (14 : Fin 15).val < 14 := by decide
        unfold substZ
        rw [dif_neg hnotlt]
        rcases operator with op | op
        · have his : isAnd = true := hg_op.mp op
          rw [Gate.lineDegree]
          simp only [op, ite_true, hg_in, List.map_cons, List.map_nil, hda u0, hda v0]
          simp [his, degree14]
        · have his : isAnd = false := by
            cases hc : isAnd
            · rfl
            · have := hg_op.mpr hc; rw [op] at this; cases this
          have horne : ¬ (GateOp.or = GateOp.and) := by intro h; cases h
          rw [Gate.lineDegree]
          simp only [op, horne, ite_false, hg_in, List.map_cons, List.map_nil, hda u0, hda v0]
          simp [his, degree14]
      · simp only [F, hge, ite_false]
        rcases operator with op | op <;>
          simp [substZ, op, degree14, Gate.lineDegree, inputs, List.getD_eq_getElem?_getD, aAt, bAt]

end PEqualNP.Outside.L_meta_5884_aux.SeedUnfold


namespace PEqualNP.Outside.L_meta_5884_aux.SymCert

def chartWords : List ℕ := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 288160007407550752, 270286071508633728, 229736628138025984, 183565875465490436, 218994303132270608, 155696362464477250]

def chartBit (v : Fin 14) (t : Fin 58) : Bool :=
  (chartWords.getD v.val 0).testBit t.val

def posChart (r : Fin 21) (v : Fin 14) : Bool :=
  chartBit v ⟨r.val, by omega⟩

def negChart (c : Fin 37) (v : Fin 14) : Bool :=
  chartBit v ⟨21 + c.val, by omega⟩

def dualMap (i : Fin 14) : Fin 14 :=
  if h : i.val < 7 then ⟨7 + (7 - i.val) % 7, by omega⟩
  else ⟨(7 - (i.val - 7)) % 7, by omega⟩

def shiftMap (t : Fin 7) (i : Fin 14) : Fin 14 :=
  if h : i.val < 7 then ⟨(i.val + t.val) % 7, by omega⟩
  else ⟨7 + (i.val - 7 + t.val) % 7, by omega⟩

def baseTable : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13],
   [0, 2, 1, 6, 4, 5, 3, 13, 8, 12, 10, 11, 9, 7],
   [0, 2, 4, 6, 1, 3, 5, 13, 8, 10, 12, 7, 9, 11],
   [0, 1, 5, 3, 6, 2, 4, 7, 12, 9, 10, 13, 8, 11],
   [0, 2, 3, 6, 5, 4, 1, 13, 9, 10, 12, 11, 8, 7],
   [0, 2, 5, 6, 3, 1, 4, 13, 9, 12, 10, 7, 8, 11],
   [0, 3, 2, 1, 5, 4, 6, 7, 9, 8, 12, 11, 10, 13]]

def baseMap (b : Fin 7) (i : Fin 14) : Fin 14 :=
  ⟨((baseTable.getD b.val []).getD i.val 0) % 14, Nat.mod_lt _ (by decide)⟩

def symMap (b t : Fin 7) (d : Bool) (i : Fin 14) : Fin 14 :=
  baseMap b (shiftMap t (if d = true then dualMap i else i))

def isInc14 (u v : Fin 14) : Bool :=
  (u.val < 7 && 7 ≤ v.val && ((u.val + 7 - (v.val - 7)) % 7 == 0 || (u.val + 7 - (v.val - 7)) % 7 == 1 || (u.val + 7 - (v.val - 7)) % 7 == 3)) ||
  (v.val < 7 && 7 ≤ u.val && ((v.val + 7 - (u.val - 7)) % 7 == 0 || (v.val + 7 - (u.val - 7)) % 7 == 1 || (v.val + 7 - (u.val - 7)) % 7 == 3))

set_option maxHeartbeats 0 in
lemma pair_sym : ∀ u v : Fin 14, u ≠ v →
    ∃ (b t : Fin 7) (d : Bool),
      (symMap b t d u = 0 ∧ (symMap b t d v = 1 ∨ symMap b t d v = 7 ∨ symMap b t d v = 12)) ∨
      (symMap b t d v = 0 ∧ (symMap b t d u = 1 ∨ symMap b t d u = 7 ∨ symMap b t d u = 12)) := by
  decide +kernel

lemma dual_pres : ∀ u v : Fin 14, isInc14 (dualMap u) (dualMap v) = isInc14 u v := by decide +kernel
lemma shift_pres : ∀ (t : Fin 7) (u v : Fin 14), isInc14 (shiftMap t u) (shiftMap t v) = isInc14 u v := by decide +kernel
lemma base_pres : ∀ (b : Fin 7) (u v : Fin 14), isInc14 (baseMap b u) (baseMap b v) = isInc14 u v := by decide +kernel
lemma dual_surj : ∀ y : Fin 14, ∃ x : Fin 14, dualMap x = y := by decide +kernel
lemma shift_surj : ∀ (t : Fin 7) (y : Fin 14), ∃ x : Fin 14, shiftMap t x = y := by decide +kernel
lemma base_surj : ∀ (b : Fin 7) (y : Fin 14), ∃ x : Fin 14, baseMap b x = y := by decide +kernel
lemma inc14_iff : ∀ u v : Fin 14, isInc14 u v = true ↔
    ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
      ((u = Fin.castAdd 7 p ∧ v = Fin.natAdd 7 l) ∨ (v = Fin.castAdd 7 p ∧ u = Fin.natAdd 7 l)) := by decide +kernel
lemma posChart_edge : ∀ r : Fin 21, ∃ u v : Fin 14, isInc14 u v = true ∧ posChart r u = true ∧ posChart r v = true := by decide +kernel
set_option maxHeartbeats 0 in
lemma negChart_no_edge : ∀ (c : Fin 37) (u v : Fin 14), isInc14 u v = true → ¬ (negChart c u = true ∧ negChart c v = true) := by decide +kernel

lemma sym_pres (b t : Fin 7) (d : Bool) (u v : Fin 14) :
    isInc14 (symMap b t d u) (symMap b t d v) = isInc14 u v := by
  unfold symMap
  rw [base_pres, shift_pres]
  cases d
  · rfl
  · exact dual_pres u v

lemma sym_surj (b t : Fin 7) (d : Bool) (y : Fin 14) : ∃ x : Fin 14, symMap b t d x = y := by
  obtain ⟨y1, hy1⟩ := base_surj b y
  obtain ⟨y2, hy2⟩ := shift_surj t y1
  cases d
  · exact ⟨y2, by simp [symMap, hy2, hy1]⟩
  · obtain ⟨x, hx⟩ := dual_surj y2
    exact ⟨x, by simp [symMap, hx, hy2, hy1]⟩

lemma sym_pos (b t : Fin 7) (d : Bool) (r : Fin 21) :
    ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
      posChart r (symMap b t d (Fin.castAdd 7 p)) = true ∧
      posChart r (symMap b t d (Fin.natAdd 7 l)) = true := by
  obtain ⟨u0, v0, hinc0, hu0, hv0⟩ := posChart_edge r
  obtain ⟨u, hu⟩ := sym_surj b t d u0
  obtain ⟨v, hv⟩ := sym_surj b t d v0
  have hinc : isInc14 u v = true := by
    rw [← sym_pres b t d u v, hu, hv]; exact hinc0
  obtain ⟨p, l, hpl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := (inc14_iff u v).mp hinc
  · exact ⟨p, l, hpl, hu ▸ hu0, hv ▸ hv0⟩
  · exact ⟨p, l, hpl, hv ▸ hv0, hu ▸ hu0⟩

lemma sym_neg (b t : Fin 7) (d : Bool) (c : Fin 37) (p l : Fin 7) (hpl : p = l ∨ p = l + 1 ∨ p = l + 3) :
    ¬ (negChart c (symMap b t d (Fin.castAdd 7 p)) = true ∧
       negChart c (symMap b t d (Fin.natAdd 7 l)) = true) := by
  have hinc : isInc14 (Fin.castAdd 7 p) (Fin.natAdd 7 l) = true :=
    (inc14_iff _ _).mpr ⟨p, l, hpl, Or.inl ⟨rfl, rfl⟩⟩
  have hinc' : isInc14 (symMap b t d (Fin.castAdd 7 p)) (symMap b t d (Fin.natAdd 7 l)) = true := by
    rw [sym_pres]; exact hinc
  exact negChart_no_edge c _ _ hinc'

def wData0 : ℕ := 0x4041414041404040404040414040403f40404041404041404040404040403f404040404040404041403f40404040404040404041414040404040404140404040404040414040403f4140403f41404140404040404041404040414040404040403f404040404041404040404041404040404040414040404040404040404141404040413f40404040404040404040403f404141404040404041414040404040404040413f4040403f414140404040404040404040404140404040404040414040404040404040403f4140404040413f40404040404040404040414041414040404040404141404040404140404041404040413f40404040404040403f404041404040404040404040423f404040403f4040404140404041414040404040404040404140404040404040404040403e41404040404040404041404040414140404040404040404140404041404040404041403f4041404040404040414040404040414040404040404040404040404140413f4040403f404141414040404041404140404040403f404040404040404040404140404040404040404140413f404041414040403f40404040404040404040404040404040404040404141404040414040404140404040413f4040404040403f41404040404040404041404041404040404040414040403f4040404040414040404040404141404040404040404040404041403f414040403f40404041404040403f414040404040404040404140404041404140404040404140404040414040404040414140404140403f404040414040404040404040404140403f4040404040403f40404040404140404040404141404040404041404040404040404040404140413f4040404140404040403f3f404041414041404040404040404040404040404040404040414140404040403f424040404040404140404040404041404040404040414041404040403f40404040414040404040404040404141404040404040404040414040403f403f40404040414140404040404041414040414040403f4140404040404040404040404040404140404040413f4040
def wData1 : ℕ := 0x404040404040295e404040524040403b4040405440405c5c405c40404040403d274040504040404e4e4040574040404073404045454040404040405c084040404040404043594040404040404064404057404040404040404045404040404040247840244040407040404040404040405e4e40424040402355404040405c404c40404022403f406940404040344040404054404040224e40405e40403440404040405c40344040405e40404040584040404c404040405e4040405e3240404040406940405340402440404040404c40415c4040404040404040404040404040464040405e405e404040521f4040404073404040404040402e314040404040614040404040404040405e40224040402e5240405c404042544040404040644040404040435940404043403a40404022405e40404040614040524c4640404040404040284f404046404040405e4040404040403e4040405f5f404054404057404040694040404017404040404c404040404a40404040404040405752404040526b40402940403e2c40404040694040404040404059404030404040404042404040406a4040154040574040422b40404040694040404040404041405550404040407340404040425f404040404040400d40404040404040524f4040404040734040404040404061404040403e21404040404040407340405e40414069404040404c404040402c40404040400040404040405f4040404040404061404040405440405c404040644040404054404040404081404040404040405361404040406140404040404040524040404040400d4040404040404032404040404040402d40405c404040404040406078404040404040404074404040404040401840404040404040406b404040404040544040404040404040404040403f4055404040644040404040404c404040644040404c3a40404040404040584040407040404040224040404040704040404040404040404040404076404040404840405c40404010404040405e4040404040684040404040404040404040404040405540404040404040404040404041402b4040
def wData2 : ℕ := 0x4040414140414041404040404140404040404041414040404041404040403e40404040404040404041403f4040404040403f4042404040404041404040404040404040424041403f414040404140404040404040404141404040404040403f404040403f4040404242403f4041404040404042404040404040424040404240404040404040404040413e404040404040404140404040403e4042404040404040404042403e404040404040404040424040404040404042404040404040414140404040404040403e404240404040404040404042404040404040404141404040404140424041404040403f40404040424140403f40403f4040404040404140404040404040403f40423f3f404040404140404040404041404040404140404040404241404040404040404040403e41414040404041404040424040404041404040404040404040404040424040404041404040414040403f404240404040404041404040403f3f424040404040404041404040403f404040414140404040424040404040403f40404040414140404040423f40404040404040414040404040424041403e40404040404040404040404140404040424041404040404040404140404041404040414140404040403e404040414040414041404040404140404040404040414040403f4040403f40404140404042404040404040414142404040404040403f404040403f40404041404040403f403f40404042404041404040404040404042404041404140404040404141404040424040404140404040423f404041404040403f404040403f40404040404040403f3f4040404240404041404240404040404040404040404140404040414040413f4040404040414040403e40404042404040404041404040404040404042404040414040404140404040424042404040404040424040404040404040404040404040404042404040403e404040404040404040404040404142414040404040404040404040414040403e4040414042404040404040404040404040404040404040404040404040404040404040404040404040404040
def wData3 : ℕ := 0x4041404040403f4040404041404040404040424041404042404040404041403f40403f404040414042404041404040424040404040404040404040413e40404040404040414040404040403f4141404041404040404040404040404040403f403f424040404042404040404041404040404042404040404042424040404040424040404040404040403e40404040404040404040404040404042404040404040424040403e40404040404040404042404040404040404042404040403e40404040404042403e4040404240404040404042404042404040404040404040404040404040424140404040413f4040404041404040404040403f3f404040414240404040404040404040423f404040403f41404040404042404040404040414040403f4041404041404040404040403e41404040404041404040424040404040404040404140404140404042404040404040404040404040423e404042404040404240403e4040404042404040404040404040404040404040404240404040404042404040403e404042404040404040404140404040414040404040404040404042404240403e4040404042404040404040404040404040404040404042404041414040404040424040403f4040403f4040404040404041414040403f4240404040404040414040404040403e40404041404040414041404240404040424040404040404040404040403f3f4040404040424040404040404041403f4140414040404040424041404040404040404040404040404042404240414140404041404040404040404140404040403e4040404040404040404040404040403e404240404042404040404040424040404040404042404040404040404040404040403e404240404240403e40404040404040404040404040404240404040424240404040424040404040404040404042404040404040404040404042404040403e403e40424140414040404040404040404040404040404140404140404040403e40404040424040403e40404040404040404040404042404042404040404040404040404042404040404040423e
def wData4 : ℕ := 0x4041414041404040404040414040403f40404041404041404040404040403f404040404040404041403f40404040404040404041414040404040404140404040404040414040403f4140403f41404140404040404041404040414040404040403f404040404041404040404041404040404040414040404040404040404141404040413f40404040404040404040403f404141404040404041414040404040404040413f4040403f414140404040404040404040404140404040404040414040404040404040403f4140404040413f40404040404040404040414041414040404040404141404040404140404041404040413f40404040404040403f404041404040404040404040423f404040403f4040404140404041414040404040404040404140404040404040404040403e41404040404040404041404040414140404040404040404140404041404040404041403f4041404040404040414040404040414040404040404040404040404140413f4040403f404141414040404041404140404040403f404040404040404040404140404040404040404140413f404041414040403f40404040404040404040404040404040404040404141404040414040404140404040413f4040404040403f41404040404040404041404041404040404040414040403f4040404040414040404040404141404040404040404040404041403f414040403f40404041404040403f414040404040404040404140404041404140404040404140404040414040404040414140404140403f404040414040404040404040404140403f4040404040403f40404040404140404040404141404040404041404040404040404040404140413f4040404140404040403f3f404041414041404040404040404040404040404040404040414140404040403f424040404040404140404040404041404040404040414041404040403f40404040414040404040404040404141404040404040404040414040403f403f40404040414140404040404041414040414040403f4140404040404040404040404040404140404040413f4040
def wData5 : ℕ := 0x4040404042444040404040404040404040404c4040404a4040484040404c364040403e4040404440443e3c4040404042483e4041404040404840404a404038404040414a4040403c4040403c404c42404040404042404240414040404240404036404040404244414a4040404640404040404040404040404c4040404442404a4040484040404c4040344040404040404040404040404040444c40404040444042404240324040404240404040404c404242404040404240404040404040444040404042483e3c3e404e4040384040404040484a403e3e4040404042404040404040404c40404040404c404040404040404040344040404040404040404a404c40424040404040404c4040404040344040404040404c40404c40404040404040344a4040404240404040404040344040404040404040404c4a404040404c404040404040404c404040404240404040404040404040404c4040424a404040404c404040403440404c4034404040404040404040404040404040404040404c424a4040404034404040404c4040404040404a40404042404040404040404048404a4040403e36404040404c4040404040404040404c41444040404140404040404c40404040404c40404040344040404040404c4040404040404040404a40344042404040404c404040404034404040404c40404040404040404040404c404c40404040404040404040403440404040404c404040404040404040404c404a404040404042404040404c40404040404044424040404a40404840404c4040404040404c404040404040404040364040403e404040403c3e4040404a403c38404441404440404840404040404840403e41404a4040424040404040404440404036404440464a41403c40404040404040404240404241404a4040424240404040403c4a484040403e40424040344e4040404c404040404040404240404040403e40404044404a4240484040403e4042403f484040404034404a40404040403c3f4440404040404040404040424038404a4040403c4a3f4c444040404840404040404040423f3c4040403e4040

def wDataOf (cid : Fin 6) : ℕ :=
  match cid.val with
  | 0 => wData0
  | 1 => wData1
  | 2 => wData2
  | 3 => wData3
  | 4 => wData4
  | _ => wData5

def wVal (cid : Fin 6) (r : Fin 21) (c : Fin 37) : ℤ :=
  Int.ofNat ((wDataOf cid >>> (8 * (37 * r.val + c.val))) % 256) - 64

def certIsAnd (cid : Fin 6) : Bool :=
  cid.val % 2 == 0

def certOther (cid : Fin 6) : Fin 14 :=
  if cid.val < 2 then 1 else if cid.val < 4 then 7 else 12

def certRawCap (cid : Fin 6) : ℤ :=
  match cid.val with
  | 0 => 3
  | 1 => 84
  | 2 => 4
  | 3 => 4
  | 4 => 3
  | _ => 24

def certSeedCap (cid : Fin 6) : ℤ :=
  if cid.val = 5 then 4 else 0

def certTot (cid : Fin 6) : ℤ :=
  match cid.val with
  | 0 => 84
  | 1 => 2184
  | 2 => 108
  | 3 => 110
  | 4 => 84
  | _ => 654

def rawRowList : List (List ℕ) := [[0, 1, 2], [3, 4, 5], [6, 7, 8], [9, 10, 11], [12, 13, 14], [15, 16, 17], [18, 19, 20], [0, 3, 9], [5, 8, 14], [7, 11, 17], [10, 13, 20], [2, 12, 16], [4, 15, 19], [1, 6, 18]]
def seedRowList : List (List ℕ) := [[], [0, 1, 2, 3, 4, 5], [0], [0, 1, 2, 3, 9], [], [0, 1, 2, 4, 15, 19]]

def rawRowAt (v : Fin 14) (a : Fin 3) : Fin 21 :=
  ⟨((rawRowList.getD v.val []).getD a.val 0) % 21, Nat.mod_lt _ (by decide)⟩

def seedBit (cid : Fin 6) (x : Fin 14 → Bool) : Bool :=
  if certIsAnd cid = true then x 0 && x (certOther cid) else x 0 || x (certOther cid)

def rawMaskRows (v : Fin 14) (M : Finset (Fin 3)) : Finset (Fin 21) :=
  M.image (rawRowAt v)

def seedMaskRows (cid : Fin 6) (M : Finset (Fin 6)) : Finset (Fin 21) :=
  (Finset.univ.filter fun a : Fin 6 => a ∈ M ∧ a.val < (seedRowList.getD cid.val []).length).image
    (fun a => ⟨((seedRowList.getD cid.val []).getD a.val 0) % 21, Nat.mod_lt _ (by decide)⟩)

set_option maxHeartbeats 0 in
lemma raw_rows_exact : ∀ (v : Fin 14) (r : Fin 21),
    posChart r v = true ↔ ∃ a : Fin 3, rawRowAt v a = r := by
  decide +kernel

set_option maxHeartbeats 0 in
lemma seed_rows_exact : ∀ (cid : Fin 6) (r : Fin 21),
    seedBit cid (posChart r) = true ↔
      ∃ a : Fin 6, a.val < (seedRowList.getD cid.val []).length ∧
        (⟨((seedRowList.getD cid.val []).getD a.val 0) % 21, Nat.mod_lt _ (by decide)⟩ : Fin 21) = r := by
  decide +kernel

set_option maxHeartbeats 0 in
lemma tot_0 : (∑ r : Fin 21, ∑ c : Fin 37, wVal 0 r c) = certTot 0 := by decide +kernel

set_option maxHeartbeats 0 in
lemma tot_1 : (∑ r : Fin 21, ∑ c : Fin 37, wVal 1 r c) = certTot 1 := by decide +kernel

set_option maxHeartbeats 0 in
lemma tot_2 : (∑ r : Fin 21, ∑ c : Fin 37, wVal 2 r c) = certTot 2 := by decide +kernel

set_option maxHeartbeats 0 in
lemma tot_3 : (∑ r : Fin 21, ∑ c : Fin 37, wVal 3 r c) = certTot 3 := by decide +kernel

set_option maxHeartbeats 0 in
lemma tot_4 : (∑ r : Fin 21, ∑ c : Fin 37, wVal 4 r c) = certTot 4 := by decide +kernel

set_option maxHeartbeats 0 in
lemma tot_5 : (∑ r : Fin 21, ∑ c : Fin 37, wVal 5 r c) = certTot 5 := by decide +kernel

lemma tot_all (cid : Fin 6) : (∑ r : Fin 21, ∑ c : Fin 37, wVal cid r c) = certTot cid := by
  fin_cases cid
  · exact tot_0
  · exact tot_1
  · exact tot_2
  · exact tot_3
  · exact tot_4
  · exact tot_5

set_option maxHeartbeats 0 in
lemma raw_bound_0 : ∀ (v : Fin 14) (M : Finset (Fin 3)),
    (∑ c : Fin 37, if negChart c v = false then max 0 (∑ r ∈ rawMaskRows v M, wVal 0 r c) else 0) ≤ certRawCap 0 := by decide +kernel

set_option maxHeartbeats 0 in
lemma raw_bound_1 : ∀ (v : Fin 14) (M : Finset (Fin 3)),
    (∑ c : Fin 37, if negChart c v = false then max 0 (∑ r ∈ rawMaskRows v M, wVal 1 r c) else 0) ≤ certRawCap 1 := by decide +kernel

set_option maxHeartbeats 0 in
lemma raw_bound_2 : ∀ (v : Fin 14) (M : Finset (Fin 3)),
    (∑ c : Fin 37, if negChart c v = false then max 0 (∑ r ∈ rawMaskRows v M, wVal 2 r c) else 0) ≤ certRawCap 2 := by decide +kernel

set_option maxHeartbeats 0 in
lemma raw_bound_3 : ∀ (v : Fin 14) (M : Finset (Fin 3)),
    (∑ c : Fin 37, if negChart c v = false then max 0 (∑ r ∈ rawMaskRows v M, wVal 3 r c) else 0) ≤ certRawCap 3 := by decide +kernel

set_option maxHeartbeats 0 in
lemma raw_bound_4 : ∀ (v : Fin 14) (M : Finset (Fin 3)),
    (∑ c : Fin 37, if negChart c v = false then max 0 (∑ r ∈ rawMaskRows v M, wVal 4 r c) else 0) ≤ certRawCap 4 := by decide +kernel

set_option maxHeartbeats 0 in
lemma raw_bound_5 : ∀ (v : Fin 14) (M : Finset (Fin 3)),
    (∑ c : Fin 37, if negChart c v = false then max 0 (∑ r ∈ rawMaskRows v M, wVal 5 r c) else 0) ≤ certRawCap 5 := by decide +kernel

lemma raw_bound_all (cid : Fin 6) (v : Fin 14) (M : Finset (Fin 3)) :
    (∑ c : Fin 37, if negChart c v = false then max 0 (∑ r ∈ rawMaskRows v M, wVal cid r c) else 0) ≤ certRawCap cid := by
  fin_cases cid
  · exact raw_bound_0 v M
  · exact raw_bound_1 v M
  · exact raw_bound_2 v M
  · exact raw_bound_3 v M
  · exact raw_bound_4 v M
  · exact raw_bound_5 v M

set_option maxHeartbeats 0 in
lemma seed_bound_0 : ∀ (M : Finset (Fin 6)),
    (∑ c : Fin 37, if seedBit 0 (negChart c) = false then max 0 (∑ r ∈ seedMaskRows 0 M, wVal 0 r c) else 0) ≤ certSeedCap 0 := by decide +kernel

set_option maxHeartbeats 0 in
lemma seed_bound_1 : ∀ (M : Finset (Fin 6)),
    (∑ c : Fin 37, if seedBit 1 (negChart c) = false then max 0 (∑ r ∈ seedMaskRows 1 M, wVal 1 r c) else 0) ≤ certSeedCap 1 := by decide +kernel

set_option maxHeartbeats 0 in
lemma seed_bound_2 : ∀ (M : Finset (Fin 6)),
    (∑ c : Fin 37, if seedBit 2 (negChart c) = false then max 0 (∑ r ∈ seedMaskRows 2 M, wVal 2 r c) else 0) ≤ certSeedCap 2 := by decide +kernel

set_option maxHeartbeats 0 in
lemma seed_bound_3 : ∀ (M : Finset (Fin 6)),
    (∑ c : Fin 37, if seedBit 3 (negChart c) = false then max 0 (∑ r ∈ seedMaskRows 3 M, wVal 3 r c) else 0) ≤ certSeedCap 3 := by decide +kernel

set_option maxHeartbeats 0 in
lemma seed_bound_4 : ∀ (M : Finset (Fin 6)),
    (∑ c : Fin 37, if seedBit 4 (negChart c) = false then max 0 (∑ r ∈ seedMaskRows 4 M, wVal 4 r c) else 0) ≤ certSeedCap 4 := by decide +kernel

set_option maxHeartbeats 0 in
lemma seed_bound_5 : ∀ (M : Finset (Fin 6)),
    (∑ c : Fin 37, if seedBit 5 (negChart c) = false then max 0 (∑ r ∈ seedMaskRows 5 M, wVal 5 r c) else 0) ≤ certSeedCap 5 := by decide +kernel

lemma seed_bound_all (cid : Fin 6) (M : Finset (Fin 6)) :
    (∑ c : Fin 37, if seedBit cid (negChart c) = false then max 0 (∑ r ∈ seedMaskRows cid M, wVal cid r c) else 0) ≤ certSeedCap cid := by
  fin_cases cid
  · exact seed_bound_0 M
  · exact seed_bound_1 M
  · exact seed_bound_2 M
  · exact seed_bound_3 M
  · exact seed_bound_4 M
  · exact seed_bound_5 M

lemma cert_gap (cid : Fin 6) :
    25 * certRawCap cid + 2 * certSeedCap cid < certTot cid ∧
    certSeedCap cid ≤ certRawCap cid ∧ 0 ≤ certRawCap cid := by
  fin_cases cid <;> decide

lemma exclude_compressed (cid : Fin 6) (k : ℕ) (hk : k ≤ 27)
    (A : Fin k → Fin 21 → Prop) (B : Fin k → Fin 37 → Prop)
    (isSeed : Fin k → Bool) (rawTag : Fin k → Fin 14)
    (hTwo : 2 ≤ Fintype.card {i : Fin k // isSeed i = true})
    (hRawA : ∀ i r, isSeed i = false → A i r → posChart r (rawTag i) = true)
    (hRawB : ∀ i c, isSeed i = false → B i c → negChart c (rawTag i) = false)
    (hSeedA : ∀ i r, isSeed i = true → A i r → seedBit cid (posChart r) = true)
    (hSeedB : ∀ i c, isSeed i = true → B i c → seedBit cid (negChart c) = false)
    (hCov : ∀ r c, ∃! i : Fin k, A i r ∧ B i c) : False := by
  classical
  let rows (i : Fin k) : Finset (Fin 21) := Finset.univ.filter (fun r => A i r)
  let actual (i : Fin k) (c : Fin 37) : ℤ :=
    if B i c then ∑ r ∈ rows i, wVal cid r c else 0
  let total (i : Fin k) : ℤ := ∑ c : Fin 37, actual i c
  have hEachRaw (i : Fin k) (hf : isSeed i = false) : total i ≤ certRawCap cid := by
    let M : Finset (Fin 3) := Finset.univ.filter (fun a => A i (rawRowAt (rawTag i) a))
    have hreq : rows i = rawMaskRows (rawTag i) M := by
      ext r
      simp only [rows, M, rawMaskRows, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hr
        obtain ⟨a, ha⟩ := (raw_rows_exact (rawTag i) r).mp (hRawA i r hf hr)
        exact ⟨a, ha.symm ▸ hr, ha⟩
      · rintro ⟨a, ha, rfl⟩
        exact ha
    have hpt (c : Fin 37) :
        actual i c ≤ (if negChart c (rawTag i) = false then max 0 (∑ r ∈ rawMaskRows (rawTag i) M, wVal cid r c) else 0) := by
      by_cases hb : B i c
      · simp only [actual, hb, hreq, hRawB i c hf hb, ite_true]
        exact le_max_right _ _
      · simp only [actual, hb, ite_false]
        split_ifs
        · exact le_max_left _ _
        · exact le_refl _
    exact (Finset.sum_le_sum fun c _ => hpt c).trans (raw_bound_all cid (rawTag i) M)
  have hEachSeed (i : Fin k) (ht : isSeed i = true) : total i ≤ certSeedCap cid := by
    let M : Finset (Fin 6) := Finset.univ.filter (fun a =>
      a.val < (seedRowList.getD cid.val []).length ∧
      A i ⟨((seedRowList.getD cid.val []).getD a.val 0) % 21, Nat.mod_lt _ (by decide)⟩)
    have hreq : rows i = seedMaskRows cid M := by
      ext r
      simp only [rows, M, seedMaskRows, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hr
        obtain ⟨a, halt, haeq⟩ := (seed_rows_exact cid r).mp (hSeedA i r ht hr)
        exact ⟨a, ⟨⟨halt, haeq.symm ▸ hr⟩, halt⟩, haeq⟩
      · rintro ⟨a, ⟨⟨_, hr⟩, _⟩, rfl⟩
        exact hr
    have hpt (c : Fin 37) :
        actual i c ≤ (if seedBit cid (negChart c) = false then max 0 (∑ r ∈ seedMaskRows cid M, wVal cid r c) else 0) := by
      by_cases hb : B i c
      · simp only [actual, hb, hreq, hSeedB i c ht hb, ite_true]
        exact le_max_right _ _
      · simp only [actual, hb, ite_false]
        split_ifs
        · exact le_max_left _ _
        · exact le_refl _
    exact (Finset.sum_le_sum fun c _ => hpt c).trans (seed_bound_all cid M)
  have hSumEq : (∑ i : Fin k, total i) = ∑ r : Fin 21, ∑ c : Fin 37, wVal cid r c := by
    have hExpand (i : Fin k) (c : Fin 37) :
        actual i c = ∑ r : Fin 21, if A i r ∧ B i c then wVal cid r c else 0 := by
      by_cases hb : B i c
      · simp [actual, rows, hb, Finset.sum_filter]
      · simp [actual, hb]
    calc ∑ i : Fin k, total i
        = ∑ i : Fin k, ∑ c : Fin 37, ∑ r : Fin 21, if A i r ∧ B i c then wVal cid r c else 0 := by
            simp only [total, hExpand]
      _ = ∑ c : Fin 37, ∑ i : Fin k, ∑ r : Fin 21, if A i r ∧ B i c then wVal cid r c else 0 :=
            Finset.sum_comm
      _ = ∑ c : Fin 37, ∑ r : Fin 21, ∑ i : Fin k, if A i r ∧ B i c then wVal cid r c else 0 := by
            refine Finset.sum_congr rfl fun c _ => Finset.sum_comm
      _ = ∑ c : Fin 37, ∑ r : Fin 21, wVal cid r c := by
            refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun r _ => ?_
            obtain ⟨i0, hi0, huniq⟩ := hCov r c
            rw [Finset.sum_eq_single i0]
            · simp [hi0]
            · intro i _ hne
              have hnot : ¬ (A i r ∧ B i c) := fun h => hne (huniq i h)
              simp [hnot]
            · intro hmem; exact (hmem (Finset.mem_univ i0)).elim
      _ = ∑ r : Fin 21, ∑ c : Fin 37, wVal cid r c := Finset.sum_comm
  have hBound : (∑ i : Fin k, total i) ≤
      ∑ i : Fin k, if isSeed i = true then certSeedCap cid else certRawCap cid := by
    apply Finset.sum_le_sum
    intro i _
    cases h : isSeed i
    · simp only [Bool.false_eq_true, ite_false]; exact hEachRaw i h
    · simp only [ite_true]; exact hEachSeed i h
  let sCount : ℕ := (Finset.univ.filter fun i : Fin k => isSeed i = true).card
  have hsEq : sCount = Fintype.card {i : Fin k // isSeed i = true} := by
    simp [sCount, Fintype.card_subtype]
  have hsGe2 : 2 ≤ sCount := hsEq.symm ▸ hTwo
  have hsLeK : sCount ≤ k := by
    calc sCount ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = k := by simp
  have hEvalSum : (∑ i : Fin k, if isSeed i = true then certSeedCap cid else certRawCap cid) =
      (sCount : ℤ) * certSeedCap cid + ((k - sCount : ℕ) : ℤ) * certRawCap cid := by
    rw [Finset.sum_ite]
    have hcomp : (Finset.univ.filter fun i : Fin k => ¬ isSeed i = true).card = k - sCount := by
      have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin k)))
        (p := fun i => isSeed i = true)
      simp only [Finset.card_univ, Fintype.card_fin] at h1
      change sCount + _ = k at h1
      omega
    simp only [Finset.sum_const, nsmul_eq_mul, hcomp]
    rfl
  rw [hSumEq, tot_all cid] at hBound
  rw [hEvalSum] at hBound
  obtain ⟨hgap, hle, hnn⟩ := cert_gap cid
  have hk_z : (k : ℤ) ≤ 27 := by exact_mod_cast hk
  have hs_z : (2 : ℤ) ≤ (sCount : ℤ) := by exact_mod_cast hsGe2
  have hslk_z : (sCount : ℤ) ≤ (k : ℤ) := by exact_mod_cast hsLeK
  have hdiff : ((k - sCount : ℕ) : ℤ) = (k : ℤ) - (sCount : ℤ) := by omega
  rw [hdiff] at hBound
  have h1 : (sCount : ℤ) * certSeedCap cid + ((k : ℤ) - (sCount : ℤ)) * certRawCap cid ≤
      25 * certRawCap cid + 2 * certSeedCap cid := by
    have ha : ((sCount : ℤ) - 2) * (certRawCap cid - certSeedCap cid) ≥ 0 :=
      mul_nonneg (by omega) (by omega)
    have hb : (27 - (k : ℤ)) * certRawCap cid ≥ 0 :=
      mul_nonneg (by omega) hnn
    nlinarith
  omega

end PEqualNP.Outside.L_meta_5884_aux.SymCert

namespace PEqualNP.Outside.L_meta_5884_aux

set_option maxHeartbeats 1000000 in
theorem core : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   have x2 : List ℕ := List.filter (fun (x2 : ℕ) => Decidable.decide ((14 : ℕ) ≤ x2)) (x1.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x1.gates);   have x3 : ℕ → Prop := fun (x3 : ℕ) => x3 < x1.gates.length ∧ (∀ x4 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x3).inputs, x4 < (14 : ℕ)) ∧ (List.filter (fun (x4 : ℕ) => x4 != (14 : ℕ) + x3) x2).Nodup;   have x4 : ℕ → Fin (14 : ℕ) → Prop := fun (x4 : ℕ) (x5 : Fin (14 : ℕ)) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((14 : ℕ) + x4 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x4 (x1.output - (14 : ℕ))) ∧ PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x1 x4 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.true ∧ ∀ (x6 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x4 x6) (PEqualNP.EdgeOwnership.pairInput x5 x5) = Bool.false;   x1.size ≤ (27 : ℕ) → (∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x6]? = Option.some x7 → (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x7.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x9 : ℕ) (x10 : ℕ), x7.inputs = [x9, x10] ∧ x9 ≠ x10 ∧ x9 < (14 : ℕ) + x6 ∧ x10 < (14 : ℕ) + x6) → (∀ (x7 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x7) = Bool.true ↔ ∃ (x8 : Fin (7 : ℕ)) (x9 : Fin (7 : ℕ)), (x8 = x9 ∨ x8 = x9 + (1 : Fin (7 : ℕ)) ∨ x8 = x9 + (3 : Fin (7 : ℕ))) ∧ x7 (Fin.castAdd (7 : ℕ) x8) = Bool.true ∧ x7 (Fin.natAdd (7 : ℕ) x9) = Bool.true) → (∃ (x9 : ℕ), x3 x9) → ∀ (x10 x11 : ℕ), x10 ≠ x11 → ¬PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x10 x11 → ¬PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x11 x10 → x4 x10 (0 : Fin (14 : ℕ)) → x4 x11 (7 : Fin (14 : ℕ)) → False) := by
  intro x1 x2 x3 x4 hsize hshape hcorr hprim x10 x11 _ _ _ hx10 hx11
  obtain ⟨g0, hg0_lt, hg0_in, hg0_nodup⟩ := hprim
  let g0_gate := x1.gates[g0]
  have hg0_get : x1.gates[g0]? = some g0_gate := List.getElem?_eq_getElem hg0_lt
  have hg0_at : PEqualNP.MetaComplexity.NestedCover.gateAt x1 g0 = g0_gate := by
    simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hg0_get]
  obtain ⟨hg0_op, a0, b0, hg0_ab, hab_ne, _, _⟩ := hshape g0 g0_gate hg0_get
  have ha0_lt : a0 < 14 := hg0_in a0 (by rw [hg0_at, hg0_ab]; simp)
  have hb0_lt : b0 < 14 := hg0_in b0 (by rw [hg0_at, hg0_ab]; simp)
  let u0 : Fin 14 := ⟨a0, ha0_lt⟩
  let v0 : Fin 14 := ⟨b0, hb0_lt⟩
  have huv_ne : u0 ≠ v0 := fun h => hab_ne (congrArg Fin.val h)
  let isAnd : Bool := match g0_gate.op with | PEqualNP.CircuitLowerBounds.GateOp.and => true | _ => false
  have hg0_spec : ∀ g, x1.gates[g0]? = some g →
      g.inputs = [u0.val, v0.val] ∧ (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ↔ isAnd = true) := by
    intro g hg
    rw [hg0_get, Option.some.injEq] at hg
    subst hg
    refine ⟨hg0_ab, ?_⟩
    rcases hg0_op with h | h <;> simp [isAnd, h]
  obtain ⟨T, hTlen, hTpos, hTeval, hTdeg, hTbud⟩ :=
    PEqualNP.Outside.L_meta_5884_aux.SeedUnfold.expandWithSeed g0 u0 v0 isAnd x1.gates hshape hg0_spec
  have hout_lt : x1.output < 14 + x1.gates.length := by
    by_contra hge
    have hev : x1.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 7)) = true :=
      (hcorr _).mpr ⟨0, 0, Or.inl rfl, by decide, by decide⟩
    have hlen : (x1.wires (List.ofFn (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 7))).length = 14 + x1.gates.length := by
      have := PEqualNP.Outside.L_meta_5884_aux.SeedUnfold.wf_len x1.gates (List.ofFn (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 7))
      simpa [PEqualNP.CircuitLowerBounds.Circuit.wires, PEqualNP.Outside.L_meta_5884_aux.SeedUnfold.wf] using this
    have hfalse : x1.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 7)) = false := by
      unfold PEqualNP.CircuitLowerBounds.Circuit.eval
      exact List.getD_eq_default _ _ (by omega)
    rw [hfalse] at hev
    cases hev
  have hout_ge : 14 ≤ x1.output := by
    by_contra hlt
    have hlt' : x1.output < 14 := by omega
    let k : Fin 14 := ⟨x1.output, hlt'⟩
    have hev : x1.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput k k)) = true := by
      unfold PEqualNP.CircuitLowerBounds.Circuit.eval
      change (PEqualNP.Outside.L_meta_5884_aux.SeedUnfold.wf x1.gates (List.ofFn (PEqualNP.EdgeOwnership.pairInput k k))).getD x1.output false = true
      rw [PEqualNP.Outside.L_meta_5884_aux.SeedUnfold.wf_getD_lt _ _ x1.output (by simp [hlt'])]
      rw [List.getD_eq_getElem _ _ (by simp [hlt'])]
      rw [List.getElem_ofFn]
      simp [k, PEqualNP.EdgeOwnership.pairInput]
    obtain ⟨p, l, _, hp, hl⟩ := (hcorr _).mp hev
    simp only [PEqualNP.EdgeOwnership.pairInput, or_self, decide_eq_true_eq] at hp hl
    have hpv := congrArg Fin.val hp
    have hlv := congrArg Fin.val hl
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hpv hlv
    have := p.isLt
    omega
  have hout_T : x1.output < T.length := by omega
  let F15 := T[x1.output]
  have hF15_get : T[x1.output]? = some F15 := List.getElem?_eq_getElem hout_T
  have hF15_pos : PEqualNP.Outside.L_meta_5884_aux.SeedUnfold.pos15 F15 = true := hTpos _ _ hF15_get
  have hF15_eval : ∀ x : Fin 14 → Bool,
      F15.eval (PEqualNP.Outside.L_meta_5884_aux.SeedUnfold.ext15 u0 v0 isAnd x) = x1.eval (List.ofFn x) := by
    intro x
    change F15.eval _ = ((PEqualNP.CircuitLowerBounds.Circuit.mk x1.gates 0).wires (List.ofFn x)).getD x1.output false
    rw [← hTeval x, PEqualNP.Outside.L_meta_5884_aux.SeedUnfold.getMap15 hF15_get]
  have hF15_nodup : (([x1.output] ++ x1.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).filter
      (fun i => decide (14 ≤ i) && (i != 14 + g0))).Nodup := by
    have h1 : (List.filter (fun w => w != 14 + g0)
        (List.filter (fun w => decide (14 ≤ w)) (x1.output :: x1.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs))).Nodup :=
      hg0_nodup
    rw [List.filter_filter] at h1
    simpa [Bool.and_comm] using h1
  have hF15_leaves : F15.leaves ≤ 27 := by
    have hb := hTbud [x1.output] hF15_nodup (by simpa using hout_T)
    have hl : PEqualNP.Outside.L_meta_5884_aux.SeedUnfold.leafSum15 T [x1.output] = F15.leaves := by
      simp [PEqualNP.Outside.L_meta_5884_aux.SeedUnfold.leafSum15,
        PEqualNP.Outside.L_meta_5884_aux.SeedUnfold.leafAt15, hF15_get]
    have hc : PEqualNP.Outside.L_meta_5884_aux.SeedUnfold.countNe g0 x1.gates.length = x1.gates.length - 1 := by
      simp [PEqualNP.Outside.L_meta_5884_aux.SeedUnfold.countNe, hg0_lt]
    rw [hl, hc] at hb
    change x1.gates.length ≤ 27 at hsize
    simp at hb
    omega
  by_cases hcz : PEqualNP.Outside.L_meta_5884_aux.Protocol.countLab (14 : Fin 15) F15 ≤ 1
  · let F14 := PEqualNP.Outside.L_meta_5884_aux.SeedUnfold.substZ u0 v0 isAnd F15
    have hF14_pos : PEqualNP.Outside.L_meta_5884_aux.SeedUnfold.pos14 F14 = true :=
      PEqualNP.Outside.L_meta_5884_aux.SeedUnfold.substZ_pos u0 v0 isAnd F15 hF15_pos
    have hF14_leaves : F14.leaves ≤ 28 := by
      have hsub : F14.leaves = F15.leaves + PEqualNP.Outside.L_meta_5884_aux.Protocol.countLab (14 : Fin 15) F15 :=
        PEqualNP.Outside.L_meta_5884_aux.SeedUnfold.substZ_leaves u0 v0 isAnd F15
      omega
    have hF14_eval : ∀ x : Fin 14 → Bool, F14.eval x = x1.eval (List.ofFn x) := by
      intro x
      rw [PEqualNP.Outside.L_meta_5884_aux.SeedUnfold.substZ_eval u0 v0 isAnd F15 hF15_pos x]
      exact hF15_eval x
    have hF14_deg : ∀ i : Fin 14, PEqualNP.Outside.L_meta_5884_aux.Protocol.degree i F14 = x1.lineDeg 14 {i.val} := by
      intro i
      change PEqualNP.Outside.L_meta_5884_aux.SeedUnfold.degree14 i F14 =
        ((PEqualNP.CircuitLowerBounds.Circuit.mk x1.gates 0).lineDegrees 14 {i.val}).getD x1.output 0
      rw [← hTdeg i, PEqualNP.Outside.L_meta_5884_aux.SeedUnfold.getMap15 hF15_get]
    obtain ⟨A, B, tag, supportsA, supportsB, partition, counts, _⟩ :=
      PEqualNP.Outside.L_meta_5884_aux.Protocol.partitionFormulaExact 14 F14 hF14_pos
    have hrig := PEqualNP.Outside.L_meta_5884_aux.Table.rectangleRigidity F14.leaves A B tag hF14_leaves
      supportsA supportsB (by
        intro a b hab Y X _
        apply partition
        · rw [hF14_eval]
          exact (hcorr _).mpr ⟨a, b, hab, by simp, by simp⟩
        · rw [hF14_eval]
          cases h : x1.eval (List.ofFn (Fin.append (fun u => decide (u ∈ X)) (fun v => decide (v ∈ Y)))) with
          | false => rfl
          | true =>
            obtain ⟨u, v, huv, hu, hv⟩ := (hcorr _).mp h
            have hu' : u ∈ X := by simpa only [Fin.append_left, decide_eq_true_eq] using hu
            have hv' : v ∈ Y := by simpa only [Fin.append_right, decide_eq_true_eq] using hv
            change u ∈ Finset.univ.filter (fun p : Fin 7 => ∀ t ∈ Y,
              p ∉ Finset.univ.filter (fun r : Fin 7 => r = t ∨ r = t + 1 ∨ r = t + 3)) at hu'
            exact ((Finset.mem_filter.mp hu').2 v hv'
              (Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv⟩)).elim) 0 0 (Or.inl rfl)
    rcases hrig with h0 | h7
    · have hd0 : PEqualNP.CircuitLowerBounds.HasLineDegree 14 {0} x1 1 := by
        have bound := (counts (Fin.castAdd 7 (0 : Fin 7))).trans h0
        have heq0 : (Fin.castAdd 7 (0 : Fin 7)).val = 0 := rfl
        unfold PEqualNP.CircuitLowerBounds.HasLineDegree
        rw [← heq0, ← hF14_deg (Fin.castAdd 7 (0 : Fin 7))]
        exact bound
      exact PEqualNP.Outside.L_meta_5884_aux.SeedUnfold.contra_one x1 hshape hout_ge hout_lt 0 7 x11 hd0
        (by decide) hx11.1 hx11.2.1 hx11.2.2.1 hx11.2.2.2
    · have hd7 : PEqualNP.CircuitLowerBounds.HasLineDegree 14 {7} x1 1 := by
        have bound := (counts (Fin.natAdd 7 (0 : Fin 7))).trans h7
        have heq7 : (Fin.natAdd 7 (0 : Fin 7)).val = 7 := rfl
        unfold PEqualNP.CircuitLowerBounds.HasLineDegree
        rw [← heq7, ← hF14_deg (Fin.natAdd 7 (0 : Fin 7))]
        exact bound
      exact PEqualNP.Outside.L_meta_5884_aux.SeedUnfold.contra_one x1 hshape hout_ge hout_lt 7 0 x10 hd7
        (by decide) hx10.1 hx10.2.1 hx10.2.2.1 hx10.2.2.2
  · have hcz2 : 2 ≤ PEqualNP.Outside.L_meta_5884_aux.Protocol.countLab (14 : Fin 15) F15 := by omega
    obtain ⟨A, B, tag, supportsA, supportsB, partition, _, exactCount⟩ :=
      PEqualNP.Outside.L_meta_5884_aux.Protocol.partitionFormulaExact 15 F15 hF15_pos
    obtain ⟨bs, ts, ds, hsym⟩ := PEqualNP.Outside.L_meta_5884_aux.SymCert.pair_sym u0 v0 huv_ne
    let σ := PEqualNP.Outside.L_meta_5884_aux.SymCert.symMap bs ts ds
    have hPairMatch : ∃ cid : Fin 6,
        PEqualNP.Outside.L_meta_5884_aux.SymCert.certIsAnd cid = isAnd ∧
        ((σ u0 = 0 ∧ σ v0 = PEqualNP.Outside.L_meta_5884_aux.SymCert.certOther cid) ∨
         (σ v0 = 0 ∧ σ u0 = PEqualNP.Outside.L_meta_5884_aux.SymCert.certOther cid)) := by
      rcases hsym with ⟨h0, h1 | h7 | h12⟩ | ⟨h0, h1 | h7 | h12⟩
      · cases isAnd
        · exact ⟨1, rfl, Or.inl ⟨h0, h1⟩⟩
        · exact ⟨0, rfl, Or.inl ⟨h0, h1⟩⟩
      · cases isAnd
        · exact ⟨3, rfl, Or.inl ⟨h0, h7⟩⟩
        · exact ⟨2, rfl, Or.inl ⟨h0, h7⟩⟩
      · cases isAnd
        · exact ⟨5, rfl, Or.inl ⟨h0, h12⟩⟩
        · exact ⟨4, rfl, Or.inl ⟨h0, h12⟩⟩
      · cases isAnd
        · exact ⟨1, rfl, Or.inr ⟨h0, h1⟩⟩
        · exact ⟨0, rfl, Or.inr ⟨h0, h1⟩⟩
      · cases isAnd
        · exact ⟨3, rfl, Or.inr ⟨h0, h7⟩⟩
        · exact ⟨2, rfl, Or.inr ⟨h0, h7⟩⟩
      · cases isAnd
        · exact ⟨5, rfl, Or.inr ⟨h0, h12⟩⟩
        · exact ⟨4, rfl, Or.inr ⟨h0, h12⟩⟩
    obtain ⟨cid, hcid_op, hcid_pair⟩ := hPairMatch
    let xPos (r : Fin 21) : Fin 14 → Bool := fun i => PEqualNP.Outside.L_meta_5884_aux.SymCert.posChart r (σ i)
    let xNeg (c : Fin 37) : Fin 14 → Bool := fun i => PEqualNP.Outside.L_meta_5884_aux.SymCert.negChart c (σ i)
    have hSeedEq : ∀ f : Fin 14 → Bool,
        PEqualNP.Outside.L_meta_5884_aux.SeedUnfold.seedVal u0 v0 isAnd (fun i => f (σ i)) =
          PEqualNP.Outside.L_meta_5884_aux.SymCert.seedBit cid f := by
      intro f
      unfold PEqualNP.Outside.L_meta_5884_aux.SeedUnfold.seedVal PEqualNP.Outside.L_meta_5884_aux.SymCert.seedBit
      dsimp only
      rw [hcid_op]
      rcases hcid_pair with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
      · rw [h1, h2]
        cases isAnd <;> simp [Bool.and_comm, Bool.or_comm]
    let isSeed (i : Fin F15.leaves) : Bool := decide (tag i = (14 : Fin 15))
    let rawTag (i : Fin F15.leaves) : Fin 14 :=
      if h : (tag i).val < 14 then σ ⟨(tag i).val, h⟩ else 0
    have hTwo : 2 ≤ Fintype.card {i : Fin F15.leaves // isSeed i = true} := by
      have heq : Fintype.card {i : Fin F15.leaves // isSeed i = true} =
          Fintype.card {i : Fin F15.leaves // tag i = (14 : Fin 15)} := by
        simp [isSeed]
      rw [heq, ← exactCount (14 : Fin 15)]
      exact hcz2
    apply PEqualNP.Outside.L_meta_5884_aux.SymCert.exclude_compressed cid F15.leaves hF15_leaves
      (fun i r => A i (PEqualNP.Outside.L_meta_5884_aux.SeedUnfold.ext15 u0 v0 isAnd (xPos r)))
      (fun i c => B i (PEqualNP.Outside.L_meta_5884_aux.SeedUnfold.ext15 u0 v0 isAnd (xNeg c)))
      isSeed rawTag hTwo
    · intro i r hf hA
      have hne : tag i ≠ (14 : Fin 15) := by simpa [isSeed] using hf
      have hlt : (tag i).val < 14 := by have := (tag i).isLt; omega
      have htag_eq : tag i = Fin.castSucc ⟨(tag i).val, hlt⟩ := by apply Fin.ext; simp
      have hsup := supportsA i _ hA
      rw [htag_eq] at hsup
      simp only [PEqualNP.Outside.L_meta_5884_aux.SeedUnfold.ext15, Fin.snoc_castSucc, xPos] at hsup
      simpa [rawTag, hlt] using hsup
    · intro i c hf hB
      have hne : tag i ≠ (14 : Fin 15) := by simpa [isSeed] using hf
      have hlt : (tag i).val < 14 := by have := (tag i).isLt; omega
      have htag_eq : tag i = Fin.castSucc ⟨(tag i).val, hlt⟩ := by apply Fin.ext; simp
      have hsup := supportsB i _ hB
      rw [htag_eq] at hsup
      simp only [PEqualNP.Outside.L_meta_5884_aux.SeedUnfold.ext15, Fin.snoc_castSucc, xNeg] at hsup
      simpa [rawTag, hlt] using hsup
    · intro i r ht hA
      have heq : tag i = (14 : Fin 15) := by simpa [isSeed] using ht
      have hsup := supportsA i _ hA
      rw [heq] at hsup
      have h14 : (14 : Fin 15) = Fin.last 14 := rfl
      rw [h14] at hsup
      simp only [PEqualNP.Outside.L_meta_5884_aux.SeedUnfold.ext15, Fin.snoc_last] at hsup
      rw [hSeedEq (PEqualNP.Outside.L_meta_5884_aux.SymCert.posChart r)] at hsup
      exact hsup
    · intro i c ht hB
      have heq : tag i = (14 : Fin 15) := by simpa [isSeed] using ht
      have hsup := supportsB i _ hB
      rw [heq] at hsup
      have h14 : (14 : Fin 15) = Fin.last 14 := rfl
      rw [h14] at hsup
      simp only [PEqualNP.Outside.L_meta_5884_aux.SeedUnfold.ext15, Fin.snoc_last] at hsup
      rw [hSeedEq (PEqualNP.Outside.L_meta_5884_aux.SymCert.negChart c)] at hsup
      exact hsup
    · intro r c
      apply partition
      · rw [hF15_eval]
        obtain ⟨p, l, hpl, hp, hl⟩ := PEqualNP.Outside.L_meta_5884_aux.SymCert.sym_pos bs ts ds r
        exact (hcorr _).mpr ⟨p, l, hpl, hp, hl⟩
      · rw [hF15_eval]
        cases hv : x1.eval (List.ofFn (xNeg c)) with
        | false => rfl
        | true =>
          obtain ⟨p, l, hpl, hp, hl⟩ := (hcorr _).mp hv
          exact (PEqualNP.Outside.L_meta_5884_aux.SymCert.sym_neg bs ts ds c p l hpl ⟨hp, hl⟩).elim

end PEqualNP.Outside.L_meta_5884_aux

theorem PEqualNP.Outside.L_meta_5884 : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   have x2 : List ℕ := List.filter (fun (x2 : ℕ) => Decidable.decide ((14 : ℕ) ≤ x2)) (x1.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x1.gates);   have x3 : ℕ → Fin (14 : ℕ) → Prop := fun (x3 : ℕ) (x4 : Fin (14 : ℕ)) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((14 : ℕ) + x3 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x3 (x1.output - (14 : ℕ))) ∧ PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x1 x3 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.true ∧ ∀ (x5 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x3 x5) (PEqualNP.EdgeOwnership.pairInput x4 x4) = Bool.false;   x1.size ≤ (27 : ℕ) → (∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x5]? = Option.some x6 → (x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x8 : ℕ) (x9 : ℕ), x6.inputs = [x8, x9] ∧ x8 ≠ x9 ∧ x8 < (14 : ℕ) + x5 ∧ x9 < (14 : ℕ) + x5) → (∀ (x6 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧ x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) → x2.Nodup → ∀ (x8 x9 : ℕ), x8 ≠ x9 → ¬PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x8 x9 → ¬PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x9 x8 → x3 x8 (0 : Fin (14 : ℕ)) → x3 x9 (7 : Fin (14 : ℕ)) → False) := by
  intro x1 x2 x3 hsize hshape hcorr hnd x8 x9 hne h89 h98 hx8 hx9
  have hlen : 0 < x1.gates.length := by
    by_contra h
    have h0 : x1.gates.length ≤ x8 := by omega
    have hop := hx8.1
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hop
    rw [List.getD_eq_default _ _ h0] at hop
    cases hop
  refine PEqualNP.Outside.L_meta_5884_aux.core x1 hsize hshape hcorr ⟨0, hlen, ?_, ?_⟩ x8 x9 hne h89 h98 hx8 hx9
  · intro i hi
    obtain ⟨_, a, b, hab, _, ha, hb⟩ := hshape 0 x1.gates[0] (List.getElem?_eq_getElem hlen)
    have hg : PEqualNP.MetaComplexity.NestedCover.gateAt x1 0 = x1.gates[0] := by
      simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
    rw [hg, hab] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> omega
  · exact hnd.filter _
