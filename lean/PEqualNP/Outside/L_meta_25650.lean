import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25650_aux

private def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

private def z2b (x : ZMod 2) : Bool := decide (x ≠ 0)

private lemma b2z_z2b (x : ZMod 2) : b2z (z2b x) = x := by
  fin_cases x <;> rfl

private lemma z2b_b2z (b : Bool) : z2b (b2z b) = b := by
  cases b <;> decide

private lemma z2b_add (x y : ZMod 2) : z2b (x + y) = xor (z2b x) (z2b y) := by
  fin_cases x <;> fin_cases y <;> decide

private lemma z2b_mul (x y : ZMod 2) : z2b (x * y) = (z2b x && z2b y) := by
  fin_cases x <;> fin_cases y <;> decide

private lemma z2b_one_add (x : ZMod 2) : z2b (1 + x) = !(z2b x) := by
  fin_cases x <;> decide

private lemma b2z_xor (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by
  cases a <;> cases b <;> decide

private lemma b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by
  cases a <;> cases b <;> decide

private lemma b2z_not (a : Bool) : b2z (!a) = 1 + b2z a := by
  cases a <;> decide

private lemma b2z_inj : Function.Injective b2z := by
  intro a b h
  have := congrArg z2b h
  rwa [z2b_b2z, z2b_b2z] at this

private def vecToZ {L : Nat} (v : Fin L → Bool) : Fin L → ZMod 2 := fun i => b2z (v i)

private def vecToB {L : Nat} (v : Fin L → ZMod 2) : Fin L → Bool := fun i => z2b (v i)

private lemma vecToZ_vecToB {L : Nat} (v : Fin L → ZMod 2) : vecToZ (vecToB v) = v := by
  funext i
  exact b2z_z2b (v i)

private lemma vecToB_vecToZ {L : Nat} (v : Fin L → Bool) : vecToB (vecToZ v) = v := by
  funext i
  exact z2b_b2z (v i)

private lemma vecToZ_inj {L : Nat} : Function.Injective (@vecToZ L) := by
  intro a b h
  funext i
  exact b2z_inj (congrFun h i)

private def xorVec {L : Nat} (a b : Fin L → Bool) : Fin L → Bool :=
  fun i => xor (a i) (b i)

private lemma vecToZ_xorVec {L : Nat} (a b : Fin L → Bool) :
    vecToZ (xorVec a b) = vecToZ a + vecToZ b := by
  funext i
  exact b2z_xor (a i) (b i)

private lemma vecToZ_false {L : Nat} : vecToZ (fun _ : Fin L => false) = 0 := by
  funext i
  rfl

private def condXorVec {L : Nat} (en : Bool) (a b : Fin L → Bool) : Fin L → Bool :=
  fun i => xor (a i) (en && b i)

private lemma vecToZ_condXorVec {L : Nat} (en : Bool) (a b : Fin L → Bool) :
    vecToZ (condXorVec en a b) = vecToZ a + b2z en • vecToZ b := by
  funext i
  change b2z (xor (a i) (en && b i)) = b2z (a i) + b2z en * b2z (b i)
  cases en <;> cases a i <;> cases b i <;> decide

private def reduceFrom {L : Nat} (hasPiv : Fin L → Bool) (pivRow : Fin L → Fin L → Bool) :
    Nat → (Fin L → Bool) → (Fin L → Bool)
  | 0, cur => cur
  | c + 1, cur =>
      let prev := reduceFrom hasPiv pivRow c cur
      if h : c < L then
        let idx : Fin L := ⟨c, h⟩
        condXorVec (hasPiv idx && prev idx) prev (pivRow idx)
      else prev

private def reduceVec {L : Nat} (hasPiv : Fin L → Bool) (pivRow : Fin L → Fin L → Bool)
    (cur : Fin L → Bool) : Fin L → Bool :=
  reduceFrom hasPiv pivRow L cur

private def isUpper {L : Nat} (hasPiv : Fin L → Bool) (pivRow : Fin L → Fin L → Bool) : Prop :=
  (∀ c : Fin L, hasPiv c = false → pivRow c = fun _ => false) ∧
  (∀ c : Fin L, hasPiv c = true → pivRow c c = true ∧ ∀ j : Fin L, j.val < c.val → pivRow c j = false)

private def pivSpan {L : Nat} (hasPiv : Fin L → Bool) (pivRow : Fin L → Fin L → Bool) :
    Submodule (ZMod 2) (Fin L → ZMod 2) :=
  Submodule.span (ZMod 2) { v : Fin L → ZMod 2 | ∃ c : Fin L, hasPiv c = true ∧ v = vecToZ (pivRow c) }

private lemma reduceFrom_sub_mem {L : Nat} (hasPiv : Fin L → Bool) (pivRow : Fin L → Fin L → Bool)
    (cur : Fin L → Bool) :
    ∀ k : Nat, vecToZ (reduceFrom hasPiv pivRow k cur) - vecToZ cur ∈ pivSpan hasPiv pivRow := by
  intro k
  induction k with
  | zero =>
      simp only [reduceFrom, sub_self]
      exact Submodule.zero_mem _
  | succ k ih =>
      simp only [reduceFrom]
      by_cases h : k < L
      · simp only [h, ↓reduceDIte]
        let idx : Fin L := ⟨k, h⟩
        rw [vecToZ_condXorVec]
        have hstep : b2z (hasPiv idx && reduceFrom hasPiv pivRow k cur idx) • vecToZ (pivRow idx) ∈
            pivSpan hasPiv pivRow := by
          cases hp : hasPiv idx
          · simp [b2z]
          · refine Submodule.smul_mem _ _ ?_
            exact Submodule.subset_span ⟨idx, hp, rfl⟩
        have hadd := Submodule.add_mem _ ih hstep
        have heq : vecToZ (reduceFrom hasPiv pivRow k cur) +
            b2z (hasPiv idx && reduceFrom hasPiv pivRow k cur idx) • vecToZ (pivRow idx) - vecToZ cur =
            (vecToZ (reduceFrom hasPiv pivRow k cur) - vecToZ cur) +
            b2z (hasPiv idx && reduceFrom hasPiv pivRow k cur idx) • vecToZ (pivRow idx) := by
          abel
        rw [heq]
        exact hadd
      · simp only [h, ↓reduceDIte]
        exact ih

private lemma reduceFrom_clears {L : Nat} (hasPiv : Fin L → Bool) (pivRow : Fin L → Fin L → Bool)
    (hup : isUpper hasPiv pivRow) (cur : Fin L → Bool) :
    ∀ (k : Nat) (j : Fin L), j.val < k → hasPiv j = true →
      reduceFrom hasPiv pivRow k cur j = false := by
  intro k
  induction k with
  | zero =>
      intro j hj
      omega
  | succ k ih =>
      intro j hj hjp
      simp only [reduceFrom]
      by_cases hk : k < L
      · simp only [hk, ↓reduceDIte]
        let idx : Fin L := ⟨k, hk⟩
        by_cases hlt : j.val < k
        · have hj0 : reduceFrom hasPiv pivRow k cur j = false := ih j hlt hjp
          dsimp only [condXorVec]
          cases hp : hasPiv idx
          · simp [hj0]
          · have hpiv0 : pivRow idx j = false := (hup.2 idx hp).2 j hlt
            change xor (reduceFrom hasPiv pivRow k cur j) ((true && reduceFrom hasPiv pivRow k cur idx) && pivRow idx j) = false
            rw [hj0, hpiv0, Bool.and_false]
            rfl
        · have heq : j = idx := Fin.ext (show j.val = k by omega)
          subst heq
          dsimp only [condXorVec]
          rw [hjp, Bool.true_and, (hup.2 idx hjp).1, Bool.and_true]
          cases reduceFrom hasPiv pivRow k cur idx <;> decide
      · simp only [hk, ↓reduceDIte]
        exact ih j (by omega) hjp

private lemma reduceVec_clears {L : Nat} (hasPiv : Fin L → Bool) (pivRow : Fin L → Fin L → Bool)
    (hup : isUpper hasPiv pivRow) (cur : Fin L → Bool) (j : Fin L) (hjp : hasPiv j = true) :
    reduceVec hasPiv pivRow cur j = false :=
  reduceFrom_clears hasPiv pivRow hup cur L j j.isLt hjp

private lemma pivSpan_eq_zero_of_cleared {L : Nat} (hasPiv : Fin L → Bool)
    (pivRow : Fin L → Fin L → Bool) (hup : isUpper hasPiv pivRow) (w : Fin L → ZMod 2)
    (hw_mem : w ∈ pivSpan hasPiv pivRow)
    (hw_clear : ∀ j : Fin L, hasPiv j = true → w j = 0) :
    w = 0 := by
  have hlin : ∀ (S : Finset (Fin L)) (coef : Fin L → ZMod 2),
      (∀ c ∈ S, hasPiv c = true) →
      (∀ j : Fin L, hasPiv j = true → (∑ c ∈ S, coef c • vecToZ (pivRow c)) j = 0) →
      ∀ c ∈ S, coef c = 0 := by
    intro S
    induction S using Finset.strongInduction with
    | H S ih =>
        intro coef hSp hzero
        by_cases hne : S.Nonempty
        · obtain ⟨cmin, hcminS, hmin⟩ := Finset.exists_min_image S (fun c : Fin L => c.val) hne
          have hval0 := hzero cmin (hSp cmin hcminS)
          rw [Finset.sum_apply, ← Finset.add_sum_erase _ _ hcminS] at hval0
          have hrest0 : ∑ c ∈ S.erase cmin, (coef c • vecToZ (pivRow c)) cmin = 0 := by
            refine Finset.sum_eq_zero fun c hc => ?_
            have hcS : c ∈ S := Finset.mem_of_mem_erase hc
            have hne_c : c ≠ cmin := Finset.ne_of_mem_erase hc
            have hle : cmin.val ≤ c.val := hmin c hcS
            have hlt : cmin.val < c.val := lt_of_le_of_ne hle (fun h => hne_c (Fin.ext h.symm))
            have hp0 : pivRow c cmin = false := (hup.2 c (hSp c hcS)).2 cmin hlt
            simp [vecToZ, hp0, b2z]
          rw [hrest0, add_zero] at hval0
          have hp1 : pivRow cmin cmin = true := (hup.2 cmin (hSp cmin hcminS)).1
          simp only [Pi.smul_apply, smul_eq_mul, vecToZ, hp1, b2z, ↓reduceIte, mul_one] at hval0
          have hsub : S.erase cmin ⊂ S := Finset.erase_ssubset hcminS
          have hzero' : ∀ j : Fin L, hasPiv j = true →
              (∑ c ∈ S.erase cmin, coef c • vecToZ (pivRow c)) j = 0 := by
            intro j hjp
            have hj := hzero j hjp
            rw [← Finset.add_sum_erase _ _ hcminS, hval0, zero_smul, zero_add] at hj
            exact hj
          have hih := ih (S.erase cmin) hsub coef (fun c hc => hSp c (Finset.mem_of_mem_erase hc)) hzero'
          intro c hc
          by_cases hce : c = cmin
          · rw [hce]; exact hval0
          · exact hih c (Finset.mem_erase.mpr ⟨hce, hc⟩)
        · intro c hc
          exact absurd ⟨c, hc⟩ hne
  have hrep : ∃ coef : Fin L → ZMod 2,
      w = ∑ c ∈ Finset.univ.filter (fun c => hasPiv c = true), coef c • vecToZ (pivRow c) := by
    let P := Finset.univ.filter (fun c : Fin L => hasPiv c = true)
    refine Submodule.span_induction (p := fun u _ =>
      ∃ coef : Fin L → ZMod 2, u = ∑ c ∈ P, coef c • vecToZ (pivRow c)) ?_ ?_ ?_ ?_ hw_mem
    · rintro _ ⟨c, hc, rfl⟩
      refine ⟨fun x => if x = c then 1 else 0, ?_⟩
      symm
      rw [Finset.sum_eq_single c]
      · simp
      · intro x _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩) h
    · exact ⟨fun _ => 0, by simp⟩
    · rintro u1 u2 _ _ ⟨c1, rfl⟩ ⟨c2, rfl⟩
      refine ⟨fun c => c1 c + c2 c, ?_⟩
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => (add_smul _ _ _).symm
    · rintro a u _ ⟨c1, rfl⟩
      refine ⟨fun c => a * c1 c, ?_⟩
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun c _ => (mul_smul _ _ _).symm
  rcases hrep with ⟨coef, rfl⟩
  have hcoef0 := hlin (Finset.univ.filter (fun c : Fin L => hasPiv c = true)) coef
    (fun c hc => (Finset.mem_filter.mp hc).2) hw_clear
  exact Finset.sum_eq_zero fun c hc => by rw [hcoef0 c hc, zero_smul]

private lemma reduceVec_eq_false_iff {L : Nat} (hasPiv : Fin L → Bool)
    (pivRow : Fin L → Fin L → Bool) (hup : isUpper hasPiv pivRow) (v : Fin L → Bool) :
    (∀ j : Fin L, reduceVec hasPiv pivRow v j = false) ↔ vecToZ v ∈ pivSpan hasPiv pivRow := by
  have hsub := reduceFrom_sub_mem hasPiv pivRow v L
  constructor
  · intro hall
    have hr0 : vecToZ (reduceVec hasPiv pivRow v) = 0 := by
      funext j
      simp [vecToZ, hall j, b2z]
    rw [reduceVec] at hr0
    rw [hr0, zero_sub] at hsub
    have hneg := Submodule.neg_mem _ hsub
    simpa using hneg
  · intro hmem
    have hr_mem : vecToZ (reduceVec hasPiv pivRow v) ∈ pivSpan hasPiv pivRow := by
      have h := Submodule.add_mem _ hsub hmem
      simpa [reduceVec] using h
    have hr_clear : ∀ j : Fin L, hasPiv j = true → vecToZ (reduceVec hasPiv pivRow v) j = 0 := by
      intro j hjp
      simp [vecToZ, reduceVec_clears hasPiv pivRow hup v j hjp, b2z]
    have hr0 := pivSpan_eq_zero_of_cleared hasPiv pivRow hup _ hr_mem hr_clear
    intro j
    have hj := congrFun hr0 j
    exact b2z_inj hj

private lemma piv_linearIndependent {L : Nat} (hasPiv : Fin L → Bool)
    (pivRow : Fin L → Fin L → Bool) (hup : isUpper hasPiv pivRow) :
    LinearIndependent (ZMod 2)
      (fun c : ↥(Finset.univ.filter (fun c : Fin L => hasPiv c = true)) => vecToZ (pivRow c.val)) := by
  rw [Fintype.linearIndependent_iff]
  intro coef hsum
  let P := Finset.univ.filter (fun c : Fin L => hasPiv c = true)
  let extCoef : Fin L → ZMod 2 := fun c => if h : c ∈ P then coef ⟨c, h⟩ else 0
  have hsum_eq : ∑ c ∈ P, extCoef c • vecToZ (pivRow c) = 0 := by
    have hbij : ∑ c ∈ P, extCoef c • vecToZ (pivRow c) =
        ∑ c : ↥P, coef c • vecToZ (pivRow c.val) := by
      symm
      refine Finset.sum_bij (fun c _ => c.val) (fun c _ => c.2)
        (fun _ _ _ _ h => Subtype.ext h) (fun c hc => ⟨⟨c, hc⟩, Finset.mem_univ _, rfl⟩)
        (fun c _ => by simp [extCoef, c.2])
    rw [hbij, hsum]
  have hlin : ∀ (S : Finset (Fin L)), S ⊆ P →
      (∑ c ∈ S, extCoef c • vecToZ (pivRow c)) = 0 → ∀ c ∈ S, extCoef c = 0 := by
    intro S
    induction S using Finset.strongInduction with
    | H S ih =>
        intro hSP hz
        by_cases hne : S.Nonempty
        · obtain ⟨cmin, hcminS, hmin⟩ := Finset.exists_min_image S (fun c : Fin L => c.val) hne
          have hcminP : hasPiv cmin = true := (Finset.mem_filter.mp (hSP hcminS)).2
          have hval0 := congrFun hz cmin
          rw [Finset.sum_apply, ← Finset.add_sum_erase _ _ hcminS] at hval0
          have hrest0 : ∑ c ∈ S.erase cmin, (extCoef c • vecToZ (pivRow c)) cmin = 0 := by
            refine Finset.sum_eq_zero fun c hc => ?_
            have hcS : c ∈ S := Finset.mem_of_mem_erase hc
            have hcP : hasPiv c = true := (Finset.mem_filter.mp (hSP hcS)).2
            have hne_c : c ≠ cmin := Finset.ne_of_mem_erase hc
            have hlt : cmin.val < c.val := lt_of_le_of_ne (hmin c hcS) (fun h => hne_c (Fin.ext h.symm))
            have hp0 : pivRow c cmin = false := (hup.2 c hcP).2 cmin hlt
            simp [vecToZ, hp0, b2z]
          rw [hrest0, add_zero] at hval0
          have hp1 : pivRow cmin cmin = true := (hup.2 cmin hcminP).1
          simp only [Pi.smul_apply, smul_eq_mul, vecToZ, hp1, b2z, ↓reduceIte, mul_one, Pi.zero_apply] at hval0
          have hz' : ∑ c ∈ S.erase cmin, extCoef c • vecToZ (pivRow c) = 0 := by
            rw [← Finset.add_sum_erase _ _ hcminS, hval0, zero_smul, zero_add] at hz
            exact hz
          have hih := ih (S.erase cmin) (Finset.erase_ssubset hcminS)
            (Finset.Subset.trans (Finset.erase_subset _ _) hSP) hz'
          intro c hc
          by_cases hce : c = cmin
          · rw [hce]; exact hval0
          · exact hih c (Finset.mem_erase.mpr ⟨hce, hc⟩)
        · intro c hc
          exact absurd ⟨c, hc⟩ hne
  intro c
  have h0 := hlin P (Finset.Subset.refl P) hsum_eq c.val c.2
  simpa [extCoef, c.2] using h0

private lemma finrank_pivSpan {L : Nat} (hasPiv : Fin L → Bool)
    (pivRow : Fin L → Fin L → Bool) (hup : isUpper hasPiv pivRow) :
    Module.finrank (ZMod 2) (pivSpan hasPiv pivRow) =
      (Finset.univ.filter (fun c : Fin L => hasPiv c = true)).card := by
  let P := Finset.univ.filter (fun c : Fin L => hasPiv c = true)
  have hli := piv_linearIndependent hasPiv pivRow hup
  have hspan_eq : pivSpan hasPiv pivRow =
      Submodule.span (ZMod 2) (Set.range fun c : ↥P => vecToZ (pivRow c.val)) := by
    unfold pivSpan
    congr 1
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_range, Subtype.exists, P, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨c, hc, rfl⟩; exact ⟨c, hc, rfl⟩
    · rintro ⟨c, hc, rfl⟩; exact ⟨c, hc, rfl⟩
  rw [hspan_eq, finrank_span_eq_card hli, Fintype.card_coe]

private def insertStep {L : Nat} (hasPiv : Fin L → Bool) (pivRow : Fin L → Fin L → Bool)
    (cur : Fin L → Bool) : Nat → Bool × (Fin L → Bool) × (Fin L → Fin L → Bool)
  | 0 => (false, hasPiv, pivRow)
  | c + 1 =>
      let (found, hp, pr) := insertStep hasPiv pivRow cur c
      if h : c < L then
        let idx : Fin L := ⟨c, h⟩
        let take := !found && cur idx
        (found || cur idx,
         fun j => if j = idx then (if take then true else hp j) else hp j,
         fun j k => if j = idx then (if take then cur k else pr j k) else pr j k)
      else (found, hp, pr)

private def echelonStep {L : Nat} (hasPiv : Fin L → Bool) (pivRow : Fin L → Fin L → Bool)
    (row : Fin L → Bool) : (Fin L → Bool) × (Fin L → Fin L → Bool) :=
  let cur := reduceVec hasPiv pivRow row
  let res := insertStep hasPiv pivRow cur L
  (res.2.1, res.2.2)

private def echelonFrom {m L : Nat} (rows : Fin m → Fin L → Bool) :
    Nat → (Fin L → Bool) × (Fin L → Fin L → Bool)
  | 0 => (fun _ => false, fun _ _ => false)
  | g + 1 =>
      let (hp, pr) := echelonFrom rows g
      if h : g < m then echelonStep hp pr (rows ⟨g, h⟩) else (hp, pr)

private def echelon {m L : Nat} (rows : Fin m → Fin L → Bool) :
    (Fin L → Bool) × (Fin L → Fin L → Bool) :=
  echelonFrom rows m

private lemma insertStep_found_iff {L : Nat} (hasPiv : Fin L → Bool)
    (pivRow : Fin L → Fin L → Bool) (cur : Fin L → Bool) :
    ∀ k : Nat, (insertStep hasPiv pivRow cur k).1 = true ↔
      ∃ j : Fin L, j.val < k ∧ cur j = true := by
  intro k
  induction k with
  | zero =>
      simp [insertStep]
  | succ k ih =>
      simp only [insertStep]
      by_cases hk : k < L
      · simp only [hk, ↓reduceDIte, Bool.or_eq_true, ih]
        constructor
        · rintro (⟨j, hj, hcj⟩ | hck)
          · exact ⟨j, by omega, hcj⟩
          · exact ⟨⟨k, hk⟩, Nat.lt_succ_self k, hck⟩
        · rintro ⟨j, hj, hcj⟩
          by_cases hlt : j.val < k
          · exact Or.inl ⟨j, hlt, hcj⟩
          · have : j = ⟨k, hk⟩ := Fin.ext (show j.val = k by omega)
            rw [← this]
            exact Or.inr hcj
      · simp only [hk, ↓reduceDIte, ih]
        constructor
        · rintro ⟨j, hj, hcj⟩; exact ⟨j, by omega, hcj⟩
        · rintro ⟨j, hj, hcj⟩; exact ⟨j, by omega, hcj⟩

private lemma insertStep_props {L : Nat} (hasPiv : Fin L → Bool)
    (pivRow : Fin L → Fin L → Bool) (cur : Fin L → Bool) :
    ∀ (k : Nat) (j : Fin L),
      (k ≤ j.val →
        (insertStep hasPiv pivRow cur k).2.1 j = hasPiv j ∧
        (insertStep hasPiv pivRow cur k).2.2 j = pivRow j) ∧
      (j.val < k →
        let isFirst : Prop := cur j = true ∧ ∀ j' : Fin L, j'.val < j.val → cur j' = false
        (isFirst →
          (insertStep hasPiv pivRow cur k).2.1 j = true ∧
          (insertStep hasPiv pivRow cur k).2.2 j = cur) ∧
        (¬isFirst →
          (insertStep hasPiv pivRow cur k).2.1 j = hasPiv j ∧
          (insertStep hasPiv pivRow cur k).2.2 j = pivRow j)) := by
  intro k
  induction k with
  | zero =>
      intro j
      exact ⟨fun _ => ⟨rfl, rfl⟩, fun h => by omega⟩
  | succ k ih =>
      intro j
      simp only [insertStep]
      by_cases hk : k < L
      · simp only [hk, ↓reduceDIte]
        let idx : Fin L := ⟨k, hk⟩
        constructor
        · intro hkj
          have hne : j ≠ idx := fun h => by have := congrArg Fin.val h; dsimp [idx] at this; omega
          change (if j = idx then _ else (insertStep hasPiv pivRow cur k).2.1 j) = hasPiv j ∧
            (fun m => if j = idx then _ else (insertStep hasPiv pivRow cur k).2.2 j m) = pivRow j
          simp only [hne, ↓reduceIte]
          exact (ih j).1 (by omega)
        · intro hjk
          by_cases hlt : j.val < k
          · have hne : j ≠ idx := fun h => by have := congrArg Fin.val h; dsimp [idx] at this; omega
            change let isFirst : Prop := cur j = true ∧ ∀ j' : Fin L, j'.val < j.val → cur j' = false
              (isFirst → (if j = idx then _ else (insertStep hasPiv pivRow cur k).2.1 j) = true ∧
                (fun m => if j = idx then _ else (insertStep hasPiv pivRow cur k).2.2 j m) = cur) ∧
              (¬isFirst → (if j = idx then _ else (insertStep hasPiv pivRow cur k).2.1 j) = hasPiv j ∧
                (fun m => if j = idx then _ else (insertStep hasPiv pivRow cur k).2.2 j m) = pivRow j)
            simp only [hne, ↓reduceIte]
            exact (ih j).2 hlt
          · have heq : j = idx := Fin.ext (show j.val = k by omega)
            subst heq
            have hprev := (ih idx).1 le_rfl
            have hfound := insertStep_found_iff hasPiv pivRow cur k
            constructor
            · rintro ⟨hcur, hprev0⟩
              have hnf : (insertStep hasPiv pivRow cur k).1 = false := by
                cases hf : (insertStep hasPiv pivRow cur k).1
                · rfl
                · exfalso
                  rcases hfound.mp hf with ⟨j', hj', hcj'⟩
                  have := hprev0 j' hj'
                  rw [this] at hcj'
                  cases hcj'
              change (if idx = idx then (if (!((insertStep hasPiv pivRow cur k).1) && cur idx) then true else _) else _) = true ∧
                (fun m => if idx = idx then (if (!((insertStep hasPiv pivRow cur k).1) && cur idx) then cur m else _) else _) = cur
              simp [hnf, hcur]
            · intro hnot
              have htake : (!(insertStep hasPiv pivRow cur k).1 && cur idx) = false := by
                cases hf : (insertStep hasPiv pivRow cur k).1 <;> cases hc : cur idx
                · rfl
                · exfalso
                  apply hnot
                  refine ⟨hc, fun j' hj' => ?_⟩
                  cases hcj' : cur j'
                  · rfl
                  · exfalso
                    have := hfound.mpr ⟨j', hj', hcj'⟩
                    rw [hf] at this
                    cases this
                · rfl
                · rfl
              change (if idx = idx then (if (!((insertStep hasPiv pivRow cur k).1) && cur idx) then true else (insertStep hasPiv pivRow cur k).2.1 idx) else _) = hasPiv idx ∧
                (fun m => if idx = idx then (if (!((insertStep hasPiv pivRow cur k).1) && cur idx) then cur m else (insertStep hasPiv pivRow cur k).2.2 idx m) else _) = pivRow idx
              simp only [↓reduceIte, htake, Bool.false_eq_true]
              exact hprev
      · simp only [hk, ↓reduceDIte]
        exact ⟨fun hkj => (ih j).1 (by omega), fun hjk => (ih j).2 (by omega)⟩

private lemma echelonStep_spec {L : Nat} (hasPiv : Fin L → Bool) (pivRow : Fin L → Fin L → Bool)
    (hup : isUpper hasPiv pivRow) (row : Fin L → Bool) :
    let res := echelonStep hasPiv pivRow row
    isUpper res.1 res.2 ∧
    pivSpan res.1 res.2 = pivSpan hasPiv pivRow ⊔ Submodule.span (ZMod 2) {vecToZ row} := by
  let cur := reduceVec hasPiv pivRow row
  let res := echelonStep hasPiv pivRow row
  have hprops : ∀ j : Fin L,
      let isFirst : Prop := cur j = true ∧ ∀ j' : Fin L, j'.val < j.val → cur j' = false
      (isFirst → res.1 j = true ∧ res.2 j = cur) ∧
      (¬isFirst → res.1 j = hasPiv j ∧ res.2 j = pivRow j) :=
    fun j => (insertStep_props hasPiv pivRow cur L j).2 j.isLt
  have hcur_clear : ∀ j : Fin L, hasPiv j = true → cur j = false :=
    reduceVec_clears hasPiv pivRow hup row
  have hup' : isUpper res.1 res.2 := by
    constructor
    · intro c hc
      by_cases hf : cur c = true ∧ ∀ j' : Fin L, j'.val < c.val → cur j' = false
      · have h1 := (hprops c).1 hf
        rw [h1.1] at hc
        cases hc
      · have h2 := (hprops c).2 hf
        rw [h2.1] at hc
        rw [h2.2]
        exact hup.1 c hc
    · intro c hc
      by_cases hf : cur c = true ∧ ∀ j' : Fin L, j'.val < c.val → cur j' = false
      · have h1 := (hprops c).1 hf
        rw [h1.2]
        exact hf
      · have h2 := (hprops c).2 hf
        rw [h2.1] at hc
        rw [h2.2]
        exact hup.2 c hc
  refine ⟨hup', ?_⟩
  have hcur_sub : vecToZ cur - vecToZ row ∈ pivSpan hasPiv pivRow :=
    reduceFrom_sub_mem hasPiv pivRow row L
  have hspan_cur : pivSpan hasPiv pivRow ⊔ Submodule.span (ZMod 2) {vecToZ row} =
      pivSpan hasPiv pivRow ⊔ Submodule.span (ZMod 2) {vecToZ cur} := by
    refine le_antisymm ?_ ?_
    · refine sup_le le_sup_left ?_
      rw [Submodule.span_le, Set.singleton_subset_iff]
      have hrow_eq : vecToZ row = vecToZ cur - (vecToZ cur - vecToZ row) := by abel
      rw [hrow_eq]
      exact Submodule.sub_mem _ (Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _)))
        (Submodule.mem_sup_left hcur_sub)
    · refine sup_le le_sup_left ?_
      rw [Submodule.span_le, Set.singleton_subset_iff]
      have hcur_eq : vecToZ cur = (vecToZ cur - vecToZ row) + vecToZ row := by abel
      rw [hcur_eq]
      exact Submodule.add_mem _ (Submodule.mem_sup_left hcur_sub)
        (Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _)))
  rw [hspan_cur]
  by_cases hex : ∃ j : Fin L, cur j = true
  · let S := Finset.univ.filter (fun j : Fin L => cur j = true)
    have hSne : S.Nonempty := by
      rcases hex with ⟨j, hj⟩
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
    obtain ⟨c0, hc0S, hc0min⟩ := Finset.exists_min_image S (fun j : Fin L => j.val) hSne
    have hc0_first : cur c0 = true ∧ ∀ j' : Fin L, j'.val < c0.val → cur j' = false := by
      refine ⟨(Finset.mem_filter.mp hc0S).2, fun j' hj' => ?_⟩
      cases hc : cur j'
      · rfl
      · exfalso
        have hle := hc0min j' (Finset.mem_filter.mpr ⟨Finset.mem_univ j', hc⟩)
        omega
    have hne_first : ∀ j : Fin L, j ≠ c0 →
        ¬(cur j = true ∧ ∀ j' : Fin L, j'.val < j.val → cur j' = false) := by
      intro j hne ⟨hcj, hprev⟩
      have hle := hc0min j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hcj⟩)
      have hlt : c0.val < j.val := lt_of_le_of_ne hle (fun h => hne (Fin.ext h.symm))
      have := hprev c0 hlt
      rw [hc0_first.1] at this
      cases this
    have hc0_old : hasPiv c0 = false := by
      cases hp : hasPiv c0
      · rfl
      · exfalso
        have := hcur_clear c0 hp
        rw [hc0_first.1] at this
        cases this
    refine le_antisymm ?_ ?_
    · rw [pivSpan, Submodule.span_le]
      rintro v ⟨c, hc, rfl⟩
      by_cases hce : c = c0
      · subst hce
        rw [((hprops c).1 hc0_first).2]
        exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _))
      · have h2 := (hprops c).2 (hne_first c hce)
        rw [h2.1] at hc
        rw [h2.2]
        exact Submodule.mem_sup_left (Submodule.subset_span ⟨c, hc, rfl⟩)
    · refine sup_le ?_ ?_
      · rw [pivSpan, Submodule.span_le]
        rintro v ⟨c, hc, rfl⟩
        have hne : c ≠ c0 := fun h => by rw [h, hc0_old] at hc; cases hc
        have h2 := (hprops c).2 (hne_first c hne)
        exact Submodule.subset_span ⟨c, h2.1.symm ▸ hc, congrArg vecToZ h2.2.symm⟩
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        have h1 := (hprops c0).1 hc0_first
        exact Submodule.subset_span ⟨c0, h1.1, congrArg vecToZ h1.2.symm⟩
  · push Not at hex
    have hcur0 : vecToZ cur = 0 := by
      funext j
      have hj : cur j = false := by
        cases h : cur j
        · rfl
        · exact absurd h (hex j)
      simp [vecToZ, hj, b2z]
    have hsame : res.1 = hasPiv ∧ res.2 = pivRow := by
      constructor
      · funext j
        have hnf : ¬(cur j = true ∧ ∀ j' : Fin L, j'.val < j.val → cur j' = false) :=
          fun h => hex j h.1
        exact ((hprops j).2 hnf).1
      · funext j
        have hnf : ¬(cur j = true ∧ ∀ j' : Fin L, j'.val < j.val → cur j' = false) :=
          fun h => hex j h.1
        exact ((hprops j).2 hnf).2
    rw [hsame.1, hsame.2, hcur0, Submodule.span_zero_singleton, sup_bot_eq]

private lemma echelon_spec {m L : Nat} (rows : Fin m → Fin L → Bool) :
    let res := echelon rows
    isUpper res.1 res.2 ∧
    pivSpan res.1 res.2 = Submodule.span (ZMod 2) (Set.range fun g : Fin m => vecToZ (rows g)) := by
  have hgen : ∀ k : Nat,
      let res := echelonFrom rows k
      isUpper res.1 res.2 ∧
      pivSpan res.1 res.2 =
        Submodule.span (ZMod 2) { v : Fin L → ZMod 2 | ∃ g : Fin m, g.val < k ∧ v = vecToZ (rows g) } := by
    intro k
    induction k with
    | zero =>
        refine ⟨⟨fun _ _ => rfl, fun _ h => by cases h⟩, ?_⟩
        unfold pivSpan
        congr 1
        ext v
        simp [echelonFrom]
    | succ k ih =>
        simp only [echelonFrom]
        by_cases hk : k < m
        · simp only [hk, ↓reduceDIte]
          have hstep := echelonStep_spec (echelonFrom rows k).1 (echelonFrom rows k).2 ih.1 (rows ⟨k, hk⟩)
          refine ⟨hstep.1, ?_⟩
          rw [hstep.2, ih.2, ← Submodule.span_union]
          congr 1
          ext v
          simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_singleton_iff]
          constructor
          · rintro (⟨g, hg, rfl⟩ | rfl)
            · exact ⟨g, by omega, rfl⟩
            · exact ⟨⟨k, hk⟩, Nat.lt_succ_self k, rfl⟩
          · rintro ⟨g, hg, rfl⟩
            by_cases hlt : g.val < k
            · exact Or.inl ⟨g, hlt, rfl⟩
            · have : g = ⟨k, hk⟩ := Fin.ext (show g.val = k by omega)
              rw [this]
              exact Or.inr rfl
        · simp only [hk, ↓reduceDIte]
          refine ⟨ih.1, ?_⟩
          rw [ih.2]
          congr 1
          ext v
          simp only [Set.mem_ofPred_eq]
          constructor
          · rintro ⟨g, hg, rfl⟩; exact ⟨g, by omega, rfl⟩
          · rintro ⟨g, hg, rfl⟩; exact ⟨g, by omega, rfl⟩
  have hm := hgen m
  refine ⟨hm.1, ?_⟩
  change pivSpan (echelonFrom rows m).1 (echelonFrom rows m).2 = _
  rw [hm.2]
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro ⟨g, _, rfl⟩; exact ⟨g, rfl⟩
  · rintro ⟨g, rfl⟩; exact ⟨g, g.isLt, rfl⟩


private def insertSlotFrom {t L : Nat} (active : Fin t → Bool) (B : Fin t → Fin L → Bool)
    (en : Bool) (row : Fin L → Bool) :
    Nat → Bool × (Fin t → Bool) × (Fin t → Fin L → Bool)
  | 0 => (false, active, B)
  | j + 1 =>
      let (placed, act, Bs) := insertSlotFrom active B en row j
      if hj : j < t then
        let idx : Fin t := ⟨j, hj⟩
        let take := en && !placed && !act idx
        (placed || take,
         fun x => if x = idx then (if take then true else act x) else act x,
         fun x c => if x = idx then (if take then row c else Bs x c) else Bs x c)
      else (placed, act, Bs)

private def compactFrom {L t : Nat} (hasPiv : Fin L → Bool) (pivRow : Fin L → Fin L → Bool) :
    Nat → (Fin t → Bool) × (Fin t → Fin L → Bool)
  | 0 => (fun _ => false, fun _ _ => false)
  | c + 1 =>
      let (act, B) := compactFrom hasPiv pivRow c
      if hc : c < L then
        let idx : Fin L := ⟨c, hc⟩
        let res := insertSlotFrom act B (hasPiv idx) (pivRow idx) t
        (res.2.1, res.2.2)
      else (act, B)

private def compact {L t : Nat} (hasPiv : Fin L → Bool) (pivRow : Fin L → Fin L → Bool) :
    (Fin t → Bool) × (Fin t → Fin L → Bool) :=
  compactFrom hasPiv pivRow L

private lemma insertSlotFrom_false {t L : Nat} (active : Fin t → Bool) (B : Fin t → Fin L → Bool)
    (row : Fin L → Bool) :
    ∀ k : Nat, insertSlotFrom active B false row k = (false, active, B) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [insertSlotFrom, ih]
      by_cases hk : k < t
      · simp only [hk, ↓reduceDIte, Bool.false_and, Bool.or_false, Bool.false_eq_true, ↓reduceIte, ite_self]
      · simp only [hk, ↓reduceDIte]

private lemma insertSlotFrom_prefix {t L : Nat} (r : Nat) (hrt : r < t)
    (B : Fin t → Fin L → Bool) (row : Fin L → Bool) :
    ∀ k : Nat,
      let res := insertSlotFrom (fun j : Fin t => decide (j.val < r)) B true row k
      res.1 = decide (r < k) ∧
      (∀ j : Fin t, res.2.1 j = decide (j.val < if r < k then r + 1 else r)) ∧
      (∀ j : Fin t, res.2.2 j = if r < k ∧ j.val = r then row else B j) := by
  intro k
  induction k with
  | zero =>
      refine ⟨rfl, fun j => by simp [insertSlotFrom], fun j => by simp [insertSlotFrom]⟩
  | succ k ih =>
      simp only [insertSlotFrom]
      by_cases hk : k < t
      · simp only [hk, ↓reduceDIte]
        rcases ih with ⟨ih1, ih2, ih3⟩
        let idx : Fin t := ⟨k, hk⟩
        have hact_idx : (insertSlotFrom (fun j : Fin t => decide (j.val < r)) B true row k).2.1 idx =
            decide (k < if r < k then r + 1 else r) := ih2 idx
        by_cases hlt : k < r
        · have hnotrk : ¬r < k := by omega
          have hnotrk1 : ¬r < k + 1 := by omega
          have hp0 : (insertSlotFrom (fun j : Fin t => decide (j.val < r)) B true row k).1 = false := by
            rw [ih1]; exact decide_eq_false hnotrk
          have ha1 : (insertSlotFrom (fun j : Fin t => decide (j.val < r)) B true row k).2.1 idx = true := by
            rw [hact_idx, ite_eq_right_iff.mpr (fun h => absurd h hnotrk)]
            exact decide_eq_true hlt
          have htake : (true && !(insertSlotFrom (fun j : Fin t => decide (j.val < r)) B true row k).1 &&
              !(insertSlotFrom (fun j : Fin t => decide (j.val < r)) B true row k).2.1 idx) = false := by
            rw [hp0, ha1]; rfl
          refine ⟨?_, ?_, ?_⟩
          · change ((insertSlotFrom _ B true row k).1 ||
              (true && !(insertSlotFrom _ B true row k).1 && !(insertSlotFrom _ B true row k).2.1 idx)) =
              decide (r < k + 1)
            rw [htake, hp0, decide_eq_false hnotrk1]; rfl
          · intro j
            change (if j = idx then (if (true && !(insertSlotFrom _ B true row k).1 && !(insertSlotFrom _ B true row k).2.1 idx) then true else (insertSlotFrom _ B true row k).2.1 j)
              else (insertSlotFrom _ B true row k).2.1 j) = decide (j.val < if r < k + 1 then r + 1 else r)
            rw [htake]
            simp only [Bool.false_eq_true, ↓reduceIte, ite_self, ih2 j, hnotrk, hnotrk1]
          · intro j
            funext c
            change (if j = idx then (if (true && !(insertSlotFrom _ B true row k).1 && !(insertSlotFrom _ B true row k).2.1 idx) then row c else (insertSlotFrom _ B true row k).2.2 j c)
              else (insertSlotFrom _ B true row k).2.2 j c) =
              (if r < k + 1 ∧ j.val = r then row else B j) c
            rw [htake]
            simp only [Bool.false_eq_true, ↓reduceIte, ite_self, ih3 j, hnotrk, hnotrk1, false_and]
        · by_cases heq : k = r
          · subst heq
            have hnotrk : ¬k < k := lt_irrefl k
            have hrk1 : k < k + 1 := Nat.lt_succ_self k
            have hp0 : (insertSlotFrom (fun j : Fin t => decide (j.val < k)) B true row k).1 = false := by
              rw [ih1]; exact decide_eq_false hnotrk
            have ha0 : (insertSlotFrom (fun j : Fin t => decide (j.val < k)) B true row k).2.1 idx = false := by
              rw [hact_idx, ite_eq_right_iff.mpr (fun h => absurd h hnotrk)]
              exact decide_eq_false hnotrk
            have htake : (true && !(insertSlotFrom (fun j : Fin t => decide (j.val < k)) B true row k).1 &&
                !(insertSlotFrom (fun j : Fin t => decide (j.val < k)) B true row k).2.1 idx) = true := by
              rw [hp0, ha0]; rfl
            refine ⟨?_, ?_, ?_⟩
            · change ((insertSlotFrom _ B true row k).1 ||
                (true && !(insertSlotFrom _ B true row k).1 && !(insertSlotFrom _ B true row k).2.1 idx)) =
                decide (k < k + 1)
              rw [htake, hp0, decide_eq_true hrk1]; rfl
            · intro j
              change (if j = idx then (if (true && !(insertSlotFrom _ B true row k).1 && !(insertSlotFrom _ B true row k).2.1 idx) then true else (insertSlotFrom _ B true row k).2.1 j)
                else (insertSlotFrom _ B true row k).2.1 j) = decide (j.val < if k < k + 1 then k + 1 else k)
              rw [htake, ite_eq_left_iff.mpr (fun h => absurd hrk1 h)]
              by_cases hj : j = idx
              · subst hj
                simp [idx, hrk1]
              · simp only [hj, ↓reduceIte, ih2 j, hnotrk]
                have hjne : j.val ≠ k := fun h => hj (Fin.ext h)
                by_cases hjlt : j.val < k
                · have hjlt1 : j.val < k + 1 := by omega
                  rw [decide_eq_true hjlt, decide_eq_true hjlt1]
                · have hjlt1 : ¬j.val < k + 1 := by omega
                  rw [decide_eq_false hjlt, decide_eq_false hjlt1]
            · intro j
              funext c
              change (if j = idx then (if (true && !(insertSlotFrom _ B true row k).1 && !(insertSlotFrom _ B true row k).2.1 idx) then row c else (insertSlotFrom _ B true row k).2.2 j c)
                else (insertSlotFrom _ B true row k).2.2 j c) =
                (if k < k + 1 ∧ j.val = k then row else B j) c
              rw [htake]
              by_cases hj : j = idx
              · subst hj
                simp [idx, hrk1]
              · have hjne : j.val ≠ k := fun h => hj (Fin.ext h)
                simp only [hj, ↓reduceIte, ih3 j, hnotrk, hjne, and_false]
          · have hrk : r < k := by omega
            have hrk1 : r < k + 1 := by omega
            have hp1 : (insertSlotFrom (fun j : Fin t => decide (j.val < r)) B true row k).1 = true := by
              rw [ih1]; exact decide_eq_true hrk
            have htake : (true && !(insertSlotFrom (fun j : Fin t => decide (j.val < r)) B true row k).1 &&
                !(insertSlotFrom (fun j : Fin t => decide (j.val < r)) B true row k).2.1 idx) = false := by
              rw [hp1]; rfl
            refine ⟨?_, ?_, ?_⟩
            · change ((insertSlotFrom _ B true row k).1 ||
                (true && !(insertSlotFrom _ B true row k).1 && !(insertSlotFrom _ B true row k).2.1 idx)) =
                decide (r < k + 1)
              rw [htake, hp1, decide_eq_true hrk1]; rfl
            · intro j
              change (if j = idx then (if (true && !(insertSlotFrom _ B true row k).1 && !(insertSlotFrom _ B true row k).2.1 idx) then true else (insertSlotFrom _ B true row k).2.1 j)
                else (insertSlotFrom _ B true row k).2.1 j) = decide (j.val < if r < k + 1 then r + 1 else r)
              rw [htake]
              simp only [Bool.false_eq_true, ↓reduceIte, ite_self, ih2 j, hrk, hrk1]
            · intro j
              funext c
              change (if j = idx then (if (true && !(insertSlotFrom _ B true row k).1 && !(insertSlotFrom _ B true row k).2.1 idx) then row c else (insertSlotFrom _ B true row k).2.2 j c)
                else (insertSlotFrom _ B true row k).2.2 j c) =
                (if r < k + 1 ∧ j.val = r then row else B j) c
              rw [htake]
              simp only [Bool.false_eq_true, ↓reduceIte, ite_self, ih3 j, hrk, hrk1, true_and]
      · simp only [hk, ↓reduceDIte]
        have hrk : r < k := by omega
        have hrk1 : r < k + 1 := by omega
        rcases ih with ⟨ih1, ih2, ih3⟩
        refine ⟨?_, ?_, ?_⟩
        · rw [ih1, decide_eq_true hrk, decide_eq_true hrk1]
        · intro j; rw [ih2 j]; simp [hrk, hrk1]
        · intro j; rw [ih3 j]; simp [hrk, hrk1]

private def pivSet {L : Nat} (hasPiv : Fin L → Bool) (k : Nat) : Finset (Fin L) :=
  (Finset.univ : Finset (Fin L)).filter (fun c => c.val < k ∧ hasPiv c = true)

private lemma equiv_finset_cast {α : Type*} {A B : Finset α} (h : A = B)
    (e : Fin A.card ≃ ↥A) :
    ∃ e' : Fin B.card ≃ ↥B, ∀ (n : Nat) (hA : n < A.card) (hB : n < B.card),
      (e' ⟨n, hB⟩).val = (e ⟨n, hA⟩).val := by
  subst h
  exact ⟨e, fun _ _ _ => rfl⟩

private lemma equiv_finset_insert {α : Type*} [DecidableEq α] {A B : Finset α} {x0 : α}
    (hx0 : x0 ∉ A) (hAB : B = insert x0 A) (e : Fin A.card ≃ ↥A) :
    ∃ e' : Fin B.card ≃ ↥B,
      (∀ (n : Nat) (hA : n < A.card) (hB : n < B.card), (e' ⟨n, hB⟩).val = (e ⟨n, hA⟩).val) ∧
      (∀ (hB : A.card < B.card), (e' ⟨A.card, hB⟩).val = x0) := by
  subst hAB
  have hcard : (insert x0 A).card = A.card + 1 := Finset.card_insert_of_notMem hx0
  let e' : Fin (insert x0 A).card ≃ ↥(insert x0 A) :=
    { toFun := fun i =>
        if hi : i.val < A.card then
          ⟨(e ⟨i.val, hi⟩).val, Finset.mem_insert_of_mem (e ⟨i.val, hi⟩).2⟩
        else
          ⟨x0, Finset.mem_insert_self x0 A⟩,
      invFun := fun y =>
        if hy : y.val = x0 then ⟨A.card, by omega⟩
        else
          have hyA : y.val ∈ A := by
            rcases Finset.mem_insert.mp y.2 with h | h
            · exact absurd h hy
            · exact h
          ⟨(e.symm ⟨y.val, hyA⟩).val, by have := (e.symm ⟨y.val, hyA⟩).isLt; omega⟩,
      left_inv := fun i => by
        apply Fin.ext
        by_cases hi : i.val < A.card
        · simp only [hi, ↓reduceDIte]
          have hne : (e ⟨i.val, hi⟩).val ≠ x0 := fun h => hx0 (h ▸ (e ⟨i.val, hi⟩).2)
          simp only [hne, ↓reduceDIte]
          have := e.symm_apply_apply ⟨i.val, hi⟩
          exact congrArg Fin.val this
        · simp only [hi, ↓reduceDIte]
          have hi_lt : i.val < A.card + 1 := hcard ▸ i.isLt
          omega,
      right_inv := fun y => by
        apply Subtype.ext
        by_cases hy : y.val = x0
        · simp only [hy, ↓reduceDIte, lt_irrefl]
        · simp only [hy, ↓reduceDIte]
          have hyA : y.val ∈ A := by
            rcases Finset.mem_insert.mp y.2 with h | h
            · exact absurd h hy
            · exact h
          have hlt : (e.symm ⟨y.val, hyA⟩).val < A.card := (e.symm ⟨y.val, hyA⟩).isLt
          simp only [hlt, ↓reduceDIte]
          have := e.apply_symm_apply ⟨y.val, hyA⟩
          exact congrArg Subtype.val this }
  refine ⟨e', ?_, ?_⟩
  · intro n hA hB
    simp [e', hA]
  · intro hB
    simp [e']

private lemma compactFrom_spec {L t : Nat} (hasPiv : Fin L → Bool) (pivRow : Fin L → Fin L → Bool)
    (hle_t : (Finset.univ.filter (fun c : Fin L => hasPiv c = true)).card ≤ t) :
    ∀ k : Nat,
      let res := compactFrom (t := t) hasPiv pivRow k
      (∀ j : Fin t, res.1 j = decide (j.val < (pivSet hasPiv k).card)) ∧
      ∃ e : Fin (pivSet hasPiv k).card ≃ ↥(pivSet hasPiv k),
        ∀ (j : Fin t) (hj : j.val < (pivSet hasPiv k).card), res.2 j = pivRow (e ⟨j.val, hj⟩).val := by
  intro k
  induction k with
  | zero =>
      have hemp : pivSet hasPiv 0 = ∅ := by ext c; simp [pivSet]
      have hcard0 : (pivSet hasPiv 0).card = 0 := by rw [hemp]; rfl
      refine ⟨fun j => by simp [compactFrom, hcard0], ?_⟩
      have : IsEmpty (Fin (pivSet hasPiv 0).card) := by rw [hcard0]; infer_instance
      have : IsEmpty ↥(pivSet hasPiv 0) := by rw [hemp]; infer_instance
      exact ⟨Equiv.equivOfIsEmpty _ _, fun j hj => by omega⟩
  | succ k ih =>
      simp only [compactFrom]
      rcases ih with ⟨ih1, e, ihe⟩
      by_cases hk : k < L
      · simp only [hk, ↓reduceDIte]
        let idx : Fin L := ⟨k, hk⟩
        cases hp : hasPiv idx
        · have hSeq : pivSet hasPiv (k + 1) = pivSet hasPiv k := by
            ext c
            simp only [pivSet, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨hlt, hcp⟩
              refine ⟨?_, hcp⟩
              by_contra hge
              have : c = idx := Fin.ext (show c.val = k by omega)
              rw [this, hp] at hcp
              cases hcp
            · rintro ⟨hlt, hcp⟩; exact ⟨by omega, hcp⟩
          have hres := insertSlotFrom_false (compactFrom (t := t) hasPiv pivRow k).1
            (compactFrom (t := t) hasPiv pivRow k).2 (pivRow idx) t
          rw [hres]
          obtain ⟨e', he'⟩ := equiv_finset_cast hSeq.symm e
          refine ⟨fun j => by rw [hSeq]; exact ih1 j, e', fun j hj => ?_⟩
          have hj0 : j.val < (pivSet hasPiv k).card := by rwa [← hSeq]
          rw [he' j.val hj0 hj]
          exact ihe j hj0
        · have hnotS : idx ∉ pivSet hasPiv k := by simp [pivSet, idx]
          have hSeq : pivSet hasPiv (k + 1) = insert idx (pivSet hasPiv k) := by
            ext c
            simp only [pivSet, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨hlt, hcp⟩
              by_cases hce : c = idx
              · exact Or.inl hce
              · right
                have hne : c.val ≠ k := fun h => hce (Fin.ext h)
                exact ⟨by omega, hcp⟩
            · rintro (rfl | ⟨hlt, hcp⟩)
              · exact ⟨Nat.lt_succ_self k, hp⟩
              · exact ⟨by omega, hcp⟩
          have hcard' : (pivSet hasPiv (k + 1)).card = (pivSet hasPiv k).card + 1 := by
            rw [hSeq, Finset.card_insert_of_notMem hnotS]
          have hS'_le : (pivSet hasPiv (k + 1)).card ≤ t := by
            refine le_trans (Finset.card_le_card ?_) hle_t
            intro c hc
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ c, (Finset.mem_filter.mp hc).2.2⟩
          have hrt : (pivSet hasPiv k).card < t := by omega
          have hfun1 : (compactFrom (t := t) hasPiv pivRow k).1 =
              fun j : Fin t => decide (j.val < (pivSet hasPiv k).card) := funext ih1
          rw [hfun1]
          have hpref := insertSlotFrom_prefix (pivSet hasPiv k).card hrt
            (compactFrom (t := t) hasPiv pivRow k).2 (pivRow idx) t
          obtain ⟨e', he'_lt, he'_eq⟩ := equiv_finset_insert hnotS hSeq e
          refine ⟨fun j => ?_, e', fun j hj => ?_⟩
          · have hj1 := hpref.2.1 j
            rw [ite_eq_left_iff.mpr (fun h => absurd hrt h), ← hcard'] at hj1
            exact hj1
          · have hj2 := hpref.2.2 j
            rw [hj2]
            by_cases hlt : j.val < (pivSet hasPiv k).card
            · have hne : j.val ≠ (pivSet hasPiv k).card := by omega
              rw [ite_eq_right_iff.mpr (fun h => absurd h.2 hne), he'_lt j.val hlt hj]
              exact ihe j hlt
            · have heq : j.val = (pivSet hasPiv k).card := by omega
              rw [ite_eq_left_iff.mpr (fun h => absurd ⟨hrt, heq⟩ h)]
              have hval_eq : (⟨j.val, hj⟩ : Fin (pivSet hasPiv (k + 1)).card) =
                  ⟨(pivSet hasPiv k).card, by omega⟩ := Fin.ext heq
              rw [hval_eq, he'_eq (by omega)]
      · simp only [hk, ↓reduceDIte]
        have hSeq : pivSet hasPiv (k + 1) = pivSet hasPiv k := by
          ext c
          simp only [pivSet, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨hlt, hcp⟩; exact ⟨by omega, hcp⟩
          · rintro ⟨hlt, hcp⟩; exact ⟨by omega, hcp⟩
        obtain ⟨e', he'⟩ := equiv_finset_cast hSeq.symm e
        refine ⟨fun j => by rw [hSeq]; exact ih1 j, e', fun j hj => ?_⟩
        have hj0 : j.val < (pivSet hasPiv k).card := by rwa [← hSeq]
        rw [he' j.val hj0 hj]
        exact ihe j hj0

private def validMask {t : Nat} (activeSlot : Fin t → Bool) (mask : Fin (2 ^ t)) : Bool :=
  (List.finRange t).all (fun j => !mask.val.testBit j.val || activeSlot j)

private def evalMaskFrom {t L : Nat} (B : Fin t → Fin L → Bool) (mask : Fin (2 ^ t)) :
    Nat → (Fin L → Bool) → (Fin L → Bool)
  | 0, acc => acc
  | j + 1, acc =>
      let prev := evalMaskFrom B mask j acc
      if hj : j < t then
        condXorVec (mask.val.testBit j) prev (B ⟨j, hj⟩)
      else prev

private def evalMask {t L : Nat} (baseB : Fin L → Bool) (B : Fin t → Fin L → Bool)
    (mask : Fin (2 ^ t)) : Fin L → Bool :=
  evalMaskFrom B mask t baseB

private lemma vecToZ_evalMask {t L : Nat} (baseB : Fin L → Bool) (B : Fin t → Fin L → Bool)
    (mask : Fin (2 ^ t)) :
    vecToZ (evalMask baseB B mask) =
      vecToZ baseB + ∑ j : Fin t, b2z (mask.val.testBit j.val) • vecToZ (B j) := by
  have hgen : ∀ k : Nat,
      vecToZ (evalMaskFrom B mask k baseB) =
        vecToZ baseB + ∑ j ∈ (Finset.univ : Finset (Fin t)).filter (fun j => j.val < k),
          b2z (mask.val.testBit j.val) • vecToZ (B j) := by
    intro k
    induction k with
    | zero =>
        simp [evalMaskFrom]
    | succ k ih =>
        simp only [evalMaskFrom]
        by_cases hk : k < t
        · simp only [hk, ↓reduceDIte, vecToZ_condXorVec, ih]
          let idx : Fin t := ⟨k, hk⟩
          have hfilt : (Finset.univ : Finset (Fin t)).filter (fun j => j.val < k + 1) =
              insert idx ((Finset.univ : Finset (Fin t)).filter (fun j => j.val < k)) := by
            ext j
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
            constructor
            · intro hlt
              by_cases hj : j = idx
              · exact Or.inl hj
              · right; have : j.val ≠ k := fun h => hj (Fin.ext h); omega
            · rintro (rfl | hlt)
              · exact Nat.lt_succ_self k
              · omega
          have hnot : idx ∉ (Finset.univ : Finset (Fin t)).filter (fun j => j.val < k) := by
            simp [idx]
          rw [hfilt, Finset.sum_insert hnot]
          abel
        · simp only [hk, ↓reduceDIte, ih]
          congr 2
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          omega
  have ht := hgen t
  have hall : (Finset.univ : Finset (Fin t)).filter (fun j => j.val < t) = Finset.univ := by
    ext j; simp
  rw [hall] at ht
  exact ht

private lemma testBit_add_two_pow_lt : ∀ (j n lo : Nat), j < n →
    (lo + 2 ^ n).testBit j = lo.testBit j := by
  intro j
  induction j with
  | zero =>
      intro n lo hn
      cases n with
      | zero => omega
      | succ n =>
          rw [Nat.testBit_zero, Nat.testBit_zero, pow_succ]
          have : (lo + 2 ^ n * 2) % 2 = lo % 2 := by omega
          rw [this]
  | succ j ih =>
      intro n lo hn
      cases n with
      | zero => omega
      | succ n =>
          rw [Nat.testBit_succ, Nat.testBit_succ, pow_succ]
          have hdiv : (lo + 2 ^ n * 2) / 2 = lo / 2 + 2 ^ n := by omega
          rw [hdiv]
          exact ih n (lo / 2) (by omega)

private lemma testBit_add_two_pow_self : ∀ (n lo : Nat), lo < 2 ^ n →
    (lo + 2 ^ n).testBit n = true := by
  intro n
  induction n with
  | zero =>
      intro lo hlo
      have : lo = 0 := by omega
      subst this
      decide
  | succ n ih =>
      intro lo hlo
      rw [Nat.testBit_succ, pow_succ]
      have hdiv : (lo + 2 ^ n * 2) / 2 = lo / 2 + 2 ^ n := by omega
      rw [hdiv]
      exact ih (lo / 2) (by omega)

private lemma testBit_sum_two_pow : ∀ (n : Nat) (f : Fin n → Bool) (i : Fin n),
    (∑ j : Fin n, if f j then 2 ^ j.val else 0).testBit i.val = f i := by
  have hlt_all : ∀ (m : Nat) (g : Fin m → Bool), (∑ j : Fin m, if g j then 2 ^ j.val else 0) < 2 ^ m := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ihm =>
        intro g
        rw [Fin.sum_univ_castSucc, pow_succ]
        have := ihm (fun j => g j.castSucc)
        cases g (Fin.last m) <;> simp <;> omega
  intro n
  induction n with
  | zero => intro _ i; exact Fin.elim0 i
  | succ n ih =>
      intro f i
      rw [Fin.sum_univ_castSucc]
      have hlo_lt := hlt_all n (fun j => f j.castSucc)
      refine Fin.lastCases ?_ ?_ i
      · simp only [Fin.val_last]
        cases hf : f (Fin.last n)
        · simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
          exact Nat.testBit_lt_two_pow hlo_lt
        · simp only [↓reduceIte]
          exact testBit_add_two_pow_self n _ hlo_lt
      · intro j
        simp only [Fin.val_castSucc, Fin.val_last]
        cases hf : f (Fin.last n)
        · simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
          exact ih (fun x => f x.castSucc) j
        · simp only [↓reduceIte]
          rw [testBit_add_two_pow_lt j.val n _ j.isLt]
          exact ih (fun x => f x.castSucc) j

private lemma evalMask_bijection {L t : Nat} (hasPiv : Fin L → Bool) (pivRow : Fin L → Fin L → Bool)
    (hup : isUpper hasPiv pivRow)
    (hle_t : (Finset.univ.filter (fun c : Fin L => hasPiv c = true)).card ≤ t)
    (baseB : Fin L → Bool) :
    let (activeSlot, B) := compact (t := t) hasPiv pivRow
    (∀ mask : Fin (2 ^ t), validMask activeSlot mask = true →
      vecToZ (evalMask baseB B mask) - vecToZ baseB ∈ pivSpan hasPiv pivRow) ∧
    (∀ m1 m2 : Fin (2 ^ t), validMask activeSlot m1 = true → validMask activeSlot m2 = true →
      evalMask baseB B m1 = evalMask baseB B m2 → m1 = m2) ∧
    (∀ v : Fin L → ZMod 2, v - vecToZ baseB ∈ pivSpan hasPiv pivRow →
      ∃ mask : Fin (2 ^ t), validMask activeSlot mask = true ∧ vecToZ (evalMask baseB B mask) = v) := by
  let P := (Finset.univ : Finset (Fin L)).filter (fun c => hasPiv c = true)
  have hS_eq : pivSet hasPiv L = P := by
    ext c; simp [pivSet, P]
  have hcomp := compactFrom_spec (t := t) hasPiv pivRow hle_t L
  dsimp only at hcomp
  rw [hS_eq] at hcomp
  rcases hcomp with ⟨hact, e, hB⟩
  have hvalid_iff : ∀ mask : Fin (2 ^ t),
      validMask (compact (t := t) hasPiv pivRow).1 mask = true ↔
      ∀ j : Fin t, mask.val.testBit j.val = true → j.val < P.card := by
    intro mask
    simp only [validMask, compact, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
      Bool.not_eq_true']
    constructor
    · intro h j htb
      rcases h j with hf | ht
      · rw [htb] at hf; cases hf
      · rw [hact j] at ht
        exact of_decide_eq_true ht
    · intro h j
      cases htb : mask.val.testBit j.val
      · exact Or.inl rfl
      · right
        rw [hact j]
        exact decide_eq_true (h j htb)
  have hsum_P : ∀ mask : Fin (2 ^ t),
      validMask (compact (t := t) hasPiv pivRow).1 mask = true →
      ∑ j : Fin t, b2z (mask.val.testBit j.val) • vecToZ ((compact (t := t) hasPiv pivRow).2 j) =
        ∑ c : ↥P, b2z (mask.val.testBit (e.symm c).val) • vecToZ (pivRow c.val) := by
    intro mask hvm
    have hvm' := (hvalid_iff mask).mp hvm
    let Q := (Finset.univ : Finset (Fin t)).filter (fun j => j.val < P.card)
    have hfilt :
        ∑ j : Fin t, b2z (mask.val.testBit j.val) • vecToZ ((compact (t := t) hasPiv pivRow).2 j) =
        ∑ j ∈ Q, b2z (mask.val.testBit j.val) • vecToZ ((compact (t := t) hasPiv pivRow).2 j) := by
      symm
      refine Finset.sum_subset (Finset.subset_univ Q) fun j _ hjnot => ?_
      have hge : ¬j.val < P.card := fun hlt => hjnot (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hlt⟩)
      have htb : mask.val.testBit j.val = false := by
        cases h : mask.val.testBit j.val
        · rfl
        · exact absurd (hvm' j h) hge
      simp [htb, b2z]
    rw [hfilt]
    refine Finset.sum_bij (fun j hj => e ⟨j.val, (Finset.mem_filter.mp hj).2⟩)
      (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro j1 hj1 j2 hj2 heq
      have h1 := e.injective heq
      exact Fin.ext (congrArg (Fin.val : Fin P.card → Nat) h1)
    · intro c _
      have hc_lt : (e.symm c).val < t := lt_of_lt_of_le (e.symm c).isLt hle_t
      refine ⟨⟨(e.symm c).val, hc_lt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (e.symm c).isLt⟩, ?_⟩
      exact e.apply_symm_apply c
    · intro j hj
      have hjlt : j.val < P.card := (Finset.mem_filter.mp hj).2
      change b2z (mask.val.testBit j.val) • vecToZ ((compactFrom (t := t) hasPiv pivRow L).2 j) = _
      rw [hB j hjlt]
      have hsymm : (e.symm (e ⟨j.val, hjlt⟩)).val = j.val := congrArg Fin.val (e.symm_apply_apply _)
      rw [hsymm]
  refine ⟨?_, ?_, ?_⟩
  · intro mask hvm
    rw [vecToZ_evalMask, add_sub_cancel_left]
    change ∑ j : Fin t, b2z (mask.val.testBit j.val) • vecToZ ((compact (t := t) hasPiv pivRow).2 j) ∈ _
    rw [hsum_P mask hvm]
    refine Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span ⟨c.val, (Finset.mem_filter.mp c.2).2, rfl⟩
  · intro m1 m2 hm1 hm2 heq
    have hzeq := congrArg vecToZ heq
    rw [vecToZ_evalMask, vecToZ_evalMask] at hzeq
    have hsum_eq := add_left_cancel hzeq
    change ∑ j : Fin t, b2z (m1.val.testBit j.val) • vecToZ ((compact (t := t) hasPiv pivRow).2 j) =
      ∑ j : Fin t, b2z (m2.val.testBit j.val) • vecToZ ((compact (t := t) hasPiv pivRow).2 j) at hsum_eq
    rw [hsum_P m1 hm1, hsum_P m2 hm2] at hsum_eq
    have hdiff : ∑ c : ↥P, (b2z (m1.val.testBit (e.symm c).val) - b2z (m2.val.testBit (e.symm c).val)) •
        vecToZ (pivRow c.val) = 0 := by
      simp_rw [sub_smul, Finset.sum_sub_distrib, hsum_eq, sub_self]
    have hli := piv_linearIndependent hasPiv pivRow hup
    have hcoef := (Fintype.linearIndependent_iff.mp hli) _ hdiff
    have htb_eq : ∀ i : Nat, m1.val.testBit i = m2.val.testBit i := by
      intro i
      by_cases hi : i < t
      · by_cases hiP : i < P.card
        · let c := e ⟨i, hiP⟩
          have hc0 := sub_eq_zero.mp (hcoef c)
          have hsym : (e.symm c).val = i := congrArg Fin.val (e.symm_apply_apply _)
          rw [hsym] at hc0
          exact b2z_inj hc0
        · have hf1 : m1.val.testBit i = false := by
            cases h : m1.val.testBit i
            · rfl
            · exact absurd ((hvalid_iff m1).mp hm1 ⟨i, hi⟩ h) hiP
          have hf2 : m2.val.testBit i = false := by
            cases h : m2.val.testBit i
            · rfl
            · exact absurd ((hvalid_iff m2).mp hm2 ⟨i, hi⟩ h) hiP
          rw [hf1, hf2]
      · have hge : t ≤ i := by omega
        have h1 : m1.val < 2 ^ i := lt_of_lt_of_le m1.isLt (Nat.pow_le_pow_right (by decide : 0 < 2) hge)
        have h2 : m2.val < 2 ^ i := lt_of_lt_of_le m2.isLt (Nat.pow_le_pow_right (by decide : 0 < 2) hge)
        rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]
    exact Fin.ext (Nat.eq_of_testBit_eq htb_eq)
  · intro v hv
    have hrep : ∃ coef : ↥P → ZMod 2, v - vecToZ baseB = ∑ c : ↥P, coef c • vecToZ (pivRow c.val) := by
      refine Submodule.span_induction (p := fun u _ =>
        ∃ coef : ↥P → ZMod 2, u = ∑ c : ↥P, coef c • vecToZ (pivRow c.val)) ?_ ?_ ?_ ?_ hv
      · rintro _ ⟨c, hc, rfl⟩
        let cp : ↥P := ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩⟩
        refine ⟨fun x => if x = cp then 1 else 0, ?_⟩
        symm
        rw [Finset.sum_eq_single cp]
        · simp [cp]
        · intro x _ hne; simp [hne]
        · intro h; exact absurd (Finset.mem_univ cp) h
      · exact ⟨fun _ => 0, by simp⟩
      · rintro u1 u2 _ _ ⟨c1, rfl⟩ ⟨c2, rfl⟩
        refine ⟨fun c => c1 c + c2 c, ?_⟩
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun c _ => (add_smul _ _ _).symm
      · rintro a u _ ⟨c1, rfl⟩
        refine ⟨fun c => a * c1 c, ?_⟩
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun c _ => (mul_smul _ _ _).symm
    rcases hrep with ⟨coef, hcoef⟩
    let bits : Fin P.card → Bool := fun i => z2b (coef (e i))
    let mVal : Nat := ∑ i : Fin P.card, if bits i then 2 ^ i.val else 0
    have hmVal_lt_P : mVal < 2 ^ P.card := by
      have hgen : ∀ (n : Nat) (f : Fin n → Bool), (∑ i : Fin n, if f i then 2 ^ i.val else 0) < 2 ^ n := by
        intro n
        induction n with
        | zero => intro _; simp
        | succ n ih =>
            intro f
            rw [Fin.sum_univ_castSucc, pow_succ]
            have h1 := ih (fun i => f i.castSucc)
            cases f (Fin.last n) <;> simp <;> omega
      exact hgen P.card bits
    have hmVal_lt : mVal < 2 ^ t :=
      lt_of_lt_of_le hmVal_lt_P (Nat.pow_le_pow_right (by decide : 0 < 2) hle_t)
    have hmVal_tb : ∀ i : Fin P.card, mVal.testBit i.val = bits i :=
      testBit_sum_two_pow P.card bits
    let mask : Fin (2 ^ t) := ⟨mVal, hmVal_lt⟩
    have hvm : validMask (compact (t := t) hasPiv pivRow).1 mask = true := by
      rw [hvalid_iff]
      intro j htb
      by_contra hge
      have hlt : mVal < 2 ^ j.val :=
        lt_of_lt_of_le hmVal_lt_P (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
      have := Nat.testBit_lt_two_pow hlt
      rw [this] at htb
      cases htb
    refine ⟨mask, hvm, ?_⟩
    rw [vecToZ_evalMask]
    change vecToZ baseB + ∑ j : Fin t, b2z (mask.val.testBit j.val) • vecToZ ((compact (t := t) hasPiv pivRow).2 j) = v
    rw [hsum_P mask hvm]
    have hsum_eq : ∑ c : ↥P, b2z (mask.val.testBit (e.symm c).val) • vecToZ (pivRow c.val) =
        ∑ c : ↥P, coef c • vecToZ (pivRow c.val) := by
      refine Finset.sum_congr rfl fun c _ => ?_
      change b2z (mVal.testBit (e.symm c).val) • _ = _
      rw [hmVal_tb (e.symm c)]
      dsimp only [bits]
      rw [e.apply_symm_apply, b2z_z2b]
    rw [hsum_eq, ← hcoef, add_sub_cancel]


private def ix (k : Nat) (hk : 0 < k) (site : Nat) : Fin k :=
  ⟨site % k, Nat.mod_lt _ hk⟩

private lemma ix_mod_eq (k : Nat) (hk : 0 < k) (a b : Nat) (h : a % k = b % k) :
    ix k hk a = ix k hk b :=
  Fin.ext h

private lemma ix_sub_mod (k : Nat) (hk : 0 < k) (a d : Nat) (hda : d ≤ a) :
    ix k hk ((ix k hk a).val + k - d % k) = ix k hk (a - d) := by
  apply Fin.ext
  dsimp only [ix]
  have hd_lt : d % k < k := Nat.mod_lt d hk
  have h1 : a % k + k - d % k = a % k + (k - d % k) := by omega
  rw [h1, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  have h2 : a + (k - d % k) = (a - d) + k * (d / k + 1) := by
    have hdiv := Nat.div_add_mod d k
    rw [Nat.mul_succ]
    omega
  rw [h2, Nat.add_mul_mod_self_left]

private lemma ix_add_mod_left (k : Nat) (hk : 0 < k) (a b : Nat) :
    ix k hk ((ix k hk a).val + b) = ix k hk (a + b) := by
  apply Fin.ext
  dsimp only [ix]
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

private lemma ix_add_mod_right (k : Nat) (hk : 0 < k) (a b : Nat) :
    ix k hk (a + (ix k hk b).val) = ix k hk (a + b) := by
  apply Fin.ext
  dsimp only [ix]
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

private lemma ix_fin (k : Nat) (hk : 0 < k) (j : Fin k) : ix k hk j.val = j := by
  apply Fin.ext
  dsimp only [ix]
  exact Nat.mod_eq_of_lt j.isLt

private def rotB (k : Nat) (hk : 0 < k) (t : Nat) (v : Fin k → Bool) (slot : Fin k) : Bool :=
  v (ix k hk (slot.val + k - t % k))

private def runB (k : Nat) (hk : 0 < k) (d t f : Nat) (w name c : Fin k → Bool) (atOut : Fin k) : Bool :=
  let z := fun j : Fin k => xor (rotB k hk t w j) (name j)
  let y := fun atMix : Fin k =>
    xor (xor (z atMix) (z (ix k hk (atMix.val + d)))) (z (ix k hk (atMix.val + k - d % k)))
  xor (xor (xor (y atOut) (!(y (ix k hk (atOut.val + 1))) && y (ix k hk (atOut.val + 2))))
    (rotB k hk f w atOut)) (c atOut)

private lemma z2b_run (k : Nat) (hk : 0 < k) (d t f : Nat) (w name c : Fin k → ZMod 2) (atOut : Fin k) :
    let rot := fun (t0 : Nat) (v : Fin k → ZMod 2) (slot : Fin k) => v (ix k hk (slot.val + k - t0 % k))
    let z := rot t w + name
    let y := fun atMix : Fin k => z atMix + z (ix k hk (atMix.val + d)) + z (ix k hk (atMix.val + k - d % k))
    z2b (y atOut + (1 + y (ix k hk (atOut.val + 1))) * y (ix k hk (atOut.val + 2)) + rot f w atOut + c atOut) =
      runB k hk d t f (vecToB w) (vecToB name) (vecToB c) atOut := by
  have h1 : z2b 1 = true := by decide
  simp only [runB, rotB, vecToB, Pi.add_apply, z2b_add, z2b_mul, h1, Bool.true_xor]

private def unShift (k s : Nat) (hk : 0 < k) (α : Fin k → Bool) (j : Fin k) : Bool :=
  α (ix k hk (j.val + k - s % k))

private def shiftB (k s : Nat) (hk : 0 < k) (w : Fin k → Bool) (j : Fin k) : Bool :=
  w (ix k hk (s + j.val))

private lemma unShift_shiftB (k s : Nat) (hk : 0 < k) (w : Fin k → Bool) :
    unShift k s hk (shiftB k s hk w) = w := by
  funext j
  dsimp only [unShift, shiftB]
  rw [ix_add_mod_right]
  have hs_lt : s % k < k := Nat.mod_lt s hk
  have h1 : s + (j.val + k - s % k) = j.val + k * (s / k + 1) := by
    have := Nat.div_add_mod s k
    rw [Nat.mul_succ]
    omega
  rw [h1]
  have hmod : (j.val + k * (s / k + 1)) % k = j.val := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt j.isLt]
  exact congrArg w (Fin.ext hmod)

private lemma unShift_ix_shift (k s : Nat) (hk : 0 < k) (α : Fin k → Bool) (a : Nat) :
    unShift k s hk α (ix k hk (s + a)) = α (ix k hk a) := by
  dsimp only [unShift]
  rw [ix_sub_mod k hk (s + a) s (Nat.le_add_right s a), Nat.add_sub_cancel_left]

private lemma rotB_unShift (k s : Nat) (hk : 0 < k) (α : Fin k → Bool) (d a : Nat) (hda : d ≤ a) :
    rotB k hk d (unShift k s hk α) (ix k hk (s + a)) = α (ix k hk (a - d)) := by
  dsimp only [rotB]
  rw [ix_sub_mod k hk (s + a) d (by omega)]
  have h1 : s + a - d = s + (a - d) := by omega
  rw [h1, unShift_ix_shift]

private def probeRowB (k s : Nat) (hk : 0 < k) (u cr α : Fin k → Bool) (p : Fin k) : Bool :=
  runB k hk 1 1 0 (unShift k s hk α) u cr (ix k hk (s + p.val + 2))

private def probeColB (k s : Nat) (hk : 0 < k) (v cc α : Fin k → Bool) (p : Fin k) : Bool :=
  runB k hk 2 3 4 (unShift k s hk α) v cc (ix k hk (s + p.val + 5))

private lemma probeRowB_eval (k s : Nat) (hk : 0 < k) (u cr α : Fin k → Bool) (p : Fin k) :
    let a0 := α (ix k hk p.val)
    let a1 := α (ix k hk (p.val + 1))
    let a2 := α (ix k hk (p.val + 2))
    let a3 := α (ix k hk (p.val + 3))
    let a4 := α (ix k hk (p.val + 4))
    let z1 := xor a0 (u (ix k hk (s + p.val + 1)))
    let z2 := xor a1 (u (ix k hk (s + p.val + 2)))
    let z3 := xor a2 (u (ix k hk (s + p.val + 3)))
    let z4 := xor a3 (u (ix k hk (s + p.val + 4)))
    let z5 := xor a4 (u (ix k hk (s + p.val + 5)))
    let y2 := xor (xor z2 z3) z1
    let y3 := xor (xor z3 z4) z2
    let y4 := xor (xor z4 z5) z3
    probeRowB k s hk u cr α p =
      xor (xor (xor y2 (!y3 && y4)) a2) (cr (ix k hk (s + p.val + 2))) := by
  dsimp only [probeRowB, runB]
  have h1 : ix k hk ((ix k hk (s + p.val + 2)).val + 1) = ix k hk (s + (p.val + 3)) := by
    rw [ix_add_mod_left]; exact congrArg (ix k hk) (by omega)
  have h2 : ix k hk ((ix k hk (s + p.val + 2)).val + 2) = ix k hk (s + (p.val + 4)) := by
    rw [ix_add_mod_left]; exact congrArg (ix k hk) (by omega)
  have h0 : ix k hk (s + p.val + 2) = ix k hk (s + (p.val + 2)) := congrArg (ix k hk) (by omega)
  have hsub2 : ix k hk ((ix k hk (s + (p.val + 2))).val + k - 1 % k) = ix k hk (s + (p.val + 1)) := by
    rw [ix_sub_mod k hk (s + (p.val + 2)) 1 (by omega)]; exact congrArg (ix k hk) (by omega)
  have hsub3 : ix k hk ((ix k hk (s + (p.val + 3))).val + k - 1 % k) = ix k hk (s + (p.val + 2)) := by
    rw [ix_sub_mod k hk (s + (p.val + 3)) 1 (by omega)]; exact congrArg (ix k hk) (by omega)
  have hadd3 : ix k hk ((ix k hk (s + (p.val + 3))).val + 1) = ix k hk (s + (p.val + 4)) := by
    rw [ix_add_mod_left]; exact congrArg (ix k hk) (by omega)
  have hsub4 : ix k hk ((ix k hk (s + (p.val + 4))).val + k - 1 % k) = ix k hk (s + (p.val + 3)) := by
    rw [ix_sub_mod k hk (s + (p.val + 4)) 1 (by omega)]; exact congrArg (ix k hk) (by omega)
  have hadd4 : ix k hk ((ix k hk (s + (p.val + 4))).val + 1) = ix k hk (s + (p.val + 5)) := by
    rw [ix_add_mod_left]; exact congrArg (ix k hk) (by omega)
  rw [h1, h2, h0, hsub2, hsub3, hadd3, hsub4, hadd4]
  rw [rotB_unShift k s hk α 1 (p.val + 1) (by omega),
      rotB_unShift k s hk α 1 (p.val + 2) (by omega),
      rotB_unShift k s hk α 1 (p.val + 3) (by omega),
      rotB_unShift k s hk α 1 (p.val + 4) (by omega),
      rotB_unShift k s hk α 1 (p.val + 5) (by omega),
      rotB_unShift k s hk α 0 (p.val + 2) (by omega)]
  have e1 : p.val + 1 - 1 = p.val := by omega
  have e2 : p.val + 2 - 1 = p.val + 1 := by omega
  have e3 : p.val + 3 - 1 = p.val + 2 := by omega
  have e4 : p.val + 4 - 1 = p.val + 3 := by omega
  have e5 : p.val + 5 - 1 = p.val + 4 := by omega
  have e0 : p.val + 2 - 0 = p.val + 2 := by omega
  have u1 : s + (p.val + 1) = s + p.val + 1 := by omega
  have u2 : s + (p.val + 2) = s + p.val + 2 := by omega
  have u3 : s + (p.val + 3) = s + p.val + 3 := by omega
  have u4 : s + (p.val + 4) = s + p.val + 4 := by omega
  have u5 : s + (p.val + 5) = s + p.val + 5 := by omega
  rw [e1, e2, e3, e4, e5, e0, u1, u2, u3, u4, u5]

private lemma probeColB_eval (k s : Nat) (hk : 0 < k) (v cc α : Fin k → Bool) (p : Fin k) :
    let a0 := α (ix k hk p.val)
    let a1 := α (ix k hk (p.val + 1))
    let a2 := α (ix k hk (p.val + 2))
    let a3 := α (ix k hk (p.val + 3))
    let a4 := α (ix k hk (p.val + 4))
    let a5 := α (ix k hk (p.val + 5))
    let a6 := α (ix k hk (p.val + 6))
    let z3 := xor a0 (v (ix k hk (s + p.val + 3)))
    let z4 := xor a1 (v (ix k hk (s + p.val + 4)))
    let z5 := xor a2 (v (ix k hk (s + p.val + 5)))
    let z6 := xor a3 (v (ix k hk (s + p.val + 6)))
    let z7 := xor a4 (v (ix k hk (s + p.val + 7)))
    let z8 := xor a5 (v (ix k hk (s + p.val + 8)))
    let z9 := xor a6 (v (ix k hk (s + p.val + 9)))
    let y5 := xor (xor z5 z7) z3
    let y6 := xor (xor z6 z8) z4
    let y7 := xor (xor z7 z9) z5
    probeColB k s hk v cc α p =
      xor (xor (xor y5 (!y6 && y7)) a1) (cc (ix k hk (s + p.val + 5))) := by
  dsimp only [probeColB, runB]
  have h1 : ix k hk ((ix k hk (s + p.val + 5)).val + 1) = ix k hk (s + (p.val + 6)) := by
    rw [ix_add_mod_left]; exact congrArg (ix k hk) (by omega)
  have h2 : ix k hk ((ix k hk (s + p.val + 5)).val + 2) = ix k hk (s + (p.val + 7)) := by
    rw [ix_add_mod_left]; exact congrArg (ix k hk) (by omega)
  have h0 : ix k hk (s + p.val + 5) = ix k hk (s + (p.val + 5)) := congrArg (ix k hk) (by omega)
  have hsub5 : ix k hk ((ix k hk (s + (p.val + 5))).val + k - 2 % k) = ix k hk (s + (p.val + 3)) := by
    rw [ix_sub_mod k hk (s + (p.val + 5)) 2 (by omega)]; exact congrArg (ix k hk) (by omega)
  have hsub6 : ix k hk ((ix k hk (s + (p.val + 6))).val + k - 2 % k) = ix k hk (s + (p.val + 4)) := by
    rw [ix_sub_mod k hk (s + (p.val + 6)) 2 (by omega)]; exact congrArg (ix k hk) (by omega)
  have hadd6 : ix k hk ((ix k hk (s + (p.val + 6))).val + 2) = ix k hk (s + (p.val + 8)) := by
    rw [ix_add_mod_left]; exact congrArg (ix k hk) (by omega)
  have hsub7 : ix k hk ((ix k hk (s + (p.val + 7))).val + k - 2 % k) = ix k hk (s + (p.val + 5)) := by
    rw [ix_sub_mod k hk (s + (p.val + 7)) 2 (by omega)]; exact congrArg (ix k hk) (by omega)
  have hadd7 : ix k hk ((ix k hk (s + (p.val + 7))).val + 2) = ix k hk (s + (p.val + 9)) := by
    rw [ix_add_mod_left]; exact congrArg (ix k hk) (by omega)
  rw [h1, h2, h0, hsub5, hsub6, hadd6, hsub7, hadd7]
  rw [rotB_unShift k s hk α 3 (p.val + 3) (by omega),
      rotB_unShift k s hk α 3 (p.val + 4) (by omega),
      rotB_unShift k s hk α 3 (p.val + 5) (by omega),
      rotB_unShift k s hk α 3 (p.val + 6) (by omega),
      rotB_unShift k s hk α 3 (p.val + 7) (by omega),
      rotB_unShift k s hk α 3 (p.val + 8) (by omega),
      rotB_unShift k s hk α 3 (p.val + 9) (by omega),
      rotB_unShift k s hk α 4 (p.val + 5) (by omega)]
  have e3 : p.val + 3 - 3 = p.val := by omega
  have e4 : p.val + 4 - 3 = p.val + 1 := by omega
  have e5 : p.val + 5 - 3 = p.val + 2 := by omega
  have e6 : p.val + 6 - 3 = p.val + 3 := by omega
  have e7 : p.val + 7 - 3 = p.val + 4 := by omega
  have e8 : p.val + 8 - 3 = p.val + 5 := by omega
  have e9 : p.val + 9 - 3 = p.val + 6 := by omega
  have e1 : p.val + 5 - 4 = p.val + 1 := by omega
  have u3 : s + (p.val + 3) = s + p.val + 3 := by omega
  have u4 : s + (p.val + 4) = s + p.val + 4 := by omega
  have u5 : s + (p.val + 5) = s + p.val + 5 := by omega
  have u6 : s + (p.val + 6) = s + p.val + 6 := by omega
  have u7 : s + (p.val + 7) = s + p.val + 7 := by omega
  have u8 : s + (p.val + 8) = s + p.val + 8 := by omega
  have u9 : s + (p.val + 9) = s + p.val + 9 := by omega
  rw [e3, e4, e5, e6, e7, e8, e9, e1, u3, u4, u5, u6, u7, u8, u9]

private def setAt {k : Nat} (α : Fin k → Bool) (p : Fin k) (val : Bool) : Fin k → Bool :=
  fun j => if j = p then val else α j

private lemma xor_linear_piv (a b c d e f g : Bool) :
    xor (xor (xor (xor (xor b c) (xor a d)) e) f) g =
      xor a (xor (xor (xor (xor (xor b c) (xor false d)) e) f) g) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> cases g <;> rfl

private lemma probeRowB_solve (k s : Nat) (hk : 0 < k) (u cr α : Fin k → Bool) (p : Fin k)
    (hfit : p.val + 4 < k) :
    probeRowB k s hk u cr α p = xor (α p) (probeRowB k s hk u cr (setAt α p false) p) := by
  rw [probeRowB_eval, probeRowB_eval]
  have h0 : ix k hk p.val = p := ix_fin k hk p
  have h1 : ix k hk (p.val + 1) ≠ p := fun h => by
    have := congrArg Fin.val h; dsimp [ix] at this; rw [Nat.mod_eq_of_lt (by omega)] at this; omega
  have h2 : ix k hk (p.val + 2) ≠ p := fun h => by
    have := congrArg Fin.val h; dsimp [ix] at this; rw [Nat.mod_eq_of_lt (by omega)] at this; omega
  have h3 : ix k hk (p.val + 3) ≠ p := fun h => by
    have := congrArg Fin.val h; dsimp [ix] at this; rw [Nat.mod_eq_of_lt (by omega)] at this; omega
  have h4 : ix k hk (p.val + 4) ≠ p := fun h => by
    have := congrArg Fin.val h; dsimp [ix] at this; rw [Nat.mod_eq_of_lt (by omega)] at this; omega
  simp only [setAt, h0, h1, h2, h3, h4, ↓reduceIte]
  exact xor_linear_piv (α p) _ _ _ _ _ _

private lemma probeColB_solve (k s : Nat) (hk : 0 < k) (v cc α : Fin k → Bool) (p : Fin k)
    (hfit : p.val + 6 < k) :
    probeColB k s hk v cc α p = xor (α p) (probeColB k s hk v cc (setAt α p false) p) := by
  rw [probeColB_eval, probeColB_eval]
  have h0 : ix k hk p.val = p := ix_fin k hk p
  have h1 : ix k hk (p.val + 1) ≠ p := fun h => by
    have := congrArg Fin.val h; dsimp [ix] at this; rw [Nat.mod_eq_of_lt (by omega)] at this; omega
  have h2 : ix k hk (p.val + 2) ≠ p := fun h => by
    have := congrArg Fin.val h; dsimp [ix] at this; rw [Nat.mod_eq_of_lt (by omega)] at this; omega
  have h3 : ix k hk (p.val + 3) ≠ p := fun h => by
    have := congrArg Fin.val h; dsimp [ix] at this; rw [Nat.mod_eq_of_lt (by omega)] at this; omega
  have h4 : ix k hk (p.val + 4) ≠ p := fun h => by
    have := congrArg Fin.val h; dsimp [ix] at this; rw [Nat.mod_eq_of_lt (by omega)] at this; omega
  have h5 : ix k hk (p.val + 5) ≠ p := fun h => by
    have := congrArg Fin.val h; dsimp [ix] at this; rw [Nat.mod_eq_of_lt (by omega)] at this; omega
  have h6 : ix k hk (p.val + 6) ≠ p := fun h => by
    have := congrArg Fin.val h; dsimp [ix] at this; rw [Nat.mod_eq_of_lt (by omega)] at this; omega
  simp only [setAt, h0, h1, h2, h3, h4, h5, h6, ↓reduceIte]
  exact xor_linear_piv (α p) _ _ _ _ _ _

private lemma probeRowB_congr_gt (k s : Nat) (hk : 0 < k) (u cr α1 α2 : Fin k → Bool) (p : Fin k)
    (hfit : p.val + 4 < k)
    (hagree : ∀ j : Fin k, p.val < j.val → j.val ≤ p.val + 4 → α1 j = α2 j) :
    probeRowB k s hk u cr (setAt α1 p false) p = probeRowB k s hk u cr (setAt α2 p false) p := by
  rw [probeRowB_eval, probeRowB_eval]
  have h0 : ix k hk p.val = p := ix_fin k hk p
  have hle : ∀ e : Nat, 1 ≤ e → e ≤ 4 →
      setAt α1 p false (ix k hk (p.val + e)) = setAt α2 p false (ix k hk (p.val + e)) := by
    intro e he1 he4
    have hlt : p.val + e < k := by omega
    have hval : (ix k hk (p.val + e)).val = p.val + e := Nat.mod_eq_of_lt hlt
    have hne : ix k hk (p.val + e) ≠ p := fun h => by have := congrArg Fin.val h; omega
    simp only [setAt, hne, ↓reduceIte]
    exact hagree (ix k hk (p.val + e)) (by omega) (by omega)
  rw [h0, hle 1 (by omega) (by omega), hle 2 (by omega) (by omega),
      hle 3 (by omega) (by omega), hle 4 (by omega) (by omega)]
  simp only [setAt, ↓reduceIte]

private lemma probeColB_congr_gt (k s : Nat) (hk : 0 < k) (v cc α1 α2 : Fin k → Bool) (p : Fin k)
    (hfit : p.val + 6 < k)
    (hagree : ∀ j : Fin k, p.val < j.val → j.val ≤ p.val + 6 → α1 j = α2 j) :
    probeColB k s hk v cc (setAt α1 p false) p = probeColB k s hk v cc (setAt α2 p false) p := by
  rw [probeColB_eval, probeColB_eval]
  have h0 : ix k hk p.val = p := ix_fin k hk p
  have hle : ∀ e : Nat, 1 ≤ e → e ≤ 6 →
      setAt α1 p false (ix k hk (p.val + e)) = setAt α2 p false (ix k hk (p.val + e)) := by
    intro e he1 he6
    have hlt : p.val + e < k := by omega
    have hval : (ix k hk (p.val + e)).val = p.val + e := Nat.mod_eq_of_lt hlt
    have hne : ix k hk (p.val + e) ≠ p := fun h => by have := congrArg Fin.val h; omega
    simp only [setAt, hne, ↓reduceIte]
    exact hagree (ix k hk (p.val + e)) (by omega) (by omega)
  rw [h0, hle 1 (by omega) (by omega), hle 2 (by omega) (by omega),
      hle 3 (by omega) (by omega), hle 4 (by omega) (by omega),
      hle 5 (by omega) (by omega), hle 6 (by omega) (by omega)]
  simp only [setAt, ↓reduceIte]

private def reconstructFrom (k s : Nat) (hk : 0 < k) (row col : Fin k → Bool)
    (u v cr cc : Fin k → Bool) (β : Fin k → Bool) : Nat → (Fin k → Bool)
  | 0 => β
  | d + 1 =>
      let α := reconstructFrom k s hk row col u v cr cc β d
      let pVal := k - 1 - d
      if hp : pVal < k then
        let p : Fin k := ⟨pVal, hp⟩
        if row p = true ∧ p.val + 4 < k then
          setAt α p (probeRowB k s hk u cr (setAt α p false) p)
        else if col p = true ∧ p.val + 6 < k then
          setAt α p (probeColB k s hk v cc (setAt α p false) p)
        else α
      else α

private def reconstruct (k s : Nat) (hk : 0 < k) (row col : Fin k → Bool)
    (u v cr cc : Fin k → Bool) (β : Fin k → Bool) : Fin k → Bool :=
  reconstructFrom k s hk row col u v cr cc β k

private def passAll (k s : Nat) (hk : 0 < k) (row col : Fin k → Bool)
    (u v cr cc α : Fin k → Bool) : Bool :=
  (List.finRange k).all (fun p =>
    (!row p || !probeRowB k s hk u cr α p) &&
    (!col p || !probeColB k s hk v cc α p))

private lemma passAll_iff (k s : Nat) (hk : 0 < k) (row col : Fin k → Bool)
    (u v cr cc α : Fin k → Bool) :
    passAll k s hk row col u v cr cc α = true ↔
      ∀ p : Fin k, (row p = true → probeRowB k s hk u cr α p = false) ∧
        (col p = true → probeColB k s hk v cc α p = false) := by
  simp only [passAll, List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
    Bool.or_eq_true, Bool.not_eq_true']
  refine forall_congr' fun p => ?_
  cases row p <;> cases col p <;> cases probeRowB k s hk u cr α p <;>
    cases probeColB k s hk v cc α p <;> simp

private lemma reconstruct_preserves_nonpiv (k s : Nat) (hk : 0 < k) (row col : Fin k → Bool)
    (u v cr cc β : Fin k → Bool) (j : Fin k)
    (hnp : ¬((row j = true ∧ j.val + 4 < k) ∨ (col j = true ∧ j.val + 6 < k))) :
    ∀ d : Nat, reconstructFrom k s hk row col u v cr cc β d j = β j := by
  intro d
  induction d with
  | zero => rfl
  | succ d ih =>
      simp only [reconstructFrom]
      split_ifs with hp h1 h2
      · by_cases hj : j = ⟨k - 1 - d, hp⟩
        · subst hj; exact absurd (Or.inl h1) hnp
        · simp [setAt, hj, ih]
      · by_cases hj : j = ⟨k - 1 - d, hp⟩
        · subst hj; exact absurd (Or.inr h2) hnp
        · simp [setAt, hj, ih]
      · exact ih
      · exact ih

private lemma reconstruct_eq_of_pass (k s : Nat) (hk : 0 < k) (row col : Fin k → Bool)
    (u v cr cc β αTrue : Fin k → Bool)
    (hpass : passAll k s hk row col u v cr cc αTrue = true)
    (hbnd : ∀ j : Fin k,
      (∃ p : Fin k, ∃ e : Fin 7, ix k hk (p.val + e.val) = j ∧ ((row p = true ∧ e.val ≤ 4) ∨ col p = true)) →
      ¬((row j = true ∧ j.val + 4 < k) ∨ (col j = true ∧ j.val + 6 < k)) →
      β j = αTrue j) :
    ∀ (d : Nat), d ≤ k → ∀ (j : Fin k), k - d ≤ j.val →
      (∃ p : Fin k, ∃ e : Fin 7, ix k hk (p.val + e.val) = j ∧ ((row p = true ∧ e.val ≤ 4) ∨ col p = true)) →
      reconstructFrom k s hk row col u v cr cc β d j = αTrue j := by
  have hpass' := (passAll_iff k s hk row col u v cr cc αTrue).mp hpass
  intro d
  induction d with
  | zero =>
      intro _ j hj
      omega
  | succ d ih =>
      intro hdk1 j hj hact
      have hdk : d < k := by omega
      have hp : k - 1 - d < k := by omega
      let p : Fin k := ⟨k - 1 - d, hp⟩
      have hpval : p.val = k - 1 - d := rfl
      have hstep_gt : ∀ j' : Fin k, p.val < j'.val →
          reconstructFrom k s hk row col u v cr cc β (d + 1) j' =
            reconstructFrom k s hk row col u v cr cc β d j' := by
        intro j' hj'
        have hne : j' ≠ ⟨k - 1 - d, hp⟩ := fun h => by
          have := congrArg Fin.val h; dsimp at this; omega
        simp only [reconstructFrom, hp, ↓reduceDIte]
        split_ifs <;> simp only [setAt, hne, ↓reduceIte]
      by_cases hgt : p.val < j.val
      · rw [hstep_gt j hgt]
        exact ih (by omega) j (by omega) hact
      · have hjeq : j = p := Fin.ext (show j.val = k - 1 - d by omega)
        subst hjeq
        by_cases h1 : row p = true ∧ p.val + 4 < k
        · simp only [reconstructFrom, hp, ↓reduceDIte]
          rw [ite_eq_left_iff.mpr (fun h => absurd h1 h)]
          simp only [setAt, p, ↓reduceIte]
          have hagree : ∀ j' : Fin k, p.val < j'.val → j'.val ≤ p.val + 4 →
              reconstructFrom k s hk row col u v cr cc β d j' = αTrue j' := by
            intro j' hlt hle
            refine ih (by omega) j' (by omega) ?_
            refine ⟨p, ⟨j'.val - p.val, by omega⟩, ?_, Or.inl ⟨h1.1, by dsimp only; omega⟩⟩
            apply Fin.ext
            dsimp only [ix]
            have : p.val + (j'.val - p.val) = j'.val := by omega
            rw [this, Nat.mod_eq_of_lt j'.isLt]
          rw [probeRowB_congr_gt k s hk u cr _ αTrue p h1.2 hagree]
          have hsol := probeRowB_solve k s hk u cr αTrue p h1.2
          have hp0 := (hpass' p).1 h1.1
          rw [hp0] at hsol
          cases hA : αTrue p <;> cases hB : probeRowB k s hk u cr (setAt αTrue p false) p <;>
            rw [hA, hB] at hsol <;> cases hsol
        · by_cases h2 : col p = true ∧ p.val + 6 < k
          · simp only [reconstructFrom, hp, ↓reduceDIte]
            rw [ite_eq_right_iff.mpr (fun h => absurd h h1), ite_eq_left_iff.mpr (fun h => absurd h2 h)]
            simp only [setAt, p, ↓reduceIte]
            have hagree : ∀ j' : Fin k, p.val < j'.val → j'.val ≤ p.val + 6 →
                reconstructFrom k s hk row col u v cr cc β d j' = αTrue j' := by
              intro j' hlt hle
              refine ih (by omega) j' (by omega) ?_
              refine ⟨p, ⟨j'.val - p.val, by omega⟩, ?_, Or.inr h2.1⟩
              apply Fin.ext
              dsimp only [ix]
              have : p.val + (j'.val - p.val) = j'.val := by omega
              rw [this, Nat.mod_eq_of_lt j'.isLt]
            rw [probeColB_congr_gt k s hk v cc _ αTrue p h2.2 hagree]
            have hsol := probeColB_solve k s hk v cc αTrue p h2.2
            have hp0 := (hpass' p).2 h2.1
            rw [hp0] at hsol
            cases hA : αTrue p <;> cases hB : probeColB k s hk v cc (setAt αTrue p false) p <;>
              rw [hA, hB] at hsol <;> cases hsol
          · have hnp : ¬((row p = true ∧ p.val + 4 < k) ∨ (col p = true ∧ p.val + 6 < k)) :=
              fun h => h.elim h1 h2
            rw [reconstruct_preserves_nonpiv k s hk row col u v cr cc β p hnp (d + 1)]
            exact hbnd p hact hnp

private lemma passAll_depends_active (k s : Nat) (hk : 0 < k) (row col : Fin k → Bool)
    (u v cr cc α1 α2 : Fin k → Bool)
    (hagree : ∀ j : Fin k,
      (∃ p : Fin k, ∃ e : Fin 7, ix k hk (p.val + e.val) = j ∧ ((row p = true ∧ e.val ≤ 4) ∨ col p = true)) →
      α1 j = α2 j) :
    passAll k s hk row col u v cr cc α1 = passAll k s hk row col u v cr cc α2 := by
  simp only [passAll]
  congr 1
  funext p
  congr 1
  · cases hrow : row p
    · rfl
    · simp only [Bool.not_true, Bool.false_or]
      congr 1
      rw [probeRowB_eval, probeRowB_eval]
      have h : ∀ e : Nat, e ≤ 4 → α1 (ix k hk (p.val + e)) = α2 (ix k hk (p.val + e)) := fun e he =>
        hagree _ ⟨p, ⟨e, by omega⟩, rfl, Or.inl ⟨hrow, he⟩⟩
      have h0 : α1 (ix k hk p.val) = α2 (ix k hk p.val) := by
        simpa using h 0 (by omega)
      rw [h0, h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega)]
  · cases hcol : col p
    · rfl
    · simp only [Bool.not_true, Bool.false_or]
      congr 1
      rw [probeColB_eval, probeColB_eval]
      have h : ∀ e : Nat, e ≤ 6 → α1 (ix k hk (p.val + e)) = α2 (ix k hk (p.val + e)) := fun e he =>
        hagree _ ⟨p, ⟨e, by omega⟩, rfl, Or.inr hcol⟩
      have h0 : α1 (ix k hk p.val) = α2 (ix k hk p.val) := by
        simpa using h 0 (by omega)
      rw [h0, h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega),
          h 5 (by omega), h 6 (by omega)]


private lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

private lemma testBit_mul_two_pow (M : Nat) :
    ∀ (d o : Nat), (M * 2 ^ d).testBit o = if d ≤ o then M.testBit (o - d) else false := by
  intro d
  induction d with
  | zero =>
      intro o
      simp
  | succ d ih =>
      intro o
      rw [pow_succ, ← mul_assoc]
      cases o with
      | zero =>
          simp [Nat.testBit_zero]
      | succ o =>
          rw [Nat.testBit_succ, Nat.mul_div_cancel _ (by decide : 0 < 2), ih o]
          by_cases h : d ≤ o
          · have h1 : d + 1 ≤ o + 1 := by omega
            have h2 : o + 1 - (d + 1) = o - d := by omega
            simp [h, h1, h2]
          · have h1 : ¬d + 1 ≤ o + 1 := by omega
            simp [h, h1]

private lemma card_submodule_zmod2 {L : Nat} (U : Submodule (ZMod 2) (Fin L → ZMod 2)) :
    Nat.card U = 2 ^ Module.finrank (ZMod 2) U := by
  let b := Module.finBasis (ZMod 2) U
  have hcard : Nat.card U = Nat.card (Fin (Module.finrank (ZMod 2) U) → ZMod 2) :=
    Nat.card_congr b.equivFun.toEquiv
  rw [hcard, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]

private def genMap {m L : Nat} (g : Fin m → Fin L → ZMod 2) :
    (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin L → ZMod 2) where
  toFun a := ∑ i : Fin m, a i • g i
  map_add' a b := by
    simp_rw [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r a := by
    simp_rw [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

private lemma range_genMap {m L : Nat} (g : Fin m → Fin L → ZMod 2) :
    LinearMap.range (genMap g) = Submodule.span (ZMod 2) (Set.range g) := by
  refine le_antisymm ?_ ?_
  · rintro v ⟨a, rfl⟩
    change ∑ i : Fin m, a i • g i ∈ Submodule.span (ZMod 2) (Set.range g)
    exact Submodule.sum_mem (Submodule.span (ZMod 2) (Set.range g)) fun i _ =>
      Submodule.smul_mem (Submodule.span (ZMod 2) (Set.range g)) (a i) (Submodule.subset_span (Set.mem_range_self i))
  · rw [Submodule.span_le]
    rintro v ⟨i, rfl⟩
    refine ⟨fun j => if j = i then 1 else 0, ?_⟩
    dsimp [genMap]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hne; simp [hne]
    · intro h; exact absurd (Finset.mem_univ i) h

private def projMap (k s : Nat) (hk : 0 < k) {n : Nat} (idx : Fin n → Fin k) :
    (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) where
  toFun w c := w (ix k hk (s + (idx c).val))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma projMap_comp_genMap (k s : Nat) (hk : 0 < k) {m n : Nat}
    (idx : Fin n → Fin k) (gen : Fin m → Fin k → ZMod 2) :
    (projMap k s hk idx).comp (genMap gen) = genMap (fun g => projMap k s hk idx (gen g)) := by
  ext a c
  simp [projMap, genMap, Finset.sum_apply]

private def activeSet (k : Nat) (hk : 0 < k) (row col : Fin k → Bool) : Finset (Fin k) :=
  Finset.univ.filter (fun reached : Fin k =>
    ∃ p : Fin k, ∃ e : Fin 7, ix k hk (p.val + e.val) = reached ∧
      ((row p = true ∧ e.val ≤ 4) ∨ col p = true))

private def pivSetMask (k : Nat) (row col : Fin k → Bool) : Finset (Fin k) :=
  Finset.univ.filter (fun p : Fin k =>
    (row p = true ∧ p.val + 4 < k) ∨ (col p = true ∧ p.val + 6 < k))

private def bndSet (k : Nat) (hk : 0 < k) (row col : Fin k → Bool) : Finset (Fin k) :=
  activeSet k hk row col \ pivSetMask k row col

private noncomputable def eAct (k : Nat) (hk : 0 < k) (row col : Fin k → Bool) :
    Fin (activeSet k hk row col).card ≃ ↥(activeSet k hk row col) :=
  (activeSet k hk row col).equivFin.symm

private noncomputable def eBnd (k : Nat) (hk : 0 < k) (row col : Fin k → Bool) :
    Fin (bndSet k hk row col).card ≃ ↥(bndSet k hk row col) :=
  (bndSet k hk row col).equivFin.symm

private noncomputable def maskFlag (k s : Nat) (hk : 0 < k) (row col : Fin k → Bool)
    (q : Nat)
    (baseAct : Fin (activeSet k hk row col).card → Bool)
    (baseBnd : Fin (bndSet k hk row col).card → Bool)
    (hasAct : Fin (activeSet k hk row col).card → Bool)
    (pivAct : Fin (activeSet k hk row col).card → Fin (activeSet k hk row col).card → Bool)
    (activeSlot : Fin (min q (bndSet k hk row col).card) → Bool)
    (B : Fin (min q (bndSet k hk row col).card) → Fin (bndSet k hk row col).card → Bool)
    (uB vB crB ccB : Fin k → Bool)
    (mask : Fin (2 ^ min q (bndSet k hk row col).card)) : Bool :=
  let vm := validMask activeSlot mask
  let bVec := evalMask baseBnd B mask
  let eB := eBnd k hk row col
  let eA := eAct k hk row col
  let β : Fin k → Bool := fun j =>
    if hj : j ∈ bndSet k hk row col then bVec (eB.symm ⟨j, hj⟩) else false
  let α := reconstruct k s hk row col uB vB crB ccB β
  let okPass := passAll k s hk row col uB vB crB ccB α
  let diffAct : Fin (activeSet k hk row col).card → Bool :=
    fun c => xor (α (eA c).val) (baseAct c)
  let okMem := (List.finRange (activeSet k hk row col).card).all
    (fun c => !reduceVec hasAct pivAct diffAct c)
  vm && okPass && okMem

private lemma count_eq_shifted (k m q s : Nat) (hk : 0 < k) (row col : Fin k → Bool)
    (base : Fin k → ZMod 2) (gen : Fin m → Fin k → ZMod 2) (u v cr cc : Fin k → ZMod 2)
    (hprom : Nat.card (Set.range (fun coeff : Fin m → ZMod 2 =>
      fun member : bndSet k hk row col =>
        (base + ∑ i : Fin m, coeff i • gen i) (ix k hk (s + member.val.val)))) ≤ 2 ^ q) :
    let eA := eAct k hk row col
    let eB := eBnd k hk row col
    let t := min q (bndSet k hk row col).card
    let rowsFull : Fin m → Fin k → Bool := fun g j => z2b (gen g j)
    let rowsAct : Fin m → Fin (activeSet k hk row col).card → Bool :=
      fun g c => z2b (gen g (ix k hk (s + (eA c).val.val)))
    let rowsBnd : Fin m → Fin (bndSet k hk row col).card → Bool :=
      fun g c => z2b (gen g (ix k hk (s + (eB c).val.val)))
    let baseAct : Fin (activeSet k hk row col).card → Bool :=
      fun c => z2b (base (ix k hk (s + (eA c).val.val)))
    let baseBnd : Fin (bndSet k hk row col).card → Bool :=
      fun c => z2b (base (ix k hk (s + (eB c).val.val)))
    let echFull := echelon rowsFull
    let echAct := echelon rowsAct
    let echBnd := echelon rowsBnd
    let compBnd := compact (t := t) echBnd.1 echBnd.2
    let rFull := (Finset.univ.filter (fun c : Fin k => echFull.1 c = true)).card
    let rAct := (Finset.univ.filter (fun c : Fin (activeSet k hk row col).card => echAct.1 c = true)).card
    let M := (Finset.univ.filter (fun mask : Fin (2 ^ t) =>
      maskFlag k s hk row col q baseAct baseBnd echAct.1 echAct.2 compBnd.1 compBnd.2
        (vecToB u) (vecToB v) (vecToB cr) (vecToB cc) mask = true)).card
    let rot := fun (t0 : Nat) (w : Fin k → ZMod 2) (slot : Fin k) => w (ix k hk (slot.val + k - t0 % k))
    let run := fun (d t0 f : Nat) (w name c : Fin k → ZMod 2) =>
      let z := rot t0 w + name
      let y := fun atMix : Fin k => z atMix + z (ix k hk (atMix.val + d)) + z (ix k hk (atMix.val + k - d % k))
      fun atOut : Fin k => y atOut + (1 + y (ix k hk (atOut.val + 1))) * y (ix k hk (atOut.val + 2)) + rot f w atOut + c atOut
    let key := fun a : Fin m → ZMod 2 => base + ∑ i : Fin m, a i • gen i
    let count := Nat.card { w : Fin k → ZMod 2 // w ∈ Set.range key ∧
      ∀ p : Fin k, (row p = true → run 1 1 0 w u cr (ix k hk (s + p.val + 2)) = 0) ∧
                   (col p = true → run 2 3 4 w v cc (ix k hk (s + p.val + 5)) = 0) }
    rAct ≤ rFull ∧ rFull ≤ k ∧ M < 2 ^ (k + 1) ∧ count = M * 2 ^ (rFull - rAct) := by
  intro eA eB t rowsFull rowsAct rowsBnd baseAct baseBnd echFull echAct echBnd compBnd rFull rAct M rot run key count
  let L := genMap gen
  let Pact := projMap k s hk (fun c => (eA c).val)
  let Pbnd := projMap k s hk (fun c => (eB c).val)
  have hkey_eq : ∀ a : Fin m → ZMod 2, key a = base + L a := fun _ => rfl
  have hspecFull := echelon_spec rowsFull
  have hspecAct := echelon_spec rowsAct
  have hspecBnd := echelon_spec rowsBnd
  have hrowsFull_eq : (fun g : Fin m => vecToZ (rowsFull g)) = gen := by
    funext g j; exact b2z_z2b (gen g j)
  have hrowsAct_eq : (fun g : Fin m => vecToZ (rowsAct g)) = fun g => Pact (gen g) := by
    funext g c; exact b2z_z2b _
  have hrowsBnd_eq : (fun g : Fin m => vecToZ (rowsBnd g)) = fun g => Pbnd (gen g) := by
    funext g c; exact b2z_z2b _
  have hspanFull : pivSpan echFull.1 echFull.2 = LinearMap.range L := by
    rw [hspecFull.2, hrowsFull_eq, range_genMap]
  have hspanAct : pivSpan echAct.1 echAct.2 = LinearMap.range (Pact.comp L) := by
    rw [hspecAct.2, hrowsAct_eq, projMap_comp_genMap, range_genMap]
  have hspanBnd : pivSpan echBnd.1 echBnd.2 = LinearMap.range (Pbnd.comp L) := by
    rw [hspecBnd.2, hrowsBnd_eq, projMap_comp_genMap, range_genMap]
  have hrFull : Module.finrank (ZMod 2) (LinearMap.range L) = rFull := by
    rw [← hspanFull, finrank_pivSpan echFull.1 echFull.2 hspecFull.1]
  have hrAct : Module.finrank (ZMod 2) (LinearMap.range (Pact.comp L)) = rAct := by
    rw [← hspanAct, finrank_pivSpan echAct.1 echAct.2 hspecAct.1]
  let rBnd := (Finset.univ.filter (fun c : Fin (bndSet k hk row col).card => echBnd.1 c = true)).card
  have hrBnd : Module.finrank (ZMod 2) (LinearMap.range (Pbnd.comp L)) = rBnd := by
    rw [← hspanBnd, finrank_pivSpan echBnd.1 echBnd.2 hspecBnd.1]
  have hrBnd_le_t : rBnd ≤ t := by
    have hcard_bnd : Nat.card (Set.range (fun coeff : Fin m → ZMod 2 =>
        fun member : bndSet k hk row col => key coeff (ix k hk (s + member.val.val)))) =
        Nat.card (LinearMap.range (Pbnd.comp L)) := by
      let f1 : ↥(LinearMap.range (Pbnd.comp L)) ≃
          ↥(Set.range (fun coeff : Fin m → ZMod 2 =>
            fun member : bndSet k hk row col => key coeff (ix k hk (s + member.val.val)))) :=
        { toFun := fun v =>
            ⟨fun member => (Pbnd base + v.val) (eB.symm member), by
              rcases v.2 with ⟨a, ha⟩
              refine ⟨a, ?_⟩
              funext member
              have hm : (Pbnd.comp L) a (eB.symm member) = v.val (eB.symm member) :=
                congrFun ha (eB.symm member)
              have hval : (eB (eB.symm member)).val = member.val :=
                congrArg Subtype.val (eB.apply_symm_apply member)
              have h1 : (Pbnd.comp L) a (eB.symm member) = L a (ix k hk (s + member.val.val)) := by
                change L a (ix k hk (s + (eB (eB.symm member)).val.val)) = _
                rw [hval]
              have h2 : Pbnd base (eB.symm member) = base (ix k hk (s + member.val.val)) := by
                change base (ix k hk (s + (eB (eB.symm member)).val.val)) = _
                rw [hval]
              dsimp only
              rw [Pi.add_apply, ← hm, h1, h2, hkey_eq, Pi.add_apply]⟩,
          invFun := fun y =>
            ⟨fun c => y.val (eB c) - Pbnd base c, by
              rcases y.2 with ⟨a, ha⟩
              refine ⟨a, ?_⟩
              funext c
              have hc : key a (ix k hk (s + (eB c).val.val)) = y.val (eB c) := congrFun ha (eB c)
              change L a (ix k hk (s + (eB c).val.val)) = y.val (eB c) - base (ix k hk (s + (eB c).val.val))
              rw [← hc, hkey_eq, Pi.add_apply, add_sub_cancel_left]⟩,
          left_inv := fun v => by
            apply Subtype.ext; funext c
            simp [eB.symm_apply_apply]
          right_inv := fun y => by
            apply Subtype.ext; funext member
            simp [eB.apply_symm_apply] }
      exact (Nat.card_congr f1).symm
    rw [hcard_bnd, card_submodule_zmod2, hrBnd] at hprom
    have hle_q : rBnd ≤ q := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hprom
    have hle_c : rBnd ≤ (bndSet k hk row col).card := by
      have := Finset.card_le_univ (Finset.univ.filter (fun c : Fin (bndSet k hk row col).card => echBnd.1 c = true))
      simpa using this
    exact le_min hle_q hle_c
  let fRes : LinearMap.range L →ₗ[ZMod 2] (Fin (activeSet k hk row col).card → ZMod 2) :=
    Pact.domRestrict (LinearMap.range L)
  have hrange_fRes : LinearMap.range fRes = LinearMap.range (Pact.comp L) := by
    ext y
    constructor
    · rintro ⟨⟨w, a, rfl⟩, rfl⟩; exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩; exact ⟨⟨L a, a, rfl⟩, rfl⟩
  have hrnk := LinearMap.finrank_range_add_finrank_ker fRes
  rw [hrange_fRes, hrAct, hrFull] at hrnk
  have hrAct_le : rAct ≤ rFull := by omega
  have hrFull_le : rFull ≤ k := by
    have := Finset.card_le_univ (Finset.univ.filter (fun c : Fin k => echFull.1 c = true))
    simpa using this
  have hker_dim : Module.finrank (ZMod 2) (LinearMap.ker fRes) = rFull - rAct := by omega
  have hker_card : Nat.card (LinearMap.ker fRes) = 2 ^ (rFull - rAct) := by
    let gEmb : LinearMap.ker fRes →ₗ[ZMod 2] (Fin k → ZMod 2) :=
      (LinearMap.range L).subtype.comp (LinearMap.ker fRes).subtype
    let emb := LinearEquiv.ofInjective gEmb (Subtype.val_injective.comp Subtype.val_injective)
    have hcard_eq : Nat.card (LinearMap.ker fRes) = Nat.card (LinearMap.range gEmb) :=
      Nat.card_congr emb.toEquiv
    have hdim_eq : Module.finrank (ZMod 2) (LinearMap.range gEmb) =
        Module.finrank (ZMod 2) (LinearMap.ker fRes) :=
      emb.symm.finrank_eq
    rw [hcard_eq, card_submodule_zmod2, hdim_eq, hker_dim]
  have hpass_iff : ∀ w : Fin k → ZMod 2,
      (∀ p : Fin k, (row p = true → run 1 1 0 w u cr (ix k hk (s + p.val + 2)) = 0) ∧
                    (col p = true → run 2 3 4 w v cc (ix k hk (s + p.val + 5)) = 0)) ↔
      passAll k s hk row col (vecToB u) (vecToB v) (vecToB cr) (vecToB cc) (shiftB k s hk (vecToB w)) = true := by
    intro w
    rw [passAll_iff]
    refine forall_congr' fun p => and_congr ?_ ?_
    · refine imp_congr_right fun _ => ?_
      have h1 : probeRowB k s hk (vecToB u) (vecToB cr) (shiftB k s hk (vecToB w)) p =
          z2b (run 1 1 0 w u cr (ix k hk (s + p.val + 2))) := by
        dsimp only [probeRowB]
        rw [unShift_shiftB, ← z2b_run]
      rw [h1]
      simp [z2b]
    · refine imp_congr_right fun _ => ?_
      have h1 : probeColB k s hk (vecToB v) (vecToB cc) (shiftB k s hk (vecToB w)) p =
          z2b (run 2 3 4 w v cc (ix k hk (s + p.val + 5))) := by
        dsimp only [probeColB]
        rw [unShift_shiftB, ← z2b_run]
      rw [h1]
      simp [z2b]
  let PassPred : (Fin k → ZMod 2) → Prop := fun w =>
    ∀ p : Fin k, (row p = true → run 1 1 0 w u cr (ix k hk (s + p.val + 2)) = 0) ∧
                 (col p = true → run 2 3 4 w v cc (ix k hk (s + p.val + 5)) = 0)
  have hPass_of_Pact : ∀ w1 w2 : Fin k → ZMod 2, Pact w1 = Pact w2 → (PassPred w1 ↔ PassPred w2) := by
    intro w1 w2 hEq
    dsimp only [PassPred]
    rw [hpass_iff w1, hpass_iff w2]
    have hagr : ∀ j : Fin k,
        (∃ p : Fin k, ∃ e : Fin 7, ix k hk (p.val + e.val) = j ∧ ((row p = true ∧ e.val ≤ 4) ∨ col p = true)) →
        shiftB k s hk (vecToB w1) j = shiftB k s hk (vecToB w2) j := by
      intro j hj
      have hjA : j ∈ activeSet k hk row col := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
      let c := eA.symm ⟨j, hjA⟩
      have hc := congrFun hEq c
      have hval : (eA c).val = j := congrArg Subtype.val (eA.apply_symm_apply ⟨j, hjA⟩)
      simp only [Pact, projMap, LinearMap.coe_mk, AddHom.coe_mk, hval] at hc
      simp [shiftB, vecToB, hc]
    rw [passAll_depends_active k s hk row col (vecToB u) (vecToB v) (vecToB cr) (vecToB cc)
      (shiftB k s hk (vecToB w1)) (shiftB k s hk (vecToB w2)) hagr]
  let Sact := { y : Fin (activeSet k hk row col).card → ZMod 2 //
    ∃ w : Fin k → ZMod 2, w ∈ Set.range key ∧ Pact w = y ∧ PassPred w }
  let Smask := { mask : Fin (2 ^ t) //
    maskFlag k s hk row col q baseAct baseBnd echAct.1 echAct.2 compBnd.1 compBnd.2
      (vecToB u) (vecToB v) (vecToB cr) (vecToB cc) mask = true }
  have hbij := evalMask_bijection (t := t) echBnd.1 echBnd.2 hspecBnd.1 hrBnd_le_t baseBnd
  dsimp only at hbij
  let reconOf : Fin (2 ^ t) → Fin k → Bool := fun mask =>
    let bVec := evalMask baseBnd compBnd.2 mask
    let β : Fin k → Bool := fun j =>
      if hj : j ∈ bndSet k hk row col then bVec (eB.symm ⟨j, hj⟩) else false
    reconstruct k s hk row col (vecToB u) (vecToB v) (vecToB cr) (vecToB cc) β
  let toAct : Fin (2 ^ t) → Fin (activeSet k hk row col).card → ZMod 2 :=
    fun mask c => b2z (reconOf mask (eA c).val)
  have hbaseAct_z : vecToZ baseAct = Pact base := by
    funext c; exact b2z_z2b _
  have hbaseBnd_z : vecToZ baseBnd = Pbnd base := by
    funext c; exact b2z_z2b _
  have hflag_mem : ∀ mask : Fin (2 ^ t),
      maskFlag k s hk row col q baseAct baseBnd echAct.1 echAct.2 compBnd.1 compBnd.2
        (vecToB u) (vecToB v) (vecToB cr) (vecToB cc) mask = true →
      ∃ w : Fin k → ZMod 2, w ∈ Set.range key ∧ Pact w = toAct mask ∧ PassPred w := by
    intro mask hfl
    simp only [maskFlag, Bool.and_eq_true] at hfl
    rcases hfl with ⟨⟨hvm, hokPass⟩, hokMem⟩
    simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.not_eq_true'] at hokMem
    have hmemSpan := (reduceVec_eq_false_iff echAct.1 echAct.2 hspecAct.1 _).mp hokMem
    rw [hspanAct] at hmemSpan
    rcases hmemSpan with ⟨a, ha⟩
    refine ⟨key a, ⟨a, rfl⟩, ?_, ?_⟩
    · funext c
      have hc := congrFun ha c
      simp only [LinearMap.comp_apply, vecToZ, b2z_xor] at hc
      have hsub : b2z (reconOf mask (eA c).val) + b2z (baseAct c) = Pact (L a) c := by
        simpa [reconOf, eA, eB, compBnd] using hc.symm
      have hba : b2z (baseAct c) = Pact base c := congrFun hbaseAct_z c
      have hka : Pact (key a) c = Pact base c + Pact (L a) c := by
        rw [hkey_eq, map_add, Pi.add_apply]
      rw [hka, ← hsub, hba]
      have h2 := zmod2_add_self (Pact base c)
      calc Pact base c + (b2z (reconOf mask (eA c).val) + Pact base c)
          = b2z (reconOf mask (eA c).val) + (Pact base c + Pact base c) := by ring
        _ = toAct mask c := by rw [h2, add_zero]
    · dsimp only [PassPred]
      rw [hpass_iff]
      have hagr : ∀ j : Fin k,
          (∃ p : Fin k, ∃ e : Fin 7, ix k hk (p.val + e.val) = j ∧ ((row p = true ∧ e.val ≤ 4) ∨ col p = true)) →
          shiftB k s hk (vecToB (key a)) j = reconOf mask j := by
        intro j hj
        have hjA : j ∈ activeSet k hk row col := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
        let c := eA.symm ⟨j, hjA⟩
        have hval : (eA c).val = j := congrArg Subtype.val (eA.apply_symm_apply ⟨j, hjA⟩)
        have hc := congrFun ha c
        simp only [LinearMap.comp_apply, vecToZ, b2z_xor] at hc
        have hsub : b2z (reconOf mask (eA c).val) + b2z (baseAct c) = Pact (L a) c := by
          simpa [reconOf, eA, eB, compBnd] using hc.symm
        have hba : b2z (baseAct c) = Pact base c := congrFun hbaseAct_z c
        have hka : Pact (key a) c = Pact base c + Pact (L a) c := by
          rw [hkey_eq, map_add, Pi.add_apply]
        have hzeq : Pact (key a) c = b2z (reconOf mask (eA c).val) := by
          rw [hka, ← hsub, hba]
          have h2 := zmod2_add_self (Pact base c)
          calc Pact base c + (b2z (reconOf mask (eA c).val) + Pact base c)
              = b2z (reconOf mask (eA c).val) + (Pact base c + Pact base c) := by ring
            _ = b2z (reconOf mask (eA c).val) := by rw [h2, add_zero]
        simp only [Pact, projMap, LinearMap.coe_mk, AddHom.coe_mk, hval] at hzeq
        change z2b (key a (ix k hk (s + j.val))) = reconOf mask j
        rw [hzeq, z2b_b2z]
      rw [passAll_depends_active k s hk row col (vecToB u) (vecToB v) (vecToB cr) (vecToB cc)
        (shiftB k s hk (vecToB (key a))) (reconOf mask) hagr]
      exact hokPass
  have htoAct_inj : ∀ m1 m2 : Smask, toAct m1.val = toAct m2.val → m1 = m2 := by
    intro m1 m2 heq
    apply Subtype.ext
    have hvm1 : validMask compBnd.1 m1.val = true := by
      have h := m1.2; simp only [maskFlag, Bool.and_eq_true] at h; exact h.1.1
    have hvm2 : validMask compBnd.1 m2.val = true := by
      have h := m2.2; simp only [maskFlag, Bool.and_eq_true] at h; exact h.1.1
    refine hbij.2.1 m1.val m2.val hvm1 hvm2 ?_
    funext cB
    let j := (eB cB).val
    have hjB : j ∈ bndSet k hk row col := (eB cB).2
    have hjA : j ∈ activeSet k hk row col := (Finset.mem_sdiff.mp hjB).1
    have hjNP : ¬((row j = true ∧ j.val + 4 < k) ∨ (col j = true ∧ j.val + 6 < k)) := by
      intro hp
      exact (Finset.mem_sdiff.mp hjB).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hp⟩)
    let cA := eA.symm ⟨j, hjA⟩
    have hvalA : (eA cA).val = j := congrArg Subtype.val (eA.apply_symm_apply ⟨j, hjA⟩)
    have h1 := congrFun heq cA
    dsimp only [toAct] at h1
    rw [hvalA] at h1
    have hb1 := b2z_inj h1
    have hr1 : reconOf m1.val j = evalMask baseBnd compBnd.2 m1.val cB := by
      dsimp only [reconOf, reconstruct]
      rw [reconstruct_preserves_nonpiv k s hk row col _ _ _ _ _ j hjNP k]
      simp only [hjB, ↓reduceDIte]
      have : eB.symm ⟨j, hjB⟩ = cB := eB.symm_apply_apply cB
      rw [this]
    have hr2 : reconOf m2.val j = evalMask baseBnd compBnd.2 m2.val cB := by
      dsimp only [reconOf, reconstruct]
      rw [reconstruct_preserves_nonpiv k s hk row col _ _ _ _ _ j hjNP k]
      simp only [hjB, ↓reduceDIte]
      have : eB.symm ⟨j, hjB⟩ = cB := eB.symm_apply_apply cB
      rw [this]
    rw [← hr1, ← hr2, hb1]
  have htoAct_surj : ∀ y : Sact, ∃ m : Smask, toAct m.val = y.val := by
    intro y
    rcases y.2 with ⟨w, ⟨a, rfl⟩, hPact, hPass⟩
    have hvBnd_mem : Pbnd (key a) - vecToZ baseBnd ∈ pivSpan echBnd.1 echBnd.2 := by
      rw [hspanBnd, hbaseBnd_z, hkey_eq, map_add, add_sub_cancel_left]
      exact ⟨a, rfl⟩
    obtain ⟨mask, hvm, heval⟩ := hbij.2.2 (Pbnd (key a)) hvBnd_mem
    have hαTrue_pass := (hpass_iff (key a)).mp hPass
    have hrecon_eq : ∀ j : Fin k, j ∈ activeSet k hk row col →
        reconOf mask j = shiftB k s hk (vecToB (key a)) j := by
      intro j hjA
      have hjAct := (Finset.mem_filter.mp hjA).2
      refine reconstruct_eq_of_pass k s hk row col (vecToB u) (vecToB v) (vecToB cr) (vecToB cc)
        _ (shiftB k s hk (vecToB (key a))) hαTrue_pass ?_ k le_rfl j (by omega) hjAct
      intro j' hj'Act hj'NP
      have hj'B : j' ∈ bndSet k hk row col :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ j', hj'Act⟩,
          fun h => hj'NP (Finset.mem_filter.mp h).2⟩
      simp only [hj'B, ↓reduceDIte]
      let cB := eB.symm ⟨j', hj'B⟩
      have hvalB : (eB cB).val = j' := congrArg Subtype.val (eB.apply_symm_apply ⟨j', hj'B⟩)
      have hc := congrFun heval cB
      simp only [vecToZ, Pbnd, projMap, LinearMap.coe_mk, AddHom.coe_mk, hvalB] at hc
      exact b2z_inj (by dsimp only [shiftB, vecToB]; rw [hc, b2z_z2b])
    have htoAct_eq : toAct mask = y.val := by
      funext c
      dsimp only [toAct]
      rw [hrecon_eq (eA c).val (eA c).2]
      simp only [shiftB, vecToB, b2z_z2b, ← hPact, Pact, projMap, LinearMap.coe_mk, AddHom.coe_mk]
    have hokPass : passAll k s hk row col (vecToB u) (vecToB v) (vecToB cr) (vecToB cc) (reconOf mask) = true := by
      rw [passAll_depends_active k s hk row col (vecToB u) (vecToB v) (vecToB cr) (vecToB cc)
        (reconOf mask) (shiftB k s hk (vecToB (key a)))
        (fun j hj => hrecon_eq j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩))]
      exact hαTrue_pass
    have hokMem : (List.finRange (activeSet k hk row col).card).all
        (fun c => !reduceVec echAct.1 echAct.2 (fun c0 => xor (reconOf mask (eA c0).val) (baseAct c0)) c) = true := by
      simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.not_eq_true']
      rw [reduceVec_eq_false_iff echAct.1 echAct.2 hspecAct.1, hspanAct]
      refine ⟨a, ?_⟩
      funext c
      simp only [vecToZ, b2z_xor, LinearMap.comp_apply]
      have hc1 : b2z (reconOf mask (eA c).val) = Pact (key a) c := by
        rw [hrecon_eq (eA c).val (eA c).2]
        simp [shiftB, vecToB, b2z_z2b, Pact, projMap]
      have hc2 : b2z (baseAct c) = Pact base c := congrFun hbaseAct_z c
      rw [hc1, hc2, hkey_eq, map_add, Pi.add_apply]
      have h2 := zmod2_add_self (Pact base c)
      calc Pact (L a) c = Pact (L a) c + (Pact base c + Pact base c) := by rw [h2, add_zero]
        _ = Pact base c + Pact (L a) c + Pact base c := by ring
    have hfl : maskFlag k s hk row col q baseAct baseBnd echAct.1 echAct.2 compBnd.1 compBnd.2
        (vecToB u) (vecToB v) (vecToB cr) (vecToB cc) mask = true := by
      simp only [maskFlag, Bool.and_eq_true]
      exact ⟨⟨hvm, hokPass⟩, hokMem⟩
    exact ⟨⟨mask, hfl⟩, htoAct_eq⟩
  have hSact_card : Nat.card Sact = M := by
    let fEquiv : Smask ≃ Sact :=
      Equiv.ofBijective (fun m => ⟨toAct m.val, hflag_mem m.val m.2⟩)
        ⟨fun m1 m2 h => htoAct_inj m1 m2 (congrArg Subtype.val h),
         fun y => by obtain ⟨m, hm⟩ := htoAct_surj y; exact ⟨m, Subtype.ext hm⟩⟩
    rw [← Nat.card_congr fEquiv, Nat.card_eq_fintype_card, Fintype.card_subtype]
  let Spass := { w : Fin k → ZMod 2 // w ∈ Set.range key ∧ PassPred w }
  have hcount_eq : count = Nat.card Spass := rfl
  let fib : Sact → Type := fun y => { w : Fin k → ZMod 2 // w ∈ Set.range key ∧ Pact w = y.val }
  have hfib_card : ∀ y : Sact, Nat.card (fib y) = 2 ^ (rFull - rAct) := by
    intro y
    rcases y.2 with ⟨w0, ⟨a0, rfl⟩, hP0, _⟩
    let eFib : ↥(LinearMap.ker fRes) ≃ fib y :=
      { toFun := fun v =>
          ⟨key a0 + v.val.val, by
            rcases v.val.2 with ⟨a1, ha1⟩
            refine ⟨⟨a0 + a1, ?_⟩, ?_⟩
            · rw [hkey_eq, hkey_eq, map_add, ← ha1]; abel
            · rw [map_add, hP0]
              have hv0 : Pact v.val.val = 0 := v.2
              rw [hv0, add_zero]⟩,
        invFun := fun z =>
          ⟨⟨z.val - key a0, by
            rcases z.2.1 with ⟨a1, ha1⟩
            refine ⟨a1 - a0, ?_⟩
            rw [← ha1, hkey_eq, hkey_eq, map_sub]; abel⟩, by
            change Pact (z.val - key a0) = 0
            rw [map_sub, z.2.2, hP0, sub_self]⟩,
        left_inv := fun v => by
          apply Subtype.ext; apply Subtype.ext
          change key a0 + v.val.val - key a0 = v.val.val
          abel
        right_inv := fun z => by
          apply Subtype.ext
          change key a0 + (z.val - key a0) = z.val
          abel }
    rw [← Nat.card_congr eFib, hker_card]
  have hSpass_equiv : Spass ≃ Σ y : Sact, fib y :=
    { toFun := fun w => ⟨⟨Pact w.val, ⟨w.val, w.2.1, rfl, w.2.2⟩⟩, ⟨w.val, w.2.1, rfl⟩⟩,
      invFun := fun p => ⟨p.2.val, p.2.2.1, by
        rcases p.1.2 with ⟨w0, _, hP0, hPass0⟩
        exact (hPass_of_Pact p.2.val w0 (p.2.2.2.trans hP0.symm)).mpr hPass0⟩,
      left_inv := fun _ => rfl,
      right_inv := fun ⟨y, w⟩ => by
        rcases y with ⟨yv, hy⟩
        rcases w with ⟨wv, hw1, hw2⟩
        dsimp only at hw2
        subst hw2
        rfl }
  have hSpass_card : Nat.card Spass = M * 2 ^ (rFull - rAct) := by
    let _ : Fintype Sact := Fintype.ofFinite Sact
    let _ : ∀ y : Sact, Fintype (fib y) := fun y => Fintype.ofFinite (fib y)
    rw [Nat.card_congr hSpass_equiv, Nat.card_eq_fintype_card, Fintype.card_sigma]
    have hsum : ∑ y : Sact, Fintype.card (fib y) = ∑ _y : Sact, 2 ^ (rFull - rAct) := by
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [← Nat.card_eq_fintype_card, hfib_card y]
    rw [hsum, Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card, hSact_card]
  have hM_lt : M < 2 ^ (k + 1) := by
    have hSpass_le : Nat.card Spass ≤ 2 ^ k := by
      rw [Nat.card_eq_fintype_card]
      refine le_trans (Fintype.card_subtype_le _) ?_
      rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    have hpow_pos : 1 ≤ 2 ^ (rFull - rAct) := Nat.one_le_two_pow
    have hM_le : M ≤ M * 2 ^ (rFull - rAct) := Nat.le_mul_of_pos_right M (by omega)
    have h2k : 2 ^ k < 2 ^ (k + 1) := by
      rw [pow_succ]; have : 0 < 2 ^ k := Nat.two_pow_pos k; omega
    omega
  exact ⟨hrAct_le, hrFull_le, hM_lt, hcount_eq.trans hSpass_card⟩


private lemma getD_append_left {α : Type*} (l1 l2 : List α) (i : Nat) (d : α) (hi : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma getD_append_right {α : Type*} (l1 l2 : List α) (i : Nat) (d : α) (hi : l1.length ≤ i) :
    (l1 ++ l2).getD i d = l2.getD (i - l1.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

private lemma flatten_pack_len {k : Nat} :
    ∀ {m : Nat} (gen : Fin m → Fin k → ZMod 2),
      (List.ofFn (fun g : Fin m => List.ofFn (fun j : Fin k => z2b (gen g j)))).flatten.length = m * k
  | 0, _ => by simp
  | m + 1, gen => by
      rw [List.ofFn_succ, List.flatten_cons, List.length_append, List.length_ofFn,
        flatten_pack_len (fun g => gen g.succ)]
      ring

private lemma flatten_pack_getD {k : Nat} :
    ∀ {m : Nat} (gen : Fin m → Fin k → ZMod 2) (g : Fin m) (j : Fin k),
      (List.ofFn (fun g0 : Fin m => List.ofFn (fun j0 : Fin k => z2b (gen g0 j0)))).flatten.getD
        (g.val * k + j.val) false = z2b (gen g j)
  | 0, _, g, _ => Fin.elim0 g
  | m + 1, gen, g, j => by
      rw [List.ofFn_succ, List.flatten_cons]
      refine Fin.cases ?_ ?_ g
      · have hlt : (0 : Fin (m + 1)).val * k + j.val <
            (List.ofFn (fun j0 : Fin k => z2b (gen 0 j0))).length := by
          rw [List.length_ofFn]; simp
        rw [getD_append_left _ _ _ _ hlt]
        simp [List.getD_eq_getElem?_getD, j.isLt]
      · intro g'
        have hge : (List.ofFn (fun j0 : Fin k => z2b (gen 0 j0))).length ≤
            g'.succ.val * k + j.val := by
          rw [List.length_ofFn]
          simp only [Fin.val_succ, Nat.succ_mul]
          omega
        rw [getD_append_right _ _ _ _ hge, List.length_ofFn]
        have hsub : g'.succ.val * k + j.val - k = g'.val * k + j.val := by
          simp only [Fin.val_succ, Nat.succ_mul]; omega
        rw [hsub]
        exact flatten_pack_getD (fun g0 => gen g0.succ) g' j

private lemma bits_spec {k m : Nat} (base : Fin k → ZMod 2) (gen : Fin m → Fin k → ZMod 2)
    (u v cr cc : Fin k → ZMod 2) :
    let pack := fun (word : Fin k → ZMod 2) => List.ofFn (fun j : Fin k => decide (word j ≠ 0))
    let bits := pack base ++ (List.ofFn (fun g => pack (gen g))).flatten ++
      pack u ++ pack v ++ pack cr ++ pack cc
    bits.length = (m + 5) * k ∧
    (∀ j : Fin k, bits.getD j.val false = z2b (base j)) ∧
    (∀ (g : Fin m) (j : Fin k), bits.getD ((g.val + 1) * k + j.val) false = z2b (gen g j)) ∧
    (∀ j : Fin k, bits.getD ((m + 1) * k + j.val) false = z2b (u j)) ∧
    (∀ j : Fin k, bits.getD ((m + 2) * k + j.val) false = z2b (v j)) ∧
    (∀ j : Fin k, bits.getD ((m + 3) * k + j.val) false = z2b (cr j)) ∧
    (∀ j : Fin k, bits.getD ((m + 4) * k + j.val) false = z2b (cc j)) := by
  intro pack bits
  have hfl : (List.ofFn (fun g => pack (gen g))).flatten.length = m * k := flatten_pack_len gen
  have hp : ∀ w : Fin k → ZMod 2, (pack w).length = k := fun _ => List.length_ofFn
  have hgetP : ∀ (w : Fin k → ZMod 2) (j : Fin k), (pack w).getD j.val false = z2b (w j) := by
    intro w j
    simp [pack, z2b, List.getD_eq_getElem?_getD, j.isLt]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [bits]
    simp only [List.length_append, hp, hfl]
    ring
  · intro j
    dsimp only [bits]
    have h1 : j.val < (pack base ++ (List.ofFn (fun g => pack (gen g))).flatten ++ pack u ++ pack v ++ pack cr).length := by
      simp only [List.length_append, hp, hfl]; omega
    have h2 : j.val < (pack base ++ (List.ofFn (fun g => pack (gen g))).flatten ++ pack u ++ pack v).length := by
      simp only [List.length_append, hp, hfl]; omega
    have h3 : j.val < (pack base ++ (List.ofFn (fun g => pack (gen g))).flatten ++ pack u).length := by
      simp only [List.length_append, hp, hfl]; omega
    have h4 : j.val < (pack base ++ (List.ofFn (fun g => pack (gen g))).flatten).length := by
      simp only [List.length_append, hp, hfl]; omega
    have h5 : j.val < (pack base).length := by rw [hp]; exact j.isLt
    rw [getD_append_left _ _ _ _ h1, getD_append_left _ _ _ _ h2, getD_append_left _ _ _ _ h3,
      getD_append_left _ _ _ _ h4, getD_append_left _ _ _ _ h5]
    exact hgetP base j
  · intro g j
    dsimp only [bits]
    have hlt_mk : g.val * k + j.val < m * k := by
      have : (g.val + 1) * k ≤ m * k := Nat.mul_le_mul_right k (by omega)
      rw [Nat.succ_mul] at this
      omega
    have h1 : (g.val + 1) * k + j.val < (pack base ++ (List.ofFn (fun g => pack (gen g))).flatten ++ pack u ++ pack v ++ pack cr).length := by
      simp only [List.length_append, hp, hfl]; rw [Nat.succ_mul]; omega
    have h2 : (g.val + 1) * k + j.val < (pack base ++ (List.ofFn (fun g => pack (gen g))).flatten ++ pack u ++ pack v).length := by
      simp only [List.length_append, hp, hfl]; rw [Nat.succ_mul]; omega
    have h3 : (g.val + 1) * k + j.val < (pack base ++ (List.ofFn (fun g => pack (gen g))).flatten ++ pack u).length := by
      simp only [List.length_append, hp, hfl]; rw [Nat.succ_mul]; omega
    have h4 : (g.val + 1) * k + j.val < (pack base ++ (List.ofFn (fun g => pack (gen g))).flatten).length := by
      simp only [List.length_append, hp, hfl]; rw [Nat.succ_mul]; omega
    have h5 : (pack base).length ≤ (g.val + 1) * k + j.val := by
      rw [hp, Nat.succ_mul]; omega
    rw [getD_append_left _ _ _ _ h1, getD_append_left _ _ _ _ h2, getD_append_left _ _ _ _ h3,
      getD_append_left _ _ _ _ h4, getD_append_right _ _ _ _ h5, hp]
    have hsub : (g.val + 1) * k + j.val - k = g.val * k + j.val := by rw [Nat.succ_mul]; omega
    rw [hsub]
    exact flatten_pack_getD gen g j
  · intro j
    dsimp only [bits]
    have h1 : (m + 1) * k + j.val < (pack base ++ (List.ofFn (fun g => pack (gen g))).flatten ++ pack u ++ pack v ++ pack cr).length := by
      simp only [List.length_append, hp, hfl]; rw [Nat.succ_mul]; omega
    have h2 : (m + 1) * k + j.val < (pack base ++ (List.ofFn (fun g => pack (gen g))).flatten ++ pack u ++ pack v).length := by
      simp only [List.length_append, hp, hfl]; rw [Nat.succ_mul]; omega
    have h3 : (m + 1) * k + j.val < (pack base ++ (List.ofFn (fun g => pack (gen g))).flatten ++ pack u).length := by
      simp only [List.length_append, hp, hfl]; rw [Nat.succ_mul]; omega
    have h4 : (pack base ++ (List.ofFn (fun g => pack (gen g))).flatten).length ≤ (m + 1) * k + j.val := by
      simp only [List.length_append, hp, hfl]; rw [Nat.succ_mul]; omega
    rw [getD_append_left _ _ _ _ h1, getD_append_left _ _ _ _ h2, getD_append_left _ _ _ _ h3,
      getD_append_right _ _ _ _ h4]
    have hsub : (m + 1) * k + j.val - (pack base ++ (List.ofFn (fun g => pack (gen g))).flatten).length = j.val := by
      simp only [List.length_append, hp, hfl]; rw [Nat.succ_mul]; omega
    rw [hsub]
    exact hgetP u j
  · intro j
    dsimp only [bits]
    have h1 : (m + 2) * k + j.val < (pack base ++ (List.ofFn (fun g => pack (gen g))).flatten ++ pack u ++ pack v ++ pack cr).length := by
      simp only [List.length_append, hp, hfl]; ring_nf; omega
    have h2 : (m + 2) * k + j.val < (pack base ++ (List.ofFn (fun g => pack (gen g))).flatten ++ pack u ++ pack v).length := by
      simp only [List.length_append, hp, hfl]; ring_nf; omega
    have h3 : (pack base ++ (List.ofFn (fun g => pack (gen g))).flatten ++ pack u).length ≤ (m + 2) * k + j.val := by
      simp only [List.length_append, hp, hfl]; ring_nf; omega
    rw [getD_append_left _ _ _ _ h1, getD_append_left _ _ _ _ h2, getD_append_right _ _ _ _ h3]
    have hsub : (m + 2) * k + j.val - (pack base ++ (List.ofFn (fun g => pack (gen g))).flatten ++ pack u).length = j.val := by
      simp only [List.length_append, hp, hfl]; ring_nf; omega
    rw [hsub]
    exact hgetP v j
  · intro j
    dsimp only [bits]
    have h1 : (m + 3) * k + j.val < (pack base ++ (List.ofFn (fun g => pack (gen g))).flatten ++ pack u ++ pack v ++ pack cr).length := by
      simp only [List.length_append, hp, hfl]; ring_nf; omega
    have h2 : (pack base ++ (List.ofFn (fun g => pack (gen g))).flatten ++ pack u ++ pack v).length ≤ (m + 3) * k + j.val := by
      simp only [List.length_append, hp, hfl]; ring_nf; omega
    rw [getD_append_left _ _ _ _ h1, getD_append_right _ _ _ _ h2]
    have hsub : (m + 3) * k + j.val - (pack base ++ (List.ofFn (fun g => pack (gen g))).flatten ++ pack u ++ pack v).length = j.val := by
      simp only [List.length_append, hp, hfl]; ring_nf; omega
    rw [hsub]
    exact hgetP cr j
  · intro j
    dsimp only [bits]
    have h1 : (pack base ++ (List.ofFn (fun g => pack (gen g))).flatten ++ pack u ++ pack v ++ pack cr).length ≤ (m + 4) * k + j.val := by
      simp only [List.length_append, hp, hfl]; ring_nf; omega
    rw [getD_append_right _ _ _ _ h1]
    have hsub : (m + 4) * k + j.val - (pack base ++ (List.ofFn (fun g => pack (gen g))).flatten ++ pack u ++ pack v ++ pack cr).length = j.val := by
      simp only [List.length_append, hp, hfl]; ring_nf; omega
    rw [hsub]
    exact hgetP cc j

private abbrev CGate := PEqualNP.CircuitLowerBounds.Gate
private abbrev CGateOp := PEqualNP.CircuitLowerBounds.GateOp
private abbrev CCircuit := PEqualNP.CircuitLowerBounds.Circuit

private def evalWires (gs : List CGate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private def WF (n : Nat) (gs : List CGate) : Prop :=
  PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩ ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n ⟨gs, 0⟩

private def Ext (gs1 gs2 : List CGate) : Prop :=
  ∃ suf, gs2 = gs1 ++ suf

private def Val (n : Nat) (gs : List CGate) (x : List Bool) (w : Nat) (b : Bool) : Prop :=
  w < n + gs.length ∧ (evalWires gs x).getD w false = b

private lemma evalWires_len (gs : List CGate) :
    ∀ x : List Bool, (evalWires gs x).length = x.length + gs.length := by
  induction gs with
  | nil => intro x; simp [evalWires]
  | cons g gs ih =>
      intro x
      simp only [evalWires, List.foldl_cons]
      change (evalWires gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])).length = _
      rw [ih, List.length_append, List.length_singleton, List.length_cons]
      omega

private lemma evalWires_append (gs1 gs2 : List CGate) (x : List Bool) :
    evalWires (gs1 ++ gs2) x = evalWires gs2 (evalWires gs1 x) :=
  List.foldl_append

private lemma evalWires_prefix (gs : List CGate) :
    ∀ (x : List Bool) (i : Nat), i < x.length → (evalWires gs x).getD i false = x.getD i false := by
  induction gs with
  | nil => intro x i _; rfl
  | cons g gs ih =>
      intro x i hi
      simp only [evalWires, List.foldl_cons]
      let x' := x ++ [g.op.eval (g.inputs.map fun idx => x.getD idx false)]
      have hi' : i < x'.length := by simp only [x', List.length_append, List.length_singleton]; omega
      change (evalWires gs x').getD i false = x.getD i false
      rw [ih x' i hi']
      exact getD_append_left _ _ _ _ hi

private lemma Ext.refl (gs : List CGate) : Ext gs gs := ⟨[], by simp⟩

private lemma Ext.trans {a b c : List CGate} (h1 : Ext a b) (h2 : Ext b c) : Ext a c := by
  rcases h1 with ⟨s1, rfl⟩
  rcases h2 with ⟨s2, rfl⟩
  exact ⟨s1 ++ s2, by rw [List.append_assoc]⟩

private lemma Ext.len_le {a b : List CGate} (h : Ext a b) : a.length ≤ b.length := by
  rcases h with ⟨s, rfl⟩
  simp

private lemma Val.mono {n : Nat} {gs1 gs2 : List CGate} {x : List Bool} {w : Nat} {b : Bool}
    (hx : x.length = n) (hext : Ext gs1 gs2) (hv : Val n gs1 x w b) : Val n gs2 x w b := by
  rcases hext with ⟨suf, rfl⟩
  have h1 := hv.1
  refine ⟨by simp only [List.length_append]; omega, ?_⟩
  rw [evalWires_append, evalWires_prefix suf (evalWires gs1 x) w (by rw [evalWires_len, hx]; exact h1)]
  exact hv.2

private def pushGate (n : Nat) (gs : List CGate) (g : CGate) : List CGate × Nat :=
  (gs ++ [g], n + gs.length)

private lemma pushGate_spec {n : Nat} {gs : List CGate} (g : CGate)
    (hwf : WF n gs)
    (hop : g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set CGateOp))
    (hlen : g.inputs.length ≤ 2)
    (hback : ∀ i ∈ g.inputs, i < n + gs.length) :
    WF n (pushGate n gs g).1 ∧ Ext gs (pushGate n gs g).1 ∧
    (pushGate n gs g).1.length = gs.length + 1 ∧
    (pushGate n gs g).2 < n + (pushGate n gs g).1.length ∧
    ∀ x : List Bool, x.length = n →
      Val n (pushGate n gs g).1 x (pushGate n gs g).2
        (g.op.eval (g.inputs.map fun i => (evalWires gs x).getD i false)) := by
  refine ⟨⟨?_, ?_⟩, ⟨[g], rfl⟩, by simp [pushGate], by simp [pushGate], ?_⟩
  · intro g0 hg0
    simp only [pushGate, List.mem_append, List.mem_singleton] at hg0
    rcases hg0 with hg0 | rfl
    · exact hwf.1 g0 hg0
    · exact ⟨hop, hlen⟩
  · intro j hj i hi
    dsimp only [pushGate] at hj hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · have hg : PEqualNP.MetaComplexity.NestedCover.gateAt ⟨gs ++ [g], 0⟩ j =
          PEqualNP.MetaComplexity.NestedCover.gateAt ⟨gs, 0⟩ j := by
        simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, getD_append_left _ _ _ _ hlt]
      rw [hg] at hi
      exact hwf.2 j hlt i hi
    · have heq : j = gs.length := by omega
      subst heq
      have hg : PEqualNP.MetaComplexity.NestedCover.gateAt ⟨gs ++ [g], 0⟩ gs.length = g := by
        simp only [PEqualNP.MetaComplexity.NestedCover.gateAt]
        rw [getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
        rfl
      rw [hg] at hi
      exact hback i hi
  · intro x hx
    refine ⟨by simp [pushGate], ?_⟩
    change (evalWires (gs ++ [g]) x).getD (n + gs.length) false = _
    rw [evalWires_append]
    change (evalWires gs x ++ [g.op.eval (g.inputs.map fun i => (evalWires gs x).getD i false)]).getD
      (n + gs.length) false = _
    have hlen_w : (evalWires gs x).length = n + gs.length := by rw [evalWires_len, hx]
    rw [getD_append_right _ _ _ _ (by omega), hlen_w, Nat.sub_self]
    rfl

private def gConst0 (n : Nat) (gs : List CGate) : List CGate × Nat :=
  pushGate n gs ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩

private def gConst1 (n : Nat) (gs : List CGate) : List CGate × Nat :=
  pushGate n gs ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩

private def gNot (n : Nat) (gs : List CGate) (a : Nat) : List CGate × Nat :=
  pushGate n gs ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [a]⟩

private def gAnd (n : Nat) (gs : List CGate) (a b : Nat) : List CGate × Nat :=
  pushGate n gs ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩

private def gOr (n : Nat) (gs : List CGate) (a b : Nat) : List CGate × Nat :=
  pushGate n gs ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, b]⟩

private def gXor (n : Nat) (gs : List CGate) (a b : Nat) : List CGate × Nat :=
  let r1 := gOr n gs a b
  let r2 := gAnd n r1.1 a b
  let r3 := gNot n r2.1 r2.2
  gAnd n r3.1 r1.2 r3.2

private def gMux (n : Nat) (gs : List CGate) (sel t f : Nat) : List CGate × Nat :=
  let r1 := gNot n gs sel
  let r2 := gAnd n r1.1 sel t
  let r3 := gAnd n r2.1 r1.2 f
  gOr n r3.1 r2.2 r3.2

private lemma gConst0_spec {n : Nat} {gs : List CGate} (hwf : WF n gs) :
    WF n (gConst0 n gs).1 ∧ Ext gs (gConst0 n gs).1 ∧
    (gConst0 n gs).1.length = gs.length + 1 ∧ (gConst0 n gs).2 < n + (gConst0 n gs).1.length ∧
    ∀ x : List Bool, x.length = n → Val n (gConst0 n gs).1 x (gConst0 n gs).2 false := by
  have h := pushGate_spec ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ hwf (by simp) (by simp) (by simp)
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun x hx => h.2.2.2.2 x hx⟩

private lemma gConst1_spec {n : Nat} {gs : List CGate} (hwf : WF n gs) :
    WF n (gConst1 n gs).1 ∧ Ext gs (gConst1 n gs).1 ∧
    (gConst1 n gs).1.length = gs.length + 1 ∧ (gConst1 n gs).2 < n + (gConst1 n gs).1.length ∧
    ∀ x : List Bool, x.length = n → Val n (gConst1 n gs).1 x (gConst1 n gs).2 true := by
  have h := pushGate_spec ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩ hwf (by simp) (by simp) (by simp)
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun x hx => h.2.2.2.2 x hx⟩

private lemma gNot_spec {n : Nat} {gs : List CGate} (hwf : WF n gs) (a : Nat) (ha : a < n + gs.length) :
    WF n (gNot n gs a).1 ∧ Ext gs (gNot n gs a).1 ∧
    (gNot n gs a).1.length = gs.length + 1 ∧ (gNot n gs a).2 < n + (gNot n gs a).1.length ∧
    ∀ (x : List Bool) (ba : Bool), x.length = n → Val n gs x a ba → Val n (gNot n gs a).1 x (gNot n gs a).2 (!ba) := by
  have h := pushGate_spec ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [a]⟩ hwf (by simp) (by simp)
    (by intro i hi; simp at hi; subst hi; exact ha)
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun x ba hx hva => ?_⟩
  have hv := h.2.2.2.2 x hx
  simp only [List.map_cons, List.map_nil, hva.2] at hv
  have hev : PEqualNP.CircuitLowerBounds.GateOp.not.eval [ba] = !ba := by cases ba <;> rfl
  rwa [hev] at hv

private lemma gAnd_spec {n : Nat} {gs : List CGate} (hwf : WF n gs) (a b : Nat)
    (ha : a < n + gs.length) (hb : b < n + gs.length) :
    WF n (gAnd n gs a b).1 ∧ Ext gs (gAnd n gs a b).1 ∧
    (gAnd n gs a b).1.length = gs.length + 1 ∧ (gAnd n gs a b).2 < n + (gAnd n gs a b).1.length ∧
    ∀ (x : List Bool) (ba bb : Bool), x.length = n → Val n gs x a ba → Val n gs x b bb →
      Val n (gAnd n gs a b).1 x (gAnd n gs a b).2 (ba && bb) := by
  have h := pushGate_spec ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩ hwf (by simp) (by simp)
    (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun x ba bb hx hva hvb => ?_⟩
  have hv := h.2.2.2.2 x hx
  simp only [List.map_cons, List.map_nil, hva.2, hvb.2] at hv
  have hev : PEqualNP.CircuitLowerBounds.GateOp.and.eval [ba, bb] = (ba && bb) := by cases ba <;> cases bb <;> rfl
  rwa [hev] at hv

private lemma gOr_spec {n : Nat} {gs : List CGate} (hwf : WF n gs) (a b : Nat)
    (ha : a < n + gs.length) (hb : b < n + gs.length) :
    WF n (gOr n gs a b).1 ∧ Ext gs (gOr n gs a b).1 ∧
    (gOr n gs a b).1.length = gs.length + 1 ∧ (gOr n gs a b).2 < n + (gOr n gs a b).1.length ∧
    ∀ (x : List Bool) (ba bb : Bool), x.length = n → Val n gs x a ba → Val n gs x b bb →
      Val n (gOr n gs a b).1 x (gOr n gs a b).2 (ba || bb) := by
  have h := pushGate_spec ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, b]⟩ hwf (by simp) (by simp)
    (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun x ba bb hx hva hvb => ?_⟩
  have hv := h.2.2.2.2 x hx
  simp only [List.map_cons, List.map_nil, hva.2, hvb.2] at hv
  have hev : PEqualNP.CircuitLowerBounds.GateOp.or.eval [ba, bb] = (ba || bb) := by cases ba <;> cases bb <;> rfl
  rwa [hev] at hv

private lemma gXor_spec {n : Nat} {gs : List CGate} (hwf : WF n gs) (a b : Nat)
    (ha : a < n + gs.length) (hb : b < n + gs.length) :
    WF n (gXor n gs a b).1 ∧ Ext gs (gXor n gs a b).1 ∧
    (gXor n gs a b).1.length = gs.length + 4 ∧ (gXor n gs a b).2 < n + (gXor n gs a b).1.length ∧
    ∀ (x : List Bool) (ba bb : Bool), x.length = n → Val n gs x a ba → Val n gs x b bb →
      Val n (gXor n gs a b).1 x (gXor n gs a b).2 (xor ba bb) := by
  unfold gXor
  have h1 := gOr_spec hwf a b ha hb
  set r1 := gOr n gs a b
  have h2 := gAnd_spec h1.1 a b (by omega) (by omega)
  set r2 := gAnd n r1.1 a b
  have h3 := gNot_spec h2.1 r2.2 h2.2.2.2.1
  set r3 := gNot n r2.1 r2.2
  have h4 := gAnd_spec h3.1 r1.2 r3.2 (by have := h1.2.2.2.1; omega) h3.2.2.2.1
  set r4 := gAnd n r3.1 r1.2 r3.2
  refine ⟨h4.1, h1.2.1.trans (h2.2.1.trans (h3.2.1.trans h4.2.1)), by omega, h4.2.2.2.1,
    fun x ba bb hx hva hvb => ?_⟩
  have v1 := h1.2.2.2.2 x ba bb hx hva hvb
  have v2 := h2.2.2.2.2 x ba bb hx (hva.mono hx h1.2.1) (hvb.mono hx h1.2.1)
  have v3 := h3.2.2.2.2 x (ba && bb) hx v2
  have v4 := h4.2.2.2.2 x (ba || bb) (!(ba && bb)) hx (v1.mono hx (h2.2.1.trans h3.2.1)) v3
  have heq : ((ba || bb) && !(ba && bb)) = xor ba bb := by cases ba <;> cases bb <;> rfl
  rwa [heq] at v4

private lemma gMux_spec {n : Nat} {gs : List CGate} (hwf : WF n gs) (sel t f : Nat)
    (hs : sel < n + gs.length) (ht : t < n + gs.length) (hf : f < n + gs.length) :
    WF n (gMux n gs sel t f).1 ∧ Ext gs (gMux n gs sel t f).1 ∧
    (gMux n gs sel t f).1.length = gs.length + 4 ∧ (gMux n gs sel t f).2 < n + (gMux n gs sel t f).1.length ∧
    ∀ (x : List Bool) (bs bt bf : Bool), x.length = n → Val n gs x sel bs → Val n gs x t bt → Val n gs x f bf →
      Val n (gMux n gs sel t f).1 x (gMux n gs sel t f).2 (if bs then bt else bf) := by
  unfold gMux
  have h1 := gNot_spec hwf sel hs
  set r1 := gNot n gs sel
  have h2 := gAnd_spec h1.1 sel t (by omega) (by omega)
  set r2 := gAnd n r1.1 sel t
  have h3 := gAnd_spec h2.1 r1.2 f (by have := h1.2.2.2.1; omega) (by omega)
  set r3 := gAnd n r2.1 r1.2 f
  have h4 := gOr_spec h3.1 r2.2 r3.2 (by have := h2.2.2.2.1; omega) h3.2.2.2.1
  set r4 := gOr n r3.1 r2.2 r3.2
  refine ⟨h4.1, h1.2.1.trans (h2.2.1.trans (h3.2.1.trans h4.2.1)), by omega, h4.2.2.2.1,
    fun x bs bt bf hx hvs hvt hvf => ?_⟩
  have v1 := h1.2.2.2.2 x bs hx hvs
  have v2 := h2.2.2.2.2 x bs bt hx (hvs.mono hx h1.2.1) (hvt.mono hx h1.2.1)
  have v3 := h3.2.2.2.2 x (!bs) bf hx (v1.mono hx h2.2.1) (hvf.mono hx (h1.2.1.trans h2.2.1))
  have v4 := h4.2.2.2.2 x (bs && bt) ((!bs) && bf) hx (v2.mono hx h3.2.1) v3
  have heq : ((bs && bt) || ((!bs) && bf)) = if bs then bt else bf := by cases bs <;> cases bt <;> cases bf <;> rfl
  rwa [heq] at v4

private def gCondXorVecFrom {L : Nat} (n : Nat) (gs : List CGate) (en : Nat) (a b : Fin L → Nat) :
    Nat → List CGate × (Fin L → Nat)
  | 0 => (gs, a)
  | j + 1 =>
      let r1 := gCondXorVecFrom n gs en a b j
      if hj : j < L then
        let idx : Fin L := ⟨j, hj⟩
        let r2 := gAnd n r1.1 en (b idx)
        let r3 := gXor n r2.1 (a idx) r2.2
        (r3.1, fun i => if i = idx then r3.2 else r1.2 i)
      else r1

private lemma gCondXorVecFrom_spec {L : Nat} {n : Nat} {gs : List CGate} (en : Nat) (a b : Fin L → Nat)
    (hwf : WF n gs) (hen : en < n + gs.length)
    (ha : ∀ i, a i < n + gs.length) (hb : ∀ i, b i < n + gs.length) :
    ∀ step : Nat,
      WF n (gCondXorVecFrom n gs en a b step).1 ∧ Ext gs (gCondXorVecFrom n gs en a b step).1 ∧
      (gCondXorVecFrom n gs en a b step).1.length ≤ gs.length + 5 * step ∧
      (∀ i, (gCondXorVecFrom n gs en a b step).2 i < n + (gCondXorVecFrom n gs en a b step).1.length) ∧
      ∀ (x : List Bool) (ben : Bool) (ba bb : Fin L → Bool), x.length = n →
        Val n gs x en ben → (∀ i, Val n gs x (a i) (ba i)) → (∀ i, Val n gs x (b i) (bb i)) →
        ∀ i : Fin L, Val n (gCondXorVecFrom n gs en a b step).1 x ((gCondXorVecFrom n gs en a b step).2 i)
          (if i.val < step then condXorVec ben ba bb i else ba i) := by
  intro step
  induction step with
  | zero =>
      exact ⟨hwf, Ext.refl gs, by simp [gCondXorVecFrom], ha,
        fun _ _ _ _ _ _ hva _ i => by simpa [gCondXorVecFrom] using hva i⟩
  | succ step ih =>
      rcases ih with ⟨hwf1, hext1, hlen1, hlt1, hval1⟩
      simp only [gCondXorVecFrom]
      by_cases hj : step < L
      · simp only [hj, ↓reduceDIte]
        set r1 := gCondXorVecFrom n gs en a b step
        set idx : Fin L := ⟨step, hj⟩
        have hle1 : gs.length ≤ r1.1.length := hext1.len_le
        have h2 := gAnd_spec hwf1 en (b idx) (by omega) (by have := hb idx; omega)
        set r2 := gAnd n r1.1 en (b idx)
        have h3 := gXor_spec h2.1 (a idx) r2.2 (by have := ha idx; omega) h2.2.2.2.1
        set r3 := gXor n r2.1 (a idx) r2.2
        refine ⟨h3.1, hext1.trans (h2.2.1.trans h3.2.1), by omega, ?_, ?_⟩
        · intro i
          by_cases hi : i = idx
          · simp only [hi, ↓reduceIte]; exact h3.2.2.2.1
          · simp only [hi, ↓reduceIte]; have := hlt1 i; omega
        · intro x ben ba bb hx hven hva hvb i
          by_cases hi : i = idx
          · subst hi
            simp only [↓reduceIte, idx, Nat.lt_succ_self]
            have v2 := h2.2.2.2.2 x ben (bb idx) hx (hven.mono hx hext1) ((hvb idx).mono hx hext1)
            exact h3.2.2.2.2 x (ba idx) (ben && bb idx) hx ((hva idx).mono hx (hext1.trans h2.2.1)) v2
          · simp only [hi, ↓reduceIte]
            have hne : i.val ≠ step := fun h => hi (Fin.ext h)
            have hlt_iff : i.val < step + 1 ↔ i.val < step := by omega
            simp only [hlt_iff]
            exact (hval1 x ben ba bb hx hven hva hvb i).mono hx (h2.2.1.trans h3.2.1)
      · simp only [hj, ↓reduceDIte]
        refine ⟨hwf1, hext1, by omega, hlt1, fun x ben ba bb hx hven hva hvb i => ?_⟩
        have hlt_iff : i.val < step + 1 ↔ i.val < step := by omega
        simp only [hlt_iff]
        exact hval1 x ben ba bb hx hven hva hvb i

private def gReduceFrom {L : Nat} (n : Nat) (gs : List CGate)
    (hasPiv : Fin L → Nat) (pivRow : Fin L → Fin L → Nat) (cur : Fin L → Nat) :
    Nat → List CGate × (Fin L → Nat)
  | 0 => (gs, cur)
  | c + 1 =>
      let r1 := gReduceFrom n gs hasPiv pivRow cur c
      if hc : c < L then
        let idx : Fin L := ⟨c, hc⟩
        let r2 := gAnd n r1.1 (hasPiv idx) (r1.2 idx)
        gCondXorVecFrom n r2.1 r2.2 r1.2 (pivRow idx) L
      else r1

private lemma gReduceFrom_spec {L : Nat} {n : Nat} {gs : List CGate}
    (hasPiv : Fin L → Nat) (pivRow : Fin L → Fin L → Nat) (cur : Fin L → Nat)
    (hwf : WF n gs) (hhp : ∀ i, hasPiv i < n + gs.length)
    (hpr : ∀ i j, pivRow i j < n + gs.length) (hcur : ∀ i, cur i < n + gs.length) :
    ∀ step : Nat,
      WF n (gReduceFrom n gs hasPiv pivRow cur step).1 ∧ Ext gs (gReduceFrom n gs hasPiv pivRow cur step).1 ∧
      (gReduceFrom n gs hasPiv pivRow cur step).1.length ≤ gs.length + step * (5 * L + 1) ∧
      (∀ i, (gReduceFrom n gs hasPiv pivRow cur step).2 i < n + (gReduceFrom n gs hasPiv pivRow cur step).1.length) ∧
      ∀ (x : List Bool) (bhp : Fin L → Bool) (bpr : Fin L → Fin L → Bool) (bcur : Fin L → Bool),
        x.length = n → (∀ i, Val n gs x (hasPiv i) (bhp i)) →
        (∀ i j, Val n gs x (pivRow i j) (bpr i j)) → (∀ i, Val n gs x (cur i) (bcur i)) →
        ∀ i : Fin L, Val n (gReduceFrom n gs hasPiv pivRow cur step).1 x
          ((gReduceFrom n gs hasPiv pivRow cur step).2 i) (reduceFrom bhp bpr step bcur i) := by
  intro step
  induction step with
  | zero =>
      exact ⟨hwf, Ext.refl gs, by simp [gReduceFrom], hcur, fun _ _ _ _ _ _ _ hv i => hv i⟩
  | succ step ih =>
      rcases ih with ⟨hwf1, hext1, hlen1, hlt1, hval1⟩
      simp only [gReduceFrom, reduceFrom]
      by_cases hc : step < L
      · simp only [hc, ↓reduceDIte]
        set r1 := gReduceFrom n gs hasPiv pivRow cur step
        set idx : Fin L := ⟨step, hc⟩
        have hle1 : gs.length ≤ r1.1.length := hext1.len_le
        have h2 := gAnd_spec hwf1 (hasPiv idx) (r1.2 idx) (by have := hhp idx; omega) (hlt1 idx)
        set r2 := gAnd n r1.1 (hasPiv idx) (r1.2 idx)
        have h3 := gCondXorVecFrom_spec r2.2 r1.2 (pivRow idx) h2.1 h2.2.2.2.1
          (fun i => by have := hlt1 i; omega) (fun i => by have := hpr idx i; omega) L
        refine ⟨h3.1, hext1.trans (h2.2.1.trans h3.2.1), ?_, h3.2.2.2.1, ?_⟩
        · have hmul : (step + 1) * (5 * L + 1) = step * (5 * L + 1) + (5 * L + 1) := Nat.succ_mul _ _
          omega
        · intro x bhp bpr bcur hx hvhp hvpr hvcur i
          have v1 := hval1 x bhp bpr bcur hx hvhp hvpr hvcur
          have v2 := h2.2.2.2.2 x (bhp idx) (reduceFrom bhp bpr step bcur idx) hx
            ((hvhp idx).mono hx hext1) (v1 idx)
          have v3 := h3.2.2.2.2 x (bhp idx && reduceFrom bhp bpr step bcur idx)
            (reduceFrom bhp bpr step bcur) (bpr idx) hx v2
            (fun j => (v1 j).mono hx h2.2.1) (fun j => (hvpr idx j).mono hx (hext1.trans h2.2.1)) i
          simpa [i.isLt] using v3
      · simp only [hc, ↓reduceDIte]
        refine ⟨hwf1, hext1, ?_, hlt1, hval1⟩
        have : step * (5 * L + 1) ≤ (step + 1) * (5 * L + 1) := Nat.mul_le_mul_right _ (by omega)
        omega

private def gMuxVecFrom {L : Nat} (n : Nat) (gs : List CGate) (sel : Nat) (t f : Fin L → Nat) :
    Nat → List CGate × (Fin L → Nat)
  | 0 => (gs, f)
  | c + 1 =>
      let r1 := gMuxVecFrom n gs sel t f c
      if hc : c < L then
        let idx : Fin L := ⟨c, hc⟩
        let r2 := gMux n r1.1 sel (t idx) (f idx)
        (r2.1, fun i => if i = idx then r2.2 else r1.2 i)
      else r1

private lemma gMuxVecFrom_spec {L : Nat} {n : Nat} {gs : List CGate} (sel : Nat) (t f : Fin L → Nat)
    (hwf : WF n gs) (hs : sel < n + gs.length)
    (ht : ∀ i, t i < n + gs.length) (hf : ∀ i, f i < n + gs.length) :
    ∀ step : Nat,
      WF n (gMuxVecFrom n gs sel t f step).1 ∧ Ext gs (gMuxVecFrom n gs sel t f step).1 ∧
      (gMuxVecFrom n gs sel t f step).1.length ≤ gs.length + 4 * step ∧
      (∀ i, (gMuxVecFrom n gs sel t f step).2 i < n + (gMuxVecFrom n gs sel t f step).1.length) ∧
      ∀ (x : List Bool) (bs : Bool) (bt bf : Fin L → Bool), x.length = n →
        Val n gs x sel bs → (∀ i, Val n gs x (t i) (bt i)) → (∀ i, Val n gs x (f i) (bf i)) →
        ∀ i : Fin L, Val n (gMuxVecFrom n gs sel t f step).1 x ((gMuxVecFrom n gs sel t f step).2 i)
          (if i.val < step then (if bs then bt i else bf i) else bf i) := by
  intro step
  induction step with
  | zero =>
      exact ⟨hwf, Ext.refl gs, by simp [gMuxVecFrom], hf,
        fun _ _ _ _ _ _ _ hvf i => by simpa [gMuxVecFrom] using hvf i⟩
  | succ step ih =>
      rcases ih with ⟨hwf1, hext1, hlen1, hlt1, hval1⟩
      simp only [gMuxVecFrom]
      by_cases hc : step < L
      · simp only [hc, ↓reduceDIte]
        set r1 := gMuxVecFrom n gs sel t f step
        set idx : Fin L := ⟨step, hc⟩
        have hle1 : gs.length ≤ r1.1.length := hext1.len_le
        have h2 := gMux_spec hwf1 sel (t idx) (f idx) (by omega) (by have := ht idx; omega) (by have := hf idx; omega)
        refine ⟨h2.1, hext1.trans h2.2.1, by omega, ?_, ?_⟩
        · intro i
          by_cases hi : i = idx
          · simp only [hi, ↓reduceIte]; exact h2.2.2.2.1
          · simp only [hi, ↓reduceIte]; have := hlt1 i; omega
        · intro x bs bt bf hx hvs hvt hvf i
          by_cases hi : i = idx
          · subst hi
            simp only [↓reduceIte, idx, Nat.lt_succ_self]
            exact h2.2.2.2.2 x bs (bt idx) (bf idx) hx (hvs.mono hx hext1)
              ((hvt idx).mono hx hext1) ((hvf idx).mono hx hext1)
          · simp only [hi, ↓reduceIte]
            have hne : i.val ≠ step := fun h => hi (Fin.ext h)
            have hlt_iff : i.val < step + 1 ↔ i.val < step := by omega
            simp only [hlt_iff]
            exact (hval1 x bs bt bf hx hvs hvt hvf i).mono hx h2.2.1
      · simp only [hc, ↓reduceDIte]
        refine ⟨hwf1, hext1, by omega, hlt1, fun x bs bt bf hx hvs hvt hvf i => ?_⟩
        have hlt_iff : i.val < step + 1 ↔ i.val < step := by omega
        simp only [hlt_iff]
        exact hval1 x bs bt bf hx hvs hvt hvf i

private def gInsertStepClean {L : Nat} (n : Nat) (gs : List CGate)
    (hasPiv : Fin L → Nat) (pivRow : Fin L → Fin L → Nat) (cur : Fin L → Nat) (c0 : Nat) :
    Nat → List CGate × Nat × (Fin L → Nat) × (Fin L → Fin L → Nat)
  | 0 => (gs, c0, hasPiv, pivRow)
  | j + 1 =>
      let r1 := gInsertStepClean n gs hasPiv pivRow cur c0 j
      if hj : j < L then
        let idx : Fin L := ⟨j, hj⟩
        let r2 := gNot n r1.1 r1.2.1
        let r3 := gAnd n r2.1 r2.2 (cur idx)
        let r4 := gOr n r3.1 r1.2.1 r3.2
        let r5 := gOr n r4.1 r3.2 (r1.2.2.1 idx)
        let r6 := gMuxVecFrom n r5.1 r3.2 cur (r1.2.2.2 idx) L
        (r6.1, r4.2,
          fun i => if i = idx then r5.2 else r1.2.2.1 i,
          fun i => if i = idx then r6.2 else r1.2.2.2 i)
      else r1

private lemma gInsertStepClean_spec {L : Nat} {n : Nat} {gs : List CGate}
    (hasPiv : Fin L → Nat) (pivRow : Fin L → Fin L → Nat) (cur : Fin L → Nat) (c0 : Nat)
    (hwf : WF n gs) (hc0 : c0 < n + gs.length)
    (hhp : ∀ i, hasPiv i < n + gs.length) (hpr : ∀ i j, pivRow i j < n + gs.length)
    (hcur : ∀ i, cur i < n + gs.length) :
    ∀ step : Nat,
      WF n (gInsertStepClean n gs hasPiv pivRow cur c0 step).1 ∧
      Ext gs (gInsertStepClean n gs hasPiv pivRow cur c0 step).1 ∧
      (gInsertStepClean n gs hasPiv pivRow cur c0 step).1.length ≤ gs.length + step * (4 * L + 4) ∧
      (gInsertStepClean n gs hasPiv pivRow cur c0 step).2.1 < n + (gInsertStepClean n gs hasPiv pivRow cur c0 step).1.length ∧
      (∀ i, (gInsertStepClean n gs hasPiv pivRow cur c0 step).2.2.1 i < n + (gInsertStepClean n gs hasPiv pivRow cur c0 step).1.length) ∧
      (∀ i j, (gInsertStepClean n gs hasPiv pivRow cur c0 step).2.2.2 i j < n + (gInsertStepClean n gs hasPiv pivRow cur c0 step).1.length) ∧
      ∀ (x : List Bool) (bhp : Fin L → Bool) (bpr : Fin L → Fin L → Bool) (bcur : Fin L → Bool),
        x.length = n → Val n gs x c0 false →
        (∀ i, Val n gs x (hasPiv i) (bhp i)) → (∀ i j, Val n gs x (pivRow i j) (bpr i j)) →
        (∀ i, Val n gs x (cur i) (bcur i)) →
        Val n (gInsertStepClean n gs hasPiv pivRow cur c0 step).1 x
          (gInsertStepClean n gs hasPiv pivRow cur c0 step).2.1 (insertStep bhp bpr bcur step).1 ∧
        (∀ i, Val n (gInsertStepClean n gs hasPiv pivRow cur c0 step).1 x
          ((gInsertStepClean n gs hasPiv pivRow cur c0 step).2.2.1 i) ((insertStep bhp bpr bcur step).2.1 i)) ∧
        (∀ i j, Val n (gInsertStepClean n gs hasPiv pivRow cur c0 step).1 x
          ((gInsertStepClean n gs hasPiv pivRow cur c0 step).2.2.2 i j) ((insertStep bhp bpr bcur step).2.2 i j)) := by
  intro step
  induction step with
  | zero =>
      exact ⟨hwf, Ext.refl gs, by simp [gInsertStepClean], hc0, hhp, hpr,
        fun _ _ _ _ _ hvc0 hvhp hvpr _ => ⟨hvc0, hvhp, hvpr⟩⟩
  | succ step ih =>
      rcases ih with ⟨hwf1, hext1, hlen1, hltF, hltHP, hltPR, hval1⟩
      simp only [gInsertStepClean, insertStep]
      by_cases hj : step < L
      · simp only [hj, ↓reduceDIte]
        set r1 := gInsertStepClean n gs hasPiv pivRow cur c0 step
        set idx : Fin L := ⟨step, hj⟩
        have hle1 : gs.length ≤ r1.1.length := hext1.len_le
        have h2 := gNot_spec hwf1 r1.2.1 hltF
        set r2 := gNot n r1.1 r1.2.1
        have h3 := gAnd_spec h2.1 r2.2 (cur idx) h2.2.2.2.1 (by have := hcur idx; omega)
        set r3 := gAnd n r2.1 r2.2 (cur idx)
        have h4 := gOr_spec h3.1 r1.2.1 r3.2 (by omega) h3.2.2.2.1
        set r4 := gOr n r3.1 r1.2.1 r3.2
        have h5 := gOr_spec h4.1 r3.2 (r1.2.2.1 idx) (by have := h3.2.2.2.1; omega) (by have := hltHP idx; omega)
        set r5 := gOr n r4.1 r3.2 (r1.2.2.1 idx)
        have h6 := gMuxVecFrom_spec r3.2 cur (r1.2.2.2 idx) h5.1
          (by have := h3.2.2.2.1; omega) (fun i => by have := hcur i; omega)
          (fun i => by have := hltPR idx i; omega) L
        set r6 := gMuxVecFrom n r5.1 r3.2 cur (r1.2.2.2 idx) L
        have hext_step := h2.2.1.trans (h3.2.1.trans (h4.2.1.trans (h5.2.1.trans h6.2.1)))
        have hle6 : r5.1.length ≤ r6.1.length := h6.2.1.len_le
        have hle16 : r1.1.length ≤ r6.1.length := hext_step.len_le
        refine ⟨h6.1, hext1.trans hext_step, ?_, ?_, ?_, ?_, ?_⟩
        · have hmul : (step + 1) * (4 * L + 4) = step * (4 * L + 4) + (4 * L + 4) := Nat.succ_mul _ _
          omega
        · have := h4.2.2.2.1; omega
        · intro i
          by_cases hi : i = idx
          · simp only [hi, ↓reduceIte]; have := h5.2.2.2.1; omega
          · simp only [hi, ↓reduceIte]; have := hltHP i; omega
        · intro i j
          by_cases hi : i = idx
          · simp only [hi, ↓reduceIte]; exact h6.2.2.2.1 j
          · simp only [hi, ↓reduceIte]; have := hltPR i j; omega
        · intro x bhp bpr bcur hx hvc0 hvhp hvpr hvcur
          rcases hval1 x bhp bpr bcur hx hvc0 hvhp hvpr hvcur with ⟨vF, vHP, vPR⟩
          have v2 := h2.2.2.2.2 x _ hx vF
          have v3 := h3.2.2.2.2 x _ (bcur idx) hx v2 ((hvcur idx).mono hx (hext1.trans h2.2.1))
          have v4 := h4.2.2.2.2 x _ _ hx (vF.mono hx (h2.2.1.trans h3.2.1)) v3
          have v5 := h5.2.2.2.2 x _ _ hx (v3.mono hx h4.2.1)
            ((vHP idx).mono hx (h2.2.1.trans (h3.2.1.trans h4.2.1)))
          have v6 := h6.2.2.2.2 x _ bcur _ hx (v3.mono hx (h4.2.1.trans h5.2.1))
            (fun c => (hvcur c).mono hx (hext1.trans (h2.2.1.trans (h3.2.1.trans (h4.2.1.trans h5.2.1)))))
            (fun c => (vPR idx c).mono hx (h2.2.1.trans (h3.2.1.trans (h4.2.1.trans h5.2.1))))
          have hor1 : ∀ a b : Bool, (a || !a && b) = (a || b) := fun a b => by cases a <;> cases b <;> rfl
          rw [hor1] at v4
          refine ⟨v4.mono hx (h5.2.1.trans h6.2.1), ?_, ?_⟩
          · intro i
            by_cases hi : i = idx
            · subst hi
              simp only [↓reduceIte]
              have hv5' := v5.mono hx h6.2.1
              have hor : ∀ a b : Bool, (a || b) = if a then true else b := by
                intro a b; cases a <;> cases b <;> rfl
              rwa [hor] at hv5'
            · simp only [hi, ↓reduceIte]
              exact (vHP i).mono hx hext_step
          · intro i c
            by_cases hi : i = idx
            · subst hi
              simp only [↓reduceIte]
              simpa [c.isLt] using v6 c
            · simp only [hi, ↓reduceIte]
              exact (vPR i c).mono hx hext_step
      · simp only [hj, ↓reduceDIte]
        refine ⟨hwf1, hext1, ?_, hltF, hltHP, hltPR, hval1⟩
        have : step * (4 * L + 4) ≤ (step + 1) * (4 * L + 4) := Nat.mul_le_mul_right _ (by omega)
        omega

private def gEchelonFrom {m L : Nat} (n : Nat) (gs : List CGate) (rows : Fin m → Fin L → Nat) (c0 : Nat) :
    Nat → List CGate × (Fin L → Nat) × (Fin L → Fin L → Nat)
  | 0 => (gs, fun _ => c0, fun _ _ => c0)
  | r + 1 =>
      let r1 := gEchelonFrom n gs rows c0 r
      if hr : r < m then
        let r2 := gReduceFrom n r1.1 r1.2.1 r1.2.2 (rows ⟨r, hr⟩) L
        let r3 := gInsertStepClean n r2.1 r1.2.1 r1.2.2 r2.2 c0 L
        (r3.1, r3.2.2.1, r3.2.2.2)
      else r1

private lemma gEchelonFrom_spec {m L : Nat} {n : Nat} {gs : List CGate}
    (rows : Fin m → Fin L → Nat) (c0 : Nat)
    (hwf : WF n gs) (hc0 : c0 < n + gs.length) (hrows : ∀ g c, rows g c < n + gs.length) :
    ∀ step : Nat,
      WF n (gEchelonFrom n gs rows c0 step).1 ∧ Ext gs (gEchelonFrom n gs rows c0 step).1 ∧
      (gEchelonFrom n gs rows c0 step).1.length ≤ gs.length + step * (L * (9 * L + 5)) ∧
      (∀ i, (gEchelonFrom n gs rows c0 step).2.1 i < n + (gEchelonFrom n gs rows c0 step).1.length) ∧
      (∀ i j, (gEchelonFrom n gs rows c0 step).2.2 i j < n + (gEchelonFrom n gs rows c0 step).1.length) ∧
      ∀ (x : List Bool) (brows : Fin m → Fin L → Bool), x.length = n →
        Val n gs x c0 false → (∀ g c, Val n gs x (rows g c) (brows g c)) →
        (∀ i, Val n (gEchelonFrom n gs rows c0 step).1 x ((gEchelonFrom n gs rows c0 step).2.1 i) ((echelonFrom brows step).1 i)) ∧
        (∀ i j, Val n (gEchelonFrom n gs rows c0 step).1 x ((gEchelonFrom n gs rows c0 step).2.2 i j) ((echelonFrom brows step).2 i j)) := by
  intro step
  induction step with
  | zero =>
      exact ⟨hwf, Ext.refl gs, by simp [gEchelonFrom], fun _ => hc0, fun _ _ => hc0,
        fun _ _ _ hvc0 _ => ⟨fun _ => hvc0, fun _ _ => hvc0⟩⟩
  | succ step ih =>
      rcases ih with ⟨hwf1, hext1, hlen1, hltHP, hltPR, hval1⟩
      simp only [gEchelonFrom, echelonFrom, echelonStep, reduceVec]
      by_cases hr : step < m
      · simp only [hr, ↓reduceDIte]
        set r1 := gEchelonFrom n gs rows c0 step
        have hle1 : gs.length ≤ r1.1.length := hext1.len_le
        have h2 := gReduceFrom_spec r1.2.1 r1.2.2 (rows ⟨step, hr⟩) hwf1 hltHP hltPR
          (fun c => by have := hrows ⟨step, hr⟩ c; omega) L
        set r2 := gReduceFrom n r1.1 r1.2.1 r1.2.2 (rows ⟨step, hr⟩) L
        have hle2 : r1.1.length ≤ r2.1.length := h2.2.1.len_le
        have h3 := gInsertStepClean_spec r1.2.1 r1.2.2 r2.2 c0 h2.1 (by omega)
          (fun i => by have := hltHP i; omega) (fun i j => by have := hltPR i j; omega) h2.2.2.2.1 L
        refine ⟨h3.1, hext1.trans (h2.2.1.trans h3.2.1), ?_, h3.2.2.2.2.1, h3.2.2.2.2.2.1, ?_⟩
        · have hmul : (step + 1) * (L * (9 * L + 5)) = step * (L * (9 * L + 5)) + L * (9 * L + 5) := Nat.succ_mul _ _
          have hadd : L * (5 * L + 1) + L * (4 * L + 4) = L * (9 * L + 5) := by ring
          omega
        · intro x brows hx hvc0 hvrows
          rcases hval1 x brows hx hvc0 hvrows with ⟨vHP, vPR⟩
          have v2 := h2.2.2.2.2 x _ _ (brows ⟨step, hr⟩) hx vHP vPR
            (fun c => (hvrows ⟨step, hr⟩ c).mono hx hext1)
          have v3 := h3.2.2.2.2.2.2 x _ _ _ hx (hvc0.mono hx (hext1.trans h2.2.1))
            (fun i => (vHP i).mono hx h2.2.1) (fun i j => (vPR i j).mono hx h2.2.1) v2
          exact ⟨v3.2.1, v3.2.2⟩
      · simp only [hr, ↓reduceDIte]
        refine ⟨hwf1, hext1, ?_, hltHP, hltPR, hval1⟩
        have : step * (L * (9 * L + 5)) ≤ (step + 1) * (L * (9 * L + 5)) := Nat.mul_le_mul_right _ (by omega)
        omega

private def gInsertSlotFrom {t L : Nat} (n : Nat) (gs : List CGate)
    (active : Fin t → Nat) (B : Fin t → Fin L → Nat) (en : Nat) (row : Fin L → Nat) (c0 : Nat) :
    Nat → List CGate × Nat × (Fin t → Nat) × (Fin t → Fin L → Nat)
  | 0 => (gs, c0, active, B)
  | j + 1 =>
      let r1 := gInsertSlotFrom n gs active B en row c0 j
      if hj : j < t then
        let idx : Fin t := ⟨j, hj⟩
        let r2 := gNot n r1.1 r1.2.1
        let r3 := gNot n r2.1 (r1.2.2.1 idx)
        let r4 := gAnd n r3.1 en r2.2
        let r5 := gAnd n r4.1 r4.2 r3.2
        let r6 := gOr n r5.1 r1.2.1 r5.2
        let r7 := gOr n r6.1 r5.2 (r1.2.2.1 idx)
        let r8 := gMuxVecFrom n r7.1 r5.2 row (r1.2.2.2 idx) L
        (r8.1, r6.2,
          fun i => if i = idx then r7.2 else r1.2.2.1 i,
          fun i => if i = idx then r8.2 else r1.2.2.2 i)
      else r1

private lemma gInsertSlotFrom_spec {t L : Nat} {n : Nat} {gs : List CGate}
    (active : Fin t → Nat) (B : Fin t → Fin L → Nat) (en : Nat) (row : Fin L → Nat) (c0 : Nat)
    (hwf : WF n gs) (hc0 : c0 < n + gs.length)
    (hact : ∀ i, active i < n + gs.length) (hB : ∀ i c, B i c < n + gs.length)
    (hen : en < n + gs.length) (hrow : ∀ c, row c < n + gs.length) :
    ∀ step : Nat,
      WF n (gInsertSlotFrom n gs active B en row c0 step).1 ∧
      Ext gs (gInsertSlotFrom n gs active B en row c0 step).1 ∧
      (gInsertSlotFrom n gs active B en row c0 step).1.length ≤ gs.length + step * (4 * L + 6) ∧
      (gInsertSlotFrom n gs active B en row c0 step).2.1 < n + (gInsertSlotFrom n gs active B en row c0 step).1.length ∧
      (∀ i, (gInsertSlotFrom n gs active B en row c0 step).2.2.1 i < n + (gInsertSlotFrom n gs active B en row c0 step).1.length) ∧
      (∀ i c, (gInsertSlotFrom n gs active B en row c0 step).2.2.2 i c < n + (gInsertSlotFrom n gs active B en row c0 step).1.length) ∧
      ∀ (x : List Bool) (bact : Fin t → Bool) (bB : Fin t → Fin L → Bool) (ben : Bool) (brow : Fin L → Bool),
        x.length = n → Val n gs x c0 false →
        (∀ i, Val n gs x (active i) (bact i)) → (∀ i c, Val n gs x (B i c) (bB i c)) →
        Val n gs x en ben → (∀ c, Val n gs x (row c) (brow c)) →
        Val n (gInsertSlotFrom n gs active B en row c0 step).1 x
          (gInsertSlotFrom n gs active B en row c0 step).2.1 (insertSlotFrom bact bB ben brow step).1 ∧
        (∀ i, Val n (gInsertSlotFrom n gs active B en row c0 step).1 x
          ((gInsertSlotFrom n gs active B en row c0 step).2.2.1 i) ((insertSlotFrom bact bB ben brow step).2.1 i)) ∧
        (∀ i c, Val n (gInsertSlotFrom n gs active B en row c0 step).1 x
          ((gInsertSlotFrom n gs active B en row c0 step).2.2.2 i c) ((insertSlotFrom bact bB ben brow step).2.2 i c)) := by
  intro step
  induction step with
  | zero =>
      exact ⟨hwf, Ext.refl gs, by simp [gInsertSlotFrom], hc0, hact, hB,
        fun _ _ _ _ _ _ hvc0 hvact hvB _ _ => ⟨hvc0, hvact, hvB⟩⟩
  | succ step ih =>
      rcases ih with ⟨hwf1, hext1, hlen1, hltP, hltA, hltB, hval1⟩
      simp only [gInsertSlotFrom, insertSlotFrom]
      by_cases hj : step < t
      · simp only [hj, ↓reduceDIte]
        set r1 := gInsertSlotFrom n gs active B en row c0 step
        set idx : Fin t := ⟨step, hj⟩
        have hle1 : gs.length ≤ r1.1.length := hext1.len_le
        have h2 := gNot_spec hwf1 r1.2.1 hltP
        set r2 := gNot n r1.1 r1.2.1
        have h3 := gNot_spec h2.1 (r1.2.2.1 idx) (by have := hltA idx; omega)
        set r3 := gNot n r2.1 (r1.2.2.1 idx)
        have h4 := gAnd_spec h3.1 en r2.2 (by omega) (by have := h2.2.2.2.1; omega)
        set r4 := gAnd n r3.1 en r2.2
        have h5 := gAnd_spec h4.1 r4.2 r3.2 h4.2.2.2.1 (by have := h3.2.2.2.1; omega)
        set r5 := gAnd n r4.1 r4.2 r3.2
        have h6 := gOr_spec h5.1 r1.2.1 r5.2 (by omega) h5.2.2.2.1
        set r6 := gOr n r5.1 r1.2.1 r5.2
        have h7 := gOr_spec h6.1 r5.2 (r1.2.2.1 idx) (by have := h5.2.2.2.1; omega) (by have := hltA idx; omega)
        set r7 := gOr n r6.1 r5.2 (r1.2.2.1 idx)
        have h8 := gMuxVecFrom_spec r5.2 row (r1.2.2.2 idx) h7.1
          (by have := h5.2.2.2.1; omega) (fun c => by have := hrow c; omega)
          (fun c => by have := hltB idx c; omega) L
        set r8 := gMuxVecFrom n r7.1 r5.2 row (r1.2.2.2 idx) L
        have hext_step := h2.2.1.trans (h3.2.1.trans (h4.2.1.trans (h5.2.1.trans (h6.2.1.trans (h7.2.1.trans h8.2.1)))))
        have hle8 : r7.1.length ≤ r8.1.length := h8.2.1.len_le
        have hle18 : r1.1.length ≤ r8.1.length := hext_step.len_le
        refine ⟨h8.1, hext1.trans hext_step, ?_, ?_, ?_, ?_, ?_⟩
        · have hmul : (step + 1) * (4 * L + 6) = step * (4 * L + 6) + (4 * L + 6) := Nat.succ_mul _ _
          omega
        · have := h6.2.2.2.1; omega
        · intro i
          by_cases hi : i = idx
          · simp only [hi, ↓reduceIte]; have := h7.2.2.2.1; omega
          · simp only [hi, ↓reduceIte]; have := hltA i; omega
        · intro i c
          by_cases hi : i = idx
          · simp only [hi, ↓reduceIte]; exact h8.2.2.2.1 c
          · simp only [hi, ↓reduceIte]; have := hltB i c; omega
        · intro x bact bB ben brow hx hvc0 hvact hvB hven hvrow
          rcases hval1 x bact bB ben brow hx hvc0 hvact hvB hven hvrow with ⟨vP, vA, vB⟩
          have v2 := h2.2.2.2.2 x _ hx vP
          have v3 := h3.2.2.2.2 x _ hx ((vA idx).mono hx h2.2.1)
          have v4 := h4.2.2.2.2 x ben _ hx (hven.mono hx (hext1.trans (h2.2.1.trans h3.2.1))) (v2.mono hx h3.2.1)
          have v5 := h5.2.2.2.2 x _ _ hx v4 (v3.mono hx h4.2.1)
          have hext5 := h2.2.1.trans (h3.2.1.trans (h4.2.1.trans h5.2.1))
          have v6 := h6.2.2.2.2 x _ _ hx (vP.mono hx hext5) v5
          have v7 := h7.2.2.2.2 x _ _ hx (v5.mono hx h6.2.1) ((vA idx).mono hx (hext5.trans h6.2.1))
          have hext7 := hext5.trans (h6.2.1.trans h7.2.1)
          have v8 := h8.2.2.2.2 x _ brow _ hx (v5.mono hx (h6.2.1.trans h7.2.1))
            (fun c => (hvrow c).mono hx (hext1.trans hext7))
            (fun c => (vB idx c).mono hx hext7)
          refine ⟨v6.mono hx (h7.2.1.trans h8.2.1), ?_, ?_⟩
          · intro i
            by_cases hi : i = idx
            · subst hi
              simp only [↓reduceIte]
              have hv7' := v7.mono hx h8.2.1
              have hor : ∀ a b : Bool, (a || b) = if a then true else b := by
                intro a b; cases a <;> cases b <;> rfl
              rwa [hor] at hv7'
            · simp only [hi, ↓reduceIte]
              exact (vA i).mono hx hext_step
          · intro i c
            by_cases hi : i = idx
            · subst hi
              simp only [↓reduceIte]
              simpa [c.isLt] using v8 c
            · simp only [hi, ↓reduceIte]
              exact (vB i c).mono hx hext_step
      · simp only [hj, ↓reduceDIte]
        refine ⟨hwf1, hext1, ?_, hltP, hltA, hltB, hval1⟩
        have : step * (4 * L + 6) ≤ (step + 1) * (4 * L + 6) := Nat.mul_le_mul_right _ (by omega)
        omega

private def gCompactFrom {L t : Nat} (n : Nat) (gs : List CGate)
    (hasPiv : Fin L → Nat) (pivRow : Fin L → Fin L → Nat) (c0 : Nat) :
    Nat → List CGate × (Fin t → Nat) × (Fin t → Fin L → Nat)
  | 0 => (gs, fun _ => c0, fun _ _ => c0)
  | c + 1 =>
      let r1 := gCompactFrom n gs hasPiv pivRow c0 c
      if hc : c < L then
        let idx : Fin L := ⟨c, hc⟩
        let r2 := gInsertSlotFrom n r1.1 r1.2.1 r1.2.2 (hasPiv idx) (pivRow idx) c0 t
        (r2.1, r2.2.2.1, r2.2.2.2)
      else r1

private lemma gCompactFrom_spec {L t : Nat} {n : Nat} {gs : List CGate}
    (hasPiv : Fin L → Nat) (pivRow : Fin L → Fin L → Nat) (c0 : Nat)
    (hwf : WF n gs) (hc0 : c0 < n + gs.length)
    (hhp : ∀ i, hasPiv i < n + gs.length) (hpr : ∀ i j, pivRow i j < n + gs.length) :
    ∀ step : Nat,
      WF n (gCompactFrom (t := t) n gs hasPiv pivRow c0 step).1 ∧
      Ext gs (gCompactFrom (t := t) n gs hasPiv pivRow c0 step).1 ∧
      (gCompactFrom (t := t) n gs hasPiv pivRow c0 step).1.length ≤ gs.length + step * (t * (4 * L + 6)) ∧
      (∀ i, (gCompactFrom (t := t) n gs hasPiv pivRow c0 step).2.1 i < n + (gCompactFrom (t := t) n gs hasPiv pivRow c0 step).1.length) ∧
      (∀ i c, (gCompactFrom (t := t) n gs hasPiv pivRow c0 step).2.2 i c < n + (gCompactFrom (t := t) n gs hasPiv pivRow c0 step).1.length) ∧
      ∀ (x : List Bool) (bhp : Fin L → Bool) (bpr : Fin L → Fin L → Bool), x.length = n →
        Val n gs x c0 false → (∀ i, Val n gs x (hasPiv i) (bhp i)) →
        (∀ i j, Val n gs x (pivRow i j) (bpr i j)) →
        (∀ i, Val n (gCompactFrom (t := t) n gs hasPiv pivRow c0 step).1 x
          ((gCompactFrom (t := t) n gs hasPiv pivRow c0 step).2.1 i) ((compactFrom (t := t) bhp bpr step).1 i)) ∧
        (∀ i c, Val n (gCompactFrom (t := t) n gs hasPiv pivRow c0 step).1 x
          ((gCompactFrom (t := t) n gs hasPiv pivRow c0 step).2.2 i c) ((compactFrom (t := t) bhp bpr step).2 i c)) := by
  intro step
  induction step with
  | zero =>
      exact ⟨hwf, Ext.refl gs, by simp [gCompactFrom], fun _ => hc0, fun _ _ => hc0,
        fun _ _ _ _ hvc0 _ _ => ⟨fun _ => hvc0, fun _ _ => hvc0⟩⟩
  | succ step ih =>
      rcases ih with ⟨hwf1, hext1, hlen1, hltA, hltB, hval1⟩
      simp only [gCompactFrom, compactFrom]
      by_cases hc : step < L
      · simp only [hc, ↓reduceDIte]
        set r1 := gCompactFrom (t := t) n gs hasPiv pivRow c0 step
        set idx : Fin L := ⟨step, hc⟩
        have hle1 : gs.length ≤ r1.1.length := hext1.len_le
        have h2 := gInsertSlotFrom_spec r1.2.1 r1.2.2 (hasPiv idx) (pivRow idx) c0 hwf1 (by omega) hltA hltB
          (by have := hhp idx; omega) (fun c => by have := hpr idx c; omega) t
        refine ⟨h2.1, hext1.trans h2.2.1, ?_, h2.2.2.2.2.1, h2.2.2.2.2.2.1, ?_⟩
        · have hmul : (step + 1) * (t * (4 * L + 6)) = step * (t * (4 * L + 6)) + t * (4 * L + 6) := Nat.succ_mul _ _
          omega
        · intro x bhp bpr hx hvc0 hvhp hvpr
          rcases hval1 x bhp bpr hx hvc0 hvhp hvpr with ⟨vA, vB⟩
          have v2 := h2.2.2.2.2.2.2 x _ _ (bhp idx) (bpr idx) hx (hvc0.mono hx hext1)
            vA vB ((hvhp idx).mono hx hext1) (fun c => (hvpr idx c).mono hx hext1)
          exact ⟨v2.2.1, v2.2.2⟩
      · simp only [hc, ↓reduceDIte]
        refine ⟨hwf1, hext1, ?_, hltA, hltB, hval1⟩
        have : step * (t * (4 * L + 6)) ≤ (step + 1) * (t * (4 * L + 6)) := Nat.mul_le_mul_right _ (by omega)
        omega

private def allFinFrom {L : Nat} (f : Fin L → Bool) : Nat → Bool
  | 0 => true
  | j + 1 =>
      let prev := allFinFrom f j
      if hj : j < L then prev && f ⟨j, hj⟩ else prev

private lemma allFinFrom_iff {L : Nat} (f : Fin L → Bool) :
    ∀ step : Nat, allFinFrom f step = true ↔ ∀ j : Fin L, j.val < step → f j = true := by
  intro step
  induction step with
  | zero =>
      simp [allFinFrom]
  | succ step ih =>
      simp only [allFinFrom]
      by_cases hj : step < L
      · simp only [hj, ↓reduceDIte, Bool.and_eq_true, ih]
        constructor
        · rintro ⟨h1, h2⟩ j hlt
          by_cases h : j.val < step
          · exact h1 j h
          · have heq : j = ⟨step, hj⟩ := Fin.ext (show j.val = step by omega)
            rwa [heq]
        · intro h
          exact ⟨fun j hlt => h j (by omega), h ⟨step, hj⟩ (Nat.lt_succ_self step)⟩
      · simp only [hj, ↓reduceDIte, ih]
        constructor
        · intro h j hlt; exact h j (by omega)
        · intro h j hlt; exact h j (by omega)

private lemma allFinFrom_eq_all {L : Nat} (f : Fin L → Bool) :
    allFinFrom f L = (List.finRange L).all f := by
  rw [Bool.eq_iff_iff, allFinFrom_iff, List.all_eq_true]
  constructor
  · intro h j _; exact h j j.isLt
  · intro h j _; exact h j (List.mem_finRange j)

private def gValidMaskFrom {t : Nat} (n : Nat) (gs : List CGate) (activeSlot : Fin t → Nat)
    (mask : Fin (2 ^ t)) (c1 : Nat) : Nat → List CGate × Nat
  | 0 => (gs, c1)
  | j + 1 =>
      let r1 := gValidMaskFrom n gs activeSlot mask c1 j
      if hj : j < t then
        if mask.val.testBit j then
          gAnd n r1.1 r1.2 (activeSlot ⟨j, hj⟩)
        else r1
      else r1

private lemma gValidMaskFrom_spec {t : Nat} {n : Nat} {gs : List CGate}
    (activeSlot : Fin t → Nat) (mask : Fin (2 ^ t)) (c1 : Nat)
    (hwf : WF n gs) (hc1 : c1 < n + gs.length) (hact : ∀ i, activeSlot i < n + gs.length) :
    ∀ step : Nat,
      WF n (gValidMaskFrom n gs activeSlot mask c1 step).1 ∧
      Ext gs (gValidMaskFrom n gs activeSlot mask c1 step).1 ∧
      (gValidMaskFrom n gs activeSlot mask c1 step).1.length ≤ gs.length + step ∧
      (gValidMaskFrom n gs activeSlot mask c1 step).2 < n + (gValidMaskFrom n gs activeSlot mask c1 step).1.length ∧
      ∀ (x : List Bool) (bact : Fin t → Bool), x.length = n →
        Val n gs x c1 true → (∀ i, Val n gs x (activeSlot i) (bact i)) →
        Val n (gValidMaskFrom n gs activeSlot mask c1 step).1 x
          (gValidMaskFrom n gs activeSlot mask c1 step).2
          (allFinFrom (fun j : Fin t => !mask.val.testBit j.val || bact j) step) := by
  intro step
  induction step with
  | zero =>
      exact ⟨hwf, Ext.refl gs, by simp [gValidMaskFrom], hc1, fun _ _ _ hvc1 _ => hvc1⟩
  | succ step ih =>
      rcases ih with ⟨hwf1, hext1, hlen1, hlt1, hval1⟩
      simp only [gValidMaskFrom, allFinFrom]
      by_cases hj : step < t
      · simp only [hj, ↓reduceDIte]
        set r1 := gValidMaskFrom n gs activeSlot mask c1 step
        cases htb : mask.val.testBit step
        · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_or, Bool.and_true]
          exact ⟨hwf1, hext1, by omega, hlt1, hval1⟩
        · simp only [↓reduceIte, Bool.not_true, Bool.false_or]
          have hle1 : gs.length ≤ r1.1.length := hext1.len_le
          have h2 := gAnd_spec hwf1 r1.2 (activeSlot ⟨step, hj⟩) hlt1 (by have := hact ⟨step, hj⟩; omega)
          refine ⟨h2.1, hext1.trans h2.2.1, by omega, h2.2.2.2.1, fun x bact hx hvc1 hvact => ?_⟩
          exact h2.2.2.2.2 x _ (bact ⟨step, hj⟩) hx (hval1 x bact hx hvc1 hvact) ((hvact ⟨step, hj⟩).mono hx hext1)
      · simp only [hj, ↓reduceDIte]
        exact ⟨hwf1, hext1, by omega, hlt1, hval1⟩

private def gXorVecFrom {L : Nat} (n : Nat) (gs : List CGate) (a b : Fin L → Nat) :
    Nat → List CGate × (Fin L → Nat)
  | 0 => (gs, a)
  | j + 1 =>
      let r1 := gXorVecFrom n gs a b j
      if hj : j < L then
        let idx : Fin L := ⟨j, hj⟩
        let r2 := gXor n r1.1 (a idx) (b idx)
        (r2.1, fun i => if i = idx then r2.2 else r1.2 i)
      else r1

private lemma gXorVecFrom_spec {L : Nat} {n : Nat} {gs : List CGate} (a b : Fin L → Nat)
    (hwf : WF n gs) (ha : ∀ i, a i < n + gs.length) (hb : ∀ i, b i < n + gs.length) :
    ∀ step : Nat,
      WF n (gXorVecFrom n gs a b step).1 ∧ Ext gs (gXorVecFrom n gs a b step).1 ∧
      (gXorVecFrom n gs a b step).1.length ≤ gs.length + 4 * step ∧
      (∀ i, (gXorVecFrom n gs a b step).2 i < n + (gXorVecFrom n gs a b step).1.length) ∧
      ∀ (x : List Bool) (ba bb : Fin L → Bool), x.length = n →
        (∀ i, Val n gs x (a i) (ba i)) → (∀ i, Val n gs x (b i) (bb i)) →
        ∀ i : Fin L, Val n (gXorVecFrom n gs a b step).1 x ((gXorVecFrom n gs a b step).2 i)
          (if i.val < step then xor (ba i) (bb i) else ba i) := by
  intro step
  induction step with
  | zero =>
      exact ⟨hwf, Ext.refl gs, by simp [gXorVecFrom], ha,
        fun _ _ _ _ hva _ i => by simpa [gXorVecFrom] using hva i⟩
  | succ step ih =>
      rcases ih with ⟨hwf1, hext1, hlen1, hlt1, hval1⟩
      simp only [gXorVecFrom]
      by_cases hj : step < L
      · simp only [hj, ↓reduceDIte]
        set r1 := gXorVecFrom n gs a b step
        set idx : Fin L := ⟨step, hj⟩
        have hle1 : gs.length ≤ r1.1.length := hext1.len_le
        have h2 := gXor_spec hwf1 (a idx) (b idx) (by have := ha idx; omega) (by have := hb idx; omega)
        refine ⟨h2.1, hext1.trans h2.2.1, by omega, ?_, ?_⟩
        · intro i
          by_cases hi : i = idx
          · simp only [hi, ↓reduceIte]; exact h2.2.2.2.1
          · simp only [hi, ↓reduceIte]; have := hlt1 i; omega
        · intro x ba bb hx hva hvb i
          by_cases hi : i = idx
          · subst hi
            simp only [↓reduceIte, idx, Nat.lt_succ_self]
            exact h2.2.2.2.2 x (ba idx) (bb idx) hx ((hva idx).mono hx hext1) ((hvb idx).mono hx hext1)
          · simp only [hi, ↓reduceIte]
            have hne : i.val ≠ step := fun h => hi (Fin.ext h)
            have hlt_iff : i.val < step + 1 ↔ i.val < step := by omega
            simp only [hlt_iff]
            exact (hval1 x ba bb hx hva hvb i).mono hx h2.2.1
      · simp only [hj, ↓reduceDIte]
        refine ⟨hwf1, hext1, by omega, hlt1, fun x ba bb hx hva hvb i => ?_⟩
        have hlt_iff : i.val < step + 1 ↔ i.val < step := by omega
        simp only [hlt_iff]
        exact hval1 x ba bb hx hva hvb i

private def gEvalMaskFrom {t L : Nat} (n : Nat) (gs : List CGate) (baseB : Fin L → Nat)
    (B : Fin t → Fin L → Nat) (mask : Fin (2 ^ t)) : Nat → List CGate × (Fin L → Nat)
  | 0 => (gs, baseB)
  | j + 1 =>
      let r1 := gEvalMaskFrom n gs baseB B mask j
      if hj : j < t then
        if mask.val.testBit j then
          gXorVecFrom n r1.1 r1.2 (B ⟨j, hj⟩) L
        else r1
      else r1

private lemma gEvalMaskFrom_spec {t L : Nat} {n : Nat} {gs : List CGate}
    (baseB : Fin L → Nat) (B : Fin t → Fin L → Nat) (mask : Fin (2 ^ t))
    (hwf : WF n gs) (hbase : ∀ c, baseB c < n + gs.length) (hB : ∀ i c, B i c < n + gs.length) :
    ∀ step : Nat,
      WF n (gEvalMaskFrom n gs baseB B mask step).1 ∧ Ext gs (gEvalMaskFrom n gs baseB B mask step).1 ∧
      (gEvalMaskFrom n gs baseB B mask step).1.length ≤ gs.length + step * (4 * L) ∧
      (∀ c, (gEvalMaskFrom n gs baseB B mask step).2 c < n + (gEvalMaskFrom n gs baseB B mask step).1.length) ∧
      ∀ (x : List Bool) (bbase : Fin L → Bool) (bB : Fin t → Fin L → Bool), x.length = n →
        (∀ c, Val n gs x (baseB c) (bbase c)) → (∀ i c, Val n gs x (B i c) (bB i c)) →
        ∀ c : Fin L, Val n (gEvalMaskFrom n gs baseB B mask step).1 x
          ((gEvalMaskFrom n gs baseB B mask step).2 c) (evalMaskFrom bB mask step bbase c) := by
  intro step
  induction step with
  | zero =>
      exact ⟨hwf, Ext.refl gs, by simp [gEvalMaskFrom], hbase, fun _ _ _ _ hvb _ c => hvb c⟩
  | succ step ih =>
      rcases ih with ⟨hwf1, hext1, hlen1, hlt1, hval1⟩
      simp only [gEvalMaskFrom, evalMaskFrom]
      by_cases hj : step < t
      · simp only [hj, ↓reduceDIte]
        set r1 := gEvalMaskFrom n gs baseB B mask step
        cases htb : mask.val.testBit step
        · simp only [Bool.false_eq_true, ↓reduceIte]
          refine ⟨hwf1, hext1, ?_, hlt1, fun x bbase bB hx hvb hvB c => ?_⟩
          · have : step * (4 * L) ≤ (step + 1) * (4 * L) := Nat.mul_le_mul_right _ (by omega)
            omega
          · simpa [condXorVec] using hval1 x bbase bB hx hvb hvB c
        · simp only [↓reduceIte]
          have hle1 : gs.length ≤ r1.1.length := hext1.len_le
          have h2 := gXorVecFrom_spec r1.2 (B ⟨step, hj⟩) hwf1 hlt1 (fun c => by have := hB ⟨step, hj⟩ c; omega) L
          refine ⟨h2.1, hext1.trans h2.2.1, ?_, h2.2.2.2.1, fun x bbase bB hx hvb hvB c => ?_⟩
          · have hmul : (step + 1) * (4 * L) = step * (4 * L) + 4 * L := Nat.succ_mul _ _
            omega
          · have v2 := h2.2.2.2.2 x _ (bB ⟨step, hj⟩) hx (hval1 x bbase bB hx hvb hvB)
              (fun i => (hvB ⟨step, hj⟩ i).mono hx hext1) c
            simpa [c.isLt, condXorVec] using v2
      · simp only [hj, ↓reduceDIte]
        refine ⟨hwf1, hext1, ?_, hlt1, hval1⟩
        have : step * (4 * L) ≤ (step + 1) * (4 * L) := Nat.mul_le_mul_right _ (by omega)
        omega

private def gMixY (n k : Nat) (hk : 0 < k) (d t : Nat) (gs : List CGate)
    (w name : Fin k → Nat) (a : Fin k) : List CGate × Nat :=
  let rotW := fun (slot : Fin k) => w (ix k hk (slot.val + k - t % k))
  let r1 := gXor n gs (rotW a) (name a)
  let a1 := ix k hk (a.val + d)
  let r2 := gXor n r1.1 (rotW a1) (name a1)
  let a2 := ix k hk (a.val + k - d % k)
  let r3 := gXor n r2.1 (rotW a2) (name a2)
  let r4 := gXor n r3.1 r1.2 r2.2
  gXor n r4.1 r4.2 r3.2

private lemma gMixY_spec {n k : Nat} (hk : 0 < k) (d t : Nat) {gs : List CGate}
    (w name : Fin k → Nat) (a : Fin k)
    (hwf : WF n gs) (hw : ∀ j, w j < n + gs.length) (hname : ∀ j, name j < n + gs.length) :
    WF n (gMixY n k hk d t gs w name a).1 ∧ Ext gs (gMixY n k hk d t gs w name a).1 ∧
    (gMixY n k hk d t gs w name a).1.length = gs.length + 20 ∧
    (gMixY n k hk d t gs w name a).2 < n + (gMixY n k hk d t gs w name a).1.length ∧
    ∀ (x : List Bool) (bw bname : Fin k → Bool), x.length = n →
      (∀ j, Val n gs x (w j) (bw j)) → (∀ j, Val n gs x (name j) (bname j)) →
      let z := fun j : Fin k => xor (rotB k hk t bw j) (bname j)
      Val n (gMixY n k hk d t gs w name a).1 x (gMixY n k hk d t gs w name a).2
        (xor (xor (z a) (z (ix k hk (a.val + d)))) (z (ix k hk (a.val + k - d % k)))) := by
  unfold gMixY
  have h1 := gXor_spec hwf (w (ix k hk (a.val + k - t % k))) (name a) (hw _) (hname _)
  set r1 := gXor n gs (w (ix k hk (a.val + k - t % k))) (name a)
  set a1 := ix k hk (a.val + d)
  have h2 := gXor_spec h1.1 (w (ix k hk (a1.val + k - t % k))) (name a1) (by have := hw (ix k hk (a1.val + k - t % k)); omega) (by have := hname a1; omega)
  set r2 := gXor n r1.1 (w (ix k hk (a1.val + k - t % k))) (name a1)
  set a2 := ix k hk (a.val + k - d % k)
  have h3 := gXor_spec h2.1 (w (ix k hk (a2.val + k - t % k))) (name a2) (by have := hw (ix k hk (a2.val + k - t % k)); omega) (by have := hname a2; omega)
  set r3 := gXor n r2.1 (w (ix k hk (a2.val + k - t % k))) (name a2)
  have h4 := gXor_spec h3.1 r1.2 r2.2 (by have := h1.2.2.2.1; omega) (by have := h2.2.2.2.1; omega)
  set r4 := gXor n r3.1 r1.2 r2.2
  have h5 := gXor_spec h4.1 r4.2 r3.2 h4.2.2.2.1 (by have := h3.2.2.2.1; omega)
  set r5 := gXor n r4.1 r4.2 r3.2
  refine ⟨h5.1, h1.2.1.trans (h2.2.1.trans (h3.2.1.trans (h4.2.1.trans h5.2.1))),
    by omega, h5.2.2.2.1, fun x bw bname hx hvw hvn => ?_⟩
  have v1 := h1.2.2.2.2 x _ _ hx (hvw _) (hvn _)
  have v2 := h2.2.2.2.2 x _ _ hx ((hvw _).mono hx h1.2.1) ((hvn _).mono hx h1.2.1)
  have v3 := h3.2.2.2.2 x _ _ hx ((hvw _).mono hx (h1.2.1.trans h2.2.1)) ((hvn _).mono hx (h1.2.1.trans h2.2.1))
  have v4 := h4.2.2.2.2 x _ _ hx (v1.mono hx (h2.2.1.trans h3.2.1)) (v2.mono hx h3.2.1)
  exact h5.2.2.2.2 x _ _ hx v4 (v3.mono hx h4.2.1)

private def gRunB (n k : Nat) (hk : 0 < k) (d t f : Nat) (gs : List CGate)
    (w name c : Fin k → Nat) (atOut : Fin k) : List CGate × Nat :=
  let r1 := gMixY n k hk d t gs w name atOut
  let r2 := gMixY n k hk d t r1.1 w name (ix k hk (atOut.val + 1))
  let r3 := gMixY n k hk d t r2.1 w name (ix k hk (atOut.val + 2))
  let r4 := gNot n r3.1 r2.2
  let r5 := gAnd n r4.1 r4.2 r3.2
  let r6 := gXor n r5.1 r1.2 r5.2
  let r7 := gXor n r6.1 r6.2 (w (ix k hk (atOut.val + k - f % k)))
  gXor n r7.1 r7.2 (c atOut)

private lemma gRunB_spec {n k : Nat} (hk : 0 < k) (d t f : Nat) {gs : List CGate}
    (w name c : Fin k → Nat) (atOut : Fin k)
    (hwf : WF n gs) (hw : ∀ j, w j < n + gs.length)
    (hname : ∀ j, name j < n + gs.length) (hc : ∀ j, c j < n + gs.length) :
    WF n (gRunB n k hk d t f gs w name c atOut).1 ∧ Ext gs (gRunB n k hk d t f gs w name c atOut).1 ∧
    (gRunB n k hk d t f gs w name c atOut).1.length = gs.length + 74 ∧
    (gRunB n k hk d t f gs w name c atOut).2 < n + (gRunB n k hk d t f gs w name c atOut).1.length ∧
    ∀ (x : List Bool) (bw bname bc : Fin k → Bool), x.length = n →
      (∀ j, Val n gs x (w j) (bw j)) → (∀ j, Val n gs x (name j) (bname j)) →
      (∀ j, Val n gs x (c j) (bc j)) →
      Val n (gRunB n k hk d t f gs w name c atOut).1 x (gRunB n k hk d t f gs w name c atOut).2
        (runB k hk d t f bw bname bc atOut) := by
  unfold gRunB
  have h1 := gMixY_spec hk d t w name atOut hwf hw hname
  set r1 := gMixY n k hk d t gs w name atOut
  have h2 := gMixY_spec hk d t w name (ix k hk (atOut.val + 1)) h1.1
    (fun j => by have := hw j; omega) (fun j => by have := hname j; omega)
  set r2 := gMixY n k hk d t r1.1 w name (ix k hk (atOut.val + 1))
  have h3 := gMixY_spec hk d t w name (ix k hk (atOut.val + 2)) h2.1
    (fun j => by have := hw j; omega) (fun j => by have := hname j; omega)
  set r3 := gMixY n k hk d t r2.1 w name (ix k hk (atOut.val + 2))
  have h4 := gNot_spec h3.1 r2.2 (by have := h2.2.2.2.1; omega)
  set r4 := gNot n r3.1 r2.2
  have h5 := gAnd_spec h4.1 r4.2 r3.2 h4.2.2.2.1 (by have := h3.2.2.2.1; omega)
  set r5 := gAnd n r4.1 r4.2 r3.2
  have h6 := gXor_spec h5.1 r1.2 r5.2 (by have := h1.2.2.2.1; omega) h5.2.2.2.1
  set r6 := gXor n r5.1 r1.2 r5.2
  have h7 := gXor_spec h6.1 r6.2 (w (ix k hk (atOut.val + k - f % k))) h6.2.2.2.1
    (by have := hw (ix k hk (atOut.val + k - f % k)); omega)
  set r7 := gXor n r6.1 r6.2 (w (ix k hk (atOut.val + k - f % k)))
  have h8 := gXor_spec h7.1 r7.2 (c atOut) h7.2.2.2.1 (by have := hc atOut; omega)
  set r8 := gXor n r7.1 r7.2 (c atOut)
  have hext_all := h1.2.1.trans (h2.2.1.trans (h3.2.1.trans (h4.2.1.trans (h5.2.1.trans (h6.2.1.trans (h7.2.1.trans h8.2.1))))))
  refine ⟨h8.1, hext_all, by omega, h8.2.2.2.1, fun x bw bname bc hx hvw hvn hvc => ?_⟩
  have v1 := h1.2.2.2.2 x bw bname hx hvw hvn
  have v2 := h2.2.2.2.2 x bw bname hx (fun j => (hvw j).mono hx h1.2.1) (fun j => (hvn j).mono hx h1.2.1)
  have v3 := h3.2.2.2.2 x bw bname hx (fun j => (hvw j).mono hx (h1.2.1.trans h2.2.1)) (fun j => (hvn j).mono hx (h1.2.1.trans h2.2.1))
  have v4 := h4.2.2.2.2 x _ hx (v2.mono hx h3.2.1)
  have v5 := h5.2.2.2.2 x _ _ hx v4 (v3.mono hx h4.2.1)
  have v6 := h6.2.2.2.2 x _ _ hx (v1.mono hx (h2.2.1.trans (h3.2.1.trans (h4.2.1.trans h5.2.1)))) v5
  have v7 := h7.2.2.2.2 x _ _ hx v6 ((hvw _).mono hx (h1.2.1.trans (h2.2.1.trans (h3.2.1.trans (h4.2.1.trans (h5.2.1.trans h6.2.1))))))
  exact h8.2.2.2.2 x _ _ hx v7 ((hvc _).mono hx (h1.2.1.trans (h2.2.1.trans (h3.2.1.trans (h4.2.1.trans (h5.2.1.trans (h6.2.1.trans h7.2.1)))))))

private def gReconstructFrom (n k s : Nat) (hk : 0 < k) (row col : Fin k → Bool)
    (u v cr cc : Fin k → Nat) (c0 : Nat) (gs : List CGate) (β : Fin k → Nat) :
    Nat → List CGate × (Fin k → Nat)
  | 0 => (gs, β)
  | d + 1 =>
      let r1 := gReconstructFrom n k s hk row col u v cr cc c0 gs β d
      let pVal := k - 1 - d
      if hp : pVal < k then
        let p : Fin k := ⟨pVal, hp⟩
        let α0 : Fin k → Nat := fun j => if j = p then c0 else r1.2 j
        let unSh : Fin k → Nat := fun j => α0 (ix k hk (j.val + k - s % k))
        if row p = true ∧ p.val + 4 < k then
          let r2 := gRunB n k hk 1 1 0 r1.1 unSh u cr (ix k hk (s + p.val + 2))
          (r2.1, fun j => if j = p then r2.2 else r1.2 j)
        else if col p = true ∧ p.val + 6 < k then
          let r2 := gRunB n k hk 2 3 4 r1.1 unSh v cc (ix k hk (s + p.val + 5))
          (r2.1, fun j => if j = p then r2.2 else r1.2 j)
        else r1
      else r1

private lemma gReconstructFrom_spec {n k s : Nat} (hk : 0 < k) (row col : Fin k → Bool)
    (u v cr cc β : Fin k → Nat) (c0 : Nat) {gs : List CGate}
    (hwf : WF n gs) (hc0 : c0 < n + gs.length)
    (hu : ∀ j, u j < n + gs.length) (hv : ∀ j, v j < n + gs.length)
    (hcr : ∀ j, cr j < n + gs.length) (hcc : ∀ j, cc j < n + gs.length)
    (hβ : ∀ j, β j < n + gs.length) :
    ∀ d : Nat,
      WF n (gReconstructFrom n k s hk row col u v cr cc c0 gs β d).1 ∧
      Ext gs (gReconstructFrom n k s hk row col u v cr cc c0 gs β d).1 ∧
      (gReconstructFrom n k s hk row col u v cr cc c0 gs β d).1.length ≤ gs.length + 74 * d ∧
      (∀ j, (gReconstructFrom n k s hk row col u v cr cc c0 gs β d).2 j <
        n + (gReconstructFrom n k s hk row col u v cr cc c0 gs β d).1.length) ∧
      ∀ (x : List Bool) (bu bv bcr bcc bβ : Fin k → Bool), x.length = n →
        Val n gs x c0 false →
        (∀ j, Val n gs x (u j) (bu j)) → (∀ j, Val n gs x (v j) (bv j)) →
        (∀ j, Val n gs x (cr j) (bcr j)) → (∀ j, Val n gs x (cc j) (bcc j)) →
        (∀ j, Val n gs x (β j) (bβ j)) →
        ∀ j : Fin k, Val n (gReconstructFrom n k s hk row col u v cr cc c0 gs β d).1 x
          ((gReconstructFrom n k s hk row col u v cr cc c0 gs β d).2 j)
          (reconstructFrom k s hk row col bu bv bcr bcc bβ d j) := by
  intro d
  induction d with
  | zero =>
      exact ⟨hwf, Ext.refl gs, by simp [gReconstructFrom], hβ,
        fun _ _ _ _ _ _ _ _ _ _ _ _ hvβ j => hvβ j⟩
  | succ d ih =>
      rcases ih with ⟨hwf1, hext1, hlen1, hlt1, hval1⟩
      simp only [gReconstructFrom, reconstructFrom]
      by_cases hp : k - 1 - d < k
      · simp only [hp, ↓reduceDIte]
        set r1 := gReconstructFrom n k s hk row col u v cr cc c0 gs β d
        have hle1 : gs.length ≤ r1.1.length := hext1.len_le
        split_ifs with h1 h2c
        · dsimp only
          set p : Fin k := ⟨k - 1 - d, hp⟩
          have h2 := gRunB_spec hk 1 1 0
            (fun j => if ix k hk (j.val + k - s % k) = p then c0 else r1.2 (ix k hk (j.val + k - s % k)))
            u cr (ix k hk (s + p.val + 2)) hwf1
            (fun j => by split_ifs; omega; exact hlt1 _)
            (fun j => by have := hu j; omega) (fun j => by have := hcr j; omega)
          set r2 := gRunB n k hk 1 1 0 r1.1
            (fun j => if ix k hk (j.val + k - s % k) = p then c0 else r1.2 (ix k hk (j.val + k - s % k)))
            u cr (ix k hk (s + p.val + 2))
          refine ⟨h2.1, hext1.trans h2.2.1, by omega, ?_, ?_⟩
          · intro j
            by_cases hj : j = p
            · simp only [hj, ↓reduceIte]; exact h2.2.2.2.1
            · simp only [hj, ↓reduceIte]; have := hlt1 j; omega
          · intro x bu bv bcr bcc bβ hx hvc0 hvu hvv hvcr hvcc hvβ j
            have v1 := hval1 x bu bv bcr bcc bβ hx hvc0 hvu hvv hvcr hvcc hvβ
            by_cases hj : j = p
            · subst hj
              simp only [↓reduceIte, setAt]
              refine h2.2.2.2.2 x (unShift k s hk (setAt (reconstructFrom k s hk row col bu bv bcr bcc bβ d) p false))
                bu bcr hx ?_ (fun i => (hvu i).mono hx hext1) (fun i => (hvcr i).mono hx hext1)
              intro i
              dsimp only [unShift, setAt]
              split_ifs
              · exact hvc0.mono hx hext1
              · exact v1 _
            · simp only [hj, ↓reduceIte, setAt]
              exact (v1 j).mono hx h2.2.1
        · dsimp only
          set p : Fin k := ⟨k - 1 - d, hp⟩
          have h2 := gRunB_spec hk 2 3 4
            (fun j => if ix k hk (j.val + k - s % k) = p then c0 else r1.2 (ix k hk (j.val + k - s % k)))
            v cc (ix k hk (s + p.val + 5)) hwf1
            (fun j => by split_ifs; omega; exact hlt1 _)
            (fun j => by have := hv j; omega) (fun j => by have := hcc j; omega)
          set r2 := gRunB n k hk 2 3 4 r1.1
            (fun j => if ix k hk (j.val + k - s % k) = p then c0 else r1.2 (ix k hk (j.val + k - s % k)))
            v cc (ix k hk (s + p.val + 5))
          refine ⟨h2.1, hext1.trans h2.2.1, by omega, ?_, ?_⟩
          · intro j
            by_cases hj : j = p
            · simp only [hj, ↓reduceIte]; exact h2.2.2.2.1
            · simp only [hj, ↓reduceIte]; have := hlt1 j; omega
          · intro x bu bv bcr bcc bβ hx hvc0 hvu hvv hvcr hvcc hvβ j
            have v1 := hval1 x bu bv bcr bcc bβ hx hvc0 hvu hvv hvcr hvcc hvβ
            by_cases hj : j = p
            · subst hj
              simp only [↓reduceIte, setAt]
              refine h2.2.2.2.2 x (unShift k s hk (setAt (reconstructFrom k s hk row col bu bv bcr bcc bβ d) p false))
                bv bcc hx ?_ (fun i => (hvv i).mono hx hext1) (fun i => (hvcc i).mono hx hext1)
              intro i
              dsimp only [unShift, setAt]
              split_ifs
              · exact hvc0.mono hx hext1
              · exact v1 _
            · simp only [hj, ↓reduceIte, setAt]
              exact (v1 j).mono hx h2.2.1
        · exact ⟨hwf1, hext1, by omega, hlt1, hval1⟩
      · simp only [hp, ↓reduceDIte]
        exact ⟨hwf1, hext1, by omega, hlt1, hval1⟩

private def gPassAllFrom (n k s : Nat) (hk : 0 < k) (row col : Fin k → Bool)
    (u v cr cc α : Fin k → Nat) (c1 : Nat) (gs : List CGate) : Nat → List CGate × Nat
  | 0 => (gs, c1)
  | j + 1 =>
      let r1 := gPassAllFrom n k s hk row col u v cr cc α c1 gs j
      if hj : j < k then
        let p : Fin k := ⟨j, hj⟩
        let unSh : Fin k → Nat := fun i => α (ix k hk (i.val + k - s % k))
        let r2 :=
          if row p then
            let ra := gRunB n k hk 1 1 0 r1.1 unSh u cr (ix k hk (s + p.val + 2))
            let rb := gNot n ra.1 ra.2
            gAnd n rb.1 r1.2 rb.2
          else r1
        if col p then
          let rc := gRunB n k hk 2 3 4 r2.1 unSh v cc (ix k hk (s + p.val + 5))
          let rd := gNot n rc.1 rc.2
          gAnd n rd.1 r2.2 rd.2
        else r2
      else r1

private lemma gPassAllFrom_spec {n k s : Nat} (hk : 0 < k) (row col : Fin k → Bool)
    (u v cr cc α : Fin k → Nat) (c1 : Nat) {gs : List CGate}
    (hwf : WF n gs) (hc1 : c1 < n + gs.length)
    (hu : ∀ j, u j < n + gs.length) (hv : ∀ j, v j < n + gs.length)
    (hcr : ∀ j, cr j < n + gs.length) (hcc : ∀ j, cc j < n + gs.length)
    (hα : ∀ j, α j < n + gs.length) :
    ∀ step : Nat,
      WF n (gPassAllFrom n k s hk row col u v cr cc α c1 gs step).1 ∧
      Ext gs (gPassAllFrom n k s hk row col u v cr cc α c1 gs step).1 ∧
      (gPassAllFrom n k s hk row col u v cr cc α c1 gs step).1.length ≤ gs.length + 152 * step ∧
      (gPassAllFrom n k s hk row col u v cr cc α c1 gs step).2 <
        n + (gPassAllFrom n k s hk row col u v cr cc α c1 gs step).1.length ∧
      ∀ (x : List Bool) (bu bv bcr bcc bα : Fin k → Bool), x.length = n →
        Val n gs x c1 true →
        (∀ j, Val n gs x (u j) (bu j)) → (∀ j, Val n gs x (v j) (bv j)) →
        (∀ j, Val n gs x (cr j) (bcr j)) → (∀ j, Val n gs x (cc j) (bcc j)) →
        (∀ j, Val n gs x (α j) (bα j)) →
        Val n (gPassAllFrom n k s hk row col u v cr cc α c1 gs step).1 x
          (gPassAllFrom n k s hk row col u v cr cc α c1 gs step).2
          (allFinFrom (fun p : Fin k =>
            (!row p || !probeRowB k s hk bu bcr bα p) &&
            (!col p || !probeColB k s hk bv bcc bα p)) step) := by
  intro step
  induction step with
  | zero =>
      exact ⟨hwf, Ext.refl gs, by simp [gPassAllFrom], hc1,
        fun _ _ _ _ _ _ _ hvc1 _ _ _ _ _ => hvc1⟩
  | succ step ih =>
      rcases ih with ⟨hwf1, hext1, hlen1, hlt1, hval1⟩
      simp only [gPassAllFrom, allFinFrom]
      by_cases hj : step < k
      · simp only [hj, ↓reduceDIte]
        set r1 := gPassAllFrom n k s hk row col u v cr cc α c1 gs step
        let p : Fin k := ⟨step, hj⟩
        have hle1 : gs.length ≤ r1.1.length := hext1.len_le
        let unSh : Fin k → Nat := fun i => α (ix k hk (i.val + k - s % k))
        set r2 :=
          if row p then
            let ra := gRunB n k hk 1 1 0 r1.1 unSh u cr (ix k hk (s + p.val + 2))
            let rb := gNot n ra.1 ra.2
            gAnd n rb.1 r1.2 rb.2
          else r1
        have hrow_step :
            WF n r2.1 ∧ Ext r1.1 r2.1 ∧ r2.1.length ≤ r1.1.length + 76 ∧ r2.2 < n + r2.1.length ∧
            ∀ (x : List Bool) (bu bv bcr bcc bα : Fin k → Bool), x.length = n →
              Val n gs x c1 true →
              (∀ j, Val n gs x (u j) (bu j)) → (∀ j, Val n gs x (v j) (bv j)) →
              (∀ j, Val n gs x (cr j) (bcr j)) → (∀ j, Val n gs x (cc j) (bcc j)) →
              (∀ j, Val n gs x (α j) (bα j)) →
              Val n r2.1 x r2.2
                (allFinFrom (fun p0 : Fin k =>
                  (!row p0 || !probeRowB k s hk bu bcr bα p0) &&
                  (!col p0 || !probeColB k s hk bv bcc bα p0)) step &&
                  (!row p || !probeRowB k s hk bu bcr bα p)) := by
          dsimp only [r2]
          cases hrp : row p
          · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_or, Bool.and_true]
            exact ⟨hwf1, Ext.refl _, by omega, hlt1, hval1⟩
          · simp only [↓reduceIte, Bool.not_true, Bool.false_or]
            have ha := gRunB_spec hk 1 1 0 unSh u cr (ix k hk (s + p.val + 2)) hwf1
              (fun j => by dsimp only [unSh]; have := hα (ix k hk (j.val + k - s % k)); omega) (fun j => by have := hu j; omega) (fun j => by have := hcr j; omega)
            set ra := gRunB n k hk 1 1 0 r1.1 unSh u cr (ix k hk (s + p.val + 2))
            have hb := gNot_spec ha.1 ra.2 ha.2.2.2.1
            set rb := gNot n ra.1 ra.2
            have hc := gAnd_spec hb.1 r1.2 rb.2 (by omega) hb.2.2.2.1
            refine ⟨hc.1, ha.2.1.trans (hb.2.1.trans hc.2.1), by omega, hc.2.2.2.1,
              fun x bu bv bcr bcc bα hx hvc1 hvu hvv hvcr hvcc hvα => ?_⟩
            have v1 := hval1 x bu bv bcr bcc bα hx hvc1 hvu hvv hvcr hvcc hvα
            have va := ha.2.2.2.2 x (unShift k s hk bα) bu bcr hx
              (fun i => (hvα _).mono hx hext1) (fun i => (hvu i).mono hx hext1) (fun i => (hvcr i).mono hx hext1)
            have vb := hb.2.2.2.2 x _ hx va
            simpa [probeRowB] using hc.2.2.2.2 x _ _ hx (v1.mono hx (ha.2.1.trans hb.2.1)) vb
        rcases hrow_step with ⟨hwf2, hext2, hlen2, hlt2, hval2⟩
        have hle2 : gs.length ≤ r2.1.length := (hext1.trans hext2).len_le
        cases hcp : col p
        · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_or, Bool.and_true]
          exact ⟨hwf2, hext1.trans hext2, by omega, hlt2, fun x bu bv bcr bcc bα hx hvc1 hvu hvv hvcr hvcc hvα => by
            simpa [Bool.and_assoc] using hval2 x bu bv bcr bcc bα hx hvc1 hvu hvv hvcr hvcc hvα⟩
        · simp only [↓reduceIte, Bool.not_true, Bool.false_or]
          have ha := gRunB_spec hk 2 3 4 unSh v cc (ix k hk (s + p.val + 5)) hwf2
            (fun j => by dsimp only [unSh]; have := hα (ix k hk (j.val + k - s % k)); omega) (fun j => by have := hv j; omega) (fun j => by have := hcc j; omega)
          set rc := gRunB n k hk 2 3 4 r2.1 unSh v cc (ix k hk (s + p.val + 5))
          have hb := gNot_spec ha.1 rc.2 ha.2.2.2.1
          set rd := gNot n rc.1 rc.2
          have hc := gAnd_spec hb.1 r2.2 rd.2 (by omega) hb.2.2.2.1
          refine ⟨hc.1, (hext1.trans hext2).trans (ha.2.1.trans (hb.2.1.trans hc.2.1)), by omega,
            hc.2.2.2.1, fun x bu bv bcr bcc bα hx hvc1 hvu hvv hvcr hvcc hvα => ?_⟩
          have v2 := hval2 x bu bv bcr bcc bα hx hvc1 hvu hvv hvcr hvcc hvα
          have va := ha.2.2.2.2 x (unShift k s hk bα) bv bcc hx
            (fun i => (hvα _).mono hx (hext1.trans hext2))
            (fun i => (hvv i).mono hx (hext1.trans hext2))
            (fun i => (hvcc i).mono hx (hext1.trans hext2))
          have vb := hb.2.2.2.2 x _ hx va
          have vc := hc.2.2.2.2 x _ _ hx (v2.mono hx (ha.2.1.trans hb.2.1)) vb
          simpa [Bool.and_assoc, probeColB] using vc
      · simp only [hj, ↓reduceDIte]
        exact ⟨hwf1, hext1, by omega, hlt1, hval1⟩

private def gAllNotFrom {L : Nat} (n : Nat) (gs : List CGate) (v : Fin L → Nat) (c1 : Nat) :
    Nat → List CGate × Nat
  | 0 => (gs, c1)
  | j + 1 =>
      let r1 := gAllNotFrom n gs v c1 j
      if hj : j < L then
        let r2 := gNot n r1.1 (v ⟨j, hj⟩)
        gAnd n r2.1 r1.2 r2.2
      else r1

private lemma gAllNotFrom_spec {L : Nat} {n : Nat} {gs : List CGate} (v : Fin L → Nat) (c1 : Nat)
    (hwf : WF n gs) (hc1 : c1 < n + gs.length) (hv : ∀ i, v i < n + gs.length) :
    ∀ step : Nat,
      WF n (gAllNotFrom n gs v c1 step).1 ∧ Ext gs (gAllNotFrom n gs v c1 step).1 ∧
      (gAllNotFrom n gs v c1 step).1.length ≤ gs.length + 2 * step ∧
      (gAllNotFrom n gs v c1 step).2 < n + (gAllNotFrom n gs v c1 step).1.length ∧
      ∀ (x : List Bool) (bv : Fin L → Bool), x.length = n →
        Val n gs x c1 true → (∀ i, Val n gs x (v i) (bv i)) →
        Val n (gAllNotFrom n gs v c1 step).1 x (gAllNotFrom n gs v c1 step).2
          (allFinFrom (fun j : Fin L => !bv j) step) := by
  intro step
  induction step with
  | zero =>
      exact ⟨hwf, Ext.refl gs, by simp [gAllNotFrom], hc1, fun _ _ _ hvc1 _ => hvc1⟩
  | succ step ih =>
      rcases ih with ⟨hwf1, hext1, hlen1, hlt1, hval1⟩
      simp only [gAllNotFrom, allFinFrom]
      by_cases hj : step < L
      · simp only [hj, ↓reduceDIte]
        set r1 := gAllNotFrom n gs v c1 step
        have hle1 : gs.length ≤ r1.1.length := hext1.len_le
        have h2 := gNot_spec hwf1 (v ⟨step, hj⟩) (by have := hv ⟨step, hj⟩; omega)
        set r2 := gNot n r1.1 (v ⟨step, hj⟩)
        have h3 := gAnd_spec h2.1 r1.2 r2.2 (by omega) h2.2.2.2.1
        refine ⟨h3.1, hext1.trans (h2.2.1.trans h3.2.1), by omega, h3.2.2.2.1,
          fun x bv hx hvc1 hvv => ?_⟩
        have v1 := hval1 x bv hx hvc1 hvv
        have v2 := h2.2.2.2.2 x (bv ⟨step, hj⟩) hx ((hvv ⟨step, hj⟩).mono hx hext1)
        exact h3.2.2.2.2 x _ _ hx (v1.mono hx h2.2.1) v2
      · simp only [hj, ↓reduceDIte]
        exact ⟨hwf1, hext1, by omega, hlt1, hval1⟩

private def carryBit (acc : Nat) (b : Bool) : Nat → Bool
  | 0 => b
  | j + 1 => acc.testBit j && carryBit acc b j

private lemma carryBit_succ_shift (acc : Nat) (b : Bool) :
    ∀ j : Nat, carryBit acc b (j + 1) = carryBit (acc / 2) (acc.testBit 0 && b) j := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [carryBit, Nat.testBit_succ, ih]; rfl

private lemma nat_add_bool_testBit :
    ∀ (j acc : Nat) (b : Bool),
      (acc + if b then 1 else 0).testBit j = xor (acc.testBit j) (carryBit acc b j) := by
  intro j
  induction j with
  | zero =>
      intro acc b
      cases b
      · simp [carryBit]
      · simp only [↓reduceIte, carryBit, Nat.testBit_zero, Bool.xor_true]
        have hmod : acc % 2 = 0 ∨ acc % 2 = 1 := by omega
        rcases hmod with h | h <;> simp [h, Nat.add_mod]
  | succ j ih =>
      intro acc b
      have hdiv : (acc + if b then 1 else 0) / 2 = acc / 2 + if (acc.testBit 0 && b) then 1 else 0 := by
        cases b
        · simp
        · simp only [↓reduceIte, Bool.and_true, Nat.testBit_zero]
          have hmod : acc % 2 = 0 ∨ acc % 2 = 1 := by omega
          rcases hmod with h | h <;> simp [h] <;> omega
      rw [Nat.testBit_succ, hdiv, ih (acc / 2) (acc.testBit 0 && b), ← carryBit_succ_shift, ← Nat.testBit_succ]

private def gIncFrom {W : Nat} (n : Nat) (gs : List CGate) (cnt : Fin W → Nat) (carryW : Nat) :
    Nat → List CGate × (Fin W → Nat) × Nat
  | 0 => (gs, cnt, carryW)
  | j + 1 =>
      let r1 := gIncFrom n gs cnt carryW j
      if hj : j < W then
        let idx : Fin W := ⟨j, hj⟩
        let r2 := gXor n r1.1 (r1.2.1 idx) r1.2.2
        let r3 := gAnd n r2.1 (r1.2.1 idx) r1.2.2
        (r3.1, fun i => if i = idx then r2.2 else r1.2.1 i, r3.2)
      else r1

private lemma gIncFrom_spec {W : Nat} {n : Nat} {gs : List CGate} (cnt : Fin W → Nat) (carryW : Nat)
    (hwf : WF n gs) (hcnt : ∀ i, cnt i < n + gs.length) (hc : carryW < n + gs.length) :
    ∀ step : Nat,
      WF n (gIncFrom n gs cnt carryW step).1 ∧ Ext gs (gIncFrom n gs cnt carryW step).1 ∧
      (gIncFrom n gs cnt carryW step).1.length ≤ gs.length + 5 * step ∧
      (∀ i, (gIncFrom n gs cnt carryW step).2.1 i < n + (gIncFrom n gs cnt carryW step).1.length) ∧
      (gIncFrom n gs cnt carryW step).2.2 < n + (gIncFrom n gs cnt carryW step).1.length ∧
      ∀ (x : List Bool) (acc : Nat) (b : Bool), x.length = n →
        (∀ i : Fin W, Val n gs x (cnt i) (acc.testBit i.val)) → Val n gs x carryW b →
        (∀ i : Fin W, Val n (gIncFrom n gs cnt carryW step).1 x ((gIncFrom n gs cnt carryW step).2.1 i)
          (if i.val < step then (acc + if b then 1 else 0).testBit i.val else acc.testBit i.val)) ∧
        Val n (gIncFrom n gs cnt carryW step).1 x (gIncFrom n gs cnt carryW step).2.2 (carryBit acc b (min step W)) := by
  intro step
  induction step with
  | zero =>
      exact ⟨hwf, Ext.refl gs, by simp [gIncFrom], hcnt, hc,
        fun _ _ _ _ hvc hvb => ⟨fun i => by simpa [gIncFrom] using hvc i, hvb⟩⟩
  | succ step ih =>
      rcases ih with ⟨hwf1, hext1, hlen1, hlt1, hltc1, hval1⟩
      simp only [gIncFrom]
      by_cases hj : step < W
      · simp only [hj, ↓reduceDIte]
        set r1 := gIncFrom n gs cnt carryW step
        set idx : Fin W := ⟨step, hj⟩
        have h2 := gXor_spec hwf1 (r1.2.1 idx) r1.2.2 (hlt1 idx) hltc1
        set r2 := gXor n r1.1 (r1.2.1 idx) r1.2.2
        have h3 := gAnd_spec h2.1 (r1.2.1 idx) r1.2.2 (by have := hlt1 idx; omega) (by omega)
        set r3 := gAnd n r2.1 (r1.2.1 idx) r1.2.2
        refine ⟨h3.1, hext1.trans (h2.2.1.trans h3.2.1), by omega, ?_, h3.2.2.2.1, ?_⟩
        · intro i
          by_cases hi : i = idx
          · simp only [hi, ↓reduceIte]; have := h2.2.2.2.1; omega
          · simp only [hi, ↓reduceIte]; have := hlt1 i; omega
        · intro x acc b hx hvc hvb
          rcases hval1 x acc b hx hvc hvb with ⟨v1, vc1⟩
          have hidx_v : Val n r1.1 x (r1.2.1 idx) (acc.testBit step) := by
            simpa [idx] using v1 idx
          have hmin1 : min step W = step := Nat.min_eq_left (by omega)
          have hmin2 : min (step + 1) W = step + 1 := Nat.min_eq_left (by omega)
          rw [hmin1] at vc1
          rw [hmin2]
          have v2 := h2.2.2.2.2 x (acc.testBit step) (carryBit acc b step) hx hidx_v vc1
          have v3 := h3.2.2.2.2 x (acc.testBit step) (carryBit acc b step) hx (hidx_v.mono hx h2.2.1) (vc1.mono hx h2.2.1)
          refine ⟨fun i => ?_, v3⟩
          by_cases hi : i = idx
          · subst hi
            simp only [↓reduceIte, idx, Nat.lt_succ_self]
            rw [nat_add_bool_testBit]
            exact v2.mono hx h3.2.1
          · simp only [hi, ↓reduceIte]
            have hne : i.val ≠ step := fun h => hi (Fin.ext h)
            have hlt_iff : i.val < step + 1 ↔ i.val < step := by omega
            simp only [hlt_iff]
            exact (v1 i).mono hx (h2.2.1.trans h3.2.1)
      · simp only [hj, ↓reduceDIte]
        refine ⟨hwf1, hext1, by omega, hlt1, hltc1, fun x acc b hx hvc hvb => ?_⟩
        rcases hval1 x acc b hx hvc hvb with ⟨v1, vc1⟩
        have hmin1 : min step W = W := Nat.min_eq_right (by omega)
        have hmin2 : min (step + 1) W = W := Nat.min_eq_right (by omega)
        rw [hmin1] at vc1
        rw [hmin2]
        refine ⟨fun i => ?_, vc1⟩
        have hlt_iff : i.val < step + 1 ↔ i.val < step := by omega
        simp only [hlt_iff]
        exact v1 i

private def gOneHotStep {K : Nat} (n : Nat) (gs : List CGate) (bitW c0 : Nat) (dp : Fin K → Nat) :
    Nat → List CGate × (Fin K → Nat)
  | 0 => (gs, dp)
  | c + 1 =>
      let r1 := gOneHotStep n gs bitW c0 dp c
      if hc : c < K then
        let idx : Fin K := ⟨c, hc⟩
        let prevW := if hc0 : c = 0 then c0 else dp ⟨c - 1, by omega⟩
        let r2 := gMux n r1.1 bitW prevW (dp idx)
        (r2.1, fun i => if i = idx then r2.2 else r1.2 i)
      else r1

private lemma gOneHotStep_spec {K : Nat} {n : Nat} {gs : List CGate} (bitW c0 : Nat) (dp : Fin K → Nat)
    (hwf : WF n gs) (hbit : bitW < n + gs.length) (hc0 : c0 < n + gs.length)
    (hdp : ∀ i, dp i < n + gs.length) :
    ∀ step : Nat,
      WF n (gOneHotStep n gs bitW c0 dp step).1 ∧ Ext gs (gOneHotStep n gs bitW c0 dp step).1 ∧
      (gOneHotStep n gs bitW c0 dp step).1.length ≤ gs.length + 4 * step ∧
      (∀ i, (gOneHotStep n gs bitW c0 dp step).2 i < n + (gOneHotStep n gs bitW c0 dp step).1.length) ∧
      ∀ (x : List Bool) (bb : Bool) (cnt : Nat), x.length = n →
        Val n gs x bitW bb → Val n gs x c0 false →
        (∀ i : Fin K, Val n gs x (dp i) (decide (cnt = i.val))) →
        ∀ i : Fin K, Val n (gOneHotStep n gs bitW c0 dp step).1 x ((gOneHotStep n gs bitW c0 dp step).2 i)
          (if i.val < step then decide (cnt + (if bb then 1 else 0) = i.val) else decide (cnt = i.val)) := by
  intro step
  induction step with
  | zero =>
      exact ⟨hwf, Ext.refl gs, by simp [gOneHotStep], hdp,
        fun _ _ _ _ _ _ hvdp i => by simpa [gOneHotStep] using hvdp i⟩
  | succ step ih =>
      rcases ih with ⟨hwf1, hext1, hlen1, hlt1, hval1⟩
      simp only [gOneHotStep]
      by_cases hc : step < K
      · simp only [hc, ↓reduceDIte]
        set r1 := gOneHotStep n gs bitW c0 dp step
        set idx : Fin K := ⟨step, hc⟩
        have hle1 : gs.length ≤ r1.1.length := hext1.len_le
        set prevW := if hc0 : step = 0 then c0 else dp ⟨step - 1, by omega⟩
        have hprev_lt : prevW < n + r1.1.length := by
          dsimp only [prevW]
          split_ifs
          · omega
          · have := hdp ⟨step - 1, by omega⟩; omega
        have h2 := gMux_spec hwf1 bitW prevW (dp idx) (by omega) hprev_lt (by have := hdp idx; omega)
        refine ⟨h2.1, hext1.trans h2.2.1, by omega, ?_, ?_⟩
        · intro i
          by_cases hi : i = idx
          · simp only [hi, ↓reduceIte]; exact h2.2.2.2.1
          · simp only [hi, ↓reduceIte]; have := hlt1 i; omega
        · intro x bb cnt hx hvbit hvc0 hvdp i
          by_cases hi : i = idx
          · subst hi
            simp only [↓reduceIte, idx, Nat.lt_succ_self]
            by_cases hs0 : step = 0
            · subst hs0
              have v2 := h2.2.2.2.2 x bb false (decide (cnt = 0)) hx
                (hvbit.mono hx hext1)
                (by simpa [prevW] using hvc0.mono hx hext1)
                ((hvdp ⟨0, hc⟩).mono hx hext1)
              have heq : (if bb then false else decide (cnt = 0)) = decide (cnt + (if bb then 1 else 0) = 0) := by
                cases bb <;> simp
              rwa [heq] at v2
            · have v2 := h2.2.2.2.2 x bb (decide (cnt = step - 1)) (decide (cnt = step)) hx
                (hvbit.mono hx hext1)
                (by simpa [prevW, hs0] using (hvdp ⟨step - 1, by omega⟩).mono hx hext1)
                ((hvdp ⟨step, hc⟩).mono hx hext1)
              have heq : (if bb then decide (cnt = step - 1) else decide (cnt = step)) =
                  decide (cnt + (if bb then 1 else 0) = step) := by
                cases bb
                · simp
                · simp only [↓reduceIte, decide_eq_decide]; omega
              rwa [heq] at v2
          · simp only [hi, ↓reduceIte]
            have hne : i.val ≠ step := fun h => hi (Fin.ext h)
            have hlt_iff : i.val < step + 1 ↔ i.val < step := by omega
            simp only [hlt_iff]
            exact (hval1 x bb cnt hx hvbit hvc0 hvdp i).mono hx h2.2.1
      · simp only [hc, ↓reduceDIte]
        refine ⟨hwf1, hext1, by omega, hlt1, fun x bb cnt hx hvbit hvc0 hvdp i => ?_⟩
        have hlt_iff : i.val < step + 1 ↔ i.val < step := by omega
        simp only [hlt_iff]
        exact hval1 x bb cnt hx hvbit hvc0 hvdp i

private def gOneHotFrom {L K : Nat} (n : Nat) (gs : List CGate) (bits : Fin L → Nat) (c0 c1 : Nat) :
    Nat → List CGate × (Fin K → Nat)
  | 0 => (gs, fun c => if c.val = 0 then c1 else c0)
  | j + 1 =>
      let r1 := gOneHotFrom n gs bits c0 c1 j
      if hj : j < L then
        gOneHotStep n r1.1 (bits ⟨j, hj⟩) c0 r1.2 K
      else r1

private lemma gOneHotFrom_spec {L K : Nat} {n : Nat} {gs : List CGate}
    (bits : Fin L → Nat) (c0 c1 : Nat)
    (hwf : WF n gs) (hc0 : c0 < n + gs.length) (hc1 : c1 < n + gs.length)
    (hbits : ∀ j, bits j < n + gs.length) :
    ∀ step : Nat,
      WF n (gOneHotFrom (K := K) n gs bits c0 c1 step).1 ∧
      Ext gs (gOneHotFrom (K := K) n gs bits c0 c1 step).1 ∧
      (gOneHotFrom (K := K) n gs bits c0 c1 step).1.length ≤ gs.length + step * (4 * K) ∧
      (∀ i, (gOneHotFrom (K := K) n gs bits c0 c1 step).2 i < n + (gOneHotFrom (K := K) n gs bits c0 c1 step).1.length) ∧
      ∀ (x : List Bool) (bb : Fin L → Bool), x.length = n →
        Val n gs x c0 false → Val n gs x c1 true → (∀ j, Val n gs x (bits j) (bb j)) →
        ∀ i : Fin K, Val n (gOneHotFrom (K := K) n gs bits c0 c1 step).1 x
          ((gOneHotFrom (K := K) n gs bits c0 c1 step).2 i)
          (decide ((Finset.univ.filter (fun j : Fin L => j.val < step ∧ bb j = true)).card = i.val)) := by
  intro step
  induction step with
  | zero =>
      refine ⟨hwf, Ext.refl gs, by simp [gOneHotFrom],
        fun c => by dsimp only [gOneHotFrom]; split_ifs <;> assumption,
        fun x bb _ hvc0 hvc1 _ i => ?_⟩
      have hemp : (Finset.univ.filter (fun j : Fin L => j.val < 0 ∧ bb j = true)).card = 0 := by simp
      rw [hemp]
      dsimp only [gOneHotFrom]
      by_cases hi : i.val = 0
      · simp [hi, hvc1]
      · have hne : ¬0 = i.val := fun h => hi h.symm
        simp [hi, hne, hvc0]
  | succ step ih =>
      rcases ih with ⟨hwf1, hext1, hlen1, hlt1, hval1⟩
      simp only [gOneHotFrom]
      by_cases hj : step < L
      · simp only [hj, ↓reduceDIte]
        set r1 := gOneHotFrom (K := K) n gs bits c0 c1 step
        have hle1 : gs.length ≤ r1.1.length := hext1.len_le
        have h2 := gOneHotStep_spec (bits ⟨step, hj⟩) c0 r1.2 hwf1
          (by have := hbits ⟨step, hj⟩; omega) (by omega) hlt1 K
        refine ⟨h2.1, hext1.trans h2.2.1, ?_, h2.2.2.2.1, fun x bb hx hvc0 hvc1 hvbits i => ?_⟩
        · have hmul : (step + 1) * (4 * K) = step * (4 * K) + 4 * K := Nat.succ_mul _ _
          omega
        · have v2 := h2.2.2.2.2 x (bb ⟨step, hj⟩)
            (Finset.univ.filter (fun j : Fin L => j.val < step ∧ bb j = true)).card hx
            ((hvbits ⟨step, hj⟩).mono hx hext1) (hvc0.mono hx hext1) (hval1 x bb hx hvc0 hvc1 hvbits) i
          simp only [i.isLt, ↓reduceIte] at v2
          have hcard : (Finset.univ.filter (fun j : Fin L => j.val < step + 1 ∧ bb j = true)).card =
              (Finset.univ.filter (fun j : Fin L => j.val < step ∧ bb j = true)).card +
                if bb ⟨step, hj⟩ then 1 else 0 := by
            set idx : Fin L := ⟨step, hj⟩
            cases hb : bb idx
            · simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
              congr 1; ext j
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              constructor
              · rintro ⟨hlt, hbj⟩
                refine ⟨?_, hbj⟩
                by_contra hge
                have : j = idx := Fin.ext (show j.val = step by omega)
                rw [this, hb] at hbj; cases hbj
              · rintro ⟨hlt, hbj⟩; exact ⟨by omega, hbj⟩
            · simp only [↓reduceIte]
              have hnot : idx ∉ Finset.univ.filter (fun j : Fin L => j.val < step ∧ bb j = true) := by
                simp [idx]
              have hfilt : Finset.univ.filter (fun j : Fin L => j.val < step + 1 ∧ bb j = true) =
                  insert idx (Finset.univ.filter (fun j : Fin L => j.val < step ∧ bb j = true)) := by
                ext j
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
                constructor
                · rintro ⟨hlt, hbj⟩
                  by_cases hje : j = idx
                  · exact Or.inl hje
                  · right; have : j.val ≠ step := fun h => hje (Fin.ext h); exact ⟨by omega, hbj⟩
                · rintro (rfl | ⟨hlt, hbj⟩)
                  · exact ⟨Nat.lt_succ_self step, hb⟩
                  · exact ⟨by omega, hbj⟩
              rw [hfilt, Finset.card_insert_of_notMem hnot]
          rw [hcard]
          exact v2
      · simp only [hj, ↓reduceDIte]
        refine ⟨hwf1, hext1, ?_, hlt1, fun x bb hx hvc0 hvc1 hvbits i => ?_⟩
        · have : step * (4 * K) ≤ (step + 1) * (4 * K) := Nat.mul_le_mul_right _ (by omega)
          omega
        · have heq : Finset.univ.filter (fun j : Fin L => j.val < step + 1 ∧ bb j = true) =
              Finset.univ.filter (fun j : Fin L => j.val < step ∧ bb j = true) := by
            ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            constructor <;> rintro ⟨hlt, hbj⟩ <;> exact ⟨by omega, hbj⟩
          rw [heq]
          exact hval1 x bb hx hvc0 hvc1 hvbits i

private def gShiftOne {K : Nat} (n : Nat) (gs : List CGate) (eqAct eqFull : Fin K → Nat) (c0 : Nat)
    (d : Fin K) : Nat → List CGate × Nat
  | 0 => (gs, c0)
  | a + 1 =>
      let r1 := gShiftOne n gs eqAct eqFull c0 d a
      if ha : a + d.val < K then
        let r2 := gAnd n r1.1 (eqAct ⟨a, by omega⟩) (eqFull ⟨a + d.val, ha⟩)
        gOr n r2.1 r1.2 r2.2
      else r1

private lemma gShiftOne_spec {K : Nat} {n : Nat} {gs : List CGate}
    (eqAct eqFull : Fin K → Nat) (c0 : Nat) (d : Fin K)
    (hwf : WF n gs) (hc0 : c0 < n + gs.length)
    (haW : ∀ i, eqAct i < n + gs.length) (hfW : ∀ i, eqFull i < n + gs.length) :
    ∀ step : Nat,
      WF n (gShiftOne n gs eqAct eqFull c0 d step).1 ∧ Ext gs (gShiftOne n gs eqAct eqFull c0 d step).1 ∧
      (gShiftOne n gs eqAct eqFull c0 d step).1.length ≤ gs.length + 2 * step ∧
      (gShiftOne n gs eqAct eqFull c0 d step).2 < n + (gShiftOne n gs eqAct eqFull c0 d step).1.length ∧
      ∀ (x : List Bool) (rA rF : Nat), x.length = n →
        Val n gs x c0 false →
        (∀ i : Fin K, Val n gs x (eqAct i) (decide (rA = i.val))) →
        (∀ i : Fin K, Val n gs x (eqFull i) (decide (rF = i.val))) →
        Val n (gShiftOne n gs eqAct eqFull c0 d step).1 x (gShiftOne n gs eqAct eqFull c0 d step).2
          (decide (rA < step ∧ rA + d.val < K ∧ rF = rA + d.val)) := by
  intro step
  induction step with
  | zero =>
      exact ⟨hwf, Ext.refl gs, by simp [gShiftOne], hc0,
        fun _ _ _ _ hvc0 _ _ => by simpa [gShiftOne] using hvc0⟩
  | succ step ih =>
      rcases ih with ⟨hwf1, hext1, hlen1, hlt1, hval1⟩
      simp only [gShiftOne]
      by_cases ha : step + d.val < K
      · simp only [ha, ↓reduceDIte]
        set r1 := gShiftOne n gs eqAct eqFull c0 d step
        have hle1 : gs.length ≤ r1.1.length := hext1.len_le
        have h2 := gAnd_spec hwf1 (eqAct ⟨step, by omega⟩) (eqFull ⟨step + d.val, ha⟩)
          (by have := haW ⟨step, by omega⟩; omega) (by have := hfW ⟨step + d.val, ha⟩; omega)
        set r2 := gAnd n r1.1 (eqAct ⟨step, by omega⟩) (eqFull ⟨step + d.val, ha⟩)
        have h3 := gOr_spec h2.1 r1.2 r2.2 (by omega) h2.2.2.2.1
        refine ⟨h3.1, hext1.trans (h2.2.1.trans h3.2.1), by omega, h3.2.2.2.1,
          fun x rA rF hx hvc0 hva hvf => ?_⟩
        have v1 := hval1 x rA rF hx hvc0 hva hvf
        have v2 := h2.2.2.2.2 x _ _ hx ((hva ⟨step, by omega⟩).mono hx hext1) ((hvf ⟨step + d.val, ha⟩).mono hx hext1)
        have v3 := h3.2.2.2.2 x _ _ hx (v1.mono hx h2.2.1) v2
        have heq : (decide (rA < step ∧ rA + d.val < K ∧ rF = rA + d.val) ||
            (decide (rA = step) && decide (rF = step + d.val))) =
            decide (rA < step + 1 ∧ rA + d.val < K ∧ rF = rA + d.val) := by
          rw [Bool.eq_iff_iff]
          simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
          constructor
          · rintro (⟨h1, h2', h3'⟩ | ⟨rfl, rfl⟩)
            · exact ⟨by omega, h2', h3'⟩
            · exact ⟨by omega, ha, rfl⟩
          · rintro ⟨h1, h2', h3'⟩
            by_cases hlt : rA < step
            · exact Or.inl ⟨hlt, h2', h3'⟩
            · have : rA = step := by omega
              subst this; exact Or.inr ⟨rfl, h3'⟩
        rwa [heq] at v3
      · simp only [ha, ↓reduceDIte]
        refine ⟨hwf1, hext1, by omega, hlt1, fun x rA rF hx hvc0 hva hvf => ?_⟩
        have v1 := hval1 x rA rF hx hvc0 hva hvf
        have heq : decide (rA < step ∧ rA + d.val < K ∧ rF = rA + d.val) =
            decide (rA < step + 1 ∧ rA + d.val < K ∧ rF = rA + d.val) := by
          rw [Bool.eq_iff_iff]
          simp only [decide_eq_true_eq]
          constructor <;> rintro ⟨h1, h2', h3'⟩ <;> exact ⟨by omega, h2', h3'⟩
        rwa [heq] at v1

private def gShiftAll {K : Nat} (n : Nat) (gs : List CGate) (eqAct eqFull : Fin K → Nat) (c0 : Nat) :
    Nat → List CGate × (Fin K → Nat)
  | 0 => (gs, fun _ => c0)
  | d + 1 =>
      let r1 := gShiftAll n gs eqAct eqFull c0 d
      if hd : d < K then
        let idx : Fin K := ⟨d, hd⟩
        let r2 := gShiftOne n r1.1 eqAct eqFull c0 idx K
        (r2.1, fun i => if i = idx then r2.2 else r1.2 i)
      else r1

private lemma gShiftAll_spec {K : Nat} {n : Nat} {gs : List CGate}
    (eqAct eqFull : Fin K → Nat) (c0 : Nat)
    (hwf : WF n gs) (hc0 : c0 < n + gs.length)
    (haW : ∀ i, eqAct i < n + gs.length) (hfW : ∀ i, eqFull i < n + gs.length) :
    ∀ step : Nat,
      WF n (gShiftAll n gs eqAct eqFull c0 step).1 ∧ Ext gs (gShiftAll n gs eqAct eqFull c0 step).1 ∧
      (gShiftAll n gs eqAct eqFull c0 step).1.length ≤ gs.length + step * (2 * K) ∧
      (∀ i, (gShiftAll n gs eqAct eqFull c0 step).2 i < n + (gShiftAll n gs eqAct eqFull c0 step).1.length) ∧
      ∀ (x : List Bool) (rA rF : Nat), x.length = n → rA ≤ rF → rF < K →
        Val n gs x c0 false →
        (∀ i : Fin K, Val n gs x (eqAct i) (decide (rA = i.val))) →
        (∀ i : Fin K, Val n gs x (eqFull i) (decide (rF = i.val))) →
        ∀ d : Fin K, d.val < step →
          Val n (gShiftAll n gs eqAct eqFull c0 step).1 x ((gShiftAll n gs eqAct eqFull c0 step).2 d)
            (decide (rF - rA = d.val)) := by
  intro step
  induction step with
  | zero =>
      exact ⟨hwf, Ext.refl gs, by simp [gShiftAll], fun _ => hc0, fun _ _ _ _ _ _ _ _ _ d hd => by omega⟩
  | succ step ih =>
      rcases ih with ⟨hwf1, hext1, hlen1, hlt1, hval1⟩
      simp only [gShiftAll]
      by_cases hd : step < K
      · simp only [hd, ↓reduceDIte]
        set r1 := gShiftAll n gs eqAct eqFull c0 step
        set idx : Fin K := ⟨step, hd⟩
        have hle1 : gs.length ≤ r1.1.length := hext1.len_le
        have h2 := gShiftOne_spec eqAct eqFull c0 idx hwf1 (by omega)
          (fun i => by have := haW i; omega) (fun i => by have := hfW i; omega) K
        have hle2 : r1.1.length ≤ (gShiftOne n r1.1 eqAct eqFull c0 idx K).1.length := h2.2.1.len_le
        refine ⟨h2.1, hext1.trans h2.2.1, ?_, ?_, ?_⟩
        · have hmul : (step + 1) * (2 * K) = step * (2 * K) + 2 * K := Nat.succ_mul _ _
          omega
        · intro i
          by_cases hi : i = idx
          · simp only [hi, ↓reduceIte]; exact h2.2.2.2.1
          · simp only [hi, ↓reduceIte]; have := hlt1 i; omega
        · intro x rA rF hx hle hltK hvc0 hva hvf d hdl
          by_cases hi : d = idx
          · subst hi
            simp only [↓reduceIte]
            have v2 := h2.2.2.2.2 x rA rF hx (hvc0.mono hx hext1)
              (fun i => (hva i).mono hx hext1) (fun i => (hvf i).mono hx hext1)
            have heq : decide (rA < K ∧ rA + idx.val < K ∧ rF = rA + idx.val) =
                decide (rF - rA = idx.val) := by
              rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; omega
            rwa [heq] at v2
          · simp only [hi, ↓reduceIte]
            have hne : d.val ≠ step := fun h => hi (Fin.ext h)
            exact (hval1 x rA rF hx hle hltK hvc0 hva hvf d (by omega)).mono hx h2.2.1
      · simp only [hd, ↓reduceDIte]
        refine ⟨hwf1, hext1, ?_, hlt1, fun x rA rF hx hle hltK hvc0 hva hvf d hdl =>
          hval1 x rA rF hx hle hltK hvc0 hva hvf d (by omega)⟩
        have : step * (2 * K) ≤ (step + 1) * (2 * K) := Nat.mul_le_mul_right _ (by omega)
        omega

private def gFinalOne {K : Nat} (n : Nat) (gs : List CGate) (isShift cnt : Fin K → Nat) (c0 : Nat)
    (o : Fin K) : Nat → List CGate × Nat
  | 0 => (gs, c0)
  | d + 1 =>
      let r1 := gFinalOne n gs isShift cnt c0 o d
      if hd : d ≤ o.val then
        let r2 := gAnd n r1.1 (isShift ⟨d, by omega⟩) (cnt ⟨o.val - d, by omega⟩)
        gOr n r2.1 r1.2 r2.2
      else r1

private lemma gFinalOne_spec {K : Nat} {n : Nat} {gs : List CGate}
    (isShift cnt : Fin K → Nat) (c0 : Nat) (o : Fin K)
    (hwf : WF n gs) (hc0 : c0 < n + gs.length)
    (hsW : ∀ i, isShift i < n + gs.length) (hcW : ∀ i, cnt i < n + gs.length) :
    ∀ step : Nat,
      WF n (gFinalOne n gs isShift cnt c0 o step).1 ∧ Ext gs (gFinalOne n gs isShift cnt c0 o step).1 ∧
      (gFinalOne n gs isShift cnt c0 o step).1.length ≤ gs.length + 2 * step ∧
      (gFinalOne n gs isShift cnt c0 o step).2 < n + (gFinalOne n gs isShift cnt c0 o step).1.length ∧
      ∀ (x : List Bool) (sh M : Nat), x.length = n →
        Val n gs x c0 false →
        (∀ i : Fin K, Val n gs x (isShift i) (decide (sh = i.val))) →
        (∀ i : Fin K, Val n gs x (cnt i) (M.testBit i.val)) →
        Val n (gFinalOne n gs isShift cnt c0 o step).1 x (gFinalOne n gs isShift cnt c0 o step).2
          (if sh < step ∧ sh ≤ o.val then M.testBit (o.val - sh) else false) := by
  intro step
  induction step with
  | zero =>
      exact ⟨hwf, Ext.refl gs, by simp [gFinalOne], hc0,
        fun _ _ _ _ hvc0 _ _ => by simpa [gFinalOne] using hvc0⟩
  | succ step ih =>
      rcases ih with ⟨hwf1, hext1, hlen1, hlt1, hval1⟩
      simp only [gFinalOne]
      by_cases hd : step ≤ o.val
      · simp only [hd, ↓reduceDIte]
        set r1 := gFinalOne n gs isShift cnt c0 o step
        have hle1 : gs.length ≤ r1.1.length := hext1.len_le
        have h2 := gAnd_spec hwf1 (isShift ⟨step, by omega⟩) (cnt ⟨o.val - step, by omega⟩)
          (by have := hsW ⟨step, by omega⟩; omega) (by have := hcW ⟨o.val - step, by omega⟩; omega)
        set r2 := gAnd n r1.1 (isShift ⟨step, by omega⟩) (cnt ⟨o.val - step, by omega⟩)
        have h3 := gOr_spec h2.1 r1.2 r2.2 (by omega) h2.2.2.2.1
        refine ⟨h3.1, hext1.trans (h2.2.1.trans h3.2.1), by omega, h3.2.2.2.1,
          fun x sh M hx hvc0 hvs hvc => ?_⟩
        have v1 := hval1 x sh M hx hvc0 hvs hvc
        have v2 := h2.2.2.2.2 x _ _ hx ((hvs ⟨step, by omega⟩).mono hx hext1) ((hvc ⟨o.val - step, by omega⟩).mono hx hext1)
        have v3 := h3.2.2.2.2 x _ _ hx (v1.mono hx h2.2.1) v2
        have heq : ((if sh < step ∧ sh ≤ o.val then M.testBit (o.val - sh) else false) ||
            (decide (sh = step) && M.testBit (o.val - step))) =
            if sh < step + 1 ∧ sh ≤ o.val then M.testBit (o.val - sh) else false := by
          by_cases h1 : sh < step
          · have h2' : sh ≤ o.val := by omega
            have h3' : sh < step + 1 := by omega
            have hne : sh ≠ step := by omega
            simp [h1, h2', h3', hne]
          · by_cases h2' : sh = step
            · subst h2'
              simp [hd]
            · have h3' : ¬sh < step + 1 := by omega
              simp [h1, h2', h3']
        rwa [heq] at v3
      · simp only [hd, ↓reduceDIte]
        refine ⟨hwf1, hext1, by omega, hlt1, fun x sh M hx hvc0 hvs hvc => ?_⟩
        have v1 := hval1 x sh M hx hvc0 hvs hvc
        have heq : (if sh < step ∧ sh ≤ o.val then M.testBit (o.val - sh) else false) =
            if sh < step + 1 ∧ sh ≤ o.val then M.testBit (o.val - sh) else false := by
          have : (sh < step ∧ sh ≤ o.val) ↔ (sh < step + 1 ∧ sh ≤ o.val) := by omega
          simp [this]
        rwa [heq] at v1

private def gFinalAll {K : Nat} (n : Nat) (gs : List CGate) (isShift cnt : Fin K → Nat) (c0 : Nat) :
    Nat → List CGate × (Fin K → Nat)
  | 0 => (gs, fun _ => c0)
  | o + 1 =>
      let r1 := gFinalAll n gs isShift cnt c0 o
      if ho : o < K then
        let idx : Fin K := ⟨o, ho⟩
        let r2 := gFinalOne n r1.1 isShift cnt c0 idx K
        (r2.1, fun i => if i = idx then r2.2 else r1.2 i)
      else r1

private lemma gFinalAll_spec {K : Nat} {n : Nat} {gs : List CGate}
    (isShift cnt : Fin K → Nat) (c0 : Nat)
    (hwf : WF n gs) (hc0 : c0 < n + gs.length)
    (hsW : ∀ i, isShift i < n + gs.length) (hcW : ∀ i, cnt i < n + gs.length) :
    ∀ step : Nat,
      WF n (gFinalAll n gs isShift cnt c0 step).1 ∧ Ext gs (gFinalAll n gs isShift cnt c0 step).1 ∧
      (gFinalAll n gs isShift cnt c0 step).1.length ≤ gs.length + step * (2 * K) ∧
      (∀ i, (gFinalAll n gs isShift cnt c0 step).2 i < n + (gFinalAll n gs isShift cnt c0 step).1.length) ∧
      ∀ (x : List Bool) (sh M : Nat), x.length = n → sh < K →
        Val n gs x c0 false →
        (∀ i : Fin K, Val n gs x (isShift i) (decide (sh = i.val))) →
        (∀ i : Fin K, Val n gs x (cnt i) (M.testBit i.val)) →
        ∀ o : Fin K, o.val < step →
          Val n (gFinalAll n gs isShift cnt c0 step).1 x ((gFinalAll n gs isShift cnt c0 step).2 o)
            ((M * 2 ^ sh).testBit o.val) := by
  intro step
  induction step with
  | zero =>
      exact ⟨hwf, Ext.refl gs, by simp [gFinalAll], fun _ => hc0, fun _ _ _ _ _ _ _ _ o ho => by omega⟩
  | succ step ih =>
      rcases ih with ⟨hwf1, hext1, hlen1, hlt1, hval1⟩
      simp only [gFinalAll]
      by_cases ho : step < K
      · simp only [ho, ↓reduceDIte]
        set r1 := gFinalAll n gs isShift cnt c0 step
        set idx : Fin K := ⟨step, ho⟩
        have hle1 : gs.length ≤ r1.1.length := hext1.len_le
        have h2 := gFinalOne_spec isShift cnt c0 idx hwf1 (by omega)
          (fun i => by have := hsW i; omega) (fun i => by have := hcW i; omega) K
        have hle2 : r1.1.length ≤ (gFinalOne n r1.1 isShift cnt c0 idx K).1.length := h2.2.1.len_le
        refine ⟨h2.1, hext1.trans h2.2.1, ?_, ?_, ?_⟩
        · have hmul : (step + 1) * (2 * K) = step * (2 * K) + 2 * K := Nat.succ_mul _ _
          omega
        · intro i
          by_cases hi : i = idx
          · simp only [hi, ↓reduceIte]; exact h2.2.2.2.1
          · simp only [hi, ↓reduceIte]; have := hlt1 i; omega
        · intro x sh M hx hsh hvc0 hvs hvc o hol
          by_cases hi : o = idx
          · subst hi
            simp only [↓reduceIte]
            have v2 := h2.2.2.2.2 x sh M hx (hvc0.mono hx hext1)
              (fun i => (hvs i).mono hx hext1) (fun i => (hvc i).mono hx hext1)
            rw [testBit_mul_two_pow]
            simpa [hsh] using v2
          · simp only [hi, ↓reduceIte]
            have hne : o.val ≠ step := fun h => hi (Fin.ext h)
            exact (hval1 x sh M hx hsh hvc0 hvs hvc o (by omega)).mono hx h2.2.1
      · simp only [ho, ↓reduceDIte]
        refine ⟨hwf1, hext1, ?_, hlt1, fun x sh M hx hsh hvc0 hvs hvc o hol =>
          hval1 x sh M hx hsh hvc0 hvs hvc o (by omega)⟩
        have : step * (2 * K) ≤ (step + 1) * (2 * K) := Nat.mul_le_mul_right _ (by omega)
        omega

private noncomputable def gMaskFlag (n k q s : Nat) (hk : 0 < k) (row col : Fin k → Bool)
    (c0 c1 : Nat)
    (baseAct : Fin (activeSet k hk row col).card → Nat)
    (baseBnd : Fin (bndSet k hk row col).card → Nat)
    (hasAct : Fin (activeSet k hk row col).card → Nat)
    (pivAct : Fin (activeSet k hk row col).card → Fin (activeSet k hk row col).card → Nat)
    (activeSlot : Fin (min q (bndSet k hk row col).card) → Nat)
    (B : Fin (min q (bndSet k hk row col).card) → Fin (bndSet k hk row col).card → Nat)
    (u v cr cc : Fin k → Nat)
    (gs : List CGate) (mask : Fin (2 ^ min q (bndSet k hk row col).card)) : List CGate × Nat :=
  let t := min q (bndSet k hk row col).card
  let eA := eAct k hk row col
  let eB := eBnd k hk row col
  let r1 := gValidMaskFrom n gs activeSlot mask c1 t
  let r2 := gEvalMaskFrom n r1.1 baseBnd B mask t
  let β : Fin k → Nat := fun j =>
    if hj : j ∈ bndSet k hk row col then r2.2 (eB.symm ⟨j, hj⟩) else c0
  let r3 := gReconstructFrom n k s hk row col u v cr cc c0 r2.1 β k
  let r4 := gPassAllFrom n k s hk row col u v cr cc r3.2 c1 r3.1 k
  let αAct : Fin (activeSet k hk row col).card → Nat := fun c => r3.2 (eA c).val
  let r5 := gXorVecFrom n r4.1 αAct baseAct (activeSet k hk row col).card
  let r6 := gReduceFrom n r5.1 hasAct pivAct r5.2 (activeSet k hk row col).card
  let r7 := gAllNotFrom n r6.1 r6.2 c1 (activeSet k hk row col).card
  let r8 := gAnd n r7.1 r1.2 r4.2
  gAnd n r8.1 r8.2 r7.2

private lemma gMaskFlag_spec {n k q s : Nat} (hk : 0 < k) (row col : Fin k → Bool)
    (c0 c1 : Nat)
    (baseAct : Fin (activeSet k hk row col).card → Nat)
    (baseBnd : Fin (bndSet k hk row col).card → Nat)
    (hasAct : Fin (activeSet k hk row col).card → Nat)
    (pivAct : Fin (activeSet k hk row col).card → Fin (activeSet k hk row col).card → Nat)
    (activeSlot : Fin (min q (bndSet k hk row col).card) → Nat)
    (B : Fin (min q (bndSet k hk row col).card) → Fin (bndSet k hk row col).card → Nat)
    (u v cr cc : Fin k → Nat)
    {gs : List CGate} (mask : Fin (2 ^ min q (bndSet k hk row col).card))
    (hwf : WF n gs) (hc0 : c0 < n + gs.length) (hc1 : c1 < n + gs.length)
    (hbA : ∀ c, baseAct c < n + gs.length) (hbB : ∀ c, baseBnd c < n + gs.length)
    (hhA : ∀ c, hasAct c < n + gs.length) (hpA : ∀ i j, pivAct i j < n + gs.length)
    (haS : ∀ j, activeSlot j < n + gs.length) (hB : ∀ j c, B j c < n + gs.length)
    (hu : ∀ j, u j < n + gs.length) (hv : ∀ j, v j < n + gs.length)
    (hcr : ∀ j, cr j < n + gs.length) (hcc : ∀ j, cc j < n + gs.length) :
    WF n (gMaskFlag n k q s hk row col c0 c1 baseAct baseBnd hasAct pivAct activeSlot B u v cr cc gs mask).1 ∧
    Ext gs (gMaskFlag n k q s hk row col c0 c1 baseAct baseBnd hasAct pivAct activeSlot B u v cr cc gs mask).1 ∧
    (gMaskFlag n k q s hk row col c0 c1 baseAct baseBnd hasAct pivAct activeSlot B u v cr cc gs mask).1.length ≤
      gs.length + (9 * k * k + 236 * k + 2) ∧
    (gMaskFlag n k q s hk row col c0 c1 baseAct baseBnd hasAct pivAct activeSlot B u v cr cc gs mask).2 <
      n + (gMaskFlag n k q s hk row col c0 c1 baseAct baseBnd hasAct pivAct activeSlot B u v cr cc gs mask).1.length ∧
    ∀ (x : List Bool)
      (bBaseAct : Fin (activeSet k hk row col).card → Bool)
      (bBaseBnd : Fin (bndSet k hk row col).card → Bool)
      (bHasAct : Fin (activeSet k hk row col).card → Bool)
      (bPivAct : Fin (activeSet k hk row col).card → Fin (activeSet k hk row col).card → Bool)
      (bActSlot : Fin (min q (bndSet k hk row col).card) → Bool)
      (bB : Fin (min q (bndSet k hk row col).card) → Fin (bndSet k hk row col).card → Bool)
      (bu bv bcr bcc : Fin k → Bool),
      x.length = n → Val n gs x c0 false → Val n gs x c1 true →
      (∀ c, Val n gs x (baseAct c) (bBaseAct c)) →
      (∀ c, Val n gs x (baseBnd c) (bBaseBnd c)) →
      (∀ c, Val n gs x (hasAct c) (bHasAct c)) →
      (∀ i j, Val n gs x (pivAct i j) (bPivAct i j)) →
      (∀ j, Val n gs x (activeSlot j) (bActSlot j)) →
      (∀ j c, Val n gs x (B j c) (bB j c)) →
      (∀ j, Val n gs x (u j) (bu j)) → (∀ j, Val n gs x (v j) (bv j)) →
      (∀ j, Val n gs x (cr j) (bcr j)) → (∀ j, Val n gs x (cc j) (bcc j)) →
      Val n (gMaskFlag n k q s hk row col c0 c1 baseAct baseBnd hasAct pivAct activeSlot B u v cr cc gs mask).1 x
        (gMaskFlag n k q s hk row col c0 c1 baseAct baseBnd hasAct pivAct activeSlot B u v cr cc gs mask).2
        (maskFlag k s hk row col q bBaseAct bBaseBnd bHasAct bPivAct bActSlot bB bu bv bcr bcc mask) := by
  unfold gMaskFlag
  let t := min q (bndSet k hk row col).card
  let eA := eAct k hk row col
  let eB := eBnd k hk row col
  have hL_act : (activeSet k hk row col).card ≤ k := by
    have := Finset.card_le_univ (activeSet k hk row col); simpa using this
  have hL_bnd : (bndSet k hk row col).card ≤ k := by
    have := Finset.card_le_univ (bndSet k hk row col); simpa using this
  have ht_le : t ≤ k := le_trans (min_le_right _ _) hL_bnd
  have h1 := gValidMaskFrom_spec activeSlot mask c1 hwf hc1 haS t
  set r1 := gValidMaskFrom n gs activeSlot mask c1 t
  have he1 := h1.2.1.len_le
  have h2 := gEvalMaskFrom_spec baseBnd B mask h1.1
    (fun c => by have := hbB c; omega) (fun j c => by have := hB j c; omega) t
  set r2 := gEvalMaskFrom n r1.1 baseBnd B mask t
  have he2 := h2.2.1.len_le
  set β : Fin k → Nat := fun j => if hj : j ∈ bndSet k hk row col then r2.2 (eB.symm ⟨j, hj⟩) else c0
  have h3 := gReconstructFrom_spec (s := s) hk row col u v cr cc β c0 h2.1 (by omega)
    (fun j => by have := hu j; omega) (fun j => by have := hv j; omega)
    (fun j => by have := hcr j; omega) (fun j => by have := hcc j; omega)
    (fun j => by dsimp only [β]; split_ifs; exact h2.2.2.2.1 _; omega) k
  set r3 := gReconstructFrom n k s hk row col u v cr cc c0 r2.1 β k
  have he3 := h3.2.1.len_le
  have h4 := gPassAllFrom_spec (s := s) hk row col u v cr cc r3.2 c1 h3.1 (by omega)
    (fun j => by have := hu j; omega) (fun j => by have := hv j; omega)
    (fun j => by have := hcr j; omega) (fun j => by have := hcc j; omega) h3.2.2.2.1 k
  set r4 := gPassAllFrom n k s hk row col u v cr cc r3.2 c1 r3.1 k
  have he4 := h4.2.1.len_le
  set αAct : Fin (activeSet k hk row col).card → Nat := fun c => r3.2 (eA c).val
  have h5 := gXorVecFrom_spec αAct baseAct h4.1
    (fun c => by dsimp only [αAct]; have := h3.2.2.2.1 (eA c).val; omega)
    (fun c => by have := hbA c; omega) (activeSet k hk row col).card
  set r5 := gXorVecFrom n r4.1 αAct baseAct (activeSet k hk row col).card
  have he5 := h5.2.1.len_le
  have h6 := gReduceFrom_spec hasAct pivAct r5.2 h5.1
    (fun c => by have := hhA c; omega)
    (fun i j => by have := hpA i j; omega) h5.2.2.2.1 (activeSet k hk row col).card
  set r6 := gReduceFrom n r5.1 hasAct pivAct r5.2 (activeSet k hk row col).card
  have he6 := h6.2.1.len_le
  have h7 := gAllNotFrom_spec r6.2 c1 h6.1 (by omega) h6.2.2.2.1 (activeSet k hk row col).card
  set r7 := gAllNotFrom n r6.1 r6.2 c1 (activeSet k hk row col).card
  have he7 := h7.2.1.len_le
  have h8 := gAnd_spec h7.1 r1.2 r4.2 (by have := h1.2.2.2.1; omega) (by have := h4.2.2.2.1; omega)
  set r8 := gAnd n r7.1 r1.2 r4.2
  have h9 := gAnd_spec h8.1 r8.2 r7.2 h8.2.2.2.1 (by have := h7.2.2.2.1; omega)
  set r9 := gAnd n r8.1 r8.2 r7.2
  have hext12 := h1.2.1.trans h2.2.1
  have hext13 := hext12.trans h3.2.1
  have hext14 := hext13.trans h4.2.1
  have hext15 := hext14.trans h5.2.1
  have hext16 := hext15.trans h6.2.1
  have hext17 := hext16.trans h7.2.1
  have hext18 := hext17.trans h8.2.1
  have hext19 := hext18.trans h9.2.1
  refine ⟨h9.1, hext19, ?_, h9.2.2.2.1, ?_⟩
  · have hm1 : t * (4 * (bndSet k hk row col).card) ≤ 4 * k * k := by
      have := Nat.mul_le_mul ht_le (Nat.mul_le_mul_left 4 hL_bnd)
      nlinarith
    have hm2 : (activeSet k hk row col).card * (5 * (activeSet k hk row col).card + 1) ≤ 5 * k * k + k := by
      have := Nat.mul_le_mul hL_act (show 5 * (activeSet k hk row col).card + 1 ≤ 5 * k + 1 by omega)
      nlinarith
    have h9k : 4 * k * k + 5 * k * k = 9 * k * k := by ring
    omega
  · intro x bBaseAct bBaseBnd bHasAct bPivAct bActSlot bB bu bv bcr bcc hx hvc0 hvc1
      hvbA hvbB hvhA hvpA hvaS hvB hvu hvv hvcr hvcc
    have v1 := h1.2.2.2.2 x bActSlot hx hvc1 hvaS
    rw [allFinFrom_eq_all] at v1
    have v2 := h2.2.2.2.2 x bBaseBnd bB hx (fun c => (hvbB c).mono hx h1.2.1)
      (fun j c => (hvB j c).mono hx h1.2.1)
    let bβ : Fin k → Bool := fun j =>
      if hj : j ∈ bndSet k hk row col then evalMask bBaseBnd bB mask (eB.symm ⟨j, hj⟩) else false
    have v3 := h3.2.2.2.2 x bu bv bcr bcc bβ hx (hvc0.mono hx hext12)
      (fun j => (hvu j).mono hx hext12) (fun j => (hvv j).mono hx hext12)
      (fun j => (hvcr j).mono hx hext12) (fun j => (hvcc j).mono hx hext12)
      (fun j => by dsimp only [β, bβ]; split_ifs; exact v2 _; exact hvc0.mono hx hext12)
    have v4 := h4.2.2.2.2 x bu bv bcr bcc _ hx (hvc1.mono hx hext13)
      (fun j => (hvu j).mono hx hext13) (fun j => (hvv j).mono hx hext13)
      (fun j => (hvcr j).mono hx hext13) (fun j => (hvcc j).mono hx hext13) v3
    rw [allFinFrom_eq_all] at v4
    have v5 := h5.2.2.2.2 x (fun c => reconstruct k s hk row col bu bv bcr bcc bβ (eA c).val) bBaseAct hx
      (fun c => (v3 (eA c).val).mono hx h4.2.1) (fun c => (hvbA c).mono hx hext14)
    have v5' : ∀ c, Val n r5.1 x (r5.2 c)
        (xor (reconstruct k s hk row col bu bv bcr bcc bβ (eA c).val) (bBaseAct c)) :=
      fun c => by simpa [c.isLt] using v5 c
    have v6 := h6.2.2.2.2 x bHasAct bPivAct _ hx
      (fun c => (hvhA c).mono hx hext15) (fun i j => (hvpA i j).mono hx hext15) v5'
    have v7 := h7.2.2.2.2 x _ hx (hvc1.mono hx hext16) v6
    rw [allFinFrom_eq_all] at v7
    have v8 := h8.2.2.2.2 x _ _ hx
      (v1.mono hx (h2.2.1.trans (h3.2.1.trans (h4.2.1.trans (h5.2.1.trans (h6.2.1.trans h7.2.1))))))
      (v4.mono hx (h5.2.1.trans (h6.2.1.trans h7.2.1)))
    exact h9.2.2.2.2 x _ _ hx v8 (v7.mono hx h8.2.1)

private noncomputable def gCountMasksFrom (n k q s : Nat) (hk : 0 < k) (row col : Fin k → Bool)
    (c0 c1 : Nat)
    (baseAct : Fin (activeSet k hk row col).card → Nat)
    (baseBnd : Fin (bndSet k hk row col).card → Nat)
    (hasAct : Fin (activeSet k hk row col).card → Nat)
    (pivAct : Fin (activeSet k hk row col).card → Fin (activeSet k hk row col).card → Nat)
    (activeSlot : Fin (min q (bndSet k hk row col).card) → Nat)
    (B : Fin (min q (bndSet k hk row col).card) → Fin (bndSet k hk row col).card → Nat)
    (u v cr cc : Fin k → Nat) (gs : List CGate) :
    Nat → List CGate × (Fin (k + 1) → Nat)
  | 0 => (gs, fun _ => c0)
  | i + 1 =>
      let r1 := gCountMasksFrom n k q s hk row col c0 c1 baseAct baseBnd hasAct pivAct activeSlot B u v cr cc gs i
      if hi : i < 2 ^ min q (bndSet k hk row col).card then
        let r2 := gMaskFlag n k q s hk row col c0 c1 baseAct baseBnd hasAct pivAct activeSlot B u v cr cc r1.1 ⟨i, hi⟩
        let r3 := gIncFrom n r2.1 r1.2 r2.2 (k + 1)
        (r3.1, r3.2.1)
      else r1

private lemma gCountMasksFrom_spec {n k q s : Nat} (hk : 0 < k) (row col : Fin k → Bool)
    (c0 c1 : Nat)
    (baseAct : Fin (activeSet k hk row col).card → Nat)
    (baseBnd : Fin (bndSet k hk row col).card → Nat)
    (hasAct : Fin (activeSet k hk row col).card → Nat)
    (pivAct : Fin (activeSet k hk row col).card → Fin (activeSet k hk row col).card → Nat)
    (activeSlot : Fin (min q (bndSet k hk row col).card) → Nat)
    (B : Fin (min q (bndSet k hk row col).card) → Fin (bndSet k hk row col).card → Nat)
    (u v cr cc : Fin k → Nat) {gs : List CGate}
    (hwf : WF n gs) (hc0 : c0 < n + gs.length) (hc1 : c1 < n + gs.length)
    (hbA : ∀ c, baseAct c < n + gs.length) (hbB : ∀ c, baseBnd c < n + gs.length)
    (hhA : ∀ c, hasAct c < n + gs.length) (hpA : ∀ i j, pivAct i j < n + gs.length)
    (haS : ∀ j, activeSlot j < n + gs.length) (hB : ∀ j c, B j c < n + gs.length)
    (hu : ∀ j, u j < n + gs.length) (hv : ∀ j, v j < n + gs.length)
    (hcr : ∀ j, cr j < n + gs.length) (hcc : ∀ j, cc j < n + gs.length) :
    ∀ step : Nat,
      WF n (gCountMasksFrom n k q s hk row col c0 c1 baseAct baseBnd hasAct pivAct activeSlot B u v cr cc gs step).1 ∧
      Ext gs (gCountMasksFrom n k q s hk row col c0 c1 baseAct baseBnd hasAct pivAct activeSlot B u v cr cc gs step).1 ∧
      (gCountMasksFrom n k q s hk row col c0 c1 baseAct baseBnd hasAct pivAct activeSlot B u v cr cc gs step).1.length ≤
        gs.length + step * (9 * k * k + 241 * k + 7) ∧
      (∀ i, (gCountMasksFrom n k q s hk row col c0 c1 baseAct baseBnd hasAct pivAct activeSlot B u v cr cc gs step).2 i <
        n + (gCountMasksFrom n k q s hk row col c0 c1 baseAct baseBnd hasAct pivAct activeSlot B u v cr cc gs step).1.length) ∧
      ∀ (x : List Bool)
        (bBaseAct : Fin (activeSet k hk row col).card → Bool)
        (bBaseBnd : Fin (bndSet k hk row col).card → Bool)
        (bHasAct : Fin (activeSet k hk row col).card → Bool)
        (bPivAct : Fin (activeSet k hk row col).card → Fin (activeSet k hk row col).card → Bool)
        (bActSlot : Fin (min q (bndSet k hk row col).card) → Bool)
        (bB : Fin (min q (bndSet k hk row col).card) → Fin (bndSet k hk row col).card → Bool)
        (bu bv bcr bcc : Fin k → Bool),
        x.length = n → Val n gs x c0 false → Val n gs x c1 true →
        (∀ c, Val n gs x (baseAct c) (bBaseAct c)) →
        (∀ c, Val n gs x (baseBnd c) (bBaseBnd c)) →
        (∀ c, Val n gs x (hasAct c) (bHasAct c)) →
        (∀ i j, Val n gs x (pivAct i j) (bPivAct i j)) →
        (∀ j, Val n gs x (activeSlot j) (bActSlot j)) →
        (∀ j c, Val n gs x (B j c) (bB j c)) →
        (∀ j, Val n gs x (u j) (bu j)) → (∀ j, Val n gs x (v j) (bv j)) →
        (∀ j, Val n gs x (cr j) (bcr j)) → (∀ j, Val n gs x (cc j) (bcc j)) →
        ∀ i : Fin (k + 1),
          Val n (gCountMasksFrom n k q s hk row col c0 c1 baseAct baseBnd hasAct pivAct activeSlot B u v cr cc gs step).1 x
            ((gCountMasksFrom n k q s hk row col c0 c1 baseAct baseBnd hasAct pivAct activeSlot B u v cr cc gs step).2 i)
            ((Finset.univ.filter (fun mask : Fin (2 ^ min q (bndSet k hk row col).card) =>
              mask.val < step ∧
              maskFlag k s hk row col q bBaseAct bBaseBnd bHasAct bPivAct bActSlot bB bu bv bcr bcc mask = true)).card.testBit i.val) := by
  intro step
  induction step with
  | zero =>
      refine ⟨hwf, Ext.refl gs, by simp [gCountMasksFrom], fun _ => hc0,
        fun _ _ _ _ _ _ _ _ _ _ _ _ hvc0 _ _ _ _ _ _ _ _ _ _ _ i => ?_⟩
      simpa [gCountMasksFrom] using hvc0
  | succ step ih =>
      rcases ih with ⟨hwf1, hext1, hlen1, hlt1, hval1⟩
      simp only [gCountMasksFrom]
      by_cases hi : step < 2 ^ min q (bndSet k hk row col).card
      · simp only [hi, ↓reduceDIte]
        set r1 := gCountMasksFrom n k q s hk row col c0 c1 baseAct baseBnd hasAct pivAct activeSlot B u v cr cc gs step
        have hle1 : gs.length ≤ r1.1.length := hext1.len_le
        have h2 := gMaskFlag_spec (q := q) (s := s) hk row col c0 c1 baseAct baseBnd hasAct pivAct activeSlot B u v cr cc ⟨step, hi⟩
          hwf1 (by omega) (by omega)
          (fun c => by have := hbA c; omega) (fun c => by have := hbB c; omega)
          (fun c => by have := hhA c; omega) (fun i j => by have := hpA i j; omega)
          (fun j => by have := haS j; omega) (fun j c => by have := hB j c; omega)
          (fun j => by have := hu j; omega) (fun j => by have := hv j; omega)
          (fun j => by have := hcr j; omega) (fun j => by have := hcc j; omega)
        set r2 := gMaskFlag n k q s hk row col c0 c1 baseAct baseBnd hasAct pivAct activeSlot B u v cr cc r1.1 ⟨step, hi⟩
        have hle2 : r1.1.length ≤ r2.1.length := h2.2.1.len_le
        have h3 := gIncFrom_spec r1.2 r2.2 h2.1 (fun i => by have := hlt1 i; omega) h2.2.2.2.1 (k + 1)
        refine ⟨h3.1, hext1.trans (h2.2.1.trans h3.2.1), ?_, h3.2.2.2.1, ?_⟩
        · have hmul : (step + 1) * (9 * k * k + 241 * k + 7) =
              step * (9 * k * k + 241 * k + 7) + (9 * k * k + 241 * k + 7) := Nat.succ_mul _ _
          omega
        · intro x bBaseAct bBaseBnd bHasAct bPivAct bActSlot bB bu bv bcr bcc hx hvc0 hvc1
            hvbA hvbB hvhA hvpA hvaS hvB hvu hvv hvcr hvcc i
          have v1 := hval1 x bBaseAct bBaseBnd bHasAct bPivAct bActSlot bB bu bv bcr bcc hx hvc0 hvc1
            hvbA hvbB hvhA hvpA hvaS hvB hvu hvv hvcr hvcc
          have v2 := h2.2.2.2.2 x bBaseAct bBaseBnd bHasAct bPivAct bActSlot bB bu bv bcr bcc hx
            (hvc0.mono hx hext1) (hvc1.mono hx hext1)
            (fun c => (hvbA c).mono hx hext1) (fun c => (hvbB c).mono hx hext1)
            (fun c => (hvhA c).mono hx hext1) (fun a b => (hvpA a b).mono hx hext1)
            (fun j => (hvaS j).mono hx hext1) (fun j c => (hvB j c).mono hx hext1)
            (fun j => (hvu j).mono hx hext1) (fun j => (hvv j).mono hx hext1)
            (fun j => (hvcr j).mono hx hext1) (fun j => (hvcc j).mono hx hext1)
          have v3 := (h3.2.2.2.2.2 x _ _ hx (fun j => (v1 j).mono hx h2.2.1) v2).1 i
          simp only [i.isLt, ↓reduceIte] at v3
          let fl := maskFlag k s hk row col q bBaseAct bBaseBnd bHasAct bPivAct bActSlot bB bu bv bcr bcc
          have hcard : (Finset.univ.filter (fun mask : Fin (2 ^ min q (bndSet k hk row col).card) =>
              mask.val < step + 1 ∧ fl mask = true)).card =
              (Finset.univ.filter (fun mask : Fin (2 ^ min q (bndSet k hk row col).card) =>
                mask.val < step ∧ fl mask = true)).card + if fl ⟨step, hi⟩ then 1 else 0 := by
            set idx : Fin (2 ^ min q (bndSet k hk row col).card) := ⟨step, hi⟩
            cases hf : fl idx
            · simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
              congr 1; ext m0
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              constructor
              · rintro ⟨hlt, hfm⟩
                refine ⟨?_, hfm⟩
                by_contra hge
                have : m0 = idx := Fin.ext (show m0.val = step by omega)
                rw [this, hf] at hfm; cases hfm
              · rintro ⟨hlt, hfm⟩; exact ⟨by omega, hfm⟩
            · simp only [↓reduceIte]
              have hnot : idx ∉ Finset.univ.filter (fun mask : Fin (2 ^ min q (bndSet k hk row col).card) =>
                  mask.val < step ∧ fl mask = true) := by simp [idx]
              have hfilt : Finset.univ.filter (fun mask : Fin (2 ^ min q (bndSet k hk row col).card) =>
                  mask.val < step + 1 ∧ fl mask = true) =
                  insert idx (Finset.univ.filter (fun mask : Fin (2 ^ min q (bndSet k hk row col).card) =>
                    mask.val < step ∧ fl mask = true)) := by
                ext m0
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
                constructor
                · rintro ⟨hlt, hfm⟩
                  by_cases hm0 : m0 = idx
                  · exact Or.inl hm0
                  · right; have : m0.val ≠ step := fun h => hm0 (Fin.ext h); exact ⟨by omega, hfm⟩
                · rintro (rfl | ⟨hlt, hfm⟩)
                  · exact ⟨Nat.lt_succ_self step, hf⟩
                  · exact ⟨by omega, hfm⟩
              rw [hfilt, Finset.card_insert_of_notMem hnot]
          rw [hcard]
          exact v3
      · simp only [hi, ↓reduceDIte]
        refine ⟨hwf1, hext1, ?_, hlt1, fun x bBaseAct bBaseBnd bHasAct bPivAct bActSlot bB bu bv bcr bcc hx hvc0 hvc1
          hvbA hvbB hvhA hvpA hvaS hvB hvu hvv hvcr hvcc i => ?_⟩
        · have : step * (9 * k * k + 241 * k + 7) ≤ (step + 1) * (9 * k * k + 241 * k + 7) :=
            Nat.mul_le_mul_right _ (by omega)
          omega
        · have heq : Finset.univ.filter (fun mask : Fin (2 ^ min q (bndSet k hk row col).card) =>
              mask.val < step + 1 ∧
              maskFlag k s hk row col q bBaseAct bBaseBnd bHasAct bPivAct bActSlot bB bu bv bcr bcc mask = true) =
              Finset.univ.filter (fun mask : Fin (2 ^ min q (bndSet k hk row col).card) =>
                mask.val < step ∧
                maskFlag k s hk row col q bBaseAct bBaseBnd bHasAct bPivAct bActSlot bB bu bv bcr bcc mask = true) := by
            ext m0; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            constructor <;> rintro ⟨hlt, hfm⟩ <;> exact ⟨by omega, hfm⟩
          rw [heq]
          exact hval1 x bBaseAct bBaseBnd bHasAct bPivAct bActSlot bB bu bv bcr bcc hx hvc0 hvc1
            hvbA hvbB hvhA hvpA hvaS hvB hvu hvv hvcr hvcc i

private lemma size_bound_aux (k m t : Nat) :
    2 + 3 * (m * (k * (9 * k + 5))) + k * (k * (4 * k + 6)) +
      2 ^ t * (9 * k * k + 241 * k + 7) +
      2 * (k * (4 * (k + 1))) + 2 * ((k + 1) * (2 * (k + 1))) ≤
    512 * (k + m + 1) ^ 4 * 2 ^ t := by
  have hpow : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  set N := k + m + 1
  have hkN : k ≤ N := by omega
  have hmN : m ≤ N := by omega
  have hk1N : k + 1 ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hN2 : N ^ 2 ≤ N ^ 4 := Nat.pow_le_pow_right hN1 (by decide)
  have hN3 : N ^ 3 ≤ N ^ 4 := Nat.pow_le_pow_right hN1 (by decide)
  have hN4 : 1 ≤ N ^ 4 := Nat.one_le_pow 4 N hN1
  have hN14 : N ≤ N ^ 4 := by
    calc N = N ^ 1 := (pow_one N).symm
      _ ≤ N ^ 4 := Nat.pow_le_pow_right hN1 (by decide)
  have h1 : 2 + 3 * (m * (k * (9 * k + 5))) + k * (k * (4 * k + 6)) +
      2 * (k * (4 * (k + 1))) + 2 * ((k + 1) * (2 * (k + 1))) ≤ 66 * N ^ 4 := by
    have hA : m * (k * (9 * k + 5)) ≤ 14 * N ^ 3 := by
      calc m * (k * (9 * k + 5)) ≤ N * (N * (14 * N)) :=
            Nat.mul_le_mul hmN (Nat.mul_le_mul hkN (by omega))
        _ = 14 * N ^ 3 := by ring
    have hB : k * (k * (4 * k + 6)) ≤ 10 * N ^ 3 := by
      calc k * (k * (4 * k + 6)) ≤ N * (N * (10 * N)) :=
            Nat.mul_le_mul hkN (Nat.mul_le_mul hkN (by omega))
        _ = 10 * N ^ 3 := by ring
    have hC : k * (4 * (k + 1)) ≤ 4 * N ^ 2 := by
      calc k * (4 * (k + 1)) ≤ N * (4 * N) := Nat.mul_le_mul hkN (by omega)
        _ = 4 * N ^ 2 := by ring
    have hD : (k + 1) * (2 * (k + 1)) ≤ 2 * N ^ 2 := by
      calc (k + 1) * (2 * (k + 1)) ≤ N * (2 * N) := Nat.mul_le_mul hk1N (by omega)
        _ = 2 * N ^ 2 := by ring
    omega
  have h2 : 9 * k * k + 241 * k + 7 ≤ 257 * N ^ 4 := by
    have hkk : k * k ≤ N ^ 2 := by
      calc k * k ≤ N * N := Nat.mul_le_mul hkN hkN
        _ = N ^ 2 := by ring
    have : 9 * k * k ≤ 9 * N ^ 4 := by nlinarith
    omega
  have h1' : 66 * N ^ 4 ≤ 66 * N ^ 4 * 2 ^ t := Nat.le_mul_of_pos_right _ (by omega)
  have h2' : 2 ^ t * (9 * k * k + 241 * k + 7) ≤ 257 * N ^ 4 * 2 ^ t := by
    rw [Nat.mul_comm]
    exact Nat.mul_le_mul_right (2 ^ t) h2
  have hsum : 66 * N ^ 4 * 2 ^ t + 257 * N ^ 4 * 2 ^ t ≤ 512 * N ^ 4 * 2 ^ t := by
    have : 66 * N ^ 4 * 2 ^ t + 257 * N ^ 4 * 2 ^ t = 323 * (N ^ 4 * 2 ^ t) := by ring
    have : 512 * N ^ 4 * 2 ^ t = 512 * (N ^ 4 * 2 ^ t) := by ring
    omega
  omega

private lemma main_25650 (k m q s : Nat) (hk : 0 < k) (row col : Fin k → Bool) :
    let W := Fin k → ZMod 2
    let X := Fin m → ZMod 2
    let ix0 := fun site : Nat => (⟨site % k, Nat.mod_lt _ hk⟩ : Fin k)
    let rot := fun (t : Nat) (v : W) (slot : Fin k) => v (ix0 (slot.val + k - t % k))
    let run := fun (d t f : Nat) (w name c : W) =>
      let z := rot t w + name
      let y := fun atMix : Fin k => z atMix + z (ix0 (atMix.val + d)) + z (ix0 (atMix.val + k - d % k))
      fun atOut : Fin k => y atOut + (1 + y (ix0 (atOut.val + 1))) * y (ix0 (atOut.val + 2)) + rot f w atOut + c atOut
    let boundary := bndSet k hk row col
    let inputs := (m + 5) * k
    ∃ (C : CCircuit) (out : Fin (k + 1) → Fin (inputs + C.size)),
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack inputs C ∧
      C.size ≤ 512 * (k + m + 1) ^ 4 * 2 ^ (min q boundary.card) ∧
      ∀ (base : W) (gen : Fin m → W) (u v cr cc : W),
        let key := fun a : X => base + ∑ i : Fin m, a i • gen i
        let pack := fun (word : W) => List.ofFn (fun j : Fin k => decide (word j ≠ 0))
        let bits := pack base ++ (List.ofFn (fun g => pack (gen g))).flatten ++
          pack u ++ pack v ++ pack cr ++ pack cc
        Nat.card (Set.range (fun coeff : X => fun member : boundary => key coeff (ix0 (s + member.val.val)))) ≤ 2 ^ q →
        let count := Nat.card { w : W // w ∈ Set.range key ∧
          ∀ p : Fin k, (row p = true → run 1 1 0 w u cr (ix0 (s + p.val + 2)) = 0) ∧
                       (col p = true → run 2 3 4 w v cc (ix0 (s + p.val + 5)) = 0) }
        ∀ o : Fin (k + 1), (C.wires bits).getD (out o).val false = count.testBit o.val := by
  intro W X ix0 rot run boundary inputs
  let active := activeSet k hk row col
  let eA := eAct k hk row col
  let eB := eBnd k hk row col
  let t := min q boundary.card
  let baseW : Fin k → Nat := fun j => j.val
  let genW : Fin m → Fin k → Nat := fun g j => (g.val + 1) * k + j.val
  let uW : Fin k → Nat := fun j => (m + 1) * k + j.val
  let vW : Fin k → Nat := fun j => (m + 2) * k + j.val
  let crW : Fin k → Nat := fun j => (m + 3) * k + j.val
  let ccW : Fin k → Nat := fun j => (m + 4) * k + j.val
  let rowsFullW : Fin m → Fin k → Nat := fun g j => genW g j
  let rowsActW : Fin m → Fin active.card → Nat := fun g c => genW g (ix k hk (s + (eA c).val.val))
  let rowsBndW : Fin m → Fin boundary.card → Nat := fun g c => genW g (ix k hk (s + (eB c).val.val))
  let baseActW : Fin active.card → Nat := fun c => baseW (ix k hk (s + (eA c).val.val))
  let baseBndW : Fin boundary.card → Nat := fun c => baseW (ix k hk (s + (eB c).val.val))
  have hbaseW_lt : ∀ j, baseW j < inputs := fun j => by
    dsimp only [baseW, inputs]; have : 5 * k ≤ (m + 5) * k := Nat.mul_le_mul_right k (by omega); omega
  have hgenW_lt : ∀ g j, genW g j < inputs := fun g j => by
    dsimp only [genW, inputs]
    have : (g.val + 1) * k ≤ m * k := Nat.mul_le_mul_right k (by omega)
    have : (m + 5) * k = m * k + 5 * k := Nat.add_mul m 5 k
    omega
  have huW_lt : ∀ j, uW j < inputs := fun j => by
    dsimp only [uW, inputs]; have : (m + 5) * k = (m + 1) * k + 4 * k := by ring
    omega
  have hvW_lt : ∀ j, vW j < inputs := fun j => by
    dsimp only [vW, inputs]; have : (m + 5) * k = (m + 2) * k + 3 * k := by ring
    omega
  have hcrW_lt : ∀ j, crW j < inputs := fun j => by
    dsimp only [crW, inputs]; have : (m + 5) * k = (m + 3) * k + 2 * k := by ring
    omega
  have hccW_lt : ∀ j, ccW j < inputs := fun j => by
    dsimp only [ccW, inputs]; have : (m + 5) * k = (m + 4) * k + k := by ring
    omega
  have hwf0 : WF inputs [] := ⟨fun _ h => by simp at h, fun _ h => by simp at h⟩
  have h0 := gConst0_spec hwf0
  set r0 := gConst0 inputs []
  have h1 := gConst1_spec h0.1
  set r1 := gConst1 inputs r0.1
  set c0 := r0.2
  set c1 := r1.2
  have hc0_lt : c0 < inputs + r1.1.length := by have := h0.2.2.2.1; omega
  have hc1_lt : c1 < inputs + r1.1.length := h1.2.2.2.1
  have hEFull := gEchelonFrom_spec rowsFullW c0 h1.1 hc0_lt (fun g j => by dsimp only [rowsFullW]; have := hgenW_lt g j; omega) m
  set rEFull := gEchelonFrom inputs r1.1 rowsFullW c0 m
  have heF := hEFull.2.1.len_le
  have hEAct := gEchelonFrom_spec rowsActW c0 hEFull.1 (by omega) (fun g c => by dsimp only [rowsActW]; have := hgenW_lt g (ix k hk (s + (eA c).val.val)); omega) m
  set rEAct := gEchelonFrom inputs rEFull.1 rowsActW c0 m
  have heA := hEAct.2.1.len_le
  have hEBnd := gEchelonFrom_spec rowsBndW c0 hEAct.1 (by omega) (fun g c => by dsimp only [rowsBndW]; have := hgenW_lt g (ix k hk (s + (eB c).val.val)); omega) m
  set rEBnd := gEchelonFrom inputs rEAct.1 rowsBndW c0 m
  have heB := hEBnd.2.1.len_le
  have hComp := gCompactFrom_spec (t := t) rEBnd.2.1 rEBnd.2.2 c0 hEBnd.1 (by omega) hEBnd.2.2.2.1 hEBnd.2.2.2.2.1 boundary.card
  set rComp := gCompactFrom (t := t) inputs rEBnd.1 rEBnd.2.1 rEBnd.2.2 c0 boundary.card
  have heC := hComp.2.1.len_le
  have hCnt := gCountMasksFrom_spec (q := q) (s := s) hk row col c0 c1 baseActW baseBndW
    rEAct.2.1 rEAct.2.2 rComp.2.1 rComp.2.2 uW vW crW ccW hComp.1 (by omega) (by omega)
    (fun c => by dsimp only [baseActW]; have := hbaseW_lt (ix k hk (s + (eA c).val.val)); omega) (fun c => by dsimp only [baseBndW]; have := hbaseW_lt (ix k hk (s + (eB c).val.val)); omega)
    (fun c => by have := hEAct.2.2.2.1 c; omega) (fun i j => by have := hEAct.2.2.2.2.1 i j; omega)
    hComp.2.2.2.1 hComp.2.2.2.2.1
    (fun j => by have := huW_lt j; omega) (fun j => by have := hvW_lt j; omega)
    (fun j => by have := hcrW_lt j; omega) (fun j => by have := hccW_lt j; omega) (2 ^ t)
  set rCnt := gCountMasksFrom inputs k q s hk row col c0 c1 baseActW baseBndW
    rEAct.2.1 rEAct.2.2 rComp.2.1 rComp.2.2 uW vW crW ccW rComp.1 (2 ^ t)
  have heCnt := hCnt.2.1.len_le
  have hOHFull := gOneHotFrom_spec (K := k + 1) rEFull.2.1 c0 c1 hCnt.1 (by omega) (by omega)
    (fun c => by have := hEFull.2.2.2.1 c; omega) k
  set rOHFull := gOneHotFrom (K := k + 1) inputs rCnt.1 rEFull.2.1 c0 c1 k
  have heOHF := hOHFull.2.1.len_le
  have hOHAct := gOneHotFrom_spec (K := k + 1) rEAct.2.1 c0 c1 hOHFull.1 (by omega) (by omega)
    (fun c => by have := hEAct.2.2.2.1 c; omega) active.card
  set rOHAct := gOneHotFrom (K := k + 1) inputs rOHFull.1 rEAct.2.1 c0 c1 active.card
  have heOHA := hOHAct.2.1.len_le
  have hShift := gShiftAll_spec rOHAct.2 rOHFull.2 c0 hOHAct.1 (by omega) hOHAct.2.2.2.1
    (fun i => by have := hOHFull.2.2.2.1 i; omega) (k + 1)
  set rShift := gShiftAll inputs rOHAct.1 rOHAct.2 rOHFull.2 c0 (k + 1)
  have heSh := hShift.2.1.len_le
  have hFinal := gFinalAll_spec rShift.2 rCnt.2 c0 hShift.1 (by omega) hShift.2.2.2.1
    (fun i => by have := hCnt.2.2.2.1 i; omega) (k + 1)
  set rFinal := gFinalAll inputs rShift.1 rShift.2 rCnt.2 c0 (k + 1)
  let C : CCircuit := ⟨rFinal.1, 0⟩
  let out : Fin (k + 1) → Fin (inputs + C.size) := fun o => ⟨rFinal.2 o, hFinal.2.2.2.1 o⟩
  have hAct_le : active.card ≤ k := by have := Finset.card_le_univ active; simpa using this
  have hBnd_le : boundary.card ≤ k := by have := Finset.card_le_univ boundary; simpa using this
  have ht_le : t ≤ k := le_trans (min_le_right _ _) hBnd_le
  have hsize : C.size ≤ 512 * (k + m + 1) ^ 4 * 2 ^ t := by
    have hCsize : C.size = rFinal.1.length := rfl
    rw [hCsize]
    have hE1 : m * (active.card * (9 * active.card + 5)) ≤ m * (k * (9 * k + 5)) :=
      Nat.mul_le_mul_left m (Nat.mul_le_mul hAct_le (by omega))
    have hE2 : m * (boundary.card * (9 * boundary.card + 5)) ≤ m * (k * (9 * k + 5)) :=
      Nat.mul_le_mul_left m (Nat.mul_le_mul hBnd_le (by omega))
    have hCp : boundary.card * (t * (4 * boundary.card + 6)) ≤ k * (k * (4 * k + 6)) :=
      Nat.mul_le_mul hBnd_le (Nat.mul_le_mul ht_le (by omega))
    have hOHA : active.card * (4 * (k + 1)) ≤ k * (4 * (k + 1)) :=
      Nat.mul_le_mul_right _ hAct_le
    have htot : rFinal.1.length ≤
        2 + 3 * (m * (k * (9 * k + 5))) + k * (k * (4 * k + 6)) +
        2 ^ t * (9 * k * k + 241 * k + 7) +
        2 * (k * (4 * (k + 1))) + 2 * ((k + 1) * (2 * (k + 1))) := by
      have hr0 : r0.1.length = 1 := h0.2.2.1
      have hr1 : r1.1.length = 2 := by rw [h1.2.2.1, hr0]
      have hEF := hEFull.2.2.1
      have hEA := hEAct.2.2.1
      have hEB := hEBnd.2.2.1
      have hC' := hComp.2.2.1
      have hCt := hCnt.2.2.1
      have hOF := hOHFull.2.2.1
      have hOA := hOHAct.2.2.1
      have hSh := hShift.2.2.1
      have hFn := hFinal.2.2.1
      omega
    exact le_trans htot (size_bound_aux k m t)
  refine ⟨C, out, hFinal.1.1, hFinal.1.2, hsize, ?_⟩
  intro base gen u v cr cc key pack bits hprom count o
  have hbs := bits_spec base gen u v cr cc
  have hbits_len : bits.length = inputs := hbs.1
  have hvIn : ∀ {w : Nat} {b : Bool}, w < inputs → bits.getD w false = b → Val inputs [] bits w b :=
    fun hw hb => ⟨by simpa using hw, by simpa [evalWires] using hb⟩
  have hvBase : ∀ j, Val inputs [] bits (baseW j) (z2b (base j)) :=
    fun j => hvIn (hbaseW_lt j) (hbs.2.1 j)
  have hvGen : ∀ g j, Val inputs [] bits (genW g j) (z2b (gen g j)) :=
    fun g j => hvIn (hgenW_lt g j) (hbs.2.2.1 g j)
  have hvU : ∀ j, Val inputs [] bits (uW j) (z2b (u j)) :=
    fun j => hvIn (huW_lt j) (hbs.2.2.2.1 j)
  have hvV : ∀ j, Val inputs [] bits (vW j) (z2b (v j)) :=
    fun j => hvIn (hvW_lt j) (hbs.2.2.2.2.1 j)
  have hvCR : ∀ j, Val inputs [] bits (crW j) (z2b (cr j)) :=
    fun j => hvIn (hcrW_lt j) (hbs.2.2.2.2.2.1 j)
  have hvCC : ∀ j, Val inputs [] bits (ccW j) (z2b (cc j)) :=
    fun j => hvIn (hccW_lt j) (hbs.2.2.2.2.2.2 j)
  have hvc0_0 := h0.2.2.2.2 bits hbits_len
  have hvc0_1 := hvc0_0.mono hbits_len h1.2.1
  have hvc1_1 := h1.2.2.2.2 bits hbits_len
  have hext01 := h0.2.1.trans h1.2.1
  let rowsFull : Fin m → Fin k → Bool := fun g j => z2b (gen g j)
  let rowsAct : Fin m → Fin active.card → Bool := fun g c => z2b (gen g (ix k hk (s + (eA c).val.val)))
  let rowsBnd : Fin m → Fin boundary.card → Bool := fun g c => z2b (gen g (ix k hk (s + (eB c).val.val)))
  let baseAct : Fin active.card → Bool := fun c => z2b (base (ix k hk (s + (eA c).val.val)))
  let baseBnd : Fin boundary.card → Bool := fun c => z2b (base (ix k hk (s + (eB c).val.val)))
  have vEFull := hEFull.2.2.2.2.2 bits rowsFull hbits_len hvc0_1 (fun g j => (hvGen g j).mono hbits_len hext01)
  have hext1F := hEFull.2.1
  have vEAct := hEAct.2.2.2.2.2 bits rowsAct hbits_len (hvc0_1.mono hbits_len hext1F)
    (fun g c => (hvGen g _).mono hbits_len (hext01.trans hext1F))
  have hext1A := hext1F.trans hEAct.2.1
  have vEBnd := hEBnd.2.2.2.2.2 bits rowsBnd hbits_len (hvc0_1.mono hbits_len hext1A)
    (fun g c => (hvGen g _).mono hbits_len (hext01.trans hext1A))
  have hext1B := hext1A.trans hEBnd.2.1
  have vComp := hComp.2.2.2.2.2 bits (echelon rowsBnd).1 (echelon rowsBnd).2 hbits_len
    (hvc0_1.mono hbits_len hext1B) vEBnd.1 vEBnd.2
  have hext1C := hext1B.trans hComp.2.1
  have vCnt := hCnt.2.2.2.2 bits baseAct baseBnd (echelon rowsAct).1 (echelon rowsAct).2
    (compact (t := t) (echelon rowsBnd).1 (echelon rowsBnd).2).1
    (compact (t := t) (echelon rowsBnd).1 (echelon rowsBnd).2).2
    (vecToB u) (vecToB v) (vecToB cr) (vecToB cc) hbits_len
    (hvc0_1.mono hbits_len hext1C) (hvc1_1.mono hbits_len hext1C)
    (fun c => (hvBase _).mono hbits_len (hext01.trans hext1C))
    (fun c => (hvBase _).mono hbits_len (hext01.trans hext1C))
    (fun c => (vEAct.1 c).mono hbits_len (hEBnd.2.1.trans hComp.2.1))
    (fun i j => (vEAct.2 i j).mono hbits_len (hEBnd.2.1.trans hComp.2.1))
    vComp.1 vComp.2
    (fun j => (hvU j).mono hbits_len (hext01.trans hext1C))
    (fun j => (hvV j).mono hbits_len (hext01.trans hext1C))
    (fun j => (hvCR j).mono hbits_len (hext01.trans hext1C))
    (fun j => (hvCC j).mono hbits_len (hext01.trans hext1C))
  have hext1Cnt := hext1C.trans hCnt.2.1
  have vOHFull := hOHFull.2.2.2.2 bits (echelon rowsFull).1 hbits_len
    (hvc0_1.mono hbits_len hext1Cnt) (hvc1_1.mono hbits_len hext1Cnt)
    (fun c => (vEFull.1 c).mono hbits_len (hEAct.2.1.trans (hEBnd.2.1.trans (hComp.2.1.trans hCnt.2.1))))
  have hext1OHF := hext1Cnt.trans hOHFull.2.1
  have vOHAct := hOHAct.2.2.2.2 bits (echelon rowsAct).1 hbits_len
    (hvc0_1.mono hbits_len hext1OHF) (hvc1_1.mono hbits_len hext1OHF)
    (fun c => (vEAct.1 c).mono hbits_len (hEBnd.2.1.trans (hComp.2.1.trans (hCnt.2.1.trans hOHFull.2.1))))
  have hext1OHA := hext1OHF.trans hOHAct.2.1
  have hmath := count_eq_shifted k m q s hk row col base gen u v cr cc hprom
  dsimp only at hmath
  rcases hmath with ⟨hrAct_le, hrFull_le, _, hcount_eq⟩
  let rFull := (Finset.univ.filter (fun c : Fin k => (echelon rowsFull).1 c = true)).card
  let rAct := (Finset.univ.filter (fun c : Fin active.card => (echelon rowsAct).1 c = true)).card
  let M := (Finset.univ.filter (fun mask : Fin (2 ^ t) =>
    maskFlag k s hk row col q baseAct baseBnd (echelon rowsAct).1 (echelon rowsAct).2
      (compact (t := t) (echelon rowsBnd).1 (echelon rowsBnd).2).1
      (compact (t := t) (echelon rowsBnd).1 (echelon rowsBnd).2).2
      (vecToB u) (vecToB v) (vecToB cr) (vecToB cc) mask = true)).card
  have hrAct_le' : rAct ≤ rFull := hrAct_le
  have hrFull_le' : rFull ≤ k := hrFull_le
  have hcount_eq' : count = M * 2 ^ (rFull - rAct) := hcount_eq
  have hvOHFull' : ∀ i : Fin (k + 1), Val inputs rOHAct.1 bits (rOHFull.2 i) (decide (rFull = i.val)) := by
    intro i
    have hfilt : Finset.univ.filter (fun c : Fin k => c.val < k ∧ (echelon rowsFull).1 c = true) =
        Finset.univ.filter (fun c : Fin k => (echelon rowsFull).1 c = true) := by
      ext c; simp
    have h1' := (vOHFull i).mono hbits_len hOHAct.2.1
    rwa [hfilt] at h1'
  have hvOHAct' : ∀ i : Fin (k + 1), Val inputs rOHAct.1 bits (rOHAct.2 i) (decide (rAct = i.val)) := by
    intro i
    have hfilt : Finset.univ.filter (fun c : Fin active.card => c.val < active.card ∧ (echelon rowsAct).1 c = true) =
        Finset.univ.filter (fun c : Fin active.card => (echelon rowsAct).1 c = true) := by
      ext c; simp
    have h1' := vOHAct i
    rwa [hfilt] at h1'
  have vShift := hShift.2.2.2.2 bits rAct rFull hbits_len hrAct_le' (by omega)
    (hvc0_1.mono hbits_len hext1OHA) hvOHAct' hvOHFull'
  have hvCnt' : ∀ i : Fin (k + 1), Val inputs rShift.1 bits (rCnt.2 i) (M.testBit i.val) := by
    intro i
    have hfilt : Finset.univ.filter (fun mask : Fin (2 ^ t) => mask.val < 2 ^ t ∧
        maskFlag k s hk row col q baseAct baseBnd (echelon rowsAct).1 (echelon rowsAct).2
          (compact (t := t) (echelon rowsBnd).1 (echelon rowsBnd).2).1
          (compact (t := t) (echelon rowsBnd).1 (echelon rowsBnd).2).2
          (vecToB u) (vecToB v) (vecToB cr) (vecToB cc) mask = true) =
        Finset.univ.filter (fun mask : Fin (2 ^ t) =>
          maskFlag k s hk row col q baseAct baseBnd (echelon rowsAct).1 (echelon rowsAct).2
            (compact (t := t) (echelon rowsBnd).1 (echelon rowsBnd).2).1
            (compact (t := t) (echelon rowsBnd).1 (echelon rowsBnd).2).2
            (vecToB u) (vecToB v) (vecToB cr) (vecToB cc) mask = true) := by
      ext m0; simp
    have h1' := (vCnt i).mono hbits_len (hOHFull.2.1.trans (hOHAct.2.1.trans hShift.2.1))
    rwa [hfilt] at h1'
  have vFinal := hFinal.2.2.2.2 bits (rFull - rAct) M hbits_len (by omega)
    (hvc0_1.mono hbits_len (hext1OHA.trans hShift.2.1))
    (fun d => vShift d d.isLt) hvCnt' o o.isLt
  have hFinalVal : (C.wires bits).getD (out o).val false = (M * 2 ^ (rFull - rAct)).testBit o.val :=
    vFinal.2
  rw [hFinalVal, hcount_eq']

end PEqualNP.Outside.L_meta_25650_aux

theorem PEqualNP.Outside.L_meta_25650 :
∀ (k m q s : Nat) (hk : 0 < k),
  let W := Fin k → ZMod 2
  let X := Fin m → ZMod 2
  let ix := fun site : Nat => (⟨site % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (t : Nat) (v : W) (slot : Fin k) => v (ix (slot.val+k-t%k))
  let run := fun (d t f : Nat) (w name c : W) =>
    let z := rot t w + name
    let y := fun atMix : Fin k => z atMix + z (ix (atMix.val+d)) + z (ix (atMix.val+k-d%k))
    fun atOut : Fin k => y atOut + (1+y (ix (atOut.val+1))) * y (ix (atOut.val+2)) + rot f w atOut + c atOut
  ∀ (row col : Fin k → Bool),
    let active := Finset.univ.filter (fun reached : Fin k =>
      ∃ p : Fin k, ∃ e : Fin 7, ix (p.val+e.val) = reached ∧
        ((row p = true ∧ e.val ≤ 4) ∨ col p = true))
    let piv := Finset.univ.filter (fun p : Fin k =>
      (row p = true ∧ p.val+4 < k) ∨ (col p = true ∧ p.val+6 < k))
    let boundary := active \ piv
    let inputs := (m+5)*k
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (out : Fin (k+1) → Fin (inputs+C.size)),
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack inputs C ∧
      C.size ≤ 512*(k+m+1)^4 * 2^(min q boundary.card) ∧
      ∀ (base : W) (gen : Fin m → W) (u v cr cc : W),
        let key := fun a : X => base + ∑ i : Fin m, a i • gen i
        let pack := fun (word : W) => List.ofFn (fun j : Fin k => decide (word j ≠ 0))
        let bits := pack base ++ (List.ofFn (fun g => pack (gen g))).flatten ++
          pack u ++ pack v ++ pack cr ++ pack cc
        Nat.card (Set.range (fun coeff : X => fun member : boundary => key coeff (ix (s+member.val.val)))) ≤ 2^q →
        let count := Nat.card { w : W // w ∈ Set.range key ∧
          ∀ p : Fin k, (row p = true → run 1 1 0 w u cr (ix (s+p.val+2)) = 0) ∧
                        (col p = true → run 2 3 4 w v cc (ix (s+p.val+5)) = 0) }
        ∀ o : Fin (k+1), (C.wires bits).getD (out o).val false = count.testBit o.val := by
  intro k m q s hk W X ix0 rot run row col
  exact PEqualNP.Outside.L_meta_25650_aux.main_25650 k m q s hk row col
