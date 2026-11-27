import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_839_aux

theorem le_true_of {a b : Bool} (h : a ≤ b) (ha : a = true) : b = true := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide) | simp_all

theorem le_false_of {a b : Bool} (h : a ≤ b) (hb : b = false) : a = false := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide) | simp_all

theorem rowpart {n m : ℕ} (A : Fin n → Fin m → Bool) (r : Fin n) (c : Fin m)
    (R : Finset (Fin n)) (K : Finset (Fin m))
    (H : Finset (Fin n) → Finset (Fin m) → Bool)
    (D : Finset (Fin n) → Finset (Fin m) → Bool → Bool)
    (hr : r ∉ R) (hc : c ∉ K) (hinj : Function.Injective A)
    (hH0 : H ∅ ∅ = false) (hD0 : D ∅ ∅ false = false)
    (hHm : ∀ X X' Y Y', X ⊆ X' → Y ⊆ Y' → H X Y ≤ H X' Y')
    (hDm : ∀ X X' Y Y' a b, X ⊆ X' → Y ⊆ Y' → a ≤ b → D X Y a ≤ D X' Y' b)
    (hA : ∀ i j, A i j = D ({i} ∩ ((Finset.univ.erase r) \ R))
      ({j} ∩ ((Finset.univ.erase c) \ K)) (!(H ({i} ∩ R) ({j} ∩ K)))) :
    (A r c = false → R.card ≤ 1 ∧ ∀ i ∈ R, H {i} ∅ = true) ∧
    (A r c = true → D ∅ ∅ true = true ∧ ((Finset.univ.erase r) \ R).card ≤ 1 ∧
      ∀ i ∈ ((Finset.univ.erase r) \ R), D {i} ∅ false = true) := by
  set P := (Finset.univ.erase r) \ R with hPdef
  set Q := (Finset.univ.erase c) \ K with hQdef
  have rP : r ∉ P := by simp [P]
  have cQ : c ∉ Q := by simp [Q]
  have RP : ∀ i ∈ R, i ∉ P := fun i hi h => (Finset.mem_sdiff.1 h).2 hi
  have PR : ∀ i ∈ P, i ∉ R := fun i h => (Finset.mem_sdiff.1 h).2
  have KQ : ∀ j ∈ K, j ∉ Q := fun j hj h => (Finset.mem_sdiff.1 h).2 hj
  have Arc : A r c = D ∅ ∅ true := by
    rw [hA, Finset.singleton_inter_of_notMem rP, Finset.singleton_inter_of_notMem cQ,
      Finset.singleton_inter_of_notMem hr, Finset.singleton_inter_of_notMem hc, hH0]
    rfl
  refine ⟨fun h0 => ?_, fun h1 => ?_⟩
  · have hDt : D ∅ ∅ true = false := Arc.symm.trans h0
    have hDall : ∀ b, D ∅ ∅ b = false := fun b =>
      le_false_of (hDm ∅ ∅ ∅ ∅ b true subset_rfl subset_rfl (Bool.le_true b)) hDt
    have rowR : ∀ i ∈ R, ∀ j, A i j = if j ∈ K then false else D ∅ ({j} ∩ Q) (!H {i} ∅) := by
      intro i hi j
      rw [hA, Finset.singleton_inter_of_notMem (RP i hi), Finset.singleton_inter_of_mem hi]
      split_ifs with hj
      · rw [Finset.singleton_inter_of_notMem (KQ j hj)]
        exact hDall _
      · rw [Finset.singleton_inter_of_notMem hj]
    have rowr : ∀ j, A r j = if j ∈ K then false else D ∅ ({j} ∩ Q) true := by
      intro j
      rw [hA, Finset.singleton_inter_of_notMem rP, Finset.singleton_inter_of_notMem hr]
      split_ifs with hj
      · rw [Finset.singleton_inter_of_notMem (KQ j hj)]
        exact hDall _
      · rw [Finset.singleton_inter_of_notMem hj, hH0]
        rfl
    have HR : ∀ i ∈ R, H {i} ∅ = true := by
      intro i hi
      by_contra hne
      have hf : H {i} ∅ = false := by simpa using hne
      have : A r = A i := by
        funext j
        rw [rowr, rowR i hi, hf]
        rfl
      exact hr (hinj this ▸ hi)
    refine ⟨Finset.card_le_one.mpr (fun i hi i' hi' => hinj (funext fun j => ?_)), HR⟩
    rw [rowR i hi, rowR i' hi', HR i hi, HR i' hi']
  · have hDt : D ∅ ∅ true = true := Arc.symm.trans h1
    have rowP : ∀ i ∈ P, ∀ j, A i j = D {i} ({j} ∩ Q) (!H ∅ ({j} ∩ K)) := by
      intro i hi j
      rw [hA, Finset.singleton_inter_of_mem hi, Finset.singleton_inter_of_notMem (PR i hi)]
    have rowr : ∀ j, A r j = D ∅ ({j} ∩ Q) (!H ∅ ({j} ∩ K)) := by
      intro j
      rw [hA, Finset.singleton_inter_of_notMem rP, Finset.singleton_inter_of_notMem hr]
    have DP : ∀ i ∈ P, D {i} ∅ false = true := by
      intro i hi
      by_contra hne
      have hf : D {i} ∅ false = false := by simpa using hne
      have : A r = A i := by
        funext j
        rw [rowr, rowP i hi]
        cases hb : (!H ∅ ({j} ∩ K))
        · have hjK : j ∈ K := by
            by_contra hjK
            rw [Finset.singleton_inter_of_notMem hjK, hH0] at hb
            exact absurd hb (by decide)
          rw [Finset.singleton_inter_of_notMem (KQ j hjK), hD0, hf]
        · rw [le_true_of (hDm ∅ ∅ ∅ _ true true subset_rfl (Finset.empty_subset _) le_rfl) hDt,
            le_true_of (hDm ∅ {i} ∅ _ true true (Finset.empty_subset _) (Finset.empty_subset _)
              le_rfl) hDt]
      exact rP (hinj this ▸ hi)
    have allT : ∀ i ∈ P, ∀ j, A i j = true := by
      intro i hi j
      rw [rowP i hi]
      exact le_true_of (hDm {i} {i} ∅ _ false _ subset_rfl (Finset.empty_subset _)
        (Bool.false_le _)) (DP i hi)
    refine ⟨hDt, Finset.card_le_one.mpr (fun i hi i' hi' => hinj (funext fun j => ?_)), DP⟩
    rw [allT i hi, allT i' hi']

theorem main {n m : ℕ} (A : Fin n → Fin m → Bool) (r : Fin n) (c : Fin m)
    (R : Finset (Fin n)) (K : Finset (Fin m))
    (H : Finset (Fin n) → Finset (Fin m) → Bool)
    (D : Finset (Fin n) → Finset (Fin m) → Bool → Bool)
    (hr : r ∉ R) (hc : c ∉ K) (hinj : Function.Injective A)
    (hinjT : Function.Injective (fun j i => A i j))
    (hH0 : H ∅ ∅ = false) (hD0 : D ∅ ∅ false = false)
    (hHm : ∀ X X' Y Y', X ⊆ X' → Y ⊆ Y' → H X Y ≤ H X' Y')
    (hDm : ∀ X X' Y Y' a b, X ⊆ X' → Y ⊆ Y' → a ≤ b → D X Y a ≤ D X' Y' b)
    (hA : ∀ i j, A i j = D ({i} ∩ ((Finset.univ.erase r) \ R))
      ({j} ∩ ((Finset.univ.erase c) \ K)) (!(H ({i} ∩ R) ({j} ∩ K)))) :
    (A r c = false → R.card ≤ 1 ∧ K.card ≤ 1 ∧
      ∀ X ⊆ R, ∀ Y ⊆ K, H X Y = decide (X.Nonempty ∨ Y.Nonempty)) ∧
    (A r c = true → ((Finset.univ.erase r) \ R).card ≤ 1 ∧ ((Finset.univ.erase c) \ K).card ≤ 1 ∧
      ∀ X ⊆ ((Finset.univ.erase r) \ R), ∀ Y ⊆ ((Finset.univ.erase c) \ K), ∀ b : Bool,
        D X Y b = (b || decide (X.Nonempty ∨ Y.Nonempty))) := by
  have row := rowpart A r c R K H D hr hc hinj hH0 hD0 hHm hDm hA
  have col := rowpart (fun j i => A i j) c r K R (fun Y X => H X Y) (fun Y X b => D X Y b)
    hc hr hinjT hH0 hD0 (fun Y Y' X X' h1 h2 => hHm X X' Y Y' h2 h1)
    (fun Y Y' X X' a b h1 h2 h3 => hDm X X' Y Y' a b h2 h1 h3) (fun j i => hA i j)
  refine ⟨fun h0 => ?_, fun h1 => ?_⟩
  · obtain ⟨cR, HR⟩ := row.1 h0
    obtain ⟨cK, HK⟩ := col.1 h0
    refine ⟨cR, cK, fun X hX Y hY => ?_⟩
    by_cases hx : X.Nonempty
    · obtain ⟨i, hi⟩ := hx
      rw [le_true_of (hHm {i} X ∅ Y (Finset.singleton_subset_iff.2 hi) (Finset.empty_subset _))
        (HR i (hX hi))]
      have hn : X.Nonempty := ⟨i, hi⟩
      simp [hn]
    · by_cases hy : Y.Nonempty
      · obtain ⟨j, hj⟩ := hy
        rw [le_true_of (hHm ∅ X {j} Y (Finset.empty_subset _) (Finset.singleton_subset_iff.2 hj))
          (HK j (hY hj))]
        have hn : Y.Nonempty := ⟨j, hj⟩
        simp [hn]
      · rw [Finset.not_nonempty_iff_eq_empty] at hx hy
        subst hx hy
        simp [hH0]
  · obtain ⟨hDt, cP, DP⟩ := row.2 h1
    obtain ⟨_, cQ, DQ⟩ := col.2 h1
    refine ⟨cP, cQ, fun X hX Y hY b => ?_⟩
    by_cases hx : X.Nonempty
    · obtain ⟨i, hi⟩ := hx
      rw [le_true_of (hDm {i} X ∅ Y false b (Finset.singleton_subset_iff.2 hi)
        (Finset.empty_subset _) (Bool.false_le _)) (DP i (hX hi))]
      have hn : X.Nonempty := ⟨i, hi⟩
      simp [hn]
    · by_cases hy : Y.Nonempty
      · obtain ⟨j, hj⟩ := hy
        rw [le_true_of (hDm ∅ X {j} Y false b (Finset.empty_subset _)
          (Finset.singleton_subset_iff.2 hj) (Bool.false_le _)) (DQ j (hY hj))]
        have hn : Y.Nonempty := ⟨j, hj⟩
        simp [hn]
      · rw [Finset.not_nonempty_iff_eq_empty] at hx hy
        subst hx hy
        cases b
        · simp [hD0]
        · simp [hDt]

end PEqualNP.Outside.L_lib_839_aux

theorem PEqualNP.Outside.L_lib_839 : ∀ (n m : Nat) (A : Fin n → Fin m → Bool) (r : Fin n) (c : Fin m)
    (R : Finset (Fin n)) (K : Finset (Fin m))
    (H : Finset (Fin n) → Finset (Fin m) → Bool)
    (D : Finset (Fin n) → Finset (Fin m) → Bool → Bool),
  let P := (Finset.univ.erase r) \ R
  let Q := (Finset.univ.erase c) \ K
  r ∉ R → c ∉ K → Function.Injective A → Function.Injective (fun j i => A i j) →
  H ∅ ∅ = false → D ∅ ∅ false = false →
  (∀ X X' Y Y', X ⊆ X' → Y ⊆ Y' → H X Y ≤ H X' Y') →
  (∀ X X' Y Y' a b, X ⊆ X' → Y ⊆ Y' → a ≤ b → D X Y a ≤ D X' Y' b) →
  (∀ i j, A i j = D ({i} ∩ P) ({j} ∩ Q) (!(H ({i} ∩ R) ({j} ∩ K)))) →
  (A r c = false → R.card ≤ 1 ∧ K.card ≤ 1 ∧
    ∀ X ⊆ R, ∀ Y ⊆ K, H X Y = decide (X.Nonempty ∨ Y.Nonempty)) ∧
  (A r c = true → P.card ≤ 1 ∧ Q.card ≤ 1 ∧
    ∀ X ⊆ P, ∀ Y ⊆ Q, ∀ b : Bool, D X Y b = (b || decide (X.Nonempty ∨ Y.Nonempty))) := by
  intro n m A r c R K H D P Q hr hc hinj hinjT hH0 hD0 hHm hDm hA
  exact PEqualNP.Outside.L_lib_839_aux.main A r c R K H D hr hc hinj hinjT hH0 hD0 hHm hDm hA
