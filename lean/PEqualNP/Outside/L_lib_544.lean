import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_544_aux

private def run {K : Type} [Field K] {q D : ℕ}
    (M : Fin q → (Fin D → K) →ₗ[K] (Fin D → K)) (s : Fin D → K)
    (w : List (Fin q)) : Fin D → K :=
  w.foldl (fun x a => M a x) s

private lemma run_nil {K : Type} [Field K] {q D : ℕ}
    (M : Fin q → (Fin D → K) →ₗ[K] (Fin D → K)) (s : Fin D → K) :
    run M s [] = s := rfl

private lemma run_append_singleton {K : Type} [Field K] {q D : ℕ}
    (M : Fin q → (Fin D → K) →ₗ[K] (Fin D → K)) (s : Fin D → K)
    (w : List (Fin q)) (a : Fin q) :
    run M s (w ++ [a]) = M a (run M s w) := by
  simp [run, List.foldl_append]

private lemma run_zero {K : Type} [Field K] {q D : ℕ}
    (M : Fin q → (Fin D → K) →ₗ[K] (Fin D → K)) (w : List (Fin q)) :
    run M 0 w = 0 := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w a ih =>
      rw [run_append_singleton, ih, map_zero]

private def Good {K : Type} [Field K] {q D : ℕ}
    (M : Fin q → (Fin D → K) →ₗ[K] (Fin D → K)) (s : Fin D → K)
    (P : Finset (List (Fin q))) : Prop :=
  [] ∈ P ∧ (∀ w a, w ++ [a] ∈ P → w ∈ P) ∧ LinearIndependent K (fun w : P => run M s w.val)

private lemma good_card_le {K : Type} [Field K] {q D : ℕ}
    (M : Fin q → (Fin D → K) →ₗ[K] (Fin D → K)) (s : Fin D → K)
    (P : Finset (List (Fin q))) (hP : Good M s P) :
    P.card ≤ D := by
  have h1 := hP.2.2.fintype_card_le_finrank
  rw [Fintype.card_coe, Module.finrank_fin_fun] at h1
  exact h1

private lemma take_mem_of_prefix_closed {α : Type*} (P : Finset (List α))
    (hpref : ∀ w a, w ++ [a] ∈ P → w ∈ P) :
    ∀ (m : ℕ) (w : List α) (k : ℕ), w ∈ P → k ≤ w.length → w.length - k ≤ m → w.take k ∈ P := by
  intro m
  induction m with
  | zero =>
      intro w k hw hkle hdiff
      have heq : k = w.length := by omega
      rw [heq, List.take_length]
      exact hw
  | succ m ih =>
      intro w k hw hkle hdiff
      by_cases heq : k = w.length
      · rw [heq, List.take_length]
        exact hw
      · have hlt : k < w.length := by omega
        have hk1 : w.take (k + 1) ∈ P := ih w (k + 1) hw (by omega) (by omega)
        have htake : w.take (k + 1) = w.take k ++ [w[k]'hlt] := List.take_succ_eq_append_getElem hlt
        rw [htake] at hk1
        exact hpref (w.take k) (w[k]'hlt) hk1

private lemma length_lt_card_of_prefix_closed {α : Type*} [DecidableEq α] (P : Finset (List α))
    (hpref : ∀ w a, w ++ [a] ∈ P → w ∈ P) (w : List α) (hw : w ∈ P) :
    w.length < P.card := by
  have hsub : (Finset.range (w.length + 1)).image (fun k => w.take k) ⊆ P := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨k, hk, rfl⟩
    have hkle : k ≤ w.length := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    exact take_mem_of_prefix_closed P hpref (w.length - k) w k hw hkle le_rfl
  have hinj : Set.InjOn (fun k => w.take k) (Finset.range (w.length + 1) : Set ℕ) := by
    intro k1 hk1 k2 hk2 hEq
    have h1 : k1 ≤ w.length := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk1)
    have h2 : k2 ≤ w.length := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk2)
    have hlen := congrArg List.length hEq
    rw [List.length_take, List.length_take, Nat.min_eq_left h1, Nat.min_eq_left h2] at hlen
    exact hlen
  have hcard : ((Finset.range (w.length + 1)).image (fun k => w.take k)).card = w.length + 1 := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hle := Finset.card_le_card hsub
  rw [hcard] at hle
  omega

private lemma good_singleton {K : Type} [Field K] {q D : ℕ}
    (M : Fin q → (Fin D → K) →ₗ[K] (Fin D → K)) (s : Fin D → K) (hs : s ≠ 0) :
    Good M s ({[]}) := by
  refine ⟨Finset.mem_singleton_self [], ?_, ?_⟩
  · intro w a h
    have heq := Finset.mem_singleton.mp h
    have hlen := congrArg List.length heq
    simp at hlen
  · rw [Fintype.linearIndependent_iff]
    intro c hc x
    have hx : x = ⟨[], Finset.mem_singleton_self []⟩ :=
      Subtype.ext (Finset.mem_singleton.mp x.2)
    have hsum : ∑ y : ({[]} : Finset (List (Fin q))), c y • run M s y.val =
        c ⟨[], Finset.mem_singleton_self []⟩ • s := by
      rw [Finset.sum_eq_single ⟨[], Finset.mem_singleton_self []⟩]
      · rfl
      · intro y _ hne
        exfalso
        exact hne (Subtype.ext (Finset.mem_singleton.mp y.2))
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hsum] at hc
    rcases smul_eq_zero.mp hc with h0 | hs0
    · rw [hx]
      exact h0
    · exact absurd hs0 hs

private lemma linearIndependent_insert_word {K : Type} [Field K] {q D : ℕ}
    (M : Fin q → (Fin D → K) →ₗ[K] (Fin D → K)) (s : Fin D → K)
    (P : Finset (List (Fin q))) (u : List (Fin q))
    (hli : LinearIndependent K (fun w : P => run M s w.val))
    (hnotspan : run M s u ∉ Submodule.span K (run M s '' (P : Set (List (Fin q))))) :
    LinearIndependent K (fun w : ↥(insert u P) => run M s w.val) := by
  classical
  have hunot : u ∉ P := fun hu =>
    hnotspan (Submodule.subset_span ⟨u, hu, rfl⟩)
  rw [Fintype.linearIndependent_iff]
  intro c hc
  let x0 : ↥(insert u P) := ⟨u, Finset.mem_insert_self u P⟩
  have hsplit :
      ∑ x : ↥(insert u P), c x • run M s x.val =
        c x0 • run M s u + ∑ x : P, c ⟨x.val, Finset.mem_insert_of_mem x.2⟩ • run M s x.val := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x0)]
    congr 1
    symm
    refine Finset.sum_bij (fun x _ => (⟨x.val, Finset.mem_insert_of_mem x.2⟩ : ↥(insert u P))) ?_ ?_ ?_ ?_
    · intro x _
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro heq
      have hval : x.val = u := congrArg Subtype.val heq
      exact hunot (hval ▸ x.2)
    · intro x1 _ x2 _ h
      exact Subtype.ext (congrArg (Subtype.val : ↥(insert u P) → List (Fin q)) h)
    · intro y hy
      have hne : y ≠ x0 := (Finset.mem_erase.mp hy).1
      have hy_ne : y.val ≠ u := fun h => hne (Subtype.ext h)
      have hyP : y.val ∈ P := by
        rcases Finset.mem_insert.mp y.2 with h | h
        · exact absurd h hy_ne
        · exact h
      exact ⟨⟨y.val, hyP⟩, Finset.mem_univ _, Subtype.ext rfl⟩
    · intro _ _
      rfl
  rw [hsplit] at hc
  have hcx0 : c x0 = 0 := by
    by_contra hne0
    have heq : run M s u = ∑ x : P, (-(c x0)⁻¹ * c ⟨x.val, Finset.mem_insert_of_mem x.2⟩) • run M s x.val := by
      have h1 : c x0 • run M s u = -(∑ x : P, c ⟨x.val, Finset.mem_insert_of_mem x.2⟩ • run M s x.val) :=
        eq_neg_of_add_eq_zero_left hc
      have h2 := congrArg (fun v => (c x0)⁻¹ • v) h1
      rw [smul_smul, inv_mul_cancel₀ hne0, one_smul, smul_neg, Finset.smul_sum, ← Finset.sum_neg_distrib] at h2
      rw [h2]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [smul_smul, neg_mul, neg_smul]
    have hmem : run M s u ∈ Submodule.span K (run M s '' (P : Set (List (Fin q)))) := by
      rw [heq]
      refine Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ ?_
      exact Submodule.subset_span ⟨x.val, x.2, rfl⟩
    exact hnotspan hmem
  rw [hcx0, zero_smul, zero_add] at hc
  have hrest := (Fintype.linearIndependent_iff.mp hli) (fun x : P => c ⟨x.val, Finset.mem_insert_of_mem x.2⟩) hc
  intro y
  by_cases hy : y.val = u
  · have : y = x0 := Subtype.ext hy
    rw [this, hcx0]
  · have hyP : y.val ∈ P := by
      rcases Finset.mem_insert.mp y.2 with h | h
      · exact absurd h hy
      · exact h
    exact hrest ⟨y.val, hyP⟩

private lemma exists_closed_good {K : Type} [Field K] {q D : ℕ}
    (M : Fin q → (Fin D → K) →ₗ[K] (Fin D → K)) (s : Fin D → K) :
    ∀ (k : ℕ) (P : Finset (List (Fin q))),
      Good M s P → D - P.card ≤ k →
      ∃ P' : Finset (List (Fin q)), Good M s P' ∧
        ∀ w ∈ P', ∀ a : Fin q, run M s (w ++ [a]) ∈ Submodule.span K (run M s '' (P' : Set (List (Fin q)))) := by
  intro k
  induction k with
  | zero =>
      intro P hP hdiff
      refine ⟨P, hP, ?_⟩
      by_contra hnot
      push Not at hnot
      rcases hnot with ⟨w, hwP, a, hnotspan⟩
      have hunot : w ++ [a] ∉ P := fun hu => hnotspan (Submodule.subset_span ⟨w ++ [a], hu, rfl⟩)
      let P1 := insert (w ++ [a]) P
      have hGood1 : Good M s P1 := by
        refine ⟨Finset.mem_insert_of_mem hP.1, ?_, linearIndependent_insert_word M s P (w ++ [a]) hP.2.2 hnotspan⟩
        intro u b hub
        rcases Finset.mem_insert.mp hub with heq | hmem
        · have hu : u = w := by
            have hdrop := congrArg List.dropLast heq
            simpa using hdrop
          exact Finset.mem_insert_of_mem (hu ▸ hwP)
        · exact Finset.mem_insert_of_mem (hP.2.1 u b hmem)
      have hcard1 : P1.card ≤ D := good_card_le M s P1 hGood1
      have hcard_eq : P1.card = P.card + 1 := Finset.card_insert_of_notMem hunot
      omega
  | succ k ih =>
      intro P hP hdiff
      by_cases hclosed : ∀ w ∈ P, ∀ a : Fin q,
          run M s (w ++ [a]) ∈ Submodule.span K (run M s '' (P : Set (List (Fin q))))
      · exact ⟨P, hP, hclosed⟩
      · push Not at hclosed
        rcases hclosed with ⟨w, hwP, a, hnotspan⟩
        have hunot : w ++ [a] ∉ P := fun hu => hnotspan (Submodule.subset_span ⟨w ++ [a], hu, rfl⟩)
        let P1 := insert (w ++ [a]) P
        have hGood1 : Good M s P1 := by
          refine ⟨Finset.mem_insert_of_mem hP.1, ?_, linearIndependent_insert_word M s P (w ++ [a]) hP.2.2 hnotspan⟩
          intro u b hub
          rcases Finset.mem_insert.mp hub with heq | hmem
          · have hu : u = w := by
              have hdrop := congrArg List.dropLast heq
              simpa using hdrop
            exact Finset.mem_insert_of_mem (hu ▸ hwP)
          · exact Finset.mem_insert_of_mem (hP.2.1 u b hmem)
        have hcard1 : P1.card ≤ D := good_card_le M s P1 hGood1
        have hcard_eq : P1.card = P.card + 1 := Finset.card_insert_of_notMem hunot
        exact ih P1 hGood1 (by omega)

private lemma prefixBasis {K : Type} [Field K] {q D : ℕ}
    (M : Fin q → (Fin D → K) →ₗ[K] (Fin D → K)) (s : Fin D → K) :
    ∃ P : Finset (List (Fin q)),
      P.card ≤ D ∧
      (∀ w ∈ P, w.length < D) ∧
      (∀ w a, w ++ [a] ∈ P → w ∈ P) ∧
      LinearIndependent K (fun w : P => run M s w.val) ∧
      (∀ w, run M s w ∈ Submodule.span K (run M s '' (P : Set (List (Fin q))))) := by
  by_cases hs : s = 0
  · subst hs
    refine ⟨∅, Nat.zero_le D, fun _ h => absurd h (Finset.notMem_empty _),
      fun _ _ h => absurd h (Finset.notMem_empty _), linearIndependent_empty_type, fun w => ?_⟩
    rw [run_zero]
    exact Submodule.zero_mem _
  · obtain ⟨P, hGood, hclosed⟩ := exists_closed_good M s D {[]} (good_singleton M s hs) (Nat.sub_le _ _)
    have hcard : P.card ≤ D := good_card_le M s P hGood
    have hlen : ∀ w ∈ P, w.length < D := fun w hw =>
      lt_of_lt_of_le (length_lt_card_of_prefix_closed P hGood.2.1 w hw) hcard
    have hinv : ∀ a : Fin q, ∀ v ∈ Submodule.span K (run M s '' (P : Set (List (Fin q)))),
        M a v ∈ Submodule.span K (run M s '' (P : Set (List (Fin q)))) := by
      intro a v hv
      have hle : Submodule.span K (run M s '' (P : Set (List (Fin q)))) ≤
          Submodule.comap (M a) (Submodule.span K (run M s '' (P : Set (List (Fin q))))) := by
        rw [Submodule.span_le]
        rintro _ ⟨w, hwP, rfl⟩
        change M a (run M s w) ∈ Submodule.span K (run M s '' (P : Set (List (Fin q))))
        rw [← run_append_singleton]
        exact hclosed w hwP a
      exact hle hv
    have hall : ∀ w, run M s w ∈ Submodule.span K (run M s '' (P : Set (List (Fin q)))) := by
      intro w
      induction w using List.reverseRecOn with
      | nil => exact Submodule.subset_span ⟨[], hGood.1, rfl⟩
      | append_singleton w a ih =>
          rw [run_append_singleton]
          exact hinv a _ ih
    exact ⟨P, hcard, hlen, hGood.2.1, hGood.2.2, hall⟩

end PEqualNP.Outside.L_lib_544_aux

theorem PEqualNP.Outside.L_lib_544 :
∀ (K : Type) [Field K] (q d : ℕ),
  let V := Fin d → K
  ∀ (s : V) (A : Fin q → V →ₗ[K] V),
    let run := fun (w : List (Fin q)) => w.foldl (fun x a => A a x) s
    ∃ P : Finset (List (Fin q)), P.card ≤ d ∧
      (∀ w ∈ P, w.length < d) ∧ (∀ w a, w ++ [a] ∈ P → w ∈ P) ∧
      LinearIndependent K (fun w : P => run w.val) ∧
      ∀ w, run w ∈ Submodule.span K (run '' (↑P : Set (List (Fin q)))) := by
  intro K _ q d V s A run
  exact PEqualNP.Outside.L_lib_544_aux.prefixBasis A s
