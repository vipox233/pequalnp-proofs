import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_692 : (∀ (q : Nat) (T : Fin (q + 3) → Fin q → Fin q), 7 ≤ q →
  let block := fun (j a : Fin q) => Finset.univ.filter (fun r : Fin (q + 3) => T r j = a)
  let triples := Finset.univ.filter (fun j : Fin q => ∃ a : Fin q, (block j a).card = 3)
  (∀ j a, (block j a).card ≤ 3) →
  (∃ j : Fin q, ∀ a : Fin q, (block j a).card ≤ 2) →
  (∀ (i j a b : Fin q), i ≠ j → (block i a).card = 3 → ((block j b) \ (block i a)).card ≤ 1) →
  triples.card ≤ 2) := by
  intro q T _ block triples h1 h2 h3
  obtain ⟨j0, hj0⟩ := h2
  have rows : ∀ j : Fin q, (Finset.univ : Finset (Fin (q + 3))).card = ∑ s : Fin q, (block j s).card :=
    fun j => Finset.card_eq_sum_card_fiberwise (fun r _ => Finset.mem_univ (T r j))
  have hD : 2 < (Finset.univ.filter (fun a : Fin q => (block j0 a).card = 2)).card := by
    by_contra hD
    have hle : ∑ a : Fin q, (block j0 a).card ≤ ∑ a : Fin q, (1 + if (block j0 a).card = 2 then 1 else 0) := by
      apply Finset.sum_le_sum
      intro a _
      have := hj0 a
      split <;> omega
    rw [← rows j0, Finset.sum_add_distrib, Finset.sum_boole] at hle
    simp at hle
    omega
  obtain ⟨b0, hb0, b1, hb1, b2, hb2, d01, d02, d12⟩ := Finset.two_lt_card.mp hD
  let b : Fin 3 → Fin q := ![b0, b1, b2]
  have hbcard : ∀ k, (block j0 (b k)).card = 2 := by
    intro k
    fin_cases k
    · exact (Finset.mem_filter.mp hb0).2
    · exact (Finset.mem_filter.mp hb1).2
    · exact (Finset.mem_filter.mp hb2).2
  have hbinj : Function.Injective b := by
    intro k l h
    fin_cases k <;> fin_cases l
    · rfl
    · exact absurd h d01
    · exact absurd h d02
    · exact absurd h.symm d01
    · rfl
    · exact absurd h d12
    · exact absurd h.symm d02
    · exact absurd h.symm d12
    · rfl
  have hpair : ∀ k, ∃ x y, x ≠ y ∧ block j0 (b k) = {x, y} := fun k => Finset.card_eq_two.mp (hbcard k)
  choose x y hxy hP using hpair
  have hdisj : ∀ k l r, r ∈ block j0 (b k) → r ∈ block j0 (b l) → k = l := by
    intro k l r hk hl
    apply hbinj
    exact ((Finset.mem_filter.mp hk).2).symm.trans (Finset.mem_filter.mp hl).2
  have key : ∀ i a, (block i a).card = 3 → ∃ c : Fin 3 → Fin (q + 3),
      (∀ k, c k ∈ block j0 (b k)) ∧ block i a = Finset.univ.image c := by
    intro i a ha
    have hi : i ≠ j0 := by
      intro e
      subst e
      have := hj0 a
      omega
    have hmeet : ∀ k, ∃ r, r ∈ block j0 (b k) ∧ r ∈ block i a := by
      intro k
      by_contra hne
      push Not at hne
      have e : block j0 (b k) \ block i a = block j0 (b k) :=
        Finset.sdiff_eq_self_of_disjoint (Finset.disjoint_left.mpr (fun {r} hr => hne r hr))
      have h := h3 i j0 a (b k) hi ha
      rw [e, hbcard k] at h
      omega
    choose c hc1 hc2 using hmeet
    refine ⟨c, hc1, ?_⟩
    have hcinj : Function.Injective c := fun k l h => hdisj k l (c k) (hc1 k) (h ▸ hc1 l)
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro r hr
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hr
      exact hc2 k
    · rw [ha, Finset.card_image_of_injective _ hcinj]
      simp
  have pair : ∀ (i j ai aj : Fin q) (ci cj : Fin 3 → Fin (q + 3)), i ≠ j → (block i ai).card = 3 →
      (∀ k, ci k ∈ block j0 (b k)) → (∀ k, cj k ∈ block j0 (b k)) →
      block i ai = Finset.univ.image ci → block j aj = Finset.univ.image cj →
      (¬ ∀ k, ci k = cj k) ∧ (∀ k l, k ≠ l → ci k = cj k ∨ ci l = cj l) := by
    intro i j ai aj ci cj hij hai mi mj ei ej
    have hout : ∀ k, ci k ≠ cj k → cj k ∈ block j aj \ block i ai := by
      intro k hne
      rw [Finset.mem_sdiff, ej, ei]
      refine ⟨Finset.mem_image_of_mem _ (Finset.mem_univ k), fun h => ?_⟩
      obtain ⟨m, _, hm⟩ := Finset.mem_image.mp h
      have e : m = k := hdisj m k (cj k) (hm ▸ mi m) (mj k)
      subst e
      exact hne hm
    constructor
    · intro hall
      have heq : block j aj = block i ai := by
        rw [ej, ei, show cj = ci from funext fun k => (hall k).symm]
      have hle : ∀ s, (block j s).card ≤ 1 + (if s = aj then 2 else 0) := by
        intro s
        split
        · have := h1 j s
          omega
        · rename_i hs
          have h := h3 i j ai s hij hai
          have e : block j s \ block i ai = block j s := by
            apply Finset.sdiff_eq_self_of_disjoint
            rw [← heq]
            apply Finset.disjoint_left.mpr
            intro r hr hr'
            exact hs (((Finset.mem_filter.mp hr).2).symm.trans (Finset.mem_filter.mp hr').2)
          rw [e] at h
          omega
      have h := Finset.sum_le_sum (s := Finset.univ) (fun s _ => hle s)
      rw [← rows j, Finset.sum_add_distrib, Finset.sum_ite_eq'] at h
      simp at h
    · intro k l hkl
      by_contra h
      push Not at h
      have hk := hout k h.1
      have hl := hout l h.2
      have hne : cj k ≠ cj l := fun e => hkl (hdisj k l (cj k) (mj k) (e ▸ mj l))
      have two : 1 < (block j aj \ block i ai).card := Finset.one_lt_card.mpr ⟨_, hk, _, hl, hne⟩
      have := h3 i j ai aj hij hai
      omega
  have bit : ∀ (ci cj : Fin 3 → Fin (q + 3)), (∀ k, ci k ∈ block j0 (b k)) → (∀ k, cj k ∈ block j0 (b k)) →
      ∀ k, (ci k = cj k ↔ decide (ci k = x k) = decide (cj k = x k)) := by
    intro ci cj mi mj k
    have u := mi k
    have v := mj k
    rw [hP k, Finset.mem_insert, Finset.mem_singleton] at u v
    rcases u with u | u <;> rcases v with v | v <;> simp [u, v, hxy k, (hxy k).symm]
  have conv : ∀ (ci cj : Fin 3 → Fin (q + 3)), (∀ k, ci k ∈ block j0 (b k)) → (∀ k, cj k ∈ block j0 (b k)) →
      ((¬ ∀ k, ci k = cj k) ∧ (∀ k l, k ≠ l → ci k = cj k ∨ ci l = cj l)) →
      ¬ (decide (ci 0 = x 0) = decide (cj 0 = x 0) ∧ decide (ci 1 = x 1) = decide (cj 1 = x 1) ∧
          decide (ci 2 = x 2) = decide (cj 2 = x 2)) ∧
        (decide (ci 0 = x 0) = decide (cj 0 = x 0) ∨ decide (ci 1 = x 1) = decide (cj 1 = x 1)) ∧
        (decide (ci 0 = x 0) = decide (cj 0 = x 0) ∨ decide (ci 2 = x 2) = decide (cj 2 = x 2)) ∧
        (decide (ci 1 = x 1) = decide (cj 1 = x 1) ∨ decide (ci 2 = x 2) = decide (cj 2 = x 2)) := by
    intro ci cj mi mj p
    refine ⟨fun h => p.1 (fun k => (bit ci cj mi mj k).mpr ?_),
      (p.2 0 1 (by decide)).imp (bit ci cj mi mj 0).mp (bit ci cj mi mj 1).mp,
      (p.2 0 2 (by decide)).imp (bit ci cj mi mj 0).mp (bit ci cj mi mj 2).mp,
      (p.2 1 2 (by decide)).imp (bit ci cj mi mj 1).mp (bit ci cj mi mj 2).mp⟩
    fin_cases k
    · exact h.1
    · exact h.2.1
    · exact h.2.2
  have cube : ∀ u0 u1 u2 v0 v1 v2 w0 w1 w2 : Bool,
      ¬ (u0 = v0 ∧ u1 = v1 ∧ u2 = v2) → (u0 = v0 ∨ u1 = v1) → (u0 = v0 ∨ u2 = v2) → (u1 = v1 ∨ u2 = v2) →
      ¬ (u0 = w0 ∧ u1 = w1 ∧ u2 = w2) → (u0 = w0 ∨ u1 = w1) → (u0 = w0 ∨ u2 = w2) → (u1 = w1 ∨ u2 = w2) →
      ¬ (v0 = w0 ∧ v1 = w1 ∧ v2 = w2) → (v0 = w0 ∨ v1 = w1) → (v0 = w0 ∨ v2 = w2) → (v1 = w1 ∨ v2 = w2) →
      False := by
    intro u0 u1 u2 v0 v1 v2 w0 w1 w2 f1 f2 f3 f4 g1 g2 g3 g4 k1 k2 k3 k4
    have par : ∀ a b c : Bool, ((if a = b then 0 else 1) + (if a = c then 0 else 1) +
        (if b = c then 0 else 1)) % 2 = 0 := by decide
    have one : ∀ (p q r : Prop) [Decidable p] [Decidable q] [Decidable r], ¬ (p ∧ q ∧ r) → (p ∨ q) → (p ∨ r) →
        (q ∨ r) → (if p then 0 else 1) + (if q then 0 else 1) + (if r then 0 else 1) = 1 := by
      intro p q r _ _ _ n x y z
      by_cases hp : p
      · by_cases hq : q
        · by_cases hr : r
          · exact absurd ⟨hp, hq, hr⟩ n
          · rw [if_pos hp, if_pos hq, if_neg hr]
        · have hr : r := z.resolve_left hq
          rw [if_pos hp, if_neg hq, if_pos hr]
      · have hq : q := x.resolve_left hp
        have hr : r := y.resolve_left hp
        rw [if_neg hp, if_pos hq, if_pos hr]
    have e0 := par u0 v0 w0
    have e1 := par u1 v1 w1
    have e2 := par u2 v2 w2
    have s1 := one _ _ _ f1 f2 f3 f4
    have s2 := one _ _ _ g1 g2 g3 g4
    have s3 := one _ _ _ k1 k2 k3 k4
    omega
  by_contra hcon
  have three : 2 < triples.card := by omega
  obtain ⟨i0, hi0, i1, hi1, i2, hi2, n01, n02, n12⟩ := Finset.two_lt_card.mp three
  obtain ⟨a0, ha0⟩ := (Finset.mem_filter.mp hi0).2
  obtain ⟨a1, ha1⟩ := (Finset.mem_filter.mp hi1).2
  obtain ⟨a2, ha2⟩ := (Finset.mem_filter.mp hi2).2
  obtain ⟨c0, m0, e0⟩ := key i0 a0 ha0
  obtain ⟨c1, m1, e1⟩ := key i1 a1 ha1
  obtain ⟨c2, m2, e2⟩ := key i2 a2 ha2
  obtain ⟨p1, p2, p3, p4⟩ := conv c0 c1 m0 m1 (pair i0 i1 a0 a1 c0 c1 n01 ha0 m0 m1 e0 e1)
  obtain ⟨r1, r2, r3, r4⟩ := conv c0 c2 m0 m2 (pair i0 i2 a0 a2 c0 c2 n02 ha0 m0 m2 e0 e2)
  obtain ⟨s1, s2, s3, s4⟩ := conv c1 c2 m1 m2 (pair i1 i2 a1 a2 c1 c2 n12 ha1 m1 m2 e1 e2)
  exact cube _ _ _ _ _ _ _ _ _ p1 p2 p3 p4 r1 r2 r3 r4 s1 s2 s3 s4
