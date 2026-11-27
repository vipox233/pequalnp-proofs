import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_879

open Finset

theorem inner {β : Type} [DecidableEq β] (A M : Finset β) :
    (∑ S ∈ M.powerset.filter (fun T => T.Nonempty),
      (if S ⊆ A then (-1 : ℤ) ^ S.card else 0)) =
      (if M ∩ A = ∅ then 1 else 0) - 1 := by
  have h1 : (∑ S ∈ M.powerset, (if S ⊆ A then (-1 : ℤ) ^ S.card else 0)) =
      (if M ∩ A = ∅ then 1 else 0) := by
    rw [← Finset.sum_filter, ← Finset.sum_powerset_neg_one_pow_card]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_inter_iff]
  have h2 : (∑ S ∈ M.powerset, (if S ⊆ A then (-1 : ℤ) ^ S.card else 0)) =
      (∑ S ∈ M.powerset.filter (fun T => T.Nonempty),
        (if S ⊆ A then (-1 : ℤ) ^ S.card else 0)) +
      ∑ S ∈ M.powerset.filter (fun T => ¬ T.Nonempty),
        (if S ⊆ A then (-1 : ℤ) ^ S.card else 0) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have h3 : M.powerset.filter (fun T => ¬ T.Nonempty) = {∅} := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.not_nonempty_iff_eq_empty,
      Finset.mem_singleton]
    constructor
    · exact fun h => h.2
    · intro h; subst h; exact ⟨Finset.empty_subset _, rfl⟩
  rw [h3, Finset.sum_singleton] at h2
  simp only [Finset.empty_subset, ite_true, Finset.card_empty, pow_zero] at h2
  linarith

theorem per_test {β : Type} [DecidableEq β] (A M : Finset β) (f g : Bool) :
    ((if (f || decide ((M ∩ A).Nonempty)) ≠ g then 1 else 0 : ℤ)) =
      (if (f || decide ((∅ ∩ A).Nonempty)) ≠ g then 1 else 0 : ℤ) +
      ∑ S ∈ M.powerset.filter (fun T => T.Nonempty),
        (-1 : ℤ) ^ S.card * (if f = false ∧ S ⊆ A then (if g then 1 else -1) else 0) := by
  have key : ∀ S : Finset β, (-1 : ℤ) ^ S.card * (if f = false ∧ S ⊆ A then (if g then 1 else -1) else 0)
      = (if f = false then (if g then 1 else -1) else 0) * (if S ⊆ A then (-1 : ℤ) ^ S.card else 0) := by
    intro S
    by_cases hf : f = false <;> by_cases hS : S ⊆ A <;> simp [hf, hS, mul_comm]
  simp_rw [key]
  rw [← Finset.mul_sum, inner]
  have hne : ((M ∩ A).Nonempty) ↔ ¬ (M ∩ A = ∅) := Finset.nonempty_iff_ne_empty
  by_cases hE : M ∩ A = ∅
  · have : ¬ (M ∩ A).Nonempty := by rw [hne]; simp [hE]
    cases f <;> cases g <;> simp [hE, this]
  · have : (M ∩ A).Nonempty := by rw [hne]; exact hE
    cases f <;> cases g <;> simp [hE, this]

theorem signed_eq {ι β : Type} [Fintype ι] [DecidableEq β] (D : ι → Finset β) (fixed target : ι → Bool)
    (S : Finset β) :
    ((Finset.univ.filter (fun t : ι => fixed t = false ∧ S ⊆ D t ∧ target t = true)).card : ℤ) -
    ((Finset.univ.filter (fun t : ι => fixed t = false ∧ S ⊆ D t ∧ target t = false)).card : ℤ) =
    ∑ t, (if fixed t = false ∧ S ⊆ D t then (if target t then 1 else -1) else 0 : ℤ) := by
  rw [Finset.natCast_card_filter, Finset.natCast_card_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t _
  by_cases hf : fixed t = false <;> by_cases hS : S ⊆ D t <;> cases h : target t <;> simp [hf, hS, h]

theorem expand {ι β : Type} [Fintype ι] [DecidableEq β] (D : ι → Finset β) (fixed target : ι → Bool)
    (M : Finset β) :
    (((Finset.univ.filter (fun t : ι =>
      (fixed t || decide ((M ∩ D t).Nonempty)) ≠ target t)).card : ℕ) : ℤ) =
    (((Finset.univ.filter (fun t : ι =>
      (fixed t || decide ((∅ ∩ D t).Nonempty)) ≠ target t)).card : ℕ) : ℤ) +
    ∑ S ∈ M.powerset.filter (fun T => T.Nonempty), (-1 : ℤ) ^ S.card *
      (((Finset.univ.filter (fun t : ι => fixed t = false ∧ S ⊆ D t ∧ target t = true)).card : ℤ) -
      ((Finset.univ.filter (fun t : ι => fixed t = false ∧ S ⊆ D t ∧ target t = false)).card : ℤ)) := by
  simp_rw [signed_eq, Finset.mul_sum]
  rw [Finset.sum_comm, Finset.natCast_card_filter, Finset.natCast_card_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  exact per_test (D t) M (fixed t) (target t)

theorem mobius {β : Type} [DecidableEq β] (P : Finset β → Prop)
    (hP : ∀ M S, P M → S ⊆ M → P S) (g h : Finset β → ℤ)
    (H : ∀ M, P M → ∑ S ∈ M.powerset, g S = ∑ S ∈ M.powerset, h S) :
    ∀ M, P M → g M = h M := by
  intro M
  induction M using Finset.strongInduction with
  | H M ih =>
    intro hM
    have e1 := Finset.sum_erase_add M.powerset g (Finset.mem_powerset_self M)
    have e2 := Finset.sum_erase_add M.powerset h (Finset.mem_powerset_self M)
    have e3 : ∑ S ∈ M.powerset.erase M, g S = ∑ S ∈ M.powerset.erase M, h S := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [Finset.mem_erase, Finset.mem_powerset] at hS
      have hss : S ⊂ M := Finset.ssubset_iff_subset_ne.mpr ⟨hS.2, hS.1⟩
      exact ih S hss (hP M S hM hS.2)
    have := H M hM
    linarith

theorem split_empty {β : Type} [DecidableEq β] (M : Finset β) (c : ℤ) (f : Finset β → ℤ) :
    ∑ S ∈ M.powerset, (if S = ∅ then c else f S) =
      c + ∑ S ∈ M.powerset.filter (fun T => T.Nonempty), f S := by
  rw [Finset.sum_ite]
  have h3 : M.powerset.filter (fun T => T = ∅) = {∅} := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
    constructor
    · exact fun h => h.2
    · intro h; subst h; exact ⟨Finset.empty_subset _, rfl⟩
  have h4 : M.powerset.filter (fun T => ¬ T = ∅) = M.powerset.filter (fun T => T.Nonempty) := by
    apply Finset.filter_congr
    intro S _
    rw [Finset.nonempty_iff_ne_empty]
  rw [h3, h4, Finset.sum_singleton]

theorem split_union {β : Type} [DecidableEq β] (K M : Finset β) (hKM : Disjoint K M)
    (g : Finset β → ℤ) :
    ∑ S ∈ (K ∪ M).powerset, g S = ∑ T ∈ M.powerset, ∑ A ∈ K.powerset, g (A ∪ T) := by
  rw [← Finset.sum_product' (f := fun T A => g (A ∪ T))]
  apply Finset.sum_nbij' (fun S => (S ∩ M, S ∩ K)) (fun p => p.2 ∪ p.1)
  · intro S _
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_powerset]
    exact ⟨Finset.inter_subset_right, Finset.inter_subset_right⟩
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_powerset] at hp ⊢
    exact Finset.union_subset_union hp.2 hp.1
  · intro S hS
    simp only [Finset.mem_coe, Finset.mem_powerset] at hS
    ext x
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact h.1
    · intro hx
      rcases Finset.mem_union.mp (hS hx) with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_powerset] at hp
    obtain ⟨p1, p2⟩ := p
    simp only at hp ⊢
    have d1 : ∀ x, x ∈ K → x ∉ M := fun x hx => Finset.disjoint_left.mp hKM hx
    refine Prod.ext ?_ ?_
    · ext x
      simp only [Finset.mem_union, Finset.mem_inter]
      constructor
      · rintro ⟨h | h, hm⟩
        · exact absurd hm (d1 x (hp.2 h))
        · exact h
      · intro h; exact ⟨Or.inr h, hp.1 h⟩
    · ext x
      simp only [Finset.mem_union, Finset.mem_inter]
      constructor
      · rintro ⟨h | h, hk⟩
        · exact h
        · exact absurd (hp.1 h) (d1 x hk)
      · intro h; exact ⟨Or.inl h, hp.2 h⟩
  · intro S hS
    simp only [Finset.mem_coe, Finset.mem_powerset] at hS
    simp only
    congr 1
    ext x
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · intro hx
      rcases Finset.mem_union.mp (hS hx) with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h

end PEqualNP.Outside.L_lib_879

open PEqualNP.Outside.L_lib_879 in
theorem PEqualNP.Outside.L_lib_879 : ∀ (k q : Nat) (D : Fin q → Finset (Finset (Fin k))) (fixed target : Fin q → Bool),
  let valid := fun (M : Finset (Finset (Fin k))) =>
    (∀ e ∈ M, e.card = 2) ∧ (∀ e ∈ M, ∀ g ∈ M, e ≠ g → Disjoint e g)
  let err := fun (M : Finset (Finset (Fin k))) =>
    (Finset.univ.filter (fun t : Fin q =>
      (fixed t || decide ((M ∩ D t).Nonempty)) ≠ target t)).card
  let signed := fun (S : Finset (Finset (Fin k))) =>
    ((Finset.univ.filter (fun t : Fin q => fixed t = false ∧ S ⊆ D t ∧ target t = true)).card : Int) -
    ((Finset.univ.filter (fun t : Fin q => fixed t = false ∧ S ⊆ D t ∧ target t = false)).card : Int)
  let low := fun (I : Finset (Finset (Fin k))) (d : Nat) =>
    ∀ K ⊆ I, valid K → ∃ h : Finset (Finset (Fin k)) → Int,
      ∀ M : Finset (Finset (Fin k)), Disjoint M I → valid (K ∪ M) →
        (err (K ∪ M) : Int) =
          ∑ T ∈ M.powerset.filter (fun V => V.card ≤ d), h T
  (∀ (I : Finset (Finset (Fin k))) (d : Nat), low I d ↔
    ∀ S, valid S → signed S ≠ 0 → (S \ I).card ≤ d) ∧
  ((∀ S, valid S → 3 ≤ S.card → signed S = 0) →
    ∀ j : Nat, ((∃ I : Finset (Finset (Fin k)), I.card ≤ j ∧ low I 1) ↔
      ∃ J : Finset (Finset (Fin k)), J.card ≤ j ∧
        ∀ a b : Finset (Fin k), a.card = 2 → b.card = 2 → Disjoint a b →
          signed {a,b} ≠ 0 → a ∈ J ∨ b ∈ J)) := by
  intro k q D fixed target valid err signed low
  have hexp : ∀ M, (err M : Int) = (err ∅ : Int) +
      ∑ S ∈ M.powerset.filter (fun T => T.Nonempty), (-1 : Int)^S.card * signed S :=
    fun M => expand D fixed target M
  have hdown : ∀ M S, valid M → S ⊆ M → valid S := by
    intro M S hM hS
    exact ⟨fun e he => hM.1 e (hS he), fun e he g hg hne => hM.2 e (hS he) g (hS hg) hne⟩
  let g : Finset (Finset (Fin k)) → Int := fun S =>
    if S = ∅ then (err ∅ : Int) else (-1 : Int)^S.card * signed S
  have hg : ∀ M, (err M : Int) = ∑ S ∈ M.powerset, g S := by
    intro M
    rw [hexp M]
    exact (split_empty M _ _).symm
  have gz : ∀ S, S ≠ ∅ → signed S = 0 → g S = 0 := by
    intro S hne h0
    simp only [g, hne, ite_false, h0, mul_zero]
  have gnz : ∀ S, S ≠ ∅ → g S = 0 → signed S = 0 := by
    intro S hne h
    simp only [g, hne, ite_false] at h
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd h1 (pow_ne_zero _ (by norm_num))
    · exact h1
  have part1 : ∀ (I : Finset (Finset (Fin k))) (d : Nat), low I d ↔
      ∀ S, valid S → signed S ≠ 0 → (S \ I).card ≤ d := by
    intro I d
    constructor
    · intro hlow S hS hs
      by_contra hc
      push_neg at hc
      have hTI : Disjoint (S \ I) I := Finset.sdiff_disjoint
      have hKI : ∀ K, K ⊆ S ∩ I → K ⊆ I := fun K hK => hK.trans Finset.inter_subset_right
      have hKS : ∀ K, K ⊆ S ∩ I → K ⊆ S := fun K hK => hK.trans Finset.inter_subset_left
      have zero : ∀ K, K ⊆ S ∩ I → ∑ A ∈ K.powerset, g (A ∪ (S \ I)) = 0 := by
        intro K hK
        obtain ⟨h, hh⟩ := hlow K (hKI K hK) (hdown S K hS (hKS K hK))
        let c : Finset (Finset (Fin k)) → Int := fun T' => ∑ A ∈ K.powerset, g (A ∪ T')
        let h' : Finset (Finset (Fin k)) → Int := fun T' => if T'.card ≤ d then h T' else 0
        have H : ∀ M, (Disjoint M I ∧ valid (K ∪ M)) →
            ∑ T' ∈ M.powerset, c T' = ∑ T' ∈ M.powerset, h' T' := by
          rintro M ⟨hMI, hMv⟩
          have hKM : Disjoint K M := Finset.disjoint_of_subset_left (hKI K hK) hMI.symm
          rw [← split_union K M hKM g, ← hg (K ∪ M), hh M hMI hMv, Finset.sum_filter]
        have hPd : ∀ M S', (Disjoint M I ∧ valid (K ∪ M)) → S' ⊆ M →
            (Disjoint S' I ∧ valid (K ∪ S')) := by
          rintro M S' ⟨h1, h2⟩ hS'
          exact ⟨Finset.disjoint_of_subset_left hS' h1,
            hdown _ _ h2 (Finset.union_subset_union (subset_refl K) hS')⟩
        have hKT : K ∪ (S \ I) ⊆ S := Finset.union_subset (hKS K hK) Finset.sdiff_subset
        have hm := mobius _ hPd c h' H (S \ I) ⟨hTI, hdown S _ hS hKT⟩
        have hnd : ¬ (S \ I).card ≤ d := by omega
        simp only [h', hnd, ite_false] at hm
        exact hm
      have hm := mobius (fun K => K ⊆ S ∩ I) (fun M S' hM hS' => hS'.trans hM)
        (fun A => g (A ∪ (S \ I))) (fun _ => 0)
        (fun M hM => by rw [zero M hM]; simp) (S ∩ I) (subset_refl _)
      have hS0 : S ∩ I ∪ S \ I = S := by
        ext x
        simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
        tauto
      simp only [hS0] at hm
      have hne : S ≠ ∅ := by
        intro h0
        rw [h0, Finset.empty_sdiff, Finset.card_empty] at hc
        exact Nat.not_lt_zero _ hc
      exact hs (gnz S hne hm)
    · intro H K hKI hK
      refine ⟨fun T => ∑ A ∈ K.powerset, g (A ∪ T), fun M hMI hv => ?_⟩
      have hKM : Disjoint K M := Finset.disjoint_of_subset_left hKI hMI.symm
      rw [hg (K ∪ M), split_union K M hKM g]
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro T hT hT'
      rw [Finset.mem_filter] at hT'
      have hTM : T ⊆ M := Finset.mem_powerset.mp hT
      have hd : d < T.card := by
        by_contra hc
        exact hT' ⟨hT, by omega⟩
      apply Finset.sum_eq_zero
      intro A hA
      have hAK : A ⊆ K := Finset.mem_powerset.mp hA
      have hsub : A ∪ T ⊆ K ∪ M := Finset.union_subset_union hAK hTM
      have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
      have hne : A ∪ T ≠ ∅ :=
        Finset.nonempty_iff_ne_empty.mp (hTne.mono Finset.subset_union_right)
      apply gz _ hne
      by_contra hs
      have h1 := H _ (hdown _ _ hv hsub) hs
      have hTsub : T ⊆ (A ∪ T) \ I := by
        intro x hx
        rw [Finset.mem_sdiff]
        exact ⟨Finset.mem_union_right _ hx, Finset.disjoint_left.mp hMI (hTM hx)⟩
      have h2 := Finset.card_le_card hTsub
      omega
  refine ⟨part1, fun H3 j => ⟨?_, ?_⟩⟩
  · rintro ⟨I, hIj, hI⟩
    refine ⟨I, hIj, fun a b ha hb hab hs => ?_⟩
    have hp := (part1 I 1).mp hI
    have hab' : a ≠ b := by
      intro h
      subst h
      have h0 : a = ∅ := by simpa using hab
      rw [h0, Finset.card_empty] at ha
      exact absurd ha (by norm_num)
    have hv : valid {a, b} := by
      refine ⟨?_, ?_⟩
      · intro e he
        rcases Finset.mem_insert.mp he with h | h
        · rw [h]; exact ha
        · rw [Finset.mem_singleton.mp h]; exact hb
      · intro e he f hf hef
        simp only [Finset.mem_insert, Finset.mem_singleton] at he hf
        rcases he with he | he <;> rcases hf with hf | hf <;> subst he <;> subst hf
        · exact absurd rfl hef
        · exact hab
        · exact hab.symm
        · exact absurd rfl hef
    have h1 := hp _ hv hs
    by_contra hc
    push_neg at hc
    have heq : ({a, b} : Finset (Finset (Fin k))) \ I = {a, b} := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · exact fun h => h.1
      · rintro (h | h)
        · subst h; exact ⟨Or.inl rfl, hc.1⟩
        · subst h; exact ⟨Or.inr rfl, hc.2⟩
    rw [heq, Finset.card_pair hab'] at h1
    omega
  · rintro ⟨J, hJj, hJ⟩
    refine ⟨J, hJj, (part1 J 1).mpr ?_⟩
    intro S hS hs
    by_contra hc
    push_neg at hc
    have hS2 : S.card ≤ 2 := by
      by_contra h
      push_neg at h
      exact hs (H3 S hS (by omega))
    have hsub : S \ J ⊆ S := Finset.sdiff_subset
    have heq : S \ J = S := Finset.eq_of_subset_of_card_le hsub (by omega)
    have hc2 : S.card = 2 := by rw [heq] at hc; omega
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hc2
    have ha : a ∈ ({a, b} : Finset (Finset (Fin k))) := Finset.mem_insert_self _ _
    have hb : b ∈ ({a, b} : Finset (Finset (Fin k))) :=
      Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    rcases hJ a b (hS.1 a ha) (hS.1 b hb) (hS.2 a ha b hb hab) hs with h | h
    · have hm : a ∈ ({a, b} : Finset (Finset (Fin k))) \ J := by rw [heq]; exact ha
      exact (Finset.mem_sdiff.mp hm).2 h
    · have hm : b ∈ ({a, b} : Finset (Finset (Fin k))) \ J := by rw [heq]; exact hb
      exact (Finset.mem_sdiff.mp hm).2 h
