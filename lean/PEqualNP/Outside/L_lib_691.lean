import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_691

lemma fwd (q : ℕ) (T : Fin (q + 3) → Fin q → Fin q)
    (hT : ∀ (j a : Fin q), (Finset.univ.filter (fun r : Fin (q + 3) => T r j = a)).card ≤ 2)
    (x : Fin q → Fin q) (hx : ∀ r : Fin (q + 3), ∃ j : Fin q, T r j = x j) :
    ∃ (c : Fin 3 → Fin q) (P : Fin 3 → Finset (Fin (q + 3))),
      Function.Injective c ∧
      (∀ k : Fin 3, (P k).card = 2 ∧ ∃ a : Fin q, ∀ r ∈ P k, T r (c k) = a) ∧
      (∀ i j : Fin 3, i ≠ j → Disjoint (P i) (P j)) := by
  choose f hf using hx
  have hfib : ∀ j : Fin q, (Finset.univ.filter (fun r : Fin (q + 3) => f r = j)).card ≤ 2 := by
    intro j
    refine le_trans (Finset.card_le_card ?_) (hT j (x j))
    intro r hr
    have hr' : f r = j := (Finset.mem_filter.mp hr).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ r, ?_⟩
    rw [← hr']
    exact hf r
  have hsum : (Finset.univ : Finset (Fin (q + 3))).card =
      ∑ j : Fin q, (Finset.univ.filter (fun r : Fin (q + 3) => f r = j)).card :=
    Finset.card_eq_sum_card_fiberwise (fun r _ => Finset.mem_univ (f r))
  rw [Finset.card_univ, Fintype.card_fin] at hsum
  have hA : 3 ≤ (Finset.univ.filter
      (fun j : Fin q => (Finset.univ.filter (fun r : Fin (q + 3) => f r = j)).card = 2)).card := by
    have hle : ∑ j : Fin q, (Finset.univ.filter (fun r : Fin (q + 3) => f r = j)).card ≤
        ∑ j : Fin q, (1 + if (Finset.univ.filter (fun r : Fin (q + 3) => f r = j)).card = 2 then 1 else 0) := by
      refine Finset.sum_le_sum fun j _ => ?_
      have := hfib j
      split_ifs <;> omega
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one,
      Finset.sum_boole] at hle
    simp only [Nat.cast_id] at hle
    omega
  obtain ⟨B, hBA, hB⟩ := Finset.exists_subset_card_eq hA
  let e := Finset.equivFinOfCardEq hB
  refine ⟨fun k => (e.symm k).1, fun k => Finset.univ.filter (fun r : Fin (q + 3) => f r = (e.symm k).1),
    Subtype.val_injective.comp e.symm.injective, ?_, ?_⟩
  · intro k
    refine ⟨(Finset.mem_filter.mp (hBA (e.symm k).2)).2, x (e.symm k).1, ?_⟩
    intro r hr
    have hr' : f r = (e.symm k).1 := (Finset.mem_filter.mp hr).2
    show T r (e.symm k).1 = x (e.symm k).1
    rw [← hr']
    exact hf r
  · intro i j hij
    rw [Finset.disjoint_left]
    intro r hri hrj
    have h1 : f r = (e.symm i).1 := (Finset.mem_filter.mp hri).2
    have h2 : f r = (e.symm j).1 := (Finset.mem_filter.mp hrj).2
    exact hij (e.symm.injective (Subtype.ext (h1.symm.trans h2)))

lemma bwd (q : ℕ) (T : Fin (q + 3) → Fin q → Fin q) (hq : 7 ≤ q)
    (c : Fin 3 → Fin q) (P : Fin 3 → Finset (Fin (q + 3))) (hc : Function.Injective c)
    (hP : ∀ k : Fin 3, (P k).card = 2 ∧ ∃ a : Fin q, ∀ r ∈ P k, T r (c k) = a)
    (hd : ∀ i j : Fin 3, i ≠ j → Disjoint (P i) (P j)) :
    ∃ x : Fin q → Fin q, ∀ r : Fin (q + 3), ∃ j : Fin q, T r j = x j := by
  classical
  choose a ha using fun k => (hP k).2
  have hU : (Finset.univ.biUnion P).card = 6 := by
    rw [Finset.card_biUnion (fun i _ j _ hij => hd i j hij)]
    simp [fun k => (hP k).1]
  have hI : (Finset.univ.image c).card = 3 := by
    rw [Finset.card_image_of_injective _ hc]
    simp
  have hRJ : ((Finset.univ.biUnion P)ᶜ).card = ((Finset.univ.image c)ᶜ).card := by
    rw [Finset.card_compl, Finset.card_compl, hU, hI, Fintype.card_fin, Fintype.card_fin]
    omega
  let g := Finset.equivOfCardEq hRJ
  refine ⟨fun j => if h : ∃ k, c k = j then a (Classical.choose h)
    else if hj : j ∈ (Finset.univ.image c)ᶜ then T (g.symm ⟨j, hj⟩).1 j else j, ?_⟩
  intro r
  by_cases hr : ∃ k, r ∈ P k
  · obtain ⟨k, hk⟩ := hr
    refine ⟨c k, ?_⟩
    have hex : ∃ k', c k' = c k := ⟨k, rfl⟩
    dsimp only
    rw [dif_pos hex]
    have hk' : Classical.choose hex = k := hc (Classical.choose_spec hex)
    rw [hk']
    exact ha k r hk
  · have hrR : r ∈ (Finset.univ.biUnion P)ᶜ := by
      rw [Finset.mem_compl, Finset.mem_biUnion]
      rintro ⟨k, -, hk⟩
      exact hr ⟨k, hk⟩
    refine ⟨(g ⟨r, hrR⟩).1, ?_⟩
    have hj : (g ⟨r, hrR⟩).1 ∈ (Finset.univ.image c)ᶜ := (g ⟨r, hrR⟩).2
    have hne : ¬ ∃ k, c k = (g ⟨r, hrR⟩).1 := by
      rintro ⟨k, hk⟩
      rw [Finset.mem_compl] at hj
      exact hj (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hk⟩)
    dsimp only
    rw [dif_neg hne, dif_pos hj]
    have he : g.symm ⟨(g ⟨r, hrR⟩).1, hj⟩ = ⟨r, hrR⟩ := g.symm_apply_apply ⟨r, hrR⟩
    rw [he]

end PEqualNP.Outside.L_lib_691

theorem PEqualNP.Outside.L_lib_691 : ∀ (q : Nat) (T : Fin (q + 3) → Fin q → Fin q), 7 ≤ q →
  (∀ (j a : Fin q), (Finset.univ.filter (fun r : Fin (q + 3) => T r j = a)).card ≤ 2) →
  ((∃ x : Fin q → Fin q, ∀ r : Fin (q + 3), ∃ j : Fin q, T r j = x j) ↔
    ∃ (c : Fin 3 → Fin q) (P : Fin 3 → Finset (Fin (q + 3))),
      Function.Injective c ∧
      (∀ k : Fin 3, (P k).card = 2 ∧ ∃ a : Fin q, ∀ r ∈ P k, T r (c k) = a) ∧
      (∀ i j : Fin 3, i ≠ j → Disjoint (P i) (P j))) := by
  intro q T hq hT
  constructor
  · rintro ⟨x, hx⟩
    exact PEqualNP.Outside.L_lib_691.fwd q T hT x hx
  · rintro ⟨c, P, hc, hP, hd⟩
    exact PEqualNP.Outside.L_lib_691.bwd q T hq c P hc hP hd
