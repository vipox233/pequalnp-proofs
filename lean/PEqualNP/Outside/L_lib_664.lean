import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_664_aux

theorem two_add (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

theorem sum_zero_of_inv {V : Type*} [Fintype V] [AddCommGroup V] (e : V) (he : e ≠ 0)
    (he2 : e + e = 0) (P : V → ZMod 2) (hP : ∀ t, P (t + e) = P t) : ∑ t, P t = 0 := by
  apply Finset.sum_involution (fun t _ => t + e)
  · intro t _
    rw [hP]
    exact two_add _
  · intro t _ _ h
    apply he
    simpa using h
  · intro t _
    exact Finset.mem_univ _
  · intro t _
    rw [add_assoc, he2, add_zero]

theorem single_ne {r : ℕ} (l0 : Fin r) : (Pi.single l0 1 : Fin r → ZMod 2) ≠ 0 := by
  intro h
  have := congrFun h l0
  simp at this

theorem single_two {r : ℕ} (l0 : Fin r) :
    (Pi.single l0 1 : Fin r → ZMod 2) + Pi.single l0 1 = 0 := by
  ext x
  exact two_add _

theorem shift_apply {r : ℕ} (t : Fin r → ZMod 2) (l0 l : Fin r) (h : l ≠ l0) :
    (t + (Pi.single l0 (1 : ZMod 2) : Fin r → ZMod 2)) l = t l := by
  rw [Pi.add_apply, Pi.single_eq_of_ne h, add_zero]

theorem free_var {m r : ℕ} (mon : Finset (Fin m × Fin r)) (hmon : mon.card < r) :
    ∃ l0 : Fin r, l0 ∉ mon.image Prod.snd := by
  by_contra h
  push_neg at h
  have hsub : (Finset.univ : Finset (Fin r)) ⊆ mon.image Prod.snd := fun l _ => h l
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_image_le (s := mon) (f := Prod.snd)
  rw [Finset.card_univ, Fintype.card_fin] at h1
  omega

theorem cube_sum_mon {m r : ℕ} (mon : Finset (Fin m × Fin r)) (hmon : mon.card < r)
    (base : Fin m → Fin r → ZMod 2) :
    ∑ t : Fin r → ZMod 2, ∏ j ∈ mon, (base j.1 j.2 + t j.2) = 0 := by
  obtain ⟨l0, h0⟩ := free_var mon hmon
  apply sum_zero_of_inv (Pi.single l0 1) (single_ne l0) (single_two l0)
  intro t
  apply Finset.prod_congr rfl
  intro j hj
  have hne : j.2 ≠ l0 := fun h => h0 (h ▸ Finset.mem_image_of_mem _ hj)
  rw [shift_apply t l0 j.2 hne]

theorem cube_moment_mon {m r : ℕ} (mon : Finset (Fin m × Fin r)) (hmon : mon.card < r)
    (base : Fin m → Fin r → ZMod 2) (k : Fin r) :
    ∑ t : Fin r → ZMod 2, (∏ j ∈ mon, (base j.1 j.2 + t j.2)) * t k =
      ∑ t : Fin r → ZMod 2, (∏ j ∈ mon, t j.2) * t k := by
  classical
  by_cases hA : ∃ l0, l0 ∉ mon.image Prod.snd ∧ l0 ≠ k
  · obtain ⟨l0, h0, hk⟩ := hA
    have both : ∀ b : Fin m → Fin r → ZMod 2,
        ∑ t : Fin r → ZMod 2, (∏ j ∈ mon, (b j.1 j.2 + t j.2)) * t k = 0 := by
      intro b
      apply sum_zero_of_inv (Pi.single l0 1) (single_ne l0) (single_two l0)
      intro t
      congr 1
      · apply Finset.prod_congr rfl
        intro j hj
        have hne : j.2 ≠ l0 := fun h => h0 (h ▸ Finset.mem_image_of_mem _ hj)
        rw [shift_apply t l0 j.2 hne]
      · exact shift_apply t l0 k (Ne.symm hk)
    rw [both base]
    have := both 0
    simp only [Pi.zero_apply, zero_add] at this
    rw [this]
  · push_neg at hA
    have hkL : k ∉ mon.image Prod.snd := by
      intro hk
      have hall : (Finset.univ : Finset (Fin r)) ⊆ mon.image Prod.snd := by
        intro l _
        by_cases hl : l = k
        · rw [hl]
          exact hk
        · by_contra hn
          exact hl (hA l hn)
      have h1 := Finset.card_le_card hall
      have h2 := Finset.card_image_le (s := mon) (f := Prod.snd)
      rw [Finset.card_univ, Fintype.card_fin] at h1
      omega
    have hcardL : (mon.image Prod.snd).card = mon.card := by
      have hsub : (Finset.univ.erase k) ⊆ mon.image Prod.snd := by
        intro l hl
        by_contra hn
        exact (Finset.mem_erase.1 hl).1 (hA l hn)
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_image_le (s := mon) (f := Prod.snd)
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at h1
      omega
    have hinj : Set.InjOn Prod.snd (mon : Set (Fin m × Fin r)) :=
      Finset.injOn_of_card_image_eq hcardL
    let c : Fin r → ZMod 2 := fun l => ∑ j ∈ mon.filter (fun j => j.2 = l), base j.1 j.2
    have hc : ∀ j ∈ mon, c j.2 = base j.1 j.2 := by
      intro j hj
      have hf : mon.filter (fun j' => j'.2 = j.2) = {j} := by
        ext j'
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hj', he⟩
          exact hinj hj' hj he
        · rintro rfl
          exact ⟨hj, rfl⟩
      show ∑ j' ∈ mon.filter (fun j' => j'.2 = j.2), base j'.1 j'.2 = _
      rw [hf, Finset.sum_singleton]
    have hck : c k = 0 := by
      have hf : mon.filter (fun j => j.2 = k) = ∅ := by
        ext j
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro hj hjk
        exact hkL (hjk ▸ Finset.mem_image_of_mem _ hj)
      show ∑ j ∈ mon.filter (fun j => j.2 = k), base j.1 j.2 = 0
      rw [hf, Finset.sum_empty]
    have hprod : ∀ t : Fin r → ZMod 2, ∏ j ∈ mon, (base j.1 j.2 + t j.2) = ∏ j ∈ mon, (t + c) j.2 := by
      intro t
      apply Finset.prod_congr rfl
      intro j hj
      rw [Pi.add_apply, hc j hj, add_comm]
    simp only [hprod]
    apply Fintype.sum_equiv (Equiv.addRight c)
    intro t
    simp only [Equiv.coe_addRight, Pi.add_apply, hck, add_zero]

end PEqualNP.Outside.L_lib_664_aux

open PEqualNP.Outside.L_lib_664_aux in
theorem PEqualNP.Outside.L_lib_664 : (∀ (r m : Nat), 0 < r →
  let K := ZMod 2
  let V := Fin r → K
  let W := Fin m → V
  let I := Fin m × Fin r
  let low := fun (f : W → K) => ∃ T : Finset (Finset I),
    (∀ mon ∈ T, mon.card < r) ∧
    ∀ word, f word = ∑ mon ∈ T, ∏ j ∈ mon, word j.1 j.2
  ∀ (point : Fin m → V) (pred : Fin m → W → K), (∀ i, low (pred i)) →
    ∃ tag : Fin m → V, ∀ (base : W) (i : Fin m),
      let bad := (Finset.univ : Finset V).filter (fun t =>
        pred i (fun j => base j + t) ≠ (if base i + t = point i then 1 else 0))
      bad.card % 2 = 1 ∧ ∀ k : Fin r, (∑ t ∈ bad, t k) = base i k + tag i k) := by
  intro r m hr K V W I low point pred hlow
  classical
  choose T hT hTe using hlow
  have hsum0 : ∀ (i : Fin m) (base : W), ∑ t : V, pred i (fun j => base j + t) = 0 := by
    intro i base
    simp only [hTe i]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro mon hmon
    exact cube_sum_mon mon (hT i mon hmon) base
  have hmom : ∀ (i : Fin m) (base : W) (k : Fin r),
      ∑ t : V, pred i (fun j => base j + t) * t k = ∑ t : V, pred i (fun _ => t) * t k := by
    intro i base k
    simp only [hTe i, Finset.sum_mul]
    rw [Finset.sum_comm, Finset.sum_comm (s := (Finset.univ : Finset V))]
    apply Finset.sum_congr rfl
    intro mon hmon
    exact cube_moment_mon mon (hT i mon hmon) base k
  have hb : ∀ x y : ZMod 2, (if x ≠ y then (1 : ZMod 2) else 0) = x + y := by decide
  have hs : ∀ x y : ZMod 2, x - y = x + y := by decide
  refine ⟨fun i k => ∑ t : V, pred i (fun _ => t) * t k + point i k, ?_⟩
  intro base i bad
  have hind : ∀ t : V, (base i + t = point i) ↔ (t = point i - base i) := by
    intro t
    rw [eq_sub_iff_add_eq']
  have hh : ∑ t : V, (if base i + t = point i then (1 : ZMod 2) else 0) = 1 := by
    simp only [hind]
    simp
  have hhk : ∀ k : Fin r, ∑ t : V, (if base i + t = point i then (1 : ZMod 2) else 0) * t k =
      point i k + base i k := by
    intro k
    simp only [hind, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [Pi.sub_apply, hs]
  refine ⟨?_, ?_⟩
  · have hc : ((bad.card : ℕ) : ZMod 2) = 1 := by
      rw [Finset.cast_card]
      show ∑ _t ∈ Finset.univ.filter (fun t => pred i (fun j => base j + t) ≠
        (if base i + t = point i then 1 else 0)), (1 : ZMod 2) = 1
      rw [Finset.sum_filter]
      simp only [hb]
      rw [Finset.sum_add_distrib, hsum0 i base, hh, zero_add]
    rw [← ZMod.val_natCast, hc]
    rfl
  · intro k
    show ∑ t ∈ Finset.univ.filter (fun t => pred i (fun j => base j + t) ≠
        (if base i + t = point i then 1 else 0)), t k = _
    rw [Finset.sum_filter]
    have hk2 : ∀ t : V, (if pred i (fun j => base j + t) ≠
        (if base i + t = point i then (1 : ZMod 2) else 0) then t k else 0) =
        (pred i (fun j => base j + t) + (if base i + t = point i then (1 : ZMod 2) else 0)) * t k := by
      intro t
      rw [← hb]
      split_ifs <;> simp
    simp only [hk2, add_mul]
    rw [Finset.sum_add_distrib, hmom i base k, hhk k]
    ring
