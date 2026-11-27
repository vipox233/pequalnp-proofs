import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_396

lemma exists_readout {d t q : ℕ}
    (P : (Fin d → ZMod 2) →ₗ[ZMod 2] (Fin t → ZMod 2))
    (Q : (Fin d → ZMod 2) →ₗ[ZMod 2] (Fin q → ZMod 2)) :
    ∃ readout : (Fin q → ZMod 2) →ₗ[ZMod 2] ((Fin t → ZMod 2) ⧸ (LinearMap.ker Q).map P),
      ∀ z, readout (Q z) = ((LinearMap.ker Q).map P).mkQ (P z) := by
  set K := (LinearMap.ker Q).map P with hK
  have hle : LinearMap.ker Q ≤ LinearMap.ker (K.mkQ.comp P) := by
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_map_of_mem hx
  let g0 : LinearMap.range Q →ₗ[ZMod 2] ((Fin t → ZMod 2) ⧸ K) :=
    ((LinearMap.ker Q).liftQ (K.mkQ.comp P) hle).comp
      (Q.quotKerEquivRange.symm : LinearMap.range Q →ₗ[ZMod 2] _)
  obtain ⟨g, hg⟩ := LinearMap.exists_extend g0
  refine ⟨g, fun z => ?_⟩
  have h1 : g (Q z) = g0 ⟨Q z, LinearMap.mem_range_self Q z⟩ := by
    rw [← hg]; rfl
  rw [h1]
  show ((LinearMap.ker Q).liftQ (K.mkQ.comp P) hle)
    (Q.quotKerEquivRange.symm ⟨Q z, LinearMap.mem_range_self Q z⟩) = _
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

lemma count {d t q : ℕ}
    (P : (Fin d → ZMod 2) →ₗ[ZMod 2] (Fin t → ZMod 2))
    (Q : (Fin d → ZMod 2) →ₗ[ZMod 2] (Fin q → ZMod 2))
    (good : (Fin t → ZMod 2) → Prop) [DecidablePred good]
    [DecidableEq ((Fin t → ZMod 2) ⧸ (LinearMap.ker Q).map P)] (x0 : Fin d → ZMod 2) :
    (Finset.univ.filter (fun x : Fin d → ZMod 2 => Q x = Q x0 ∧ good (P x))).card =
      2 ^ Module.finrank (ZMod 2)
        (LinearMap.ker Q ⊓ LinearMap.ker P : Submodule (ZMod 2) (Fin d → ZMod 2)) *
      (Finset.univ.filter (fun u : Fin t → ZMod 2 =>
        ((LinearMap.ker Q).map P).mkQ u = ((LinearMap.ker Q).map P).mkQ (P x0) ∧
          good u)).card := by
  classical
  set N : Submodule (ZMod 2) (Fin d → ZMod 2) := LinearMap.ker Q ⊓ LinearMap.ker P
  have hN : Fintype.card N = 2 ^ Module.finrank (ZMod 2) N := by
    have := Module.card_eq_pow_finrank (K := ZMod 2) (V := N)
    simpa [ZMod.card] using this
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x => P x)
    (t := Finset.univ.filter (fun u : Fin t → ZMod 2 =>
        ((LinearMap.ker Q).map P).mkQ u = ((LinearMap.ker Q).map P).mkQ (P x0) ∧ good u))]
  · rw [Finset.sum_const_nat (m := 2 ^ Module.finrank (ZMod 2) N), mul_comm]
    intro u hu
    rw [Finset.mem_filter] at hu
    obtain ⟨-, hu1, hu2⟩ := hu
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hu1
    obtain ⟨k, hk, hPk⟩ := hu1
    rw [SetLike.mem_coe, LinearMap.mem_ker] at hk
    have hPx1 : P (x0 + k) = u := by rw [map_add, hPk]; abel
    have hQx1 : Q (x0 + k) = Q x0 := by rw [map_add, hk, add_zero]
    rw [← hN, ← Finset.card_univ]
    refine Finset.card_bij' (fun x _ => (⟨x - (x0 + k), ?_⟩ : N))
      (fun n _ => (n : Fin d → ZMod 2) + (x0 + k)) ?_ ?_ ?_ ?_
    · rename_i hx
      rw [Finset.mem_filter, Finset.mem_filter] at hx
      obtain ⟨⟨-, hx1, -⟩, hx2⟩ := hx
      refine ⟨?_, ?_⟩
      · show Q (x - (x0 + k)) = 0
        rw [map_sub, hQx1, hx1, sub_self]
      · show P (x - (x0 + k)) = 0
        rw [map_sub, hPx1, hx2, sub_self]
    · intro x hx; exact Finset.mem_univ _
    · intro n _
      have hn1 : Q (n : Fin d → ZMod 2) = 0 := n.2.1
      have hn2 : P (n : Fin d → ZMod 2) = 0 := n.2.2
      rw [Finset.mem_filter, Finset.mem_filter]
      refine ⟨⟨Finset.mem_univ _, ?_, ?_⟩, ?_⟩
      · rw [map_add, hn1, zero_add, hQx1]
      · rw [map_add, hn2, zero_add, hPx1]; exact hu2
      · show P (_ + _) = u
        rw [map_add, hn2, zero_add, hPx1]
    · intro x hx; simp
    · intro n _; simp
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_filter] at hx ⊢
    obtain ⟨-, hx1, hx2⟩ := hx
    refine ⟨Finset.mem_univ _, ?_, hx2⟩
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    refine ⟨x - x0, ?_, map_sub _ _ _⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, hx1, sub_self]

end PEqualNP.Outside.L_lib_396

theorem PEqualNP.Outside.L_lib_396 : (∀ d t q v : ℕ,
  let H := Fin d → ZMod 2
  let U := Fin t → ZMod 2
  let R := Fin q → ZMod 2
  ∀ (P : H →ₗ[ZMod 2] U) (Q : H →ₗ[ZMod 2] R) (edge : U → Fin v × Fin v),
    let K := (LinearMap.ker Q).map P
    let Z := U ⧸ K
    letI : DecidableEq Z := Classical.typeDecidableEq Z
    let sourceLoss := fun (s : R) (label : Fin v → Bool) =>
      (Finset.univ.filter (fun x : H => Q x = s ∧
        label (edge (P x)).1 = label (edge (P x)).2)).card
    let localLoss := fun (c : Z) (color : Fin v → Bool) =>
      (Finset.univ.filter (fun u : U => K.mkQ u = c ∧
        color (edge u).1 = color (edge u).2)).card
    ∃ readout : R →ₗ[ZMod 2] Z,
      (∀ z : H, readout (Q z) = K.mkQ (P z)) ∧
      (∀ s ∈ Set.range Q, ∀ f : Fin v → Bool,
        sourceLoss s f =
          2 ^ Module.finrank (ZMod 2) (LinearMap.ker Q ⊓ LinearMap.ker P : Submodule (ZMod 2) H) * localLoss (readout s) f) ∧
      ∃ best : Z → Fin v → Bool, ∀ answer : R, ∀ alt : Fin v → Bool,
        sourceLoss answer (best (readout answer)) ≤ sourceLoss answer alt) := by
  intro d t q v H U R P Q edge K Z sourceLoss localLoss
  obtain ⟨readout, hread⟩ := PEqualNP.Outside.L_lib_396.exists_readout P Q
  have hcount : ∀ s ∈ Set.range Q, ∀ f : Fin v → Bool,
      sourceLoss s f =
        2 ^ Module.finrank (ZMod 2)
          (LinearMap.ker Q ⊓ LinearMap.ker P : Submodule (ZMod 2) H) *
          localLoss (readout s) f := by
    rintro s ⟨x0, rfl⟩ f
    rw [hread x0]
    exact @PEqualNP.Outside.L_lib_396.count d t q P Q
      (fun u => f (edge u).1 = f (edge u).2) _ (Classical.typeDecidableEq _) x0
  refine ⟨readout, hread, hcount, ?_⟩
  have hmin : ∀ c : Z, ∃ b : Fin v → Bool, ∀ alt, localLoss c b ≤ localLoss c alt := by
    intro c
    obtain ⟨b, -, hb⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin v → Bool))
      (localLoss c) Finset.univ_nonempty
    exact ⟨b, fun alt => hb alt (Finset.mem_univ _)⟩
  choose best hbest using hmin
  refine ⟨best, fun answer alt => ?_⟩
  by_cases hs : answer ∈ Set.range Q
  · rw [hcount answer hs, hcount answer hs]
    exact Nat.mul_le_mul_left _ (hbest _ _)
  · have h0 : sourceLoss answer (best (readout answer)) = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.filter_eq_empty_iff.mpr
      intro x _ hx
      exact hs ⟨x, hx.1⟩
    rw [h0]
    exact Nat.zero_le _
