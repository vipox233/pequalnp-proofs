import PEqualNP.Defs

open Finset
namespace PEqualNP.Outside.L_pcx_413_aux

abbrev F := ZMod 2
abbrev X {r : Nat} (m : Fin r → Nat) := (i : Fin r) → Fin (m i) → F

def Separates {r : Nat} {m : Fin r → Nat} (S : Submodule F (X m))
    (I : Finset (Fin r)) : Prop :=
  ∀ u ∈ S, (∀ j ∈ I, u j = 0) → u = 0

theorem existsMinimal {r : Nat} {m : Fin r → Nat} (S : Submodule F (X m)) :
    ∃ I : Finset (Fin r), Separates S I ∧ ∀ j ∈ I, ¬ Separates S (I.erase j) := by
  classical
  let P (n : Nat) := ∃ I : Finset (Fin r), I.card = n ∧ Separates S I
  have hP : ∃ n, P n := ⟨(univ : Finset (Fin r)).card, univ, rfl, by
    intro u _ hu
    funext j
    exact hu j (mem_univ j)⟩
  obtain ⟨I,hc,hsep⟩ := Nat.find_spec hP
  refine ⟨I,hsep,?_⟩
  intro j hj hs
  have hw : P (I.erase j).card := ⟨I.erase j,rfl,hs⟩
  have hl := Nat.find_min' hP hw
  have hlt := card_erase_lt_of_mem hj
  omega

theorem isolated {r : Nat} {m : Fin r → Nat} {S : Submodule F (X m)}
    {I : Finset (Fin r)} (hsep : Separates S I) {j : Fin r} (hj : j ∈ I)
    (hm : ¬ Separates S (I.erase j)) :
    ∃ u : X m, u ∈ S ∧ u j ≠ 0 ∧ ∀ k ∈ I, k ≠ j → u k = 0 := by
  classical
  unfold Separates at hm
  push Not at hm
  obtain ⟨u,hu,hI,hne⟩ := hm
  have hout (k : Fin r) (hk : k ∈ I) (hd : k ≠ j) : u k = 0 :=
    hI k (mem_erase.mpr ⟨hd,hk⟩)
  refine ⟨u,hu,?_ ,hout⟩
  intro h0
  apply hne
  apply hsep u hu
  intro k hk
  by_cases hkj : k = j
  · subst k; exact h0
  · exact hout k hk hkj

theorem dimension {r : Nat} {m : Fin r → Nat} {S : Submodule F (X m)}
    {I : Finset (Fin r)} (hsep : Separates S I) :
    Module.finrank F S ≤ ∑ j ∈ I, m j := by
  classical
  let T : S →ₗ[F] ((j : I) → Fin (m j.val) → F) :=
    { toFun := fun u j => u.val j.val
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hk : Function.Injective T := by
    intro u v he
    apply Subtype.ext
    apply sub_eq_zero.mp
    have hz : ∀ j ∈ I, (u.val - v.val) j = 0 := by
      intro j hj
      have he' := congrFun he ⟨j,hj⟩
      change u.val j = v.val j at he'
      exact sub_eq_zero.mpr he'
    exact hsep _ (S.sub_mem u.2 v.2) hz
  have h := LinearMap.finrank_le_finrank_of_injective hk
  rw [Module.finrank_pi_fintype] at h
  have hv (j : I) : Module.finrank F (Fin (m j.val) → F) = m j.val := by
    rw [Module.finrank_pi,Fintype.card_fin]
  simpa [hv,Finset.sum_attach] using h

theorem twoValues : ∀ u v b : F, u ≠ v → b = u ∨ b = v := by decide +kernel

theorem main (r : Nat) (m : Fin r → Nat)
    (f : (j : Fin r) → (Fin (m j) → F) → F)
    (hn : ∀ (j : Fin r) (v : Fin (m j) → F), v ≠ 0 → ∃ p, f j (p+v) ≠ f j p)
    (S : Submodule F (X m)) :
    ∃ (I : Finset (Fin r)) (a : X m),
      Module.finrank F S ≤ ∑ i ∈ I, m i ∧ Separates S I ∧
        ∀ b : Fin r → F, ∃ w ∈ S, ∀ j ∈ I, f j (a j+w j) = b j := by
  classical
  obtain ⟨I,hsep,hmin⟩ := existsMinimal S
  have hU (j : I) := isolated hsep j.2 (hmin j.val j.2)
  choose u hSu hnz hof using hU
  have hA (j : I) : ∃ p, f j.val (p + u j j.val) ≠ f j.val p :=
    hn j.val (u j j.val) (hnz j)
  choose p hp using hA
  let a (j : Fin r) : Fin (m j) → F := if hj : j ∈ I then p ⟨j,hj⟩ else 0
  have ha (j : I) : a j.val = p j := by simpa [a,dite_eq_left j.2]
  refine ⟨I,a,dimension hsep,hsep,?_⟩
  intro b
  let v (j : I) : X m := if b j.val = f j.val (a j.val) then 0 else u j
  let w : X m := ∑ j : I, v j
  refine ⟨w, S.sum_mem (fun j _ => by
    by_cases he : b j.val = f j.val (a j.val)
    · simpa [v,he] using S.zero_mem
    · simpa [v,he] using hSu j), ?_⟩
  intro j hj
  let k : I := ⟨j,hj⟩
  have hw : w j = v k j := by
    unfold w
    rw [Finset.sum_apply]
    refine Finset.sum_eq_single k (fun i _ hi => ?_) (fun h => False.elim (h (mem_univ k)))
    have hne : j ≠ i.val := fun he => hi (Subtype.ext he.symm)
    by_cases he : b i.val = f i.val (a i.val)
    · simp [v,he]
    · simpa [v,he] using hof i j hj hne
  rw [hw]
  change f j (a j + (if b j = f j (a j) then 0 else u k) j) = b j
  by_cases he : b j = f j (a j)
  · simpa [if_pos he] using he.symm
  · rw [if_neg he]
    have hpi : f j (a j + u k j) ≠ f j (a j) := by
      simpa [show a j = p k from ha k] using hp k
    exact ((twoValues _ _ _ hpi.symm).resolve_left he).symm

end PEqualNP.Outside.L_pcx_413_aux

theorem PEqualNP.Outside.L_pcx_413 : ∀ (r : ℕ) (m : Fin r → ℕ),
  let F := ZMod 2
  let X := (i : Fin r) → Fin (m i) → F
  ∀ (f : (i : Fin r) → (Fin (m i) → F) → F),
    (∀ (j : Fin r) (v : Fin (m j) → F), v ≠ 0 → ∃ p, f j (p+v) ≠ f j p) →
    ∀ S : Submodule F X, ∃ (I : Finset (Fin r)) (a : X),
      Module.finrank F S ≤ ∑ i ∈ I, m i ∧
      (∀ u ∈ S, (∀ j ∈ I, u j = 0) → u = 0) ∧
      ∀ b : Fin r → F, ∃ w ∈ S, ∀ j ∈ I, f j (a j+w j) = b j :=
  PEqualNP.Outside.L_pcx_413_aux.main
