import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_389

theorem reach {Z : Type} (N J : Finset (List Bool)) (c : List Bool → Z → Bool)
    (hch : ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N) (z : Z) :
    ∀ (fuel : ℕ) (p : List Bool), p ∈ N → N.sup List.length ≤ p.length + fuel →
      (∀ j (hj : j < p.length), c (p.take j) z = p[j]) →
      ∃ q ∈ N \ J, ∀ j (hj : j < q.length), c (q.take j) z = q[j] := by
  intro fuel
  induction fuel with
  | zero =>
    intro p hp hlen hc
    by_cases hpJ : p ∈ J
    · exfalso
      have h1 := (hch p hpJ).1
      have h2 : (p ++ [false]).length ≤ N.sup List.length := Finset.le_sup (f := List.length) h1
      rw [List.length_append, List.length_singleton] at h2
      omega
    · exact ⟨p, Finset.mem_sdiff.2 ⟨hp, hpJ⟩, hc⟩
  | succ f ih =>
    intro p hp hlen hc
    by_cases hpJ : p ∈ J
    · have hchild : p ++ [c p z] ∈ N := by
        cases hb : c p z
        · exact (hch p hpJ).1
        · exact (hch p hpJ).2
      refine ih (p ++ [c p z]) hchild (by rw [List.length_append, List.length_singleton]; omega) ?_
      intro j hj
      simp at hj
      by_cases hjl : j < p.length
      · rw [List.take_append_of_le_length (by omega), List.getElem_append_left hjl]
        exact hc j hjl
      · have hjeq : j = p.length := by omega
        subst hjeq
        simp
    · exact ⟨p, Finset.mem_sdiff.2 ⟨hp, hpJ⟩, hc⟩

theorem zkey : ∀ a a0 b : ZMod 2, ∀ t : Bool,
    decide (a = b) = t → decide (a0 = b) = t → a - a0 = 0 := by decide

theorem zbit : ∀ (v : ZMod 2) (t : Bool), decide (v = 1) = t → v = if t then 1 else 0 := by
  decide

theorem mem_lists (l : ℕ) (p : List Bool) :
    p ∈ (Finset.univ : Finset (Fin l → Bool)).image List.ofFn ↔ p.length = l := by
  constructor
  · intro h
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.1 h
    simp
  · intro h
    subst h
    exact Finset.mem_image.2 ⟨fun i => p.get i, Finset.mem_univ _, List.ofFn_get p⟩

theorem getD_take (p : List Bool) (r j : ℕ) (h : j < r) :
    (p.take r).getD j false = p.getD j false := by
  simp [List.getD_eq_getElem?_getD, h]

theorem tree_flat (n m : ℕ) (T : (Fin n → ZMod 2) × (Fin m → ZMod 2) → (Fin m → ZMod 2)) (allowed : Set (Set (Fin m → ZMod 2))) (K : ℕ)
    (N J : Finset (List Bool))
    (query : List Bool → ((Fin n → ZMod 2) × (Fin m → ZMod 2)) →ₗ[ZMod 2] ZMod 2)
    (bias : List Bool → ZMod 2) (out : List Bool → Set (Fin m → ZMod 2))
    (h0 : [] ∈ N)
    (hch : ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N)
    (hcard : (N \ J).card ≤ K)
    (hleaf : ∀ p ∈ N \ J, out p ∈ allowed ∧
      ∀ z : (Fin n → ZMod 2) × (Fin m → ZMod 2), (∀ j : Fin p.length,
        decide (query (p.take j.val) z = bias (p.take j.val)) = p.get j) → T z ∈ out p) :
    ∃ (S : Submodule (ZMod 2) ((Fin n → ZMod 2) × (Fin m → ZMod 2))) (base : (Fin n → ZMod 2) × (Fin m → ZMod 2)) (L : Set (Fin m → ZMod 2)), L ∈ allowed ∧
      2 ^ (n + m) ≤ K * 2 ^ (Module.finrank (ZMod 2) S) ∧
      ∀ z : (Fin n → ZMod 2) × (Fin m → ZMod 2), z - base ∈ S → T z ∈ L := by
  classical
  have hcover : ∀ z : (Fin n → ZMod 2) × (Fin m → ZMod 2), ∃ q ∈ N \ J,
      ∀ j (hj : j < q.length), decide (query (q.take j) z = bias (q.take j)) = q[j] := by
    intro z
    exact reach N J (fun p z => decide (query p z = bias p)) hch z (N.sup List.length) [] h0
      (by simp) (by intro j hj; simp at hj)
  let region : List Bool → Finset ((Fin n → ZMod 2) × (Fin m → ZMod 2)) := fun p =>
    Finset.univ.filter (fun z => ∀ j (hj : j < p.length),
      decide (query (p.take j) z = bias (p.take j)) = p[j])
  have hsum : 2 ^ (n + m) ≤ ∑ p ∈ N \ J, (region p).card := by
    have h1 : (Finset.univ : Finset ((Fin n → ZMod 2) × (Fin m → ZMod 2))) ⊆ (N \ J).biUnion region := by
      intro z _
      obtain ⟨q, hq, hc⟩ := hcover z
      exact Finset.mem_biUnion.2 ⟨q, hq, Finset.mem_filter.2 ⟨Finset.mem_univ _, hc⟩⟩
    have h2 := Finset.card_le_card h1
    have h3 : (Finset.univ : Finset ((Fin n → ZMod 2) × (Fin m → ZMod 2))).card = 2 ^ (n + m) := by
      simp [pow_add]
    calc 2 ^ (n + m) = _ := h3.symm
      _ ≤ _ := h2
      _ ≤ _ := Finset.card_biUnion_le
  have hne : (N \ J).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h] at hsum
    simp at hsum
  obtain ⟨p, hp, hpbig⟩ : ∃ p ∈ N \ J, 2 ^ (n + m) ≤ K * (region p).card := by
    apply Finset.exists_le_of_sum_le hne
    calc ∑ _p ∈ N \ J, 2 ^ (n + m) = (N \ J).card * 2 ^ (n + m) := by simp
      _ ≤ K * ∑ p ∈ N \ J, (region p).card := Nat.mul_le_mul hcard hsum
      _ = ∑ p ∈ N \ J, K * (region p).card := Finset.mul_sum _ _ _
  obtain ⟨hallow, hT⟩ := hleaf p hp
  have hpos : 0 < (region p).card := by
    rcases Nat.eq_zero_or_pos (region p).card with h | h
    · rw [h] at hpbig
      simp at hpbig
    · exact h
  obtain ⟨z0, hz0⟩ := Finset.card_pos.1 hpos
  have hz0c := (Finset.mem_filter.1 hz0).2
  let U : Submodule (ZMod 2) ((Fin n → ZMod 2) × (Fin m → ZMod 2)) :=
    ⨅ j : Fin p.length, LinearMap.ker (query (p.take j))
  have hUmem : ∀ u : (Fin n → ZMod 2) × (Fin m → ZMod 2),
      u ∈ U ↔ ∀ j (_ : j < p.length), query (p.take j) u = 0 := by
    intro u
    simp only [U, Submodule.mem_iInf, LinearMap.mem_ker]
    constructor
    · intro h j hj
      exact h ⟨j, hj⟩
    · intro h j
      exact h j j.2
  have hTU : ∀ u ∈ U, T (z0 + u) ∈ out p := by
    intro u hu
    apply hT (z0 + u)
    intro j
    rw [map_add, (hUmem u).1 hu j j.2, add_zero]
    exact hz0c j j.2
  have : Fintype U := Fintype.ofFinite U
  have hzU : ∀ z ∈ region p, z - z0 ∈ U := by
    intro z hz
    have hzc := (Finset.mem_filter.1 hz).2
    rw [hUmem]
    intro j hj
    rw [map_sub]
    exact zkey _ _ _ _ (hzc j hj) (hz0c j hj)
  have hregU : (region p).card ≤ Fintype.card U := by
    rw [← Fintype.card_coe]
    apply Fintype.card_le_of_injective (fun z : region p => (⟨z.1 - z0, hzU z.1 z.2⟩ : U))
    intro z z' h
    have h' := congrArg Subtype.val h
    exact Subtype.ext (sub_left_injective h')
  have h1 : Fintype.card U = 2 ^ Module.finrank (ZMod 2) U := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := U), ZMod.card]
  refine ⟨U, z0, out p, hallow, ?_, ?_⟩
  · rw [← h1]
    exact le_trans hpbig (Nat.mul_le_mul_left _ hregU)
  · intro z hz
    have h2 := hTU (z - z0) hz
    rw [add_sub_cancel] at h2
    exact h2

theorem flat_batches (n m : ℕ) (Q : (Fin n → ZMod 2) → (Fin m → ZMod 2))
    (hQ : ∀ a : (Fin n → ZMod 2), ∃ B : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2),
      ∀ h : (Fin n → ZMod 2), Q (a + h) = Q a + Q h - Q 0 + B h)
    (allowed : Set (Set (Fin m → ZMod 2)))
    (htrans : ∀ L ∈ allowed, ∀ v : (Fin m → ZMod 2), {z : (Fin m → ZMod 2) | z - v ∈ L} ∈ allowed) (K : ℕ)
    (S : Submodule (ZMod 2) ((Fin n → ZMod 2) × (Fin m → ZMod 2))) (base : (Fin n → ZMod 2) × (Fin m → ZMod 2)) (L : Set (Fin m → ZMod 2)) (hL : L ∈ allowed)
    (hK : 2 ^ (n + m) ≤ K * 2 ^ (Module.finrank (ZMod 2) S))
    (hS : ∀ z : (Fin n → ZMod 2) × (Fin m → ZMod 2), z - base ∈ S → z.2 + Q z.1 ∈ L) :
    ∃ (a b : ℕ) (first : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin a → ZMod 2))
      (second : (Fin a → ZMod 2) → ((Fin n → ZMod 2) × (Fin m → ZMod 2)) →ₗ[ZMod 2] (Fin b → ZMod 2))
      (readout : (Fin a → ZMod 2) → (Fin b → ZMod 2) → Set (Fin m → ZMod 2)),
      2 ^ (a + b) ≤ K ∧ ∀ z : (Fin n → ZMod 2) × (Fin m → ZMod 2),
        readout (first z.1) (second (first z.1) z) ∈ allowed ∧
        z.2 + Q z.1 ∈ readout (first z.1) (second (first z.1) z) := by
  classical
  choose B hB using hQ
  let f : S →ₗ[ZMod 2] (Fin n → ZMod 2) := (LinearMap.fst (ZMod 2) (Fin n → ZMod 2) (Fin m → ZMod 2)) ∘ₗ S.subtype
  let Bv : Submodule (ZMod 2) (Fin m → ZMod 2) := S.comap (LinearMap.inr (ZMod 2) (Fin n → ZMod 2) (Fin m → ZMod 2))
  have hBv : ∀ β : (Fin m → ZMod 2), β ∈ Bv ↔ ((0 : (Fin n → ZMod 2)), β) ∈ S := fun β => Iff.rfl
  have hker : Module.finrank (ZMod 2) (LinearMap.ker f) ≤ Module.finrank (ZMod 2) Bv := by
    let g0 : LinearMap.ker f →ₗ[ZMod 2] Bv := LinearMap.codRestrict Bv
      ((LinearMap.snd (ZMod 2) (Fin n → ZMod 2) (Fin m → ZMod 2)) ∘ₗ S.subtype ∘ₗ (LinearMap.ker f).subtype) (by
        intro u
        have hu1 : ((u : S) : (Fin n → ZMod 2) × (Fin m → ZMod 2)).1 = 0 := LinearMap.mem_ker.1 u.2
        have hu2 : ((0 : (Fin n → ZMod 2)), ((u : S) : (Fin n → ZMod 2) × (Fin m → ZMod 2)).2) = ((u : S) : (Fin n → ZMod 2) × (Fin m → ZMod 2)) :=
          Prod.ext hu1.symm rfl
        show ((0 : (Fin n → ZMod 2)), ((u : S) : (Fin n → ZMod 2) × (Fin m → ZMod 2)).2) ∈ S
        rw [hu2]
        exact (u : S).2)
    apply LinearMap.finrank_le_finrank_of_injective (f := g0)
    rw [injective_iff_map_eq_zero]
    intro u hu
    have hu2 : ((u : S) : (Fin n → ZMod 2) × (Fin m → ZMod 2)).2 = 0 := congrArg Subtype.val hu
    have hu1 : ((u : S) : (Fin n → ZMod 2) × (Fin m → ZMod 2)).1 = 0 := LinearMap.mem_ker.1 u.2
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext hu1 hu2
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  obtain ⟨H', hH'⟩ := Submodule.exists_isCompl (LinearMap.range f)
  obtain ⟨B', hB'⟩ := Submodule.exists_isCompl Bv
  have hHH := Submodule.finrank_add_eq_of_isCompl hH'
  have hBB := Submodule.finrank_add_eq_of_isCompl hB'
  rw [Module.finrank_fin_fun] at hHH hBB
  obtain ⟨a, ha⟩ : ∃ a : ℕ, Module.finrank (ZMod 2) H' = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ, Module.finrank (ZMod 2) B' = b := ⟨_, rfl⟩
  have hab : a + b + Module.finrank (ZMod 2) S ≤ n + m := by omega
  have hKab : 2 ^ (a + b) ≤ K := by
    have h1 : 2 ^ (a + b) * 2 ^ Module.finrank (ZMod 2) S
        ≤ K * 2 ^ Module.finrank (ZMod 2) S := by
      rw [← pow_add]
      exact le_trans (Nat.pow_le_pow_right (by norm_num) hab) hK
    exact Nat.le_of_mul_le_mul_right h1 (by positivity)
  let eH := (Module.finBasisOfFinrankEq (ZMod 2) H' ha).equivFun
  let φ : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin a → ZMod 2) :=
    eH.toLinearMap ∘ₗ H'.projectionOnto (LinearMap.range f) hH'.symm
  let σ : (Fin a → ZMod 2) → (Fin n → ZMod 2) := fun s => ((eH.symm s : H') : (Fin n → ZMod 2))
  let ρ : (Fin n → ZMod 2) →ₗ[ZMod 2] LinearMap.range f := (LinearMap.range f).projectionOnto H' hH'
  have hdecomp : ∀ x : (Fin n → ZMod 2), x = σ (φ x) + (ρ x : (Fin n → ZMod 2)) := by
    intro x
    have h1 := Submodule.projection_add_projection_eq_self hH' x
    have h2 : σ (φ x) = H'.projection (LinearMap.range f) hH'.symm x := by
      simp [σ, φ]
    have h3 : (ρ x : (Fin n → ZMod 2)) = (LinearMap.range f).projection H' hH' x := rfl
    rw [h2, h3, add_comm]
    exact h1.symm
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective f.rangeRestrict
    (LinearMap.range_rangeRestrict f)
  have hg1 : ∀ c : LinearMap.range f, ((g c : S) : (Fin n → ZMod 2) × (Fin m → ZMod 2)).1 = (c : (Fin n → ZMod 2)) := by
    intro c
    have h1 := LinearMap.congr_fun hg c
    exact congrArg Subtype.val h1
  let eB := (Module.finBasisOfFinrankEq (ZMod 2) B' hb).equivFun
  let θ : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin b → ZMod 2) :=
    eB.toLinearMap ∘ₗ B'.projectionOnto Bv hB'.symm
  let τ : (Fin b → ZMod 2) → (Fin m → ZMod 2) := fun e => ((eB.symm e : B') : (Fin m → ZMod 2))
  have hτ : ∀ e, θ (τ e) = e := by
    intro e
    simp [θ, τ]
  have hθker : ∀ w : (Fin m → ZMod 2), θ w = 0 → w ∈ Bv := by
    intro w hw
    have h1 : B'.projectionOnto Bv hB'.symm w = 0 := by
      have h2 : eB (B'.projectionOnto Bv hB'.symm w) = 0 := hw
      exact (LinearEquiv.map_eq_zero_iff eB).1 h2
    exact (Submodule.projectionOnto_apply_eq_zero_iff hB'.symm).1 h1
  let M : (Fin a → ZMod 2) → ((Fin n → ZMod 2) × (Fin m → ZMod 2)) →ₗ[ZMod 2] (Fin m → ZMod 2) := fun s =>
    LinearMap.snd (ZMod 2) (Fin n → ZMod 2) (Fin m → ZMod 2)
      - ((LinearMap.snd (ZMod 2) (Fin n → ZMod 2) (Fin m → ZMod 2)) ∘ₗ S.subtype ∘ₗ g) ∘ₗ ρ ∘ₗ LinearMap.fst (ZMod 2) (Fin n → ZMod 2) (Fin m → ZMod 2)
      + ((B (σ s) - B base.1) ∘ₗ (LinearMap.range f).subtype) ∘ₗ ρ ∘ₗ
          LinearMap.fst (ZMod 2) (Fin n → ZMod 2) (Fin m → ZMod 2)
  refine ⟨a, b, φ, fun s => θ ∘ₗ M s,
    fun s e => {w | w - (τ e + Q (σ s) - Q base.1 - base.2) ∈ L}, hKab, ?_⟩
  intro z
  refine ⟨htrans L hL _, ?_⟩
  show z.2 + Q z.1 - (τ (θ (M (φ z.1) z)) + Q (σ (φ z.1)) - Q base.1 - base.2) ∈ L
  obtain ⟨c, hc⟩ : ∃ c : LinearMap.range f, c = ρ z.1 := ⟨_, rfl⟩
  obtain ⟨β, hβdef⟩ : ∃ β : (Fin m → ZMod 2), β = M (φ z.1) z - τ (θ (M (φ z.1) z)) := ⟨_, rfl⟩
  have hβ : β ∈ Bv := by
    apply hθker
    rw [hβdef, map_sub, hτ, sub_self]
  have hmem : base + ((g c : S) : (Fin n → ZMod 2) × (Fin m → ZMod 2)) + ((0 : (Fin n → ZMod 2)), β) - base ∈ S := by
    have h1 : base + ((g c : S) : (Fin n → ZMod 2) × (Fin m → ZMod 2)) + ((0 : (Fin n → ZMod 2)), β) - base
        = ((g c : S) : (Fin n → ZMod 2) × (Fin m → ZMod 2)) + ((0 : (Fin n → ZMod 2)), β) := by abel
    rw [h1]
    exact S.add_mem (g c).2 ((hBv β).1 hβ)
  have hz' := hS _ hmem
  have e1 : Q z.1 = Q (σ (φ z.1)) + Q (c : (Fin n → ZMod 2)) - Q 0 + B (σ (φ z.1)) (c : (Fin n → ZMod 2)) := by
    have h1 := hB (σ (φ z.1)) (c : (Fin n → ZMod 2))
    rw [hc, ← hdecomp z.1] at h1
    rw [hc]
    exact h1
  have e2 := hB base.1 (c : (Fin n → ZMod 2))
  have e3 : M (φ z.1) z = z.2 - ((g c : S) : (Fin n → ZMod 2) × (Fin m → ZMod 2)).2
      + (B (σ (φ z.1)) (c : (Fin n → ZMod 2)) - B base.1 (c : (Fin n → ZMod 2))) := by
    rw [hc]
    rfl
  have e4 : (base + ((g c : S) : (Fin n → ZMod 2) × (Fin m → ZMod 2)) + ((0 : (Fin n → ZMod 2)), β)).1 = base.1 + (c : (Fin n → ZMod 2)) := by
    simp [hg1]
  have e5 : (base + ((g c : S) : (Fin n → ZMod 2) × (Fin m → ZMod 2)) + ((0 : (Fin n → ZMod 2)), β)).2
      = base.2 + ((g c : S) : (Fin n → ZMod 2) × (Fin m → ZMod 2)).2 + β := by
    simp
  rw [e4, e5, e2] at hz'
  have e6 : z.2 + Q z.1 - (τ (θ (M (φ z.1) z)) + Q (σ (φ z.1)) - Q base.1 - base.2)
      = base.2 + ((g c : S) : (Fin n → ZMod 2) × (Fin m → ZMod 2)).2 + β
        + (Q base.1 + Q (c : (Fin n → ZMod 2)) - Q 0 + B base.1 (c : (Fin n → ZMod 2))) := by
    rw [hβdef, e1, e3]
    abel
  rw [e6]
  exact hz'

theorem batches_tree (n m : ℕ) (T : (Fin n → ZMod 2) × (Fin m → ZMod 2) → (Fin m → ZMod 2)) (allowed : Set (Set (Fin m → ZMod 2))) (K : ℕ)
    (a b : ℕ) (φ : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin a → ZMod 2))
    (Λ : (Fin a → ZMod 2) → ((Fin n → ZMod 2) × (Fin m → ZMod 2)) →ₗ[ZMod 2] (Fin b → ZMod 2))
    (readout : (Fin a → ZMod 2) → (Fin b → ZMod 2) → Set (Fin m → ZMod 2))
    (hK : 2 ^ (a + b) ≤ K)
    (hall : ∀ z : (Fin n → ZMod 2) × (Fin m → ZMod 2), readout (φ z.1) (Λ (φ z.1) z) ∈ allowed ∧
      T z ∈ readout (φ z.1) (Λ (φ z.1) z)) :
    ∃ (N J : Finset (List Bool))
      (query : List Bool → ((Fin n → ZMod 2) × (Fin m → ZMod 2)) →ₗ[ZMod 2] ZMod 2)
      (bias : List Bool → ZMod 2) (out : List Bool → Set (Fin m → ZMod 2)),
      [] ∈ N ∧ J ⊆ N ∧
      (∀ (p : List Bool) (t : Bool), p ++ [t] ∈ N → p ∈ J) ∧
      (∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N) ∧
      (N \ J).card ≤ K ∧ ∀ p ∈ N \ J, out p ∈ allowed ∧
        ∀ z : (Fin n → ZMod 2) × (Fin m → ZMod 2), (∀ j : Fin p.length,
          decide (query (p.take j.val) z = bias (p.take j.val)) = p.get j) →
          T z ∈ out p := by
  classical
  let bits : List Bool → ℕ → ZMod 2 := fun p i => if p.getD i false then 1 else 0
  let sOf : List Bool → (Fin a → ZMod 2) := fun p i => bits p i
  let eOf : List Bool → (Fin b → ZMod 2) := fun p i => bits p (a + i)
  let query : List Bool → ((Fin n → ZMod 2) × (Fin m → ZMod 2)) →ₗ[ZMod 2] ZMod 2 := fun p =>
    if h : p.length < a then
      (LinearMap.proj (⟨p.length, h⟩ : Fin a)) ∘ₗ φ ∘ₗ
        LinearMap.fst (ZMod 2) (Fin n → ZMod 2) (Fin m → ZMod 2)
    else if h2 : p.length - a < b then
      (LinearMap.proj (⟨p.length - a, h2⟩ : Fin b)) ∘ₗ Λ (sOf p)
    else 0
  have hq1 : ∀ (q : List Bool) (j : Fin a) (z : (Fin n → ZMod 2) × (Fin m → ZMod 2)),
      q.length = j.val → query q z = φ z.1 j := by
    intro q j z hq
    have h : q.length < a := hq ▸ j.2
    simp only [query, h, ↓reduceDIte]
    show φ z.1 ⟨q.length, h⟩ = φ z.1 j
    exact congrArg (φ z.1) (Fin.ext hq)
  have hq2 : ∀ (q : List Bool) (j : Fin b) (z : (Fin n → ZMod 2) × (Fin m → ZMod 2)),
      q.length = a + j.val → query q z = Λ (sOf q) z j := by
    intro q j z hq
    have h : ¬ q.length < a := by omega
    have h2 : q.length - a < b := by have := j.2; omega
    simp only [query, h, h2, ↓reduceDIte]
    show Λ (sOf q) z ⟨q.length - a, h2⟩ = Λ (sOf q) z j
    have h3 : (⟨q.length - a, h2⟩ : Fin b) = j := Fin.ext (by show q.length - a = j.val; omega)
    exact congrArg (Λ (sOf q) z) h3
  let lists : ℕ → Finset (List Bool) := fun l =>
    (Finset.univ : Finset (Fin l → Bool)).image List.ofFn
  let N : Finset (List Bool) := (Finset.range (a + b + 1)).biUnion lists
  let J : Finset (List Bool) := (Finset.range (a + b)).biUnion lists
  have hN : ∀ p : List Bool, p ∈ N ↔ p.length ≤ a + b := by
    intro p
    simp only [N, lists, Finset.mem_biUnion, Finset.mem_range, mem_lists]
    constructor
    · rintro ⟨l, hl, rfl⟩
      omega
    · intro h
      exact ⟨p.length, by omega, rfl⟩
  have hJ : ∀ p : List Bool, p ∈ J ↔ p.length < a + b := by
    intro p
    simp only [J, lists, Finset.mem_biUnion, Finset.mem_range, mem_lists]
    constructor
    · rintro ⟨l, hl, rfl⟩
      omega
    · intro h
      exact ⟨p.length, by omega, rfl⟩
  refine ⟨N, J, query, fun _ => 1,
    fun p => if ∃ z : (Fin n → ZMod 2) × (Fin m → ZMod 2), φ z.1 = sOf p ∧ Λ (sOf p) z = eOf p then
      readout (sOf p) (eOf p) else readout (φ 0) (Λ (φ 0) 0), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hN]
    simp
  · intro p hp
    rw [hJ] at hp
    rw [hN]
    omega
  · intro p t hp
    rw [hN, List.length_append, List.length_singleton] at hp
    rw [hJ]
    omega
  · intro p hp
    rw [hJ] at hp
    rw [hN, hN, List.length_append, List.length_append, List.length_singleton,
      List.length_singleton]
    omega
  · have hsub : N \ J ⊆ lists (a + b) := by
      intro p hp
      rw [Finset.mem_sdiff, hN, hJ] at hp
      exact (mem_lists (a + b) p).2 (by omega)
    calc (N \ J).card ≤ (lists (a + b)).card := Finset.card_le_card hsub
      _ ≤ (Finset.univ : Finset (Fin (a + b) → Bool)).card := Finset.card_image_le
      _ = 2 ^ (a + b) := by simp
      _ ≤ K := hK
  · intro p hp
    rw [Finset.mem_sdiff, hN, hJ] at hp
    have hlen : p.length = a + b := by omega
    constructor
    · by_cases hex : ∃ z : (Fin n → ZMod 2) × (Fin m → ZMod 2), φ z.1 = sOf p ∧ Λ (sOf p) z = eOf p
      · simp only [hex, ↓reduceIte]
        obtain ⟨z0, h1, h2⟩ := hex
        have h3 := (hall z0).1
        rw [h1, h2] at h3
        exact h3
      · simp only [hex, ↓reduceIte]
        have h3 := (hall 0).1
        exact h3
    intro z H
    have c1 : φ z.1 = sOf p := by
      funext i
      have hi : i.val < p.length := by have := i.2; omega
      have h1 := H ⟨i.val, hi⟩
      have h2 : (p.take i.val).length = i.val := by
        rw [List.length_take]
        omega
      have h1' : decide (query (p.take i.val) z = 1) = p[i.val] := h1
      rw [hq1 (p.take i.val) i z h2] at h1'
      have h3 := zbit _ _ h1'
      rw [h3]
      show (if p[i.val] then (1 : ZMod 2) else 0) = if p.getD i.val false then 1 else 0
      rw [List.getD_eq_getElem p false hi]
    have c2 : Λ (sOf p) z = eOf p := by
      funext i
      have hi : a + i.val < p.length := by have := i.2; omega
      have h1 := H ⟨a + i.val, hi⟩
      have h2 : (p.take (a + i.val)).length = a + i.val := by
        rw [List.length_take]
        omega
      have h1' : decide (query (p.take (a + i.val)) z = 1) = p[a + i.val] := h1
      rw [hq2 (p.take (a + i.val)) i z h2] at h1'
      have hs : sOf (p.take (a + i.val)) = sOf p := by
        funext j
        show (if (p.take (a + i.val)).getD j.val false then (1 : ZMod 2) else 0)
          = if p.getD j.val false then 1 else 0
        rw [getD_take p (a + i.val) j.val (by have := j.2; omega)]
      rw [hs] at h1'
      have h3 := zbit _ _ h1'
      rw [h3]
      show (if p[a + i.val] then (1 : ZMod 2) else 0) = if p.getD (a + i.val) false then 1 else 0
      rw [List.getD_eq_getElem p false hi]
    have hex : ∃ z : (Fin n → ZMod 2) × (Fin m → ZMod 2), φ z.1 = sOf p ∧ Λ (sOf p) z = eOf p := ⟨z, c1, c2⟩
    simp only [hex, ↓reduceIte]
    have h3 := (hall z).2
    rw [c1, c2] at h3
    exact h3

end PEqualNP.Outside.L_pcx_389

theorem PEqualNP.Outside.L_pcx_389 : (∀ (n m : ℕ),
  let F := ZMod 2
  let X := Fin n → F
  let Y := Fin m → F
  let tree := fun (target : (X × Y) → Y) (allowed : Set (Set Y)) (K : ℕ) =>
    ∃ (N J : Finset (List Bool)) (query : List Bool → (X × Y) →ₗ[F] F)
      (bias : List Bool → F) (out : List Bool → Set Y),
      [] ∈ N ∧ J ⊆ N ∧
      (∀ (p : List Bool) (t : Bool), p ++ [t] ∈ N → p ∈ J) ∧
      (∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N) ∧
      (N \ J).card ≤ K ∧ ∀ p ∈ N \ J, out p ∈ allowed ∧
        ∀ z : X × Y, (∀ j : Fin p.length,
          decide (query (p.take j.val) z = bias (p.take j.val)) = p.get j) → target z ∈ out p
  ∀ (Q : X → Y)
    (_ : ∀ a : X, ∃ B : X →ₗ[F] Y, ∀ h : X, Q (a+h) = Q a + Q h - Q 0 + B h)
    (allowed : Set (Set Y))
    (_ : ∀ L ∈ allowed, ∀ v : Y, {z : Y | z-v ∈ L} ∈ allowed) (K : ℕ),
    let target := fun z : X × Y => z.2 + Q z.1
    let flat := ∃ (S : Submodule F (X × Y)) (base : X × Y) (L : Set Y), L ∈ allowed ∧
      2^(n+m) ≤ K * 2^(Module.finrank F S) ∧
      ∀ z : X × Y, z-base ∈ S → target z ∈ L
    let batches := ∃ (a b : ℕ) (first : X →ₗ[F] (Fin a → F))
      (second : (Fin a → F) → (X × Y) →ₗ[F] (Fin b → F))
      (readout : (Fin a → F) → (Fin b → F) → Set Y),
      2^(a+b) ≤ K ∧ ∀ z : X × Y,
        let L := readout (first z.1) (second (first z.1) z)
        L ∈ allowed ∧ target z ∈ L
    (tree target allowed K ↔ flat) ∧ (flat ↔ batches)) := by
  intro n m F X Y tree Q hQ allowed htrans K target flat batches
  have hTF : tree target allowed K → flat := by
    rintro ⟨N, J, query, bias, out, h0, _, _, hch, hcard, hleaf⟩
    exact PEqualNP.Outside.L_pcx_389.tree_flat n m target allowed K N J query bias out
      h0 hch hcard hleaf
  have hFB : flat → batches := by
    rintro ⟨S, base, L, hL, hK, hS⟩
    exact PEqualNP.Outside.L_pcx_389.flat_batches n m Q hQ allowed htrans K S base L hL hK hS
  have hBT : batches → tree target allowed K := by
    rintro ⟨a, b, first, second, readout, hK, hall⟩
    exact PEqualNP.Outside.L_pcx_389.batches_tree n m target allowed K a b first second
      readout hK (fun z => hall z)
  exact ⟨⟨hTF, fun h => hBT (hFB h)⟩, ⟨hFB, fun h => hTF (hBT h)⟩⟩
