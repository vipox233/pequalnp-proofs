import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_396

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

theorem quad {n m : ℕ} (Q : (Fin n → ZMod 2) → (Fin m → ZMod 2))
    (B : (Fin n → ZMod 2) → (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2))
    (hB : ∀ a h, Q (a + h) = Q a + Q h - Q 0 + B a h) (x0 x x' : Fin n → ZMod 2) :
    Q (x0 + (x + x')) - Q (x0 + x) - Q (x0 + x') + Q x0 = Q (x + x') - Q x - Q x' + Q 0 := by
  have hsym : ∀ a h, B a h = B h a := by
    intro a h
    have h1 := hB a h
    have h2 := hB h a
    rw [add_comm h a] at h2
    have h3 := h1.symm.trans h2
    rw [add_comm (Q h) (Q a)] at h3
    exact add_left_cancel h3
  have e1 := hB (x0 + x) x'
  have e2 := hB x0 x'
  have e3 := hB x x'
  have e4 : B (x0 + x) x' = B x0 x' + B x x' := by
    rw [hsym (x0 + x) x', map_add, hsym x' x0, hsym x' x]
  rw [← add_assoc, e1, e2, e3, e4]
  abel

theorem fwd (n m : ℕ) (Q : (Fin n → ZMod 2) → (Fin m → ZMod 2))
    (hQ : ∀ a : Fin n → ZMod 2, ∃ B : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2),
      ∀ h : Fin n → ZMod 2, Q (a + h) = Q a + Q h - Q 0 + B h)
    (k d : ℕ)
    (N J : Finset (List Bool))
    (query : List Bool → ((Fin n → ZMod 2) × (Fin m → ZMod 2)) →ₗ[ZMod 2] ZMod 2)
    (bias : List Bool → ZMod 2) (out : List Bool → Set (Fin m → ZMod 2))
    (h0 : [] ∈ N)
    (hch : ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N)
    (hcard : (N \ J).card ≤ 2 ^ d)
    (hleaf : ∀ p ∈ N \ J,
      (∃ (R : Submodule (ZMod 2) (Fin m → ZMod 2)) (c : Fin m → ZMod 2),
        Module.finrank (ZMod 2) R ≤ k ∧ out p = {w : Fin m → ZMod 2 | w - c ∈ R}) ∧
      ∀ z : (Fin n → ZMod 2) × (Fin m → ZMod 2), (∀ j : Fin p.length,
        decide (query (p.take j.val) z = bias (p.take j.val)) = p.get j) →
        z.2 + Q z.1 ∈ out p) :
    ∃ cols : Fin (n + m - (k + d)) → (Fin n → ZMod 2),
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range cols)) = n + m - (k + d) ∧
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
        (Set.range (fun ij : Fin (n + m - (k + d)) × Fin (n + m - (k + d)) =>
          Q (cols ij.1 + cols ij.2) - Q (cols ij.1) - Q (cols ij.2) + Q 0))) ≤ k := by
  classical
  choose B hB using hQ
  have hcover : ∀ z : (Fin n → ZMod 2) × (Fin m → ZMod 2), ∃ q ∈ N \ J,
      ∀ j (hj : j < q.length), decide (query (q.take j) z = bias (q.take j)) = q[j] := by
    intro z
    exact reach N J (fun p z => decide (query p z = bias p)) hch z (N.sup List.length) [] h0
      (by simp) (by intro j hj; simp at hj)
  let region : List Bool → Finset ((Fin n → ZMod 2) × (Fin m → ZMod 2)) := fun p =>
    Finset.univ.filter (fun z => ∀ j (hj : j < p.length),
      decide (query (p.take j) z = bias (p.take j)) = p[j])
  have hsum : 2 ^ (n + m) ≤ ∑ p ∈ N \ J, (region p).card := by
    have h1 : (Finset.univ : Finset ((Fin n → ZMod 2) × (Fin m → ZMod 2))) ⊆
        (N \ J).biUnion region := by
      intro z _
      obtain ⟨q, hq, hc⟩ := hcover z
      exact Finset.mem_biUnion.2 ⟨q, hq, Finset.mem_filter.2 ⟨Finset.mem_univ _, hc⟩⟩
    have h2 := Finset.card_le_card h1
    have h3 : (Finset.univ : Finset ((Fin n → ZMod 2) × (Fin m → ZMod 2))).card
        = 2 ^ (n + m) := by
      simp [pow_add]
    calc 2 ^ (n + m) = _ := h3.symm
      _ ≤ _ := h2
      _ ≤ _ := Finset.card_biUnion_le
  have hne : (N \ J).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h] at hsum
    simp at hsum
  obtain ⟨p, hp, hpbig⟩ : ∃ p ∈ N \ J, 2 ^ (n + m) ≤ 2 ^ d * (region p).card := by
    apply Finset.exists_le_of_sum_le hne
    calc ∑ _p ∈ N \ J, 2 ^ (n + m) = (N \ J).card * 2 ^ (n + m) := by simp
      _ ≤ 2 ^ d * ∑ p ∈ N \ J, (region p).card := Nat.mul_le_mul hcard hsum
      _ = ∑ p ∈ N \ J, 2 ^ d * (region p).card := Finset.mul_sum _ _ _
  obtain ⟨⟨R, c, hRk, hout⟩, hT⟩ := hleaf p hp
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
  have hTU : ∀ u ∈ U, (z0 + u).2 + Q (z0 + u).1 - c ∈ R := by
    intro u hu
    have h1 : (z0 + u).2 + Q (z0 + u).1 ∈ out p := by
      apply hT (z0 + u)
      intro j
      rw [map_add, (hUmem u).1 hu j j.2, add_zero]
      exact hz0c j j.2
    rw [hout] at h1
    exact h1
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
  have hUdim : n + m ≤ d + Module.finrank (ZMod 2) U := by
    have h1 : Fintype.card U = 2 ^ Module.finrank (ZMod 2) U := by
      rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := U), ZMod.card]
    have h2 : 2 ^ (n + m) ≤ 2 ^ (d + Module.finrank (ZMod 2) U) := by
      rw [pow_add 2 d, ← h1]
      exact le_trans hpbig (Nat.mul_le_mul_left _ hregU)
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
  let f : U →ₗ[ZMod 2] (Fin n → ZMod 2) :=
    (LinearMap.fst (ZMod 2) (Fin n → ZMod 2) (Fin m → ZMod 2)) ∘ₗ U.subtype
  have hvert : ∀ u : (Fin n → ZMod 2) × (Fin m → ZMod 2), u ∈ U → u.1 = 0 → u.2 ∈ R := by
    intro u hu hu0
    have h1 := hTU u hu
    have h2 := hTU 0 U.zero_mem
    have h3 := R.sub_mem h1 h2
    have h4 : (z0 + u).2 + Q (z0 + u).1 - c - ((z0 + 0).2 + Q (z0 + 0).1 - c) = u.2 := by
      simp [hu0]
    rw [h4] at h3
    exact h3
  have hker : Module.finrank (ZMod 2) (LinearMap.ker f) ≤ Module.finrank (ZMod 2) R := by
    let g : LinearMap.ker f →ₗ[ZMod 2] R := LinearMap.codRestrict R
      ((LinearMap.snd (ZMod 2) (Fin n → ZMod 2) (Fin m → ZMod 2)) ∘ₗ U.subtype ∘ₗ
        (LinearMap.ker f).subtype) (by
        intro u
        exact hvert (u : U) (u : U).2 (LinearMap.mem_ker.1 u.2))
    apply LinearMap.finrank_le_finrank_of_injective (f := g)
    rw [injective_iff_map_eq_zero]
    intro u hu
    have hu2 : ((u : U) : (Fin n → ZMod 2) × (Fin m → ZMod 2)).2 = 0 := by
      have := congrArg Subtype.val hu
      exact this
    have hu1 : ((u : U) : (Fin n → ZMod 2) × (Fin m → ZMod 2)).1 = 0 := LinearMap.mem_ker.1 u.2
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext hu1 hu2
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  have hrange : n + m - (k + d) ≤ Module.finrank (ZMod 2) (LinearMap.range f) := by omega
  have hpolar : ∀ u ∈ U, ∀ u' ∈ U, Q (u.1 + u'.1) - Q u.1 - Q u'.1 + Q 0 ∈ R := by
    intro u hu u' hu'
    have h1 := hTU (u + u') (U.add_mem hu hu')
    have h2 := hTU u hu
    have h3 := hTU u' hu'
    have h4 := hTU 0 U.zero_mem
    have h5 := R.add_mem (R.sub_mem (R.sub_mem h1 h2) h3) h4
    have e := quad Q B hB z0.1 u.1 u'.1
    have h6 : (z0 + (u + u')).2 + Q (z0 + (u + u')).1 - c - ((z0 + u).2 + Q (z0 + u).1 - c)
        - ((z0 + u').2 + Q (z0 + u').1 - c) + ((z0 + 0).2 + Q (z0 + 0).1 - c)
        = Q (u.1 + u'.1) - Q u.1 - Q u'.1 + Q 0 := by
      rw [← e]
      simp only [Prod.fst_add, Prod.snd_add, add_zero]
      abel
    rw [h6] at h5
    exact h5
  let b := Module.finBasis (ZMod 2) (LinearMap.range f)
  let cols : Fin (n + m - (k + d)) → (Fin n → ZMod 2) := fun i =>
    ((b (Fin.castLE hrange i) : LinearMap.range f) : Fin n → ZMod 2)
  have hli : LinearIndependent (ZMod 2) cols := by
    have h1 : LinearIndependent (ZMod 2) (fun i : Fin (n + m - (k + d)) =>
        b (Fin.castLE hrange i)) :=
      b.linearIndependent.comp _ (Fin.castLE_injective hrange)
    exact h1.map' (LinearMap.range f).subtype (Submodule.ker_subtype _)
  refine ⟨cols, ?_, ?_⟩
  · rw [finrank_span_eq_card hli]
    simp
  · have hsub : Submodule.span (ZMod 2)
        (Set.range (fun ij : Fin (n + m - (k + d)) × Fin (n + m - (k + d)) =>
          Q (cols ij.1 + cols ij.2) - Q (cols ij.1) - Q (cols ij.2) + Q 0)) ≤ R := by
      rw [Submodule.span_le]
      rintro _ ⟨⟨i, j⟩, rfl⟩
      obtain ⟨u, hu⟩ := LinearMap.mem_range.1 (b (Fin.castLE hrange i)).2
      obtain ⟨u', hu'⟩ := LinearMap.mem_range.1 (b (Fin.castLE hrange j)).2
      have hi : cols i = (u : (Fin n → ZMod 2) × (Fin m → ZMod 2)).1 := hu.symm
      have hj : cols j = (u' : (Fin n → ZMod 2) × (Fin m → ZMod 2)).1 := hu'.symm
      show Q (cols i + cols j) - Q (cols i) - Q (cols j) + Q 0 ∈ R
      rw [hi, hj]
      exact hpolar u u.2 u' u'.2
    exact le_trans (Submodule.finrank_mono hsub) hRk

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

theorem polar_span {n m : ℕ} {ι : Type} (Q : (Fin n → ZMod 2) → (Fin m → ZMod 2))
    (B : (Fin n → ZMod 2) → (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2))
    (hB : ∀ a h, Q (a + h) = Q a + Q h - Q 0 + B a h) (cols : ι → (Fin n → ZMod 2))
    (S : Submodule (ZMod 2) (Fin m → ZMod 2))
    (hS : ∀ i j, Q (cols i + cols j) - Q (cols i) - Q (cols j) + Q 0 ∈ S) :
    ∀ x ∈ Submodule.span (ZMod 2) (Set.range cols),
      ∀ x' ∈ Submodule.span (ZMod 2) (Set.range cols), B x x' ∈ S := by
  have hsym : ∀ a h, B a h = B h a := by
    intro a h
    have h1 := hB a h
    have h2 := hB h a
    rw [add_comm h a] at h2
    have h3 := h1.symm.trans h2
    rw [add_comm (Q h) (Q a)] at h3
    exact add_left_cancel h3
  have hgen : ∀ i j, B (cols i) (cols j) ∈ S := by
    intro i j
    have h1 := hB (cols i) (cols j)
    have h2 : B (cols i) (cols j) = Q (cols i + cols j) - Q (cols i) - Q (cols j) + Q 0 := by
      rw [h1]
      abel
    rw [h2]
    exact hS i j
  have hA : ∀ i, ∀ x' ∈ Submodule.span (ZMod 2) (Set.range cols), B (cols i) x' ∈ S := by
    intro i x' hx'
    refine Submodule.span_induction (p := fun x' _ => B (cols i) x' ∈ S) ?_ ?_ ?_ ?_ hx'
    · rintro x ⟨j, rfl⟩
      exact hgen i j
    · rw [map_zero]
      exact S.zero_mem
    · intro x y _ _ hx hy
      rw [map_add]
      exact S.add_mem hx hy
    · intro r x _ hx
      rw [map_smul]
      exact S.smul_mem r hx
  intro x hx x' hx'
  refine Submodule.span_induction (p := fun x _ => B x x' ∈ S) ?_ ?_ ?_ ?_ hx
  · rintro x ⟨i, rfl⟩
    exact hA i x' hx'
  · rw [hsym, map_zero]
    exact S.zero_mem
  · intro x y _ _ hx hy
    rw [hsym, map_add, hsym x' x, hsym x' y]
    exact S.add_mem hx hy
  · intro r x _ hx
    rw [hsym, map_smul, hsym x' x]
    exact S.smul_mem r hx

theorem bwd (n m : ℕ) (Q : (Fin n → ZMod 2) → (Fin m → ZMod 2))
    (hQ : ∀ a : Fin n → ZMod 2, ∃ B : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2),
      ∀ h : Fin n → ZMod 2, Q (a + h) = Q a + Q h - Q 0 + B h)
    (k d : ℕ) (hkm : k ≤ m)
    (cols : Fin (n + m - (k + d)) → (Fin n → ZMod 2))
    (hind : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range cols))
      = n + m - (k + d))
    (hpol : Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
        (Set.range (fun ij : Fin (n + m - (k + d)) × Fin (n + m - (k + d)) =>
          Q (cols ij.1 + cols ij.2) - Q (cols ij.1) - Q (cols ij.2) + Q 0))) ≤ k) :
    ∃ (N J : Finset (List Bool))
      (query : List Bool → ((Fin n → ZMod 2) × (Fin m → ZMod 2)) →ₗ[ZMod 2] ZMod 2)
      (bias : List Bool → ZMod 2) (out : List Bool → Set (Fin m → ZMod 2)),
      [] ∈ N ∧ J ⊆ N ∧
      (∀ (p : List Bool) (t : Bool), p ++ [t] ∈ N → p ∈ J) ∧
      (∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N) ∧
      (N \ J).card ≤ 2 ^ d ∧ ∀ p ∈ N \ J,
        (∃ (R : Submodule (ZMod 2) (Fin m → ZMod 2)) (c : Fin m → ZMod 2),
          Module.finrank (ZMod 2) R ≤ k ∧ out p = {w : Fin m → ZMod 2 | w - c ∈ R}) ∧
        ∀ z : (Fin n → ZMod 2) × (Fin m → ZMod 2), (∀ j : Fin p.length,
          decide (query (p.take j.val) z = bias (p.take j.val)) = p.get j) →
          z.2 + Q z.1 ∈ out p := by
  classical
  choose B hB using hQ
  obtain ⟨C, hCdef⟩ : ∃ C : Submodule (ZMod 2) (Fin n → ZMod 2),
      C = Submodule.span (ZMod 2) (Set.range cols) := ⟨_, rfl⟩
  obtain ⟨S, hSdef⟩ : ∃ S : Submodule (ZMod 2) (Fin m → ZMod 2),
      S = Submodule.span (ZMod 2)
        (Set.range (fun ij : Fin (n + m - (k + d)) × Fin (n + m - (k + d)) =>
          Q (cols ij.1 + cols ij.2) - Q (cols ij.1) - Q (cols ij.2) + Q 0)) := ⟨_, rfl⟩
  rw [← hCdef] at hind
  rw [← hSdef] at hpol
  have hBS : ∀ x ∈ C, ∀ x' ∈ C, B x x' ∈ S := by
    rw [hCdef]
    apply polar_span Q B hB cols S
    intro i j
    rw [hSdef]
    exact Submodule.subset_span ⟨(i, j), rfl⟩
  obtain ⟨C', hC'⟩ := Submodule.exists_isCompl C
  obtain ⟨S', hS'⟩ := Submodule.exists_isCompl S
  have hCC := Submodule.finrank_add_eq_of_isCompl hC'
  have hSS := Submodule.finrank_add_eq_of_isCompl hS'
  rw [Module.finrank_fin_fun] at hCC hSS
  have hC'dim : Module.finrank (ZMod 2) C' = n - (n + m - (k + d)) := by omega
  have hS'dim : m - k ≤ Module.finrank (ZMod 2) S' := by omega
  have hD : (n - (n + m - (k + d))) + (m - k) ≤ d := by omega
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a = n - (n + m - (k + d)) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ, b = m - k := ⟨_, rfl⟩
  rw [← ha] at hC'dim hD
  rw [← hb] at hS'dim hD

  let eC := (Module.finBasisOfFinrankEq (ZMod 2) C' hC'dim).equivFun
  let φ : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin a → ZMod 2) :=
    eC.toLinearMap ∘ₗ C'.projectionOnto C hC'.symm
  let σ : (Fin a → ZMod 2) → (Fin n → ZMod 2) := fun s => ((eC.symm s : C') : Fin n → ZMod 2)
  let ρ : (Fin n → ZMod 2) →ₗ[ZMod 2] C := C.projectionOnto C' hC'
  have hdecomp : ∀ x : Fin n → ZMod 2, x = σ (φ x) + (ρ x : Fin n → ZMod 2) := by
    intro x
    have h1 := Submodule.projection_add_projection_eq_self hC' x
    have h2 : σ (φ x) = C'.projection C hC'.symm x := by
      simp [σ, φ]
    have h3 : (ρ x : Fin n → ZMod 2) = C.projection C' hC' x := rfl
    rw [h2, h3, add_comm]
    exact h1.symm

  let eS := (Module.finBasis (ZMod 2) S').equivFun
  let θ : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin b → ZMod 2) :=
    (LinearMap.funLeft (ZMod 2) (ZMod 2) (Fin.castLE hS'dim)) ∘ₗ eS.toLinearMap ∘ₗ
      S'.projectionOnto S hS'.symm
  have hθsurj : Function.Surjective θ := by
    have h1 : Function.Surjective (LinearMap.funLeft (ZMod 2) (ZMod 2) (Fin.castLE hS'dim)) :=
      LinearMap.funLeft_surjective_of_injective _ _ _ (Fin.castLE_injective hS'dim)
    have h2 : Function.Surjective (S'.projectionOnto S hS'.symm) :=
      Submodule.projectionOnto_surjective hS'.symm
    exact h1.comp (eS.surjective.comp h2)
  have hθS : ∀ w ∈ S, θ w = 0 := by
    intro w hw
    have h1 : S'.projectionOnto S hS'.symm w = 0 :=
      (Submodule.projectionOnto_apply_eq_zero_iff hS'.symm).2 hw
    simp [θ, h1]
  have hkerdim : Module.finrank (ZMod 2) (LinearMap.ker θ) ≤ k := by
    have h1 := LinearMap.finrank_range_add_finrank_ker θ
    rw [LinearMap.range_eq_top.2 hθsurj, finrank_top, Module.finrank_fin_fun,
      Module.finrank_fin_fun] at h1
    omega
  let τ : (Fin b → ZMod 2) → (Fin m → ZMod 2) := Function.surjInv hθsurj
  have hτ : ∀ v, θ (τ v) = v := Function.surjInv_eq hθsurj
  let gC : C →ₗ[ZMod 2] (Fin b → ZMod 2) := AddMonoidHom.toZModLinearMap 2
    { toFun := fun c => θ (Q (c : Fin n → ZMod 2) - Q 0)
      map_zero' := by simp
      map_add' := by
        intro c c'
        have h1 := hB (c : Fin n → ZMod 2) (c' : Fin n → ZMod 2)
        have h2 := hθS _ (hBS c c.2 c' c'.2)
        show θ (Q ((c : Fin n → ZMod 2) + (c' : Fin n → ZMod 2)) - Q 0)
          = θ (Q (c : Fin n → ZMod 2) - Q 0) + θ (Q (c' : Fin n → ZMod 2) - Q 0)
        rw [h1, ← map_add]
        have h3 : Q (c : Fin n → ZMod 2) + Q (c' : Fin n → ZMod 2) - Q 0
            + B (c : Fin n → ZMod 2) (c' : Fin n → ZMod 2) - Q 0
            = (Q (c : Fin n → ZMod 2) - Q 0 + (Q (c' : Fin n → ZMod 2) - Q 0))
              + B (c : Fin n → ZMod 2) (c' : Fin n → ZMod 2) := by abel
        rw [h3, map_add θ, h2, add_zero] }
  have hgC : ∀ c : C, gC c = θ (Q (c : Fin n → ZMod 2) - Q 0) := fun _ => rfl
  let Λ : (Fin a → ZMod 2) → ((Fin n → ZMod 2) × (Fin m → ZMod 2)) →ₗ[ZMod 2] (Fin b → ZMod 2) :=
    fun s => θ ∘ₗ LinearMap.snd (ZMod 2) (Fin n → ZMod 2) (Fin m → ZMod 2)
      + (gC + θ ∘ₗ (B (σ s)) ∘ₗ C.subtype) ∘ₗ ρ ∘ₗ
        LinearMap.fst (ZMod 2) (Fin n → ZMod 2) (Fin m → ZMod 2)
  have hΛ : ∀ z : (Fin n → ZMod 2) × (Fin m → ZMod 2),
      θ (z.2 + Q z.1) = Λ (φ z.1) z + θ (Q (σ (φ z.1))) := by
    intro z
    have h1 := hB (σ (φ z.1)) (ρ z.1 : Fin n → ZMod 2)
    rw [← hdecomp z.1] at h1
    have h2 : Λ (φ z.1) z = θ z.2 + (θ (Q (ρ z.1 : Fin n → ZMod 2) - Q 0)
        + θ (B (σ (φ z.1)) (ρ z.1 : Fin n → ZMod 2))) := rfl
    rw [h2, ← map_add, ← map_add, ← map_add]
    congr 1
    rw [h1]
    abel

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
    fun p => {w | w - τ (eOf p + θ (Q (σ (sOf p)))) ∈ LinearMap.ker θ}, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hD
  · intro p hp
    rw [Finset.mem_sdiff, hN, hJ] at hp
    have hlen : p.length = a + b := by omega
    refine ⟨⟨LinearMap.ker θ, τ (eOf p + θ (Q (σ (sOf p)))), hkerdim, rfl⟩, ?_⟩
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
    show z.2 + Q z.1 - τ (eOf p + θ (Q (σ (sOf p)))) ∈ LinearMap.ker θ
    rw [LinearMap.mem_ker, map_sub, hτ, hΛ z, c1, c2, sub_self]

end PEqualNP.Outside.L_pcx_396

theorem PEqualNP.Outside.L_pcx_396 : (∀ (n m : ℕ),
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
    (k d : ℕ) (_ : k ≤ m),
    let allowed := {L : Set Y | ∃ (R : Submodule F Y) (c : Y),
      Module.finrank F R ≤ k ∧ L = {w : Y | w-c ∈ R}}
    let t := n+m-(k+d)
    tree (fun z => z.2 + Q z.1) allowed (2^d) ↔
      ∃ cols : Fin t → X,
        Module.finrank F (Submodule.span F (Set.range cols)) = t ∧
        Module.finrank F (Submodule.span F (Set.range (fun ij : Fin t × Fin t =>
          Q (cols ij.1 + cols ij.2) - Q (cols ij.1) - Q (cols ij.2) + Q 0))) ≤ k) := by
  intro n m F X Y tree Q hQ k d hkm allowed t
  constructor
  · rintro ⟨N, J, query, bias, out, h0, _, _, hch, hcard, hleaf⟩
    exact PEqualNP.Outside.L_pcx_396.fwd n m Q hQ k d N J query bias out h0 hch hcard hleaf
  · rintro ⟨cols, hind, hpol⟩
    exact PEqualNP.Outside.L_pcx_396.bwd n m Q hQ k d hkm cols hind hpol
