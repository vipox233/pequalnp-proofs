import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_536 : (∀ (n d : Nat),
  let k := d+1
  let V := Fin n
  let Point := V → Bool
  let Clause := Finset (V × Bool)
  ∀ (F : Finset Clause) (center : Point),
    let vars := fun (c : Clause) => c.image Prod.fst
    let bad := fun (x : Point) (c : Clause) => ∀ lit ∈ c, x lit.1 ≠ lit.2
    (∀ c ∈ F, (vars c).card ≤ k) →
    ∃ G : Finset Clause, G ⊆ F ∧
      (∀ c ∈ G, bad center c ∧ (vars c).card = k) ∧
      (∀ c ∈ G, ∀ d ∈ G, c ≠ d → Disjoint (vars c) (vars d)) ∧
      let U := G.biUnion vars
      U.card ≤ k*G.card ∧
        ∀ beta : Point,
          let mixed : Point := fun v => if v ∈ U then beta v else center v
          ∀ cl ∈ F, bad mixed cl → ((vars cl) \ U).card < k) := by
  intro n d k V Point Clause F center vars bad hF
  classical
  let valid : Finset Clause → Prop := fun G => G ⊆ F ∧ (∀ c ∈ G, bad center c ∧ (vars c).card = k) ∧
      (∀ c ∈ G, ∀ e ∈ G, c ≠ e → Disjoint (vars c) (vars e))
  obtain ⟨G, hGS, hmax⟩ := (F.powerset.filter valid).exists_max_image Finset.card
    ⟨∅, Finset.mem_filter.2 ⟨Finset.empty_mem_powerset _, Finset.empty_subset _, by simp, by simp⟩⟩
  obtain ⟨-, hGF, hbad, hdisj⟩ := Finset.mem_filter.1 hGS
  refine ⟨G, hGF, hbad, hdisj, ?_⟩
  intro U
  refine ⟨?_, ?_⟩
  · calc U.card ≤ ∑ c ∈ G, (vars c).card := Finset.card_biUnion_le
      _ = ∑ c ∈ G, k := Finset.sum_congr rfl (fun c hc => (hbad c hc).2)
      _ = k * G.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  · intro beta mixed cl hcl hb
    by_contra hlt
    have hlt' : k ≤ (vars cl \ U).card := Nat.le_of_not_lt hlt
    have hsub : vars cl \ U ⊆ vars cl := Finset.sdiff_subset
    have hle : (vars cl).card ≤ k := hF cl hcl
    have heq : vars cl \ U = vars cl := Finset.eq_of_subset_of_card_le hsub (by omega)
    have hdisjU : Disjoint (vars cl) U := by
      rw [← heq]
      exact Finset.sdiff_disjoint
    have hcard : (vars cl).card = k := by
      have := Finset.card_le_card hsub
      omega
    have hbc : bad center cl := by
      show ∀ lit ∈ cl, center lit.1 ≠ lit.2
      intro lit hlit
      have hv : lit.1 ∈ vars cl := Finset.mem_image_of_mem _ hlit
      have hnU : lit.1 ∉ U := Finset.disjoint_left.1 hdisjU hv
      have h1 : mixed lit.1 ≠ lit.2 := hb lit hlit
      have h2 : mixed lit.1 = center lit.1 := by
        show (if lit.1 ∈ U then beta lit.1 else center lit.1) = center lit.1
        rw [if_neg hnU]
      rw [h2] at h1
      exact h1
    have hnotin : cl ∉ G := by
      intro hin
      have hne : (vars cl).Nonempty := by
        rw [← Finset.card_pos, hcard]
        omega
      obtain ⟨x, hx⟩ := hne
      exact Finset.disjoint_left.1 hdisjU hx (Finset.mem_biUnion.2 ⟨cl, hin, hx⟩)
    have hvalid : insert cl G ∈ F.powerset.filter valid := by
      refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.insert_subset hcl hGF),
        Finset.insert_subset hcl hGF, ?_, ?_⟩
      · intro c hc
        rcases Finset.mem_insert.1 hc with rfl | hc
        · exact ⟨hbc, hcard⟩
        · exact hbad c hc
      · intro c hc e he hce
        rcases Finset.mem_insert.1 hc with rfl | hcG <;> rcases Finset.mem_insert.1 he with rfl | heG
        · exact absurd rfl hce
        · exact Finset.disjoint_of_subset_right (Finset.subset_biUnion_of_mem vars heG) hdisjU
        · exact (Finset.disjoint_of_subset_right (Finset.subset_biUnion_of_mem vars hcG) hdisjU).symm
        · exact hdisj c hcG e heG hce
    have hm := hmax _ hvalid
    rw [Finset.card_insert_of_notMem hnotin] at hm
    omega
