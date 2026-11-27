import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_643_aux

theorem greedy {α : Type*} [DecidableEq α] (w : α → ℕ) (h : ℕ) :
    ∀ F : Finset α, (∀ s ∈ F, 3 * w s < h) → h ≤ 3 * ∑ s ∈ F, w s →
    ∃ L, L ⊆ F ∧ h ≤ 3 * ∑ s ∈ L, w s ∧ 3 * ∑ s ∈ L, w s ≤ 2 * h := by
  intro F
  induction F using Finset.induction_on with
  | empty =>
    intro _ h0
    exact ⟨∅, Finset.Subset.refl _, h0, by simp⟩
  | insert a F' ha ih =>
    intro hs hsum
    by_cases hc : h ≤ 3 * ∑ s ∈ F', w s
    · obtain ⟨L, hL, h1, h2⟩ := ih (fun s hs' => hs s (Finset.mem_insert_of_mem hs')) hc
      exact ⟨L, hL.trans (Finset.subset_insert _ _), h1, h2⟩
    · refine ⟨insert a F', Finset.Subset.refl _, hsum, ?_⟩
      rw [Finset.sum_insert ha]
      have := hs a (Finset.mem_insert_self _ _)
      omega

theorem split {α : Type*} [DecidableEq α] (w : α → ℕ) (h : ℕ) (hh : 2 ≤ h) (F : Finset α)
    (hw : ∀ s ∈ F, 1 ≤ w s ∧ w s < h) (hsum : ∑ s ∈ F, w s = h) :
    ∃ L, L ⊆ F ∧ 0 < ∑ s ∈ L, w s ∧ ∑ s ∈ L, w s < h ∧
      (2 * h < 3 * ∑ s ∈ L, w s → L.card = 1) ∧
      (2 * h < 3 * (h - ∑ s ∈ L, w s) → (F \ L).card = 1) := by
  by_cases hc : ∃ s ∈ F, h ≤ 3 * w s
  · obtain ⟨s, hs, h3⟩ := hc
    have := hw s hs
    refine ⟨{s}, Finset.singleton_subset_iff.mpr hs, ?_⟩
    simp only [Finset.sum_singleton, Finset.card_singleton]
    refine ⟨by omega, by omega, fun _ => trivial, ?_⟩
    intro h4
    omega
  · simp only [not_exists, not_and, not_le] at hc
    obtain ⟨L, hL, h1, h2⟩ := greedy w h F hc (by omega)
    exact ⟨L, hL, by omega, by omega, by omega, by omega⟩

def recolor {v : ℕ} (U LU red : Finset (Fin v)) : Finset (Fin v) := (red \ U) ∪ LU

theorem count {v : ℕ} (h : ℕ) (F L : Finset (Finset (Fin v))) (hL : L ⊆ F)
    (hcard : ∀ s ∈ F, 2 ≤ s.card)
    (hdisj : ∀ s ∈ F, ∀ u ∈ F, s ≠ u → Disjoint s u)
    (hsum : ∑ s ∈ F, (s.card - 1) = h) :
    ∃ G : Finset (Finset (Fin v)),
      (∀ red ∈ G, (∀ s ∈ L, s ⊆ red) ∧ (∀ s ∈ F \ L, Disjoint s red)) ∧
      2 ^ v ≤ G.card * 4 ^ h := by
  have hLUU : L.biUnion id ⊆ F.biUnion id := Finset.biUnion_subset_biUnion_of_subset_left _ hL
  have hUcard : (F.biUnion id).card ≤ 2 * h := by
    calc (F.biUnion id).card ≤ ∑ s ∈ F, (id s).card := Finset.card_biUnion_le
      _ ≤ ∑ s ∈ F, 2 * (s.card - 1) :=
          Finset.sum_le_sum (fun s hs => by have := hcard s hs; simp only [id]; omega)
      _ = 2 * h := by rw [← Finset.mul_sum, hsum]
  refine ⟨Finset.univ.image (recolor (F.biUnion id) (L.biUnion id)), ?_, ?_⟩
  · intro red hred
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hred
    constructor
    · intro s hs
      exact (Finset.subset_biUnion_of_mem id hs).trans Finset.subset_union_right
    · intro s hs
      obtain ⟨hsF, hsL⟩ := Finset.mem_sdiff.mp hs
      unfold recolor
      rw [Finset.disjoint_union_right]
      constructor
      · exact Disjoint.mono_left (Finset.subset_biUnion_of_mem id hsF) Finset.disjoint_sdiff
      · rw [Finset.disjoint_biUnion_right]
        intro u hu
        exact hdisj s hsF u (hL hu) (fun e => hsL (by rw [e]; exact hu))
  · have key := Finset.card_le_mul_card_image (f := recolor (F.biUnion id) (L.biUnion id))
      Finset.univ (4 ^ h) ?_
    · rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin] at key
      rw [Nat.mul_comm]; exact key
    · intro a _
      calc (Finset.univ.filter fun x => recolor (F.biUnion id) (L.biUnion id) x = a).card
            ≤ (F.biUnion id).powerset.card := by
            apply Finset.card_le_card_of_injOn (fun x => x ∩ F.biUnion id)
            · intro x _
              exact Finset.mem_coe.mpr (Finset.mem_powerset.mpr Finset.inter_subset_right)
            · intro x hx y hy hxy
              rw [Finset.mem_coe, Finset.mem_filter] at hx hy
              have hxy' : x ∩ F.biUnion id = y ∩ F.biUnion id := hxy
              ext z
              have h1 := Finset.ext_iff.mp (hx.2.trans hy.2.symm) z
              have h2 := Finset.ext_iff.mp hxy' z
              have h3 : z ∈ L.biUnion id → z ∈ F.biUnion id := fun hz => hLUU hz
              simp only [recolor, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter] at h1 h2
              tauto
        _ = 2 ^ (F.biUnion id).card := Finset.card_powerset _
        _ ≤ 2 ^ (2 * h) := Nat.pow_le_pow_right (by norm_num) hUcard
        _ = 4 ^ h := by rw [pow_mul]; norm_num

end PEqualNP.Outside.L_lib_643_aux

theorem PEqualNP.Outside.L_lib_643 : ∀ (v n h : Nat), 0 < n → 2 ≤ h →
  let V := Fin v
  let P := Finset (Finset V)
  let gain := fun (p : P) => p.sum (fun s => s.card-1)
  ∀ fam : Fin n → P,
    (∀ i, (∀ s ∈ fam i, 2 ≤ s.card ∧ s.card-1 < h) ∧
      (∀ s ∈ fam i, ∀ u ∈ fam i, s ≠ u → Disjoint s u) ∧ gain (fam i) = h) →
    ∃ (red : Finset V) (redGain : Nat) (I : Finset (Fin n)),
      0 < redGain ∧ redGain < h ∧ n ≤ I.card * h * 4^h ∧
      ∀ i ∈ I,
        let left := (fam i).filter (fun s => s ⊆ red)
        let right := (fam i).filter (fun u => Disjoint u red)
        fam i = left ∪ right ∧ gain left = redGain ∧ gain right = h-redGain ∧
        (2*h < 3*redGain → left.card = 1) ∧
        (2*h < 3*(h-redGain) → right.card = 1) := by
  intro v n h hn hh
  dsimp only
  intro fam hfam
  have hsplit : ∀ i, ∃ L, L ⊆ fam i ∧ 0 < ∑ s ∈ L, (s.card - 1) ∧ ∑ s ∈ L, (s.card - 1) < h ∧
      (2 * h < 3 * ∑ s ∈ L, (s.card - 1) → L.card = 1) ∧
      (2 * h < 3 * (h - ∑ s ∈ L, (s.card - 1)) → (fam i \ L).card = 1) := fun i =>
    PEqualNP.Outside.L_lib_643_aux.split (fun s : Finset (Fin v) => s.card - 1) h hh (fam i)
      (fun s hs => by have := (hfam i).1 s hs; show 1 ≤ s.card - 1 ∧ s.card - 1 < h; omega) (hfam i).2.2
  choose L hLsub hLpos hLlt hL1 hL2 using hsplit
  have hcount := fun i => PEqualNP.Outside.L_lib_643_aux.count h (fam i) (L i) (hLsub i)
    (fun s hs => ((hfam i).1 s hs).1) (hfam i).2.1 (hfam i).2.2
  choose G hGgood hGcard using hcount
  obtain ⟨c, hc⟩ : ∃ c : Finset (Fin v) → ℕ,
      ∀ r, c r = (Finset.univ.filter (fun i => r ∈ G i)).card := ⟨_, fun _ => rfl⟩
  obtain ⟨red, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Finset (Fin v))) c
    ⟨∅, Finset.mem_univ _⟩
  have hswap : ∑ i, (G i).card = ∑ r : Finset (Fin v), c r := by
    have : ∀ i, (G i).card = ∑ r : Finset (Fin v), if r ∈ G i then 1 else 0 := by intro i; simp
    simp only [this, hc, Finset.card_filter]
    exact Finset.sum_comm
  have hle : ∑ r : Finset (Fin v), c r ≤ 2 ^ v * c red := by
    have := Finset.sum_le_card_nsmul Finset.univ c (c red) (fun r hr => hmax r hr)
    simpa [Finset.card_univ, Fintype.card_finset] using this
  have hn1 : n * 2 ^ v ≤ (∑ i, (G i).card) * 4 ^ h := by
    rw [Finset.sum_mul]
    calc n * 2 ^ v = ∑ i : Fin n, 2 ^ v := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i _ => hGcard i)
  have hn2 : n ≤ c red * 4 ^ h := by
    have : 2 ^ v * n ≤ 2 ^ v * (c red * 4 ^ h) := by
      calc 2 ^ v * n = n * 2 ^ v := Nat.mul_comm _ _
        _ ≤ (∑ i, (G i).card) * 4 ^ h := hn1
        _ ≤ (2 ^ v * c red) * 4 ^ h := Nat.mul_le_mul_right _ (by rw [hswap]; exact hle)
        _ = _ := Nat.mul_assoc _ _ _
    exact Nat.le_of_mul_le_mul_left this (by positivity)
  obtain ⟨J, hJ⟩ : ∃ J, J = Finset.univ.filter (fun i => red ∈ G i) := ⟨_, rfl⟩
  rw [hc, ← hJ] at hn2
  obtain ⟨g, hg⟩ : ∃ g : Fin n → ℕ, ∀ i, g i = ∑ s ∈ L i, (s.card - 1) := ⟨_, fun _ => rfl⟩
  have hfib := Finset.card_eq_sum_card_fiberwise (s := J) (t := Finset.Ico 1 h) (f := g)
    (fun i _ => Finset.mem_Ico.mpr ⟨by rw [hg]; exact hLpos i, by rw [hg]; exact hLlt i⟩)
  obtain ⟨b, hb, hbmax⟩ := Finset.exists_max_image (Finset.Ico 1 h)
    (fun b => (J.filter (fun i => g i = b)).card) ⟨1, Finset.mem_Ico.mpr ⟨le_refl _, hh⟩⟩
  have hJle : J.card ≤ (J.filter (fun i => g i = b)).card * h := by
    rw [hfib]
    have := Finset.sum_le_card_nsmul (Finset.Ico 1 h) _ _ hbmax
    simp only [Nat.card_Ico, smul_eq_mul] at this
    calc _ ≤ (h - 1) * _ := this
      _ ≤ _ := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  obtain ⟨hb1, hb2⟩ := Finset.mem_Ico.mp hb
  refine ⟨red, b, J.filter (fun i => g i = b), hb1, hb2, ?_, ?_⟩
  · calc n ≤ J.card * 4 ^ h := hn2
      _ ≤ _ := Nat.mul_le_mul_right _ hJle
  · intro i hi
    obtain ⟨hiJ, hgi⟩ := Finset.mem_filter.mp hi
    rw [hJ] at hiJ
    have hired : red ∈ G i := (Finset.mem_filter.mp hiJ).2
    obtain ⟨hg1, hg2⟩ := hGgood i red hired
    have hne : ∀ s ∈ fam i, s ⊆ red → Disjoint s red → False := by
      intro s hsF hsr hd
      have h0 : s = ∅ := by simpa using Disjoint.mono_right hsr hd
      have h2 := ((hfam i).1 s hsF).1
      rw [h0] at h2
      simp at h2
    have hl : (fam i).filter (fun s => s ⊆ red) = L i := by
      ext s
      rw [Finset.mem_filter]
      constructor
      · rintro ⟨hsF, hsr⟩
        by_contra hsL
        exact hne s hsF hsr (hg2 s (Finset.mem_sdiff.mpr ⟨hsF, hsL⟩))
      · intro hsL
        exact ⟨hLsub i hsL, hg1 s hsL⟩
    have hr : (fam i).filter (fun u => Disjoint u red) = fam i \ L i := by
      ext s
      rw [Finset.mem_filter, Finset.mem_sdiff]
      constructor
      · rintro ⟨hsF, hd⟩
        exact ⟨hsF, fun hsL => hne s hsF (hg1 s hsL) hd⟩
      · rintro ⟨hsF, hsL⟩
        exact ⟨hsF, hg2 s (Finset.mem_sdiff.mpr ⟨hsF, hsL⟩)⟩
    rw [hl, hr]
    have hsd := Finset.sum_sdiff (f := fun s : Finset (Fin v) => s.card - 1) (hLsub i)
    have htot := (hfam i).2.2
    have hgi' : ∑ s ∈ L i, (s.card - 1) = b := by rw [← hg]; exact hgi
    refine ⟨(Finset.union_sdiff_of_subset (hLsub i)).symm, hgi', ?_, ?_, ?_⟩
    · omega
    · have := hL1 i
      rw [hgi'] at this
      exact this
    · have := hL2 i
      rw [hgi'] at this
      exact this
