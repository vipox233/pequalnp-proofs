import Mathlib
import PEqualNP.Defs

open Module

namespace PEqualNP.Outside.L_lib_665_aux

lemma odd_nsmul_eq {r : ℕ} (v : Fin r → ZMod 2) (n : ℕ) (h : n % 2 = 1) : n • v = v := by
  have h1 : ((n : ℕ) : ZMod 2) = 1 := ZMod.natCast_eq_one_iff_odd.2 (Nat.odd_iff.2 h)
  funext k
  simp [Pi.smul_apply, nsmul_eq_mul, h1]

lemma even_nsmul_eq {r : ℕ} (v : Fin r → ZMod 2) (n : ℕ) (h : n % 2 = 0) : n • v = 0 := by
  have h1 : ((n : ℕ) : ZMod 2) = 0 := ZMod.natCast_eq_zero_iff_even.2 (Nat.even_iff.2 h)
  funext k
  simp [Pi.smul_apply, nsmul_eq_mul, h1]

lemma sum_sub_const {r : ℕ} (E : Finset (Fin r → ZMod 2)) (s : Fin r → ZMod 2)
    (h : E.card % 2 = 1) : ∑ t ∈ E, (t - s) = (∑ t ∈ E, t) - s := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, odd_nsmul_eq s _ h]

lemma lower {r m : ℕ} (tag : Fin m → Fin r → ZMod 2) (hm : 0 < m)
    (E : Fin m → Finset (Fin r → ZMod 2))
    (hE : ∀ i, (E i).card % 2 = 1 ∧ ∑ t ∈ E i, t = tag i) :
    finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range fun i => tag i - tag ⟨0, hm⟩)) + 1 ≤
      ((Finset.univ : Finset (Fin m)).biUnion E).card := by
  classical
  set S := (Finset.univ : Finset (Fin m)).biUnion E with hS
  obtain ⟨s0, hs0⟩ : (E ⟨0, hm⟩).Nonempty := by
    rw [← Finset.card_pos]; have := (hE ⟨0, hm⟩).1; omega
  have hs0S : s0 ∈ S := Finset.mem_biUnion.2 ⟨_, Finset.mem_univ _, hs0⟩
  set G := (S.erase s0).image (fun t => t - s0) with hG
  have hmemS : ∀ t ∈ S, t - s0 ∈ Submodule.span (ZMod 2) (G : Set (Fin r → ZMod 2)) := by
    intro t ht
    by_cases h : t = s0
    · subst h; simp
    · exact Submodule.subset_span
        (Finset.mem_coe.2 (Finset.mem_image.2 ⟨t, Finset.mem_erase.2 ⟨h, ht⟩, rfl⟩))
  have htag : ∀ i, tag i - s0 ∈ Submodule.span (ZMod 2) (G : Set (Fin r → ZMod 2)) := by
    intro i
    rw [← (hE i).2, ← sum_sub_const _ _ (hE i).1]
    exact Submodule.sum_mem _
      (fun t ht => hmemS t (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, ht⟩))
  have hle : Submodule.span (ZMod 2) (Set.range fun i => tag i - tag ⟨0, hm⟩) ≤
      Submodule.span (ZMod 2) (G : Set (Fin r → ZMod 2)) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have := Submodule.sub_mem _ (htag i) (htag ⟨0, hm⟩)
    simpa using this
  have h1 := Submodule.finrank_mono hle
  have h2 : finrank (ZMod 2) (Submodule.span (ZMod 2) (G : Set (Fin r → ZMod 2))) ≤ G.card :=
    finrank_span_finset_le_card G
  have h3 : G.card ≤ (S.erase s0).card := Finset.card_image_le
  have h4 := Finset.card_erase_add_one hs0S
  omega

lemma normals_card {r m : ℕ} (tag : Fin m → Fin r → ZMod 2) (hm : 0 < m) :
    ((Finset.univ : Finset (Fin r → ZMod 2)).filter (fun v =>
      ∀ i j : Fin m, (∑ k, v k * tag i k) = ∑ k, v k * tag j k)).card =
    2 ^ (r - finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range fun i => tag i - tag ⟨0, hm⟩))) ∧
    finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range fun i => tag i - tag ⟨0, hm⟩)) ≤ r := by
  classical
  let A : Matrix (Fin m) (Fin r) (ZMod 2) := fun i => tag i - tag ⟨0, hm⟩
  have hrank : A.rank = finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range fun i => tag i - tag ⟨0, hm⟩)) :=
    Matrix.rank_eq_finrank_span_row A
  have hrn := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  rw [Module.finrank_fin_fun] at hrn
  have hr : A.rank = finrank (ZMod 2) (LinearMap.range A.mulVecLin) := rfl
  have hmv : ∀ v i, (A.mulVec v) i = (∑ k, v k * tag i k) - ∑ k, v k * tag ⟨0, hm⟩ k := by
    intro v i
    simp only [Matrix.mulVec, dotProduct, A, Pi.sub_apply]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  have hfilter : ((Finset.univ : Finset (Fin r → ZMod 2)).filter (fun v =>
      ∀ i j : Fin m, (∑ k, v k * tag i k) = ∑ k, v k * tag j k)) =
      (Finset.univ : Finset (Fin r → ZMod 2)).filter (fun v => v ∈ LinearMap.ker A.mulVecLin) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, LinearMap.mem_ker,
      Matrix.mulVecLin_apply]
    constructor
    · intro h
      funext i
      rw [hmv, h i ⟨0, hm⟩, sub_self]
      rfl
    · intro h i j
      have hi := congrFun h i
      have hj := congrFun h j
      rw [hmv] at hi hj
      have hi' := sub_eq_zero.1 hi
      have hj' := sub_eq_zero.1 hj
      rw [hi', hj']
  have hcard : ((Finset.univ : Finset (Fin r → ZMod 2)).filter
      (fun v => v ∈ LinearMap.ker A.mulVecLin)).card = 2 ^ finrank (ZMod 2) (LinearMap.ker A.mulVecLin) := by
    rw [← Fintype.card_subtype, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  rw [hfilter, hcard]
  constructor
  · congr 1; omega
  · omega

lemma upper {r m : ℕ} (tag : Fin m → Fin r → ZMod 2) (hm : 0 < m) :
    ∃ E : Fin m → Finset (Fin r → ZMod 2), (∀ i, (E i).card % 2 = 1 ∧ ∑ t ∈ E i, t = tag i) ∧
      (Finset.univ : Finset (Fin m)).biUnion E ⊆ (Finset.univ : Finset (Fin m)).image tag ∧
      ((Finset.univ : Finset (Fin m)).biUnion E).card ≤
        finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range fun i => tag i - tag ⟨0, hm⟩)) + 1 := by
  classical
  set t0 := tag ⟨0, hm⟩ with ht0
  obtain ⟨b, hbsub, hbspan, hbli⟩ :=
    exists_linearIndependent (ZMod 2) (Set.range fun i => tag i - t0)
  set bF : Finset (Fin r → ZMod 2) := Finset.univ.filter (· ∈ b) with hbFdef
  have hbF : (bF : Set (Fin r → ZMod 2)) = b := by ext x; simp [bF]
  have hdim : finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range fun i => tag i - t0)) =
      bF.card := by
    rw [← hbspan, ← hbF]
    apply finrank_span_finset_eq_card
    rw [hbF]
    exact hbli
  have hne : ∀ x ∈ bF, x ≠ 0 := fun x hx => by
    have hx' : x ∈ b := by simpa [bF] using hx
    exact hbli.ne_zero ⟨x, hx'⟩
  have hentry : ∀ x ∈ bF, t0 + x ∈ (Finset.univ : Finset (Fin m)).image tag := by
    intro x hx
    have hx' : x ∈ b := by simpa [bF] using hx
    obtain ⟨i, hi⟩ := hbsub hx'
    refine Finset.mem_image.2 ⟨i, Finset.mem_univ _, ?_⟩
    rw [← hi]
    simp
  have ht0mem : t0 ∈ (Finset.univ : Finset (Fin m)).image tag :=
    Finset.mem_image.2 ⟨⟨0, hm⟩, Finset.mem_univ _, rfl⟩
  have hrep : ∀ i, ∃ T ⊆ bF, ∑ x ∈ T, x = tag i - t0 := by
    intro i
    have hmem : tag i - t0 ∈ Submodule.span (ZMod 2) (bF : Set (Fin r → ZMod 2)) := by
      rw [hbF, hbspan]; exact Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.1 hmem
    refine ⟨bF.filter (fun x => f x = 1), Finset.filter_subset _ _, ?_⟩
    rw [← hf, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) (f x) with h | h <;> simp [h]
  choose T hTsub hTsum using hrep
  let F : Fin m → Finset (Fin r → ZMod 2) := fun i => (T i).image (fun x => t0 + x)
  let E : Fin m → Finset (Fin r → ZMod 2) :=
    fun i => if (T i).card % 2 = 1 then F i else insert t0 (F i)
  have hFcard : ∀ i, (F i).card = (T i).card := fun i =>
    Finset.card_image_of_injective _ (add_right_injective t0)
  have hFsum : ∀ i, ∑ y ∈ F i, y = (T i).card • t0 + (tag i - t0) := by
    intro i
    rw [Finset.sum_image (fun x _ y _ h => add_left_cancel h), Finset.sum_add_distrib,
      Finset.sum_const, hTsum]
  have ht0F : ∀ i, t0 ∉ F i := by
    intro i h
    obtain ⟨x, hx, hx0⟩ := Finset.mem_image.1 h
    exact hne x (hTsub i hx) (by simpa using hx0)
  have hEsub : ∀ i, E i ⊆ insert t0 (bF.image (fun x => t0 + x)) := by
    intro i y hy
    have hy' : y ∈ insert t0 (F i) := by
      by_cases h : (T i).card % 2 = 1
      · simp only [E, h, ↓reduceIte] at hy; exact Finset.mem_insert_of_mem hy
      · simpa only [E, h, ↓reduceIte] using hy
    rcases Finset.mem_insert.1 hy' with h | h
    · exact Finset.mem_insert.2 (Or.inl h)
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 h
      exact Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨x, hTsub i hx, rfl⟩)
  have hU : (Finset.univ : Finset (Fin m)).biUnion E ⊆ insert t0 (bF.image (fun x => t0 + x)) :=
    Finset.biUnion_subset.2 (fun i _ => hEsub i)
  refine ⟨E, ?_, ?_, ?_⟩
  · intro i
    by_cases h : (T i).card % 2 = 1
    · simp only [E, h, ↓reduceIte]
      refine ⟨by rw [hFcard]; exact h, ?_⟩
      rw [hFsum, odd_nsmul_eq _ _ h]
      abel
    · simp only [E, h, ↓reduceIte]
      refine ⟨by rw [Finset.card_insert_of_notMem (ht0F i), hFcard]; omega, ?_⟩
      rw [Finset.sum_insert (ht0F i), hFsum, even_nsmul_eq _ _ (by omega)]
      abel
  · intro y hy
    rcases Finset.mem_insert.1 (hU hy) with h | h
    · rw [h]; exact ht0mem
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 h
      exact hentry x hx
  · have h1 := Finset.card_le_card hU
    have h2 := Finset.card_insert_le t0 (bF.image (fun x => t0 + x))
    have h3 : (bF.image (fun x => t0 + x)).card ≤ bF.card := Finset.card_image_le
    rw [hdim]
    omega

end PEqualNP.Outside.L_lib_665_aux

theorem PEqualNP.Outside.L_lib_665 : (∀ (r m : Nat), 0 < m →
  let K := ZMod 2
  let V := Fin r → K
  let dot := fun (u v : V) => ∑ j, u j * v j
  ∀ tag : Fin m → V,
    let normals := (Finset.univ : Finset V).filter (fun v =>
      ∀ i j : Fin m, dot v (tag i) = dot v (tag j))
    let moments := fun (E : Fin m → Finset V) =>
      ∀ i, (E i).card % 2 = 1 ∧ ∀ k, (∑ t ∈ E i, t k) = tag i k
    let supp := fun (E : Fin m → Finset V) => (Finset.univ : Finset (Fin m)).biUnion E
    let entries := (Finset.univ : Finset (Fin m)).image tag
    (∀ E, moments E → r+1 ≤ (supp E).card + Nat.log 2 normals.card) ∧
    ∃ E, moments E ∧ supp E ⊆ entries ∧ (supp E).card + Nat.log 2 normals.card = r+1) := by
  intro r m hm
  dsimp only
  intro tag
  obtain ⟨hcard, hdr⟩ := PEqualNP.Outside.L_lib_665_aux.normals_card tag hm
  rw [hcard, Nat.log_pow (by norm_num)]
  have hmom : ∀ E : Fin m → Finset (Fin r → ZMod 2),
      (∀ i, (E i).card % 2 = 1 ∧ ∀ k, (∑ t ∈ E i, t k) = tag i k) →
      ∀ i, (E i).card % 2 = 1 ∧ ∑ t ∈ E i, t = tag i := by
    intro E hE i
    refine ⟨(hE i).1, ?_⟩
    funext k
    rw [Finset.sum_apply]
    exact (hE i).2 k
  refine ⟨?_, ?_⟩
  · intro E hE
    have := PEqualNP.Outside.L_lib_665_aux.lower tag hm E (hmom E hE)
    omega
  · obtain ⟨E, hE, hsub, hle⟩ := PEqualNP.Outside.L_lib_665_aux.upper tag hm
    have hlow := PEqualNP.Outside.L_lib_665_aux.lower tag hm E hE
    refine ⟨E, ?_, hsub, ?_⟩
    · intro i
      refine ⟨(hE i).1, fun k => ?_⟩
      rw [← Finset.sum_apply, (hE i).2]
    · omega
