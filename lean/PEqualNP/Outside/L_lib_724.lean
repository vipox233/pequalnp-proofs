import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_724

open scoped BigOperators

def pairing {n names : ℕ} (c x : Fin names → Fin (n + 1) → ZMod 2) : ZMod 2 :=
  ∑ y : Fin names, dotProduct (c y) (x y)

lemma pairing_add_right {n names : ℕ} (c x₁ x₂ : Fin names → Fin (n + 1) → ZMod 2) :
    pairing c (x₁ + x₂) = pairing c x₁ + pairing c x₂ := by
  simp [pairing, dotProduct_add, Finset.sum_add_distrib]

lemma pairing_add_left {n names : ℕ} (c₁ c₂ x : Fin names → Fin (n + 1) → ZMod 2) :
    pairing (c₁ + c₂) x = pairing c₁ x + pairing c₂ x := by
  simp [pairing, add_dotProduct, Finset.sum_add_distrib]

lemma pairing_smul_right {n names : ℕ} (a : ZMod 2) (c x : Fin names → Fin (n + 1) → ZMod 2) :
    pairing c (a • x) = a * pairing c x := by
  simp [pairing, dotProduct_smul, Finset.mul_sum]

lemma pairing_smul_left {n names : ℕ} (a : ZMod 2) (c x : Fin names → Fin (n + 1) → ZMod 2) :
    pairing (a • c) x = a * pairing c x := by
  simp [pairing, smul_dotProduct, Finset.mul_sum]

lemma pairing_single {n names : ℕ} (c : Fin names → Fin (n + 1) → ZMod 2)
    (y : Fin names) (w : Fin (n + 1) → ZMod 2) :
    pairing c (Pi.single y w) = dotProduct (c y) w := by
  simp only [pairing]
  rw [Finset.sum_eq_single y]
  · simp
  · intro z _ hz
    simp [Pi.single_eq_of_ne hz]
  · intro hy
    exact False.elim (hy (Finset.mem_univ y))

def pairingLin {n names : ℕ} :
    (Fin names → Fin (n + 1) → ZMod 2) →ₗ[ZMod 2]
      (Fin names → Fin (n + 1) → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun c :=
    { toFun := fun x => pairing c x
      map_add' := pairing_add_right c
      map_smul' := fun a x => by simp [pairing_smul_right] }
  map_add' c₁ c₂ := by ext x; simp [pairing_add_left]
  map_smul' a c := by ext x; simp [pairing_smul_left]

lemma pairing_nondeg_left {n names : ℕ} (c : Fin names → Fin (n + 1) → ZMod 2)
    (hc : ∀ x, pairing c x = 0) : c = 0 := by
  ext y k
  have h := hc (Pi.single y (Pi.single k 1))
  rw [pairing_single] at h
  simp only [dotProduct] at h
  rw [Finset.sum_eq_single k] at h
  · simpa using h
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · intro hk
    exact False.elim (hk (Finset.mem_univ k))

lemma pairing_symm {n names : ℕ} (c x : Fin names → Fin (n + 1) → ZMod 2) :
    pairing c x = pairing x c := by
  simp only [pairing]
  apply Finset.sum_congr rfl
  intro y _
  exact dotProduct_comm (c y) (x y)

def ann {n names : ℕ} (S : Submodule (ZMod 2) (Fin names → Fin (n + 1) → ZMod 2)) :
    Submodule (ZMod 2) (Fin names → Fin (n + 1) → ZMod 2) :=
  { carrier := {c | ∀ x ∈ S, pairing c x = 0}, add_mem' := fun hc₁ hc₂ x hx => by
      rw [pairing_add_left, hc₁ x hx, hc₂ x hx, add_zero]
    zero_mem' := fun x _ => by simp [pairing]
    smul_mem' := fun a c hc x hx => by rw [pairing_smul_left, hc x hx, mul_zero] }

lemma ann_antitone {n names : ℕ}
    {S T : Submodule (ZMod 2) (Fin names → Fin (n + 1) → ZMod 2)} (h : S ≤ T) :
    ann T ≤ ann S :=
  fun _ hc x hx => hc x (h hx)

lemma le_ann_ann {n names : ℕ}
    (S : Submodule (ZMod 2) (Fin names → Fin (n + 1) → ZMod 2)) :
    S ≤ ann (ann S) := by
  intro x hx c hc
  rw [pairing_symm]
  exact hc x hx

lemma finrank_add_finrank_ann {n names : ℕ}
    (S : Submodule (ZMod 2) (Fin names → Fin (n + 1) → ZMod 2)) :
    Module.finrank (ZMod 2) S + Module.finrank (ZMod 2) (ann S) =
      Module.finrank (ZMod 2) (Fin names → Fin (n + 1) → ZMod 2) := by
  let U := Fin names → Fin (n + 1) → ZMod 2
  let f : U →ₗ[ZMod 2] Module.Dual (ZMod 2) S :=
    { toFun := fun c => (pairingLin c).domRestrict S
      map_add' := fun c₁ c₂ => by
        ext ⟨x, hx⟩
        exact pairing_add_left c₁ c₂ x
      map_smul' := fun a c => by
        ext ⟨x, hx⟩
        exact pairing_smul_left a c x }
  have hker : LinearMap.ker f = ann S := by
    ext c
    simp only [LinearMap.mem_ker, f, LinearMap.ext_iff, Subtype.forall,
      LinearMap.domRestrict_apply, LinearMap.zero_apply]
    rfl
  have hsurj : Function.Surjective f := by
    intro φ
    obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl S
    let ψ : Module.Dual (ZMod 2) U := φ.comp (Submodule.projectionOnto S Q hQ)
    have hsurj_p : Function.Surjective (pairingLin (n := n) (names := names)) := by
      rw [← LinearMap.range_eq_top]
      apply Submodule.eq_top_of_finrank_eq
      have hker_p : LinearMap.ker (pairingLin (n := n) (names := names)) = ⊥ := by
        rw [Submodule.eq_bot_iff]
        intro c hc
        apply pairing_nondeg_left
        intro x
        exact LinearMap.ext_iff.mp hc x
      have hrk_p := LinearMap.finrank_range_add_finrank_ker (pairingLin (n := n) (names := names))
      rw [hker_p, finrank_bot, add_zero] at hrk_p
      rw [hrk_p, Subspace.dual_finrank_eq]
    obtain ⟨c, hc⟩ := hsurj_p ψ
    refine ⟨c, ?_⟩
    ext ⟨x, hx⟩
    have h1 := LinearMap.ext_iff.mp hc x
    have h2 : ψ x = φ ⟨x, hx⟩ := by
      dsimp [ψ]
      congr 1
      exact Submodule.projectionOnto_apply_left hQ ⟨x, hx⟩
    simpa [f, pairingLin] using h1.trans h2
  have hrk := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hker, Subspace.dual_finrank_eq] at hrk
  exact hrk

lemma ann_ann {n names : ℕ}
    (S : Submodule (ZMod 2) (Fin names → Fin (n + 1) → ZMod 2)) :
    ann (ann S) = S := by
  apply (Submodule.eq_of_le_of_finrank_eq (le_ann_ann S) _).symm
  have h1 := finrank_add_finrank_ann S
  have h2 := finrank_add_finrank_ann (ann S)
  omega

lemma ann_sup {n names : ℕ}
    (S T : Submodule (ZMod 2) (Fin names → Fin (n + 1) → ZMod 2)) :
    ann (S ⊔ T) = ann S ⊓ ann T := by
  ext c
  simp only [ann, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_setOf_eq, Submodule.mem_inf]
  constructor
  · intro h
    exact ⟨fun a ha => h a (Submodule.mem_sup_left ha),
           fun b hb => h b (Submodule.mem_sup_right hb)⟩
  · rintro ⟨hcs, hct⟩ x hx
    rcases Submodule.mem_sup.mp hx with ⟨a, ha, b, hb, rfl⟩
    rw [pairing_add_right, hcs a ha, hct b hb, add_zero]

lemma ann_inf {n names : ℕ}
    (S T : Submodule (ZMod 2) (Fin names → Fin (n + 1) → ZMod 2)) :
    ann (S ⊓ T) = ann S ⊔ ann T := by
  have hle : ann S ⊔ ann T ≤ ann (S ⊓ T) :=
    sup_le (ann_antitone inf_le_left) (ann_antitone inf_le_right)
  apply (Submodule.eq_of_le_of_finrank_eq hle _).symm
  have h1 := finrank_add_finrank_ann (S ⊓ T)
  have h2 := finrank_add_finrank_ann S
  have h3 := finrank_add_finrank_ann T
  have h4 := Submodule.finrank_sup_add_finrank_inf_eq S T
  have h5 := Submodule.finrank_sup_add_finrank_inf_eq (ann S) (ann T)
  have h6 := finrank_add_finrank_ann (S ⊔ T)
  rw [ann_sup] at h6
  omega

lemma neg_eq_self_zmod2 {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (v : V) : -v = v := by
  rw [← neg_one_smul (ZMod 2) v]
  have : (-1 : ZMod 2) = 1 := by decide
  rw [this, one_smul]

lemma two_proper_subspaces_ne_union {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {A B₀ B₁ : Submodule (ZMod 2) V} (h₀ : B₀ < A) (h₁ : B₁ < A) :
    ∃ x ∈ A, x ∉ B₀ ∧ x ∉ B₁ := by
  by_contra h
  push_neg at h
  obtain ⟨x, hxA, hx0⟩ := SetLike.exists_of_lt h₀
  obtain ⟨y, hyA, hy1⟩ := SetLike.exists_of_lt h₁
  have hx1 : x ∈ B₁ := h x hxA hx0
  by_cases hy0 : y ∈ B₀
  · have hxyA : x + y ∈ A := A.add_mem hxA hyA
    have hxy0 : x + y ∉ B₀ := fun hc => hx0 (by simpa using B₀.sub_mem hc hy0)
    have hxy1 : x + y ∈ B₁ := h (x + y) hxyA hxy0
    exact hy1 (by simpa using B₁.sub_mem hxy1 hx1)
  · exact hy0 (by have := h y hyA; tauto)

lemma three_proper_cover_structure {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {A : Submodule (ZMod 2) V} {B : Fin 3 → Submodule (ZMod 2) V}
    (hB_le : ∀ i, B i < A)
    (hcov : ∀ x ∈ A, ∃ i, x ∈ B i) :
    ∃ (J : Submodule (ZMod 2) V) (e₀ e₁ : V),
      e₀ ∈ A ∧ e₁ ∈ A ∧ e₀ ∉ J ∧ e₁ ∉ J ∧ (e₀ + e₁) ∉ J ∧
      B 0 = J ⊔ Submodule.span (ZMod 2) {e₀} ∧
      B 1 = J ⊔ Submodule.span (ZMod 2) {e₁} ∧
      B 2 = J ⊔ Submodule.span (ZMod 2) {e₀ + e₁} ∧
      A = B 0 ⊔ B 1 ∧
      J = B 0 ⊓ B 1 := by
  obtain ⟨e₀, he0A, he01, he02⟩ := two_proper_subspaces_ne_union (hB_le 1) (hB_le 2)
  obtain ⟨e₁, he1A, he10, he12⟩ := two_proper_subspaces_ne_union (hB_le 0) (hB_le 2)
  obtain ⟨e₂, he2A, he20, he21⟩ := two_proper_subspaces_ne_union (hB_le 0) (hB_le 1)
  have he00 : e₀ ∈ B 0 := by rcases hcov e₀ he0A with ⟨i, hi⟩; fin_cases i <;> tauto
  have he11 : e₁ ∈ B 1 := by rcases hcov e₁ he1A with ⟨i, hi⟩; fin_cases i <;> tauto
  have he22 : e₂ ∈ B 2 := by rcases hcov e₂ he2A with ⟨i, hi⟩; fin_cases i <;> tauto
  have h01_in_2 : e₀ + e₁ ∈ B 2 := by
    rcases hcov (e₀ + e₁) (A.add_mem he0A he1A) with ⟨i, hi⟩
    fin_cases i
    · exact False.elim (he10 (by simpa using (B 0).sub_mem hi he00))
    · exact False.elim (he01 (by simpa using (B 1).sub_mem hi he11))
    · exact hi
  let J := B 0 ⊓ B 1 ⊓ B 2
  have hJ01 : B 0 ⊓ B 1 ≤ B 2 := by
    intro x ⟨hx0, hx1⟩
    rcases hcov (x + e₂) (A.add_mem ((hB_le 0).le hx0) he2A) with ⟨i, hi⟩
    fin_cases i
    · exact False.elim (he20 (by simpa using (B 0).sub_mem hi hx0))
    · exact False.elim (he21 (by simpa using (B 1).sub_mem hi hx1))
    · exact by simpa using (B 2).sub_mem hi he22
  have hJ02 : B 0 ⊓ B 2 ≤ B 1 := by
    intro x ⟨hx0, hx2⟩
    rcases hcov (x + e₁) (A.add_mem ((hB_le 0).le hx0) he1A) with ⟨i, hi⟩
    fin_cases i
    · exact False.elim (he10 (by simpa using (B 0).sub_mem hi hx0))
    · exact by simpa using (B 1).sub_mem hi he11
    · exact False.elim (he12 (by simpa using (B 2).sub_mem hi hx2))
  have hJ12 : B 1 ⊓ B 2 ≤ B 0 := by
    intro x ⟨hx1, hx2⟩
    rcases hcov (x + e₀) (A.add_mem ((hB_le 1).le hx1) he0A) with ⟨i, hi⟩
    fin_cases i
    · exact by simpa using (B 0).sub_mem hi he00
    · exact False.elim (he01 (by simpa using (B 1).sub_mem hi hx1))
    · exact False.elim (he02 (by simpa using (B 2).sub_mem hi hx2))
  have hJ_eq01 : J = B 0 ⊓ B 1 := le_antisymm inf_le_left (le_inf le_rfl hJ01)
  have hB0_eq : B 0 = J ⊔ Submodule.span (ZMod 2) {e₀} := by
    apply le_antisymm
    · intro x hx0
      by_cases hx1 : x ∈ B 1
      · exact Submodule.mem_sup_left ⟨⟨hx0, hx1⟩, hJ01 ⟨hx0, hx1⟩⟩
      · rcases hcov (x + e₁) (A.add_mem ((hB_le 0).le hx0) he1A) with ⟨i, hi⟩
        fin_cases i
        · exact False.elim (he10 (by simpa using (B 0).sub_mem hi hx0))
        · exact False.elim (hx1 (by simpa using (B 1).sub_mem hi he11))
        · have hxe0_2 : x + e₀ ∈ B 2 := by
            have hd := (B 2).sub_mem hi h01_in_2
            have heq : (x + e₁) - (e₀ + e₁) = x + e₀ := by
              calc (x + e₁) - (e₀ + e₁) = x - e₀ := by abel
                _ = x + (-e₀) := sub_eq_add_neg x e₀
                _ = x + e₀ := by rw [neg_eq_self_zmod2]
            rwa [heq] at hd
          have hxe0_0 : x + e₀ ∈ B 0 := (B 0).add_mem hx0 he00
          have hxe0_1 : x + e₀ ∈ B 1 := hJ02 ⟨hxe0_0, hxe0_2⟩
          have hxe0_J : x + e₀ ∈ J := ⟨⟨hxe0_0, hxe0_1⟩, hxe0_2⟩
          have hx_eq : x = (x + e₀) + e₀ := by
            calc x = (x + e₀) - e₀ := by abel
              _ = (x + e₀) + (-e₀) := sub_eq_add_neg _ _
              _ = (x + e₀) + e₀ := by rw [neg_eq_self_zmod2]
          rw [hx_eq]
          exact Submodule.add_mem_sup hxe0_J (Submodule.subset_span (Set.mem_singleton e₀))
    · refine sup_le (inf_le_left.trans inf_le_left) ?_
      rw [Submodule.span_singleton_le_iff_mem]
      exact he00
  have hB1_eq : B 1 = J ⊔ Submodule.span (ZMod 2) {e₁} := by
    apply le_antisymm
    · intro x hx1
      by_cases hx0 : x ∈ B 0
      · exact Submodule.mem_sup_left ⟨⟨hx0, hx1⟩, hJ01 ⟨hx0, hx1⟩⟩
      · rcases hcov (x + e₀) (A.add_mem ((hB_le 1).le hx1) he0A) with ⟨i, hi⟩
        fin_cases i
        · exact False.elim (hx0 (by simpa using (B 0).sub_mem hi he00))
        · exact False.elim (he01 (by simpa using (B 1).sub_mem hi hx1))
        · have hxe1_2 : x + e₁ ∈ B 2 := by
            have hd := (B 2).sub_mem hi h01_in_2
            have heq : (x + e₀) - (e₀ + e₁) = x + e₁ := by
              calc (x + e₀) - (e₀ + e₁) = x - e₁ := by abel
                _ = x + (-e₁) := sub_eq_add_neg x e₁
                _ = x + e₁ := by rw [neg_eq_self_zmod2]
            rwa [heq] at hd
          have hxe1_1 : x + e₁ ∈ B 1 := (B 1).add_mem hx1 he11
          have hxe1_0 : x + e₁ ∈ B 0 := hJ12 ⟨hxe1_1, hxe1_2⟩
          have hx_eq : x = (x + e₁) + e₁ := by
            calc x = (x + e₁) - e₁ := by abel
              _ = (x + e₁) + (-e₁) := sub_eq_add_neg _ _
              _ = (x + e₁) + e₁ := by rw [neg_eq_self_zmod2]
          rw [hx_eq]
          exact Submodule.add_mem_sup ⟨⟨hxe1_0, hxe1_1⟩, hxe1_2⟩
            (Submodule.subset_span (Set.mem_singleton e₁))
    · refine sup_le (inf_le_left.trans inf_le_right) ?_
      rw [Submodule.span_singleton_le_iff_mem]
      exact he11
  have hB2_eq : B 2 = J ⊔ Submodule.span (ZMod 2) {e₀ + e₁} := by
    apply le_antisymm
    · intro x hx2
      by_cases hx0 : x ∈ B 0
      · exact Submodule.mem_sup_left ⟨⟨hx0, hJ02 ⟨hx0, hx2⟩⟩, hx2⟩
      · rcases hcov (x + e₀) (A.add_mem ((hB_le 2).le hx2) he0A) with ⟨i, hi⟩
        fin_cases i
        · exact False.elim (hx0 (by simpa using (B 0).sub_mem hi he00))
        · have hx01_2 : x + (e₀ + e₁) ∈ B 2 := (B 2).add_mem hx2 h01_in_2
          have hx01_1 : x + (e₀ + e₁) ∈ B 1 := by
            have ha := (B 1).add_mem hi he11
            rwa [add_assoc] at ha
          have hx01_0 : x + (e₀ + e₁) ∈ B 0 := hJ12 ⟨hx01_1, hx01_2⟩
          have hx_eq : x = (x + (e₀ + e₁)) + (e₀ + e₁) := by
            calc x = (x + (e₀ + e₁)) - (e₀ + e₁) := by abel
              _ = (x + (e₀ + e₁)) + (-(e₀ + e₁)) := sub_eq_add_neg _ _
              _ = (x + (e₀ + e₁)) + (e₀ + e₁) := by rw [neg_eq_self_zmod2]
          rw [hx_eq]
          exact Submodule.add_mem_sup ⟨⟨hx01_0, hx01_1⟩, hx01_2⟩
            (Submodule.subset_span (Set.mem_singleton (e₀ + e₁)))
        · exact False.elim (he02 (by simpa using (B 2).sub_mem hi hx2))
    · refine sup_le inf_le_right ?_
      rw [Submodule.span_singleton_le_iff_mem]
      exact h01_in_2
  have hA_eq : A = B 0 ⊔ B 1 := by
    apply le_antisymm
    · intro x hxA
      rcases hcov x hxA with ⟨i, hi⟩
      fin_cases i
      · exact Submodule.mem_sup_left hi
      · exact Submodule.mem_sup_right hi
      · dsimp at hi
        rw [hB2_eq] at hi
        rcases Submodule.mem_sup.mp hi with ⟨j, hj, k, hk, rfl⟩
        rcases Submodule.mem_span_singleton.mp hk with ⟨a, rfl⟩
        have hj0 : j ∈ B 0 := hj.1.1
        have he0' : a • e₀ ∈ B 0 := (B 0).smul_mem a he00
        have he1' : a • e₁ ∈ B 1 := (B 1).smul_mem a he11
        have hsum : j + a • (e₀ + e₁) = (j + a • e₀) + a • e₁ := by
          rw [smul_add, add_assoc]
        rw [hsum]
        exact Submodule.add_mem_sup ((B 0).add_mem hj0 he0') he1'
    · exact sup_le (hB_le 0).le (hB_le 1).le
  exact ⟨J, e₀, e₁, he0A, he1A, fun h => he01 h.1.2, fun h => he10 h.1.1,
    fun h => he10 (by simpa using (B 0).sub_mem h.1.1 he00), hB0_eq, hB1_eq, hB2_eq, hA_eq, hJ_eq01⟩

lemma finrank_sup_span_eq {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    {S : Submodule (ZMod 2) V} {x : V} (hx : x ∉ S) :
    Module.finrank (ZMod 2) ↥(S ⊔ Submodule.span (ZMod 2) {x}) =
      Module.finrank (ZMod 2) S + 1 := by
  have hdisj : Disjoint S (Submodule.span (ZMod 2) {x}) := by
    rw [Submodule.disjoint_span_singleton]
    intro hmem
    exact False.elim (hx hmem)
  have h := Submodule.finrank_sup_add_finrank_inf_eq S (Submodule.span (ZMod 2) {x})
  rw [hdisj.eq_bot] at h
  simp only [finrank_bot, add_zero] at h
  have hsp : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {x}) = 1 :=
    finrank_span_singleton (fun h0 => hx (by subst h0; exact S.zero_mem))
  omega

lemma eq_sup_span_of_lt_finrank {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Module.Finite (ZMod 2) V] {S T : Submodule (ZMod 2) V} (hST : S ≤ T)
    (hfin : Module.finrank (ZMod 2) T = Module.finrank (ZMod 2) S + 1)
    {u : V} (huT : u ∈ T) (huS : u ∉ S) :
    T = S ⊔ Submodule.span (ZMod 2) {u} := by
  apply (Submodule.eq_of_le_of_finrank_eq _ _).symm
  · exact sup_le hST (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr huT))
  · rw [finrank_sup_span_eq huS, hfin]

lemma dot_eq_zero_of_mem_span {n : ℕ} {S : Set (Fin (n + 1) → ZMod 2)}
    {c : Fin (n + 1) → ZMod 2} (hc : ∀ w ∈ S, dotProduct c w = 0)
    {x : Fin (n + 1) → ZMod 2} (hx : x ∈ Submodule.span (ZMod 2) S) :
    dotProduct c x = 0 := by
  induction hx using Submodule.span_induction with
  | mem w hw => exact hc w hw
  | zero => simp
  | add u v _ _ hu hv => rw [dotProduct_add, hu, hv, add_zero]
  | smul a u _ hu => rw [dotProduct_smul, hu]; simp

end PEqualNP.Outside.L_lib_724

theorem PEqualNP.Outside.L_lib_724 : (∀ (n names : Nat),
  let V := Fin n → ZMod 2
  let W := Fin (n+1) → ZMod 2
  let E := Fin names × V
  let lift := fun p : E => Fin.cons (1 : ZMod 2) p.2
  let spanAt := fun (cell : Finset E) (y : Fin names) =>
    Submodule.span (ZMod 2) (((cell.filter (fun p => p.1 = y)).image lift : Finset W) : Set W)
  ∀ (negative : Finset E) (positive : Fin 3 → Finset E),
    let H := spanAt negative
    let G := fun (i : Fin 3) (y : Fin names) => H y ⊔ spanAt (positive i) y
    let line := fun (y : Fin names) (x : W) => H y ⊔ Submodule.span (ZMod 2) ({x} : Set W)
    let exact := ∃ coeff : Fin names → W,
      (∀ p ∈ negative, dotProduct (coeff p.1) (lift p) = 0) ∧
      (∀ i : Fin 3, ∃ p ∈ positive i, dotProduct (coeff p.1) (lift p) = 1)
    (¬exact) ↔ ((∃ i : Fin 3, ∀ y : Fin names, G i y = H y) ∨
      ∃ (y : Fin names) (a b : W), a ∉ H y ∧ b ∉ H y ∧ (a+b) ∉ H y ∧
        (∀ (i : Fin 3) (z : Fin names), z ≠ y → G i z = H z) ∧
        G 0 y = line y a ∧ G 1 y = line y b ∧ G 2 y = line y (a+b))) := by
  intro n names V W E lift spanAt negative positive H G line exact
  let U := Fin names → W
  let Htot : Submodule (ZMod 2) U := Submodule.pi Set.univ (fun y => H y)
  let Gtot : Fin 3 → Submodule (ZMod 2) U := fun i => Submodule.pi Set.univ (fun y => G i y)
  let A := PEqualNP.Outside.L_lib_724.ann Htot
  let B : Fin 3 → Submodule (ZMod 2) U := fun i => PEqualNP.Outside.L_lib_724.ann (Gtot i)
  have hH_le_G : ∀ i, Htot ≤ Gtot i := by
    intro i x hx y hy
    exact Submodule.mem_sup_left (hx y hy)
  have hB_le_A : ∀ i, B i ≤ A := fun i => PEqualNP.Outside.L_lib_724.ann_antitone (hH_le_G i)
  have hmem_ann_span : ∀ (cell : Finset E) (c : U),
      (∀ x ∈ Submodule.pi Set.univ (fun y => spanAt cell y),
        PEqualNP.Outside.L_lib_724.pairing c x = 0) ↔
      (∀ p ∈ cell, dotProduct (c p.1) (lift p) = 0) := by
    intro cell c
    constructor
    · intro h p hp
      have hx : Pi.single p.1 (lift p) ∈ Submodule.pi Set.univ (fun y => spanAt cell y) := by
        intro y _
        by_cases hy : y = p.1
        · subst hy
          rw [Pi.single_eq_same]
          apply Submodule.subset_span
          simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_filter]
          exact ⟨p, ⟨hp, rfl⟩, rfl⟩
        · rw [Pi.single_eq_of_ne hy]
          exact (spanAt cell y).zero_mem
      have hp0 := h _ hx
      rwa [PEqualNP.Outside.L_lib_724.pairing_single] at hp0
    · intro h x hx
      simp only [PEqualNP.Outside.L_lib_724.pairing]
      apply Finset.sum_eq_zero
      intro y _
      have hy := hx y (Set.mem_univ y)
      apply PEqualNP.Outside.L_lib_724.dot_eq_zero_of_mem_span _ hy
      intro w hw
      simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_filter] at hw
      rcases hw with ⟨p, ⟨hp, rfl⟩, rfl⟩
      exact h p hp
  have hmem_A : ∀ c : U, c ∈ A ↔ (∀ p ∈ negative, dotProduct (c p.1) (lift p) = 0) :=
    fun c => hmem_ann_span negative c
  have hmem_B : ∀ (i : Fin 3) (c : U), c ∈ A →
      (c ∈ B i ↔ ∀ p ∈ positive i, dotProduct (c p.1) (lift p) = 0) := by
    intro i c hcA
    constructor
    · intro hcB p hp
      have hx : Pi.single p.1 (lift p) ∈ Gtot i := by
        intro y _
        by_cases hy : y = p.1
        · subst hy
          rw [Pi.single_eq_same]
          apply Submodule.mem_sup_right
          apply Submodule.subset_span
          simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_filter]
          exact ⟨p, ⟨hp, rfl⟩, rfl⟩
        · rw [Pi.single_eq_of_ne hy]
          exact (G i y).zero_mem
      have hp0 := hcB _ hx
      rwa [PEqualNP.Outside.L_lib_724.pairing_single] at hp0
    · intro hpos x hx
      simp only [PEqualNP.Outside.L_lib_724.pairing]
      apply Finset.sum_eq_zero
      intro y _
      have hy : x y ∈ H y ⊔ spanAt (positive i) y := hx y (Set.mem_univ y)
      rcases Submodule.mem_sup.mp hy with ⟨h1, hh1, h2, hh2, hsum⟩
      rw [← hsum, dotProduct_add]
      have hdot1 : dotProduct (c y) h1 = 0 := by
        have hx1 : Pi.single y h1 ∈ Htot := by
          intro z _
          by_cases hz : z = y
          · subst hz; simpa using hh1
          · simp [Pi.single_eq_of_ne hz]
        have := hcA _ hx1
        rwa [PEqualNP.Outside.L_lib_724.pairing_single] at this
      have hdot2 : dotProduct (c y) h2 = 0 := by
        have hx2 : Pi.single y h2 ∈ Submodule.pi Set.univ (fun z => spanAt (positive i) z) := by
          intro z _
          by_cases hz : z = y
          · subst hz; simpa using hh2
          · simp [Pi.single_eq_of_ne hz]
        have := (hmem_ann_span (positive i) c).mpr hpos _ hx2
        rwa [PEqualNP.Outside.L_lib_724.pairing_single] at this
      rw [hdot1, hdot2, add_zero]
  have hexact_iff : exact ↔ ∃ c ∈ A, ∀ i : Fin 3, c ∉ B i := by
    constructor
    · rintro ⟨c, hneg, hpos⟩
      refine ⟨c, (hmem_A c).mpr hneg, fun i hi => ?_⟩
      rcases hpos i with ⟨p, hp, hp1⟩
      have hp0 := (hmem_B i c ((hmem_A c).mpr hneg)).mp hi p hp
      rw [hp1] at hp0
      exact one_ne_zero hp0
    · rintro ⟨c, hcA, hcB⟩
      refine ⟨c, (hmem_A c).mp hcA, fun i => ?_⟩
      by_contra hnone
      push_neg at hnone
      have h0 : ∀ p ∈ positive i, dotProduct (c p.1) (lift p) = 0 := by
        intro p hp
        have hne : dotProduct (c p.1) (lift p) ≠ 1 := hnone p hp
        have hz : ∀ z : ZMod 2, z ≠ 1 → z = 0 := by decide
        exact hz _ hne
      exact hcB i ((hmem_B i c hcA).mpr h0)
  have hnot_exact_iff : (¬exact) ↔ (∀ c ∈ A, ∃ i : Fin 3, c ∈ B i) := by
    rw [hexact_iff]
    push_neg
    rfl
  rw [hnot_exact_iff]
  constructor
  · intro hcov
    by_cases htop : ∃ i : Fin 3, B i = A
    · left
      rcases htop with ⟨i, hi⟩
      refine ⟨i, fun y => ?_⟩
      have hGeq : Gtot i = Htot := by
        rw [← PEqualNP.Outside.L_lib_724.ann_ann (Gtot i),
            ← PEqualNP.Outside.L_lib_724.ann_ann Htot]
        exact congrArg PEqualNP.Outside.L_lib_724.ann hi
      apply le_antisymm _ (fun w hw => Submodule.mem_sup_left hw)
      intro w hw
      have hmem : Pi.single y w ∈ Gtot i := by
        intro z _
        by_cases hz : z = y
        · subst hz; simpa using hw
        · simp [Pi.single_eq_of_ne hz]
      rw [hGeq] at hmem
      simpa using hmem y (Set.mem_univ y)
    · right
      push_neg at htop
      have hB_lt : ∀ i, B i < A := fun i => lt_of_le_of_ne (hB_le_A i) (htop i)
      obtain ⟨J, e₀, e₁, he0A, he1A, he0J, he1J, he01J, hB0, hB1, hB2, hA_eq, hJ_eq⟩ :=
        PEqualNP.Outside.L_lib_724.three_proper_cover_structure hB_lt hcov
      let C : Fin 3 → Submodule (ZMod 2) U := Gtot
      have hC_eq_ann : ∀ i, C i = PEqualNP.Outside.L_lib_724.ann (B i) :=
        fun i => (PEqualNP.Outside.L_lib_724.ann_ann (Gtot i)).symm
      have hH_eq_ann : Htot = PEqualNP.Outside.L_lib_724.ann A :=
        (PEqualNP.Outside.L_lib_724.ann_ann Htot).symm
      have hfin_B0 : Module.finrank (ZMod 2) (B 0) = Module.finrank (ZMod 2) J + 1 := by
        rw [hB0]; exact PEqualNP.Outside.L_lib_724.finrank_sup_span_eq he0J
      have hfin_B1 : Module.finrank (ZMod 2) (B 1) = Module.finrank (ZMod 2) J + 1 := by
        rw [hB1]; exact PEqualNP.Outside.L_lib_724.finrank_sup_span_eq he1J
      have hfin_B2 : Module.finrank (ZMod 2) (B 2) = Module.finrank (ZMod 2) J + 1 := by
        rw [hB2]; exact PEqualNP.Outside.L_lib_724.finrank_sup_span_eq he01J
      have hfin_A : Module.finrank (ZMod 2) A = Module.finrank (ZMod 2) J + 2 := by
        have h := Submodule.finrank_sup_add_finrank_inf_eq (B 0) (B 1)
        rw [← hA_eq, ← hJ_eq, hfin_B0, hfin_B1] at h
        linarith
      have hfin_C : ∀ i, Module.finrank (ZMod 2) (C i) = Module.finrank (ZMod 2) Htot + 1 := by
        intro i
        have ha := PEqualNP.Outside.L_lib_724.finrank_add_finrank_ann Htot
        change Module.finrank (ZMod 2) Htot + Module.finrank (ZMod 2) A = _ at ha
        fin_cases i
        · have hc0 := PEqualNP.Outside.L_lib_724.finrank_add_finrank_ann (B 0)
          rw [← hC_eq_ann 0] at hc0
          have heq : Module.finrank (ZMod 2) Htot + Module.finrank (ZMod 2) A =
              Module.finrank (ZMod 2) (B 0) + Module.finrank (ZMod 2) (C 0) := ha.trans hc0.symm
          rw [hfin_A, hfin_B0] at heq
          dsimp; omega
        · have hc1 := PEqualNP.Outside.L_lib_724.finrank_add_finrank_ann (B 1)
          rw [← hC_eq_ann 1] at hc1
          have heq : Module.finrank (ZMod 2) Htot + Module.finrank (ZMod 2) A =
              Module.finrank (ZMod 2) (B 1) + Module.finrank (ZMod 2) (C 1) := ha.trans hc1.symm
          rw [hfin_A, hfin_B1] at heq
          dsimp; omega
        · have hc2 := PEqualNP.Outside.L_lib_724.finrank_add_finrank_ann (B 2)
          rw [← hC_eq_ann 2] at hc2
          have heq : Module.finrank (ZMod 2) Htot + Module.finrank (ZMod 2) A =
              Module.finrank (ZMod 2) (B 2) + Module.finrank (ZMod 2) (C 2) := ha.trans hc2.symm
          rw [hfin_A, hfin_B2] at heq
          dsimp; omega
      have hH_lt_C : ∀ i, Htot < C i := by
        intro i
        apply lt_of_le_of_ne (hH_le_G i)
        intro h
        change Htot = C i at h
        have hfc := hfin_C i
        rw [← h] at hfc
        omega
      obtain ⟨u₀, hu0C0, hu0H⟩ := SetLike.exists_of_lt (hH_lt_C 0)
      obtain ⟨u₁, hu1C1, hu1H⟩ := SetLike.exists_of_lt (hH_lt_C 1)
      have hC01_inf : C 0 ⊓ C 1 = Htot := by
        rw [hC_eq_ann 0, hC_eq_ann 1, ← PEqualNP.Outside.L_lib_724.ann_sup, ← hA_eq, ← hH_eq_ann]
      have hu0_not_C1 : u₀ ∉ C 1 := fun h => hu0H (hC01_inf ▸ ⟨hu0C0, h⟩)
      have hu1_not_C0 : u₁ ∉ C 0 := fun h => hu1H (hC01_inf ▸ ⟨h, hu1C1⟩)
      have hu01_not_H : u₀ + u₁ ∉ Htot := fun h =>
        hu0_not_C1 (by
          have := (C 1).sub_mem (hH_le_G 1 h) hu1C1
          simpa using this)
      have hu01_C2 : u₀ + u₁ ∈ C 2 := by
        rw [hC_eq_ann 2]
        intro c hc
        rw [hB2] at hc
        rcases Submodule.mem_sup.mp hc with ⟨j, hj, k, hk, rfl⟩
        rcases Submodule.mem_span_singleton.mp hk with ⟨α, rfl⟩
        have hj0 : j ∈ B 0 := (hJ_eq ▸ hj).1
        have hj1 : j ∈ B 1 := (hJ_eq ▸ hj).2
        have hju0 : PEqualNP.Outside.L_lib_724.pairing j u₀ = 0 := by
          rw [PEqualNP.Outside.L_lib_724.pairing_symm]
          exact (hC_eq_ann 0 ▸ hu0C0) j hj0
        have hju1 : PEqualNP.Outside.L_lib_724.pairing j u₁ = 0 := by
          rw [PEqualNP.Outside.L_lib_724.pairing_symm]
          exact (hC_eq_ann 1 ▸ hu1C1) j hj1
        have he0u0 : PEqualNP.Outside.L_lib_724.pairing e₀ u₀ = 0 := by
          rw [PEqualNP.Outside.L_lib_724.pairing_symm]
          exact (hC_eq_ann 0 ▸ hu0C0) e₀ (hB0 ▸ Submodule.mem_sup_right (Submodule.subset_span rfl))
        have he1u1 : PEqualNP.Outside.L_lib_724.pairing e₁ u₁ = 0 := by
          rw [PEqualNP.Outside.L_lib_724.pairing_symm]
          exact (hC_eq_ann 1 ▸ hu1C1) e₁ (hB1 ▸ Submodule.mem_sup_right (Submodule.subset_span rfl))
        have he1u0 : PEqualNP.Outside.L_lib_724.pairing e₁ u₀ = 1 := by
          have hne : PEqualNP.Outside.L_lib_724.pairing e₁ u₀ ≠ 0 := by
            intro h0
            apply hu0_not_C1
            rw [hC_eq_ann 1, hB1]
            intro x hx
            rcases Submodule.mem_sup.mp hx with ⟨j', hj', k', hk', rfl⟩
            rcases Submodule.mem_span_singleton.mp hk' with ⟨β, rfl⟩
            rw [PEqualNP.Outside.L_lib_724.pairing_add_right,
                PEqualNP.Outside.L_lib_724.pairing_smul_right]
            have hjp : PEqualNP.Outside.L_lib_724.pairing j' u₀ = 0 := by
              rw [PEqualNP.Outside.L_lib_724.pairing_symm]
              exact (hC_eq_ann 0 ▸ hu0C0) j' (hJ_eq ▸ hj').1
            rw [PEqualNP.Outside.L_lib_724.pairing_symm u₀ j', hjp,
                PEqualNP.Outside.L_lib_724.pairing_symm u₀ e₁, h0, mul_zero, add_zero]
          have hz1 : ∀ z : ZMod 2, z ≠ 0 → z = 1 := by decide
          exact hz1 _ hne
        have he0u1 : PEqualNP.Outside.L_lib_724.pairing e₀ u₁ = 1 := by
          have hne : PEqualNP.Outside.L_lib_724.pairing e₀ u₁ ≠ 0 := by
            intro h0
            apply hu1_not_C0
            rw [hC_eq_ann 0, hB0]
            intro x hx
            rcases Submodule.mem_sup.mp hx with ⟨j', hj', k', hk', rfl⟩
            rcases Submodule.mem_span_singleton.mp hk' with ⟨β, rfl⟩
            rw [PEqualNP.Outside.L_lib_724.pairing_add_right,
                PEqualNP.Outside.L_lib_724.pairing_smul_right]
            have hjp : PEqualNP.Outside.L_lib_724.pairing j' u₁ = 0 := by
              rw [PEqualNP.Outside.L_lib_724.pairing_symm]
              exact (hC_eq_ann 1 ▸ hu1C1) j' (hJ_eq ▸ hj').2
            rw [PEqualNP.Outside.L_lib_724.pairing_symm u₁ j', hjp,
                PEqualNP.Outside.L_lib_724.pairing_symm u₁ e₀, h0, mul_zero, add_zero]
          have hz1 : ∀ z : ZMod 2, z ≠ 0 → z = 1 := by decide
          exact hz1 _ hne
        rw [PEqualNP.Outside.L_lib_724.pairing_add_left,
            PEqualNP.Outside.L_lib_724.pairing_symm u₀,
            PEqualNP.Outside.L_lib_724.pairing_symm u₁]
        rw [PEqualNP.Outside.L_lib_724.pairing_add_left,
            PEqualNP.Outside.L_lib_724.pairing_add_left,
            PEqualNP.Outside.L_lib_724.pairing_smul_left,
            PEqualNP.Outside.L_lib_724.pairing_smul_left,
            PEqualNP.Outside.L_lib_724.pairing_add_left,
            PEqualNP.Outside.L_lib_724.pairing_add_left]
        rw [hju0, hju1, he0u0, he1u1, he1u0, he0u1]
        fin_cases α <;> decide
      have hsingle_coord : ∀ i : Fin 3, ∃ y : Fin names,
          (∀ z : Fin names, z ≠ y → G i z = H z) ∧
          ∃ w : W, w ∉ H y ∧ G i y = line y w := by
        intro i
        have hex : ∃ y : Fin names, G i y ≠ H y := by
          by_contra hall
          push_neg at hall
          have hCi_eq_H : C i = Htot := by
            ext x
            simp [C, Gtot, Htot, hall]
          have hlt := hH_lt_C i
          rw [hCi_eq_H] at hlt
          exact lt_irrefl _ hlt
        obtain ⟨y, hy⟩ := hex
        have hHy_lt : H y < G i y := lt_of_le_of_ne (fun w hw => Submodule.mem_sup_left hw) hy.symm
        obtain ⟨w, hwG, hwH⟩ := SetLike.exists_of_lt hHy_lt
        have hsingle_in : Pi.single y w ∈ C i := by
          intro z _
          by_cases hz : z = y
          · subst hz; simpa using hwG
          · simp [Pi.single_eq_of_ne hz]
        have hsingle_not : Pi.single y w ∉ Htot := fun h => hwH (by simpa using h y (Set.mem_univ y))
        have hCi_eq : C i = Htot ⊔ Submodule.span (ZMod 2) {Pi.single y w} :=
          PEqualNP.Outside.L_lib_724.eq_sup_span_of_lt_finrank (hH_le_G i) (hfin_C i) hsingle_in hsingle_not
        refine ⟨y, fun z hzy => ?_, w, hwH, ?_⟩
        · apply le_antisymm _ (fun v hv => Submodule.mem_sup_left hv)
          intro v hv
          have hvC : Pi.single z v ∈ C i := by
            intro z' _
            by_cases hz' : z' = z
            · subst hz'; simpa using hv
            · simp [Pi.single_eq_of_ne hz']
          rw [hCi_eq] at hvC
          rcases Submodule.mem_sup.mp hvC with ⟨h1, hh1, k, hk, hsum⟩
          rcases Submodule.mem_span_singleton.mp hk with ⟨α, rfl⟩
          have hvy := congr_fun hsum y
          have hvz := congr_fun hsum z
          simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hzy, smul_zero, add_zero] at hvz
          rw [Pi.single_eq_same] at hvz
          rw [← hvz]
          exact hh1 z (Set.mem_univ z)
        · apply le_antisymm _ (sup_le (fun v hv => Submodule.mem_sup_left hv)
            (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hwG)))
          intro v hv
          have hvC : Pi.single y v ∈ C i := by
            intro z _
            by_cases hz : z = y
            · subst hz; simpa using hv
            · simp [Pi.single_eq_of_ne hz]
          rw [hCi_eq] at hvC
          rcases Submodule.mem_sup.mp hvC with ⟨h1, hh1, k, hk, hsum⟩
          rcases Submodule.mem_span_singleton.mp hk with ⟨α, rfl⟩
          have hvy := congr_fun hsum y
          simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same] at hvy
          rw [← hvy]
          exact Submodule.add_mem_sup (hh1 y (Set.mem_univ y))
            (Submodule.smul_mem _ α (Submodule.subset_span rfl))
      obtain ⟨y₀, hy0_other, a, haH, hG0y⟩ := hsingle_coord 0
      obtain ⟨y₁, hy1_other, b, hbH, hG1y⟩ := hsingle_coord 1
      obtain ⟨y₂, hy2_other, c₂, hc2H, hG2y⟩ := hsingle_coord 2
      have hy01 : y₀ = y₁ := by
        by_contra hne
        have hu0y0 : u₀ y₀ ∉ H y₀ := by
          intro h0
          apply hu0H
          intro z _
          dsimp
          by_cases hz : z = y₀
          · subst hz; exact h0
          · rw [← hy0_other z hz]; exact hu0C0 z (Set.mem_univ z)
        have hu1y1 : u₁ y₁ ∉ H y₁ := by
          intro h1
          apply hu1H
          intro z _
          dsimp
          by_cases hz : z = y₁
          · subst hz; exact h1
          · rw [← hy1_other z hz]; exact hu1C1 z (Set.mem_univ z)
        have hu0y1 : u₀ y₁ ∈ H y₁ := by
          rw [← hy0_other y₁ (Ne.symm hne)]; exact hu0C0 y₁ (Set.mem_univ y₁)
        have hu1y0 : u₁ y₀ ∈ H y₀ := by
          rw [← hy1_other y₀ hne]; exact hu1C1 y₀ (Set.mem_univ y₀)
        have hsum_y0 : (u₀ + u₁) y₀ ∉ H y₀ := fun h =>
          hu0y0 (by
            have hm := (H y₀).sub_mem h hu1y0
            have heq : (u₀ + u₁) y₀ - u₁ y₀ = u₀ y₀ := by
              change u₀ y₀ + u₁ y₀ - u₁ y₀ = u₀ y₀
              abel
            rwa [heq] at hm)
        have hsum_y1 : (u₀ + u₁) y₁ ∉ H y₁ := fun h =>
          hu1y1 (by
            have hm := (H y₁).sub_mem h hu0y1
            have heq : (u₀ + u₁) y₁ - u₀ y₁ = u₁ y₁ := by
              change u₀ y₁ + u₁ y₁ - u₀ y₁ = u₁ y₁
              abel
            rwa [heq] at hm)
        have hG2_y0 : G 2 y₀ ≠ H y₀ := fun h =>
          hsum_y0 (h ▸ hu01_C2 y₀ (Set.mem_univ y₀))
        have hG2_y1 : G 2 y₁ ≠ H y₁ := fun h =>
          hsum_y1 (h ▸ hu01_C2 y₁ (Set.mem_univ y₁))
        have hy0_eq2 : y₀ = y₂ := by by_contra h; exact hG2_y0 (hy2_other y₀ h)
        have hy1_eq2 : y₁ = y₂ := by by_contra h; exact hG2_y1 (hy2_other y₁ h)
        exact hne (hy0_eq2.trans hy1_eq2.symm)
      subst hy01
      have hC0_eq : C 0 = Htot ⊔ Submodule.span (ZMod 2) {u₀} :=
        PEqualNP.Outside.L_lib_724.eq_sup_span_of_lt_finrank (hH_le_G 0) (hfin_C 0) hu0C0 hu0H
      have hC1_eq : C 1 = Htot ⊔ Submodule.span (ZMod 2) {u₁} :=
        PEqualNP.Outside.L_lib_724.eq_sup_span_of_lt_finrank (hH_le_G 1) (hfin_C 1) hu1C1 hu1H
      have hC2_eq : C 2 = Htot ⊔ Submodule.span (ZMod 2) {u₀ + u₁} :=
        PEqualNP.Outside.L_lib_724.eq_sup_span_of_lt_finrank (hH_le_G 2) (hfin_C 2) hu01_C2 hu01_not_H
      have hu0y0 : u₀ y₀ ∉ H y₀ := by
        intro h0; apply hu0H; intro z _; dsimp; by_cases hz : z = y₀
        · subst hz; exact h0
        · rw [← hy0_other z hz]; exact hu0C0 z (Set.mem_univ z)
      have hu1y0 : u₁ y₀ ∉ H y₀ := by
        intro h1; apply hu1H; intro z _; dsimp; by_cases hz : z = y₀
        · subst hz; exact h1
        · rw [← hy1_other z hz]; exact hu1C1 z (Set.mem_univ z)
      have hu01y0 : u₀ y₀ + u₁ y₀ ∉ H y₀ := by
        intro h01
        apply hu01_not_H
        intro z _
        by_cases hz : z = y₀
        · subst hz; exact h01
        · have hz0 : u₀ z ∈ H z := by rw [← hy0_other z hz]; exact hu0C0 z (Set.mem_univ z)
          have hz1 : u₁ z ∈ H z := by rw [← hy1_other z hz]; exact hu1C1 z (Set.mem_univ z)
          exact (H z).add_mem hz0 hz1
      have hy0_eq2 : y₀ = y₂ := by
        by_contra hne
        have hG2_y0 : G 2 y₀ ≠ H y₀ := fun h =>
          hu01y0 (h ▸ (hu01_C2 y₀ (Set.mem_univ y₀)))
        exact hG2_y0 (hy2_other y₀ hne)
      subst hy0_eq2
      have hG0_u0 : G 0 y₀ = line y₀ (u₀ y₀) := by
        apply le_antisymm _ (sup_le (fun v hv => Submodule.mem_sup_left hv)
          (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (hu0C0 y₀ (Set.mem_univ y₀)))))
        intro v hv
        have hvC : Pi.single y₀ v ∈ C 0 := by
          intro z _; by_cases hz : z = y₀
          · subst hz; simpa using hv
          · simp [Pi.single_eq_of_ne hz]
        rw [hC0_eq] at hvC
        rcases Submodule.mem_sup.mp hvC with ⟨h1, hh1, k, hk, hsum⟩
        rcases Submodule.mem_span_singleton.mp hk with ⟨α, rfl⟩
        have hvy := congr_fun hsum y₀
        simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same] at hvy
        rw [← hvy]
        exact Submodule.add_mem_sup (hh1 y₀ (Set.mem_univ y₀))
          (Submodule.smul_mem _ α (Submodule.subset_span rfl))
      have hG1_u1 : G 1 y₀ = line y₀ (u₁ y₀) := by
        apply le_antisymm _ (sup_le (fun v hv => Submodule.mem_sup_left hv)
          (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (hu1C1 y₀ (Set.mem_univ y₀)))))
        intro v hv
        have hvC : Pi.single y₀ v ∈ C 1 := by
          intro z _; by_cases hz : z = y₀
          · subst hz; simpa using hv
          · simp [Pi.single_eq_of_ne hz]
        rw [hC1_eq] at hvC
        rcases Submodule.mem_sup.mp hvC with ⟨h1, hh1, k, hk, hsum⟩
        rcases Submodule.mem_span_singleton.mp hk with ⟨α, rfl⟩
        have hvy := congr_fun hsum y₀
        simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same] at hvy
        rw [← hvy]
        exact Submodule.add_mem_sup (hh1 y₀ (Set.mem_univ y₀))
          (Submodule.smul_mem _ α (Submodule.subset_span rfl))
      have hG2_u01 : G 2 y₀ = line y₀ (u₀ y₀ + u₁ y₀) := by
        apply le_antisymm _ (sup_le (fun v hv => Submodule.mem_sup_left hv)
          (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (hu01_C2 y₀ (Set.mem_univ y₀)))))
        intro v hv
        have hvC : Pi.single y₀ v ∈ C 2 := by
          intro z _; by_cases hz : z = y₀
          · subst hz; simpa using hv
          · simp [Pi.single_eq_of_ne hz]
        rw [hC2_eq] at hvC
        rcases Submodule.mem_sup.mp hvC with ⟨h1, hh1, k, hk, hsum⟩
        rcases Submodule.mem_span_singleton.mp hk with ⟨α, rfl⟩
        have hvy := congr_fun hsum y₀
        simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same] at hvy
        rw [← hvy]
        exact Submodule.add_mem_sup (hh1 y₀ (Set.mem_univ y₀))
          (Submodule.smul_mem _ α (Submodule.subset_span rfl))
      refine ⟨y₀, u₀ y₀, u₁ y₀, hu0y0, hu1y0, hu01y0, fun i z hz => ?_, hG0_u0, hG1_u1, hG2_u01⟩
      fin_cases i
      · exact hy0_other z hz
      · exact hy1_other z hz
      · exact hy2_other z hz
  · rintro (⟨i, hi⟩ | ⟨y, a, b, _, _, _, hother, hG0, hG1, hG2⟩) c hcA
    · refine ⟨i, fun x hx => hcA x (fun z hz => ?_)⟩
      dsimp
      rw [← hi z]
      exact hx z hz
    · have hdot_in_B : ∀ (i : Fin 3) (w : W),
          G i y = line y w → dotProduct (c y) w = 0 → c ∈ B i := by
        intro i w hGi hcw x hx
        simp only [PEqualNP.Outside.L_lib_724.pairing]
        apply Finset.sum_eq_zero
        intro z _
        by_cases hz : z = y
        · subst hz
          have hxG : x z ∈ line z w := hGi ▸ hx z (Set.mem_univ z)
          rcases Submodule.mem_sup.mp hxG with ⟨h1, hh1, k, hk, hsum⟩
          rcases Submodule.mem_span_singleton.mp hk with ⟨α, rfl⟩
          rw [← hsum, dotProduct_add, dotProduct_smul, hcw, smul_zero, add_zero]
          have h1s : Pi.single z h1 ∈ Htot := by
            intro z' _
            by_cases hz' : z' = z
            · subst hz'; simpa using hh1
            · simp [Pi.single_eq_of_ne hz']
          have := hcA _ h1s
          rwa [PEqualNP.Outside.L_lib_724.pairing_single] at this
        · have hxH : x z ∈ H z := hother i z hz ▸ hx z (Set.mem_univ z)
          have hxs : Pi.single z (x z) ∈ Htot := by
            intro z' _
            by_cases hz' : z' = z
            · subst hz'; simpa using hxH
            · simp [Pi.single_eq_of_ne hz']
          have := hcA _ hxs
          rwa [PEqualNP.Outside.L_lib_724.pairing_single] at this
      by_cases ha0 : dotProduct (c y) a = 0
      · exact ⟨0, hdot_in_B 0 a hG0 ha0⟩
      · by_cases hb0 : dotProduct (c y) b = 0
        · exact ⟨1, hdot_in_B 1 b hG1 hb0⟩
        · have hz1 : ∀ z : ZMod 2, z ≠ 0 → z = 1 := by decide
          have ha1 : dotProduct (c y) a = 1 := hz1 _ ha0
          have hb1 : dotProduct (c y) b = 1 := hz1 _ hb0
          have hab0 : dotProduct (c y) (a + b) = 0 := by
            rw [dotProduct_add, ha1, hb1]
            decide
          exact ⟨2, hdot_in_B 2 (a + b) hG2 hab0⟩
