import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_910

private lemma zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  match a with
  | ⟨0, _⟩ => exact Or.inl rfl
  | ⟨1, _⟩ => exact Or.inr rfl

private lemma zmod2_mul_self (a : ZMod 2) : a * a = a := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;> decide

private lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;> decide

private lemma exists_free_cols {K : Type*} [Field K] {k : ℕ}
    (H : Submodule K (Fin k → K)) :
    ∃ (free : Finset (Fin k)) (b : Fin k → (Fin k → K)),
      free.card = Module.finrank K H ∧
      (∀ h ∈ H, (∀ j ∈ free, h j = 0) → h = 0) ∧
      (∀ t ∈ free, b t ∈ H) ∧
      (∀ t ∈ free, ∀ j ∈ free, b t j = if j = t then 1 else 0) := by
  classical
  let good : Finset (Fin k) → Prop := fun s => ∀ h ∈ H, (∀ j ∈ s, h j = 0) → h = 0
  let goodSet : Finset (Finset (Fin k)) := Finset.univ.filter good
  have huniv : Finset.univ ∈ goodSet := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun h _ hz => ?_⟩
    funext j
    exact hz j (Finset.mem_univ j)
  obtain ⟨free, hfree_mem, hfree_min⟩ :=
    Finset.exists_min_image goodSet Finset.card ⟨Finset.univ, huniv⟩
  have hgood : good free := (Finset.mem_filter.mp hfree_mem).2
  have hex_vec : ∀ t ∈ free, ∃ v ∈ H, ∀ j ∈ free, v j = if j = t then 1 else 0 := by
    intro t ht
    have hnot : ¬ good (free.erase t) := by
      intro hg
      have hmem : free.erase t ∈ goodSet := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩
      have hle := hfree_min (free.erase t) hmem
      have hlt : (free.erase t).card < free.card := Finset.card_erase_lt_of_mem ht
      omega
    have hnot' : ∃ h ∈ H, (∀ j ∈ free.erase t, h j = 0) ∧ h ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hnot hcon
    rcases hnot' with ⟨h, hhH, hzero, hne⟩
    have hht : h t ≠ 0 := by
      intro h0
      apply hne
      apply hgood h hhH
      intro j hj
      by_cases hjt : j = t
      · simpa [hjt] using h0
      · exact hzero j (Finset.mem_erase.mpr ⟨hjt, hj⟩)
    refine ⟨(h t)⁻¹ • h, H.smul_mem _ hhH, ?_⟩
    intro j hj
    simp only [Pi.smul_apply, smul_eq_mul]
    by_cases hjt : j = t
    · subst hjt
      simp [inv_mul_cancel₀ hht]
    · simp [hjt, hzero j (Finset.mem_erase.mpr ⟨hjt, hj⟩)]
  let b : Fin k → (Fin k → K) := fun t =>
    if ht : t ∈ free then Classical.choose (hex_vec t ht) else 0
  have hbH : ∀ t ∈ free, b t ∈ H := by
    intro t ht
    simp only [b, dif_pos ht]
    exact (Classical.choose_spec (hex_vec t ht)).1
  have hbval : ∀ t ∈ free, ∀ j ∈ free, b t j = if j = t then 1 else 0 := by
    intro t ht j hj
    simp only [b, dif_pos ht]
    exact (Classical.choose_spec (hex_vec t ht)).2 j hj
  let proj : H →ₗ[K] (free → K) :=
    { toFun := fun h j => h.val j.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective proj := by
    intro u v huv
    apply Subtype.ext
    have hsub : u.val - v.val ∈ H := H.sub_mem u.2 v.2
    have hz : ∀ j ∈ free, (u.val - v.val) j = 0 := by
      intro j hj
      have h := congr_fun huv ⟨j, hj⟩
      exact sub_eq_zero.mpr h
    exact sub_eq_zero.mp (hgood _ hsub hz)
  have hsurj : Function.Surjective proj := by
    intro y
    let v : Fin k → K := ∑ t : free, y t • b t.val
    have hvH : v ∈ H := H.sum_mem fun t _ => H.smul_mem _ (hbH t.val t.2)
    refine ⟨⟨v, hvH⟩, ?_⟩
    funext j
    change (∑ t : free, y t • b t.val) j.val = y j
    rw [Finset.sum_apply]
    trans ∑ t : free, if t = j then y t else 0
    · refine Finset.sum_congr rfl fun t _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul, hbval t.val t.2 j.val j.2]
      by_cases htj : t = j
      · subst htj
        simp
      · have hvne : j.val ≠ t.val := fun h => htj (Subtype.ext h.symm)
        simp [htj, hvne]
    · simp
  have hcard : free.card = Module.finrank K H := by
    have hfr := (LinearEquiv.ofBijective proj ⟨hinj, hsurj⟩).finrank_eq
    rw [Module.finrank_pi, Fintype.card_coe] at hfr
    exact hfr.symm
  exact ⟨free, b, hcard, hgood, hbH, hbval⟩

private lemma card_add_card_le_card_of_exact {K : Type*} [Field K]
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (phi : (α → K) →ₗ[K] (β → K))
    (psi : (β → K) →ₗ[K] (γ → K))
    (hphi : Function.Injective phi)
    (hpsi : Function.Surjective psi)
    (hcomp : ∀ v, psi (phi v) = 0) :
    Fintype.card α + Fintype.card γ ≤ Fintype.card β := by
  have hle : LinearMap.range phi ≤ LinearMap.ker psi := by
    rintro y ⟨v, rfl⟩
    exact hcomp v
  have h1 : Module.finrank K (LinearMap.range phi) = Fintype.card α := by
    rw [LinearMap.finrank_range_of_inj hphi, Module.finrank_pi]
  have h2 : Module.finrank K (LinearMap.range psi) = Fintype.card γ := by
    rw [LinearMap.range_eq_top.mpr hpsi, finrank_top, Module.finrank_pi]
  have h3 : Module.finrank K (LinearMap.range psi) + Module.finrank K (LinearMap.ker psi) =
      Fintype.card β := by
    rw [LinearMap.finrank_range_add_finrank_ker psi, Module.finrank_pi]
  have hmono : Module.finrank K (LinearMap.range phi) ≤ Module.finrank K (LinearMap.ker psi) :=
    Submodule.finrank_mono hle
  omega

private def mon {k : ℕ} (S : Finset (Fin k)) (x : Fin k → ZMod 2) : ZMod 2 :=
  ∏ j ∈ S, x j

private lemma mon_empty {k : ℕ} (x : Fin k → ZMod 2) : mon (∅ : Finset (Fin k)) x = 1 := by
  simp [mon]

private lemma mon_singleton {k : ℕ} (j : Fin k) (x : Fin k → ZMod 2) :
    mon ({j} : Finset (Fin k)) x = x j := by
  simp [mon]

private lemma mon_mul {k : ℕ} (A B : Finset (Fin k)) (x : Fin k → ZMod 2) :
    mon A x * mon B x = mon (A ∪ B) x := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    simp [mon]
  | insert a s ha ih =>
    simp only [mon, Finset.prod_insert ha, Finset.insert_union] at ih ⊢
    by_cases hmem : a ∈ s ∪ B
    · rw [Finset.insert_eq_of_mem hmem, mul_assoc, ih]
      rw [← Finset.mul_prod_erase (s ∪ B) x hmem, ← mul_assoc, zmod2_mul_self]
    · rw [Finset.prod_insert hmem, mul_assoc, ih]

private def evalPoly {k : ℕ} (free : Finset (Fin k))
    (c : {S : Finset (Fin k) // S ⊆ free} → ZMod 2)
    (x : Fin k → ZMod 2) : ZMod 2 :=
  ∑ S : {S : Finset (Fin k) // S ⊆ free}, c S * mon S.val x

private lemma evalPoly_add {k : ℕ} (free : Finset (Fin k))
    (c₁ c₂ : {S : Finset (Fin k) // S ⊆ free} → ZMod 2)
    (x : Fin k → ZMod 2) :
    evalPoly free (c₁ + c₂) x = evalPoly free c₁ x + evalPoly free c₂ x := by
  simp [evalPoly, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private lemma evalPoly_smul {k : ℕ} (free : Finset (Fin k))
    (a : ZMod 2) (c : {S : Finset (Fin k) // S ⊆ free} → ZMod 2)
    (x : Fin k → ZMod 2) :
    evalPoly free (a • c) x = a * evalPoly free c x := by
  simp [evalPoly, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

private lemma evalPoly_sum {k : ℕ} {ι : Type*} (free : Finset (Fin k))
    (s : Finset ι) (c : ι → {S : Finset (Fin k) // S ⊆ free} → ZMod 2)
    (x : Fin k → ZMod 2) :
    evalPoly free (∑ i ∈ s, c i) x = ∑ i ∈ s, evalPoly free (c i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [evalPoly]
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, evalPoly_add, Finset.sum_insert ha, ih]

private def mulCoeff {k : ℕ} (free : Finset (Fin k))
    (c₁ c₂ : {S : Finset (Fin k) // S ⊆ free} → ZMod 2) :
    {S : Finset (Fin k) // S ⊆ free} → ZMod 2 :=
  fun T =>
    ∑ T₁ : {S : Finset (Fin k) // S ⊆ free},
      ∑ T₂ : {S : Finset (Fin k) // S ⊆ free},
        if T₁.val ∪ T₂.val = T.val then c₁ T₁ * c₂ T₂ else 0

private lemma evalPoly_mul {k : ℕ} (free : Finset (Fin k))
    (c₁ c₂ : {S : Finset (Fin k) // S ⊆ free} → ZMod 2)
    (x : Fin k → ZMod 2) :
    evalPoly free c₁ x * evalPoly free c₂ x = evalPoly free (mulCoeff free c₁ c₂) x := by
  classical
  let FSub := {S : Finset (Fin k) // S ⊆ free}
  calc
    evalPoly free c₁ x * evalPoly free c₂ x
      = ∑ T₁ : FSub, ∑ T₂ : FSub, (c₁ T₁ * c₂ T₂) * (mon T₁.val x * mon T₂.val x) := by
          unfold evalPoly
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun T₁ _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun T₂ _ => ?_
          ring
    _ = ∑ T₁ : FSub, ∑ T₂ : FSub, (c₁ T₁ * c₂ T₂) * mon (T₁.val ∪ T₂.val) x := by
          refine Finset.sum_congr rfl fun T₁ _ => Finset.sum_congr rfl fun T₂ _ => ?_
          rw [mon_mul]
    _ = ∑ T₁ : FSub, ∑ T₂ : FSub,
          ∑ T : FSub, (if T₁.val ∪ T₂.val = T.val then c₁ T₁ * c₂ T₂ else 0) * mon T.val x := by
          refine Finset.sum_congr rfl fun T₁ _ => Finset.sum_congr rfl fun T₂ _ => ?_
          let U : FSub := ⟨T₁.val ∪ T₂.val, Finset.union_subset T₁.2 T₂.2⟩
          rw [Finset.sum_eq_single U]
          · simp [U]
          · intro T _ hTU
            have hne : T₁.val ∪ T₂.val ≠ T.val := fun h => hTU (Subtype.ext h.symm)
            simp [hne]
          · intro h
            exact (h (Finset.mem_univ U)).elim
    _ = ∑ T : FSub,
          (∑ T₁ : FSub, ∑ T₂ : FSub,
            if T₁.val ∪ T₂.val = T.val then c₁ T₁ * c₂ T₂ else 0) * mon T.val x := by
          trans ∑ T₁ : FSub, ∑ T : FSub, ∑ T₂ : FSub,
              (if T₁.val ∪ T₂.val = T.val then c₁ T₁ * c₂ T₂ else 0) * mon T.val x
          · refine Finset.sum_congr rfl fun T₁ _ => Finset.sum_comm
          · rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun T _ => ?_
            simp only [Finset.sum_mul]
    _ = evalPoly free (mulCoeff free c₁ c₂) x := rfl

private lemma evalPoly_inj {k : ℕ} (free : Finset (Fin k))
    (H : Submodule (ZMod 2) (Fin k → ZMod 2)) (base : Fin k → ZMod 2)
    (hsurj : ∀ y : free → ZMod 2, ∃ x : {x : Fin k → ZMod 2 // x - base ∈ H},
      ∀ j : free, x.val j.val = y j)
    (c : {S : Finset (Fin k) // S ⊆ free} → ZMod 2)
    (hzero : ∀ x : {x : Fin k → ZMod 2 // x - base ∈ H}, evalPoly free c x.val = 0) :
    c = 0 := by
  classical
  let FSub := {S : Finset (Fin k) // S ⊆ free}
  by_contra hc
  have hne : (Finset.univ.filter (fun S : FSub => c S ≠ 0)).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    apply hc
    funext S
    by_contra hcs
    have hmem : S ∈ Finset.univ.filter (fun S : FSub => c S ≠ 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ S, hcs⟩
    rw [hemp] at hmem
    exact Finset.notMem_empty S hmem
  obtain ⟨S₀, hS₀_mem, hS₀_min⟩ :=
    Finset.exists_min_image _ (fun S : FSub => S.val.card) hne
  have hcS₀ : c S₀ ≠ 0 := (Finset.mem_filter.mp hS₀_mem).2
  let y₀ : free → ZMod 2 := fun j => if j.val ∈ S₀.val then 1 else 0
  obtain ⟨x₀, hx₀⟩ := hsurj y₀
  have hmon : ∀ S : FSub, mon S.val x₀.val = if S.val ⊆ S₀.val then 1 else 0 := by
    intro S
    by_cases hsub : S.val ⊆ S₀.val
    · rw [if_pos hsub]
      unfold mon
      apply Finset.prod_eq_one
      intro j hj
      have hjf : j ∈ free := S.2 hj
      have h := hx₀ ⟨j, hjf⟩
      simp only [y₀, if_pos (hsub hj)] at h
      exact h
    · rw [if_neg hsub]
      rw [Finset.not_subset] at hsub
      rcases hsub with ⟨j, hjS, hjnot⟩
      have hjf : j ∈ free := S.2 hjS
      have h := hx₀ ⟨j, hjf⟩
      simp only [y₀, if_neg hjnot] at h
      unfold mon
      exact Finset.prod_eq_zero hjS h
  have hev : evalPoly free c x₀.val = c S₀ := by
    unfold evalPoly
    rw [Finset.sum_eq_single S₀]
    · rw [hmon S₀, if_pos (Finset.Subset.refl _), mul_one]
    · intro S _ hneS
      by_cases hcs : c S = 0
      · simp [hcs]
      · have hnotSub : ¬ S.val ⊆ S₀.val := by
          intro hsub
          have hmem : S ∈ Finset.univ.filter (fun S : FSub => c S ≠ 0) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ S, hcs⟩
          have hle := hS₀_min S hmem
          have heq := Finset.eq_of_subset_of_card_le hsub hle
          exact hneS (Subtype.ext heq)
        rw [hmon S, if_neg hnotSub, mul_zero]
    · intro h
      exact (h (Finset.mem_univ S₀)).elim
  have h0 := hzero x₀
  rw [hev] at h0
  exact hcS₀ h0

private def HasDegLe {k : ℕ} (free : Finset (Fin k))
    (H : Submodule (ZMod 2) (Fin k → ZMod 2)) (base : Fin k → ZMod 2)
    (d : ℕ) (f : {x : Fin k → ZMod 2 // x - base ∈ H} → ZMod 2) : Prop :=
  ∃ c : {S : Finset (Fin k) // S ⊆ free} → ZMod 2,
    (∀ T : {S : Finset (Fin k) // S ⊆ free}, d < T.val.card → c T = 0) ∧
    ∀ x : {x : Fin k → ZMod 2 // x - base ∈ H}, f x = evalPoly free c x.val

private lemma hasDegLe_mono {k : ℕ} {free : Finset (Fin k)}
    {H : Submodule (ZMod 2) (Fin k → ZMod 2)} {base : Fin k → ZMod 2}
    {d₁ d₂ : ℕ} {f : {x : Fin k → ZMod 2 // x - base ∈ H} → ZMod 2}
    (hd : d₁ ≤ d₂) (hf : HasDegLe free H base d₁ f) :
    HasDegLe free H base d₂ f := by
  rcases hf with ⟨c, hdeg, heval⟩
  exact ⟨c, fun T hT => hdeg T (lt_of_le_of_lt hd hT), heval⟩

private lemma hasDegLe_const {k : ℕ} (free : Finset (Fin k))
    (H : Submodule (ZMod 2) (Fin k → ZMod 2)) (base : Fin k → ZMod 2) (a : ZMod 2) :
    HasDegLe free H base 0 (fun _ => a) := by
  classical
  let FSub := {S : Finset (Fin k) // S ⊆ free}
  let emp : FSub := ⟨∅, Finset.empty_subset _⟩
  refine ⟨fun T => if T = emp then a else 0, ?_, ?_⟩
  · intro T hT
    have hne : T ≠ emp := by
      intro heq
      subst heq
      simp [emp] at hT
    simp [hne]
  · intro x
    unfold evalPoly
    rw [Finset.sum_eq_single emp]
    · simp [emp, mon_empty]
    · intro T _ hne
      simp [hne]
    · intro h
      exact (h (Finset.mem_univ emp)).elim

private lemma hasDegLe_free_coord {k : ℕ} (free : Finset (Fin k))
    (H : Submodule (ZMod 2) (Fin k → ZMod 2)) (base : Fin k → ZMod 2)
    (t : Fin k) (ht : t ∈ free) :
    HasDegLe free H base 1 (fun x => x.val t) := by
  classical
  let FSub := {S : Finset (Fin k) // S ⊆ free}
  let sing : FSub := ⟨{t}, Finset.singleton_subset_iff.mpr ht⟩
  refine ⟨fun T => if T = sing then 1 else 0, ?_, ?_⟩
  · intro T hT
    have hne : T ≠ sing := by
      intro heq
      subst heq
      simp [sing] at hT
    simp [hne]
  · intro x
    unfold evalPoly
    rw [Finset.sum_eq_single sing]
    · simp [sing, mon_singleton]
    · intro T _ hne
      simp [hne]
    · intro h
      exact (h (Finset.mem_univ sing)).elim

private lemma hasDegLe_add {k : ℕ} {free : Finset (Fin k)}
    {H : Submodule (ZMod 2) (Fin k → ZMod 2)} {base : Fin k → ZMod 2}
    {d : ℕ} {f g : {x : Fin k → ZMod 2 // x - base ∈ H} → ZMod 2}
    (hf : HasDegLe free H base d f) (hg : HasDegLe free H base d g) :
    HasDegLe free H base d (fun x => f x + g x) := by
  rcases hf with ⟨c₁, h₁, he₁⟩
  rcases hg with ⟨c₂, h₂, he₂⟩
  refine ⟨c₁ + c₂, ?_, ?_⟩
  · intro T hT
    simp [Pi.add_apply, h₁ T hT, h₂ T hT]
  · intro x
    dsimp only
    rw [evalPoly_add, he₁ x, he₂ x]

private lemma hasDegLe_smul {k : ℕ} {free : Finset (Fin k)}
    {H : Submodule (ZMod 2) (Fin k → ZMod 2)} {base : Fin k → ZMod 2}
    {d : ℕ} (a : ZMod 2) {f : {x : Fin k → ZMod 2 // x - base ∈ H} → ZMod 2}
    (hf : HasDegLe free H base d f) :
    HasDegLe free H base d (fun x => a * f x) := by
  rcases hf with ⟨c, h, he⟩
  refine ⟨a • c, ?_, ?_⟩
  · intro T hT
    simp [Pi.smul_apply, h T hT]
  · intro x
    dsimp only
    rw [evalPoly_smul, he x]

private lemma hasDegLe_sum {k : ℕ} {ι : Type*} {free : Finset (Fin k)}
    {H : Submodule (ZMod 2) (Fin k → ZMod 2)} {base : Fin k → ZMod 2}
    {d : ℕ} (s : Finset ι) (f : ι → {x : Fin k → ZMod 2 // x - base ∈ H} → ZMod 2)
    (hf : ∀ i ∈ s, HasDegLe free H base d (f i)) :
    HasDegLe free H base d (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using hasDegLe_mono (Nat.zero_le d) (hasDegLe_const free H base 0)
  | insert a t ha ih =>
    have h1 := hf a (Finset.mem_insert_self a t)
    have h2 := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have hsum := hasDegLe_add h1 h2
    simpa [Finset.sum_insert ha] using hsum

private lemma hasDegLe_mul {k : ℕ} {free : Finset (Fin k)}
    {H : Submodule (ZMod 2) (Fin k → ZMod 2)} {base : Fin k → ZMod 2}
    {d₁ d₂ : ℕ} {f g : {x : Fin k → ZMod 2 // x - base ∈ H} → ZMod 2}
    (hf : HasDegLe free H base d₁ f) (hg : HasDegLe free H base d₂ g) :
    HasDegLe free H base (d₁ + d₂) (fun x => f x * g x) := by
  rcases hf with ⟨c₁, h₁, he₁⟩
  rcases hg with ⟨c₂, h₂, he₂⟩
  refine ⟨mulCoeff free c₁ c₂, ?_, ?_⟩
  · intro T hT
    unfold mulCoeff
    apply Finset.sum_eq_zero
    intro T₁ _
    apply Finset.sum_eq_zero
    intro T₂ _
    split_ifs with hu
    · have hcard : T.val.card ≤ T₁.val.card + T₂.val.card := by
        rw [← hu]
        exact Finset.card_union_le T₁.val T₂.val
      by_cases hlt1 : d₁ < T₁.val.card
      · rw [h₁ T₁ hlt1, zero_mul]
      · have hlt2 : d₂ < T₂.val.card := by omega
        rw [h₂ T₂ hlt2, mul_zero]
    · rfl
  · intro x
    dsimp only
    rw [he₁ x, he₂ x, evalPoly_mul]

private def HasLeading {k : ℕ} (free : Finset (Fin k))
    (H : Submodule (ZMod 2) (Fin k → ZMod 2)) (base : Fin k → ZMod 2)
    (B : {S : Finset (Fin k) // S ⊆ free})
    (f : {x : Fin k → ZMod 2 // x - base ∈ H} → ZMod 2) : Prop :=
  ∃ c : {S : Finset (Fin k) // S ⊆ free} → ZMod 2,
    c B = 1 ∧
    (∀ T : {S : Finset (Fin k) // S ⊆ free}, B.val.card ≤ T.val.card → T ≠ B → c T = 0) ∧
    ∀ x : {x : Fin k → ZMod 2 // x - base ∈ H}, f x = evalPoly free c x.val

private lemma hasLeading_mon {k : ℕ} (free : Finset (Fin k))
    (H : Submodule (ZMod 2) (Fin k → ZMod 2)) (base : Fin k → ZMod 2)
    (B : {S : Finset (Fin k) // S ⊆ free}) :
    HasLeading free H base B (fun x => mon B.val x.val) := by
  classical
  refine ⟨fun T => if T = B then 1 else 0, by simp, ?_, ?_⟩
  · intro T _ hne
    simp [hne]
  · intro x
    unfold evalPoly
    rw [Finset.sum_eq_single B]
    · simp
    · intro T _ hne
      simp [hne]
    · intro h
      exact (h (Finset.mem_univ B)).elim

private lemma hasLeading_mon_add_degLt {k : ℕ} (free : Finset (Fin k))
    (H : Submodule (ZMod 2) (Fin k → ZMod 2)) (base : Fin k → ZMod 2)
    (B : {S : Finset (Fin k) // S ⊆ free})
    (hBne : B.val.Nonempty)
    {p : {x : Fin k → ZMod 2 // x - base ∈ H} → ZMod 2}
    (hp : HasDegLe free H base (B.val.card - 1) p) :
    HasLeading free H base B (fun x => mon B.val x.val + p x) := by
  classical
  rcases hp with ⟨cp, hdeg, heval⟩
  have hpos : 0 < B.val.card := Finset.card_pos.mpr hBne
  let c : {S : Finset (Fin k) // S ⊆ free} → ZMod 2 := fun T => (if T = B then 1 else 0) + cp T
  refine ⟨c, ?_, ?_, ?_⟩
  · have hcpB : cp B = 0 := hdeg B (by omega)
    simp [c, hcpB]
  · intro T hle hne
    have hcpT : cp T = 0 := hdeg T (by omega)
    simp [c, hne, hcpT]
  · intro x
    have h1 : evalPoly free (fun T => if T = B then 1 else 0) x.val = mon B.val x.val := by
      unfold evalPoly
      rw [Finset.sum_eq_single B]
      · simp
      · intro T _ hne
        simp [hne]
      · intro h
        exact (h (Finset.mem_univ B)).elim
    have hc : c = (fun T => if T = B then 1 else 0) + cp := rfl
    dsimp only
    rw [hc, evalPoly_add, h1, heval x]

private lemma hasLeading_mul {k : ℕ} (free : Finset (Fin k))
    (H : Submodule (ZMod 2) (Fin k → ZMod 2)) (base : Fin k → ZMod 2)
    (B₁ B₂ : {S : Finset (Fin k) // S ⊆ free})
    (hdisj : Disjoint B₁.val B₂.val)
    {f₁ f₂ : {x : Fin k → ZMod 2 // x - base ∈ H} → ZMod 2}
    (hf₁ : HasLeading free H base B₁ f₁)
    (hf₂ : HasLeading free H base B₂ f₂) :
    HasLeading free H base ⟨B₁.val ∪ B₂.val, Finset.union_subset B₁.2 B₂.2⟩
      (fun x => f₁ x * f₂ x) := by
  classical
  let FSub := {S : Finset (Fin k) // S ⊆ free}
  let B : FSub := ⟨B₁.val ∪ B₂.val, Finset.union_subset B₁.2 B₂.2⟩
  have hBcard : B.val.card = B₁.val.card + B₂.val.card := Finset.card_union_of_disjoint hdisj
  rcases hf₁ with ⟨c₁, hc₁B, hc₁0, he₁⟩
  rcases hf₂ with ⟨c₂, hc₂B, hc₂0, he₂⟩
  have hterm_zero : ∀ (T T₁ T₂ : FSub), B.val.card ≤ T.val.card →
      T₁.val ∪ T₂.val = T.val → (T₁ ≠ B₁ ∨ T₂ ≠ B₂) → c₁ T₁ * c₂ T₂ = 0 := by
    intro T T₁ T₂ hle hu hneq
    have hcard : T.val.card ≤ T₁.val.card + T₂.val.card := by
      rw [← hu]
      exact Finset.card_union_le T₁.val T₂.val
    by_cases h1 : B₁.val.card < T₁.val.card
    · rw [hc₁0 T₁ (le_of_lt h1) (fun h => by subst h; omega), zero_mul]
    · by_cases h2 : B₂.val.card < T₂.val.card
      · rw [hc₂0 T₂ (le_of_lt h2) (fun h => by subst h; omega), mul_zero]
      · have he1 : T₁.val.card = B₁.val.card := by omega
        have he2 : T₂.val.card = B₂.val.card := by omega
        rcases hneq with hne1 | hne2
        · rw [hc₁0 T₁ (le_of_eq he1.symm) hne1, zero_mul]
        · rw [hc₂0 T₂ (le_of_eq he2.symm) hne2, mul_zero]
  refine ⟨mulCoeff free c₁ c₂, ?_, ?_, ?_⟩
  · unfold mulCoeff
    rw [Finset.sum_eq_single B₁]
    · rw [Finset.sum_eq_single B₂]
      · simp [B, hc₁B, hc₂B]
      · intro T₂ _ hne2
        split_ifs with hu
        · exact hterm_zero B B₁ T₂ (le_refl _) hu (Or.inr hne2)
        · rfl
      · intro h
        exact (h (Finset.mem_univ B₂)).elim
    · intro T₁ _ hne1
      apply Finset.sum_eq_zero
      intro T₂ _
      split_ifs with hu
      · exact hterm_zero B T₁ T₂ (le_refl _) hu (Or.inl hne1)
      · rfl
    · intro h
      exact (h (Finset.mem_univ B₁)).elim
  · intro T hle hne
    unfold mulCoeff
    apply Finset.sum_eq_zero
    intro T₁ _
    apply Finset.sum_eq_zero
    intro T₂ _
    split_ifs with hu
    · have hneq : T₁ ≠ B₁ ∨ T₂ ≠ B₂ := by
        by_contra hall
        push_neg at hall
        rcases hall with ⟨rfl, rfl⟩
        exact hne (Subtype.ext hu.symm)
      exact hterm_zero T T₁ T₂ hle hu hneq
    · rfl
  · intro x
    dsimp only
    rw [he₁ x, he₂ x, evalPoly_mul]

private lemma hasLeading_prod {k m : ℕ} (free : Finset (Fin k))
    (H : Submodule (ZMod 2) (Fin k → ZMod 2)) (base : Fin k → ZMod 2)
    (block : Fin m → Finset (Fin k))
    (hdisj : ∀ i j, i ≠ j → Disjoint (block i) (block j))
    (f : Fin m → {x : Fin k → ZMod 2 // x - base ∈ H} → ZMod 2)
    (I : Finset (Fin m))
    (hsub : ∀ i ∈ I, block i ⊆ free)
    (hf : ∀ i (hi : i ∈ I), HasLeading free H base ⟨block i, hsub i hi⟩ (f i)) :
    HasLeading free H base
      ⟨I.biUnion block, Finset.biUnion_subset.mpr hsub⟩
      (fun x => ∏ i ∈ I, f i x) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    have h0 := hasLeading_mon free H base ⟨∅, Finset.empty_subset _⟩
    simpa [mon_empty] using h0
  | insert a t ha ih =>
    have ha_sub : block a ⊆ free := hsub a (Finset.mem_insert_self a t)
    have ht_sub : ∀ i ∈ t, block i ⊆ free := fun i hi => hsub i (Finset.mem_insert_of_mem hi)
    have hfa := hf a (Finset.mem_insert_self a t)
    have hft := ih ht_sub (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have hdisj_at : Disjoint (block a) (t.biUnion block) := by
      rw [Finset.disjoint_biUnion_right]
      intro i hi
      exact hdisj a i (fun heq => ha (heq ▸ hi))
    have hmul := hasLeading_mul free H base
      ⟨block a, ha_sub⟩
      ⟨t.biUnion block, Finset.biUnion_subset.mpr ht_sub⟩
      hdisj_at hfa hft
    have hbu : block a ∪ t.biUnion block = (insert a t).biUnion block := by
      rw [Finset.biUnion_insert]
    have hsub_eq :
        (⟨block a ∪ t.biUnion block,
          Finset.union_subset ha_sub (Finset.biUnion_subset.mpr ht_sub)⟩ :
            {S : Finset (Fin k) // S ⊆ free}) =
        ⟨(insert a t).biUnion block, Finset.biUnion_subset.mpr hsub⟩ :=
      Subtype.ext hbu
    rw [hsub_eq] at hmul
    simpa [Finset.prod_insert ha] using hmul

end PEqualNP.Outside.L_lib_910

open PEqualNP.Outside.L_lib_910 in
theorem PEqualNP.Outside.L_lib_910 :
    ∀ (k : Nat),
      let F := ZMod 2
      let W := Fin k → F
      ∀ (H : Submodule F W) (base : W),
        let X := {x : W // x-base ∈ H}
        ∃ free : Finset (Fin k),
          free.card = Module.finrank F H ∧
          (∀ u v : X, (∀ j ∈ free, u.val j = v.val j) → u = v) ∧
          ∀ (m : Nat) (block : Fin m → Finset (Fin k)),
            (∀ i, (block i).Nonempty) →
            (∀ i j, i ≠ j → Disjoint (block i) (block j)) →
            ∀ P : Fin m → W → F,
              (∀ i, ∃ terms : Finset (Finset (Fin k)),
                (∀ S ∈ terms, S.card < (block i).card) ∧
                ∀ x, P i x = ∑ S ∈ terms, ∏ j ∈ S, x j) →
              ∃ pair : X ≃ {S : Finset (Fin k) // S ⊆ free},
                ∀ (x : X) (i : Fin m), block i ⊆ (pair x).val →
                  P i x.val ≠ ∏ j ∈ block i, x.val j := by
  classical
  intro k F W H base X
  obtain ⟨free, b, hcard_free, hgood, hbH, hbval⟩ := exists_free_cols H
  have huniq : ∀ u v : X, (∀ j ∈ free, u.val j = v.val j) → u = v := by
    intro u v huv
    apply Subtype.ext
    have hdiff : u.val - v.val ∈ H := by
      have h1 := H.sub_mem u.2 v.2
      simpa [sub_sub_sub_cancel_right] using h1
    have hz : ∀ j ∈ free, (u.val - v.val) j = 0 := by
      intro j hj
      exact sub_eq_zero.mpr (huv j hj)
    exact sub_eq_zero.mp (hgood _ hdiff hz)
  refine ⟨free, hcard_free, huniq, ?_⟩
  intro m block hne hdisj P hPdeg
  let FSub := {S : Finset (Fin k) // S ⊆ free}
  let lift : (free → F) → X := fun y =>
    ⟨base + ∑ t : free, (y t - base t.val) • b t.val, by
      have hmem : ∑ t : free, (y t - base t.val) • b t.val ∈ H :=
        H.sum_mem fun t _ => H.smul_mem _ (hbH t.val t.2)
      simpa [add_sub_cancel_left] using hmem⟩
  have hlift_val : ∀ (y : free → F) (j : free), (lift y).val j.val = y j := by
    intro y j
    change base j.val + (∑ t : free, (y t - base t.val) • b t.val) j.val = y j
    rw [Finset.sum_apply]
    have hsum : (∑ t : free, ((y t - base t.val) • b t.val) j.val) = y j - base j.val := by
      rw [Finset.sum_eq_single j]
      · simp [Pi.smul_apply, smul_eq_mul, hbval j.val j.2 j.val j.2]
      · intro t _ htj
        have hvne : j.val ≠ t.val := fun h => htj (Subtype.ext h.symm)
        simp [Pi.smul_apply, smul_eq_mul, hbval t.val t.2 j.val j.2, hvne]
      · intro h
        exact (h (Finset.mem_univ j)).elim
    rw [hsum]
    ring
  have hsurj_X : ∀ y : free → F, ∃ x : X, ∀ j : free, x.val j.val = y j :=
    fun y => ⟨lift y, hlift_val y⟩
  have hX_eq_lift : ∀ x : X, x = lift (fun j : free => x.val j.val) := by
    intro x
    apply huniq
    intro j hj
    exact (hlift_val (fun t : free => x.val t.val) ⟨j, hj⟩).symm
  have hcoord_deg1 : ∀ j : Fin k, HasDegLe free H base 1 (fun x : X => x.val j) := by
    intro j
    have hexpr : ∀ x : X,
        x.val j = (base j - ∑ t : free, base t.val * b t.val j) +
          ∑ t : free, b t.val j * x.val t.val := by
      intro x
      have hx := congr_fun (congr_arg Subtype.val (hX_eq_lift x)) j
      change x.val j = base j + (∑ t : free, (x.val t.val - base t.val) • b t.val) j at hx
      rw [hx, Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib]
      have hcomm : ∑ t : free, x.val t.val * b t.val j = ∑ t : free, b t.val j * x.val t.val :=
        Finset.sum_congr rfl fun t _ => mul_comm _ _
      rw [hcomm]
      ring
    have h1 := hasDegLe_mono (Nat.zero_le 1)
      (hasDegLe_const free H base (base j - ∑ t : free, base t.val * b t.val j))
    have h2 : HasDegLe free H base 1 (fun x : X => ∑ t : free, b t.val j * x.val t.val) :=
      hasDegLe_sum Finset.univ (fun (t : free) (x : X) => b t.val j * x.val t.val)
        (fun t _ => hasDegLe_smul (b t.val j) (hasDegLe_free_coord free H base t.val t.2))
    have h3 := hasDegLe_add h1 h2
    rcases h3 with ⟨c, hdeg, heval⟩
    exact ⟨c, hdeg, fun x => by dsimp only; rw [hexpr x]; exact heval x⟩
  have hmon_deg : ∀ S : Finset (Fin k), HasDegLe free H base S.card (fun x : X => mon S x.val) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have h0 := hasDegLe_const free H base 1
      simpa [mon_empty] using h0
    | insert a s ha ih =>
      have hmul := hasDegLe_mul (hcoord_deg1 a) ih
      have hcard : 1 + s.card = (insert a s).card := by
        rw [Finset.card_insert_of_notMem ha]
        omega
      rw [hcard] at hmul
      simpa [mon, Finset.prod_insert ha] using hmul
  have hP_deg : ∀ i : Fin m, HasDegLe free H base ((block i).card - 1) (fun x : X => P i x.val) := by
    intro i
    rcases hPdeg i with ⟨terms, hlt, hsum⟩
    have hpos : 1 ≤ (block i).card := Finset.card_pos.mpr (hne i)
    have hterm : ∀ S ∈ terms, HasDegLe free H base ((block i).card - 1) (fun x : X => mon S x.val) := by
      intro S hS
      have hle : S.card ≤ (block i).card - 1 := by
        have := hlt S hS
        omega
      exact hasDegLe_mono hle (hmon_deg S)
    have htot := hasDegLe_sum terms (fun S (x : X) => mon S x.val) hterm
    rcases htot with ⟨c, hdeg, heval⟩
    exact ⟨c, hdeg, fun x => by dsimp only; rw [hsum x.val]; exact heval x⟩
  have hX_equiv_fun : X ≃ (free → F) :=
    { toFun := fun x j => x.val j.val
      invFun := lift
      left_inv := fun x => (hX_eq_lift x).symm
      right_inv := fun y => funext (hlift_val y) }
  have hFSub_equiv_fun : FSub ≃ (free → F) :=
    { toFun := fun S j => if j.val ∈ S.val then 1 else 0
      invFun := fun y => ⟨free.filter (fun j => if hj : j ∈ free then y ⟨j, hj⟩ = 1 else False),
        Finset.filter_subset _ _⟩
      left_inv := by
        intro S
        apply Subtype.ext
        ext j
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hj, h1⟩
          rw [dif_pos hj] at h1
          split_ifs at h1 with hmem
          · exact hmem
          · exfalso
            exact zero_ne_one h1
        · intro hjS
          have hj : j ∈ free := S.2 hjS
          exact ⟨hj, by rw [dif_pos hj]; simp [hjS]⟩
      right_inv := by
        intro y
        funext j
        simp only [Finset.mem_filter, j.2, true_and, dif_pos]
        rcases zmod2_eq_zero_or_one (y j) with h0 | h1
        · simp [h0]
        · simp [h1] }
  have hcard_XF : Fintype.card X = Fintype.card FSub := by
    rw [Fintype.card_congr hX_equiv_fun, Fintype.card_congr hFSub_equiv_fun]
  let nbr : X → Finset FSub := fun x =>
    Finset.univ.filter (fun S : FSub =>
      ∀ i : Fin m, block i ⊆ S.val → P i x.val ≠ mon (block i) x.val)
  have hhall : ∀ A : Finset X, A.card ≤ (A.biUnion nbr).card := by
    intro A
    let bad : Finset FSub := Finset.univ \ A.biUnion nbr
    let Iof : FSub → Finset (Fin m) := fun S =>
      Finset.univ.filter (fun i : Fin m => block i ⊆ S.val)
    let gFun : FSub → X → F := fun S x =>
      mon (S.val \ (Iof S).biUnion block) x.val *
        ∏ i ∈ Iof S, (mon (block i) x.val + P i x.val)
    have hg_lead : ∀ S : FSub, HasLeading free H base S (gFun S) := by
      intro S
      have hIsub : ∀ i ∈ Iof S, block i ⊆ free := by
        intro i hi
        exact Finset.Subset.trans (Finset.mem_filter.mp hi).2 S.2
      have hprod_lead := hasLeading_prod free H base block hdisj
        (fun i x => mon (block i) x.val + P i x.val) (Iof S) hIsub
        (fun i hi => hasLeading_mon_add_degLt free H base ⟨block i, hIsub i hi⟩ (hne i) (hP_deg i))
      let U : Finset (Fin k) := (Iof S).biUnion block
      have hU_sub : U ⊆ S.val := by
        refine Finset.biUnion_subset.mpr fun i hi => (Finset.mem_filter.mp hi).2
      let R : Finset (Fin k) := S.val \ U
      have hR_sub : R ⊆ free := Finset.Subset.trans Finset.sdiff_subset S.2
      have hR_lead := hasLeading_mon free H base ⟨R, hR_sub⟩
      have hRU_disj : Disjoint R U := Finset.sdiff_disjoint
      have hmul := hasLeading_mul free H base ⟨R, hR_sub⟩
        ⟨U, Finset.biUnion_subset.mpr hIsub⟩ hRU_disj hR_lead hprod_lead
      have hRU_eq : R ∪ U = S.val := Finset.sdiff_union_of_subset hU_sub
      have hsub_eq :
          (⟨R ∪ U, Finset.union_subset hR_sub (Finset.biUnion_subset.mpr hIsub)⟩ : FSub) = S :=
        Subtype.ext hRU_eq
      rw [hsub_eq] at hmul
      exact hmul
    have hg_zero : ∀ S ∈ bad, ∀ x ∈ A, gFun S x = 0 := by
      intro S hS x hx
      have hnotmem : S ∉ A.biUnion nbr := (Finset.mem_sdiff.mp hS).2
      have hnot_nbr : S ∉ nbr x := fun h => hnotmem (Finset.mem_biUnion.mpr ⟨x, hx, h⟩)
      have hex : ∃ i : Fin m, block i ⊆ S.val ∧ P i x.val = mon (block i) x.val := by
        simp only [nbr, Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_ne_iff] at hnot_nbr
        rcases hnot_nbr with ⟨i, hbi, heq⟩
        exact ⟨i, hbi, heq⟩
      rcases hex with ⟨i, hbi, heq⟩
      have hiI : i ∈ Iof S := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hbi⟩
      have hfac0 : mon (block i) x.val + P i x.val = 0 := by
        rw [heq, zmod2_add_self]
      have hprod0 : ∏ j ∈ Iof S, (mon (block j) x.val + P j x.val) = 0 :=
        Finset.prod_eq_zero hiI hfac0
      simp [gFun, hprod0]
    let cOf : FSub → FSub → F := fun S => Classical.choose (hg_lead S)
    have hcOf_diag : ∀ S : FSub, cOf S S = 1 := fun S => (Classical.choose_spec (hg_lead S)).1
    have hcOf_top : ∀ S T : FSub, S.val.card ≤ T.val.card → T ≠ S → cOf S T = 0 :=
      fun S => (Classical.choose_spec (hg_lead S)).2.1
    have hcOf_eval : ∀ S : FSub, ∀ x : X, gFun S x = evalPoly free (cOf S) x.val :=
      fun S => (Classical.choose_spec (hg_lead S)).2.2
    let phi : (bad → F) →ₗ[F] (X → F) :=
      { toFun := fun α x => ∑ S : bad, α S * gFun S.val x
        map_add' := fun α β => by
          funext x
          simp [Pi.add_apply, add_mul, Finset.sum_add_distrib]
        map_smul' := fun a α => by
          funext x
          simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc] }
    have hphi_inj : Function.Injective phi := by
      rw [injective_iff_map_eq_zero]
      intro α hα
      by_contra hneα
      have hsupp_ne : (Finset.univ.filter (fun S : bad => α S ≠ 0)).Nonempty := by
        by_contra hemp
        rw [Finset.not_nonempty_iff_eq_empty] at hemp
        apply hneα
        funext S
        by_contra h0
        have hmem : S ∈ Finset.univ.filter (fun S : bad => α S ≠ 0) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ S, h0⟩
        rw [hemp] at hmem
        exact Finset.notMem_empty S hmem
      obtain ⟨S₀, hS₀_mem, hS₀_max⟩ :=
        Finset.exists_max_image _ (fun S : bad => S.val.val.card) hsupp_ne
      have hαS₀ : α S₀ ≠ 0 := (Finset.mem_filter.mp hS₀_mem).2
      let totC : FSub → F := ∑ S : bad, α S • cOf S.val
      have htot_zero : ∀ x : X, evalPoly free totC x.val = 0 := by
        intro x
        rw [evalPoly_sum]
        have heq : (∑ S : bad, evalPoly free (α S • cOf S.val) x.val) = phi α x := by
          refine Finset.sum_congr rfl fun S _ => ?_
          rw [evalPoly_smul, ← hcOf_eval S.val x]
        rw [heq, hα]
        rfl
      have htotC0 : totC = 0 := evalPoly_inj free H base hsurj_X totC htot_zero
      have hval0 : totC S₀.val = 0 := congr_fun htotC0 S₀.val
      have hval : totC S₀.val = α S₀ := by
        change (∑ S : bad, α S • cOf S.val) S₀.val = α S₀
        rw [Finset.sum_apply]
        rw [Finset.sum_eq_single S₀]
        · simp [Pi.smul_apply, smul_eq_mul, hcOf_diag S₀.val]
        · intro S _ hneS
          by_cases hαS : α S = 0
          · simp [hαS]
          · have hmem : S ∈ Finset.univ.filter (fun S : bad => α S ≠ 0) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ S, hαS⟩
            have hle : S.val.val.card ≤ S₀.val.val.card := hS₀_max S hmem
            have hne_sub : S₀.val ≠ S.val := fun h => hneS (Subtype.ext h.symm)
            simp [Pi.smul_apply, smul_eq_mul, hcOf_top S.val S₀.val hle hne_sub]
        · intro h
          exact (h (Finset.mem_univ S₀)).elim
      rw [hval] at hval0
      exact hαS₀ hval0
    let psi : (X → F) →ₗ[F] (A → F) :=
      { toFun := fun f x => f x.val
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hpsi_surj : Function.Surjective psi := by
      intro h
      refine ⟨fun x => if hx : x ∈ A then h ⟨x, hx⟩ else 0, ?_⟩
      funext x
      simp [psi, x.2]
    have hcomp : ∀ α : bad → F, psi (phi α) = 0 := by
      intro α
      funext x
      change ∑ S : bad, α S * gFun S.val x.val = 0
      apply Finset.sum_eq_zero
      intro S _
      rw [hg_zero S.val S.2 x.val x.2, mul_zero]
    have hineq := card_add_card_le_card_of_exact phi psi hphi_inj hpsi_surj hcomp
    rw [Fintype.card_coe, Fintype.card_coe, hcard_XF] at hineq
    have hbad_card : bad.card + (A.biUnion nbr).card = Fintype.card FSub := by
      have h1 := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (A.biUnion nbr))
      simpa [bad, Finset.card_univ] using h1
    omega
  obtain ⟨f, hf_inj, hf_mem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective nbr).mp hhall
  have hf_bij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf_inj, hcard_XF⟩
  refine ⟨Equiv.ofBijective f hf_bij, ?_⟩
  intro x i hbi
  have hmem := hf_mem x
  simp only [nbr, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  exact hmem i hbi
