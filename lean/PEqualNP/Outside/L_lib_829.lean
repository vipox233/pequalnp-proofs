import PEqualNP.Defs

open scoped BigOperators

namespace PEqualNP.Outside.L_lib_829_aux

lemma zmod2_eq_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 := by
  fin_cases c
  · left; rfl
  · right; rfl

lemma zmod2_ne_iff_eq_add_one (a b : ZMod 2) : a ≠ b ↔ a = b + 1 := by
  revert a b
  decide

lemma zmod2_add_eq_iff (a b c : ZMod 2) : a + c = b ↔ a = b + c := by
  revert a b c
  decide

lemma zmod2_decide_eq_one_iff (c : ZMod 2) (b : Bool) :
    decide (c = 1) = b ↔ c = if b then 1 else 0 := by
  revert c b
  decide

lemma zmod2_decide_eq_iff (a b : ZMod 2) (r : Bool) :
    decide (a = b) = r ↔ a = if r then b else b + 1 := by
  revert a b r
  decide

lemma pi_eq_sum_single {m : ℕ} (x : Fin m → ZMod 2) :
    x = ∑ i : Fin m, x i • Pi.single i (1 : ZMod 2) := by
  ext j
  simp [Finset.sum_apply, Pi.single_apply]

lemma linearMap_pi_eq_dot {m : ℕ} (l : (Fin m → ZMod 2) →ₗ[ZMod 2] ZMod 2) :
    ∃ v : Fin m → ZMod 2, ∀ x, l x = dotProduct v x := by
  refine ⟨fun i => l (Pi.single i 1), fun x => ?_⟩
  conv_lhs => rw [pi_eq_sum_single x]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, dotProduct]
  refine Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma linearMap_prod_eq_dot {n k : ℕ}
    (l : ((Fin n → ZMod 2) × (Fin k → ZMod 2)) →ₗ[ZMod 2] ZMod 2) :
    ∃ (lx : Fin n → ZMod 2) (lu : Fin k → ZMod 2),
      ∀ z, l z = dotProduct lx z.1 + dotProduct lu z.2 := by
  obtain ⟨lx, hlx⟩ := linearMap_pi_eq_dot (l.comp (LinearMap.inl (ZMod 2) (Fin n → ZMod 2) (Fin k → ZMod 2)))
  obtain ⟨lu, hlu⟩ := linearMap_pi_eq_dot (l.comp (LinearMap.inr (ZMod 2) (Fin n → ZMod 2) (Fin k → ZMod 2)))
  refine ⟨lx, lu, fun z => ?_⟩
  have hz : z = (z.1, 0) + (0, z.2) := by
    ext <;> simp
  conv_lhs => rw [hz]
  rw [map_add]
  have h1 : l (z.1, 0) = dotProduct lx z.1 := hlx z.1
  have h2 : l (0, z.2) = dotProduct lu z.2 := hlu z.2
  rw [h1, h2]

def dotLinear {m : ℕ} (v : Fin m → ZMod 2) : (Fin m → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun x := dotProduct v x
  map_add' x y := dotProduct_add v x y
  map_smul' c x := by simp [dotProduct_smul]

lemma exists_functional_vanishing {E : Type} [AddCommGroup E] [Module (ZMod 2) E]
    (V : Submodule (ZMod 2) E) (w : E) (hw : w ∉ V) :
    ∃ ψ : E →ₗ[ZMod 2] ZMod 2, (∀ v ∈ V, ψ v = 0) ∧ ψ w = 1 := by
  set q : E ⧸ V := V.mkQ w
  have hq : q ≠ 0 := by
    intro h
    exact hw ((Submodule.Quotient.mk_eq_zero V).mp h)
  set L : Submodule (ZMod 2) (E ⧸ V) := Submodule.span (ZMod 2) {q}
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl L
  let proj : (E ⧸ V) →ₗ[ZMod 2] L := Submodule.projectionOnto L C hC
  let e : ZMod 2 ≃ₗ[ZMod 2] L := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) (E ⧸ V) q hq
  refine ⟨e.symm.toLinearMap.comp (proj.comp V.mkQ), ?_, ?_⟩
  · intro v hv
    have hmk : V.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero V).mpr hv
    simp [hmk]
  · have hmem : q ∈ L := Submodule.mem_span_singleton_self q
    have hproj : proj q = ⟨q, hmem⟩ := Submodule.projectionOnto_apply_left hC ⟨q, hmem⟩
    have he1 : e 1 = ⟨q, hmem⟩ := by
      ext
      simp [e, LinearEquiv.toSpanNonzeroSingleton]
    have hsymm : e.symm ⟨q, hmem⟩ = 1 := by
      rw [← he1]
      exact e.symm_apply_apply 1
    change e.symm (proj q) = 1
    rw [hproj, hsymm]

lemma exists_dot_orth_pi {m : ℕ} (V : Submodule (ZMod 2) (Fin m → ZMod 2))
    (w : Fin m → ZMod 2) (hw : w ∉ V) :
    ∃ d : Fin m → ZMod 2, (∀ v ∈ V, dotProduct v d = 0) ∧ dotProduct w d = 1 := by
  obtain ⟨ψ, hV, hw1⟩ := exists_functional_vanishing V w hw
  obtain ⟨d, hd⟩ := linearMap_pi_eq_dot ψ
  refine ⟨d, ?_, ?_⟩
  · intro v hv
    rw [dotProduct_comm, ← hd v]
    exact hV v hv
  · rw [dotProduct_comm, ← hd w]
    exact hw1

lemma exists_dot_orth_prod {n k : ℕ}
    (W : Submodule (ZMod 2) ((Fin n → ZMod 2) × (Fin k → ZMod 2)))
    (w : (Fin n → ZMod 2) × (Fin k → ZMod 2)) (hw : w ∉ W) :
    ∃ (dx : Fin n → ZMod 2) (du : Fin k → ZMod 2),
      (∀ z ∈ W, dotProduct z.1 dx + dotProduct z.2 du = 0) ∧
      dotProduct w.1 dx + dotProduct w.2 du = 1 := by
  obtain ⟨ψ, hW, hw1⟩ := exists_functional_vanishing W w hw
  obtain ⟨dx, du, hd⟩ := linearMap_prod_eq_dot ψ
  refine ⟨dx, du, ?_, ?_⟩
  · intro z hz
    rw [dotProduct_comm z.1 dx, dotProduct_comm z.2 du, ← hd z]
    exact hW z hz
  · rw [dotProduct_comm w.1 dx, dotProduct_comm w.2 du, ← hd w]
    exact hw1

def transposeMap {k t : ℕ} (M : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin t → ZMod 2)) :
    (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) where
  toFun y i := dotProduct y (M (Pi.single i 1))
  map_add' y₁ y₂ := by
    ext i
    simp [add_dotProduct]
  map_smul' c y := by
    ext i
    simp [smul_dotProduct]

lemma dot_transposeMap {k t : ℕ}
    (M : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin t → ZMod 2))
    (y : Fin t → ZMod 2) (u : Fin k → ZMod 2) :
    dotProduct (transposeMap M y) u = dotProduct y (M u) := by
  conv_rhs => rw [pi_eq_sum_single u]
  rw [map_sum, dotProduct_sum]
  simp only [dotProduct, transposeMap, LinearMap.coe_mk, AddHom.coe_mk]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma finrank_range_transposeMap {k t : ℕ}
    (M : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin t → ZMod 2)) :
    Module.finrank (ZMod 2) (LinearMap.range (transposeMap M)) =
      Module.finrank (ZMod 2) (LinearMap.range M) := by
  set d := Module.finrank (ZMod 2) (LinearMap.range M)
  let B : Module.Basis (Fin d) (ZMod 2) (LinearMap.range M) :=
    Module.finBasis (ZMod 2) (LinearMap.range M)
  let ev : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin d → ZMod 2) :=
    { toFun := fun y j => dotProduct y (B j).val
      map_add' := fun y₁ y₂ => by ext j; simp [add_dotProduct]
      map_smul' := fun c y => by ext j; simp [smul_dotProduct] }
  have hker : LinearMap.ker ev = LinearMap.ker (transposeMap M) := by
    ext y
    simp only [LinearMap.mem_ker, funext_iff, Pi.zero_apply]
    constructor
    · intro hy i
      have hmem : M (Pi.single i 1) ∈ LinearMap.range M := LinearMap.mem_range_self M _
      have hrepr : (⟨M (Pi.single i 1), hmem⟩ : LinearMap.range M) =
          ∑ j : Fin d, B.repr ⟨M (Pi.single i 1), hmem⟩ j • B j := (B.sum_repr _).symm
      have hval : M (Pi.single i 1) =
          ∑ j : Fin d, B.repr ⟨M (Pi.single i 1), hmem⟩ j • (B j).val := by
        have h := congrArg Subtype.val hrepr
        simp only [Submodule.coe_sum, SetLike.val_smul] at h
        exact h
      change dotProduct y (M (Pi.single i 1)) = 0
      rw [hval, dotProduct_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [dotProduct_smul, smul_eq_mul]
      have hj : dotProduct y (B j).val = 0 := hy j
      rw [hj, mul_zero]
    · intro hy j
      obtain ⟨u, hu⟩ := (B j).property
      change dotProduct y (B j).val = 0
      rw [← hu, ← dot_transposeMap]
      have h0 : transposeMap M y = 0 := funext hy
      rw [h0, zero_dotProduct]
  have hsurj : Function.Surjective ev := by
    have hbasis : ∀ j : Fin d, ∃ y : Fin t → ZMod 2, ev y = Pi.single j 1 := by
      intro j
      set Vj : Submodule (ZMod 2) (Fin t → ZMod 2) :=
        Submodule.span (ZMod 2) ((Finset.univ.erase j).image (fun j' : Fin d => (B j').val) : Set (Fin t → ZMod 2))
      have hnotmem : (B j).val ∉ Vj := by
        intro hmem
        have hli : LinearIndependent (ZMod 2) (fun j' : Fin d => (B j').val) :=
          B.linearIndependent.map' (Submodule.subtype _) (Submodule.ker_subtype _)
        have hnot := linearIndependent_iff_notMem_span.mp hli j
        apply hnot
        refine Submodule.span_mono ?_ hmem
        intro z hz
        simp only [Finset.coe_image, Finset.coe_erase, Finset.coe_univ, Set.mem_image,
          Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and] at hz ⊢
        exact hz
      obtain ⟨y, hVy, hyj⟩ := exists_dot_orth_pi Vj (B j).val hnotmem
      refine ⟨y, ?_⟩
      ext j'
      by_cases hjj' : j' = j
      · subst hjj'
        simpa [ev, dotProduct_comm] using hyj
      · have hmem : (B j').val ∈ Vj := by
          apply Submodule.subset_span
          simp only [Finset.coe_image, Finset.coe_erase, Finset.coe_univ, Set.mem_image,
            Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and]
          exact ⟨j', hjj', rfl⟩
        have h0 : dotProduct (B j').val y = 0 := hVy (B j').val hmem
        simpa [ev, hjj', dotProduct_comm] using h0
    choose ys hys using hbasis
    intro c
    refine ⟨∑ j : Fin d, c j • ys j, ?_⟩
    rw [map_sum]
    ext j'
    simp only [map_smul, hys, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    simp
  have hrange_ev : LinearMap.range ev = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hr1 : Module.finrank (ZMod 2) (LinearMap.range ev) +
      Module.finrank (ZMod 2) (LinearMap.ker ev) =
      Module.finrank (ZMod 2) (Fin t → ZMod 2) :=
    LinearMap.finrank_range_add_finrank_ker ev
  have hr2 : Module.finrank (ZMod 2) (LinearMap.range (transposeMap M)) +
      Module.finrank (ZMod 2) (LinearMap.ker (transposeMap M)) =
      Module.finrank (ZMod 2) (Fin t → ZMod 2) :=
    LinearMap.finrank_range_add_finrank_ker (transposeMap M)
  have htop : Module.finrank (ZMod 2) (LinearMap.range ev) = d := by
    rw [hrange_ev, finrank_top, Module.finrank_fin_fun]
  rw [htop, hker] at hr1
  omega

lemma finrank_sup_span_of_not_mem {E : Type} [AddCommGroup E] [Module (ZMod 2) E]
    [Module.Finite (ZMod 2) E]
    (V : Submodule (ZMod 2) E) (w : E) (hw : w ∉ V) :
    Module.finrank (ZMod 2) ↥(V ⊔ Submodule.span (ZMod 2) {w}) =
      Module.finrank (ZMod 2) V + 1 := by
  have hw0 : w ≠ 0 := fun h => hw (h ▸ V.zero_mem)
  have hinf : V ⊓ Submodule.span (ZMod 2) {w} = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rcases hx with ⟨hxV, hxS⟩
    rcases Submodule.mem_span_singleton.mp hxS with ⟨c, rfl⟩
    rcases zmod2_eq_zero_or_one c with rfl | rfl
    · simp
    · simp at hxV
      exact absurd hxV hw
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq V (Submodule.span (ZMod 2) {w})
  rw [hinf, finrank_bot, add_zero, finrank_span_singleton hw0] at hsum
  exact hsum

lemma finrank_sup_span_le {E : Type} [AddCommGroup E] [Module (ZMod 2) E]
    [Module.Finite (ZMod 2) E]
    (V : Submodule (ZMod 2) E) (w : E) :
    Module.finrank (ZMod 2) ↥(V ⊔ Submodule.span (ZMod 2) {w}) ≤
      Module.finrank (ZMod 2) V + 1 := by
  by_cases hw : w ∈ V
  · have hle : Submodule.span (ZMod 2) {w} ≤ V :=
      Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hw)
    rw [sup_eq_left.mpr hle]
    omega
  · rw [finrank_sup_span_of_not_mem V w hw]

lemma card_fiber_mul_pow_finrank {k t : ℕ}
    (M : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin t → ZMod 2)) (v : Fin t → ZMod 2) :
    (Finset.univ.filter (fun u : Fin k → ZMod 2 => M u = v)).card *
      2 ^ Module.finrank (ZMod 2) (LinearMap.range M) ≤
      Fintype.card (Fin k → ZMod 2) := by
  classical
  set F := Finset.univ.filter (fun u : Fin k → ZMod 2 => M u = v)
  by_cases hne : F.Nonempty
  · rcases hne with ⟨u₀, hu₀⟩
    have hMu₀ : M u₀ = v := (Finset.mem_filter.mp hu₀).2
    have hcardF : F.card = Fintype.card (LinearMap.ker M) := by
      let f : LinearMap.ker M → Fin k → ZMod 2 := fun w => u₀ + w.val
      have hfinj : Function.Injective f := by
        intro w₁ w₂ h
        exact Subtype.ext (add_left_cancel h)
      have himg : Finset.univ.image f = F := by
        ext u
        simp only [Finset.mem_image, Finset.mem_univ, true_and, F, Finset.mem_filter]
        constructor
        · rintro ⟨w, rfl⟩
          simp [f, map_add, hMu₀, LinearMap.mem_ker.mp w.property]
        · intro hMu
          have hmem : u - u₀ ∈ LinearMap.ker M := by
            simp [LinearMap.mem_ker, map_sub, hMu, hMu₀]
          refine ⟨⟨u - u₀, hmem⟩, ?_⟩
          simp [f]
      rw [← himg, Finset.card_image_of_injective _ hfinj, Finset.card_univ]
    rw [hcardF]
    have hker_card : Fintype.card (LinearMap.ker M) =
        2 ^ Module.finrank (ZMod 2) (LinearMap.ker M) := by
      have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := LinearMap.ker M)
      rw [h, ZMod.card]
    have hU_card : Fintype.card (Fin k → ZMod 2) =
        2 ^ Module.finrank (ZMod 2) (Fin k → ZMod 2) := by
      have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := Fin k → ZMod 2)
      rw [h, ZMod.card]
    have hrk := LinearMap.finrank_range_add_finrank_ker M
    rw [hker_card, hU_card, ← pow_add, add_comm, hrk]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp

def TreeShape (N J : Finset (List Bool)) : Prop :=
  [] ∈ N ∧ J ⊆ N ∧
  (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
  ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N

def Follows {V : Type} (q : List Bool → V → Bool) (p : List Bool) (x : V) : Prop :=
  ∀ j : Fin p.length, q (p.take j.val) x = p.get j

lemma shape_prefix_mem_J {N J : Finset (List Bool)} (hS : TreeShape N J)
    {p s : List Bool} (hmem : p ++ s ∈ N) (hne : s ≠ []) : p ∈ J := by
  induction s using List.reverseRecOn with
  | nil => exact absurd rfl hne
  | append_singleton s' b ih =>
    rw [← List.append_assoc] at hmem
    have hJ : p ++ s' ∈ J := hS.2.2.1 (p ++ s') b hmem
    cases s' with
    | nil => simpa using hJ
    | cons a t => exact ih (hS.2.1 hJ) (List.cons_ne_nil a t)

lemma shape_leaf_not_proper_prefix {N J : Finset (List Bool)} (hS : TreeShape N J)
    {p₁ p₂ s : List Bool} (hp₁ : p₁ ∈ N \ J) (hp₂ : p₂ ∈ N) (heq : p₁ ++ s = p₂) :
    s = [] := by
  by_contra hne
  have hJ : p₁ ∈ J := shape_prefix_mem_J hS (heq ▸ hp₂) hne
  exact (Finset.mem_sdiff.mp hp₁).2 hJ

lemma shape_leaf_prefix_eq {N J : Finset (List Bool)} (hS : TreeShape N J)
    {p₁ p₂ : List Bool} (hp₁ : p₁ ∈ N \ J) (hp₂ : p₂ ∈ N) (hpre : p₁ <+: p₂) :
    p₁ = p₂ := by
  rcases hpre with ⟨s, hs⟩
  have hnil := shape_leaf_not_proper_prefix hS hp₁ hp₂ hs
  subst hnil
  simpa using hs

lemma shape_leaf_append_inj {N J : Finset (List Bool)} (hS : TreeShape N J)
    {p₁ p₂ s₁ s₂ : List Bool} (hp₁ : p₁ ∈ N \ J) (hp₂ : p₂ ∈ N \ J)
    (heq : p₁ ++ s₁ = p₂ ++ s₂) : p₁ = p₂ ∧ s₁ = s₂ := by
  by_cases hle : p₁.length ≤ p₂.length
  · have hpre : p₁ <+: p₂ := by
      have htake := congrArg (List.take p₂.length) heq
      rw [List.take_left] at htake
      refine ⟨s₁.take (p₂.length - p₁.length), ?_⟩
      rw [List.take_append] at htake
      simpa [List.take_of_length_le hle] using htake
    have hp : p₁ = p₂ := shape_leaf_prefix_eq hS hp₁ (Finset.mem_sdiff.mp hp₂).1 hpre
    subst hp
    exact ⟨rfl, List.append_cancel_left heq⟩
  · have hle' : p₂.length ≤ p₁.length := by omega
    have hpre : p₂ <+: p₁ := by
      have htake := congrArg (List.take p₁.length) heq.symm
      rw [List.take_left] at htake
      refine ⟨s₂.take (p₁.length - p₂.length), ?_⟩
      rw [List.take_append] at htake
      simpa [List.take_of_length_le hle'] using htake
    have hp : p₂ = p₁ := shape_leaf_prefix_eq hS hp₂ (Finset.mem_sdiff.mp hp₁).1 hpre
    subst hp
    exact ⟨rfl, List.append_cancel_left heq⟩

lemma follows_nil {V : Type} (q : List Bool → V → Bool) (x : V) :
    Follows q [] x := by
  intro j
  exact Fin.elim0 j

lemma follows_append_singleton {V : Type} (q : List Bool → V → Bool)
    (p : List Bool) (b : Bool) (x : V) :
    Follows q (p ++ [b]) x ↔ Follows q p x ∧ q p x = b := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro j
      have hj : j.val < (p ++ [b]).length := by simp [Nat.lt_succ_of_lt j.isLt]
      have h1 := h ⟨j.val, hj⟩
      rw [List.take_append_of_le_length (le_of_lt j.isLt)] at h1
      have hget : (p ++ [b]).get ⟨j.val, hj⟩ = p.get j := by
        simp [List.getElem_append_left j.isLt]
      rw [hget] at h1
      exact h1
    · have hj : p.length < (p ++ [b]).length := by simp
      have h1 := h ⟨p.length, hj⟩
      rw [List.take_left] at h1
      have hget : (p ++ [b]).get ⟨p.length, hj⟩ = b := by
        simp
      rw [hget] at h1
      exact h1
  · rintro ⟨hp, hb⟩ j
    by_cases hlt : j.val < p.length
    · rw [List.take_append_of_le_length (le_of_lt hlt)]
      have hget : (p ++ [b]).get j = p.get ⟨j.val, hlt⟩ := by
        simp [List.getElem_append_left hlt]
      rw [hget]
      exact hp ⟨j.val, hlt⟩
    · have heq : j.val = p.length := by
        have hlen := j.isLt
        simp at hlen
        omega
      rw [heq, List.take_left]
      have hget : (p ++ [b]).get j = b := by
        simp [heq]
      rw [hget]
      exact hb

lemma follows_prefix {V : Type} (q : List Bool → V → Bool)
    {p p' : List Bool} (hpre : p <+: p') {x : V} (hf : Follows q p' x) :
    Follows q p x := by
  rcases hpre with ⟨s, rfl⟩
  induction s using List.reverseRecOn with
  | nil => simpa using hf
  | append_singleton s' b ih =>
    rw [← List.append_assoc] at hf
    exact ih ((follows_append_singleton q (p ++ s') b x).mp hf).1

def allLists (d : ℕ) : Finset (List Bool) :=
  (Finset.univ : Finset (Fin d → Bool)).image List.ofFn

lemma mem_allLists {d : ℕ} {s : List Bool} : s ∈ allLists d ↔ s.length = d := by
  simp only [allLists, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨f, rfl⟩
    simp
  · intro hlen
    refine ⟨fun j => s.get (j.cast hlen.symm), ?_⟩
    apply List.ext_get (by simp [hlen])
    intro i hi1 hi2
    simp

lemma card_allLists (d : ℕ) : (allLists d).card = 2 ^ d := by
  unfold allLists
  rw [Finset.card_image_of_injective _ List.ofFn_injective, Finset.card_univ,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

def prefixes (d : ℕ) : Finset (List Bool) :=
  (Finset.range (d + 1)).biUnion allLists

def strictPrefixes (d : ℕ) : Finset (List Bool) :=
  (Finset.range d).biUnion allLists

lemma mem_prefixes {d : ℕ} {s : List Bool} : s ∈ prefixes d ↔ s.length ≤ d := by
  simp only [prefixes, Finset.mem_biUnion, Finset.mem_range, mem_allLists]
  constructor
  · rintro ⟨m, hm, rfl⟩; omega
  · intro h; exact ⟨s.length, by omega, rfl⟩

lemma mem_strictPrefixes {d : ℕ} {s : List Bool} : s ∈ strictPrefixes d ↔ s.length < d := by
  simp only [strictPrefixes, Finset.mem_biUnion, Finset.mem_range, mem_allLists]
  constructor
  · rintro ⟨m, hm, rfl⟩; omega
  · intro h; exact ⟨s.length, h, rfl⟩

inductive PTree (X A : Type)
  | leaf (p : List Bool) (a : A)
  | node (f : X → Bool) (lo hi : PTree X A)

def PTree.nodes {X A : Type} : PTree X A → Finset (List Bool)
  | .leaf _ _ => {[]}
  | .node _ lo hi => insert [] ((lo.nodes.image (false :: ·)) ∪ (hi.nodes.image (true :: ·)))

def PTree.internal {X A : Type} : PTree X A → Finset (List Bool)
  | .leaf _ _ => ∅
  | .node _ lo hi => insert [] ((lo.internal.image (false :: ·)) ∪ (hi.internal.image (true :: ·)))

def PTree.leaves {X A : Type} : PTree X A → Finset (List Bool)
  | .leaf _ _ => {[]}
  | .node _ lo hi => (lo.leaves.image (false :: ·)) ∪ (hi.leaves.image (true :: ·))

def PTree.queryAt {X A : Type} : PTree X A → List Bool → (X → Bool)
  | .leaf _ _, _ => fun _ => false
  | .node f _ _, [] => f
  | .node _ lo _, false :: p => lo.queryAt p
  | .node _ _ hi, true :: p => hi.queryAt p

def PTree.outAt {X A : Type} : PTree X A → List Bool → A
  | .leaf _ a, _ => a
  | .node _ lo _, [] => lo.outAt []
  | .node _ lo _, false :: p => lo.outAt p
  | .node _ _ hi, true :: p => hi.outAt p

def PTree.leafSum {X A : Type} (w : A → ℕ) : PTree X A → ℕ
  | .leaf _ a => w a
  | .node _ lo hi => lo.leafSum w + hi.leafSum w

lemma PTree.nil_mem_nodes {X A : Type} (t : PTree X A) : [] ∈ t.nodes := by
  cases t <;> simp [PTree.nodes]

lemma PTree.internal_subset_nodes {X A : Type} (t : PTree X A) : t.internal ⊆ t.nodes := by
  induction t with
  | leaf _ _ => simp [PTree.internal]
  | node _ lo hi ihlo ihhi =>
    intro p hp
    simp only [PTree.internal, PTree.nodes, Finset.mem_insert, Finset.mem_union,
      Finset.mem_image] at hp ⊢
    rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · left; rfl
    · right; left; exact ⟨q, ihlo hq, rfl⟩
    · right; right; exact ⟨q, ihhi hq, rfl⟩

lemma PTree.shape {X A : Type} (t : PTree X A) : TreeShape t.nodes t.internal := by
  refine ⟨t.nil_mem_nodes, t.internal_subset_nodes, ?_, ?_⟩
  · induction t with
    | leaf _ _ =>
      intro p b hmem
      simp [PTree.nodes] at hmem
    | node _ lo hi ihlo ihhi =>
      intro p b hmem
      cases p with
      | nil => simp [PTree.internal]
      | cons c p' =>
        simp only [List.cons_append, PTree.nodes, Finset.mem_insert, Finset.mem_union,
          Finset.mem_image, List.cons_ne_nil, false_or] at hmem
        simp only [PTree.internal, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
        cases c
        · rcases hmem with ⟨q, hq, hEq⟩ | ⟨q, _, hEq⟩
          · injection hEq with _ hEq'
            subst hEq'
            right; left; exact ⟨p', ihlo p' b hq, rfl⟩
          · cases hEq
        · rcases hmem with ⟨q, _, hEq⟩ | ⟨q, hq, hEq⟩
          · cases hEq
          · injection hEq with _ hEq'
            subst hEq'
            right; right; exact ⟨p', ihhi p' b hq, rfl⟩
  · induction t with
    | leaf _ _ =>
      intro p hp
      simp [PTree.internal] at hp
    | node _ lo hi ihlo ihhi =>
      intro p hp
      simp only [PTree.internal, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp
      rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
      · constructor
        · simp only [List.nil_append, PTree.nodes, Finset.mem_insert, Finset.mem_union,
            Finset.mem_image]
          right; left; exact ⟨[], lo.nil_mem_nodes, rfl⟩
        · simp only [List.nil_append, PTree.nodes, Finset.mem_insert, Finset.mem_union,
            Finset.mem_image]
          right; right; exact ⟨[], hi.nil_mem_nodes, rfl⟩
      · rcases ihlo q hq with ⟨h1, h2⟩
        constructor
        · simp only [List.cons_append, PTree.nodes, Finset.mem_insert, Finset.mem_union,
            Finset.mem_image]
          right; left; exact ⟨q ++ [false], h1, rfl⟩
        · simp only [List.cons_append, PTree.nodes, Finset.mem_insert, Finset.mem_union,
            Finset.mem_image]
          right; left; exact ⟨q ++ [true], h2, rfl⟩
      · rcases ihhi q hq with ⟨h1, h2⟩
        constructor
        · simp only [List.cons_append, PTree.nodes, Finset.mem_insert, Finset.mem_union,
            Finset.mem_image]
          right; right; exact ⟨q ++ [false], h1, rfl⟩
        · simp only [List.cons_append, PTree.nodes, Finset.mem_insert, Finset.mem_union,
            Finset.mem_image]
          right; right; exact ⟨q ++ [true], h2, rfl⟩

lemma PTree.sdiff_eq_leaves {X A : Type} (t : PTree X A) : t.nodes \ t.internal = t.leaves := by
  induction t with
  | leaf _ _ => simp [PTree.nodes, PTree.internal, PTree.leaves]
  | node _ lo hi ihlo ihhi =>
    ext p
    simp only [Finset.mem_sdiff, PTree.nodes, PTree.internal, PTree.leaves,
      Finset.mem_insert, Finset.mem_union, Finset.mem_image]
    cases p with
    | nil => simp
    | cons b p' =>
      cases b
      · have hmem : p' ∈ lo.nodes \ lo.internal ↔ p' ∈ lo.leaves := by
          rw [ihlo]
        simp only [Finset.mem_sdiff] at hmem
        simpa [List.cons_ne_nil] using hmem
      · have hmem : p' ∈ hi.nodes \ hi.internal ↔ p' ∈ hi.leaves := by
          rw [ihhi]
        simp only [Finset.mem_sdiff] at hmem
        simpa [List.cons_ne_nil] using hmem

lemma PTree.sum_leaves_eq_leafSum {X A : Type} (w : A → ℕ) (t : PTree X A) :
    t.leaves.sum (fun p => w (t.outAt p)) = t.leafSum w := by
  induction t with
  | leaf _ a => simp [PTree.leaves, PTree.outAt, PTree.leafSum]
  | node _ lo hi ihlo ihhi =>
    simp only [PTree.leaves, PTree.leafSum]
    have hdisj : Disjoint (lo.leaves.image (false :: ·)) (hi.leaves.image (true :: ·)) := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [Finset.mem_image] at hp1 hp2
      rcases hp1 with ⟨q₁, _, rfl⟩
      rcases hp2 with ⟨q₂, _, hEq⟩
      cases hEq
    rw [Finset.sum_union hdisj,
      Finset.sum_image (fun a _ b _ h => List.cons.inj h |>.2),
      Finset.sum_image (fun a _ b _ h => List.cons.inj h |>.2)]
    simp only [PTree.outAt]
    rw [ihlo, ihhi]

lemma PTree.follows_node_cons {X A : Type} (f : X → Bool) (lo hi : PTree X A)
    (b : Bool) (p : List Bool) (x : X) :
    Follows (PTree.node f lo hi).queryAt (b :: p) x →
      f x = b ∧ Follows (if b then hi else lo).queryAt p x := by
  intro hf
  refine ⟨?_, ?_⟩
  · have h0 := hf ⟨0, by simp⟩
    simpa [PTree.queryAt] using h0
  · intro j
    have hj := hf ⟨j.val + 1, by simp [j.isLt]⟩
    cases b <;> simpa [PTree.queryAt] using hj

lemma exists_le_of_sum_le_mul {α : Type} [Fintype α] [Nonempty α] (f : α → ℕ) (K : ℕ)
    (hsum : ∑ a : α, f a ≤ K * Fintype.card α) : ∃ a : α, f a ≤ K := by
  by_contra h
  push Not at h
  have hge : ∑ a : α, (K + 1) ≤ ∑ a : α, f a :=
    Finset.sum_le_sum fun a _ => Nat.succ_le_of_lt (h a)
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm] at hge
  have hpos : 0 < Fintype.card α := Fintype.card_pos
  have hlt : K * Fintype.card α < (K + 1) * Fintype.card α := by
    rw [add_mul, one_mul]
    omega
  omega

lemma backward_dir (n k t : ℕ) (A : Type)
    (ok : (Fin n → ZMod 2) → A → Prop)
    (M : A → (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin t → ZMod 2))
    (H K : ℕ)
    (N J : Finset (List Bool))
    (q : List Bool → (Fin n → ZMod 2) → Bool)
    (out : List Bool → A)
    (hshape : TreeShape N J)
    (hq : ∀ p ∈ J, ∃ (l : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) (b : ZMod 2),
      q p = fun x => decide (l x = b))
    (hcert : ∀ p ∈ N \ J, ∀ x : Fin n → ZMod 2, Follows q p x → ok x (out p))
    (hH : ∀ p ∈ N \ J, p.length + Module.finrank (ZMod 2) (LinearMap.range (M (out p))) ≤ H)
    (hK : (N \ J).sum (fun p => 2 ^ Module.finrank (ZMod 2) (LinearMap.range (M (out p)))) ≤ K) :
    ∃ (N' J' : Finset (List Bool))
      (q' : List Bool → ((Fin n → ZMod 2) × (Fin k → ZMod 2)) → Bool)
      (out' : List Bool → A × (Fin t → ZMod 2)),
      TreeShape N' J' ∧
      (∀ p ∈ J', ∃ (l : ((Fin n → ZMod 2) × (Fin k → ZMod 2)) →ₗ[ZMod 2] ZMod 2) (b : ZMod 2),
        q' p = fun z => decide (l z = b)) ∧
      (∀ p ∈ N' \ J', ∀ z : (Fin n → ZMod 2) × (Fin k → ZMod 2),
        Follows q' p z → ok z.1 (out' p).1 ∧ (out' p).2 = M (out' p).1 z.2) ∧
      (∀ p ∈ N' \ J', p.length + 0 ≤ H) ∧
      (N' \ J').sum (fun _ => 1) ≤ K := by
  classical
  let X := Fin n → ZMod 2
  let U := Fin k → ZMod 2
  let Y := Fin t → ZMod 2
  let r : A → ℕ := fun a => Module.finrank (ZMod 2) (LinearMap.range (M a))
  let B : (a : A) → Module.Basis (Fin (r a)) (ZMod 2) (LinearMap.range (M a)) :=
    fun a => Module.finBasis (ZMod 2) (LinearMap.range (M a))
  let phi : (a : A) → Fin (r a) → U →ₗ[ZMod 2] ZMod 2 :=
    fun a j => ((LinearMap.proj (R := ZMod 2) j).comp (B a).equivFun.toLinearMap).comp (M a).rangeRestrict
  let recon : (a : A) → List Bool → Y :=
    fun a s => ((B a).equivFun.symm (fun j : Fin (r a) => if s.getD j.val false then 1 else 0)).val
  let N' : Finset (List Bool) :=
    N ∪ (N \ J).biUnion (fun p => (prefixes (r (out p))).image (p ++ ·))
  let J' : Finset (List Bool) :=
    J ∪ (N \ J).biUnion (fun p => (strictPrefixes (r (out p))).image (p ++ ·))
  let q' : List Bool → (X × U) → Bool := fun p' =>
    if p' ∈ J then fun z => q p' z.1
    else if h : ∃ p ∈ N \ J, ∃ s : List Bool, p' = p ++ s ∧ s.length < r (out p) then
      let p := Classical.choose h
      let hp := Classical.choose_spec h
      let s := Classical.choose hp.2
      let hs := Classical.choose_spec hp.2
      fun z => decide (phi (out p) ⟨s.length, hs.2⟩ z.2 = 1)
    else fun _ => false
  let out' : List Bool → A × Y := fun p' =>
    if h : ∃ p ∈ N \ J, ∃ s : List Bool, p' = p ++ s ∧ s.length = r (out p) then
      let p := Classical.choose h
      let hp := Classical.choose_spec h
      let s := Classical.choose hp.2
      (out p, recon (out p) s)
    else (out p', 0)
  have hdisj_append : ∀ {p : List Bool} {s : List Bool},
      p ∈ N \ J → s ≠ [] → p ++ s ∉ N := by
    intro p s hp hs hmem
    exact (Finset.mem_sdiff.mp hp).2 (shape_prefix_mem_J hshape hmem hs)
  have hshape' : TreeShape N' J' := by
    refine ⟨Finset.mem_union_left _ hshape.1, ?_, ?_, ?_⟩
    · intro p' hp'
      simp only [J', N', Finset.mem_union, Finset.mem_biUnion, Finset.mem_image] at hp' ⊢
      rcases hp' with hpJ | ⟨p, hp, s, hs, rfl⟩
      · left; exact hshape.2.1 hpJ
      · right
        refine ⟨p, hp, s, ?_, rfl⟩
        rw [mem_strictPrefixes] at hs
        rw [mem_prefixes]
        omega
    · intro p' b hmem
      simp only [N', J', Finset.mem_union, Finset.mem_biUnion, Finset.mem_image] at hmem ⊢
      rcases hmem with hN | ⟨p, hp, s, hs, heq⟩
      · left; exact hshape.2.2.1 p' b hN
      · cases s using List.reverseRecOn with
        | nil =>
          simp only [List.append_nil] at heq
          left
          exact hshape.2.2.1 p' b (heq ▸ (Finset.mem_sdiff.mp hp).1)
        | append_singleton s' b' =>
          rw [← List.append_assoc] at heq
          have hp' : p' = p ++ s' := (List.append_inj_left' heq (by simp)).symm
          rw [mem_prefixes] at hs
          simp only [List.length_append, List.length_singleton] at hs
          right
          exact ⟨p, hp, s', mem_strictPrefixes.mpr (by omega), hp'.symm⟩
    · intro p' hp'
      simp only [J', N', Finset.mem_union, Finset.mem_biUnion, Finset.mem_image] at hp' ⊢
      rcases hp' with hpJ | ⟨p, hp, s, hs, rfl⟩
      · rcases hshape.2.2.2 p' hpJ with ⟨h1, h2⟩
        exact ⟨Or.inl h1, Or.inl h2⟩
      · rw [mem_strictPrefixes] at hs
        constructor
        · right
          refine ⟨p, hp, s ++ [false], mem_prefixes.mpr (by simp; omega), by rw [List.append_assoc]⟩
        · right
          refine ⟨p, hp, s ++ [true], mem_prefixes.mpr (by simp; omega), by rw [List.append_assoc]⟩
  have hq' : ∀ p' ∈ J', ∃ (l : (X × U) →ₗ[ZMod 2] ZMod 2) (b : ZMod 2),
      q' p' = fun z => decide (l z = b) := by
    intro p' hp'
    by_cases hpJ : p' ∈ J
    · obtain ⟨l, b, hl⟩ := hq p' hpJ
      refine ⟨l.comp (LinearMap.fst (ZMod 2) X U), b, ?_⟩
      simp only [q', hpJ, ↓reduceIte, hl]
      rfl
    · simp only [J', Finset.mem_union, Finset.mem_biUnion, Finset.mem_image] at hp'
      rcases hp' with hpJ' | ⟨p, hp, s, hs, rfl⟩
      · exact absurd hpJ' hpJ
      · have hex : ∃ p₀ ∈ N \ J, ∃ s₀ : List Bool, p ++ s = p₀ ++ s₀ ∧ s₀.length < r (out p₀) :=
          ⟨p, hp, s, rfl, mem_strictPrefixes.mp hs⟩
        let p₀ := Classical.choose hex
        let hp₀ := Classical.choose_spec hex
        let s₀ := Classical.choose hp₀.2
        let hs₀ := Classical.choose_spec hp₀.2
        refine ⟨(phi (out p₀) ⟨s₀.length, hs₀.2⟩).comp (LinearMap.snd (ZMod 2) X U), 1, ?_⟩
        simp only [q', hpJ, ↓reduceIte, hex, ↓reduceDIte]
        rfl
  have hsdiff' : N' \ J' = (N \ J).biUnion (fun p => (allLists (r (out p))).image (p ++ ·)) := by
    ext p'
    rw [Finset.mem_sdiff]
    simp only [N', J', Finset.mem_union, Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨hN' | ⟨p, hp, s, hs, rfl⟩, hnotJ'⟩
      · push Not at hnotJ'
        have hp_leaf : p' ∈ N \ J := Finset.mem_sdiff.mpr ⟨hN', hnotJ'.1⟩
        have hr0 : r (out p') = 0 := by
          by_contra hne
          have hpos : 0 < r (out p') := Nat.pos_of_ne_zero hne
          exact hnotJ'.2 p' hp_leaf [] (mem_strictPrefixes.mpr (by simpa using hpos)) (by simp)
        exact ⟨p', hp_leaf, [], mem_allLists.mpr (by simp [hr0]), by simp⟩
      · push Not at hnotJ'
        rw [mem_prefixes] at hs
        have hge : r (out p) ≤ s.length := by
          by_contra hlt
          exact hnotJ'.2 p hp s (mem_strictPrefixes.mpr (by omega)) rfl
        exact ⟨p, hp, s, mem_allLists.mpr (by omega), rfl⟩
    · rintro ⟨p, hp, s, hs, rfl⟩
      rw [mem_allLists] at hs
      refine ⟨Or.inr ⟨p, hp, s, mem_prefixes.mpr (by omega), rfl⟩, ?_⟩
      rintro (hpJ | ⟨p₂, hp₂, s₂, hs₂, heq⟩)
      · cases s with
        | nil =>
          simp only [List.append_nil] at hpJ
          exact (Finset.mem_sdiff.mp hp).2 hpJ
        | cons b s' =>
          exact hdisj_append hp (List.cons_ne_nil b s') (hshape.2.1 hpJ)
      · obtain ⟨rfl, rfl⟩ := shape_leaf_append_inj hshape hp hp₂ heq.symm
        rw [mem_strictPrefixes] at hs₂
        omega
  have hcert' : ∀ p' ∈ N' \ J', ∀ z : X × U,
      Follows q' p' z → ok z.1 (out' p').1 ∧ (out' p').2 = M (out' p').1 z.2 := by
    intro p' hp' z hf
    rw [hsdiff', Finset.mem_biUnion] at hp'
    rcases hp' with ⟨p, hp, hp'img⟩
    rcases Finset.mem_image.mp hp'img with ⟨s, hs, rfl⟩
    rw [mem_allLists] at hs
    have hex_out : ∃ p₀ ∈ N \ J, ∃ s₀ : List Bool, p ++ s = p₀ ++ s₀ ∧ s₀.length = r (out p₀) :=
      ⟨p, hp, s, rfl, hs⟩
    have hout_eq : out' (p ++ s) = (out p, recon (out p) s) := by
      simp only [out', hex_out, ↓reduceDIte]
      set p₀ := Classical.choose hex_out
      have hp₀ := Classical.choose_spec hex_out
      set s₀ := Classical.choose hp₀.2
      have hs₀ := Classical.choose_spec hp₀.2
      obtain ⟨h1, h2⟩ := shape_leaf_append_inj hshape hp hp₀.1 hs₀.1
      change p = p₀ at h1
      change s = s₀ at h2
      change (out p₀, recon (out p₀) s₀) = (out p, recon (out p) s)
      rw [← h1, ← h2]
    rw [hout_eq]
    have hf_p : Follows q p z.1 := by
      intro j
      have hj : j.val < (p ++ s).length := by simp; omega
      have h1 := hf ⟨j.val, hj⟩
      rw [List.take_append_of_le_length (le_of_lt j.isLt)] at h1
      have hget : (p ++ s).get ⟨j.val, hj⟩ = p.get j := by
        simp [List.getElem_append_left j.isLt]
      rw [hget] at h1
      have htakeJ : p.take j.val ∈ J := by
        have hdecomp : p.take j.val ++ p.drop j.val = p := List.take_append_drop j.val p
        have hne : p.drop j.val ≠ [] := by
          intro hnil
          have := congrArg List.length hnil
          simp at this
          omega
        have hmemN : p.take j.val ++ p.drop j.val ∈ N := by
          rw [hdecomp]
          exact (Finset.mem_sdiff.mp hp).1
        exact shape_prefix_mem_J hshape hmemN hne
      simpa [q', htakeJ] using h1
    refine ⟨hcert p hp z.1 hf_p, ?_⟩
    have hcoords : ∀ j : Fin (r (out p)),
        (B (out p)).equivFun ⟨M (out p) z.2, LinearMap.mem_range_self _ _⟩ j =
          if s.getD j.val false then 1 else 0 := by
      intro j
      have hj : p.length + j.val < (p ++ s).length := by simp [hs, j.isLt]
      have h1 := hf ⟨p.length + j.val, hj⟩
      have htake : (p ++ s).take (p.length + j.val) = p ++ s.take j.val := by
        rw [List.take_append]
        simp
      rw [htake] at h1
      have hget : (p ++ s).get ⟨p.length + j.val, hj⟩ = s.getD j.val false := by
        have hlt : j.val < s.length := by omega
        simp [List.getElem_append_right (Nat.le_add_right p.length j.val),
          List.getD_eq_getElem?_getD, hlt]
      rw [hget] at h1
      have hnotJ : p ++ s.take j.val ∉ J := by
        cases hst : s.take j.val with
        | nil =>
          simp only [List.append_nil]
          exact (Finset.mem_sdiff.mp hp).2
        | cons b rest =>
          intro hJ
          exact hdisj_append hp (List.cons_ne_nil b rest) (hshape.2.1 hJ)
      have hex_q : ∃ p₀ ∈ N \ J, ∃ s₀ : List Bool,
          p ++ s.take j.val = p₀ ++ s₀ ∧ s₀.length < r (out p₀) := by
        refine ⟨p, hp, s.take j.val, rfl, ?_⟩
        rw [List.length_take]
        omega
      have hq_eq : q' (p ++ s.take j.val) z = decide (phi (out p) j z.2 = 1) := by
        simp only [q', hnotJ, ↓reduceIte, hex_q, ↓reduceDIte]
        set p₀ := Classical.choose hex_q
        have hp₀ := Classical.choose_spec hex_q
        set s₀ := Classical.choose hp₀.2
        have hs₀ := Classical.choose_spec hp₀.2
        obtain ⟨h1', h2'⟩ := shape_leaf_append_inj hshape hp hp₀.1 hs₀.1
        change p = p₀ at h1'
        change s.take j.val = s₀ at h2'
        have hlen_s : (s.take j.val).length = j.val := by
          rw [List.length_take]
          omega
        have hlen_eq : s₀.length = j.val := by
          rw [← h2', hlen_s]
        have hphi_eq : ∀ (a₁ a₂ : A) (h : a₁ = a₂) (j₁ : Fin (r a₁)) (j₂ : Fin (r a₂)),
            j₁.val = j₂.val → phi a₁ j₁ z.2 = phi a₂ j₂ z.2 := by
          intro a₁ a₂ h j₁ j₂ hj
          subst h
          rw [Fin.ext hj]
        exact congrArg (fun v => decide (v = 1))
          (hphi_eq _ _ (congrArg out h1'.symm) ⟨s₀.length, hs₀.2⟩ j hlen_eq)
      rw [hq_eq] at h1
      exact (zmod2_decide_eq_one_iff _ _).mp h1
    have hrepr_eq : (B (out p)).equivFun ⟨M (out p) z.2, LinearMap.mem_range_self _ _⟩ =
        fun j : Fin (r (out p)) => if s.getD j.val false then 1 else 0 :=
      funext hcoords
    have hsub : (⟨M (out p) z.2, LinearMap.mem_range_self _ _⟩ : LinearMap.range (M (out p))) =
        (B (out p)).equivFun.symm (fun j : Fin (r (out p)) => if s.getD j.val false then 1 else 0) := by
      rw [← hrepr_eq]
      exact ((B (out p)).equivFun.symm_apply_apply _).symm
    exact (congrArg Subtype.val hsub).symm
  have hH' : ∀ p' ∈ N' \ J', p'.length + 0 ≤ H := by
    intro p' hp'
    rw [hsdiff', Finset.mem_biUnion] at hp'
    rcases hp' with ⟨p, hp, hp'img⟩
    rcases Finset.mem_image.mp hp'img with ⟨s, hs, rfl⟩
    rw [mem_allLists] at hs
    have := hH p hp
    simp only [List.length_append, hs, add_zero]
    exact this
  have hK' : (N' \ J').sum (fun _ => 1) ≤ K := by
    rw [hsdiff', Finset.sum_const, smul_eq_mul, mul_one]
    have hpw : ((N \ J : Finset (List Bool)) : Set (List Bool)).PairwiseDisjoint
        (fun p => (allLists (r (out p))).image (p ++ ·)) := by
      intro p₁ hp₁ p₂ hp₂ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro p' h1 h2
      rcases Finset.mem_image.mp h1 with ⟨s₁, _, rfl⟩
      rcases Finset.mem_image.mp h2 with ⟨s₂, _, heq⟩
      exact hne (shape_leaf_append_inj hshape hp₁ hp₂ heq.symm).1
    rw [Finset.card_biUnion hpw]
    calc (N \ J).sum (fun p => ((allLists (r (out p))).image (p ++ ·)).card)
        = (N \ J).sum (fun p => (allLists (r (out p))).card) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          exact Finset.card_image_of_injective _ (fun _ _ h => List.append_cancel_left h)
      _ = (N \ J).sum (fun p => 2 ^ r (out p)) := by
          refine Finset.sum_congr rfl fun p _ => card_allLists (r (out p))
      _ ≤ K := hK
  exact ⟨N', J', q', out', hshape', hq', hcert', hH', hK'⟩

section Forward

variable {n k t : ℕ} {A : Type}
variable (ok : (Fin n → ZMod 2) → A → Prop)
variable (M : A → (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin t → ZMod 2))
variable (N J : Finset (List Bool))
variable (q : List Bool → ((Fin n → ZMod 2) × (Fin k → ZMod 2)) → Bool)
variable (out : List Bool → A × (Fin t → ZMod 2))
variable (lx : List Bool → Fin n → ZMod 2)
variable (lu : List Bool → Fin k → ZMod 2)
variable (qb : List Bool → ZMod 2)

def SectionSet (p : List Bool) (u : Fin k → ZMod 2) : Set (Fin n → ZMod 2) :=
  {x | Follows q p (x, u)}

def PathSpace (p : List Bool) :
    Submodule (ZMod 2) ((Fin n → ZMod 2) × (Fin k → ZMod 2)) :=
  Submodule.span (ZMod 2)
    (Set.range (fun j : Fin p.length => (lx (p.take j.val), lu (p.take j.val))))

def XSpace (p : List Bool) : Submodule (ZMod 2) (Fin n → ZMod 2) :=
  (PathSpace lx lu p).map (LinearMap.fst (ZMod 2) (Fin n → ZMod 2) (Fin k → ZMod 2))

lemma pathSpace_nil : PathSpace lx lu [] = ⊥ := by
  unfold PathSpace
  have h : Set.range (fun j : Fin ([] : List Bool).length => (lx ([].take j.val), lu ([].take j.val))) = ∅ := by
    ext z
    simp
  rw [h, Submodule.span_empty]

lemma xSpace_nil : XSpace lx lu [] = ⊥ := by
  unfold XSpace
  rw [pathSpace_nil, Submodule.map_bot]

lemma pathSpace_append_singleton (p : List Bool) (b : Bool) :
    PathSpace lx lu (p ++ [b]) =
      PathSpace lx lu p ⊔ Submodule.span (ZMod 2) {(lx p, lu p)} := by
  unfold PathSpace
  rw [← Submodule.span_union]
  congr 1
  ext z
  simp only [Set.mem_range, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, rfl⟩
    by_cases hlt : j.val < p.length
    · left
      refine ⟨⟨j.val, hlt⟩, ?_⟩
      rw [List.take_append_of_le_length (le_of_lt hlt)]
    · right
      have heq : j.val = p.length := by
        have := j.isLt
        simp at this
        omega
      rw [heq, List.take_left]
  · rintro (⟨j, rfl⟩ | rfl)
    · refine ⟨⟨j.val, by simp [Nat.lt_succ_of_lt j.isLt]⟩, ?_⟩
      rw [List.take_append_of_le_length (le_of_lt j.isLt)]
    · refine ⟨⟨p.length, by simp⟩, ?_⟩
      rw [List.take_left]

lemma xSpace_append_singleton (p : List Bool) (b : Bool) :
    XSpace lx lu (p ++ [b]) = XSpace lx lu p ⊔ Submodule.span (ZMod 2) {lx p} := by
  unfold XSpace
  rw [pathSpace_append_singleton, Submodule.map_sup, Submodule.map_span, Set.image_singleton]
  rfl

lemma finrank_pathSpace_le (p : List Bool) :
    Module.finrank (ZMod 2) (PathSpace lx lu p) ≤ p.length := by
  induction p using List.reverseRecOn with
  | nil =>
    rw [pathSpace_nil, finrank_bot]
    simp
  | append_singleton p b ih =>
    rw [pathSpace_append_singleton, List.length_append, List.length_singleton]
    exact le_trans (finrank_sup_span_le _ _) (Nat.add_le_add_right ih 1)

lemma lx_not_mem_xSpace_of_both_nonempty
    (hq_aff : ∀ p' ∈ J, q p' = fun z => decide (dotProduct (lx p') z.1 + dotProduct (lu p') z.2 = qb p'))
    (hshape : TreeShape N J)
    {p : List Bool} (hp : p ∈ J) {u : Fin k → ZMod 2}
    (hlo : (SectionSet q (p ++ [false]) u).Nonempty)
    (hhi : (SectionSet q (p ++ [true]) u).Nonempty) :
    lx p ∉ XSpace lx lu p := by
  rcases hlo with ⟨x₀, hx₀⟩
  rcases hhi with ⟨x₁, hx₁⟩
  rcases (follows_append_singleton q p false (x₀, u)).mp hx₀ with ⟨hf₀, hq₀⟩
  rcases (follows_append_singleton q p true (x₁, u)).mp hx₁ with ⟨hf₁, hq₁⟩
  have hdiff_orth : ∀ v ∈ XSpace lx lu p, dotProduct v (x₁ - x₀) = 0 := by
    intro v hv
    have hX : XSpace lx lu p =
        Submodule.span (ZMod 2) (Set.range (fun j : Fin p.length => lx (p.take j.val))) := by
      unfold XSpace PathSpace
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    rw [hX] at hv
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨j, rfl⟩
      have htakeJ : p.take j.val ∈ J := by
        have hdecomp : p.take j.val ++ p.drop j.val = p := List.take_append_drop j.val p
        have hne : p.drop j.val ≠ [] := by
          intro hnil
          have := congrArg List.length hnil
          simp at this
          omega
        have hmemN : p.take j.val ++ p.drop j.val ∈ N := by
          rw [hdecomp]
          exact hshape.2.1 hp
        exact shape_prefix_mem_J hshape hmemN hne
      have h0 := hf₀ j
      have h1 := hf₁ j
      rw [hq_aff _ htakeJ] at h0 h1
      have h0' := (zmod2_decide_eq_iff _ _ _).mp h0
      have h1' := (zmod2_decide_eq_iff _ _ _).mp h1
      have heq : dotProduct (lx (p.take j.val)) x₁ = dotProduct (lx (p.take j.val)) x₀ := by
        have hsum : dotProduct (lx (p.take j.val)) x₁ + dotProduct (lu (p.take j.val)) u =
            dotProduct (lx (p.take j.val)) x₀ + dotProduct (lu (p.take j.val)) u :=
          h1'.trans h0'.symm
        exact add_right_cancel hsum
      rw [dotProduct_sub, heq, sub_self]
    · simp
    · intro a b _ _ ha hb
      rw [add_dotProduct, ha, hb, add_zero]
    · intro c a _ ha
      rw [smul_dotProduct, ha, smul_zero]
  intro hmem
  have h0 : dotProduct (lx p) (x₁ - x₀) = 0 := hdiff_orth (lx p) hmem
  rw [dotProduct_sub, sub_eq_zero] at h0
  rw [hq_aff p hp] at hq₀ hq₁
  simp only at hq₀ hq₁
  rw [h0] at hq₁
  rw [hq₀] at hq₁
  cases hq₁

lemma finrank_xSpace_add_rank_le
    (hq_aff : ∀ p' ∈ J, q p' = fun z => decide (dotProduct (lx p') z.1 + dotProduct (lu p') z.2 = qb p'))
    (hshape : TreeShape N J)
    (hcert : ∀ p' ∈ N \ J, ∀ z : (Fin n → ZMod 2) × (Fin k → ZMod 2),
      Follows q p' z → ok z.1 (out p').1 ∧ (out p').2 = M (out p').1 z.2)
    {p : List Bool} (hp : p ∈ N \ J) {u : Fin k → ZMod 2}
    (hne : (SectionSet q p u).Nonempty) :
    Module.finrank (ZMod 2) (XSpace lx lu p) +
      Module.finrank (ZMod 2) (LinearMap.range (M (out p).1)) ≤ p.length := by
  rcases hne with ⟨x₀, hx₀⟩
  set a := (out p).1
  set f : PathSpace lx lu p →ₗ[ZMod 2] (Fin n → ZMod 2) :=
    (LinearMap.fst (ZMod 2) (Fin n → ZMod 2) (Fin k → ZMod 2)).domRestrict (PathSpace lx lu p)
  have hrange_f : LinearMap.range f = XSpace lx lu p := LinearMap.range_domRestrict _ _
  have hrk_f := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange_f] at hrk_f
  have hmem_W : ∀ y : Fin t → ZMod 2, ((0 : Fin n → ZMod 2), transposeMap (M a) y) ∈ PathSpace lx lu p := by
    intro y
    by_contra hnot
    obtain ⟨dx, du, horth, hdot1⟩ := exists_dot_orth_prod (PathSpace lx lu p) (0, transposeMap (M a) y) hnot
    have hdot_u : dotProduct (transposeMap (M a) y) du = 1 := by
      simpa using hdot1
    have hMdu_ne : M a du ≠ 0 := by
      intro h0
      rw [dot_transposeMap, h0, dotProduct_zero] at hdot_u
      exact zero_ne_one hdot_u
    have hf1 : Follows q p (x₀ + dx, u + du) := by
      intro j
      have htakeJ : p.take j.val ∈ J := by
        have hdecomp : p.take j.val ++ p.drop j.val = p := List.take_append_drop j.val p
        have hne' : p.drop j.val ≠ [] := by
          intro hnil
          have := congrArg List.length hnil
          simp at this
          omega
        have hmemN : p.take j.val ++ p.drop j.val ∈ N := by
          rw [hdecomp]
          exact (Finset.mem_sdiff.mp hp).1
        exact shape_prefix_mem_J hshape hmemN hne'
      have hgen : (lx (p.take j.val), lu (p.take j.val)) ∈ PathSpace lx lu p :=
        Submodule.subset_span ⟨j, rfl⟩
      have h0 := horth _ hgen
      have hdot_eq : dotProduct (lx (p.take j.val)) (x₀ + dx) + dotProduct (lu (p.take j.val)) (u + du) =
          dotProduct (lx (p.take j.val)) x₀ + dotProduct (lu (p.take j.val)) u := by
        rw [dotProduct_add, dotProduct_add]
        have hre : (dotProduct (lx (p.take j.val)) x₀ + dotProduct (lx (p.take j.val)) dx) +
            (dotProduct (lu (p.take j.val)) u + dotProduct (lu (p.take j.val)) du) =
            (dotProduct (lx (p.take j.val)) x₀ + dotProduct (lu (p.take j.val)) u) +
            (dotProduct (lx (p.take j.val)) dx + dotProduct (lu (p.take j.val)) du) := by ring
        rw [hre, h0, add_zero]
      have horig := hx₀ j
      rw [hq_aff _ htakeJ] at horig ⊢
      change decide (dotProduct (lx (p.take j.val)) (x₀ + dx) +
        dotProduct (lu (p.take j.val)) (u + du) = qb (p.take j.val)) = p.get j
      rw [hdot_eq]
      exact horig
    have hc0 := (hcert p hp (x₀, u) hx₀).2
    have hc1 := (hcert p hp (x₀ + dx, u + du) hf1).2
    have hsum : M a u = M a u + M a du := by
      simpa [map_add] using hc0.symm.trans hc1
    have hMdu0 : M a du = 0 := by
      have := congrArg (fun z => z - M a u) hsum
      simpa using this.symm
    exact hMdu_ne hMdu0
  let Ksub : Submodule (ZMod 2) ((Fin n → ZMod 2) × (Fin k → ZMod 2)) :=
    PathSpace lx lu p ⊓ LinearMap.ker (LinearMap.fst (ZMod 2) (Fin n → ZMod 2) (Fin k → ZMod 2))
  let eK : Ksub ≃ₗ[ZMod 2] LinearMap.ker f :=
    { toFun := fun z => ⟨⟨z.val, z.property.1⟩, z.property.2⟩
      invFun := fun z => ⟨z.val.val, ⟨z.val.property, z.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let g : (Fin t → ZMod 2) →ₗ[ZMod 2] ((Fin n → ZMod 2) × (Fin k → ZMod 2)) :=
    (LinearMap.inr (ZMod 2) (Fin n → ZMod 2) (Fin k → ZMod 2)).comp (transposeMap (M a))
  have hrange_g_le : LinearMap.range g ≤ Ksub := by
    rintro z ⟨y, rfl⟩
    exact ⟨hmem_W y, by simp [g]⟩
  have hker_g : LinearMap.ker g = LinearMap.ker (transposeMap (M a)) := by
    ext y
    simp [g, LinearMap.mem_ker]
  have hfin_g : Module.finrank (ZMod 2) (LinearMap.range g) =
      Module.finrank (ZMod 2) (LinearMap.range (transposeMap (M a))) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker g
    have h2 := LinearMap.finrank_range_add_finrank_ker (transposeMap (M a))
    rw [hker_g] at h1
    omega
  have hle_ker : Module.finrank (ZMod 2) (LinearMap.range (transposeMap (M a))) ≤
      Module.finrank (ZMod 2) (LinearMap.ker f) := by
    rw [← hfin_g, ← LinearEquiv.finrank_eq eK]
    exact Submodule.finrank_mono hrange_g_le
  rw [finrank_range_transposeMap] at hle_ker
  have hle_len := finrank_pathSpace_le lx lu p
  omega

open Classical in
noncomputable def pruneTree (u : Fin k → ZMod 2) : ℕ → List Bool → PTree (Fin n → ZMod 2) A
  | 0, p => PTree.leaf p (out p).1
  | fuel + 1, p =>
    if p ∈ J then
      if (SectionSet q (p ++ [false]) u).Nonempty then
        if (SectionSet q (p ++ [true]) u).Nonempty then
          PTree.node (fun x => q p (x, u))
            (pruneTree u fuel (p ++ [false]))
            (pruneTree u fuel (p ++ [true]))
        else
          pruneTree u fuel (p ++ [false])
      else
        pruneTree u fuel (p ++ [true])
    else
      PTree.leaf p (out p).1

lemma pruneTree_queries
    (hq_aff : ∀ p' ∈ J, q p' = fun z => decide (dotProduct (lx p') z.1 + dotProduct (lu p') z.2 = qb p'))
    (u : Fin k → ZMod 2) (fuel : ℕ) (p : List Bool) :
    ∀ s ∈ (pruneTree J q out u fuel p).internal,
      ∃ (l : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) (b : ZMod 2),
        (pruneTree J q out u fuel p).queryAt s = fun x => decide (l x = b) := by
  induction fuel generalizing p with
  | zero =>
    intro s hs
    simp [pruneTree, PTree.internal] at hs
  | succ fuel ih =>
    unfold pruneTree
    by_cases hpJ : p ∈ J
    · simp only [hpJ, ↓reduceIte]
      by_cases hlo : (SectionSet q (p ++ [false]) u).Nonempty
      · simp only [hlo, ↓reduceIte]
        by_cases hhi : (SectionSet q (p ++ [true]) u).Nonempty
        · simp only [hhi, ↓reduceIte]
          intro s hs
          cases s with
          | nil =>
            refine ⟨dotLinear (lx p), qb p + dotProduct (lu p) u, ?_⟩
            ext x
            simp only [PTree.queryAt, hq_aff p hpJ, dotLinear, LinearMap.coe_mk, AddHom.coe_mk]
            exact decide_eq_decide.mpr (zmod2_add_eq_iff _ _ _)
          | cons b s' =>
            simp only [PTree.internal, Finset.mem_insert, Finset.mem_union, Finset.mem_image,
              List.cons_ne_nil, false_or] at hs
            cases b
            · rcases hs with ⟨r, hr, hEq⟩ | ⟨r, _, hEq⟩
              · injection hEq with _ hEq'
                subst hEq'
                simpa [PTree.queryAt] using ih (p ++ [false]) r hr
              · cases hEq
            · rcases hs with ⟨r, _, hEq⟩ | ⟨r, hr, hEq⟩
              · cases hEq
              · injection hEq with _ hEq'
                subst hEq'
                simpa [PTree.queryAt] using ih (p ++ [true]) r hr
        · simp only [hhi, ↓reduceIte]
          exact ih (p ++ [false])
      · simp only [hlo, ↓reduceIte]
        exact ih (p ++ [true])
    · simp only [hpJ, ↓reduceIte]
      intro s hs
      simp [PTree.internal] at hs

lemma pruneTree_correct
    (hshape : TreeShape N J)
    (hcert : ∀ p' ∈ N \ J, ∀ z : (Fin n → ZMod 2) × (Fin k → ZMod 2),
      Follows q p' z → ok z.1 (out p').1 ∧ (out p').2 = M (out p').1 z.2)
    (u : Fin k → ZMod 2) (fuel : ℕ) :
    ∀ p ∈ N, N.sup List.length - p.length ≤ fuel →
      ∀ s ∈ (pruneTree J q out u fuel p).leaves,
        ∀ x : Fin n → ZMod 2,
          x ∈ SectionSet q p u →
          Follows (pruneTree J q out u fuel p).queryAt s x →
          ok x ((pruneTree J q out u fuel p).outAt s) := by
  induction fuel with
  | zero =>
    intro p hp hfuel s hs x hx _
    have hnotJ : p ∉ J := by
      intro hpJ
      have hchild : p ++ [false] ∈ N := (hshape.2.2.2 p hpJ).1
      have hle : (p ++ [false]).length ≤ N.sup List.length := Finset.le_sup (f := List.length) hchild
      simp only [List.length_append, List.length_singleton] at hle
      omega
    have hleaf : p ∈ N \ J := Finset.mem_sdiff.mpr ⟨hp, hnotJ⟩
    simpa [pruneTree, PTree.outAt] using (hcert p hleaf (x, u) hx).1
  | succ fuel ih =>
    intro p hp hfuel s hs x hx hf
    unfold pruneTree at hs hf ⊢
    by_cases hpJ : p ∈ J
    · simp only [hpJ, ↓reduceIte] at hs hf ⊢
      have hc0 : p ++ [false] ∈ N := (hshape.2.2.2 p hpJ).1
      have hc1 : p ++ [true] ∈ N := (hshape.2.2.2 p hpJ).2
      have hf0 : N.sup List.length - (p ++ [false]).length ≤ fuel := by
        simp only [List.length_append, List.length_singleton]
        omega
      have hf1 : N.sup List.length - (p ++ [true]).length ≤ fuel := by
        simp only [List.length_append, List.length_singleton]
        omega
      by_cases hlo : (SectionSet q (p ++ [false]) u).Nonempty
      · simp only [hlo, ↓reduceIte] at hs hf ⊢
        by_cases hhi : (SectionSet q (p ++ [true]) u).Nonempty
        · simp only [hhi, ↓reduceIte] at hs hf ⊢
          cases s with
          | nil => simp [PTree.leaves] at hs
          | cons b s' =>
            obtain ⟨hb, hf'⟩ := PTree.follows_node_cons _ _ _ b s' x hf
            have hx' : x ∈ SectionSet q (p ++ [b]) u :=
              (follows_append_singleton q p b (x, u)).mpr ⟨hx, hb⟩
            cases b
            · have hs' : s' ∈ (pruneTree J q out u fuel (p ++ [false])).leaves := by
                simp only [PTree.leaves, Finset.mem_union, Finset.mem_image] at hs
                rcases hs with ⟨r, hr, hEq⟩ | ⟨r, _, hEq⟩
                · injection hEq with _ hEq'
                  subst hEq'
                  exact hr
                · cases hEq
              simpa [PTree.outAt] using ih (p ++ [false]) hc0 hf0 s' hs' x hx' hf'
            · have hs' : s' ∈ (pruneTree J q out u fuel (p ++ [true])).leaves := by
                simp only [PTree.leaves, Finset.mem_union, Finset.mem_image] at hs
                rcases hs with ⟨r, _, hEq⟩ | ⟨r, hr, hEq⟩
                · cases hEq
                · injection hEq with _ hEq'
                  subst hEq'
                  exact hr
              simpa [PTree.outAt] using ih (p ++ [true]) hc1 hf1 s' hs' x hx' hf'
        · simp only [hhi, ↓reduceIte] at hs hf ⊢
          have hqf : q p (x, u) = false := by
            cases hqval : q p (x, u)
            · rfl
            · exfalso
              exact hhi ⟨x, (follows_append_singleton q p true (x, u)).mpr ⟨hx, hqval⟩⟩
          have hx' : x ∈ SectionSet q (p ++ [false]) u :=
            (follows_append_singleton q p false (x, u)).mpr ⟨hx, hqf⟩
          exact ih (p ++ [false]) hc0 hf0 s hs x hx' hf
      · simp only [hlo, ↓reduceIte] at hs hf ⊢
        have hqt : q p (x, u) = true := by
          cases hqval : q p (x, u)
          · exfalso
            exact hlo ⟨x, (follows_append_singleton q p false (x, u)).mpr ⟨hx, hqval⟩⟩
          · rfl
        have hx' : x ∈ SectionSet q (p ++ [true]) u :=
          (follows_append_singleton q p true (x, u)).mpr ⟨hx, hqt⟩
        exact ih (p ++ [true]) hc1 hf1 s hs x hx' hf
    · simp only [hpJ, ↓reduceIte] at hs hf ⊢
      have hleaf : p ∈ N \ J := Finset.mem_sdiff.mpr ⟨hp, hpJ⟩
      simpa [PTree.outAt] using (hcert p hleaf (x, u) hx).1

lemma pruneTree_depth
    (hq_aff : ∀ p' ∈ J, q p' = fun z => decide (dotProduct (lx p') z.1 + dotProduct (lu p') z.2 = qb p'))
    (hshape : TreeShape N J)
    (hcert : ∀ p' ∈ N \ J, ∀ z : (Fin n → ZMod 2) × (Fin k → ZMod 2),
      Follows q p' z → ok z.1 (out p').1 ∧ (out p').2 = M (out p').1 z.2)
    {H : ℕ} (hH : ∀ p' ∈ N \ J, p'.length ≤ H)
    (u : Fin k → ZMod 2) (fuel : ℕ) :
    ∀ p ∈ N, N.sup List.length - p.length ≤ fuel →
      (SectionSet q p u).Nonempty →
      ∀ s ∈ (pruneTree J q out u fuel p).leaves,
        s.length + Module.finrank (ZMod 2) (XSpace lx lu p) +
          Module.finrank (ZMod 2) (LinearMap.range (M ((pruneTree J q out u fuel p).outAt s))) ≤ H := by
  induction fuel with
  | zero =>
    intro p hp hfuel hne s hs
    have hnotJ : p ∉ J := by
      intro hpJ
      have hchild : p ++ [false] ∈ N := (hshape.2.2.2 p hpJ).1
      have hle : (p ++ [false]).length ≤ N.sup List.length := Finset.le_sup (f := List.length) hchild
      simp only [List.length_append, List.length_singleton] at hle
      omega
    have hleaf : p ∈ N \ J := Finset.mem_sdiff.mpr ⟨hp, hnotJ⟩
    have hs_nil : s = [] := by simpa [pruneTree, PTree.leaves] using hs
    subst hs_nil
    have h1 := finrank_xSpace_add_rank_le ok M N J q out lx lu qb hq_aff hshape hcert hleaf hne
    have h2 := hH p hleaf
    simp only [pruneTree, PTree.outAt, List.length_nil, zero_add]
    exact le_trans h1 h2
  | succ fuel ih =>
    intro p hp hfuel hne s hs
    by_cases hpJ : p ∈ J
    · have hc0 : p ++ [false] ∈ N := (hshape.2.2.2 p hpJ).1
      have hc1 : p ++ [true] ∈ N := (hshape.2.2.2 p hpJ).2
      have hf0 : N.sup List.length - (p ++ [false]).length ≤ fuel := by
        simp only [List.length_append, List.length_singleton]
        omega
      have hf1 : N.sup List.length - (p ++ [true]).length ≤ fuel := by
        simp only [List.length_append, List.length_singleton]
        omega
      by_cases hlo : (SectionSet q (p ++ [false]) u).Nonempty
      · by_cases hhi : (SectionSet q (p ++ [true]) u).Nonempty
        · have htree : pruneTree J q out u (fuel + 1) p =
              PTree.node (fun x => q p (x, u))
                (pruneTree J q out u fuel (p ++ [false]))
                (pruneTree J q out u fuel (p ++ [true])) := by
            rw [pruneTree]
            simp only [hpJ, hlo, hhi, ↓reduceIte]
          rw [htree] at hs ⊢
          have hnotmem := lx_not_mem_xSpace_of_both_nonempty N J q lx lu qb hq_aff hshape hpJ hlo hhi
          have hstep : ∀ b : Bool,
              Module.finrank (ZMod 2) (XSpace lx lu (p ++ [b])) =
                Module.finrank (ZMod 2) (XSpace lx lu p) + 1 := by
            intro b
            rw [xSpace_append_singleton]
            exact finrank_sup_span_of_not_mem _ _ hnotmem
          cases s with
          | nil => simp [PTree.leaves] at hs
          | cons b s' =>
            cases b
            · have hs' : s' ∈ (pruneTree J q out u fuel (p ++ [false])).leaves := by
                simp only [PTree.leaves, Finset.mem_union, Finset.mem_image] at hs
                rcases hs with ⟨r, hr, hEq⟩ | ⟨r, _, hEq⟩
                · injection hEq with _ hEq'
                  subst hEq'
                  exact hr
                · cases hEq
              have hih := ih (p ++ [false]) hc0 hf0 hlo s' hs'
              rw [hstep false] at hih
              have hout : (PTree.node (fun x => q p (x, u))
                  (pruneTree J q out u fuel (p ++ [false]))
                  (pruneTree J q out u fuel (p ++ [true]))).outAt (false :: s') =
                  (pruneTree J q out u fuel (p ++ [false])).outAt s' := rfl
              rw [hout]
              simp only [List.length_cons]
              omega
            · have hs' : s' ∈ (pruneTree J q out u fuel (p ++ [true])).leaves := by
                simp only [PTree.leaves, Finset.mem_union, Finset.mem_image] at hs
                rcases hs with ⟨r, _, hEq⟩ | ⟨r, hr, hEq⟩
                · cases hEq
                · injection hEq with _ hEq'
                  subst hEq'
                  exact hr
              have hih := ih (p ++ [true]) hc1 hf1 hhi s' hs'
              rw [hstep true] at hih
              have hout : (PTree.node (fun x => q p (x, u))
                  (pruneTree J q out u fuel (p ++ [false]))
                  (pruneTree J q out u fuel (p ++ [true]))).outAt (true :: s') =
                  (pruneTree J q out u fuel (p ++ [true])).outAt s' := rfl
              rw [hout]
              simp only [List.length_cons]
              omega
        · have htree : pruneTree J q out u (fuel + 1) p = pruneTree J q out u fuel (p ++ [false]) := by
            rw [pruneTree]
            simp only [hpJ, hlo, hhi, ↓reduceIte]
          rw [htree] at hs ⊢
          have hih := ih (p ++ [false]) hc0 hf0 hlo s hs
          have hmono : Module.finrank (ZMod 2) (XSpace lx lu p) ≤
              Module.finrank (ZMod 2) (XSpace lx lu (p ++ [false])) := by
            rw [xSpace_append_singleton]
            exact Submodule.finrank_mono le_sup_left
          omega
      · have htree : pruneTree J q out u (fuel + 1) p = pruneTree J q out u fuel (p ++ [true]) := by
          rw [pruneTree]
          simp only [hpJ, hlo, ↓reduceIte]
        rw [htree] at hs ⊢
        have hhi : (SectionSet q (p ++ [true]) u).Nonempty := by
          rcases hne with ⟨x, hx⟩
          cases hqv : q p (x, u)
          · exfalso
            exact hlo ⟨x, (follows_append_singleton q p false (x, u)).mpr ⟨hx, hqv⟩⟩
          · exact ⟨x, (follows_append_singleton q p true (x, u)).mpr ⟨hx, hqv⟩⟩
        have hih := ih (p ++ [true]) hc1 hf1 hhi s hs
        have hmono : Module.finrank (ZMod 2) (XSpace lx lu p) ≤
            Module.finrank (ZMod 2) (XSpace lx lu (p ++ [true])) := by
          rw [xSpace_append_singleton]
          exact Submodule.finrank_mono le_sup_left
        omega
    · have htree : pruneTree J q out u (fuel + 1) p = PTree.leaf p (out p).1 := by
        rw [pruneTree]
        simp only [hpJ, ↓reduceIte]
      rw [htree] at hs ⊢
      have hleaf : p ∈ N \ J := Finset.mem_sdiff.mpr ⟨hp, hpJ⟩
      have hs_nil : s = [] := by simpa [PTree.leaves] using hs
      subst hs_nil
      have h1 := finrank_xSpace_add_rank_le ok M N J q out lx lu qb hq_aff hshape hcert hleaf hne
      have h2 := hH p hleaf
      have hout : (PTree.leaf p (out p).1 : PTree (Fin n → ZMod 2) A).outAt [] = (out p).1 := rfl
      rw [hout]
      simp only [List.length_nil, zero_add]
      exact le_trans h1 h2

open Classical in
lemma pruneTree_leafSum
    (hshape : TreeShape N J) (w : A → ℕ) (u : Fin k → ZMod 2) (fuel : ℕ) :
    ∀ p ∈ N, N.sup List.length - p.length ≤ fuel →
      (SectionSet q p u).Nonempty →
      (pruneTree J q out u fuel p).leafSum w =
        ((N \ J).filter (fun p' => p <+: p' ∧ (SectionSet q p' u).Nonempty)).sum
          (fun p' => w (out p').1) := by
  classical
  induction fuel with
  | zero =>
    intro p hp hfuel hne
    have hnotJ : p ∉ J := by
      intro hpJ
      have hchild : p ++ [false] ∈ N := (hshape.2.2.2 p hpJ).1
      have hle : (p ++ [false]).length ≤ N.sup List.length := Finset.le_sup (f := List.length) hchild
      simp only [List.length_append, List.length_singleton] at hle
      omega
    have hleaf : p ∈ N \ J := Finset.mem_sdiff.mpr ⟨hp, hnotJ⟩
    have hfilt : (N \ J).filter (fun p' => p <+: p' ∧ (SectionSet q p' u).Nonempty) = {p} := by
      ext p'
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hp', hpre, _⟩
        exact (shape_leaf_prefix_eq hshape hleaf (Finset.mem_sdiff.mp hp').1 hpre).symm
      · rintro rfl
        exact ⟨hleaf, List.prefix_refl _, hne⟩
    rw [hfilt]
    simp [pruneTree, PTree.leafSum]
  | succ fuel ih =>
    intro p hp hfuel hne
    unfold pruneTree
    by_cases hpJ : p ∈ J
    · simp only [hpJ, ↓reduceIte]
      have hc0 : p ++ [false] ∈ N := (hshape.2.2.2 p hpJ).1
      have hc1 : p ++ [true] ∈ N := (hshape.2.2.2 p hpJ).2
      have hf0 : N.sup List.length - (p ++ [false]).length ≤ fuel := by
        simp only [List.length_append, List.length_singleton]
        omega
      have hf1 : N.sup List.length - (p ++ [true]).length ≤ fuel := by
        simp only [List.length_append, List.length_singleton]
        omega
      have hsplit : (N \ J).filter (fun p' => p <+: p' ∧ (SectionSet q p' u).Nonempty) =
          (N \ J).filter (fun p' => p ++ [false] <+: p' ∧ (SectionSet q p' u).Nonempty) ∪
          (N \ J).filter (fun p' => p ++ [true] <+: p' ∧ (SectionSet q p' u).Nonempty) := by
        ext p'
        simp only [Finset.mem_filter, Finset.mem_union]
        constructor
        · rintro ⟨hp', ⟨s, rfl⟩, hne'⟩
          cases s with
          | nil =>
            simp only [List.append_nil] at hp'
            exact absurd hpJ (Finset.mem_sdiff.mp hp').2
          | cons b rest =>
            cases b
            · left; exact ⟨hp', ⟨rest, by simp⟩, hne'⟩
            · right; exact ⟨hp', ⟨rest, by simp⟩, hne'⟩
        · rintro (⟨hp', ⟨s, rfl⟩, hne'⟩ | ⟨hp', ⟨s, rfl⟩, hne'⟩)
          · exact ⟨hp', ⟨false :: s, by simp⟩, hne'⟩
          · exact ⟨hp', ⟨true :: s, by simp⟩, hne'⟩
      have hdisj : Disjoint
          ((N \ J).filter (fun p' => p ++ [false] <+: p' ∧ (SectionSet q p' u).Nonempty))
          ((N \ J).filter (fun p' => p ++ [true] <+: p' ∧ (SectionSet q p' u).Nonempty)) := by
        rw [Finset.disjoint_left]
        intro p' h1 h2
        rcases (Finset.mem_filter.mp h1).2.1 with ⟨s₁, rfl⟩
        rcases (Finset.mem_filter.mp h2).2.1 with ⟨s₂, heq⟩
        have htail : [false] ++ s₁ = [true] ++ s₂ := by
          have h' : p ++ ([false] ++ s₁) = p ++ ([true] ++ s₂) := by
            simp only [← List.append_assoc]
            exact heq.symm
          exact List.append_cancel_left h'
        cases htail
      have hempty_of_not : ∀ b : Bool, ¬ (SectionSet q (p ++ [b]) u).Nonempty →
          (N \ J).filter (fun p' => p ++ [b] <+: p' ∧ (SectionSet q p' u).Nonempty) = ∅ := by
        intro b hnot
        rw [Finset.filter_eq_empty_iff]
        intro p' _ ⟨hpre, ⟨x, hx⟩⟩
        exact hnot ⟨x, follows_prefix q hpre hx⟩
      by_cases hlo : (SectionSet q (p ++ [false]) u).Nonempty
      · simp only [hlo, ↓reduceIte]
        by_cases hhi : (SectionSet q (p ++ [true]) u).Nonempty
        · simp only [hhi, ↓reduceIte, PTree.leafSum]
          rw [hsplit, Finset.sum_union hdisj,
            ih (p ++ [false]) hc0 hf0 hlo,
            ih (p ++ [true]) hc1 hf1 hhi]
        · simp only [hhi, ↓reduceIte]
          rw [hsplit, hempty_of_not true hhi, Finset.union_empty]
          exact ih (p ++ [false]) hc0 hf0 hlo
      · simp only [hlo, ↓reduceIte]
        have hhi : (SectionSet q (p ++ [true]) u).Nonempty := by
          rcases hne with ⟨x, hx⟩
          cases hqv : q p (x, u)
          · exfalso
            exact hlo ⟨x, (follows_append_singleton q p false (x, u)).mpr ⟨hx, hqv⟩⟩
          · exact ⟨x, (follows_append_singleton q p true (x, u)).mpr ⟨hx, hqv⟩⟩
        rw [hsplit, hempty_of_not false hlo, Finset.empty_union]
        exact ih (p ++ [true]) hc1 hf1 hhi
    · simp only [hpJ, ↓reduceIte]
      have hleaf : p ∈ N \ J := Finset.mem_sdiff.mpr ⟨hp, hpJ⟩
      have hfilt : (N \ J).filter (fun p' => p <+: p' ∧ (SectionSet q p' u).Nonempty) = {p} := by
        ext p'
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hp', hpre, _⟩
          exact (shape_leaf_prefix_eq hshape hleaf (Finset.mem_sdiff.mp hp').1 hpre).symm
        · rintro rfl
          exact ⟨hleaf, List.prefix_refl _, hne⟩
      rw [hfilt]
      simp [PTree.leafSum]

end Forward

lemma forward_dir (n k t : ℕ) (A : Type)
    (ok : (Fin n → ZMod 2) → A → Prop)
    (M : A → (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin t → ZMod 2))
    (H K : ℕ)
    (N J : Finset (List Bool))
    (q : List Bool → ((Fin n → ZMod 2) × (Fin k → ZMod 2)) → Bool)
    (out : List Bool → A × (Fin t → ZMod 2))
    (hshape : TreeShape N J)
    (hq : ∀ p ∈ J, ∃ (l : ((Fin n → ZMod 2) × (Fin k → ZMod 2)) →ₗ[ZMod 2] ZMod 2) (b : ZMod 2),
      q p = fun z => decide (l z = b))
    (hcert : ∀ p ∈ N \ J, ∀ z : (Fin n → ZMod 2) × (Fin k → ZMod 2),
      Follows q p z → ok z.1 (out p).1 ∧ (out p).2 = M (out p).1 z.2)
    (hH : ∀ p ∈ N \ J, p.length + 0 ≤ H)
    (hK : (N \ J).sum (fun _ => 1) ≤ K) :
    ∃ (N' J' : Finset (List Bool))
      (q' : List Bool → (Fin n → ZMod 2) → Bool)
      (out' : List Bool → A),
      TreeShape N' J' ∧
      (∀ p ∈ J', ∃ (l : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) (b : ZMod 2),
        q' p = fun x => decide (l x = b)) ∧
      (∀ p ∈ N' \ J', ∀ x : Fin n → ZMod 2, Follows q' p x → ok x (out' p)) ∧
      (∀ p ∈ N' \ J', p.length + Module.finrank (ZMod 2) (LinearMap.range (M (out' p))) ≤ H) ∧
      (N' \ J').sum (fun p => 2 ^ Module.finrank (ZMod 2) (LinearMap.range (M (out' p)))) ≤ K := by
  classical
  have haff : ∀ p : List Bool, ∃ (lx : Fin n → ZMod 2) (lu : Fin k → ZMod 2) (b : ZMod 2),
      p ∈ J → q p = fun z => decide (dotProduct lx z.1 + dotProduct lu z.2 = b) := by
    intro p
    by_cases hp : p ∈ J
    · obtain ⟨l, b, hl⟩ := hq p hp
      obtain ⟨lx, lu, hdot⟩ := linearMap_prod_eq_dot l
      refine ⟨lx, lu, b, fun _ => ?_⟩
      rw [hl]
      ext z
      rw [hdot z]
    · exact ⟨0, 0, 0, fun h => absurd h hp⟩
  choose lx lu qb hq_aff using haff
  have hq_aff' : ∀ p ∈ J, q p = fun z => decide (dotProduct (lx p) z.1 + dotProduct (lu p) z.2 = qb p) :=
    fun p hp => hq_aff p hp
  set fuel := N.sup List.length
  let w : A → ℕ := fun a => 2 ^ Module.finrank (ZMod 2) (LinearMap.range (M a))
  have hsum_u : ∑ u : Fin k → ZMod 2, (pruneTree J q out u fuel []).leafSum w ≤
      K * Fintype.card (Fin k → ZMod 2) := by
    have hstep1 : ∀ u : Fin k → ZMod 2,
        (pruneTree J q out u fuel []).leafSum w =
          (N \ J).sum (fun p => if (SectionSet q p u).Nonempty then w (out p).1 else 0) := by
      intro u
      have hne0 : (SectionSet q [] u).Nonempty := ⟨0, follows_nil q (0, u)⟩
      rw [pruneTree_leafSum N J q out hshape w u fuel [] hshape.1 (by simp [fuel]) hne0]
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun p _ => by simp
    simp_rw [hstep1]
    rw [Finset.sum_comm]
    have hbound_p : ∀ p ∈ N \ J,
        (∑ u : Fin k → ZMod 2, if (SectionSet q p u).Nonempty then w (out p).1 else 0) ≤
          Fintype.card (Fin k → ZMod 2) := by
      intro p hp
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
      have hsub : Finset.univ.filter (fun u : Fin k → ZMod 2 => (SectionSet q p u).Nonempty) ⊆
          Finset.univ.filter (fun u : Fin k → ZMod 2 => M (out p).1 u = (out p).2) := by
        intro u hu
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
        rcases hu with ⟨x, hx⟩
        exact (hcert p hp (x, u) hx).2.symm
      calc (Finset.univ.filter (fun u : Fin k → ZMod 2 => (SectionSet q p u).Nonempty)).card * w (out p).1
          ≤ (Finset.univ.filter (fun u : Fin k → ZMod 2 => M (out p).1 u = (out p).2)).card * w (out p).1 :=
            Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
        _ ≤ Fintype.card (Fin k → ZMod 2) := card_fiber_mul_pow_finrank (M (out p).1) (out p).2
    calc (N \ J).sum (fun p => ∑ u : Fin k → ZMod 2, if (SectionSet q p u).Nonempty then w (out p).1 else 0)
        ≤ (N \ J).sum (fun _ => Fintype.card (Fin k → ZMod 2)) := Finset.sum_le_sum hbound_p
      _ = (N \ J).card * Fintype.card (Fin k → ZMod 2) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ K * Fintype.card (Fin k → ZMod 2) := by
          have hcard : (N \ J).card ≤ K := by simpa using hK
          exact Nat.mul_le_mul_right _ hcard
  obtain ⟨u, hu⟩ := exists_le_of_sum_le_mul (fun u => (pruneTree J q out u fuel []).leafSum w) K hsum_u
  set T := pruneTree J q out u fuel []
  refine ⟨T.nodes, T.internal, T.queryAt, T.outAt, T.shape, ?_, ?_, ?_, ?_⟩
  · exact pruneTree_queries J q out lx lu qb hq_aff' u fuel []
  · intro s hs x hf
    rw [PTree.sdiff_eq_leaves] at hs
    exact pruneTree_correct ok M N J q out hshape hcert u fuel [] hshape.1 (by simp [fuel])
      s hs x (follows_nil q (x, u)) hf
  · intro s hs
    rw [PTree.sdiff_eq_leaves] at hs
    have hH' : ∀ p' ∈ N \ J, p'.length ≤ H := fun p' hp' => by simpa using hH p' hp'
    have hne0 : (SectionSet q [] u).Nonempty := ⟨0, follows_nil q (0, u)⟩
    have hd := pruneTree_depth ok M N J q out lx lu qb hq_aff' hshape hcert hH' u fuel
      [] hshape.1 (by simp [fuel]) hne0 s hs
    rw [xSpace_nil, finrank_bot, add_zero] at hd
    exact hd
  · rw [PTree.sdiff_eq_leaves]
    exact (PTree.sum_leaves_eq_leafSum w T).trans_le hu

end PEqualNP.Outside.L_lib_829_aux

theorem PEqualNP.Outside.L_lib_829 :
    ∀ (n k t : ℕ),
      let X := Fin n → ZMod 2
      let U := Fin k → ZMod 2
      let Y := Fin t → ZMod 2
      let shape := fun (N J : Finset (List Bool)) =>
        [] ∈ N ∧ J ⊆ N ∧
        (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
        ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N
      let queries := fun (V : Type) [AddCommGroup V] [Module (ZMod 2) V] =>
        {f : V → Bool | ∃ (l : V →ₗ[ZMod 2] ZMod 2) (b : ZMod 2), f = fun x => decide (l x = b)}
      let cert := fun {V O : Type} (qs : Set (V → Bool)) (ok : V → O → Prop)
          (N J : Finset (List Bool)) (q : List Bool → V → Bool) (out : List Bool → O) =>
        shape N J ∧ (∀ p ∈ J, q p ∈ qs) ∧ ∀ p ∈ N \ J, ∀ x : V,
          (∀ j : Fin p.length, q (p.take j.val) x = p.get j) → ok x (out p)
      let fits := fun {V O : Type} (qs : Set (V → Bool)) (ok : V → O → Prop)
          (depth leaves : O → ℕ) (H K : ℕ) =>
        ∃ (N J : Finset (List Bool)) (q : List Bool → V → Bool) (out : List Bool → O),
          cert qs ok N J q out ∧ (∀ p ∈ N \ J, p.length + depth (out p) ≤ H) ∧
          (N \ J).sum (fun p => leaves (out p)) ≤ K
      ∀ (A : Type) (ok : X → A → Prop) (M : A → U →ₗ[ZMod 2] Y) (H K : ℕ),
        let r := fun a => Module.finrank (ZMod 2) (LinearMap.range (M a))
        fits (queries (X × U)) (fun z (o : A × Y) => ok z.1 o.1 ∧ o.2 = M o.1 z.2)
          (fun _ => 0) (fun _ => 1) H K ↔
        fits (queries X) ok r (fun a => 2^(r a)) H K := by
  intro n k t X U Y shape queries cert fits A ok M H K r
  constructor
  · rintro ⟨N, J, q, out, ⟨hshape, hq, hcert⟩, hH, hK⟩
    obtain ⟨N', J', q', out', hs', hq', hc', hH', hK'⟩ :=
      PEqualNP.Outside.L_lib_829_aux.forward_dir n k t A ok M H K N J q out hshape hq hcert hH hK
    exact ⟨N', J', q', out', ⟨hs', hq', hc'⟩, hH', hK'⟩
  · rintro ⟨N, J, q, out, ⟨hshape, hq, hcert⟩, hH, hK⟩
    obtain ⟨N', J', q', out', hs', hq', hc', hH', hK'⟩ :=
      PEqualNP.Outside.L_lib_829_aux.backward_dir n k t A ok M H K N J q out hshape hq hcert hH hK
    exact ⟨N', J', q', out', ⟨hs', hq', hc'⟩, hH', hK'⟩
