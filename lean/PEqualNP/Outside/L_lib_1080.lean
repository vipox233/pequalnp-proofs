import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1080_aux

open scoped BigOperators

lemma card_filter_mod_three_eq (t : ℕ) (a : ℕ) :
    (Finset.univ.filter (fun i : Fin (3 * t) => i.val % 3 = a)).card ≤ t := by
  by_cases ha : a < 3
  · have hsub : Finset.univ.filter (fun i : Fin (3 * t) => i.val % 3 = a) ⊆
        (Finset.univ : Finset (Fin t)).image (fun q : Fin t =>
          (⟨3 * q.val + a, by omega⟩ : Fin (3 * t))) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      refine ⟨⟨i.val / 3, by omega⟩, ?_⟩
      apply Fin.ext
      dsimp
      omega
    exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))
  · have hemp : Finset.univ.filter (fun i : Fin (3 * t) => i.val % 3 = a) = ∅ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      omega
    simp [hemp]

lemma exists_orth_zmod2 (S : Submodule (ZMod 2) (Fin 2 → ZMod 2))
    (hlt : Module.finrank (ZMod 2) S < 2) :
    ∃ α0 α1 : ZMod 2, (α0 ≠ 0 ∨ α1 ≠ 0) ∧ ∀ z ∈ S, α0 * z 0 + α1 * z 1 = 0 := by
  have hnot_top : S ≠ ⊤ := by
    intro htop
    rw [htop, finrank_top] at hlt
    have h2 : Module.finrank (ZMod 2) (Fin 2 → ZMod 2) = 2 := by simp
    omega
  by_cases h0 : ∀ z ∈ S, z 0 = 0
  · exact ⟨1, 0, Or.inl one_ne_zero, fun z hz => by simp [h0 z hz]⟩
  · by_cases h1 : ∀ z ∈ S, z 1 = 0
    · exact ⟨0, 1, Or.inr one_ne_zero, fun z hz => by simp [h1 z hz]⟩
    · by_cases h01 : ∀ z ∈ S, z 0 + z 1 = 0
      · exact ⟨1, 1, Or.inl one_ne_zero, fun z hz => by simpa using h01 z hz⟩
      · exfalso
        push Not at h0 h1 h01
        rcases h0 with ⟨z0, hz0S, hz0⟩
        rcases h1 with ⟨z1, hz1S, hz1⟩
        rcases h01 with ⟨z2, hz2S, hz2⟩
        apply hnot_top
        rw [eq_top_iff]
        intro w _
        let e0 : Fin 2 → ZMod 2 := fun e => if e = 0 then 1 else 0
        let e1 : Fin 2 → ZMod 2 := fun e => if e = 1 then 1 else 0
        have hz : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
        have h11 : (1 : ZMod 2) + 1 = 0 := by decide
        have h10_01 : e0 ∈ S ∧ e1 ∈ S := by
          have hz0_0 : z0 0 = 1 := (hz (z0 0)).resolve_left hz0
          have hz1_1 : z1 1 = 1 := (hz (z1 1)).resolve_left hz1
          rcases hz (z2 0) with h2a | h2a <;> rcases hz (z2 1) with h2b | h2b
          · exfalso; apply hz2; simp [h2a, h2b]
          · have hz2_e1 : z2 = e1 := by ext e; fin_cases e <;> simp [e1, h2a, h2b]
            have he1 : e1 ∈ S := hz2_e1 ▸ hz2S
            refine ⟨?_, he1⟩
            rcases hz (z0 1) with h0b | h0b
            · have : z0 = e0 := by ext e; fin_cases e <;> simp [e0, hz0_0, h0b]
              exact this ▸ hz0S
            · have : z0 + z2 = e0 := by ext e; fin_cases e <;> simp [e0, hz0_0, h0b, h2a, h2b, h11]
              exact this ▸ S.add_mem hz0S hz2S
          · have hz2_e0 : z2 = e0 := by ext e; fin_cases e <;> simp [e0, h2a, h2b]
            have he0 : e0 ∈ S := hz2_e0 ▸ hz2S
            refine ⟨he0, ?_⟩
            rcases hz (z1 0) with h1a | h1a
            · have : z1 = e1 := by ext e; fin_cases e <;> simp [e1, h1a, hz1_1]
              exact this ▸ hz1S
            · have : z1 + z2 = e1 := by ext e; fin_cases e <;> simp [e1, h1a, hz1_1, h2a, h2b, h11]
              exact this ▸ S.add_mem hz1S hz2S
          · exfalso; apply hz2
            simp [h2a, h2b, h11]
        have hw_eq : w = w 0 • e0 + w 1 • e1 := by
          ext e; fin_cases e <;> simp [e0, e1]
        rw [hw_eq]
        exact S.add_mem (S.smul_mem _ h10_01.1) (S.smul_mem _ h10_01.2)

lemma finrank_le_card_add_k_sub_syndrome
    (t k : ℕ)
    (P : Submodule (ZMod 2) (Fin (3 * t) → ZMod 2))
    (hcode : ∀ x ∈ P, ∀ e : Fin 2,
      (∑ i : Fin (3 * t), if i.val % 3 = e.val ∨ i.val % 3 = 2 then x i else 0) = 0)
    (ZP AL IL : Finset (Fin (3 * t)))
    (hpart1 : Disjoint ZP AL) (hpart2 : Disjoint ZP IL) (hpart3 : Disjoint AL IL)
    (hcov : ZP ∪ AL ∪ IL = Finset.univ)
    (hZP : ∀ i ∈ ZP, ∀ x ∈ P, x i = 0)
    (rep : Fin k → Fin (3 * t))
    (cL : Fin (3 * t) → Fin k)
    (hrep : ∀ c : Fin k, rep c ∈ AL ∧ cL (rep c) = c)
    (hAL : ∀ i ∈ AL, ∀ x ∈ P, x i = x (rep (cL i))) :
    ∃ rP : ℕ, rP ≤ 2 ∧
      Module.finrank (ZMod 2) P + rP ≤ IL.card + k ∧
      (rP = 0 → ∀ c : Fin k, 2 ≤ (AL.filter (fun i => cL i = c)).card) ∧
      (rP = 1 → (∀ c : Fin k, (AL.filter (fun i => cL i = c)).card = 1) →
        ∃ a : ℕ, ∀ i ∈ AL ∪ IL, i.val % 3 = a) := by
  classical
  let F := ZMod 2
  let n := 3 * t
  let V := (IL → F) × (Fin k → F)
  let φ : P →ₗ[F] V :=
    { toFun := fun x => (fun i => x.1 i.1, fun c => x.1 (rep c))
      map_add' := fun x y => by ext <;> rfl
      map_smul' := fun a x => by ext <;> rfl }
  have hφ_inj : Function.Injective φ := by
    intro x y hxy
    apply Subtype.ext
    funext i
    have hi : i ∈ ZP ∪ AL ∪ IL := hcov ▸ Finset.mem_univ i
    simp only [Finset.mem_union] at hi
    rcases hi with (hi | hi) | hi
    · rw [hZP i hi x.1 x.2, hZP i hi y.1 y.2]
    · rw [hAL i hi x.1 x.2, hAL i hi y.1 y.2]
      exact congrFun (congrArg Prod.snd hxy) (cL i)
    · exact congrFun (congrArg Prod.fst hxy) ⟨i, hi⟩
  let wt (c : Fin k) (e : Fin 2) : F :=
    ∑ i ∈ AL.filter (fun i => cL i = c), if i.val % 3 = e.val ∨ i.val % 3 = 2 then (1 : F) else 0
  let σ : V →ₗ[F] (Fin 2 → F) :=
    { toFun := fun v e =>
        (∑ i : IL, if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then v.1 i else 0) +
        (∑ c : Fin k, wt c e * v.2 c)
      map_add' := fun u v => by
        ext e
        change (∑ i : IL, if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then u.1 i + v.1 i else (0 : F)) +
            (∑ c : Fin k, wt c e * (u.2 c + v.2 c)) =
          ((∑ i : IL, if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then u.1 i else 0) +
            (∑ c : Fin k, wt c e * u.2 c)) +
          ((∑ i : IL, if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then v.1 i else 0) +
            (∑ c : Fin k, wt c e * v.2 c))
        have h1 : ∀ i : IL, (if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then u.1 i + v.1 i else (0 : F)) =
            (if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then u.1 i else 0) +
            (if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then v.1 i else 0) := by
          intro i; split_ifs <;> simp
        simp only [h1, Finset.sum_add_distrib, mul_add]
        ring
      map_smul' := fun a v => by
        ext e
        change (∑ i : IL, if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then a * v.1 i else (0 : F)) +
            (∑ c : Fin k, wt c e * (a * v.2 c)) =
          a * ((∑ i : IL, if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then v.1 i else 0) +
            (∑ c : Fin k, wt c e * v.2 c))
        have h1 : ∀ i : IL, (if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then a * v.1 i else (0 : F)) =
            a * (if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then v.1 i else 0) := by
          intro i; split_ifs <;> simp
        simp only [h1, ← Finset.mul_sum]
        have h2 : ∀ c : Fin k, wt c e * (a * v.2 c) = a * (wt c e * v.2 c) := fun c => by ring
        simp only [h2, ← Finset.mul_sum]
        ring }
  have hcomp : σ.comp φ = 0 := by
    apply LinearMap.ext
    intro x
    ext e
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, Pi.zero_apply, σ, φ,
      LinearMap.coe_mk, AddHom.coe_mk]
    have hsum_all : (∑ i : Fin n, if i.val % 3 = e.val ∨ i.val % 3 = 2 then x.1 i else (0 : F)) = 0 :=
      hcode x.1 x.2 e
    have hsplit : (∑ i : Fin n, if i.val % 3 = e.val ∨ i.val % 3 = 2 then x.1 i else (0 : F)) =
        (∑ i ∈ ZP, if i.val % 3 = e.val ∨ i.val % 3 = 2 then x.1 i else (0 : F)) +
        (∑ i ∈ AL, if i.val % 3 = e.val ∨ i.val % 3 = 2 then x.1 i else (0 : F)) +
        (∑ i ∈ IL, if i.val % 3 = e.val ∨ i.val % 3 = 2 then x.1 i else (0 : F)) := by
      rw [← Finset.sum_union hpart1, ← Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hpart2, hpart3⟩),
        hcov]
    have hZ0 : (∑ i ∈ ZP, if i.val % 3 = e.val ∨ i.val % 3 = 2 then x.1 i else (0 : F)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp [hZP i hi x.1 x.2]
    have hIL_eq : (∑ i : IL, if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then x.1 i.1 else (0 : F)) =
        ∑ i ∈ IL, if i.val % 3 = e.val ∨ i.val % 3 = 2 then x.1 i else (0 : F) :=
      Finset.sum_coe_sort IL (fun i => if i.val % 3 = e.val ∨ i.val % 3 = 2 then x.1 i else (0 : F))
    have hAL_eq : (∑ c : Fin k, wt c e * x.1 (rep c)) =
        ∑ i ∈ AL, if i.val % 3 = e.val ∨ i.val % 3 = 2 then x.1 i else (0 : F) := by
      have hfib : ∑ c : Fin k, ∑ i ∈ AL.filter (fun i => cL i = c),
          (if i.val % 3 = e.val ∨ i.val % 3 = 2 then x.1 i else (0 : F)) =
          ∑ i ∈ AL, if i.val % 3 = e.val ∨ i.val % 3 = 2 then x.1 i else (0 : F) := by
        rw [← Finset.sum_biUnion]
        · congr 1
          ext i
          simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and]
          exact ⟨fun ⟨_, hi, _⟩ => hi, fun hi => ⟨cL i, hi, rfl⟩⟩
        · intro c1 _ c2 _ hne
          change Disjoint _ _
          rw [Finset.disjoint_left]
          intro i h1 h2
          exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
      rw [← hfib]
      refine Finset.sum_congr rfl fun c _ => ?_
      dsimp [wt]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hci : cL i = c := (Finset.mem_filter.mp hi).2
      have hxi : x.1 i = x.1 (rep c) := hci ▸ hAL i (Finset.mem_filter.mp hi).1 x.1 x.2
      rw [hxi]
      split_ifs <;> simp
    rw [hIL_eq, hAL_eq]
    rw [hZ0, zero_add] at hsplit
    rw [add_comm, ← hsplit, hsum_all]
  let rP := Module.finrank F (LinearMap.range σ)
  refine ⟨rP, ?_, ?_, ?_, ?_⟩
  · have hle := Submodule.finrank_le (LinearMap.range σ)
    simpa using hle
  · have hsub : LinearMap.range φ ≤ LinearMap.ker σ := by
      rintro _ ⟨x, rfl⟩
      rw [LinearMap.mem_ker]
      exact LinearMap.congr_fun hcomp x
    have h1 : Module.finrank F P = Module.finrank F (LinearMap.range φ) :=
      (LinearEquiv.ofInjective φ hφ_inj).finrank_eq
    have h2 : Module.finrank F (LinearMap.range φ) ≤ Module.finrank F (LinearMap.ker σ) :=
      Submodule.finrank_mono hsub
    have h3 : Module.finrank F (LinearMap.range σ) + Module.finrank F (LinearMap.ker σ) =
        Module.finrank F V := LinearMap.finrank_range_add_finrank_ker σ
    have hV : Module.finrank F V = IL.card + k := by
      simp [V, Module.finrank_prod, Fintype.card_coe]
    change Module.finrank F P + rP ≤ IL.card + k
    omega
  · intro hr0 c
    have hker_all : LinearMap.range σ = ⊥ := Submodule.finrank_eq_zero.mp hr0
    have hσ0 : ∀ v : V, σ v = 0 := fun v =>
      (Submodule.mem_bot F).mp (hker_all ▸ ⟨v, rfl⟩)
    have hwt0 : ∀ e : Fin 2, wt c e = 0 := fun e => by
      let v : V := (0, fun c' => if c' = c then 1 else 0)
      have hv := congrFun (hσ0 v) e
      simpa [σ, v] using hv
    by_contra hlt
    push Not at hlt
    have hmem : rep c ∈ AL.filter (fun i => cL i = c) :=
      Finset.mem_filter.mpr (hrep c)
    have hsing : AL.filter (fun i => cL i = c) = {rep c} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hmem, fun j hj => ?_⟩
      by_contra hne
      have h2 : ({rep c, j} : Finset (Fin n)).card ≤ (AL.filter (fun i => cL i = c)).card :=
        Finset.card_le_card (by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption)
      rw [Finset.card_pair (Ne.symm hne)] at h2
      omega
    have h0 := hwt0 0
    have h1 := hwt0 1
    dsimp [wt] at h0 h1
    rw [hsing, Finset.sum_singleton] at h0 h1
    have hmod : (rep c).val % 3 = 0 ∨ (rep c).val % 3 = 1 ∨ (rep c).val % 3 = 2 := by omega
    rcases hmod with hm | hm | hm
    · simp [hm] at h0
    · simp [hm] at h1
    · simp [hm] at h0
  · intro hr1 hcard1
    obtain ⟨α0, α1, hαne, horthS⟩ := exists_orth_zmod2 (LinearMap.range σ) (by change rP < 2; omega)
    have horth : ∀ v : V, α0 * σ v 0 + α1 * σ v 1 = 0 := fun v => horthS (σ v) ⟨v, rfl⟩
    have hcoeff : ∀ i ∈ AL ∪ IL,
        α0 * (if i.val % 3 = 0 ∨ i.val % 3 = 2 then (1 : F) else 0) +
        α1 * (if i.val % 3 = 1 ∨ i.val % 3 = 2 then (1 : F) else 0) = 0 := by
      intro i hi
      rcases Finset.mem_union.mp hi with hiA | hiI
      · let c := cL i
        have hsing : AL.filter (fun j => cL j = c) = {i} := by
          have hc1 := hcard1 c
          have hmem : i ∈ AL.filter (fun j => cL j = c) := Finset.mem_filter.mpr ⟨hiA, rfl⟩
          apply Finset.eq_singleton_iff_unique_mem.mpr
          refine ⟨hmem, fun j hj => ?_⟩
          by_contra hne
          have h2 : ({i, j} : Finset (Fin n)).card ≤ (AL.filter (fun x => cL x = c)).card :=
            Finset.card_le_card (by
              intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl <;> assumption)
          rw [Finset.card_pair (Ne.symm hne)] at h2
          omega
        let v : V := (0, fun c' => if c' = c then 1 else 0)
        have hv := horth v
        have hσv : ∀ e : Fin 2, σ v e = if i.val % 3 = e.val ∨ i.val % 3 = 2 then (1 : F) else 0 := by
          intro e
          have h1 : σ v e = wt c e := by simp [σ, v]
          rw [h1]
          dsimp [wt]
          rw [hsing, Finset.sum_singleton]
        rw [hσv 0, hσv 1] at hv
        simpa using hv
      · let v : V := (fun j : IL => if j.1 = i then 1 else 0, 0)
        have hv := horth v
        have hsum_e : ∀ e : Fin 2,
            (∑ j : IL, if j.1.val % 3 = e.val ∨ j.1.val % 3 = 2 then v.1 j else (0 : F)) =
            if i.val % 3 = e.val ∨ i.val % 3 = 2 then 1 else 0 := by
          intro e
          rw [Finset.sum_eq_single ⟨i, hiI⟩]
          · simp [v]
          · intro b _ hbi
            have hne : b.1 ≠ i := fun h => hbi (Subtype.ext h)
            simp [v, hne]
          · intro h; exact (h (Finset.mem_univ _)).elim
        simp only [σ, LinearMap.coe_mk, AddHom.coe_mk, hsum_e, v] at hv
        simpa using hv
    have hz2 : ∀ x : F, x = 0 ∨ x = 1 := by decide
    rcases hz2 α0 with rfl | rfl <;> rcases hz2 α1 with rfl | rfl
    · simp at hαne
    · refine ⟨0, fun i hi => ?_⟩
      have hc := hcoeff i hi
      have hm : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
      rcases hm with hm | hm | hm <;> simp [hm] at hc ⊢
    · refine ⟨1, fun i hi => ?_⟩
      have hc := hcoeff i hi
      have hm : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
      rcases hm with hm | hm | hm <;> simp [hm] at hc ⊢
    · refine ⟨2, fun i hi => ?_⟩
      have hc := hcoeff i hi
      have hm : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
      rcases hm with hm | hm | hm
      · simp [hm] at hc
      · simp [hm] at hc
      · exact hm

lemma cycle_ends_bound
    (n k : ℕ) (hn_pos : 0 < n) (hk : 3 ≤ k)
    (ZP ZQ AL AR IL IR : Finset (Fin n))
    (hAL_disj_ZP : Disjoint ZP AL) (hIL_disj_ZP : Disjoint ZP IL) (hIL_disj_AL : Disjoint AL IL)
    (hPcov : ZP ∪ AL ∪ IL = Finset.univ)
    (hAR_disj_ZQ : Disjoint ZQ AR) (hIR_disj_ZQ : Disjoint ZQ IR) (hIR_disj_AR : Disjoint AR IR)
    (hQcov : ZQ ∪ AR ∪ IR = Finset.univ)
    (Eact : Finset (Fin (2 * n)))
    (left right : Fin (2 * n) → Fin n)
    (hleft : ∀ e : Fin (2 * n), left e = ⟨((e.val + 1) / 2) % n, Nat.mod_lt _ hn_pos⟩)
    (hright : ∀ e : Fin (2 * n), right e = ⟨(e.val / 2) % n, Nat.mod_lt _ hn_pos⟩)
    (hEact_def : ∀ e : Fin (2 * n), e ∈ Eact ↔ left e ∉ ZP ∧ right e ∉ ZQ)
    (hAL_mem : ∀ e ∈ Eact, left e ∈ AL)
    (hAR_mem : ∀ e ∈ Eact, right e ∈ AR)
    (s : Fin k → Fin (2 * n))
    (hs_act : ∀ c : Fin k, s c ∈ Eact)
    (cL cR : Fin n → Fin k)
    (hrepL : ∀ c : Fin k, left (s c) ∈ AL ∧ cL (left (s c)) = c)
    (hedge_same_col : ∀ e ∈ Eact, cL (left e) = cR (right e)) :
    ∃ nLive nDead nEnds : ℕ,
      nLive + nDead = 2 * n ∧
      nLive = (AL.card + IL.card) + (AR.card + IR.card) ∧
      nEnds ≤ nDead ∧
      nEnds ≤ nLive ∧
      IL.card + IR.card + k ≤ nEnds := by
  classical
  have hkpos : 0 < k := by omega
  let nxt : Fin (2 * n) → Fin (2 * n) := fun v => ⟨(v.val + 1) % (2 * n), Nat.mod_lt _ (by omega)⟩
  have hnxt_inj : Function.Injective nxt := by
    intro v1 v2 heq
    have hval : (v1.val + 1) % (2 * n) = (v2.val + 1) % (2 * n) := congrArg Fin.val heq
    apply Fin.ext
    have hv1 := v1.2; have hv2 := v2.2
    by_cases h1 : v1.val + 1 < 2 * n <;> by_cases h2 : v2.val + 1 < 2 * n
    · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hval; omega
    · have h2eq : v2.val + 1 = 2 * n := by omega
      rw [Nat.mod_eq_of_lt h1, h2eq, Nat.mod_self] at hval; omega
    · have h1eq : v1.val + 1 = 2 * n := by omega
      rw [h1eq, Nat.mod_self, Nat.mod_eq_of_lt h2] at hval; omega
    · omega
  let isLive : Fin (2 * n) → Prop := fun v =>
    if v.val % 2 = 0 then (⟨v.val / 2, by omega⟩ : Fin n) ∉ ZP
    else (⟨v.val / 2, by omega⟩ : Fin n) ∉ ZQ
  let Live : Finset (Fin (2 * n)) := Finset.univ.filter (fun v => isLive v)
  let Dead : Finset (Fin (2 * n)) := Finset.univ.filter (fun v => ¬ isLive v)
  have hLive_Dead : Live.card + Dead.card = 2 * n := by
    have hdisj : Disjoint Live Dead := by
      rw [Finset.disjoint_filter]; intro v _ h1 h2; exact h2 h1
    have hun : Live ∪ Dead = Finset.univ := by
      ext v; simp only [Live, Dead, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]; tauto
    rw [← Finset.card_union_of_disjoint hdisj, hun, Finset.card_univ, Fintype.card_fin]
  have hLive_card : Live.card = (AL.card + IL.card) + (AR.card + IR.card) := by
    let UP := AL ∪ IL
    let UQ := AR ∪ IR
    have hUP : UP.card = AL.card + IL.card := Finset.card_union_of_disjoint hIL_disj_AL
    have hUQ : UQ.card = AR.card + IR.card := Finset.card_union_of_disjoint hIR_disj_AR
    have hUP_iff : ∀ i : Fin n, i ∈ UP ↔ i ∉ ZP := by
      intro i
      have hi : i ∈ ZP ∪ AL ∪ IL := hPcov ▸ Finset.mem_univ i
      simp only [UP, Finset.mem_union] at hi ⊢
      constructor
      · rintro (hA | hI) hZ
        · exact Finset.disjoint_left.mp hAL_disj_ZP hZ hA
        · exact Finset.disjoint_left.mp hIL_disj_ZP hZ hI
      · intro hnotZ
        rcases hi with (hZ | hA) | hI
        · exact absurd hZ hnotZ
        · exact Or.inl hA
        · exact Or.inr hI
    have hUQ_iff : ∀ j : Fin n, j ∈ UQ ↔ j ∉ ZQ := by
      intro j
      have hj : j ∈ ZQ ∪ AR ∪ IR := hQcov ▸ Finset.mem_univ j
      simp only [UQ, Finset.mem_union] at hj ⊢
      constructor
      · rintro (hA | hI) hZ
        · exact Finset.disjoint_left.mp hAR_disj_ZQ hZ hA
        · exact Finset.disjoint_left.mp hIR_disj_ZQ hZ hI
      · intro hnotZ
        rcases hj with (hZ | hA) | hI
        · exact absurd hZ hnotZ
        · exact Or.inl hA
        · exact Or.inr hI
    let Leven := UP.image (fun i : Fin n => (⟨2 * i.val, by omega⟩ : Fin (2 * n)))
    let Lodd := UQ.image (fun j : Fin n => (⟨2 * j.val + 1, by omega⟩ : Fin (2 * n)))
    have hLeven_card : Leven.card = UP.card :=
      Finset.card_image_of_injective _ (fun a b h => Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega))
    have hLodd_card : Lodd.card = UQ.card :=
      Finset.card_image_of_injective _ (fun a b h => Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega))
    have hdisj_eo : Disjoint Leven Lodd := by
      rw [Finset.disjoint_left]
      intro v h1 h2
      rcases Finset.mem_image.mp h1 with ⟨i, _, rfl⟩
      rcases Finset.mem_image.mp h2 with ⟨j, _, heq⟩
      have := congrArg Fin.val heq; dsimp at this; omega
    have hLive_eq : Live = Leven ∪ Lodd := by
      ext v
      simp only [Live, Leven, Lodd, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_image, isLive]
      by_cases hv : v.val % 2 = 0
      · simp only [hv, ↓reduceIte]
        constructor
        · intro hnotZ
          left
          refine ⟨⟨v.val / 2, by omega⟩, (hUP_iff _).mpr hnotZ, Fin.ext (by dsimp; omega)⟩
        · rintro (⟨i, hi, heq⟩ | ⟨j, _, heq⟩)
          · have hval : 2 * i.val = v.val := congrArg Fin.val heq
            have hi' : (⟨v.val / 2, by omega⟩ : Fin n) = i := Fin.ext (by dsimp; omega)
            rw [hi']; exact (hUP_iff i).mp hi
          · have hval : 2 * j.val + 1 = v.val := congrArg Fin.val heq; omega
      · simp only [hv, ↓reduceIte]
        constructor
        · intro hnotZ
          right
          refine ⟨⟨v.val / 2, by omega⟩, (hUQ_iff _).mpr hnotZ, Fin.ext (by dsimp; omega)⟩
        · rintro (⟨i, _, heq⟩ | ⟨j, hj, heq⟩)
          · have hval : 2 * i.val = v.val := congrArg Fin.val heq; omega
          · have hval : 2 * j.val + 1 = v.val := congrArg Fin.val heq
            have hj' : (⟨v.val / 2, by omega⟩ : Fin n) = j := Fin.ext (by dsimp; omega)
            rw [hj']; exact (hUQ_iff j).mp hj
    rw [hLive_eq, Finset.card_union_of_disjoint hdisj_eo, hLeven_card, hLodd_card, hUP, hUQ]
  have hEact_iff : ∀ e : Fin (2 * n), e ∈ Eact ↔ isLive e ∧ isLive (nxt e) := by
    intro e
    rw [hEact_def e, hleft e, hright e]
    simp only [isLive, nxt]
    by_cases he : e.val % 2 = 0
    · have he1 : (e.val + 1) % (2 * n) = e.val + 1 := Nat.mod_eq_of_lt (by omega)
      have he1odd : (e.val + 1) % 2 ≠ 0 := by omega
      simp only [he, he1, he1odd, ↓reduceIte]
      have hL : (⟨((e.val + 1) / 2) % n, Nat.mod_lt _ hn_pos⟩ : Fin n) = ⟨e.val / 2, by omega⟩ :=
        Fin.ext (by dsimp; rw [Nat.mod_eq_of_lt (by omega)]; omega)
      have hR : (⟨(e.val / 2) % n, Nat.mod_lt _ hn_pos⟩ : Fin n) = ⟨(e.val + 1) / 2, by omega⟩ :=
        Fin.ext (by dsimp; rw [Nat.mod_eq_of_lt (by omega)]; omega)
      rw [hL, hR]
    · have hne2 : (e.val + 1) % (2 * n) % 2 = 0 := by
        by_cases htop : e.val + 1 < 2 * n
        · rw [Nat.mod_eq_of_lt htop]; omega
        · have : e.val + 1 = 2 * n := by omega
          rw [this, Nat.mod_self]
      simp only [he, hne2, ↓reduceIte]
      have hR : (⟨(e.val / 2) % n, Nat.mod_lt _ hn_pos⟩ : Fin n) = ⟨e.val / 2, by omega⟩ :=
        Fin.ext (by dsimp; rw [Nat.mod_eq_of_lt (by omega)])
      have hmod_lt : (e.val + 1) % (2 * n) < 2 * n := Nat.mod_lt _ (by omega)
      have hL : (⟨((e.val + 1) / 2) % n, Nat.mod_lt _ hn_pos⟩ : Fin n) =
          ⟨((e.val + 1) % (2 * n)) / 2, by omega⟩ := by
        apply Fin.ext; dsimp
        by_cases htop : e.val + 1 < 2 * n
        · rw [Nat.mod_eq_of_lt htop, Nat.mod_eq_of_lt (by omega)]
        · have : e.val + 1 = 2 * n := by omega
          rw [this, Nat.mod_self]
          have : (2 * n) / 2 = n := by omega
          rw [this, Nat.mod_self]
      rw [hL, hR, and_comm]
  let Ends : Finset (Fin (2 * n)) := Live.filter (fun v => ¬ isLive (nxt v))
  have hEnds_le_Dead : Ends.card ≤ Dead.card := by
    refine Finset.card_le_card_of_injOn nxt ?_ (fun x _ y _ h => hnxt_inj h)
    intro v hv
    simp only [Finset.mem_coe, Ends, Dead, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact hv.2
  have hEnds_le_Live : Ends.card ≤ Live.card := Finset.card_filter_le _ _
  let isColV : Fin (2 * n) → Prop := fun v =>
    if v.val % 2 = 0 then (⟨v.val / 2, by omega⟩ : Fin n) ∈ AL
    else (⟨v.val / 2, by omega⟩ : Fin n) ∈ AR
  let vcol : Fin (2 * n) → Fin k := fun v =>
    if v.val % 2 = 0 then cL ⟨v.val / 2, by omega⟩
    else cR ⟨v.val / 2, by omega⟩
  have hstep_col : ∀ e : Fin (2 * n), isLive e → isLive (nxt e) →
      isColV e ∧ isColV (nxt e) ∧ vcol e = vcol (nxt e) := by
    intro e h1 h2
    have heA : e ∈ Eact := (hEact_iff e).mpr ⟨h1, h2⟩
    have hcol := hedge_same_col e heA
    have hmemL : left e ∈ AL := hAL_mem e heA
    have hmemR : right e ∈ AR := hAR_mem e heA
    simp only [isColV, vcol, nxt]
    by_cases he : e.val % 2 = 0
    · have he1 : (e.val + 1) % (2 * n) = e.val + 1 := Nat.mod_eq_of_lt (by omega)
      have he1odd : (e.val + 1) % 2 ≠ 0 := by omega
      simp only [he, he1, he1odd, ↓reduceIte]
      have hL : left e = ⟨e.val / 2, by omega⟩ := by
        rw [hleft e]; exact Fin.ext (by dsimp; rw [Nat.mod_eq_of_lt (by omega)]; omega)
      have hR : right e = ⟨(e.val + 1) / 2, by omega⟩ := by
        rw [hright e]; exact Fin.ext (by dsimp; rw [Nat.mod_eq_of_lt (by omega)]; omega)
      rw [← hL, ← hR]
      exact ⟨hmemL, hmemR, hcol⟩
    · have hne2 : (e.val + 1) % (2 * n) % 2 = 0 := by
        by_cases htop : e.val + 1 < 2 * n
        · rw [Nat.mod_eq_of_lt htop]; omega
        · have : e.val + 1 = 2 * n := by omega
          rw [this, Nat.mod_self]
      simp only [he, hne2, ↓reduceIte]
      have hR : right e = ⟨e.val / 2, by omega⟩ := by
        rw [hright e]; exact Fin.ext (by dsimp; rw [Nat.mod_eq_of_lt (by omega)])
      have hmod_lt : (e.val + 1) % (2 * n) < 2 * n := Nat.mod_lt _ (by omega)
      have hL : left e = ⟨((e.val + 1) % (2 * n)) / 2, by omega⟩ := by
        rw [hleft e]; apply Fin.ext; dsimp
        by_cases htop : e.val + 1 < 2 * n
        · rw [Nat.mod_eq_of_lt htop, Nat.mod_eq_of_lt (by omega)]
        · have : e.val + 1 = 2 * n := by omega
          rw [this, Nat.mod_self]
          have : (2 * n) / 2 = n := by omega
          rw [this, Nat.mod_self]
      rw [← hL, ← hR]
      exact ⟨hmemR, hmemL, hcol.symm⟩
  have hEnds_color : ∀ c : Fin k, ∃ v ∈ Ends, isColV v ∧ vcol v = c := by
    intro c
    let v0 : Fin (2 * n) := ⟨2 * (left (s c)).val, by omega⟩
    have hv0_live : isLive v0 := by
      simp only [isLive, v0, Nat.mul_mod_right, ↓reduceIte]
      have h1 : (⟨2 * (left (s c)).val / 2, by omega⟩ : Fin n) = left (s c) :=
        Fin.ext (by dsimp; omega)
      rw [h1]
      exact ((hEact_def (s c)).mp (hs_act c)).1
    have hv0_col : isColV v0 ∧ vcol v0 = c := by
      simp only [isColV, vcol, v0, Nat.mul_mod_right, ↓reduceIte]
      have h1 : (⟨2 * (left (s c)).val / 2, by omega⟩ : Fin n) = left (s c) :=
        Fin.ext (by dsimp; omega)
      rw [h1]
      exact hrepL c
    have hex_dead : ∃ d : ℕ, ¬ isLive (nxt^[d] v0) := by
      by_contra hall
      push Not at hall
      have hsame : ∀ d : ℕ, vcol (nxt^[d] v0) = c := by
        intro d
        induction d with
        | zero => exact hv0_col.2
        | succ d ih =>
          rw [Function.iterate_succ_apply']
          have hst := hstep_col (nxt^[d] v0) (hall d)
            ((Function.iterate_succ_apply' nxt d v0).symm ▸ hall (d + 1))
          rw [← hst.2.2, ih]
      have hiter_val : ∀ d : ℕ, (nxt^[d] v0).val = (v0.val + d) % (2 * n) := by
        intro d
        induction d with
        | zero => simp [Nat.mod_eq_of_lt v0.2]
        | succ d ih =>
          rw [Function.iterate_succ_apply']
          dsimp [nxt]
          rw [ih, Nat.mod_add_mod, add_assoc]
      let c' : Fin k := ⟨(c.val + 1) % k, Nat.mod_lt _ hkpos⟩
      have hc'ne : c' ≠ c := by
        intro heq
        have hv : (c.val + 1) % k = c.val := congrArg Fin.val heq
        have hc2 := c.2
        by_cases htop : c.val + 1 < k
        · rw [Nat.mod_eq_of_lt htop] at hv; omega
        · have : c.val + 1 = k := by omega
          rw [this, Nat.mod_self] at hv; omega
      let w0 : Fin (2 * n) := ⟨2 * (left (s c')).val, by omega⟩
      let d0 : ℕ := (w0.val + 2 * n - v0.val) % (2 * n)
      have hhit : nxt^[d0] v0 = w0 := by
        apply Fin.ext
        rw [hiter_val d0]
        have hv0lt := v0.2; have hw0lt := w0.2
        dsimp [d0]
        rw [Nat.add_mod_mod]
        have : v0.val + (w0.val + 2 * n - v0.val) = w0.val + 2 * n := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hw0lt]
      have h1 := hsame d0
      rw [hhit] at h1
      have h2 : vcol w0 = c' := by
        simp only [vcol, w0, Nat.mul_mod_right, ↓reduceIte]
        have heq : (⟨2 * (left (s c')).val / 2, by omega⟩ : Fin n) = left (s c') :=
          Fin.ext (by dsimp; omega)
        rw [heq]
        exact (hrepL c').2
      rw [h2] at h1
      exact hc'ne h1
    let d0 := Nat.find hex_dead
    have hd0_spec : ¬ isLive (nxt^[d0] v0) := Nat.find_spec hex_dead
    have hd0_pos : 0 < d0 := by
      by_contra h0
      have : d0 = 0 := by omega
      rw [this] at hd0_spec
      exact hd0_spec hv0_live
    have hlive_lt : ∀ m < d0, isLive (nxt^[m] v0) := fun m hm =>
      by_contra fun h => Nat.find_min hex_dead hm h
    have hprop_lt : ∀ m < d0, isColV (nxt^[m] v0) ∧ vcol (nxt^[m] v0) = c := by
      intro m hm
      induction m with
      | zero => exact hv0_col
      | succ m ih =>
        rw [Function.iterate_succ_apply']
        have hst := hstep_col (nxt^[m] v0) (hlive_lt m (by omega))
          ((Function.iterate_succ_apply' nxt m v0).symm ▸ hlive_lt (m + 1) hm)
        exact ⟨hst.2.1, hst.2.2.symm.trans (ih (by omega)).2⟩
    let v := nxt^[d0 - 1] v0
    have hv_live : isLive v := hlive_lt (d0 - 1) (by omega)
    have hv_nxt : ¬ isLive (nxt v) := by
      have : nxt v = nxt^[d0] v0 := by
        dsimp [v]
        rw [← Function.iterate_succ_apply' nxt (d0 - 1) v0]
        congr 1; omega
      rw [this]; exact hd0_spec
    have hv_col := hprop_lt (d0 - 1) (by omega)
    exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv_live⟩, hv_nxt⟩,
      hv_col.1, hv_col.2⟩
  let E_IL := IL.image (fun i : Fin n => (⟨2 * i.val, by omega⟩ : Fin (2 * n)))
  let E_IR := IR.image (fun j : Fin n => (⟨2 * j.val + 1, by omega⟩ : Fin (2 * n)))
  let E_C := (Finset.univ : Finset (Fin k)).image (fun c => Classical.choose (hEnds_color c))
  have hEIL_sub : E_IL ⊆ Ends := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨i, hi, rfl⟩
    have hi_notZ : i ∉ ZP := Finset.disjoint_right.mp hIL_disj_ZP hi
    have hi_notA : i ∉ AL := Finset.disjoint_right.mp hIL_disj_AL hi
    have hlive : isLive ⟨2 * i.val, by omega⟩ := by
      simp only [isLive, Nat.mul_mod_right, ↓reduceIte]
      have : (⟨2 * i.val / 2, by omega⟩ : Fin n) = i := Fin.ext (by dsimp; omega)
      rw [this]; exact hi_notZ
    have hdead : ¬ isLive (nxt ⟨2 * i.val, by omega⟩) := by
      intro hl2
      have heA : (⟨2 * i.val, by omega⟩ : Fin (2 * n)) ∈ Eact := (hEact_iff _).mpr ⟨hlive, hl2⟩
      have hleft_i : left ⟨2 * i.val, by omega⟩ = i := by
        rw [hleft]; exact Fin.ext (by dsimp; rw [Nat.mod_eq_of_lt (by omega)]; omega)
      exact hi_notA (hleft_i ▸ hAL_mem _ heA)
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlive⟩, hdead⟩
  have hEIR_sub : E_IR ⊆ Ends := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨j, hj, rfl⟩
    have hj_notZ : j ∉ ZQ := Finset.disjoint_right.mp hIR_disj_ZQ hj
    have hj_notA : j ∉ AR := Finset.disjoint_right.mp hIR_disj_AR hj
    have hlive : isLive ⟨2 * j.val + 1, by omega⟩ := by
      have hodd : (2 * j.val + 1) % 2 ≠ 0 := by omega
      simp only [isLive, hodd, ↓reduceIte]
      have : (⟨(2 * j.val + 1) / 2, by omega⟩ : Fin n) = j := Fin.ext (by dsimp; omega)
      rw [this]; exact hj_notZ
    have hdead : ¬ isLive (nxt ⟨2 * j.val + 1, by omega⟩) := by
      intro hl2
      have heA : (⟨2 * j.val + 1, by omega⟩ : Fin (2 * n)) ∈ Eact := (hEact_iff _).mpr ⟨hlive, hl2⟩
      have hright_j : right ⟨2 * j.val + 1, by omega⟩ = j := by
        rw [hright]; exact Fin.ext (by dsimp; rw [Nat.mod_eq_of_lt (by omega)]; omega)
      exact hj_notA (hright_j ▸ hAR_mem _ heA)
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlive⟩, hdead⟩
  have hEC_sub : E_C ⊆ Ends := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨c, _, rfl⟩
    exact (Classical.choose_spec (hEnds_color c)).1
  have hEIL_card : E_IL.card = IL.card :=
    Finset.card_image_of_injective _ (fun a b h => Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega))
  have hEIR_card : E_IR.card = IR.card :=
    Finset.card_image_of_injective _ (fun a b h => Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega))
  have hEC_card : E_C.card = k := by
    rw [Finset.card_image_of_injective]
    · simp
    · intro c1 c2 h
      dsimp only at h
      have h1 := (Classical.choose_spec (hEnds_color c1)).2.2
      have h2 := (Classical.choose_spec (hEnds_color c2)).2.2
      rw [h] at h1
      exact h1.symm.trans h2
  have hd1 : Disjoint E_IL E_IR := by
    rw [Finset.disjoint_left]
    intro v h1 h2
    rcases Finset.mem_image.mp h1 with ⟨i, _, rfl⟩
    rcases Finset.mem_image.mp h2 with ⟨j, _, heq⟩
    have := congrArg Fin.val heq; dsimp at this; omega
  have hd2 : Disjoint E_IL E_C := by
    rw [Finset.disjoint_left]
    intro v h1 h2
    rcases Finset.mem_image.mp h1 with ⟨i, hi, rfl⟩
    rcases Finset.mem_image.mp h2 with ⟨c, _, heq⟩
    have hcolV := (Classical.choose_spec (hEnds_color c)).2.1
    rw [heq] at hcolV
    simp only [isColV, Nat.mul_mod_right, ↓reduceIte] at hcolV
    have hi' : (⟨2 * i.val / 2, by omega⟩ : Fin n) = i := Fin.ext (by dsimp; omega)
    rw [hi'] at hcolV
    exact Finset.disjoint_right.mp hIL_disj_AL hi hcolV
  have hd3 : Disjoint E_IR E_C := by
    rw [Finset.disjoint_left]
    intro v h1 h2
    rcases Finset.mem_image.mp h1 with ⟨j, hj, rfl⟩
    rcases Finset.mem_image.mp h2 with ⟨c, _, heq⟩
    have hcolV := (Classical.choose_spec (hEnds_color c)).2.1
    rw [heq] at hcolV
    have hodd : (2 * j.val + 1) % 2 ≠ 0 := by omega
    simp only [isColV, hodd, ↓reduceIte] at hcolV
    have hj' : (⟨(2 * j.val + 1) / 2, by omega⟩ : Fin n) = j := Fin.ext (by dsimp; omega)
    rw [hj'] at hcolV
    exact Finset.disjoint_right.mp hIR_disj_AR hj hcolV
  have hEnds_ge : IL.card + IR.card + k ≤ Ends.card := by
    have hsub : E_IL ∪ E_IR ∪ E_C ⊆ Ends :=
      Finset.union_subset (Finset.union_subset hEIL_sub hEIR_sub) hEC_sub
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hd2, hd3⟩),
      Finset.card_union_of_disjoint hd1, hEIL_card, hEIR_card, hEC_card] at hcard
    exact hcard
  exact ⟨Live.card, Dead.card, Ends.card, hLive_Dead, hLive_card, hEnds_le_Dead, hEnds_le_Live, hEnds_ge⟩

theorem main :
    ∀ (t : ℕ) (ht : 0 < t) (k : ℕ), 3 ≤ k →
      let F := ZMod 2
      let n := 3*t
      let W := Fin n → F
      let ix := fun j : ℕ => (⟨j % n, Nat.mod_lt _ (Nat.mul_pos (Nat.succ_pos 2) ht)⟩ : Fin n)
      let code := fun (x : W) => ∀ e : Fin 2,
        (∑ i : Fin n, if i.val % 3 = e.val ∨ i.val % 3 = 2 then x i else 0) = 0
      ∀ P Q : Submodule F W, (∀ x ∈ P, code x) → (∀ y ∈ Q, code y) →
        let left := fun (e : Fin (2*n)) => ix ((e.val+1)/2)
        let right := fun (e : Fin (2*n)) => ix (e.val/2)
        ∀ s : Fin k → Fin (2*n),
          Function.Surjective (fun x : P => fun c : Fin k => x.val (left (s c))) →
          Function.Surjective (fun y : Q => fun c : Fin k => y.val (right (s c))) →
          (∀ e : Fin (2*n), (∀ x : P, x.val (left e) = 0) ∨ (∀ y : Q, y.val (right e) = 0) ∨
            ∃ c : Fin k, (∀ x : P, x.val (left e) = x.val (left (s c))) ∧
              (∀ y : Q, y.val (right e) = y.val (right (s c)))) →
          2*(Module.finrank F P + Module.finrank F Q)+5 ≤ 2*n+k := by
  classical
  dsimp only
  intro t ht k hk P Q hPcode hQcode s hPsurj hQsurj hedge
  let F := ZMod 2
  let n := 3 * t
  have hn_pos : 0 < n := by omega
  let ix : ℕ → Fin n := fun j => ⟨j % n, Nat.mod_lt _ hn_pos⟩
  let left : Fin (2 * n) → Fin n := fun e => ix ((e.val + 1) / 2)
  let right : Fin (2 * n) → Fin n := fun e => ix (e.val / 2)
  have hPdist : ∀ c1 c2 : Fin k, (∀ x : P, x.val (left (s c1)) = x.val (left (s c2))) → c1 = c2 := by
    intro c1 c2 heq
    by_contra hne
    obtain ⟨x, hx⟩ := hPsurj (fun c => if c = c1 then (1 : F) else 0)
    have h1 : x.val (left (s c1)) = 1 := by simpa using congrFun hx c1
    have h2 : x.val (left (s c2)) = 0 := by simpa [Ne.symm hne] using congrFun hx c2
    rw [heq x] at h1
    rw [h1] at h2
    exact one_ne_zero h2
  have hQdist : ∀ c1 c2 : Fin k, (∀ y : Q, y.val (right (s c1)) = y.val (right (s c2))) → c1 = c2 := by
    intro c1 c2 heq
    by_contra hne
    obtain ⟨y, hy⟩ := hQsurj (fun c => if c = c1 then (1 : F) else 0)
    have h1 : y.val (right (s c1)) = 1 := by simpa using congrFun hy c1
    have h2 : y.val (right (s c2)) = 0 := by simpa [Ne.symm hne] using congrFun hy c2
    rw [heq y] at h1
    rw [h1] at h2
    exact one_ne_zero h2
  have hPnz : ∀ c : Fin k, ¬ (∀ x : P, x.val (left (s c)) = 0) := by
    intro c h0
    obtain ⟨x, hx⟩ := hPsurj (fun _ => (1 : F))
    have h1 : x.val (left (s c)) = 1 := congrFun hx c
    rw [h0 x] at h1
    exact zero_ne_one h1
  have hQnz : ∀ c : Fin k, ¬ (∀ y : Q, y.val (right (s c)) = 0) := by
    intro c h0
    obtain ⟨y, hy⟩ := hQsurj (fun _ => (1 : F))
    have h1 : y.val (right (s c)) = 1 := congrFun hy c
    rw [h0 y] at h1
    exact zero_ne_one h1
  let ZP : Finset (Fin n) := Finset.univ.filter (fun i => ∀ x : P, x.val i = 0)
  let ZQ : Finset (Fin n) := Finset.univ.filter (fun j => ∀ y : Q, y.val j = 0)
  let Eact : Finset (Fin (2 * n)) :=
    Finset.univ.filter (fun e => left e ∉ ZP ∧ right e ∉ ZQ)
  have hEact_col : ∀ e ∈ Eact,
      ∃ c : Fin k, (∀ x : P, x.val (left e) = x.val (left (s c))) ∧
        (∀ y : Q, y.val (right e) = y.val (right (s c))) := by
    intro e he
    simp only [Eact, ZP, ZQ, Finset.mem_filter, Finset.mem_univ, true_and] at he
    rcases hedge e with h1 | h2 | h3
    · exact absurd h1 he.1
    · exact absurd h2 he.2
    · exact h3
  have hs_act : ∀ c : Fin k, s c ∈ Eact := by
    intro c
    simp only [Eact, ZP, ZQ, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hPnz c, hQnz c⟩
  let AL : Finset (Fin n) := Finset.univ.filter (fun i => ∃ e ∈ Eact, left e = i)
  let AR : Finset (Fin n) := Finset.univ.filter (fun j => ∃ e ∈ Eact, right e = j)
  let IL : Finset (Fin n) := Finset.univ.filter (fun i => i ∉ ZP ∧ i ∉ AL)
  let IR : Finset (Fin n) := Finset.univ.filter (fun j => j ∉ ZQ ∧ j ∉ AR)
  have hAL_disj_ZP : Disjoint ZP AL := by
    rw [Finset.disjoint_left]
    intro i hiZ hiA
    rcases (Finset.mem_filter.mp hiA).2 with ⟨e, he, rfl⟩
    exact (Finset.mem_filter.mp he).2.1 hiZ
  have hAR_disj_ZQ : Disjoint ZQ AR := by
    rw [Finset.disjoint_left]
    intro j hjZ hjA
    rcases (Finset.mem_filter.mp hjA).2 with ⟨e, he, rfl⟩
    exact (Finset.mem_filter.mp he).2.2 hjZ
  have hIL_disj_ZP : Disjoint ZP IL := by
    rw [Finset.disjoint_left]; intro i hiZ hiI; exact (Finset.mem_filter.mp hiI).2.1 hiZ
  have hIL_disj_AL : Disjoint AL IL := by
    rw [Finset.disjoint_left]; intro i hiA hiI; exact (Finset.mem_filter.mp hiI).2.2 hiA
  have hIR_disj_ZQ : Disjoint ZQ IR := by
    rw [Finset.disjoint_left]; intro j hjZ hjI; exact (Finset.mem_filter.mp hjI).2.1 hjZ
  have hIR_disj_AR : Disjoint AR IR := by
    rw [Finset.disjoint_left]; intro j hjA hjI; exact (Finset.mem_filter.mp hjI).2.2 hjA
  have hPcov : ZP ∪ AL ∪ IL = Finset.univ := by
    ext i
    simp only [Finset.mem_union, IL, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    tauto
  have hQcov : ZQ ∪ AR ∪ IR = Finset.univ := by
    ext j
    simp only [Finset.mem_union, IR, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    tauto
  have hAL_col_ex : ∀ i ∈ AL, ∃ c : Fin k, ∀ x : P, x.val i = x.val (left (s c)) := by
    intro i hi
    rcases (Finset.mem_filter.mp hi).2 with ⟨e, he, rfl⟩
    rcases hEact_col e he with ⟨c, hcL, _⟩
    exact ⟨c, hcL⟩
  have hAR_col_ex : ∀ j ∈ AR, ∃ c : Fin k, ∀ y : Q, y.val j = y.val (right (s c)) := by
    intro j hj
    rcases (Finset.mem_filter.mp hj).2 with ⟨e, he, rfl⟩
    rcases hEact_col e he with ⟨c, _, hcR⟩
    exact ⟨c, hcR⟩
  have hkpos : 0 < k := by omega
  let c0 : Fin k := ⟨0, hkpos⟩
  let cL : Fin n → Fin k := fun i =>
    if h : i ∈ AL then Classical.choose (hAL_col_ex i h) else c0
  let cR : Fin n → Fin k := fun j =>
    if h : j ∈ AR then Classical.choose (hAR_col_ex j h) else c0
  have hcL_spec : ∀ i ∈ AL, ∀ x : P, x.val i = x.val (left (s (cL i))) := by
    intro i hi
    simp only [cL, hi, ↓reduceDIte]
    exact Classical.choose_spec (hAL_col_ex i hi)
  have hcR_spec : ∀ j ∈ AR, ∀ y : Q, y.val j = y.val (right (s (cR j))) := by
    intro j hj
    simp only [cR, hj, ↓reduceDIte]
    exact Classical.choose_spec (hAR_col_ex j hj)
  have hrepL : ∀ c : Fin k, left (s c) ∈ AL ∧ cL (left (s c)) = c := by
    intro c
    have hmem : left (s c) ∈ AL :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, s c, hs_act c, rfl⟩
    refine ⟨hmem, hPdist _ _ fun x => (hcL_spec _ hmem x).symm⟩
  have hrepR : ∀ c : Fin k, right (s c) ∈ AR ∧ cR (right (s c)) = c := by
    intro c
    have hmem : right (s c) ∈ AR :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, s c, hs_act c, rfl⟩
    refine ⟨hmem, hQdist _ _ fun y => (hcR_spec _ hmem y).symm⟩
  have hedge_same_col : ∀ e ∈ Eact, cL (left e) = cR (right e) := by
    intro e he
    rcases hEact_col e he with ⟨c, hcL, hcR⟩
    have hmemL : left e ∈ AL := Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, he, rfl⟩
    have hmemR : right e ∈ AR := Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, he, rfl⟩
    have h1 : cL (left e) = c := hPdist _ _ fun x => (hcL_spec _ hmemL x).symm.trans (hcL x)
    have h2 : cR (right e) = c := hQdist _ _ fun y => (hcR_spec _ hmemR y).symm.trans (hcR y)
    rw [h1, h2]
  obtain ⟨rP, hrP2, hdimP, hrP0, hrP1⟩ :=
    finrank_le_card_add_k_sub_syndrome t k P hPcode ZP AL IL
      hAL_disj_ZP hIL_disj_ZP hIL_disj_AL hPcov
      (fun i hi x hx => (Finset.mem_filter.mp hi).2 ⟨x, hx⟩)
      (fun c => left (s c)) cL hrepL
      (fun i hi x hx => hcL_spec i hi ⟨x, hx⟩)
  obtain ⟨rQ, hrQ2, hdimQ, hrQ0, hrQ1⟩ :=
    finrank_le_card_add_k_sub_syndrome t k Q hQcode ZQ AR IR
      hAR_disj_ZQ hIR_disj_ZQ hIR_disj_AR hQcov
      (fun j hj y hy => (Finset.mem_filter.mp hj).2 ⟨y, hy⟩)
      (fun c => right (s c)) cR hrepR
      (fun j hj y hy => hcR_spec j hj ⟨y, hy⟩)
  have hAL_sum : AL.card = ∑ c : Fin k, (AL.filter (fun i => cL i = c)).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext i
      simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and]
      exact ⟨fun hi => ⟨cL i, hi, rfl⟩, fun ⟨_, hi, _⟩ => hi⟩
    · intro c1 _ c2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro i h1 h2
      exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
  have hAR_sum : AR.card = ∑ c : Fin k, (AR.filter (fun j => cR j = c)).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext j
      simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and]
      exact ⟨fun hj => ⟨cR j, hj, rfl⟩, fun ⟨_, hj, _⟩ => hj⟩
    · intro c1 _ c2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro j h1 h2
      exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
  have hAL_ge_k : k ≤ AL.card := by
    rw [hAL_sum]
    have : ∑ _c : Fin k, 1 ≤ ∑ c : Fin k, (AL.filter (fun i => cL i = c)).card :=
      Finset.sum_le_sum fun c _ => Finset.card_pos.mpr ⟨left (s c), Finset.mem_filter.mpr (hrepL c)⟩
    simpa using this
  have hAR_ge_k : k ≤ AR.card := by
    rw [hAR_sum]
    have : ∑ _c : Fin k, 1 ≤ ∑ c : Fin k, (AR.filter (fun j => cR j = c)).card :=
      Finset.sum_le_sum fun c _ => Finset.card_pos.mpr ⟨right (s c), Finset.mem_filter.mpr (hrepR c)⟩
    simpa using this
  obtain ⟨nLive, nDead, nEnds, hLive_Dead, hLive_card, hEnds_le_Dead, hEnds_le_Live, hEnds_ge⟩ :=
    cycle_ends_bound n k hn_pos hk ZP ZQ AL AR IL IR
      hAL_disj_ZP hIL_disj_ZP hIL_disj_AL hPcov
      hAR_disj_ZQ hIR_disj_ZQ hIR_disj_AR hQcov
      Eact left right (fun _ => rfl) (fun _ => rfl)
      (fun e => by simp only [Eact, Finset.mem_filter, Finset.mem_univ, true_and])
      (fun e he => Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, he, rfl⟩)
      (fun e he => Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, he, rfl⟩)
      s hs_act cL cR hrepL hedge_same_col
  have hdimP' : Module.finrank F P + rP ≤ IL.card + k := hdimP
  have hdimQ' : Module.finrank F Q + rQ ≤ IR.card + k := hdimQ
  have hn_eq : n = 3 * t := rfl
  change 2 * (Module.finrank F P + Module.finrank F Q) + 5 ≤ 2 * n + k
  have hmaster : 2 * (Module.finrank F P + Module.finrank F Q) +
      (AL.card - k) + (AR.card - k) + (nDead - nEnds) +
      (nEnds - (IL.card + IR.card + k)) + 2 * (rP + rQ) ≤ 2 * n + k := by
    omega
  by_cases hsum3 : 3 ≤ rP + rQ
  · omega
  · by_cases hrP0_case : rP = 0
    · have hAL_2k : 2 * k ≤ AL.card := by
        rw [hAL_sum]
        have : ∑ _c : Fin k, 2 ≤ ∑ c : Fin k, (AL.filter (fun i => cL i = c)).card :=
          Finset.sum_le_sum fun c _ => hrP0 hrP0_case c
        simpa [mul_comm] using this
      by_cases hrQ0_case : rQ = 0
      · have hAR_2k : 2 * k ≤ AR.card := by
          rw [hAR_sum]
          have : ∑ _c : Fin k, 2 ≤ ∑ c : Fin k, (AR.filter (fun j => cR j = c)).card :=
            Finset.sum_le_sum fun c _ => hrQ0 hrQ0_case c
          simpa [mul_comm] using this
        omega
      · omega
    · by_cases hrQ0_case : rQ = 0
      · have hAR_2k : 2 * k ≤ AR.card := by
          rw [hAR_sum]
          have : ∑ _c : Fin k, 2 ≤ ∑ c : Fin k, (AR.filter (fun j => cR j = c)).card :=
            Finset.sum_le_sum fun c _ => hrQ0 hrQ0_case c
          simpa [mul_comm] using this
        omega
      · have hrP1_eq : rP = 1 := by omega
        have hrQ1_eq : rQ = 1 := by omega
        by_cases hex0 : (AL.card - k) + (AR.card - k) + (nDead - nEnds) = 0
        · exfalso
          have hAL_eq_k : AL.card = k := by omega
          have hAR_eq_k : AR.card = k := by omega
          have hDead_eq : nDead = nEnds := by omega
          have hAL_c1 : ∀ c : Fin k, (AL.filter (fun i => cL i = c)).card = 1 := by
            intro c
            by_contra hne1
            have hge1 : 1 ≤ (AL.filter (fun i => cL i = c)).card :=
              Finset.card_pos.mpr ⟨left (s c), Finset.mem_filter.mpr (hrepL c)⟩
            have hge2 : 2 ≤ (AL.filter (fun i => cL i = c)).card := by omega
            have hsum_gt : k < ∑ c' : Fin k, (AL.filter (fun i => cL i = c')).card := by
              have h1 : ∑ c' : Fin k, (if c' = c then 2 else 1) ≤
                  ∑ c' : Fin k, (AL.filter (fun i => cL i = c')).card := by
                refine Finset.sum_le_sum fun c' _ => ?_
                by_cases hc' : c' = c
                · subst hc'; simpa using hge2
                · simp only [hc', ↓reduceIte]
                  exact Finset.card_pos.mpr ⟨left (s c'), Finset.mem_filter.mpr (hrepL c')⟩
              have h2 : ∑ c' : Fin k, (if c' = c then 2 else 1) = k + 1 := by
                rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
                have hf1 : (Finset.univ.filter (fun c' : Fin k => c' = c)).card = 1 := by
                  have : Finset.univ.filter (fun c' : Fin k => c' = c) = {c} := by ext x; simp
                  rw [this, Finset.card_singleton]
                have hf2 : (Finset.univ.filter (fun c' : Fin k => ¬ c' = c)).card = k - 1 := by
                  have : Finset.univ.filter (fun c' : Fin k => ¬ c' = c) = Finset.univ.erase c := by ext x; simp
                  rw [this, Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]
                rw [hf1, hf2]
                simp only [smul_eq_mul]
                omega
              omega
            omega
          have hAR_c1 : ∀ c : Fin k, (AR.filter (fun j => cR j = c)).card = 1 := by
            intro c
            by_contra hne1
            have hge1 : 1 ≤ (AR.filter (fun j => cR j = c)).card :=
              Finset.card_pos.mpr ⟨right (s c), Finset.mem_filter.mpr (hrepR c)⟩
            have hge2 : 2 ≤ (AR.filter (fun j => cR j = c)).card := by omega
            have hsum_gt : k < ∑ c' : Fin k, (AR.filter (fun j => cR j = c')).card := by
              have h1 : ∑ c' : Fin k, (if c' = c then 2 else 1) ≤
                  ∑ c' : Fin k, (AR.filter (fun j => cR j = c')).card := by
                refine Finset.sum_le_sum fun c' _ => ?_
                by_cases hc' : c' = c
                · subst hc'; simpa using hge2
                · simp only [hc', ↓reduceIte]
                  exact Finset.card_pos.mpr ⟨right (s c'), Finset.mem_filter.mpr (hrepR c')⟩
              have h2 : ∑ c' : Fin k, (if c' = c then 2 else 1) = k + 1 := by
                rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
                have hf1 : (Finset.univ.filter (fun c' : Fin k => c' = c)).card = 1 := by
                  have : Finset.univ.filter (fun c' : Fin k => c' = c) = {c} := by ext x; simp
                  rw [this, Finset.card_singleton]
                have hf2 : (Finset.univ.filter (fun c' : Fin k => ¬ c' = c)).card = k - 1 := by
                  have : Finset.univ.filter (fun c' : Fin k => ¬ c' = c) = Finset.univ.erase c := by ext x; simp
                  rw [this, Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]
                rw [hf1, hf2]
                simp only [smul_eq_mul]
                omega
              omega
            omega
          obtain ⟨a, ha⟩ := hrP1 hrP1_eq hAL_c1
          obtain ⟨b, hb⟩ := hrQ1 hrQ1_eq hAR_c1
          have hUP_le_t : AL.card + IL.card ≤ t := by
            rw [← Finset.card_union_of_disjoint hIL_disj_AL]
            have hsub : AL ∪ IL ⊆ Finset.univ.filter (fun i : Fin (3 * t) => i.val % 3 = a) :=
              fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha i hi⟩
            exact (Finset.card_le_card hsub).trans (card_filter_mod_three_eq t a)
          have hUQ_le_t : AR.card + IR.card ≤ t := by
            rw [← Finset.card_union_of_disjoint hIR_disj_AR]
            have hsub : AR ∪ IR ⊆ Finset.univ.filter (fun j : Fin (3 * t) => j.val % 3 = b) :=
              fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb j hj⟩
            exact (Finset.card_le_card hsub).trans (card_filter_mod_three_eq t b)
          omega
        · omega

end PEqualNP.Outside.L_lib_1080_aux

theorem PEqualNP.Outside.L_lib_1080 : (∀ (t : ℕ) (ht : 0 < t) (k : ℕ), 3 ≤ k →
  let F := ZMod 2
  let n := 3*t
  let W := Fin n → F
  let ix := fun j : ℕ => (⟨j % n, Nat.mod_lt _ (Nat.mul_pos (Nat.succ_pos 2) ht)⟩ : Fin n)
  let code := fun (x : W) => ∀ e : Fin 2,
    (∑ i : Fin n, if i.val % 3 = e.val ∨ i.val % 3 = 2 then x i else 0) = 0
  ∀ P Q : Submodule F W, (∀ x ∈ P, code x) → (∀ y ∈ Q, code y) →
    let left := fun (e : Fin (2*n)) => ix ((e.val+1)/2)
    let right := fun (e : Fin (2*n)) => ix (e.val/2)
    ∀ s : Fin k → Fin (2*n),
      Function.Surjective (fun x : P => fun c : Fin k => x.val (left (s c))) →
      Function.Surjective (fun y : Q => fun c : Fin k => y.val (right (s c))) →
      (∀ e : Fin (2*n), (∀ x : P, x.val (left e) = 0) ∨ (∀ y : Q, y.val (right e) = 0) ∨
        ∃ c : Fin k, (∀ x : P, x.val (left e) = x.val (left (s c))) ∧
          (∀ y : Q, y.val (right e) = y.val (right (s c)))) →
      2*(Module.finrank F P + Module.finrank F Q)+5 ≤ 2*n+k) :=
  PEqualNP.Outside.L_lib_1080_aux.main
