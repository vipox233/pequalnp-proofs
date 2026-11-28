import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1064_aux

open scoped BigOperators

abbrev F := ZMod 2

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

lemma pure_copy_dim_bound
    (t : ℕ) (ht : 0 < t) (k : ℕ) (hk : 3 ≤ k)
    (P Q : Submodule F (Fin (3 * t) → F))
    (hPcode : ∀ x ∈ P, ∀ e : Fin 2,
      (∑ i : Fin (3 * t), if i.val % 3 = e.val ∨ i.val % 3 = 2 then x i else 0) = 0)
    (hQcode : ∀ y ∈ Q, ∀ e : Fin 2,
      (∑ i : Fin (3 * t), if i.val % 3 = e.val ∨ i.val % 3 = 2 then y i else 0) = 0)
    (s : Fin k → Fin (2 * (3 * t)))
    (hPsurj : Function.Surjective (fun x : P => fun c : Fin k =>
      x.val ⟨((s c).val + 1) / 2 % (3 * t), Nat.mod_lt _ (by omega)⟩))
    (hQsurj : Function.Surjective (fun y : Q => fun c : Fin k =>
      y.val ⟨(s c).val / 2 % (3 * t), Nat.mod_lt _ (by omega)⟩))
    (hedge : ∀ e : Fin (2 * (3 * t)),
      (∀ x : P, x.val ⟨(e.val + 1) / 2 % (3 * t), Nat.mod_lt _ (by omega)⟩ = 0) ∨
      (∀ y : Q, y.val ⟨e.val / 2 % (3 * t), Nat.mod_lt _ (by omega)⟩ = 0) ∨
      ∃ c : Fin k,
        (∀ x : P, x.val ⟨(e.val + 1) / 2 % (3 * t), Nat.mod_lt _ (by omega)⟩ =
          x.val ⟨((s c).val + 1) / 2 % (3 * t), Nat.mod_lt _ (by omega)⟩) ∧
        (∀ y : Q, y.val ⟨e.val / 2 % (3 * t), Nat.mod_lt _ (by omega)⟩ =
          y.val ⟨(s c).val / 2 % (3 * t), Nat.mod_lt _ (by omega)⟩)) :
    2 * (Module.finrank F P + Module.finrank F Q) + 5 ≤ 2 * (3 * t) + k := by
  classical
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
  let Eact : Finset (Fin (2 * n)) := Finset.univ.filter (fun e => left e ∉ ZP ∧ right e ∉ ZQ)
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
    rw [Finset.disjoint_left]; intro i hiZ hiA
    rcases (Finset.mem_filter.mp hiA).2 with ⟨e, he, rfl⟩
    exact (Finset.mem_filter.mp he).2.1 hiZ
  have hAR_disj_ZQ : Disjoint ZQ AR := by
    rw [Finset.disjoint_left]; intro j hjZ hjA
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
    ext i; simp only [Finset.mem_union, IL, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]; tauto
  have hQcov : ZQ ∪ AR ∪ IR = Finset.univ := by
    ext j; simp only [Finset.mem_union, IR, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]; tauto
  have hAL_col_ex : ∀ i ∈ AL, ∃ c : Fin k, ∀ x : P, x.val i = x.val (left (s c)) := by
    intro i hi; rcases (Finset.mem_filter.mp hi).2 with ⟨e, he, rfl⟩
    rcases hEact_col e he with ⟨c, hcL, _⟩; exact ⟨c, hcL⟩
  have hAR_col_ex : ∀ j ∈ AR, ∃ c : Fin k, ∀ y : Q, y.val j = y.val (right (s c)) := by
    intro j hj; rcases (Finset.mem_filter.mp hj).2 with ⟨e, he, rfl⟩
    rcases hEact_col e he with ⟨c, _, hcR⟩; exact ⟨c, hcR⟩
  have hkpos : 0 < k := by omega
  let c0 : Fin k := ⟨0, hkpos⟩
  let cL : Fin n → Fin k := fun i => if h : i ∈ AL then Classical.choose (hAL_col_ex i h) else c0
  let cR : Fin n → Fin k := fun j => if h : j ∈ AR then Classical.choose (hAR_col_ex j h) else c0
  have hcL_spec : ∀ i ∈ AL, ∀ x : P, x.val i = x.val (left (s (cL i))) := by
    intro i hi; simp only [cL, hi, ↓reduceDIte]; exact Classical.choose_spec (hAL_col_ex i hi)
  have hcR_spec : ∀ j ∈ AR, ∀ y : Q, y.val j = y.val (right (s (cR j))) := by
    intro j hj; simp only [cR, hj, ↓reduceDIte]; exact Classical.choose_spec (hAR_col_ex j hj)
  have hrepL : ∀ c : Fin k, left (s c) ∈ AL ∧ cL (left (s c)) = c := by
    intro c
    have hmem : left (s c) ∈ AL := Finset.mem_filter.mpr ⟨Finset.mem_univ _, s c, hs_act c, rfl⟩
    refine ⟨hmem, hPdist _ _ fun x => (hcL_spec _ hmem x).symm⟩
  have hrepR : ∀ c : Fin k, right (s c) ∈ AR ∧ cR (right (s c)) = c := by
    intro c
    have hmem : right (s c) ∈ AR := Finset.mem_filter.mpr ⟨Finset.mem_univ _, s c, hs_act c, rfl⟩
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
      (fun c => left (s c)) cL hrepL (fun i hi x hx => hcL_spec i hi ⟨x, hx⟩)
  obtain ⟨rQ, hrQ2, hdimQ, hrQ0, hrQ1⟩ :=
    finrank_le_card_add_k_sub_syndrome t k Q hQcode ZQ AR IR
      hAR_disj_ZQ hIR_disj_ZQ hIR_disj_AR hQcov
      (fun j hj y hy => (Finset.mem_filter.mp hj).2 ⟨y, hy⟩)
      (fun c => right (s c)) cR hrepR (fun j hj y hy => hcR_spec j hj ⟨y, hy⟩)
  have hAL_sum : AL.card = ∑ c : Fin k, (AL.filter (fun i => cL i = c)).card := by
    rw [← Finset.card_biUnion]
    · congr 1; ext i; simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and]
      exact ⟨fun hi => ⟨cL i, hi, rfl⟩, fun ⟨_, hi, _⟩ => hi⟩
    · intro c1 _ c2 _ hne; change Disjoint _ _; rw [Finset.disjoint_left]
      intro i h1 h2; exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
  have hAR_sum : AR.card = ∑ c : Fin k, (AR.filter (fun j => cR j = c)).card := by
    rw [← Finset.card_biUnion]
    · congr 1; ext j; simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and]
      exact ⟨fun hj => ⟨cR j, hj, rfl⟩, fun ⟨_, hj, _⟩ => hj⟩
    · intro c1 _ c2 _ hne; change Disjoint _ _; rw [Finset.disjoint_left]
      intro j h1 h2; exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
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
            intro c; by_contra hne1
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
                rw [hf1, hf2]; simp only [smul_eq_mul]; omega
              omega
            omega
          have hAR_c1 : ∀ c : Fin k, (AR.filter (fun j => cR j = c)).card = 1 := by
            intro c; by_contra hne1
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
                rw [hf1, hf2]; simp only [smul_eq_mul]; omega
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

lemma support_syndrome_bound (t : ℕ)
    (P0 : Submodule F (Fin (3 * t) → F))
    (U : Finset (Fin (3 * t)))
    (hU_iff : ∀ i : Fin (3 * t), i ∈ U ↔ ∃ x ∈ P0, x i ≠ 0)
    (hcode : ∀ x ∈ P0, ∀ e : Fin 2,
      (∑ i : Fin (3 * t), if i.val % 3 = e.val ∨ i.val % 3 = 2 then x i else 0) = 0)
    (hPne : P0 ≠ ⊥) :
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ 2 ∧
      Module.finrank F P0 + r ≤ U.card ∧
      2 ≤ U.card ∧
      (r = 1 → ∃ a : ℕ, ∀ i ∈ U, i.val % 3 = a) := by
  classical
  let n := 3 * t
  have hU_ne : U.Nonempty := by
    have ⟨x, hxP, hx0⟩ : ∃ x ∈ P0, x ≠ 0 := by
      by_contra hall; push Not at hall
      exact hPne ((Submodule.eq_bot_iff P0).mpr hall)
    have ⟨i, hi⟩ : ∃ i : Fin n, x i ≠ 0 := by
      by_contra h0; push Not at h0; exact hx0 (funext h0)
    exact ⟨i, (hU_iff i).mpr ⟨x, hxP, hi⟩⟩
  let φ : P0 →ₗ[F] (U → F) :=
    { toFun := fun x i => x.1 i.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hφ_inj : Function.Injective φ := by
    intro x y hxy
    apply Subtype.ext; funext i
    by_cases hi : i ∈ U
    · exact congrFun hxy ⟨i, hi⟩
    · have hx0 : x.1 i = 0 := by
        by_contra h; exact hi ((hU_iff i).mpr ⟨x.1, x.2, h⟩)
      have hy0 : y.1 i = 0 := by
        by_contra h; exact hi ((hU_iff i).mpr ⟨y.1, y.2, h⟩)
      rw [hx0, hy0]
  let σ : (U → F) →ₗ[F] (Fin 2 → F) :=
    { toFun := fun v e => ∑ i : U, if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then v i else 0
      map_add' := fun u v => by
        ext e
        change (∑ i : U, if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then u i + v i else (0 : F)) =
          (∑ i : U, if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then u i else 0) +
          (∑ i : U, if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then v i else 0)
        have h1 : ∀ i : U, (if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then u i + v i else (0 : F)) =
            (if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then u i else 0) +
            (if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then v i else 0) := by
          intro i; split_ifs <;> simp
        simp only [h1, Finset.sum_add_distrib]
      map_smul' := fun a v => by
        ext e
        change (∑ i : U, if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then a * v i else (0 : F)) =
          a * (∑ i : U, if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then v i else 0)
        have h1 : ∀ i : U, (if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then a * v i else (0 : F)) =
            a * (if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then v i else 0) := by
          intro i; split_ifs <;> simp
        simp only [h1, ← Finset.mul_sum] }
  have hcomp : σ.comp φ = 0 := by
    apply LinearMap.ext; intro x; ext e
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, Pi.zero_apply, σ, φ,
      LinearMap.coe_mk, AddHom.coe_mk]
    have hsum := hcode x.1 x.2 e
    rw [Finset.sum_coe_sort U (fun i => if i.val % 3 = e.val ∨ i.val % 3 = 2 then x.1 i else (0 : F))]
    have hsub : U ⊆ Finset.univ := Finset.subset_univ U
    rw [Finset.sum_subset hsub]
    · exact hsum
    · intro i _ hiU
      have hx0 : x.1 i = 0 := by
        by_contra h; exact hiU ((hU_iff i).mpr ⟨x.1, x.2, h⟩)
      simp [hx0]
  let r := Module.finrank F (LinearMap.range σ)
  have hr_pos : 1 ≤ r := by
    rcases hU_ne with ⟨i0, hi0⟩
    by_contra h0
    have hr0 : r = 0 := by omega
    have hbot : LinearMap.range σ = ⊥ := Submodule.finrank_eq_zero.mp hr0
    let v : U → F := fun i => if i.1 = i0 then 1 else 0
    have hv0 : σ v = 0 := (Submodule.mem_bot F).mp (hbot ▸ ⟨v, rfl⟩)
    have hev : ∀ e : Fin 2, σ v e = if i0.val % 3 = e.val ∨ i0.val % 3 = 2 then (1 : F) else 0 := by
      intro e
      change (∑ j : U, if j.1.val % 3 = e.val ∨ j.1.val % 3 = 2 then v j else (0 : F)) = _
      rw [Finset.sum_eq_single (⟨i0, hi0⟩ : U)]
      · simp [v]
      · intro b _ hne; have : b.1 ≠ i0 := fun h => hne (Subtype.ext h); simp [v, this]
      · intro h; exact (h (Finset.mem_univ _)).elim
    have h0' := congrFun hv0 0
    have h1' := congrFun hv0 1
    rw [hev 0] at h0'; rw [hev 1] at h1'
    have hm : i0.val % 3 = 0 ∨ i0.val % 3 = 1 ∨ i0.val % 3 = 2 := by omega
    rcases hm with hm | hm | hm
    · simp [hm] at h0'
    · simp [hm] at h1'
    · simp [hm] at h0'
  have hr_le2 : r ≤ 2 := by
    have := Submodule.finrank_le (LinearMap.range σ)
    simpa using this
  have hdim : Module.finrank F P0 + r ≤ U.card := by
    have hsub : LinearMap.range φ ≤ LinearMap.ker σ := by
      rintro _ ⟨x, rfl⟩; rw [LinearMap.mem_ker]; exact LinearMap.congr_fun hcomp x
    have h1 : Module.finrank F P0 = Module.finrank F (LinearMap.range φ) :=
      (LinearEquiv.ofInjective φ hφ_inj).finrank_eq
    have h2 : Module.finrank F (LinearMap.range φ) ≤ Module.finrank F (LinearMap.ker σ) :=
      Submodule.finrank_mono hsub
    have h3 : Module.finrank F (LinearMap.range σ) + Module.finrank F (LinearMap.ker σ) =
        Module.finrank F (U → F) := LinearMap.finrank_range_add_finrank_ker σ
    have hU : Module.finrank F (U → F) = U.card := by simp [Fintype.card_coe]
    omega
  have hP0_pos : 1 ≤ Module.finrank F P0 := by
    by_contra h0
    exact hPne (Submodule.finrank_eq_zero.mp (by omega))
  refine ⟨r, hr_pos, hr_le2, hdim, by omega, ?_⟩
  intro hr1
  obtain ⟨α0, α1, hαne, horthS⟩ := exists_orth_zmod2 (LinearMap.range σ) (by change r < 2; omega)
  have hcoeff : ∀ i ∈ U,
      α0 * (if i.val % 3 = 0 ∨ i.val % 3 = 2 then (1 : F) else 0) +
      α1 * (if i.val % 3 = 1 ∨ i.val % 3 = 2 then (1 : F) else 0) = 0 := by
    intro i hi
    let v : U → F := fun j => if j.1 = i then 1 else 0
    have hv := horthS (σ v) ⟨v, rfl⟩
    have hev : ∀ e : Fin 2, σ v e = if i.val % 3 = e.val ∨ i.val % 3 = 2 then (1 : F) else 0 := by
      intro e
      change (∑ j : U, if j.1.val % 3 = e.val ∨ j.1.val % 3 = 2 then v j else (0 : F)) = _
      rw [Finset.sum_eq_single (⟨i, hi⟩ : U)]
      · simp [v]
      · intro b _ hne; have : b.1 ≠ i := fun h => hne (Subtype.ext h); simp [v, this]
      · intro h; exact (h (Finset.mem_univ _)).elim
    rw [hev 0, hev 1] at hv
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

lemma mixed_zero_space_ceiling (t : ℕ) (ht : 3 ≤ t)
    (P0 Q0 : Submodule F (Fin (3 * t) → F))
    (hPcode : ∀ x ∈ P0, ∀ e : Fin 2,
      (∑ i : Fin (3 * t), if i.val % 3 = e.val ∨ i.val % 3 = 2 then x i else 0) = 0)
    (hQcode : ∀ y ∈ Q0, ∀ e : Fin 2,
      (∑ i : Fin (3 * t), if i.val % 3 = e.val ∨ i.val % 3 = 2 then y i else 0) = 0)
    (hPne : P0 ≠ ⊥) (hQne : Q0 ≠ ⊥)
    (horth : ∀ x ∈ P0, ∀ y ∈ Q0, ∀ i : Fin (3 * t),
      x i * y i = 0 ∧ x ⟨(i.val + 1) % (3 * t), Nat.mod_lt _ (by omega)⟩ * y i = 0) :
    Module.finrank F P0 + Module.finrank F Q0 ≤ 3 * t - 5 := by
  classical
  let n := 3 * t
  have hn_pos : 0 < n := by omega
  let UP : Finset (Fin n) := Finset.univ.filter (fun i => ∃ x ∈ P0, x i ≠ 0)
  let UQ : Finset (Fin n) := Finset.univ.filter (fun j => ∃ y ∈ Q0, y j ≠ 0)
  obtain ⟨rP, hrP1, hrP2, hdimP, hUP2, hrP_mod⟩ :=
    support_syndrome_bound t P0 UP (fun i => by simp [UP]) hPcode hPne
  obtain ⟨rQ, hrQ1, hrQ2, hdimQ, hUQ2, hrQ_mod⟩ :=
    support_syndrome_bound t Q0 UQ (fun j => by simp [UQ]) hQcode hQne
  let pred : Fin n → Fin n := fun i => ⟨(i.val + n - 1) % n, Nat.mod_lt _ hn_pos⟩
  let succ : Fin n → Fin n := fun i => ⟨(i.val + 1) % n, Nat.mod_lt _ hn_pos⟩
  have hsucc_pred : ∀ i : Fin n, succ (pred i) = i := by
    intro i; apply Fin.ext; dsimp [succ, pred]
    have hi := i.2
    rw [Nat.mod_add_mod]
    have : i.val + n - 1 + 1 = i.val + n := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
  have hpred_succ : ∀ i : Fin n, pred (succ i) = i := by
    intro i; apply Fin.ext; dsimp [succ, pred]
    have hi := i.2
    by_cases htop : i.val + 1 < n
    · rw [Nat.mod_eq_of_lt htop]
      have : i.val + 1 + n - 1 = i.val + n := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
    · have : i.val + 1 = n := by omega
      rw [this, Nat.mod_self]
      have : 0 + n - 1 = n - 1 := by omega
      rw [this, Nat.mod_eq_of_lt (by omega)]; omega
  have hpred_inj : Function.Injective pred := Function.LeftInverse.injective hsucc_pred
  have hsucc_inj : Function.Injective succ := Function.LeftInverse.injective hpred_succ
  have hdisj_PQ : Disjoint UP UQ := by
    rw [Finset.disjoint_left]
    intro i hiP hiQ
    rcases (Finset.mem_filter.mp hiP).2 with ⟨x, hxP, hx⟩
    rcases (Finset.mem_filter.mp hiQ).2 with ⟨y, hyQ, hy⟩
    have h0 := (horth x hxP y hyQ i).1
    exact mul_ne_zero hx hy h0
  have hdisj_predP_Q : Disjoint (UP.image pred) UQ := by
    rw [Finset.disjoint_left]
    intro j hjP hjQ
    rcases Finset.mem_image.mp hjP with ⟨i, hiP, rfl⟩
    rcases (Finset.mem_filter.mp hiP).2 with ⟨x, hxP, hx⟩
    rcases (Finset.mem_filter.mp hjQ).2 with ⟨y, hyQ, hy⟩
    have h0 := (horth x hxP y hyQ (pred i)).2
    have heq : (⟨((pred i).val + 1) % n, Nat.mod_lt _ hn_pos⟩ : Fin n) = i := hsucc_pred i
    rw [heq] at h0
    exact mul_ne_zero hx hy h0
  have hdisj_P_succQ : Disjoint UP (UQ.image succ) := by
    rw [Finset.disjoint_left]
    intro i hiP hiQ
    rcases Finset.mem_image.mp hiQ with ⟨j, hjQ, rfl⟩
    rcases (Finset.mem_filter.mp hiP).2 with ⟨x, hxP, hx⟩
    rcases (Finset.mem_filter.mp hjQ).2 with ⟨y, hyQ, hy⟩
    exact mul_ne_zero hx hy (horth x hxP y hyQ j).2
  have hUP_le : (UP ∪ UP.image pred).card + UQ.card ≤ n := by
    have hd : Disjoint (UP ∪ UP.image pred) UQ := Finset.disjoint_union_left.mpr ⟨hdisj_PQ, hdisj_predP_Q⟩
    have hle := Finset.card_le_univ ((UP ∪ UP.image pred) ∪ UQ)
    rw [Finset.card_union_of_disjoint hd, Fintype.card_fin] at hle
    exact hle
  have hUQ_le : UP.card + (UQ ∪ UQ.image succ).card ≤ n := by
    have hd : Disjoint UP (UQ ∪ UQ.image succ) := Finset.disjoint_union_right.mpr ⟨hdisj_PQ, hdisj_P_succQ⟩
    have hle := Finset.card_le_univ (UP ∪ (UQ ∪ UQ.image succ))
    rw [Finset.card_union_of_disjoint hd, Fintype.card_fin] at hle
    exact hle
  have hsucc_mod_ne : ∀ i : Fin n, (succ i).val % 3 ≠ i.val % 3 := by
    intro i; dsimp [succ]
    have hi := i.2
    by_cases htop : i.val + 1 < n
    · rw [Nat.mod_eq_of_lt htop]; omega
    · have : i.val + 1 = 3 * t := by omega
      rw [this, Nat.mod_self]; omega
  by_cases hP1 : rP = 1
  · obtain ⟨a, ha⟩ := hrP_mod hP1
    have hdisj_self : Disjoint UP (UP.image pred) := by
      rw [Finset.disjoint_left]
      intro i hi1 hi2
      rcases Finset.mem_image.mp hi2 with ⟨j, hj, rfl⟩
      have h1 := ha (pred j) hi1
      have h2 := ha j hj
      have hne := hsucc_mod_ne (pred j)
      rw [hsucc_pred j] at hne
      omega
    have hun_card : (UP ∪ UP.image pred).card = 2 * UP.card := by
      rw [Finset.card_union_of_disjoint hdisj_self, Finset.card_image_of_injective _ hpred_inj]; omega
    by_cases hQ1 : rQ = 1
    · obtain ⟨b, hb⟩ := hrQ_mod hQ1
      have hUP_t : UP.card ≤ t := by
        have hsub : UP ⊆ Finset.univ.filter (fun i : Fin (3 * t) => i.val % 3 = a) :=
          fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha i hi⟩
        exact (Finset.card_le_card hsub).trans (card_filter_mod_three_eq t a)
      have hUQ_t : UQ.card ≤ t := by
        have hsub : UQ ⊆ Finset.univ.filter (fun j : Fin (3 * t) => j.val % 3 = b) :=
          fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb j hj⟩
        exact (Finset.card_le_card hsub).trans (card_filter_mod_three_eq t b)
      omega
    · omega
  · by_cases hQ1 : rQ = 1
    · obtain ⟨b, hb⟩ := hrQ_mod hQ1
      have hdisj_self : Disjoint UQ (UQ.image succ) := by
        rw [Finset.disjoint_left]
        intro i hi1 hi2
        rcases Finset.mem_image.mp hi2 with ⟨j, hj, rfl⟩
        have h1 := hb (succ j) hi1
        have h2 := hb j hj
        have hne := hsucc_mod_ne j
        omega
      have hun_card : (UQ ∪ UQ.image succ).card = 2 * UQ.card := by
        rw [Finset.card_union_of_disjoint hdisj_self, Finset.card_image_of_injective _ hsucc_inj]; omega
      omega
    · have hex_out : ∃ i ∈ UP, pred i ∉ UP := by
        by_contra hall
        push Not at hall
        have hUP_ne : UP.Nonempty := Finset.card_pos.mp (by omega)
        have hUQ_ne : UQ.Nonempty := Finset.card_pos.mp (by omega)
        rcases hUP_ne with ⟨i0, hi0⟩
        rcases hUQ_ne with ⟨j0, hj0⟩
        have hstep : ∀ d : ℕ, pred^[d] i0 ∈ UP := by
          intro d
          induction d with
          | zero => exact hi0
          | succ d ih => rw [Function.iterate_succ_apply']; exact hall _ ih
        have hiter : ∀ d : ℕ, (pred^[d] i0).val = (i0.val + d * (n - 1)) % n := by
          intro d
          induction d with
          | zero => simp [Nat.mod_eq_of_lt i0.2]
          | succ d ih =>
            rw [Function.iterate_succ_apply']
            dsimp [pred]
            rw [ih]
            have h1 : ((i0.val + d * (n - 1)) % n + n - 1) % n =
                ((i0.val + d * (n - 1)) % n + (n - 1)) % n := by
              congr 1; omega
            rw [h1, Nat.mod_add_mod]
            congr 1; ring
        let d0 := (i0.val + n - j0.val) % n
        have hhit : pred^[d0] i0 = j0 := by
          apply Fin.ext
          rw [hiter d0]
          have hi0lt := i0.2; have hj0lt := j0.2
          have hd0lt : d0 < n := Nat.mod_lt _ hn_pos
          have hmod : (i0.val + d0 * (n - 1)) % n = j0.val := by
            have hsum : i0.val + d0 * (n - 1) + d0 = i0.val + d0 * n := by
              have : d0 * (n - 1) + d0 = d0 * n := by
                calc d0 * (n - 1) + d0 = d0 * (n - 1 + 1) := by ring
                  _ = d0 * n := by rw [Nat.sub_add_cancel (by omega)]
              omega
            have hcongr : (i0.val + d0 * (n - 1) + d0) % n = i0.val % n := by
              rw [hsum, Nat.add_mul_mod_self_right]
            have hd0_eq : (j0.val + d0) % n = i0.val := by
              dsimp [d0]
              rw [Nat.add_mod_mod]
              have : j0.val + (i0.val + n - j0.val) = i0.val + n := by omega
              rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hi0lt]
            have h1 : (i0.val + d0 * (n - 1)) % n + d0 ≡ j0.val + d0 [MOD n] := by
              show ((i0.val + d0 * (n - 1)) % n + d0) % n = (j0.val + d0) % n
              rw [Nat.mod_add_mod, hcongr, Nat.mod_eq_of_lt hi0lt, hd0_eq]
            have h2 := Nat.ModEq.add_right_cancel' d0 h1
            show (i0.val + d0 * (n - 1)) % n = j0.val
            rw [← Nat.mod_eq_of_lt hj0lt]
            exact (Nat.mod_eq_of_lt (Nat.mod_lt _ hn_pos)).symm.trans h2
          exact hmod
        have hj0P : j0 ∈ UP := hhit ▸ hstep d0
        exact Finset.disjoint_left.mp hdisj_PQ hj0P hj0
      rcases hex_out with ⟨i0, hi0, hpred0⟩
      have hcard_gt : UP.card + 1 ≤ (UP ∪ UP.image pred).card := by
        have hsub : insert (pred i0) UP ⊆ UP ∪ UP.image pred := by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hxU
          · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i0, hi0, rfl⟩)
          · exact Finset.mem_union_left _ hxU
        have h1 := Finset.card_le_card hsub
        rw [Finset.card_insert_of_notMem hpred0] at h1
        exact h1
      omega

lemma mem_span_inter_of_forall_erase {E U : Type*} [DecidableEq E]
    [AddCommGroup U] [Module F U]
    (f : E → U) (I S : Finset E)
    (hind : LinearIndependent F (fun i : I => f i.1))
    (u : U) (hmem : u ∈ Submodule.span F (f '' (I : Set E)))
    (herase : ∀ x ∈ I, x ∉ S → u ∈ Submodule.span F (f '' ((I.erase x : Finset E) : Set E))) :
    u ∈ Submodule.span F (f '' ((I ∩ S : Finset E) : Set E)) := by
  classical
  have hrep : ∃ c : I → F, u = ∑ i : I, c i • f i.1 := by
    have h1 : f '' (I : Set E) = Set.range (fun i : I => f i.1) := by
      ext v; simp
    rw [h1, Submodule.mem_span_range_iff_exists_fun] at hmem
    rcases hmem with ⟨c, rfl⟩
    exact ⟨c, rfl⟩
  rcases hrep with ⟨c, hu⟩
  have hc0 : ∀ i : I, i.1 ∉ S → c i = 0 := by
    intro i hiS
    have hmem_e := herase i.1 i.2 hiS
    have h1 : f '' ((I.erase i.1 : Finset E) : Set E) =
        Set.range (fun j : I.erase i.1 => f j.1) := by
      ext v; simp [and_comm]
    rw [h1, Submodule.mem_span_range_iff_exists_fun] at hmem_e
    rcases hmem_e with ⟨d, hd⟩
    let d' : I → F := fun j => if h : j.1 ∈ I.erase i.1 then d ⟨j.1, h⟩ else 0
    have hd'_sum : ∑ j : I, d' j • f j.1 = u := by
      rw [← hd]
      have hfilt : ∑ j : I, d' j • f j.1 = ∑ j ∈ I.erase i.1, if h : j ∈ I.erase i.1 then d ⟨j, h⟩ • f j else 0 := by
        have h1' : ∑ j : I, d' j • f j.1 = ∑ j ∈ I, if h : j ∈ I then d' ⟨j, h⟩ • f j else 0 := by
          rw [← Finset.sum_coe_sort I (fun j => if h : j ∈ I then d' ⟨j, h⟩ • f j else 0)]
          exact Finset.sum_congr rfl fun j _ => by simp [j.2]
        rw [h1', ← Finset.sum_subset (Finset.erase_subset i.1 I)]
        · refine Finset.sum_congr rfl fun j hj => ?_
          have hjI : j ∈ I := Finset.mem_of_mem_erase hj
          dsimp only [d']
          rw [dif_pos hjI, dif_pos hj, dif_pos hj]
        · intro j hjI hjE
          dsimp only [d']
          rw [dif_pos hjI, dif_neg hjE, zero_smul]
      have hfilt2 : ∑ j ∈ I.erase i.1, (if h : j ∈ I.erase i.1 then d ⟨j, h⟩ • f j else 0) =
          ∑ j : I.erase i.1, d j • f j.1 := by
        rw [← Finset.sum_coe_sort (I.erase i.1) (fun j => if h : j ∈ I.erase i.1 then d ⟨j, h⟩ • f j else 0)]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp [j.2]
      exact hfilt.trans hfilt2
    have hdiff : ∑ j : I, (c j - d' j) • f j.1 = 0 := by
      simp_rw [sub_smul, Finset.sum_sub_distrib, ← hu, hd'_sum, sub_self]
    have hzero := Fintype.linearIndependent_iff.mp hind (fun j => c j - d' j) hdiff i
    have hdi : d' i = 0 := by simp [d']
    rw [hdi, sub_zero] at hzero
    exact hzero
  have hu_inter : u = ∑ i ∈ (I ∩ S).attach,
      c ⟨i.1, (Finset.mem_inter.mp i.2).1⟩ • f i.1 := by
    rw [hu]
    have h1 : ∑ i : I, c i • f i.1 =
        ∑ i ∈ I, if h : i ∈ I then c ⟨i, h⟩ • f i else 0 := by
      rw [← Finset.sum_coe_sort I (fun i => if h : i ∈ I then c ⟨i, h⟩ • f i else 0)]
      refine Finset.sum_congr rfl fun i _ => by simp [i.2]
    rw [h1, ← Finset.sum_subset Finset.inter_subset_left]
    · rw [← Finset.sum_coe_sort (I ∩ S) (fun i => if h : i ∈ I then c ⟨i, h⟩ • f i else 0)]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hiI : i.1 ∈ I := (Finset.mem_inter.mp i.2).1
      simp [hiI]
    · intro x hxI hxIS
      have hxS : x ∉ S := fun h => hxIS (Finset.mem_inter.mpr ⟨hxI, h⟩)
      simp [hxI, hc0 ⟨x, hxI⟩ hxS]
  rw [hu_inter]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i.1, i.2, rfl⟩)

lemma linear_matroid_intersection {E U V : Type*} [Fintype E] [DecidableEq E]
    [AddCommGroup U] [Module F U] [Module.Finite F U]
    [AddCommGroup V] [Module F V] [Module.Finite F V]
    (f : E → U) (g : E → V) :
    ∃ (I A : Finset E),
      LinearIndependent F (fun e : I => f e.1) ∧
      LinearIndependent F (fun e : I => g e.1) ∧
      I.card = Module.finrank F (Submodule.span F (f '' (A : Set E))) +
        Module.finrank F (Submodule.span F (g '' ((Finset.univ \ A : Finset E) : Set E))) := by
  classical
  let Common : Finset (Finset E) := (Finset.univ : Finset (Finset E)).filter (fun (I : Finset E) =>
    LinearIndependent F (fun e : I => f e.1) ∧ LinearIndependent F (fun e : I => g e.1))
  have hCommon_ne : Common.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩⟩
    · exact linearIndependent_empty_type
    · exact linearIndependent_empty_type
  obtain ⟨I, hIC, hImax⟩ := Finset.exists_max_image Common Finset.card hCommon_ne
  have hIf : LinearIndependent F (fun e : I => f e.1) := (Finset.mem_filter.mp hIC).2.1
  have hIg : LinearIndependent F (fun e : I => g e.1) := (Finset.mem_filter.mp hIC).2.2
  let X1 : Finset E := Finset.univ.filter (fun e => e ∉ I ∧ f e ∉ Submodule.span F (f '' (I : Set E)))
  let X2 : Finset E := Finset.univ.filter (fun e => e ∉ I ∧ g e ∉ Submodule.span F (g '' (I : Set E)))
  let ValidPath : ∀ (m : ℕ), (Fin (m + 1) → E) → (Fin m → E) → Prop := fun m y x =>
    y 0 ∈ X1 ∧
    (∀ i : Fin m, x i ∈ I ∧ g (y i.castSucc) ∉ Submodule.span F (g '' ((I.erase (x i) : Finset E) : Set E))) ∧
    (∀ i : Fin m, y i.succ ∉ I ∧ f (y i.succ) ∉ Submodule.span F (f '' ((I.erase (x i) : Finset E) : Set E)))
  by_cases hpath : ∃ m : ℕ, ∃ (y : Fin (m + 1) → E) (x : Fin m → E),
      ValidPath m y x ∧ y (Fin.last m) ∈ X2
  · exfalso
    let m := Nat.find hpath
    obtain ⟨y, x, hVP, hyend⟩ := Nat.find_spec hpath
    have hmin : ∀ m' < m, ¬ ∃ (y' : Fin (m' + 1) → E) (x' : Fin m' → E),
        ValidPath m' y' x' ∧ y' (Fin.last m') ∈ X2 := fun m' hm' => Nat.find_min hpath hm'
    have hy_notI : ∀ r : Fin (m + 1), y r ∉ I := by
      intro r
      rcases Fin.eq_zero_or_eq_succ r with rfl | ⟨i, rfl⟩
      · exact (Finset.mem_filter.mp hVP.1).2.1
      · exact (hVP.2.2 i).1
    have hx_inI : ∀ i : Fin m, x i ∈ I := fun i => (hVP.2.1 i).1
    have hno_X1 : ∀ r : Fin (m + 1), 0 < r.val → y r ∉ X1 := by
      intro r hr hX1
      let m' := m - r.val
      have hm'_lt : m' < m := by omega
      let y' : Fin (m' + 1) → E := fun j => y ⟨r.val + j.val, by omega⟩
      let x' : Fin m' → E := fun i => x ⟨r.val + i.val, by omega⟩
      apply hmin m' hm'_lt
      refine ⟨y', x', ⟨?_, ?_, ?_⟩, ?_⟩
      · have : y' 0 = y r := by apply congrArg y; apply Fin.ext; simp
        rw [this]; exact hX1
      · intro i
        have h1 := hVP.2.1 ⟨r.val + i.val, by omega⟩
        have hcast : (⟨r.val + i.val, by omega⟩ : Fin m).castSucc = ⟨r.val + i.castSucc.val, by omega⟩ :=
          Fin.ext rfl
        rw [hcast] at h1
        exact h1
      · intro i
        have h1 := hVP.2.2 ⟨r.val + i.val, by omega⟩
        have hsucc : (⟨r.val + i.val, by omega⟩ : Fin m).succ = ⟨r.val + i.succ.val, by omega⟩ :=
          Fin.ext (by dsimp; omega)
        rw [hsucc] at h1
        exact h1
      · have : y' (Fin.last m') = y (Fin.last m) := by
          dsimp [y']; congr 1; apply Fin.ext; dsimp [m']; omega
        rw [this]; exact hyend
    have hno_X2 : ∀ r : Fin (m + 1), r.val < m → y r ∉ X2 := by
      intro r hr hX2
      let m' := r.val
      let y' : Fin (m' + 1) → E := fun j => y ⟨j.val, by omega⟩
      let x' : Fin m' → E := fun i => x ⟨i.val, by omega⟩
      apply hmin m' hr
      refine ⟨y', x', ⟨?_, ?_, ?_⟩, ?_⟩
      · exact hVP.1
      · intro i; exact hVP.2.1 ⟨i.val, by omega⟩
      · intro i; exact hVP.2.2 ⟨i.val, by omega⟩
      · have : y' (Fin.last m') = y r := by apply congrArg y; apply Fin.ext; rfl
        rw [this]; exact hX2
    have hno_chord_f : ∀ (i : Fin m) (j : Fin (m + 1)), i.val + 1 < j.val →
        f (y j) ∈ Submodule.span F (f '' ((I.erase (x i) : Finset E) : Set E)) := by
      intro i j hij
      by_contra hnot
      let m' := i.val + 1 + (m - j.val)
      have hm'_lt : m' < m := by omega
      let y' : Fin (m' + 1) → E := fun r =>
        if hr : r.val ≤ i.val then y ⟨r.val, by omega⟩
        else y ⟨j.val + (r.val - (i.val + 1)), by omega⟩
      let x' : Fin m' → E := fun r =>
        if hr : r.val ≤ i.val then x ⟨r.val, by omega⟩
        else x ⟨j.val + (r.val - (i.val + 1)), by omega⟩
      apply hmin m' hm'_lt
      refine ⟨y', x', ⟨?_, ?_, ?_⟩, ?_⟩
      · change y 0 ∈ X1; exact hVP.1
      · intro r
        by_cases hr : r.val ≤ i.val
        · dsimp [x', y']; simp only [hr, ↓reduceDIte]
          exact hVP.2.1 ⟨r.val, by omega⟩
        · dsimp [x', y']; simp only [hr, ↓reduceDIte]
          have h1 := hVP.2.1 ⟨j.val + (r.val - (i.val + 1)), by omega⟩
          exact h1
      · intro r
        by_cases hr : r.val < i.val
        · have hr1 : r.val ≤ i.val := by omega
          have hr2 : r.val + 1 ≤ i.val := by omega
          dsimp [x', y']; simp only [hr1, hr2, Fin.val_succ, ↓reduceDIte]
          exact hVP.2.2 ⟨r.val, by omega⟩
        · by_cases hreq : r.val = i.val
          · have hr1 : r.val ≤ i.val := by omega
            have hr2 : ¬ (r.val + 1 ≤ i.val) := by omega
            dsimp [x', y']; simp only [hr1, hr2, Fin.val_succ, ↓reduceDIte]
            have hx_eq : (⟨r.val, by omega⟩ : Fin m) = i := Fin.ext hreq
            have hy_eq : (⟨j.val + (r.val + 1 - (i.val + 1)), by omega⟩ : Fin (m + 1)) = j :=
              Fin.ext (by dsimp; omega)
            rw [hx_eq, hy_eq]
            exact ⟨hy_notI j, hnot⟩
          · have hr1 : ¬ (r.val ≤ i.val) := by omega
            have hr2 : ¬ (r.val + 1 ≤ i.val) := by omega
            dsimp [x', y']; simp only [hr1, hr2, Fin.val_succ, ↓reduceDIte]
            have h1 := hVP.2.2 ⟨j.val + (r.val - (i.val + 1)), by omega⟩
            have hsucc : (⟨j.val + (r.val - (i.val + 1)), by omega⟩ : Fin m).succ =
                ⟨j.val + (r.val + 1 - (i.val + 1)), by omega⟩ := Fin.ext (by dsimp; omega)
            rw [hsucc] at h1
            exact h1
      · dsimp [y']
        have hnotle : ¬ (m' ≤ i.val) := by dsimp [m']; omega
        simp only [Fin.val_last, hnotle, ↓reduceDIte]
        have : (⟨j.val + (m' - (i.val + 1)), by omega⟩ : Fin (m + 1)) = Fin.last m :=
          Fin.ext (by dsimp [m']; omega)
        rw [this]; exact hyend
    have hno_chord_g : ∀ (j : Fin (m + 1)) (i : Fin m), j.val < i.val →
        g (y j) ∈ Submodule.span F (g '' ((I.erase (x i) : Finset E) : Set E)) := by
      intro j i hji
      by_contra hnot
      let m' := j.val + (m - i.val)
      have hm'_lt : m' < m := by omega
      let y' : Fin (m' + 1) → E := fun r =>
        if hr : r.val ≤ j.val then y ⟨r.val, by omega⟩
        else y ⟨i.val + (r.val - j.val), by omega⟩
      let x' : Fin m' → E := fun r =>
        if hr : r.val < j.val then x ⟨r.val, by omega⟩
        else x ⟨i.val + (r.val - j.val), by omega⟩
      apply hmin m' hm'_lt
      refine ⟨y', x', ⟨?_, ?_, ?_⟩, ?_⟩
      · change y 0 ∈ X1; exact hVP.1
      · intro r
        by_cases hr : r.val < j.val
        · have hr1 : r.val ≤ j.val := by omega
          dsimp [x', y']; simp only [hr, hr1, Fin.val_castSucc, ↓reduceDIte]
          exact hVP.2.1 ⟨r.val, by omega⟩
        · by_cases hreq : r.val = j.val
          · have hr1 : ¬ (r.val < j.val) := by omega
            have hr2 : r.val ≤ j.val := by omega
            dsimp [x', y']; simp only [hr1, hr2, Fin.val_castSucc, ↓reduceDIte]
            have hx_eq : (⟨i.val + (r.val - j.val), by omega⟩ : Fin m) = i :=
              Fin.ext (by dsimp; omega)
            have hy_eq : (⟨r.val, by omega⟩ : Fin (m + 1)) = j := Fin.ext hreq
            rw [hx_eq, hy_eq]
            exact ⟨hx_inI i, hnot⟩
          · have hr1 : ¬ (r.val < j.val) := by omega
            have hr2 : ¬ (r.val ≤ j.val) := by omega
            dsimp [x', y']; simp only [hr1, hr2, Fin.val_castSucc, ↓reduceDIte]
            exact hVP.2.1 ⟨i.val + (r.val - j.val), by omega⟩
      · intro r
        by_cases hr : r.val < j.val
        · have hr2 : r.val + 1 ≤ j.val := by omega
          dsimp [x', y']; simp only [hr, hr2, Fin.val_succ, ↓reduceDIte]
          exact hVP.2.2 ⟨r.val, by omega⟩
        · have hr2 : ¬ (r.val + 1 ≤ j.val) := by omega
          dsimp [x', y']; simp only [hr, hr2, Fin.val_succ, ↓reduceDIte]
          have h1 := hVP.2.2 ⟨i.val + (r.val - j.val), by omega⟩
          have hsucc : (⟨i.val + (r.val - j.val), by omega⟩ : Fin m).succ =
              ⟨i.val + (r.val + 1 - j.val), by omega⟩ := Fin.ext (by dsimp; omega)
          rw [hsucc] at h1
          exact h1
      · dsimp [y']
        have hnotle : ¬ (m' ≤ j.val) := by dsimp [m']; omega
        simp only [Fin.val_last, hnotle, ↓reduceDIte]
        have : (⟨i.val + (m' - j.val), by omega⟩ : Fin (m + 1)) = Fin.last m :=
          Fin.ext (by dsimp [m']; omega)
        rw [this]; exact hyend
    have hy_inj : Function.Injective y := by
      intro j1 j2 heq
      by_contra hne
      have hlt : j1.val < j2.val ∨ j2.val < j1.val := by
        rcases lt_trichotomy j1.val j2.val with h | h | h
        · exact Or.inl h
        · exact absurd (Fin.ext h) hne
        · exact Or.inr h
      wlog h12 : j1.val < j2.val generalizing j1 j2
      · exact this heq.symm (Ne.symm hne) (hlt.symm) (hlt.resolve_left h12)
      let m' := j1.val + (m - j2.val)
      have hm'_lt : m' < m := by omega
      let y' : Fin (m' + 1) → E := fun r =>
        if hr : r.val ≤ j1.val then y ⟨r.val, by omega⟩
        else y ⟨j2.val + (r.val - j1.val), by omega⟩
      let x' : Fin m' → E := fun r =>
        if hr : r.val < j1.val then x ⟨r.val, by omega⟩
        else x ⟨j2.val + (r.val - j1.val), by omega⟩
      apply hmin m' hm'_lt
      refine ⟨y', x', ⟨?_, ?_, ?_⟩, ?_⟩
      · change y 0 ∈ X1; exact hVP.1
      · intro r
        by_cases hr : r.val < j1.val
        · have hr1 : r.val ≤ j1.val := by omega
          dsimp [x', y']; simp only [hr, hr1, Fin.val_castSucc, ↓reduceDIte]
          exact hVP.2.1 ⟨r.val, by omega⟩
        · by_cases hreq : r.val = j1.val
          · have hr1 : ¬ (r.val < j1.val) := by omega
            have hr2 : r.val ≤ j1.val := by omega
            dsimp [x', y']; simp only [hr1, hr2, Fin.val_castSucc, ↓reduceDIte]
            have hx_eq : (⟨j2.val + (r.val - j1.val), by omega⟩ : Fin m) = ⟨j2.val, by omega⟩ :=
              Fin.ext (by dsimp; omega)
            have hy_eq : (⟨r.val, by omega⟩ : Fin (m + 1)) = j1 := Fin.ext hreq
            rw [hx_eq, hy_eq, heq]
            exact hVP.2.1 ⟨j2.val, by omega⟩
          · have hr1 : ¬ (r.val < j1.val) := by omega
            have hr2 : ¬ (r.val ≤ j1.val) := by omega
            dsimp [x', y']; simp only [hr1, hr2, Fin.val_castSucc, ↓reduceDIte]
            exact hVP.2.1 ⟨j2.val + (r.val - j1.val), by omega⟩
      · intro r
        by_cases hr : r.val < j1.val
        · have hr2 : r.val + 1 ≤ j1.val := by omega
          dsimp [x', y']; simp only [hr, hr2, Fin.val_succ, ↓reduceDIte]
          exact hVP.2.2 ⟨r.val, by omega⟩
        · have hr2 : ¬ (r.val + 1 ≤ j1.val) := by omega
          dsimp [x', y']; simp only [hr, hr2, Fin.val_succ, ↓reduceDIte]
          have h1 := hVP.2.2 ⟨j2.val + (r.val - j1.val), by omega⟩
          have hsucc : (⟨j2.val + (r.val - j1.val), by omega⟩ : Fin m).succ =
              ⟨j2.val + (r.val + 1 - j1.val), by omega⟩ := Fin.ext (by dsimp; omega)
          rw [hsucc] at h1
          exact h1
      · dsimp [y']
        by_cases hle : m' ≤ j1.val
        · have hjm : j2.val = m := by dsimp [m'] at hle; omega
          have hj2_last : j2 = Fin.last m := Fin.ext hjm
          simp only [Fin.val_last, hle, ↓reduceDIte]
          have : (⟨m', by omega⟩ : Fin (m + 1)) = j1 := Fin.ext (by dsimp [m']; omega)
          rw [this, heq, hj2_last]; exact hyend
        · simp only [Fin.val_last, hle, ↓reduceDIte]
          have : (⟨j2.val + (m' - j1.val), by omega⟩ : Fin (m + 1)) = Fin.last m :=
            Fin.ext (by dsimp [m']; omega)
          rw [this]; exact hyend
    have hx_inj : Function.Injective x := by
      intro i1 i2 heq
      by_contra hne
      have hlt : i1.val < i2.val ∨ i2.val < i1.val := by
        rcases lt_trichotomy i1.val i2.val with h | h | h
        · exact Or.inl h
        · exact absurd (Fin.ext h) hne
        · exact Or.inr h
      wlog h12 : i1.val < i2.val generalizing i1 i2
      · exact this heq.symm (Ne.symm hne) (hlt.symm) (hlt.resolve_left h12)
      have hch := hno_chord_f i1 i2.succ (by dsimp; omega)
      rw [heq] at hch
      exact (hVP.2.2 i2).2 hch
    let Xset : Finset E := Finset.univ.image x
    let Yset : Finset E := Finset.univ.image y
    let I' : Finset E := (I \ Xset) ∪ Yset
    have hX_sub : Xset ⊆ I := by
      intro e he; rcases Finset.mem_image.mp he with ⟨i, _, rfl⟩; exact hx_inI i
    have hY_disj : Disjoint I Yset := by
      rw [Finset.disjoint_right]
      intro e he; rcases Finset.mem_image.mp he with ⟨r, _, rfl⟩; exact hy_notI r
    have hI'_card : I'.card = I.card + 1 := by
      have hd : Disjoint (I \ Xset) Yset := Disjoint.mono_left Finset.sdiff_subset hY_disj
      rw [Finset.card_union_of_disjoint hd, Finset.card_sdiff, Finset.inter_eq_left.mpr hX_sub,
        Finset.card_image_of_injective _ hx_inj, Finset.card_image_of_injective _ hy_inj,
        Finset.card_univ, Finset.card_univ, Fintype.card_fin, Fintype.card_fin]
      have hm_le : m ≤ I.card := by
        have := Finset.card_le_card hX_sub
        rwa [Finset.card_image_of_injective _ hx_inj, Finset.card_univ, Fintype.card_fin] at this
      omega
    have hI'_f : LinearIndependent F (fun e : I' => f e.1) := by
      rw [Fintype.linearIndependent_iff]
      intro c hsum
      have hsplit_sum : (∑ e : I', c e • f e.1) =
          (∑ e ∈ (I \ Xset).attach, c ⟨e.1, Finset.mem_union_left _ e.2⟩ • f e.1) +
          (∑ r : Fin (m + 1), c ⟨y r, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩)⟩ • f (y r)) := by
        have hd : Disjoint (I \ Xset) Yset := Disjoint.mono_left Finset.sdiff_subset hY_disj
        have h1 : ∑ e : I', c e • f e.1 = ∑ e ∈ I', if h : e ∈ I' then c ⟨e, h⟩ • f e else 0 := by
          rw [← Finset.sum_coe_sort I' (fun e => if h : e ∈ I' then c ⟨e, h⟩ • f e else 0)]
          refine Finset.sum_congr rfl fun e _ => by simp [e.2]
        rw [h1]
        dsimp only [I']
        rw [Finset.sum_union hd]
        congr 1
        · rw [← Finset.sum_coe_sort (I \ Xset) (fun e => if h : e ∈ (I \ Xset) ∪ Yset then c ⟨e, h⟩ • f e else 0)]
          refine Finset.sum_congr rfl fun e _ => ?_
          simp [Finset.mem_union_left _ e.2]
        · dsimp only [Yset]
          rw [Finset.sum_image (fun a _ b _ h => hy_inj h)]
          refine Finset.sum_congr rfl fun r _ => ?_
          have hmem : y r ∈ (I \ Xset) ∪ Finset.univ.image y :=
            Finset.mem_union_right _ (Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩)
          simp [hmem]
      rw [hsplit_sum] at hsum
      let cy : Fin (m + 1) → F := fun r =>
        c ⟨y r, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩)⟩
      have hcy0 : ∀ k : ℕ, ∀ r : Fin (m + 1), r.val = k → cy r = 0 := by
        intro k
        induction k using Nat.strong_induction_on with
        | _ k ih =>
          intro r hrk
          by_cases hk0 : k = 0
          · have hr0 : r = 0 := Fin.ext (hrk.trans hk0)
            subst hr0
            by_contra hne0
            have hmemI : f (y 0) ∈ Submodule.span F (f '' (I : Set E)) := by
              have hrem : cy 0 • f (y 0) =
                  -(∑ e ∈ (I \ Xset).attach, c ⟨e.1, Finset.mem_union_left _ e.2⟩ • f e.1) -
                  ∑ j ∈ Finset.univ.erase (0 : Fin (m + 1)), cy j • f (y j) := by
                have hsplit0 := Finset.add_sum_erase Finset.univ (fun j : Fin (m + 1) => cy j • f (y j)) (Finset.mem_univ (0 : Fin (m + 1)))
                change (∑ e ∈ (I \ Xset).attach, c ⟨e.1, Finset.mem_union_left _ e.2⟩ • f e.1) +
                    (∑ j : Fin (m + 1), cy j • f (y j)) = 0 at hsum
                rw [← hsplit0] at hsum
                calc cy 0 • f (y 0) =
                      ((∑ e ∈ (I \ Xset).attach, c ⟨e.1, Finset.mem_union_left _ e.2⟩ • f e.1) +
                        (cy 0 • f (y 0) + ∑ j ∈ Finset.univ.erase (0 : Fin (m + 1)), cy j • f (y j))) -
                      (∑ e ∈ (I \ Xset).attach, c ⟨e.1, Finset.mem_union_left _ e.2⟩ • f e.1) -
                      ∑ j ∈ Finset.univ.erase (0 : Fin (m + 1)), cy j • f (y j) := by abel
                  _ = _ := by rw [hsum, zero_sub]
              have h1 : cy 0 • f (y 0) ∈ Submodule.span F (f '' (I : Set E)) := by
                rw [hrem]
                apply Submodule.sub_mem
                · apply Submodule.neg_mem
                  apply Submodule.sum_mem
                  intro e _
                  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e.1, (Finset.mem_sdiff.mp e.2).1, rfl⟩)
                · apply Submodule.sum_mem
                  intro j hj
                  have hjpos : 0 < j.val := by
                    have hne : j ≠ 0 := Finset.ne_of_mem_erase hj
                    exact Nat.pos_of_ne_zero (fun h => hne (Fin.ext h))
                  have hnotX1 := hno_X1 j hjpos
                  have hfmem : f (y j) ∈ Submodule.span F (f '' (I : Set E)) := by
                    by_contra hnf
                    exact hnotX1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy_notI j, hnf⟩)
                  exact Submodule.smul_mem _ _ hfmem
              have hcy1 : cy 0 = 1 := by
                have hz : ∀ z : F, z = 0 ∨ z = 1 := by decide
                exact (hz (cy 0)).resolve_left hne0
              simpa [hcy1] using h1
            exact (Finset.mem_filter.mp hVP.1).2.2 hmemI
          · let i0 : Fin m := ⟨k - 1, by omega⟩
            have hi0_succ : i0.succ = r := Fin.ext (by dsimp [i0]; omega)
            by_contra hne0
            have hmemE : f (y r) ∈ Submodule.span F (f '' ((I.erase (x i0) : Finset E) : Set E)) := by
              have hrem : cy r • f (y r) =
                  -(∑ e ∈ (I \ Xset).attach, c ⟨e.1, Finset.mem_union_left _ e.2⟩ • f e.1) -
                  ∑ j ∈ Finset.univ.erase r, cy j • f (y j) := by
                have hsplitr := Finset.add_sum_erase Finset.univ (fun j : Fin (m + 1) => cy j • f (y j)) (Finset.mem_univ r)
                change (∑ e ∈ (I \ Xset).attach, c ⟨e.1, Finset.mem_union_left _ e.2⟩ • f e.1) +
                    (∑ j : Fin (m + 1), cy j • f (y j)) = 0 at hsum
                rw [← hsplitr] at hsum
                calc cy r • f (y r) =
                      ((∑ e ∈ (I \ Xset).attach, c ⟨e.1, Finset.mem_union_left _ e.2⟩ • f e.1) +
                        (cy r • f (y r) + ∑ j ∈ Finset.univ.erase r, cy j • f (y j))) -
                      (∑ e ∈ (I \ Xset).attach, c ⟨e.1, Finset.mem_union_left _ e.2⟩ • f e.1) -
                      ∑ j ∈ Finset.univ.erase r, cy j • f (y j) := by abel
                  _ = _ := by rw [hsum, zero_sub]
              have h1 : cy r • f (y r) ∈ Submodule.span F (f '' ((I.erase (x i0) : Finset E) : Set E)) := by
                rw [hrem]
                apply Submodule.sub_mem
                · apply Submodule.neg_mem
                  apply Submodule.sum_mem
                  intro e _
                  have heI : e.1 ∈ I := (Finset.mem_sdiff.mp e.2).1
                  have hene : e.1 ≠ x i0 := fun heq =>
                    (Finset.mem_sdiff.mp e.2).2 (heq ▸ Finset.mem_image.mpr ⟨i0, Finset.mem_univ _, rfl⟩)
                  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e.1, Finset.mem_erase.mpr ⟨hene, heI⟩, rfl⟩)
                · apply Submodule.sum_mem
                  intro j hj
                  have hjne : j ≠ r := Finset.ne_of_mem_erase hj
                  by_cases hjlt : j.val < k
                  · rw [ih j.val hjlt j rfl, zero_smul]; exact Submodule.zero_mem _
                  · have hjgt : i0.val + 1 < j.val := by
                      have : j.val ≠ r.val := fun h => hjne (Fin.ext h)
                      dsimp [i0]; omega
                    exact Submodule.smul_mem _ _ (hno_chord_f i0 j hjgt)
              have hcy1 : cy r = 1 := by
                have hz : ∀ z : F, z = 0 ∨ z = 1 := by decide
                exact (hz (cy r)).resolve_left hne0
              simpa [hcy1] using h1
            have hnotE := (hVP.2.2 i0).2
            rw [hi0_succ] at hnotE
            exact hnotE hmemE
      have hcy_all : ∀ r : Fin (m + 1), cy r = 0 := fun r => hcy0 r.val r rfl
      have hsum_left : ∑ e ∈ (I \ Xset).attach, c ⟨e.1, Finset.mem_union_left _ e.2⟩ • f e.1 = 0 := by
        have hzeroR : ∑ r : Fin (m + 1), cy r • f (y r) = 0 := by
          apply Finset.sum_eq_zero; intro r _; simp [hcy_all r]
        change (∑ e ∈ (I \ Xset).attach, c ⟨e.1, Finset.mem_union_left _ e.2⟩ • f e.1) +
            (∑ r : Fin (m + 1), cy r • f (y r)) = 0 at hsum
        rw [hzeroR, add_zero] at hsum
        exact hsum
      let cI : I → F := fun e =>
        if h : e.1 ∈ I \ Xset then c ⟨e.1, Finset.mem_union_left _ h⟩ else 0
      have hcI_sum : ∑ e : I, cI e • f e.1 = 0 := by
        have h1 : ∑ e : I, cI e • f e.1 =
            ∑ e ∈ I, if h : e ∈ I \ Xset then c ⟨e, Finset.mem_union_left _ h⟩ • f e else 0 := by
          rw [← Finset.sum_coe_sort I (fun e => if h : e ∈ I \ Xset then c ⟨e, Finset.mem_union_left _ h⟩ • f e else 0)]
          refine Finset.sum_congr rfl fun e _ => ?_
          dsimp [cI]; split_ifs <;> simp
        rw [h1, ← Finset.sum_subset Finset.sdiff_subset]
        · rw [← Finset.sum_coe_sort (I \ Xset) (fun e => if h : e ∈ I \ Xset then c ⟨e, Finset.mem_union_left _ h⟩ • f e else 0)]
          rw [← hsum_left]
          refine Finset.sum_congr rfl fun e _ => by simp [e.2]
        · intro e _ he; simp [he]
      have hcI0 := Fintype.linearIndependent_iff.mp hIf cI hcI_sum
      intro e
      rcases Finset.mem_union.mp e.2 with hL | hR
      · have h0 := hcI0 ⟨e.1, (Finset.mem_sdiff.mp hL).1⟩
        dsimp only [cI] at h0
        rw [dif_pos hL] at h0
        exact h0
      · rcases Finset.mem_image.mp hR with ⟨r, _, hr⟩
        have heq : e = ⟨y r, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩)⟩ :=
          Subtype.ext hr.symm
        rw [heq]; exact hcy_all r
    have hI'_g : LinearIndependent F (fun e : I' => g e.1) := by
      rw [Fintype.linearIndependent_iff]
      intro c hsum
      have hsplit_sum : (∑ e : I', c e • g e.1) =
          (∑ e ∈ (I \ Xset).attach, c ⟨e.1, Finset.mem_union_left _ e.2⟩ • g e.1) +
          (∑ r : Fin (m + 1), c ⟨y r, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩)⟩ • g (y r)) := by
        have hd : Disjoint (I \ Xset) Yset := Disjoint.mono_left Finset.sdiff_subset hY_disj
        have h1 : ∑ e : I', c e • g e.1 = ∑ e ∈ I', if h : e ∈ I' then c ⟨e, h⟩ • g e else 0 := by
          rw [← Finset.sum_coe_sort I' (fun e => if h : e ∈ I' then c ⟨e, h⟩ • g e else 0)]
          refine Finset.sum_congr rfl fun e _ => by simp [e.2]
        rw [h1]
        dsimp only [I']
        rw [Finset.sum_union hd]
        congr 1
        · rw [← Finset.sum_coe_sort (I \ Xset) (fun e => if h : e ∈ (I \ Xset) ∪ Yset then c ⟨e, h⟩ • g e else 0)]
          refine Finset.sum_congr rfl fun e _ => ?_
          simp [Finset.mem_union_left _ e.2]
        · dsimp only [Yset]
          rw [Finset.sum_image (fun a _ b _ h => hy_inj h)]
          refine Finset.sum_congr rfl fun r _ => ?_
          have hmem : y r ∈ (I \ Xset) ∪ Finset.univ.image y :=
            Finset.mem_union_right _ (Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩)
          simp [hmem]
      rw [hsplit_sum] at hsum
      let cy : Fin (m + 1) → F := fun r =>
        c ⟨y r, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩)⟩
      have hcy0 : ∀ d : ℕ, ∀ r : Fin (m + 1), m - r.val = d → cy r = 0 := by
        intro d
        induction d using Nat.strong_induction_on with
        | _ d ih =>
          intro r hrd
          by_cases hd0 : d = 0
          · have hrm : r = Fin.last m := Fin.ext (by dsimp; omega)
            subst hrm
            by_contra hne0
            have hmemI : g (y (Fin.last m)) ∈ Submodule.span F (g '' (I : Set E)) := by
              have hrem : cy (Fin.last m) • g (y (Fin.last m)) =
                  -(∑ e ∈ (I \ Xset).attach, c ⟨e.1, Finset.mem_union_left _ e.2⟩ • g e.1) -
                  ∑ j ∈ Finset.univ.erase (Fin.last m), cy j • g (y j) := by
                have hsplitm := Finset.add_sum_erase Finset.univ (fun j : Fin (m + 1) => cy j • g (y j)) (Finset.mem_univ (Fin.last m))
                change (∑ e ∈ (I \ Xset).attach, c ⟨e.1, Finset.mem_union_left _ e.2⟩ • g e.1) +
                    (∑ j : Fin (m + 1), cy j • g (y j)) = 0 at hsum
                rw [← hsplitm] at hsum
                calc cy (Fin.last m) • g (y (Fin.last m)) =
                      ((∑ e ∈ (I \ Xset).attach, c ⟨e.1, Finset.mem_union_left _ e.2⟩ • g e.1) +
                        (cy (Fin.last m) • g (y (Fin.last m)) + ∑ j ∈ Finset.univ.erase (Fin.last m), cy j • g (y j))) -
                      (∑ e ∈ (I \ Xset).attach, c ⟨e.1, Finset.mem_union_left _ e.2⟩ • g e.1) -
                      ∑ j ∈ Finset.univ.erase (Fin.last m), cy j • g (y j) := by abel
                  _ = _ := by rw [hsum, zero_sub]
              have h1 : cy (Fin.last m) • g (y (Fin.last m)) ∈ Submodule.span F (g '' (I : Set E)) := by
                rw [hrem]
                apply Submodule.sub_mem
                · apply Submodule.neg_mem
                  apply Submodule.sum_mem
                  intro e _
                  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e.1, (Finset.mem_sdiff.mp e.2).1, rfl⟩)
                · apply Submodule.sum_mem
                  intro j hj
                  have hjlt : j.val < m := by
                    have hne : j ≠ Fin.last m := Finset.ne_of_mem_erase hj
                    have : j.val ≠ m := fun h => hne (Fin.ext h)
                    omega
                  have hnotX2 := hno_X2 j hjlt
                  have hgmem : g (y j) ∈ Submodule.span F (g '' (I : Set E)) := by
                    by_contra hng
                    exact hnotX2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy_notI j, hng⟩)
                  exact Submodule.smul_mem _ _ hgmem
              have hcy1 : cy (Fin.last m) = 1 := by
                have hz : ∀ z : F, z = 0 ∨ z = 1 := by decide
                exact (hz (cy (Fin.last m))).resolve_left hne0
              simpa [hcy1] using h1
            exact (Finset.mem_filter.mp hyend).2.2 hmemI
          · let i0 : Fin m := ⟨r.val, by omega⟩
            have hi0_cast : i0.castSucc = r := Fin.ext rfl
            by_contra hne0
            have hmemE : g (y r) ∈ Submodule.span F (g '' ((I.erase (x i0) : Finset E) : Set E)) := by
              have hrem : cy r • g (y r) =
                  -(∑ e ∈ (I \ Xset).attach, c ⟨e.1, Finset.mem_union_left _ e.2⟩ • g e.1) -
                  ∑ j ∈ Finset.univ.erase r, cy j • g (y j) := by
                have hsplitr := Finset.add_sum_erase Finset.univ (fun j : Fin (m + 1) => cy j • g (y j)) (Finset.mem_univ r)
                change (∑ e ∈ (I \ Xset).attach, c ⟨e.1, Finset.mem_union_left _ e.2⟩ • g e.1) +
                    (∑ j : Fin (m + 1), cy j • g (y j)) = 0 at hsum
                rw [← hsplitr] at hsum
                calc cy r • g (y r) =
                      ((∑ e ∈ (I \ Xset).attach, c ⟨e.1, Finset.mem_union_left _ e.2⟩ • g e.1) +
                        (cy r • g (y r) + ∑ j ∈ Finset.univ.erase r, cy j • g (y j))) -
                      (∑ e ∈ (I \ Xset).attach, c ⟨e.1, Finset.mem_union_left _ e.2⟩ • g e.1) -
                      ∑ j ∈ Finset.univ.erase r, cy j • g (y j) := by abel
                  _ = _ := by rw [hsum, zero_sub]
              have h1 : cy r • g (y r) ∈ Submodule.span F (g '' ((I.erase (x i0) : Finset E) : Set E)) := by
                rw [hrem]
                apply Submodule.sub_mem
                · apply Submodule.neg_mem
                  apply Submodule.sum_mem
                  intro e _
                  have heI : e.1 ∈ I := (Finset.mem_sdiff.mp e.2).1
                  have hene : e.1 ≠ x i0 := fun heq =>
                    (Finset.mem_sdiff.mp e.2).2 (heq ▸ Finset.mem_image.mpr ⟨i0, Finset.mem_univ _, rfl⟩)
                  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e.1, Finset.mem_erase.mpr ⟨hene, heI⟩, rfl⟩)
                · apply Submodule.sum_mem
                  intro j hj
                  have hjne : j ≠ r := Finset.ne_of_mem_erase hj
                  by_cases hjgt : r.val < j.val
                  · rw [ih (m - j.val) (by omega) j rfl, zero_smul]; exact Submodule.zero_mem _
                  · have hjlt : j.val < i0.val := by
                      have : j.val ≠ r.val := fun h => hjne (Fin.ext h)
                      dsimp [i0]; omega
                    exact Submodule.smul_mem _ _ (hno_chord_g j i0 hjlt)
              have hcy1 : cy r = 1 := by
                have hz : ∀ z : F, z = 0 ∨ z = 1 := by decide
                exact (hz (cy r)).resolve_left hne0
              simpa [hcy1] using h1
            have hnotE := (hVP.2.1 i0).2
            rw [hi0_cast] at hnotE
            exact hnotE hmemE
      have hcy_all : ∀ r : Fin (m + 1), cy r = 0 := fun r => hcy0 (m - r.val) r rfl
      have hsum_left : ∑ e ∈ (I \ Xset).attach, c ⟨e.1, Finset.mem_union_left _ e.2⟩ • g e.1 = 0 := by
        have hzeroR : ∑ r : Fin (m + 1), cy r • g (y r) = 0 := by
          apply Finset.sum_eq_zero; intro r _; simp [hcy_all r]
        change (∑ e ∈ (I \ Xset).attach, c ⟨e.1, Finset.mem_union_left _ e.2⟩ • g e.1) +
            (∑ r : Fin (m + 1), cy r • g (y r)) = 0 at hsum
        rw [hzeroR, add_zero] at hsum
        exact hsum
      let cI : I → F := fun e =>
        if h : e.1 ∈ I \ Xset then c ⟨e.1, Finset.mem_union_left _ h⟩ else 0
      have hcI_sum : ∑ e : I, cI e • g e.1 = 0 := by
        have h1 : ∑ e : I, cI e • g e.1 =
            ∑ e ∈ I, if h : e ∈ I \ Xset then c ⟨e, Finset.mem_union_left _ h⟩ • g e else 0 := by
          rw [← Finset.sum_coe_sort I (fun e => if h : e ∈ I \ Xset then c ⟨e, Finset.mem_union_left _ h⟩ • g e else 0)]
          refine Finset.sum_congr rfl fun e _ => ?_
          dsimp [cI]; split_ifs <;> simp
        rw [h1, ← Finset.sum_subset Finset.sdiff_subset]
        · rw [← Finset.sum_coe_sort (I \ Xset) (fun e => if h : e ∈ I \ Xset then c ⟨e, Finset.mem_union_left _ h⟩ • g e else 0)]
          rw [← hsum_left]
          refine Finset.sum_congr rfl fun e _ => by simp [e.2]
        · intro e _ he; simp [he]
      have hcI0 := Fintype.linearIndependent_iff.mp hIg cI hcI_sum
      intro e
      rcases Finset.mem_union.mp e.2 with hL | hR
      · have h0 := hcI0 ⟨e.1, (Finset.mem_sdiff.mp hL).1⟩
        dsimp only [cI] at h0
        rw [dif_pos hL] at h0
        exact h0
      · rcases Finset.mem_image.mp hR with ⟨r, _, hr⟩
        have heq : e = ⟨y r, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩)⟩ :=
          Subtype.ext hr.symm
        rw [heq]; exact hcy_all r
    have hI'_in : I' ∈ Common := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI'_f, hI'_g⟩
    have hle := hImax I' hI'_in
    omega
  · let RY : Finset E := Finset.univ.filter (fun v =>
      v ∉ I ∧ ∃ m : ℕ, ∃ (y : Fin (m + 1) → E) (x : Fin m → E), ValidPath m y x ∧ y (Fin.last m) = v)
    let RX : Finset E := Finset.univ.filter (fun u =>
      u ∈ I ∧ ∃ v ∈ RY, g v ∉ Submodule.span F (g '' ((I.erase u : Finset E) : Set E)))
    let R : Finset E := RY ∪ RX
    let A : Finset E := Finset.univ \ R
    have hR_eq : Finset.univ \ A = R := by
      ext e; simp [A]
    have hspan_A : Submodule.span F (f '' (A : Set E)) = Submodule.span F (f '' ((I ∩ A : Finset E) : Set E)) := by
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro _ ⟨v, hvA, rfl⟩
        have hvA' : v ∈ A := hvA
        by_cases hvI : v ∈ I
        · exact Submodule.subset_span ⟨v, Finset.mem_inter.mpr ⟨hvI, hvA'⟩, rfl⟩
        · have hvnotR : v ∉ R := (Finset.mem_sdiff.mp hvA').2
          have hvnotRY : v ∉ RY := fun h => hvnotR (Finset.mem_union_left _ h)
          have hmemI : f v ∈ Submodule.span F (f '' (I : Set E)) := by
            by_contra hnf
            have hvX1 : v ∈ X1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvI, hnf⟩
            apply hvnotRY
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvI, 0, fun _ => v, fun i => i.elim0, ?_, rfl⟩
            exact ⟨hvX1, fun i => i.elim0, fun i => i.elim0⟩
          refine mem_span_inter_of_forall_erase f I A hIf (f v) hmemI ?_
          intro u huI huA
          have huR : u ∈ R := by
            by_contra hnotR
            exact huA (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnotR⟩)
          have huRX : u ∈ RX := by
            rcases Finset.mem_union.mp huR with hRY | hRX
            · exact absurd huI (Finset.mem_filter.mp hRY).2.1
            · exact hRX
          rcases (Finset.mem_filter.mp huRX).2.2 with ⟨w, hwRY, hgw⟩
          rcases (Finset.mem_filter.mp hwRY).2.2 with ⟨m, y, x, hVP, hyw⟩
          by_contra hnf
          apply hvnotRY
          let y' : Fin (m + 2) → E := Fin.snoc (α := fun _ => E) y v
          let x' : Fin (m + 1) → E := Fin.snoc (α := fun _ => E) x u
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvI, m + 1, y', x', ⟨?_, ?_, ?_⟩, ?_⟩
          · change Fin.snoc (α := fun _ => E) y v 0 ∈ X1
            have h0 : (0 : Fin (m + 2)) = (0 : Fin (m + 1)).castSucc := rfl
            rw [h0, Fin.snoc_castSucc]; exact hVP.1
          · intro i
            refine Fin.lastCases (motive := fun i =>
                x' i ∈ I ∧ g (y' i.castSucc) ∉
                  Submodule.span F (g '' ((I.erase (x' i) : Finset E) : Set E))) ?_ ?_ i
            · simp only [x', y', Fin.snoc_last, Fin.snoc_castSucc, hyw]
              exact ⟨huI, hgw⟩
            · intro j
              simp only [x', y', Fin.snoc_castSucc]
              exact hVP.2.1 j
          · intro i
            refine Fin.lastCases (motive := fun i =>
                y' i.succ ∉ I ∧ f (y' i.succ) ∉
                  Submodule.span F (f '' ((I.erase (x' i) : Finset E) : Set E))) ?_ ?_ i
            · simp only [x', y', Fin.snoc_last, Fin.succ_last]
              exact ⟨hvI, hnf⟩
            · intro j
              have h1 : j.castSucc.succ = j.succ.castSucc := rfl
              simp only [x', y', h1, Fin.snoc_castSucc]
              exact hVP.2.2 j
          · simp [y']
      · apply Submodule.span_mono
        exact Set.image_mono (Finset.coe_subset.mpr Finset.inter_subset_right)
    have hspan_R : Submodule.span F (g '' (R : Set E)) = Submodule.span F (g '' ((I ∩ R : Finset E) : Set E)) := by
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro _ ⟨v, hvR, rfl⟩
        have hvR' : v ∈ R := hvR
        by_cases hvI : v ∈ I
        · exact Submodule.subset_span ⟨v, Finset.mem_inter.mpr ⟨hvI, hvR'⟩, rfl⟩
        · have hvRY : v ∈ RY := by
            rcases Finset.mem_union.mp hvR' with hRY | hRX
            · exact hRY
            · exact absurd (Finset.mem_filter.mp hRX).2.1 hvI
          have hmemI : g v ∈ Submodule.span F (g '' (I : Set E)) := by
            by_contra hng
            have hvX2 : v ∈ X2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvI, hng⟩
            rcases (Finset.mem_filter.mp hvRY).2.2 with ⟨m, y, x, hVP, hyv⟩
            exact hpath ⟨m, y, x, hVP, hyv.symm ▸ hvX2⟩
          refine mem_span_inter_of_forall_erase g I R hIg (g v) hmemI ?_
          intro u huI huR
          by_contra hng
          exact huR (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, huI, v, hvRY, hng⟩))
      · apply Submodule.span_mono
        exact Set.image_mono (Finset.coe_subset.mpr Finset.inter_subset_right)
    have hIfA : LinearIndependent F (fun e : (I ∩ A : Finset E) => f e.1) :=
      hIf.comp (fun e : (I ∩ A : Finset E) => (⟨e.1, (Finset.mem_inter.mp e.2).1⟩ : I))
        (fun a b h => Subtype.ext (congrArg (fun z : I => z.1) h))
    have hIgR : LinearIndependent F (fun e : (I ∩ R : Finset E) => g e.1) :=
      hIg.comp (fun e : (I ∩ R : Finset E) => (⟨e.1, (Finset.mem_inter.mp e.2).1⟩ : I))
        (fun a b h => Subtype.ext (congrArg (fun z : I => z.1) h))
    have hfrA : Module.finrank F (Submodule.span F (f '' ((I ∩ A : Finset E) : Set E))) = (I ∩ A).card := by
      have h1 : f '' ((I ∩ A : Finset E) : Set E) = Set.range (fun e : (I ∩ A : Finset E) => f e.1) := by ext v; simp
      rw [h1, finrank_span_eq_card hIfA, Fintype.card_coe]
    have hfrR : Module.finrank F (Submodule.span F (g '' ((I ∩ R : Finset E) : Set E))) = (I ∩ R).card := by
      have h1 : g '' ((I ∩ R : Finset E) : Set E) = Set.range (fun e : (I ∩ R : Finset E) => g e.1) := by ext v; simp
      rw [h1, finrank_span_eq_card hIgR, Fintype.card_coe]
    refine ⟨I, A, hIf, hIg, ?_⟩
    rw [hR_eq, hspan_A, hspan_R, hfrA, hfrR]
    have hd : Disjoint (I ∩ A) (I ∩ R) := by
      rw [Finset.disjoint_left]; intro e h1 h2
      exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp h1).2).2 (Finset.mem_inter.mp h2).2
    have hun : (I ∩ A) ∪ (I ∩ R) = I := by
      ext e; simp only [Finset.mem_union, Finset.mem_inter, A, Finset.mem_sdiff, Finset.mem_univ, true_and]
      tauto
    rw [← Finset.card_union_of_disjoint hd, hun]

lemma card_good_pairs_indep (k : ℕ) :
    (Finset.univ.filter (fun uv : (Fin k → F) × (Fin k → F) =>
      ∀ c : Fin k, uv.1 c * uv.2 c = 0)).card = 3 ^ k := by
  classical
  let eEquiv : ((Fin k → F) × (Fin k → F)) ≃ (Fin k → F × F) :=
    { toFun := fun uv c => (uv.1 c, uv.2 c)
      invFun := fun f => (fun c => (f c).1, fun c => (f c).2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hbij : (Finset.univ.filter (fun uv : (Fin k → F) × (Fin k → F) =>
        ∀ c : Fin k, uv.1 c * uv.2 c = 0)).card =
      (Finset.univ.filter (fun f : Fin k → F × F => ∀ c : Fin k, (f c).1 * (f c).2 = 0)).card := by
    refine Finset.card_bij (fun uv _ => eEquiv uv) ?_ ?_ ?_
    · intro uv huv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at huv ⊢
      exact huv
    · intro u _ v _ h; exact eEquiv.injective h
    · intro f hf
      refine ⟨eEquiv.symm f, ?_, eEquiv.apply_symm_apply f⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
      exact hf
  rw [hbij]
  let S0 : Finset (F × F) := Finset.univ.filter (fun p : F × F => p.1 * p.2 = 0)
  have hS0 : S0.card = 3 := by decide
  have hpi : Finset.univ.filter (fun f : Fin k → F × F => ∀ c : Fin k, (f c).1 * (f c).2 = 0) =
      Fintype.piFinset (fun _ : Fin k => S0) := by
    ext f; simp [S0, Fintype.mem_piFinset]
  rw [hpi, Fintype.card_piFinset, Finset.prod_const, hS0, Finset.card_univ, Fintype.card_fin]

lemma card_linear_map_domain {U V : Type*} [AddCommGroup U] [Module F U] [Fintype U]
    [AddCommGroup V] [Module F V] [Fintype V]
    (φ : U →ₗ[F] V) (hsurj : Function.Surjective φ) :
    Fintype.card U = Fintype.card V * Nat.card (LinearMap.ker φ) := by
  classical
  rw [Nat.card_eq_fintype_card]
  have hfiber : ∀ v : V, (Finset.univ.filter (fun u : U => φ u = v)).card =
      Fintype.card (LinearMap.ker φ) := by
    intro v
    obtain ⟨u0, hu0⟩ := hsurj v
    refine Finset.card_bij (fun u hu => (⟨u - u0, by
        rw [LinearMap.mem_ker, map_sub, (Finset.mem_filter.mp hu).2, hu0]
        exact sub_self v⟩ : LinearMap.ker φ)) ?_ ?_ ?_
    · intro u _; exact Finset.mem_univ _
    · intro u1 _ u2 _ h
      have : u1 - u0 = u2 - u0 := congrArg Subtype.val h
      exact sub_left_inj.mp this
    · intro w _
      refine ⟨w.1 + u0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Subtype.ext (by abel)⟩
      rw [map_add, LinearMap.mem_ker.mp w.2, zero_add, hu0]
  have hpart : Fintype.card U = ∑ v : V, (Finset.univ.filter (fun u : U => φ u = v)).card := by
    rw [← Finset.card_univ, ← Finset.card_biUnion]
    · congr 1; ext u; simp
    · intro v1 _ v2 _ hne; change Disjoint _ _; rw [Finset.disjoint_left]
      intro u h1 h2; exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
  rw [hpart]
  simp_rw [hfiber]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

lemma card_hits_le_of_good {P Q : Type*} [AddCommGroup P] [Module F P] [Fintype P]
    [AddCommGroup Q] [Module F Q] [Fintype Q]
    {V1 V2 : Type*} [AddCommGroup V1] [Module F V1] [Fintype V1]
    [AddCommGroup V2] [Module F V2] [Fintype V2]
    (φ : P →ₗ[F] V1) (ψ : Q →ₗ[F] V2)
    (hφ : Function.Surjective φ) (hψ : Function.Surjective ψ)
    (pred : P × Q → Prop) (G : Finset (V1 × V2))
    (himp : ∀ w : P × Q, pred w → (φ w.1, ψ w.2) ∈ G) :
    Fintype.card V1 * Fintype.card V2 * Nat.card {w : P × Q // pred w} ≤
      G.card * Nat.card P * Nat.card Q := by
  classical
  have hP := card_linear_map_domain φ hφ
  have hQ := card_linear_map_domain ψ hψ
  rw [Nat.card_eq_fintype_card] at hP hQ
  let Φ : P × Q →ₗ[F] V1 × V2 := LinearMap.prodMap φ ψ
  have hΦ : Function.Surjective Φ := fun ⟨v1, v2⟩ => by
    obtain ⟨x, hx⟩ := hφ v1; obtain ⟨y, hy⟩ := hψ v2
    exact ⟨(x, y), Prod.ext hx hy⟩
  have hker : Fintype.card (LinearMap.ker Φ) =
      Fintype.card (LinearMap.ker φ) * Fintype.card (LinearMap.ker ψ) := by
    have heq : Fintype.card (LinearMap.ker Φ) =
        Fintype.card (LinearMap.ker φ × LinearMap.ker ψ) :=
      Fintype.card_congr
        { toFun := fun z => (⟨z.1.1, (Prod.ext_iff.mp (LinearMap.mem_ker.mp z.2)).1⟩,
            ⟨z.1.2, (Prod.ext_iff.mp (LinearMap.mem_ker.mp z.2)).2⟩)
          invFun := fun z => ⟨(z.1.1, z.2.1), LinearMap.mem_ker.mpr
            (Prod.ext (LinearMap.mem_ker.mp z.1.2) (LinearMap.mem_ker.mp z.2.2))⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    rw [heq, Fintype.card_prod]
  have hfiber : ∀ p : V1 × V2, (Finset.univ.filter (fun w : P × Q => Φ w = p)).card =
      Fintype.card (LinearMap.ker φ) * Fintype.card (LinearMap.ker ψ) := by
    intro p
    obtain ⟨w0, hw0⟩ := hΦ p
    rw [← hker]
    refine Finset.card_bij (fun w hw => (⟨w - w0, by
        rw [LinearMap.mem_ker, map_sub, (Finset.mem_filter.mp hw).2, hw0]; exact sub_self p⟩ : LinearMap.ker Φ)) ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro w1 _ w2 _ h; exact sub_left_inj.mp (congrArg Subtype.val h)
    · intro z _
      refine ⟨z.1 + w0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Subtype.ext (by abel)⟩
      rw [map_add, LinearMap.mem_ker.mp z.2, zero_add, hw0]
  have hhits : Nat.card {w : P × Q // pred w} ≤
      G.card * (Fintype.card (LinearMap.ker φ) * Fintype.card (LinearMap.ker ψ)) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hsub : Finset.univ.filter pred ⊆ G.biUnion (fun p => Finset.univ.filter (fun w : P × Q => Φ w = p)) := by
      intro w hw
      rw [Finset.mem_biUnion]
      exact ⟨Φ w, himp w (Finset.mem_filter.mp hw).2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
    have hle := Finset.card_le_card hsub
    have hbu : (G.biUnion (fun p => Finset.univ.filter (fun w : P × Q => Φ w = p))).card ≤
        ∑ p ∈ G, (Finset.univ.filter (fun w : P × Q => Φ w = p)).card := Finset.card_biUnion_le
    have hsum : ∑ p ∈ G, (Finset.univ.filter (fun w : P × Q => Φ w = p)).card =
        G.card * (Fintype.card (LinearMap.ker φ) * Fintype.card (LinearMap.ker ψ)) := by
      simp_rw [hfiber]; rw [Finset.sum_const, smul_eq_mul]
    exact (hle.trans hbu).trans_eq hsum
  rw [Nat.card_eq_fintype_card (α := P), Nat.card_eq_fintype_card (α := Q), hP, hQ]
  have hmul := Nat.mul_le_mul_left (Fintype.card V1 * Fintype.card V2) hhits
  calc Fintype.card V1 * Fintype.card V2 * Nat.card {w : P × Q // pred w}
      ≤ Fintype.card V1 * Fintype.card V2 *
        (G.card * (Fintype.card (LinearMap.ker φ) * Fintype.card (LinearMap.ker ψ))) := hmul
    _ = G.card * (Fintype.card V1 * Fintype.card (LinearMap.ker φ)) *
        (Fintype.card V2 * Fintype.card (LinearMap.ker ψ)) := by ring

lemma bad_pair_2coord_decide :
    ∀ (p q a b : F),
      (Finset.univ.filter (fun x : ((F × F) × (F × F)) =>
        x.1.1 * x.1.2 = 0 ∧ x.2.1 * x.2.2 = 0 ∧
        (x.1.1 + p * x.2.1 + a) * (x.2.2 + q * x.1.2 + b) = 0)).card ≤ 8 := by
  decide

lemma bad_pair_1coord_decide :
    ∀ (a : F),
      (Finset.univ.filter (fun x : (F × F) × F =>
        x.1.1 * x.1.2 = 0 ∧ (x.1.1 + a) * x.2 = 0)).card ≤ 5 := by
  decide

lemma surj_ext_of_surj {U : Type*} [AddCommGroup U] [Module F U] [Fintype U]
    {k : ℕ} (f : Fin k → U →ₗ[F] F) (hf : Function.Surjective (LinearMap.pi f))
    (g : U →ₗ[F] F) :
    (∃ S : Finset (Fin k), ∀ x : U, g x = ∑ c ∈ S, f c x) ∨
    Function.Surjective (LinearMap.prod (LinearMap.pi f) g) := by
  classical
  by_cases hker : ∀ x ∈ LinearMap.ker (LinearMap.pi f), g x = 0
  · left
    have hsec : ∀ c : Fin k, ∃ e : U, LinearMap.pi f e = fun c' => if c' = c then 1 else 0 :=
      fun c => hf (fun c' => if c' = c then 1 else 0)
    let e : Fin k → U := fun c => Classical.choose (hsec c)
    have he : ∀ c c' : Fin k, f c' (e c) = if c' = c then 1 else 0 := fun c c' =>
      congrFun (Classical.choose_spec (hsec c)) c'
    let S : Finset (Fin k) := Finset.univ.filter (fun c => g (e c) ≠ 0)
    refine ⟨S, fun x => ?_⟩
    let z : U := x - ∑ c : Fin k, f c x • e c
    have hz : z ∈ LinearMap.ker (LinearMap.pi f) := by
      rw [LinearMap.mem_ker]
      funext c'
      change f c' (x - ∑ c : Fin k, f c x • e c) = 0
      rw [map_sub, map_sum]
      simp_rw [map_smul, he, smul_eq_mul]
      rw [Finset.sum_eq_single c']
      · simp
      · intro c _ hne; simp [Ne.symm hne]
      · intro h; exact (h (Finset.mem_univ _)).elim
    have hgz : g z = 0 := hker z hz
    have hgx : g x = ∑ c : Fin k, f c x * g (e c) := by
      dsimp [z] at hgz
      rw [map_sub, map_sum] at hgz
      have h1 : g x = ∑ c : Fin k, g (f c x • e c) := sub_eq_zero.mp hgz
      rw [h1]
      refine Finset.sum_congr rfl fun c _ => by rw [map_smul, smul_eq_mul]
    rw [hgx, ← Finset.sum_subset (Finset.subset_univ S)]
    · refine Finset.sum_congr rfl fun c hc => ?_
      have hg1 : g (e c) = 1 := by
        have hne := (Finset.mem_filter.mp hc).2
        have hz2 : ∀ t : F, t = 0 ∨ t = 1 := by decide
        exact (hz2 (g (e c))).resolve_left hne
      rw [hg1, mul_one]
    · intro c _ hcS
      have hg0 : g (e c) = 0 := by
        by_contra h; exact hcS (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      rw [hg0, mul_zero]
  · right
    push Not at hker
    rcases hker with ⟨z, hzker, hgz⟩
    have hgz1 : g z = 1 := by
      have hz2 : ∀ t : F, t = 0 ∨ t = 1 := by decide
      exact (hz2 (g z)).resolve_left hgz
    intro ⟨v, b⟩
    obtain ⟨x0, hx0⟩ := hf v
    refine ⟨x0 + (b - g x0) • z, Prod.ext ?_ ?_⟩
    · change (LinearMap.pi f) (x0 + (b - g x0) • z) = v
      rw [map_add, map_smul, hx0, LinearMap.mem_ker.mp hzker, smul_zero, add_zero]
    · change g (x0 + (b - g x0) • z) = b
      rw [map_add, map_smul, smul_eq_mul, hgz1, mul_one]; abel

lemma hits_bound_one_ninth
    {P Q : Type*} [AddCommGroup P] [Module F P] [Fintype P] [Module.Finite F P]
    [AddCommGroup Q] [Module F Q] [Fintype Q] [Module.Finite F Q]
    (k : ℕ) (L : Fin k → P →ₗ[F] F) (R : Fin k → Q →ₗ[F] F)
    (hPsurj : Function.Surjective (fun x : P => fun c : Fin k => L c x))
    (hQsurj : Function.Surjective (fun y : Q => fun c : Fin k => R c y))
    (u0 : P →ₗ[F] F) (v0 : Q →ₗ[F] F)
    (hu0 : u0 ≠ 0) (hv0 : v0 ≠ 0)
    (hnot_copy : ∀ c : Fin k, ¬ (u0 = L c ∧ v0 = R c))
    (pred : P × Q → Prop)
    (hpred_s : ∀ w : P × Q, pred w → ∀ c : Fin k, L c w.1 * R c w.2 = 0)
    (hpred_0 : ∀ w : P × Q, pred w → u0 w.1 * v0 w.2 = 0) :
    9 * 4 ^ k * Nat.card {w : P × Q // pred w} ≤ 8 * 3 ^ k * Nat.card P * Nat.card Q := by
  classical
  let φ : P →ₗ[F] (Fin k → F) := LinearMap.pi L
  let ψ : Q →ₗ[F] (Fin k → F) := LinearMap.pi R
  rcases surj_ext_of_surj L hPsurj u0 with ⟨S, hS⟩ | hPsurj'
  · have hS_ne : S.Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      apply hu0; apply LinearMap.ext; intro x; rw [hS x, hemp]; simp
    rcases surj_ext_of_surj R hQsurj v0 with ⟨T, hT⟩ | hQsurj'
    · have hT_ne : T.Nonempty := by
        by_contra hemp
        rw [Finset.not_nonempty_iff_eq_empty] at hemp
        apply hv0; apply LinearMap.ext; intro y; rw [hT y, hemp]; simp
      have hex_pair : ∃ c1 ∈ S, ∃ c2 ∈ T, c1 ≠ c2 := by
        by_contra hall
        push Not at hall
        rcases hS_ne with ⟨c1, hc1⟩
        rcases hT_ne with ⟨c2, hc2⟩
        have h12 : c1 = c2 := hall c1 hc1 c2 hc2
        subst h12
        have hSsing : S = {c1} := by
          apply Finset.eq_singleton_iff_unique_mem.mpr ⟨hc1, fun c hc => hall c hc c1 hc2⟩
        have hTsing : T = {c1} := by
          apply Finset.eq_singleton_iff_unique_mem.mpr ⟨hc2, fun c hc => (hall c1 hc1 c hc).symm⟩
        apply hnot_copy c1
        refine ⟨LinearMap.ext fun x => by rw [hS x, hSsing, Finset.sum_singleton],
          LinearMap.ext fun y => by rw [hT y, hTsing, Finset.sum_singleton]⟩
      rcases hex_pair with ⟨c1, hc1S, c2, hc2T, hc12⟩
      let G : Finset ((Fin k → F) × (Fin k → F)) :=
        Finset.univ.filter (fun uv =>
          (∀ c : Fin k, uv.1 c * uv.2 c = 0) ∧ (∑ c ∈ S, uv.1 c) * (∑ c ∈ T, uv.2 c) = 0)
      have hG_card : 9 * G.card ≤ 8 * 3 ^ k := by
        let Rest := (Finset.univ : Finset (Fin k)).erase c1 |>.erase c2
        have hRest_card : Rest.card = k - 2 := by
          have hc2_in : c2 ∈ Finset.univ.erase c1 := Finset.mem_erase.mpr ⟨hc12.symm, Finset.mem_univ _⟩
          rw [Finset.card_erase_of_mem hc2_in, Finset.card_erase_of_mem (Finset.mem_univ c1),
            Finset.card_univ, Fintype.card_fin]
          omega
        have hk2 : 2 ≤ k := by
          have : ({c1, c2} : Finset (Fin k)).card ≤ (Finset.univ : Finset (Fin k)).card :=
            Finset.card_le_univ _
          rw [Finset.card_pair hc12, Finset.card_univ, Fintype.card_fin] at this
          exact this
        let GoodRest : Finset (Rest → F × F) :=
          Finset.univ.filter (fun r => ∀ c : Rest, (r c).1 * (r c).2 = 0)
        have hGoodRest : GoodRest.card = 3 ^ (k - 2) := by
          let S0 : Finset (F × F) := Finset.univ.filter (fun p : F × F => p.1 * p.2 = 0)
          have hS0 : S0.card = 3 := by decide
          have hpi : GoodRest = Fintype.piFinset (fun _ : Rest => S0) := by
            ext r; simp [GoodRest, S0, Fintype.mem_piFinset]
          rw [hpi, Fintype.card_piFinset, Finset.prod_const, hS0, Finset.card_univ,
            Fintype.card_coe, hRest_card]
        let proj : ((Fin k → F) × (Fin k → F)) → (Rest → F × F) := fun uv c => (uv.1 c.1, uv.2 c.1)
        have hG_le : G.card ≤ ∑ r ∈ GoodRest, (G.filter (fun uv => proj uv = r)).card := by
          have hsub : G ⊆ GoodRest.biUnion (fun r => G.filter (fun uv => proj uv = r)) := by
            intro uv huv
            rw [Finset.mem_biUnion]
            refine ⟨proj uv, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun c =>
              (Finset.mem_filter.mp huv).2.1 c.1⟩, Finset.mem_filter.mpr ⟨huv, rfl⟩⟩
          exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le
        have hfib_le : ∀ r ∈ GoodRest, (G.filter (fun uv => proj uv = r)).card ≤ 8 := by
          intro r _
          let p : F := if c2 ∈ S then 1 else 0
          let q : F := if c1 ∈ T then 1 else 0
          let a : F := ∑ c ∈ ((S.erase c1).erase c2).attach,
            (r ⟨c.1, Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase c.2,
              Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase (Finset.mem_of_mem_erase c.2), Finset.mem_univ _⟩⟩⟩).1
          let b : F := ∑ c ∈ ((T.erase c2).erase c1).attach,
            (r ⟨c.1, Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase (Finset.mem_of_mem_erase c.2),
              Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase c.2, Finset.mem_univ _⟩⟩⟩).2
          let img : ((Fin k → F) × (Fin k → F)) → ((F × F) × (F × F)) :=
            fun uv => ((uv.1 c1, uv.2 c1), (uv.1 c2, uv.2 c2))
          have hinj : Set.InjOn img (G.filter (fun uv => proj uv = r) : Set _) := by
            intro uv1 h1 uv2 h2 heq
            have hr1 := (Finset.mem_filter.mp h1).2
            have hr2 := (Finset.mem_filter.mp h2).2
            apply Prod.ext <;> funext c
            · by_cases hcc1 : c = c1
              · subst hcc1; exact congrArg (fun z => z.1.1) heq
              · by_cases hcc2 : c = c2
                · subst hcc2; exact congrArg (fun z => z.2.1) heq
                · have hcR : c ∈ Rest := Finset.mem_erase.mpr ⟨hcc2, Finset.mem_erase.mpr ⟨hcc1, Finset.mem_univ _⟩⟩
                  exact congrArg Prod.fst (congrFun (hr1.trans hr2.symm) ⟨c, hcR⟩)
            · by_cases hcc1 : c = c1
              · subst hcc1; exact congrArg (fun z => z.1.2) heq
              · by_cases hcc2 : c = c2
                · subst hcc2; exact congrArg (fun z => z.2.2) heq
                · have hcR : c ∈ Rest := Finset.mem_erase.mpr ⟨hcc2, Finset.mem_erase.mpr ⟨hcc1, Finset.mem_univ _⟩⟩
                  exact congrArg Prod.snd (congrFun (hr1.trans hr2.symm) ⟨c, hcR⟩)
          have hsub_img : (G.filter (fun uv => proj uv = r)).image img ⊆
              Finset.univ.filter (fun x : ((F × F) × (F × F)) =>
                x.1.1 * x.1.2 = 0 ∧ x.2.1 * x.2.2 = 0 ∧
                (x.1.1 + p * x.2.1 + a) * (x.2.2 + q * x.1.2 + b) = 0) := by
            intro z hz
            rcases Finset.mem_image.mp hz with ⟨uv, huv, rfl⟩
            have huvG := (Finset.mem_filter.mp huv).1
            have huvR := (Finset.mem_filter.mp huv).2
            have huvSpec := (Finset.mem_filter.mp huvG).2
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, huvSpec.1 c1, huvSpec.1 c2, ?_⟩
            have hS_sum : ∑ c ∈ S, uv.1 c = uv.1 c1 + p * uv.1 c2 + a := by
              rw [← Finset.add_sum_erase S uv.1 hc1S]
              by_cases hc2S : c2 ∈ S
              · have hc2S' : c2 ∈ S.erase c1 := Finset.mem_erase.mpr ⟨hc12.symm, hc2S⟩
                rw [← Finset.add_sum_erase (S.erase c1) uv.1 hc2S']
                have ha_eq : a = ∑ c ∈ (S.erase c1).erase c2, uv.1 c := by
                  dsimp [a]
                  rw [← Finset.sum_attach ((S.erase c1).erase c2) uv.1]
                  refine Finset.sum_congr rfl fun c _ => ?_
                  exact (congrArg Prod.fst (congrFun huvR _)).symm
                simp [p, hc2S, ha_eq, add_assoc]
              · have her : (S.erase c1).erase c2 = S.erase c1 :=
                  Finset.erase_eq_of_notMem (fun h => hc2S (Finset.mem_of_mem_erase h))
                have ha_eq : a = ∑ c ∈ S.erase c1, uv.1 c := by
                  dsimp [a]
                  have : ∑ c ∈ (S.erase c1).erase c2, uv.1 c = ∑ c ∈ S.erase c1, uv.1 c := by rw [her]
                  rw [← this, ← Finset.sum_attach ((S.erase c1).erase c2) uv.1]
                  refine Finset.sum_congr rfl fun c _ => ?_
                  exact (congrArg Prod.fst (congrFun huvR _)).symm
                simp [p, hc2S, ha_eq]
            have hT_sum : ∑ c ∈ T, uv.2 c = uv.2 c2 + q * uv.2 c1 + b := by
              rw [← Finset.add_sum_erase T uv.2 hc2T]
              by_cases hc1T : c1 ∈ T
              · have hc1T' : c1 ∈ T.erase c2 := Finset.mem_erase.mpr ⟨hc12, hc1T⟩
                rw [← Finset.add_sum_erase (T.erase c2) uv.2 hc1T']
                have hb_eq : b = ∑ c ∈ (T.erase c2).erase c1, uv.2 c := by
                  dsimp [b]
                  rw [← Finset.sum_attach ((T.erase c2).erase c1) uv.2]
                  refine Finset.sum_congr rfl fun c _ => ?_
                  exact (congrArg Prod.snd (congrFun huvR _)).symm
                simp [q, hc1T, hb_eq, add_assoc]
              · have her : (T.erase c2).erase c1 = T.erase c2 :=
                  Finset.erase_eq_of_notMem (fun h => hc1T (Finset.mem_of_mem_erase h))
                have hb_eq : b = ∑ c ∈ T.erase c2, uv.2 c := by
                  dsimp [b]
                  have : ∑ c ∈ (T.erase c2).erase c1, uv.2 c = ∑ c ∈ T.erase c2, uv.2 c := by rw [her]
                  rw [← this, ← Finset.sum_attach ((T.erase c2).erase c1) uv.2]
                  refine Finset.sum_congr rfl fun c _ => ?_
                  exact (congrArg Prod.snd (congrFun huvR _)).symm
                simp [q, hc1T, hb_eq]
            rw [← hS_sum, ← hT_sum]
            exact huvSpec.2
          rw [← Finset.card_image_of_injOn hinj]
          exact (Finset.card_le_card hsub_img).trans (bad_pair_2coord_decide p q a b)
        have hG_bound : G.card ≤ 8 * 3 ^ (k - 2) := by
          calc G.card ≤ ∑ r ∈ GoodRest, (G.filter (fun uv => proj uv = r)).card := hG_le
            _ ≤ ∑ _r ∈ GoodRest, 8 := Finset.sum_le_sum hfib_le
            _ = GoodRest.card * 8 := by rw [Finset.sum_const, smul_eq_mul]
            _ = 8 * 3 ^ (k - 2) := by rw [hGoodRest, mul_comm]
        calc 9 * G.card ≤ 9 * (8 * 3 ^ (k - 2)) := Nat.mul_le_mul_left 9 hG_bound
          _ = 8 * (3 ^ 2 * 3 ^ (k - 2)) := by ring
          _ = 8 * 3 ^ (2 + (k - 2)) := by rw [← pow_add]
          _ = 8 * 3 ^ k := by rw [Nat.add_sub_of_le hk2]
      have hcore := card_hits_le_of_good φ ψ hPsurj hQsurj pred G (fun w hw => by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpred_s w hw, ?_⟩
        change (∑ c ∈ S, L c w.1) * (∑ c ∈ T, R c w.2) = 0
        rw [← hS w.1, ← hT w.2]
        exact hpred_0 w hw)
      have hcardV : Fintype.card (Fin k → F) = 2 ^ k := by simp
      rw [hcardV] at hcore
      have h4k : 2 ^ k * 2 ^ k = 4 ^ k := by rw [← mul_pow]; norm_num
      rw [h4k] at hcore
      calc 9 * 4 ^ k * Nat.card {w : P × Q // pred w}
          = 9 * (4 ^ k * Nat.card {w : P × Q // pred w}) := by ring
        _ ≤ 9 * (G.card * Nat.card P * Nat.card Q) := Nat.mul_le_mul_left 9 hcore
        _ = (9 * G.card) * Nat.card P * Nat.card Q := by ring
        _ ≤ (8 * 3 ^ k) * Nat.card P * Nat.card Q :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hG_card)
    · rcases hS_ne with ⟨c1, hc1S⟩
      let ψ' : Q →ₗ[F] ((Fin k → F) × F) := LinearMap.prod ψ v0
      let G : Finset ((Fin k → F) × ((Fin k → F) × F)) :=
        Finset.univ.filter (fun uvb =>
          (∀ c : Fin k, uvb.1 c * uvb.2.1 c = 0) ∧ (∑ c ∈ S, uvb.1 c) * uvb.2.2 = 0)
      have hG_card : 3 * G.card ≤ 5 * 3 ^ k := by
        let Rest := (Finset.univ : Finset (Fin k)).erase c1
        have hRest_card : Rest.card = k - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ c1), Finset.card_univ, Fintype.card_fin]
        have hk1 : 1 ≤ k := Nat.pos_of_ne_zero (fun hk0 => by subst hk0; exact Fin.elim0 c1)
        let GoodRest : Finset (Rest → F × F) :=
          Finset.univ.filter (fun r => ∀ c : Rest, (r c).1 * (r c).2 = 0)
        have hGoodRest : GoodRest.card = 3 ^ (k - 1) := by
          let S0 : Finset (F × F) := Finset.univ.filter (fun p : F × F => p.1 * p.2 = 0)
          have hS0 : S0.card = 3 := by decide
          have hpi : GoodRest = Fintype.piFinset (fun _ : Rest => S0) := by
            ext r; simp [GoodRest, S0, Fintype.mem_piFinset]
          rw [hpi, Fintype.card_piFinset, Finset.prod_const, hS0, Finset.card_univ,
            Fintype.card_coe, hRest_card]
        let proj : ((Fin k → F) × ((Fin k → F) × F)) → (Rest → F × F) :=
          fun uvb c => (uvb.1 c.1, uvb.2.1 c.1)
        have hG_le : G.card ≤ ∑ r ∈ GoodRest, (G.filter (fun uvb => proj uvb = r)).card := by
          have hsub : G ⊆ GoodRest.biUnion (fun r => G.filter (fun uvb => proj uvb = r)) := by
            intro uvb huvb
            rw [Finset.mem_biUnion]
            refine ⟨proj uvb, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun c =>
              (Finset.mem_filter.mp huvb).2.1 c.1⟩, Finset.mem_filter.mpr ⟨huvb, rfl⟩⟩
          exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le
        have hfib_le : ∀ r ∈ GoodRest, (G.filter (fun uvb => proj uvb = r)).card ≤ 5 := by
          intro r _
          let a : F := ∑ c ∈ (S.erase c1).attach,
            (r ⟨c.1, Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase c.2, Finset.mem_univ _⟩⟩).1
          let img : ((Fin k → F) × ((Fin k → F) × F)) → ((F × F) × F) :=
            fun uvb => ((uvb.1 c1, uvb.2.1 c1), uvb.2.2)
          have hinj : Set.InjOn img (G.filter (fun uvb => proj uvb = r) : Set _) := by
            intro x1 h1 x2 h2 heq
            have hr1 := (Finset.mem_filter.mp h1).2
            have hr2 := (Finset.mem_filter.mp h2).2
            refine Prod.ext (funext fun c => ?_) (Prod.ext (funext fun c => ?_) (congrArg (fun z : ((F × F) × F) => z.2) heq))
            · by_cases hcc : c = c1
              · subst hcc; exact congrArg (fun z => z.1.1) heq
              · exact congrArg Prod.fst (congrFun (hr1.trans hr2.symm) ⟨c, Finset.mem_erase.mpr ⟨hcc, Finset.mem_univ _⟩⟩)
            · by_cases hcc : c = c1
              · subst hcc; exact congrArg (fun z => z.1.2) heq
              · exact congrArg Prod.snd (congrFun (hr1.trans hr2.symm) ⟨c, Finset.mem_erase.mpr ⟨hcc, Finset.mem_univ _⟩⟩)
          have hsub_img : (G.filter (fun uvb => proj uvb = r)).image img ⊆
              Finset.univ.filter (fun z : (F × F) × F => z.1.1 * z.1.2 = 0 ∧ (z.1.1 + a) * z.2 = 0) := by
            intro z hz
            rcases Finset.mem_image.mp hz with ⟨uvb, huvb, rfl⟩
            have hG := (Finset.mem_filter.mp (Finset.mem_filter.mp huvb).1).2
            have hR := (Finset.mem_filter.mp huvb).2
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hG.1 c1, ?_⟩
            have hS_sum : ∑ c ∈ S, uvb.1 c = uvb.1 c1 + a := by
              rw [← Finset.add_sum_erase S uvb.1 hc1S, ← Finset.sum_attach (S.erase c1) uvb.1]
              congr 1; dsimp [a]
              refine Finset.sum_congr rfl fun c _ => ?_
              exact congrArg Prod.fst (congrFun hR ⟨c.1, Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase c.2, Finset.mem_univ _⟩⟩)
            rw [← hS_sum]; exact hG.2
          rw [← Finset.card_image_of_injOn hinj]
          exact (Finset.card_le_card hsub_img).trans (bad_pair_1coord_decide a)
        have hG_bound : G.card ≤ 5 * 3 ^ (k - 1) := by
          calc G.card ≤ ∑ r ∈ GoodRest, (G.filter (fun uvb => proj uvb = r)).card := hG_le
            _ ≤ ∑ _r ∈ GoodRest, 5 := Finset.sum_le_sum hfib_le
            _ = GoodRest.card * 5 := by rw [Finset.sum_const, smul_eq_mul]
            _ = 5 * 3 ^ (k - 1) := by rw [hGoodRest, mul_comm]
        calc 3 * G.card ≤ 3 * (5 * 3 ^ (k - 1)) := Nat.mul_le_mul_left 3 hG_bound
          _ = 5 * (3 ^ 1 * 3 ^ (k - 1)) := by ring
          _ = 5 * 3 ^ (1 + (k - 1)) := by rw [← pow_add]
          _ = 5 * 3 ^ k := by rw [Nat.add_sub_of_le hk1]
      have hcore := card_hits_le_of_good φ ψ' hPsurj hQsurj' pred G (fun w hw => by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpred_s w hw, ?_⟩
        change (∑ c ∈ S, L c w.1) * v0 w.2 = 0
        rw [← hS w.1]; exact hpred_0 w hw)
      have hcardV1 : Fintype.card (Fin k → F) = 2 ^ k := by simp
      have hcardV2 : Fintype.card ((Fin k → F) × F) = 2 ^ k * 2 := by simp
      rw [hcardV1, hcardV2] at hcore
      have h4k : 2 ^ k * (2 ^ k * 2) = 2 * 4 ^ k := by
        have : 2 ^ k * 2 ^ k = 4 ^ k := by rw [← mul_pow]; norm_num
        linarith
      rw [h4k] at hcore
      have h18 : 2 * (9 * 4 ^ k * Nat.card {w : P × Q // pred w}) ≤
          2 * (8 * 3 ^ k * Nat.card P * Nat.card Q) := by
        calc 2 * (9 * 4 ^ k * Nat.card {w : P × Q // pred w})
            = 9 * (2 * 4 ^ k * Nat.card {w : P × Q // pred w}) := by ring
          _ ≤ 9 * (G.card * Nat.card P * Nat.card Q) := Nat.mul_le_mul_left 9 hcore
          _ = 3 * (3 * G.card) * Nat.card P * Nat.card Q := by ring
          _ ≤ 3 * (5 * 3 ^ k) * Nat.card P * Nat.card Q :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 3 hG_card))
          _ ≤ 16 * 3 ^ k * Nat.card P * Nat.card Q := by
              have : 3 * (5 * 3 ^ k) ≤ 16 * 3 ^ k := by omega
              exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ this)
          _ = 2 * (8 * 3 ^ k * Nat.card P * Nat.card Q) := by ring
      omega
  · rcases surj_ext_of_surj R hQsurj v0 with ⟨T, hT⟩ | hQsurj'
    · have hT_ne : T.Nonempty := by
        by_contra hemp
        rw [Finset.not_nonempty_iff_eq_empty] at hemp
        apply hv0; apply LinearMap.ext; intro y; rw [hT y, hemp]; simp
      rcases hT_ne with ⟨c1, hc1T⟩
      let φ' : P →ₗ[F] ((Fin k → F) × F) := LinearMap.prod φ u0
      let G : Finset (((Fin k → F) × F) × (Fin k → F)) :=
        Finset.univ.filter (fun ubv =>
          (∀ c : Fin k, ubv.1.1 c * ubv.2 c = 0) ∧ ubv.1.2 * (∑ c ∈ T, ubv.2 c) = 0)
      have hG_card : 3 * G.card ≤ 5 * 3 ^ k := by
        let Rest := (Finset.univ : Finset (Fin k)).erase c1
        have hRest_card : Rest.card = k - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ c1), Finset.card_univ, Fintype.card_fin]
        have hk1 : 1 ≤ k := Nat.pos_of_ne_zero (fun hk0 => by subst hk0; exact Fin.elim0 c1)
        let GoodRest : Finset (Rest → F × F) :=
          Finset.univ.filter (fun r => ∀ c : Rest, (r c).1 * (r c).2 = 0)
        have hGoodRest : GoodRest.card = 3 ^ (k - 1) := by
          let S0 : Finset (F × F) := Finset.univ.filter (fun p : F × F => p.1 * p.2 = 0)
          have hS0 : S0.card = 3 := by decide
          have hpi : GoodRest = Fintype.piFinset (fun _ : Rest => S0) := by
            ext r; simp [GoodRest, S0, Fintype.mem_piFinset]
          rw [hpi, Fintype.card_piFinset, Finset.prod_const, hS0, Finset.card_univ,
            Fintype.card_coe, hRest_card]
        let proj : (((Fin k → F) × F) × (Fin k → F)) → (Rest → F × F) :=
          fun ubv c => (ubv.1.1 c.1, ubv.2 c.1)
        have hG_le : G.card ≤ ∑ r ∈ GoodRest, (G.filter (fun ubv => proj ubv = r)).card := by
          have hsub : G ⊆ GoodRest.biUnion (fun r => G.filter (fun ubv => proj ubv = r)) := by
            intro ubv hubv
            rw [Finset.mem_biUnion]
            refine ⟨proj ubv, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun c =>
              (Finset.mem_filter.mp hubv).2.1 c.1⟩, Finset.mem_filter.mpr ⟨hubv, rfl⟩⟩
          exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le
        have hfib_le : ∀ r ∈ GoodRest, (G.filter (fun ubv => proj ubv = r)).card ≤ 5 := by
          intro r _
          let a : F := ∑ c ∈ (T.erase c1).attach,
            (r ⟨c.1, Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase c.2, Finset.mem_univ _⟩⟩).2
          let img : (((Fin k → F) × F) × (Fin k → F)) → ((F × F) × F) :=
            fun ubv => ((ubv.2 c1, ubv.1.1 c1), ubv.1.2)
          have hinj : Set.InjOn img (G.filter (fun ubv => proj ubv = r) : Set _) := by
            intro x1 h1 x2 h2 heq
            have hr1 := (Finset.mem_filter.mp h1).2
            have hr2 := (Finset.mem_filter.mp h2).2
            refine Prod.ext (Prod.ext (funext fun c => ?_) (congrArg (fun z : ((F × F) × F) => z.2) heq)) (funext fun c => ?_)
            · by_cases hcc : c = c1
              · subst hcc; exact congrArg (fun z => z.1.2) heq
              · exact congrArg Prod.fst (congrFun (hr1.trans hr2.symm) ⟨c, Finset.mem_erase.mpr ⟨hcc, Finset.mem_univ _⟩⟩)
            · by_cases hcc : c = c1
              · subst hcc; exact congrArg (fun z => z.1.1) heq
              · exact congrArg Prod.snd (congrFun (hr1.trans hr2.symm) ⟨c, Finset.mem_erase.mpr ⟨hcc, Finset.mem_univ _⟩⟩)
          have hsub_img : (G.filter (fun ubv => proj ubv = r)).image img ⊆
              Finset.univ.filter (fun z : (F × F) × F => z.1.1 * z.1.2 = 0 ∧ (z.1.1 + a) * z.2 = 0) := by
            intro z hz
            rcases Finset.mem_image.mp hz with ⟨ubv, hubv, rfl⟩
            have hG := (Finset.mem_filter.mp (Finset.mem_filter.mp hubv).1).2
            have hR := (Finset.mem_filter.mp hubv).2
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
            · rw [mul_comm]; exact hG.1 c1
            · have hT_sum : ∑ c ∈ T, ubv.2 c = ubv.2 c1 + a := by
                rw [← Finset.add_sum_erase T ubv.2 hc1T, ← Finset.sum_attach (T.erase c1) ubv.2]
                congr 1; dsimp [a]
                refine Finset.sum_congr rfl fun c _ => ?_
                exact congrArg Prod.snd (congrFun hR ⟨c.1, Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase c.2, Finset.mem_univ _⟩⟩)
              rw [← hT_sum, mul_comm]; exact hG.2
          rw [← Finset.card_image_of_injOn hinj]
          exact (Finset.card_le_card hsub_img).trans (bad_pair_1coord_decide a)
        have hG_bound : G.card ≤ 5 * 3 ^ (k - 1) := by
          calc G.card ≤ ∑ r ∈ GoodRest, (G.filter (fun ubv => proj ubv = r)).card := hG_le
            _ ≤ ∑ _r ∈ GoodRest, 5 := Finset.sum_le_sum hfib_le
            _ = GoodRest.card * 5 := by rw [Finset.sum_const, smul_eq_mul]
            _ = 5 * 3 ^ (k - 1) := by rw [hGoodRest, mul_comm]
        calc 3 * G.card ≤ 3 * (5 * 3 ^ (k - 1)) := Nat.mul_le_mul_left 3 hG_bound
          _ = 5 * (3 ^ 1 * 3 ^ (k - 1)) := by ring
          _ = 5 * 3 ^ (1 + (k - 1)) := by rw [← pow_add]
          _ = 5 * 3 ^ k := by rw [Nat.add_sub_of_le hk1]
      have hcore := card_hits_le_of_good φ' ψ hPsurj' hQsurj pred G (fun w hw => by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpred_s w hw, ?_⟩
        change u0 w.1 * (∑ c ∈ T, R c w.2) = 0
        rw [← hT w.2]; exact hpred_0 w hw)
      have hcardV1 : Fintype.card ((Fin k → F) × F) = 2 ^ k * 2 := by simp
      have hcardV2 : Fintype.card (Fin k → F) = 2 ^ k := by simp
      rw [hcardV1, hcardV2] at hcore
      have h4k : (2 ^ k * 2) * 2 ^ k = 2 * 4 ^ k := by
        have : 2 ^ k * 2 ^ k = 4 ^ k := by rw [← mul_pow]; norm_num
        linarith
      rw [h4k] at hcore
      have h18 : 2 * (9 * 4 ^ k * Nat.card {w : P × Q // pred w}) ≤
          2 * (8 * 3 ^ k * Nat.card P * Nat.card Q) := by
        calc 2 * (9 * 4 ^ k * Nat.card {w : P × Q // pred w})
            = 9 * (2 * 4 ^ k * Nat.card {w : P × Q // pred w}) := by ring
          _ ≤ 9 * (G.card * Nat.card P * Nat.card Q) := Nat.mul_le_mul_left 9 hcore
          _ = 3 * (3 * G.card) * Nat.card P * Nat.card Q := by ring
          _ ≤ 3 * (5 * 3 ^ k) * Nat.card P * Nat.card Q :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 3 hG_card))
          _ ≤ 16 * 3 ^ k * Nat.card P * Nat.card Q := by
              have : 3 * (5 * 3 ^ k) ≤ 16 * 3 ^ k := by omega
              exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ this)
          _ = 2 * (8 * 3 ^ k * Nat.card P * Nat.card Q) := by ring
      omega
    · let φ' : P →ₗ[F] ((Fin k → F) × F) := LinearMap.prod φ u0
      let ψ' : Q →ₗ[F] ((Fin k → F) × F) := LinearMap.prod ψ v0
      let G : Finset (((Fin k → F) × F) × ((Fin k → F) × F)) :=
        Finset.univ.filter (fun p => (∀ c : Fin k, p.1.1 c * p.2.1 c = 0) ∧ p.1.2 * p.2.2 = 0)
      have hG_card : G.card = 3 * 3 ^ k := by
        let G1 : Finset ((Fin k → F) × (Fin k → F)) :=
          Finset.univ.filter (fun uv => ∀ c : Fin k, uv.1 c * uv.2 c = 0)
        let G2 : Finset (F × F) := Finset.univ.filter (fun ab => ab.1 * ab.2 = 0)
        have hG2 : G2.card = 3 := by decide
        have hbij : G.card = (G1 ×ˢ G2).card := by
          refine Finset.card_bij (fun p _ => ((p.1.1, p.2.1), (p.1.2, p.2.2))) ?_ ?_ ?_
          · intro p hp
            have h := (Finset.mem_filter.mp hp).2
            exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.1⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.2⟩⟩
          · intro p1 _ p2 _ h
            exact Prod.ext (Prod.ext (congrArg (fun z => z.1.1) h) (congrArg (fun z => z.2.1) h))
              (Prod.ext (congrArg (fun z => z.1.2) h) (congrArg (fun z => z.2.2) h))
          · intro q hq
            have hq1 := (Finset.mem_filter.mp (Finset.mem_product.mp hq).1).2
            have hq2 := (Finset.mem_filter.mp (Finset.mem_product.mp hq).2).2
            exact ⟨((q.1.1, q.2.1), (q.1.2, q.2.2)),
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq1, hq2⟩, rfl⟩
        rw [hbij, Finset.card_product, card_good_pairs_indep k, hG2, mul_comm]
      have hcore := card_hits_le_of_good φ' ψ' hPsurj' hQsurj' pred G (fun w hw =>
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpred_s w hw, hpred_0 w hw⟩)
      have hcardV : Fintype.card ((Fin k → F) × F) = 2 ^ k * 2 := by simp
      rw [hcardV, hG_card] at hcore
      have h4k : (2 ^ k * 2) * (2 ^ k * 2) = 4 * 4 ^ k := by
        have : 2 ^ k * 2 ^ k = 4 ^ k := by rw [← mul_pow]; norm_num
        linarith
      rw [h4k] at hcore
      have h36 : 4 * (9 * 4 ^ k * Nat.card {w : P × Q // pred w}) ≤
          4 * (8 * 3 ^ k * Nat.card P * Nat.card Q) := by
        calc 4 * (9 * 4 ^ k * Nat.card {w : P × Q // pred w})
            = 9 * (4 * 4 ^ k * Nat.card {w : P × Q // pred w}) := by ring
          _ ≤ 9 * (3 * 3 ^ k * Nat.card P * Nat.card Q) := Nat.mul_le_mul_left 9 hcore
          _ = 27 * 3 ^ k * Nat.card P * Nat.card Q := by ring
          _ ≤ 32 * 3 ^ k * Nat.card P * Nat.card Q := by
              have : 27 * 3 ^ k ≤ 32 * 3 ^ k := by omega
              exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ this)
          _ = 4 * (8 * 3 ^ k * Nat.card P * Nat.card Q) := by ring
      omega

lemma finrank_dualAnnihilator_add {U : Type*} [AddCommGroup U] [Module F U] [Module.Finite F U]
    (W : Submodule F U) :
    Module.finrank F W.dualAnnihilator + Module.finrank F W = Module.finrank F U := by
  obtain ⟨W', hcompl⟩ := Submodule.exists_isCompl W
  let proj : U →ₗ[F] W := W.linearProjOfIsCompl W' hcompl
  have hsurj : Function.Surjective (LinearMap.dualMap W.subtype) := by
    intro α
    refine ⟨α.comp proj, LinearMap.ext fun w => ?_⟩
    rw [LinearMap.dualMap_apply, LinearMap.comp_apply, Submodule.coe_subtype]
    exact congrArg α (Submodule.linearProjOfIsCompl_apply_left hcompl w)
  have hker : LinearMap.ker (LinearMap.dualMap W.subtype) = W.dualAnnihilator := by
    ext α
    simp only [LinearMap.mem_ker, Submodule.mem_dualAnnihilator]
    constructor
    · intro h u hu
      exact LinearMap.congr_fun h ⟨u, hu⟩
    · intro h
      apply LinearMap.ext; intro w
      exact h w.1 w.2
  have hrk := LinearMap.finrank_range_add_finrank_ker (LinearMap.dualMap W.subtype)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hker] at hrk
  have hWdual : Module.finrank F (Module.Dual F W) = Module.finrank F W := Subspace.dual_finrank_eq
  have hUdual : Module.finrank F (Module.Dual F U) = Module.finrank F U := Subspace.dual_finrank_eq
  omega

lemma linearIndependent_dual_iff_surjective {U : Type*} [AddCommGroup U] [Module F U] [Module.Finite F U]
    {k : ℕ} (f : Fin k → U →ₗ[F] F) :
    LinearIndependent F f → Function.Surjective (fun u : U => fun c : Fin k => f c u) := by
  intro hind
  let φ : U →ₗ[F] (Fin k → F) := LinearMap.pi f
  change Function.Surjective φ
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  have hdual_inj : Function.Injective (LinearMap.dualMap φ) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro α hα
    rw [LinearMap.mem_ker] at hα
    have hsum : ∑ c : Fin k, α (Pi.single c 1) • f c = 0 := by
      apply LinearMap.ext; intro u
      have hu := LinearMap.congr_fun hα u
      simp only [LinearMap.dualMap_apply, LinearMap.zero_apply] at hu
      have hdecomp : φ u = ∑ c : Fin k, f c u • Pi.single c (1 : F) := by
        ext c'
        simp [φ, Pi.single_apply]
      rw [hdecomp, map_sum] at hu
      simp only [map_smul, smul_eq_mul] at hu
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply]
      rw [← hu]
      refine Finset.sum_congr rfl fun c _ => mul_comm _ _
    have hc0 := Fintype.linearIndependent_iff.mp hind (fun c => α (Pi.single c 1)) hsum
    apply LinearMap.ext; intro v
    have hv : v = ∑ c : Fin k, v c • Pi.single c (1 : F) := by
      ext c'; simp [Pi.single_apply]
    rw [hv, map_sum]
    apply Finset.sum_eq_zero
    intro c _
    rw [map_smul, hc0 c, smul_zero]
  have h1 : Module.finrank F (Module.Dual F (Fin k → F)) =
      Module.finrank F (LinearMap.range (LinearMap.dualMap φ)) :=
    (LinearEquiv.ofInjective _ hdual_inj).finrank_eq
  have h2 : Module.finrank F (LinearMap.range (LinearMap.dualMap φ)) ≤
      Module.finrank F (LinearMap.range φ) := by
    have hker := LinearMap.finrank_range_add_finrank_ker φ
    have hsub : LinearMap.range (LinearMap.dualMap φ) ≤ (LinearMap.ker φ).dualAnnihilator := by
      rintro _ ⟨α, rfl⟩
      rw [Submodule.mem_dualAnnihilator]
      intro u hu
      simp [LinearMap.dualMap_apply, LinearMap.mem_ker.mp hu]
    have hle1 := Submodule.finrank_mono hsub
    have hann := finrank_dualAnnihilator_add (LinearMap.ker φ)
    omega
  have h3 := Submodule.finrank_le (LinearMap.range φ)
  have h4 : Module.finrank F (Module.Dual F (Fin k → F)) = Module.finrank F (Fin k → F) :=
    Subspace.dual_finrank_eq
  omega

lemma finrank_span_eval_eq_sub_ker {E U : Type*} [DecidableEq E]
    [AddCommGroup U] [Module F U] [Module.Finite F U]
    (f : E → U →ₗ[F] F) (A : Finset E) :
    Module.finrank F (Submodule.span F (f '' (A : Set E))) +
      Module.finrank F (⨅ e ∈ A, LinearMap.ker (f e) : Submodule F U) = Module.finrank F U := by
  classical
  let φ : U →ₗ[F] (A → F) := LinearMap.pi (fun e : A => f e.1)
  have hker : LinearMap.ker φ = (⨅ e ∈ A, LinearMap.ker (f e) : Submodule F U) := by
    ext u
    simp only [LinearMap.mem_ker, Submodule.mem_iInf, φ]
    constructor
    · intro h e he
      exact congrFun h ⟨e, he⟩
    · intro h
      funext e
      exact h e.1 e.2
  have hdual_range : LinearMap.range (LinearMap.dualMap φ) = Submodule.span F (f '' (A : Set E)) := by
    apply le_antisymm
    · rintro _ ⟨α, rfl⟩
      have hdecomp : LinearMap.dualMap φ α = ∑ e : A, α (Pi.single e 1) • f e.1 := by
        apply LinearMap.ext; intro u
        simp only [LinearMap.dualMap_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
        have hu : φ u = ∑ e : A, f e.1 u • Pi.single e (1 : F) := by
          ext e'; simp [φ, Pi.single_apply]
        rw [hu, map_sum]
        refine Finset.sum_congr rfl fun e _ => by rw [map_smul, smul_eq_mul, mul_comm]
      rw [hdecomp]
      apply Submodule.sum_mem
      intro e _
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e.1, e.2, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨e, he, rfl⟩
      refine ⟨LinearMap.proj ⟨e, he⟩, LinearMap.ext fun u => rfl⟩
  have hker_eq : LinearMap.range (LinearMap.dualMap φ) = (LinearMap.ker φ).dualAnnihilator := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨α, rfl⟩
      rw [Submodule.mem_dualAnnihilator]
      intro u hu; simp [LinearMap.dualMap_apply, LinearMap.mem_ker.mp hu]
    · have h1 := LinearMap.finrank_range_add_finrank_ker φ
      have h2 := LinearMap.finrank_range_add_finrank_ker (LinearMap.dualMap φ)
      have hann := finrank_dualAnnihilator_add (LinearMap.ker φ)
      have hAdual : Module.finrank F (Module.Dual F (A → F)) = Module.finrank F (A → F) := Subspace.dual_finrank_eq
      have hkerD : LinearMap.ker (LinearMap.dualMap φ) = (LinearMap.range φ).dualAnnihilator := by
        ext α
        simp only [LinearMap.mem_ker, Submodule.mem_dualAnnihilator, LinearMap.mem_range]
        constructor
        · rintro h _ ⟨u, rfl⟩; exact LinearMap.congr_fun h u
        · intro h; apply LinearMap.ext; intro u; exact h (φ u) ⟨u, rfl⟩
      have hannR := finrank_dualAnnihilator_add (LinearMap.range φ)
      rw [hkerD] at h2
      omega
  rw [← hdual_range, hker_eq, ← hker]
  exact finrank_dualAnnihilator_add (LinearMap.ker φ)

theorem main :
    (∀ (t : ℕ) (ht : 0 < t) (j : ℕ), 3 ≤ j → j+9 ≤ t →
      letI : ∀ p : Prop, Decidable p := Classical.propDecidable
      let F := ZMod 2
      let n := 3*t
      let W := Fin n → F
      let ix := fun i : ℕ => (⟨i % n, Nat.mod_lt _ (Nat.mul_pos (Nat.succ_pos 2) ht)⟩ : Fin n)
      let code := fun (x : W) => ∀ e : Fin 2,
        (∑ i : Fin n, if i.val % 3 = e.val ∨ i.val % 3 = 2 then x i else 0) = 0
      ∀ P Q : Submodule F W, (∀ x ∈ P, code x) → (∀ y ∈ Q, code y) →
        n-2+j ≤ Module.finrank F P + Module.finrank F Q →
        j+2 < Module.finrank F P → j+2 < Module.finrank F Q →
        let hits := Nat.card {w : P × Q // ∀ i : Fin n,
          w.1.val i * w.2.val i = 0 ∧ w.1.val (ix (i.val+1)) * w.2.val i = 0}
        9*4^(j+3)*hits ≤ 8*3^(j+3)*Nat.card P*Nat.card Q) := by
  classical
  dsimp only
  intro t ht j hj hjt P Q hPcode hQcode hdimPQ hdimP hdimQ
  let n := 3 * t
  have hn_pos : 0 < n := by omega
  have hPcode' : ∀ x ∈ P, ∀ e : Fin 2,
      (∑ i : Fin n, if i.val % 3 = e.val ∨ i.val % 3 = 2 then x i else 0) = 0 :=
    fun x hx e => by convert hPcode x hx e
  have hQcode' : ∀ y ∈ Q, ∀ e : Fin 2,
      (∑ i : Fin n, if i.val % 3 = e.val ∨ i.val % 3 = 2 then y i else 0) = 0 :=
    fun y hy e => by convert hQcode y hy e
  let ix : ℕ → Fin n := fun i => ⟨i % n, Nat.mod_lt _ hn_pos⟩
  let left : Fin (2 * n) → Fin n := fun e => ix ((e.val + 1) / 2)
  let right : Fin (2 * n) → Fin n := fun e => ix (e.val / 2)
  let evL : Fin (2 * n) → P →ₗ[F] F := fun e =>
    { toFun := fun x => x.1 (left e)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let evR : Fin (2 * n) → Q →ₗ[F] F := fun e =>
    { toFun := fun y => y.1 (right e)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  obtain ⟨I, A, hIL, hIR, hIcard⟩ := linear_matroid_intersection evL evR
  let P0_sub : Submodule F P := ⨅ e ∈ A, LinearMap.ker (evL e)
  let Q0_sub : Submodule F Q := ⨅ e ∈ (Finset.univ \ A : Finset (Fin (2 * n))), LinearMap.ker (evR e)
  have hrkP : Module.finrank F (Submodule.span F (evL '' (A : Set (Fin (2 * n))))) +
      Module.finrank F P0_sub = Module.finrank F P := finrank_span_eval_eq_sub_ker evL A
  have hrkQ : Module.finrank F (Submodule.span F (evR '' ((Finset.univ \ A : Finset (Fin (2 * n))) : Set (Fin (2 * n))))) +
      Module.finrank F Q0_sub = Module.finrank F Q := finrank_span_eval_eq_sub_ker evR (Finset.univ \ A)
  have hdimPQ' : n - 2 + j ≤ Module.finrank F P + Module.finrank F Q := hdimPQ
  have hdimP' : j + 2 < Module.finrank F P := hdimP
  have hdimQ' : j + 2 < Module.finrank F Q := hdimQ
  have hIge : j + 3 ≤ I.card := by
    let P0 : Submodule F (Fin n → F) := P0_sub.map P.subtype
    let Q0 : Submodule F (Fin n → F) := Q0_sub.map Q.subtype
    have hP0_dim : Module.finrank F P0 = Module.finrank F P0_sub :=
      LinearEquiv.finrank_eq (Submodule.equivMapOfInjective P.subtype Subtype.val_injective P0_sub).symm
    have hQ0_dim : Module.finrank F Q0 = Module.finrank F Q0_sub :=
      LinearEquiv.finrank_eq (Submodule.equivMapOfInjective Q.subtype Subtype.val_injective Q0_sub).symm
    by_cases hPbot : P0 = ⊥
    · have h0 : Module.finrank F P0_sub = 0 := by rw [← hP0_dim, hPbot, finrank_bot]
      have hQle : Module.finrank F Q0_sub ≤ Module.finrank F Q := Submodule.finrank_le Q0_sub
      omega
    · by_cases hQbot : Q0 = ⊥
      · have h0 : Module.finrank F Q0_sub = 0 := by rw [← hQ0_dim, hQbot, finrank_bot]
        have hPle : Module.finrank F P0_sub ≤ Module.finrank F P := Submodule.finrank_le P0_sub
        omega
      · have hP0code : ∀ x ∈ P0, ∀ e : Fin 2,
            (∑ i : Fin n, if i.val % 3 = e.val ∨ i.val % 3 = 2 then x i else 0) = 0 := by
          rintro _ ⟨x, _, rfl⟩; exact hPcode' x.1 x.2
        have hQ0code : ∀ y ∈ Q0, ∀ e : Fin 2,
            (∑ i : Fin n, if i.val % 3 = e.val ∨ i.val % 3 = 2 then y i else 0) = 0 := by
          rintro _ ⟨y, _, rfl⟩; exact hQcode' y.1 y.2
        have horth : ∀ x ∈ P0, ∀ y ∈ Q0, ∀ i : Fin n,
            x i * y i = 0 ∧ x ⟨(i.val + 1) % n, Nat.mod_lt _ hn_pos⟩ * y i = 0 := by
          rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ i
          have hxA : ∀ e ∈ A, x.1 (left e) = 0 := by
            intro e he
            have hx' : x ∈ P0_sub := hx
            simp only [P0_sub, Submodule.mem_iInf, LinearMap.mem_ker] at hx'
            exact hx' e he
          have hyB : ∀ e : Fin (2 * n), e ∉ A → y.1 (right e) = 0 := by
            intro e he
            have he' : e ∈ Finset.univ \ A := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, he⟩
            have hy' : y ∈ Q0_sub := hy
            simp only [Q0_sub, Submodule.mem_iInf, LinearMap.mem_ker] at hy'
            exact hy' e he'
          constructor
          · let e0 : Fin (2 * n) := ⟨2 * i.val, by omega⟩
            have hL0 : left e0 = i := Fin.ext (by dsimp [left, ix, e0]; rw [Nat.mod_eq_of_lt (by omega)]; omega)
            have hR0 : right e0 = i := Fin.ext (by dsimp [right, ix, e0]; rw [Nat.mod_eq_of_lt (by omega)]; omega)
            by_cases heA : e0 ∈ A
            · have := hxA e0 heA; rw [hL0] at this; simp [this]
            · have := hyB e0 heA; rw [hR0] at this; simp [this]
          · let e1 : Fin (2 * n) := ⟨2 * i.val + 1, by omega⟩
            have hL1 : left e1 = ⟨(i.val + 1) % n, Nat.mod_lt _ hn_pos⟩ :=
              Fin.ext (by dsimp [left, ix, e1]; congr 1; omega)
            have hR1 : right e1 = i := Fin.ext (by dsimp [right, ix, e1]; rw [Nat.mod_eq_of_lt (by omega)]; omega)
            by_cases heA : e1 ∈ A
            · have := hxA e1 heA; rw [hL1] at this; simp [this]
            · have := hyB e1 heA; rw [hR1] at this; simp [this]
        have hceil : Module.finrank F P0 + Module.finrank F Q0 ≤ 3 * t - 5 :=
          mixed_zero_space_ceiling t (by omega) P0 Q0 hP0code hQ0code hPbot hQbot horth
        have hneq : n = 3 * t := rfl
        omega
  let pred : P × Q → Prop := fun w =>
    ∀ i : Fin n, w.1.val i * w.2.val i = 0 ∧ w.1.val (ix (i.val + 1)) * w.2.val i = 0
  have hpred_edge : ∀ w : P × Q, pred w → ∀ e : Fin (2 * n), w.1.val (left e) * w.2.val (right e) = 0 := by
    intro w hw e
    by_cases he : e.val % 2 = 0
    · let i : Fin n := ⟨e.val / 2, by omega⟩
      have hL : left e = i := Fin.ext (by dsimp [left, ix, i]; rw [Nat.mod_eq_of_lt (by omega)]; omega)
      have hR : right e = i := Fin.ext (by dsimp [right, ix, i]; rw [Nat.mod_eq_of_lt (by omega)])
      rw [hL, hR]; exact (hw i).1
    · let i : Fin n := ⟨e.val / 2, by omega⟩
      have hL : left e = ix (i.val + 1) := Fin.ext (by dsimp [left, ix, i]; congr 1; omega)
      have hR : right e = i := Fin.ext (by dsimp [right, ix, i]; rw [Nat.mod_eq_of_lt (by omega)])
      rw [hL, hR]; exact (hw i).2
  by_cases hgt : j + 4 ≤ I.card
  · obtain ⟨J, hJI, hJcard⟩ := Finset.exists_subset_card_eq hgt
    let sEquiv : Fin (j + 4) ≃ J := (Fintype.equivFinOfCardEq (by simp [Fintype.card_coe, hJcard])).symm
    let s : Fin (j + 4) → Fin (2 * n) := fun c => (sEquiv c).1
    have hL_ind : LinearIndependent F (fun c : Fin (j + 4) => evL (s c)) :=
      hIL.comp (fun c => ⟨s c, hJI (sEquiv c).2⟩) (fun a b h => by
        have h' : (sEquiv a).1 = (sEquiv b).1 := congrArg (fun z : I => z.1) h
        exact sEquiv.injective (Subtype.ext h'))
    have hR_ind : LinearIndependent F (fun c : Fin (j + 4) => evR (s c)) :=
      hIR.comp (fun c => ⟨s c, hJI (sEquiv c).2⟩) (fun a b h => by
        have h' : (sEquiv a).1 = (sEquiv b).1 := congrArg (fun z : I => z.1) h
        exact sEquiv.injective (Subtype.ext h'))
    have hPsurj := linearIndependent_dual_iff_surjective _ hL_ind
    have hQsurj := linearIndependent_dual_iff_surjective _ hR_ind
    let φ : P →ₗ[F] (Fin (j + 4) → F) := LinearMap.pi (fun c => evL (s c))
    let ψ : Q →ₗ[F] (Fin (j + 4) → F) := LinearMap.pi (fun c => evR (s c))
    let G : Finset ((Fin (j + 4) → F) × (Fin (j + 4) → F)) :=
      Finset.univ.filter (fun uv => ∀ c : Fin (j + 4), uv.1 c * uv.2 c = 0)
    have hcore := card_hits_le_of_good φ ψ hPsurj hQsurj pred G (fun w hw =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun c => hpred_edge w hw (s c)⟩)
    have hGcard : G.card = 3 ^ (j + 4) := card_good_pairs_indep (j + 4)
    have hVcard : Fintype.card (Fin (j + 4) → F) = 2 ^ (j + 4) := by simp
    rw [hGcard, hVcard] at hcore
    have h4pow : 2 ^ (j + 4) * 2 ^ (j + 4) = 4 * 4 ^ (j + 3) := by
      have h1 : 2 ^ (j + 4) * 2 ^ (j + 4) = 4 ^ (j + 4) := by rw [← mul_pow]; norm_num
      rw [h1, show j + 4 = (j + 3) + 1 by omega, pow_succ]; ring
    have h3pow : 3 ^ (j + 4) = 3 * 3 ^ (j + 3) := by
      rw [show j + 4 = (j + 3) + 1 by omega, pow_succ]; ring
    rw [h4pow, h3pow] at hcore
    have h36 : 4 * (9 * 4 ^ (j + 3) * Nat.card {w : P × Q // pred w}) ≤
        4 * (8 * 3 ^ (j + 3) * Nat.card P * Nat.card Q) := by
      calc 4 * (9 * 4 ^ (j + 3) * Nat.card {w : P × Q // pred w})
          = 9 * (4 * 4 ^ (j + 3) * Nat.card {w : P × Q // pred w}) := by ring
        _ ≤ 9 * (3 * 3 ^ (j + 3) * Nat.card P * Nat.card Q) := Nat.mul_le_mul_left 9 hcore
        _ = 27 * 3 ^ (j + 3) * Nat.card P * Nat.card Q := by ring
        _ ≤ 32 * 3 ^ (j + 3) * Nat.card P * Nat.card Q := by
            have : 27 * 3 ^ (j + 3) ≤ 32 * 3 ^ (j + 3) := by omega
            exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ this)
        _ = 4 * (8 * 3 ^ (j + 3) * Nat.card P * Nat.card Q) := by ring
    change 9 * 4 ^ (j + 3) * Nat.card {w : P × Q // pred w} ≤ 8 * 3 ^ (j + 3) * Nat.card P * Nat.card Q
    omega
  · have hIeq : I.card = j + 3 := by omega
    let sEquiv : Fin (j + 3) ≃ I := (Fintype.equivFinOfCardEq (by simp [Fintype.card_coe, hIeq])).symm
    let s : Fin (j + 3) → Fin (2 * n) := fun c => (sEquiv c).1
    have hL_ind : LinearIndependent F (fun c : Fin (j + 3) => evL (s c)) :=
      hIL.comp sEquiv sEquiv.injective
    have hR_ind : LinearIndependent F (fun c : Fin (j + 3) => evR (s c)) :=
      hIR.comp sEquiv sEquiv.injective
    have hPsurj := linearIndependent_dual_iff_surjective _ hL_ind
    have hQsurj := linearIndependent_dual_iff_surjective _ hR_ind
    by_cases hcopy : ∀ e : Fin (2 * n),
        (∀ x : P, x.val (left e) = 0) ∨ (∀ y : Q, y.val (right e) = 0) ∨
        ∃ c : Fin (j + 3), (∀ x : P, x.val (left e) = x.val (left (s c))) ∧
          (∀ y : Q, y.val (right e) = y.val (right (s c)))
    · exfalso
      have hbound : 2 * (Module.finrank F P + Module.finrank F Q) + 5 ≤ 2 * (3 * t) + (j + 3) :=
        pure_copy_dim_bound t ht (j + 3) (by omega) P Q hPcode' hQcode' s hPsurj hQsurj hcopy
      have hneq : n = 3 * t := rfl
      omega
    · push Not at hcopy
      rcases hcopy with ⟨e0, he0L, he0R, he0not⟩
      have hu0 : evL e0 ≠ 0 := fun h => by rcases he0L with ⟨x, hx⟩; exact hx (LinearMap.congr_fun h x)
      have hv0 : evR e0 ≠ 0 := fun h => by rcases he0R with ⟨y, hy⟩; exact hy (LinearMap.congr_fun h y)
      have hnc : ∀ c : Fin (j + 3), ¬ (evL e0 = evL (s c) ∧ evR e0 = evR (s c)) := by
        intro c ⟨h1, h2⟩
        rcases he0not c (fun x => LinearMap.congr_fun h1 x) with ⟨y, hy⟩
        exact hy (LinearMap.congr_fun h2 y)
      exact hits_bound_one_ninth (j + 3) (fun c => evL (s c)) (fun c => evR (s c))
        hPsurj hQsurj (evL e0) (evR e0) hu0 hv0 hnc pred
        (fun w hw c => hpred_edge w hw (s c)) (fun w hw => hpred_edge w hw e0)

end PEqualNP.Outside.L_lib_1064_aux

theorem PEqualNP.Outside.L_lib_1064 : (∀ (t : ℕ) (ht : 0 < t) (j : ℕ), 3 ≤ j → j+9 ≤ t →
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let F := ZMod 2
  let n := 3*t
  let W := Fin n → F
  let ix := fun i : ℕ => (⟨i % n, Nat.mod_lt _ (Nat.mul_pos (Nat.succ_pos 2) ht)⟩ : Fin n)
  let code := fun (x : W) => ∀ e : Fin 2,
    (∑ i : Fin n, if i.val % 3 = e.val ∨ i.val % 3 = 2 then x i else 0) = 0
  ∀ P Q : Submodule F W, (∀ x ∈ P, code x) → (∀ y ∈ Q, code y) →
    n-2+j ≤ Module.finrank F P + Module.finrank F Q →
    j+2 < Module.finrank F P → j+2 < Module.finrank F Q →
    let hits := Nat.card {w : P × Q // ∀ i : Fin n,
      w.1.val i * w.2.val i = 0 ∧ w.1.val (ix (i.val+1)) * w.2.val i = 0}
    9*4^(j+3)*hits ≤ 8*3^(j+3)*Nat.card P*Nat.card Q) :=
  PEqualNP.Outside.L_lib_1064_aux.main
